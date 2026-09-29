-- Prove2me | solution 1 for syracuse_descends_range_1332985_1334985
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:41.643387+00:00
-- url     : https://prove2.me/submissions/7db494c2-88fd-4226-8db2-c2e02f21846d

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


theorem B3203101 : Blo 1332985 3203101 := bbase (se 3 (by rfl) ⟨600581, by rfl⟩ : syracuseStep 3203101 = 1201163) (by norm_num)
theorem B1425497 : Blo 1332985 1425497 := bbase (se 2 (by rfl) ⟨534561, by rfl⟩ : syracuseStep 1425497 = 1069123) (by norm_num)
theorem B1687645 : Blo 1332985 1687645 := bbase (se 3 (by rfl) ⟨316433, by rfl⟩ : syracuseStep 1687645 = 632867) (by norm_num)
theorem B3375229 : Blo 1332985 3375229 := bbase (se 3 (by rfl) ⟨632855, by rfl⟩ : syracuseStep 3375229 = 1265711) (by norm_num)
theorem B1425557 : Blo 1332985 1425557 := bbase (se 6 (by rfl) ⟨33411, by rfl⟩ : syracuseStep 1425557 = 66823) (by norm_num)
theorem B3801269 : Blo 1332985 3801269 := bbase (se 5 (by rfl) ⟨178184, by rfl⟩ : syracuseStep 3801269 = 356369) (by norm_num)
theorem B3375341 : Blo 1332985 3375341 := bbase (se 3 (by rfl) ⟨632876, by rfl⟩ : syracuseStep 3375341 = 1265753) (by norm_num)
theorem B3203333 : Blo 1332985 3203333 := bbase (se 4 (by rfl) ⟨300312, by rfl⟩ : syracuseStep 3203333 = 600625) (by norm_num)
theorem B1687817 : Blo 1332985 1687817 := bbase (se 2 (by rfl) ⟨632931, by rfl⟩ : syracuseStep 1687817 = 1265863) (by norm_num)
theorem B1687873 : Blo 1332985 1687873 := bbase (se 2 (by rfl) ⟨632952, by rfl⟩ : syracuseStep 1687873 = 1265905) (by norm_num)
theorem B32440661 : Blo 1332985 32440661 := bbase (se 10 (by rfl) ⟨47520, by rfl⟩ : syracuseStep 32440661 = 95041) (by norm_num)
theorem B7594357 : Blo 1332985 7594357 := bbase (se 5 (by rfl) ⟨355985, by rfl⟩ : syracuseStep 7594357 = 711971) (by norm_num)
theorem B3203477 : Blo 1332985 3203477 := bbase (se 6 (by rfl) ⟨75081, by rfl⟩ : syracuseStep 3203477 = 150163) (by norm_num)
theorem B1687969 : Blo 1332985 1687969 := bbase (se 2 (by rfl) ⟨632988, by rfl⟩ : syracuseStep 1687969 = 1265977) (by norm_num)
theorem B2531749 : Blo 1332985 2531749 := bbase (se 4 (by rfl) ⟨237351, by rfl⟩ : syracuseStep 2531749 = 474703) (by norm_num)
theorem B1712549 : Blo 1332985 1712549 := bbase (se 4 (by rfl) ⟨160551, by rfl⟩ : syracuseStep 1712549 = 321103) (by norm_num)
theorem B3375533 : Blo 1332985 3375533 := bbase (se 3 (by rfl) ⟨632912, by rfl⟩ : syracuseStep 3375533 = 1265825) (by norm_num)
theorem B3203525 : Blo 1332985 3203525 := bbase (se 4 (by rfl) ⟨300330, by rfl⟩ : syracuseStep 3203525 = 600661) (by norm_num)
theorem B1499629 : Blo 1332985 1499629 := bbase (se 3 (by rfl) ⟨281180, by rfl⟩ : syracuseStep 1499629 = 562361) (by norm_num)
theorem B1499665 : Blo 1332985 1499665 := bbase (se 2 (by rfl) ⟨562374, by rfl⟩ : syracuseStep 1499665 = 1124749) (by norm_num)
theorem B1499701 : Blo 1332985 1499701 := bbase (se 5 (by rfl) ⟨70298, by rfl⟩ : syracuseStep 1499701 = 140597) (by norm_num)
theorem B2531893 : Blo 1332985 2531893 := bbase (se 5 (by rfl) ⟨118682, by rfl⟩ : syracuseStep 2531893 = 237365) (by norm_num)
theorem B11395637 : Blo 1332985 11395637 := bbase (se 5 (by rfl) ⟨534170, by rfl⟩ : syracuseStep 11395637 = 1068341) (by norm_num)
theorem B1802821 : Blo 1332985 1802821 := bbase (se 4 (by rfl) ⟨169014, by rfl⟩ : syracuseStep 1802821 = 338029) (by norm_num)
theorem B1688141 : Blo 1332985 1688141 := bbase (se 3 (by rfl) ⟨316526, by rfl⟩ : syracuseStep 1688141 = 633053) (by norm_num)
theorem B1499737 : Blo 1332985 1499737 := bbase (se 2 (by rfl) ⟨562401, by rfl⟩ : syracuseStep 1499737 = 1124803) (by norm_num)
theorem B5063269 : Blo 1332985 5063269 := bbase (se 4 (by rfl) ⟨474681, by rfl⟩ : syracuseStep 5063269 = 949363) (by norm_num)
theorem B1499773 : Blo 1332985 1499773 := bbase (se 3 (by rfl) ⟨281207, by rfl⟩ : syracuseStep 1499773 = 562415) (by norm_num)
theorem B1999493 : Blo 1332985 1999493 := bbase (se 4 (by rfl) ⟨187452, by rfl⟩ : syracuseStep 1999493 = 374905) (by norm_num)
theorem B1688197 : Blo 1332985 1688197 := bbase (se 4 (by rfl) ⟨158268, by rfl⟩ : syracuseStep 1688197 = 316537) (by norm_num)
theorem B2704013 : Blo 1332985 2704013 := bbase (se 3 (by rfl) ⟨507002, by rfl⟩ : syracuseStep 2704013 = 1014005) (by norm_num)
theorem B1999517 : Blo 1332985 1999517 := bbase (se 3 (by rfl) ⟨374909, by rfl⟩ : syracuseStep 1999517 = 749819) (by norm_num)
theorem B1499809 : Blo 1332985 1499809 := bbase (se 2 (by rfl) ⟨562428, by rfl⟩ : syracuseStep 1499809 = 1124857) (by norm_num)
theorem B1999541 : Blo 1332985 1999541 := bbase (se 5 (by rfl) ⟨93728, by rfl⟩ : syracuseStep 1999541 = 187457) (by norm_num)
theorem B1499845 : Blo 1332985 1499845 := bbase (se 4 (by rfl) ⟨140610, by rfl⟩ : syracuseStep 1499845 = 281221) (by norm_num)
theorem B1999565 : Blo 1332985 1999565 := bbase (se 3 (by rfl) ⟨374918, by rfl⟩ : syracuseStep 1999565 = 749837) (by norm_num)
theorem B2532053 : Blo 1332985 2532053 := bbase (se 7 (by rfl) ⟨29672, by rfl⟩ : syracuseStep 2532053 = 59345) (by norm_num)
theorem B7701205 : Blo 1332985 7701205 := bbase (se 7 (by rfl) ⟨90248, by rfl⟩ : syracuseStep 7701205 = 180497) (by norm_num)
theorem B1999589 : Blo 1332985 1999589 := bbase (se 4 (by rfl) ⟨187461, by rfl⟩ : syracuseStep 1999589 = 374923) (by norm_num)
theorem B3203813 : Blo 1332985 3203813 := bbase (se 4 (by rfl) ⟨300357, by rfl⟩ : syracuseStep 3203813 = 600715) (by norm_num)
theorem B1688293 : Blo 1332985 1688293 := bbase (se 4 (by rfl) ⟨158277, by rfl⟩ : syracuseStep 1688293 = 316555) (by norm_num)
theorem B1499881 : Blo 1332985 1499881 := bbase (se 2 (by rfl) ⟨562455, by rfl⟩ : syracuseStep 1499881 = 1124911) (by norm_num)
theorem B1999613 : Blo 1332985 1999613 := bbase (se 3 (by rfl) ⟨374927, by rfl⟩ : syracuseStep 1999613 = 749855) (by norm_num)
theorem B3375877 : Blo 1332985 3375877 := bbase (se 4 (by rfl) ⟨316488, by rfl⟩ : syracuseStep 3375877 = 632977) (by norm_num)
theorem B1499917 : Blo 1332985 1499917 := bbase (se 3 (by rfl) ⟨281234, by rfl⟩ : syracuseStep 1499917 = 562469) (by norm_num)
theorem B1999637 : Blo 1332985 1999637 := bbase (se 6 (by rfl) ⟨46866, by rfl⟩ : syracuseStep 1999637 = 93733) (by norm_num)
theorem B1999661 : Blo 1332985 1999661 := bbase (se 3 (by rfl) ⟨374936, by rfl⟩ : syracuseStep 1999661 = 749873) (by norm_num)
theorem B1499953 : Blo 1332985 1499953 := bbase (se 2 (by rfl) ⟨562482, by rfl⟩ : syracuseStep 1499953 = 1124965) (by norm_num)
theorem B1999685 : Blo 1332985 1999685 := bbase (se 4 (by rfl) ⟨187470, by rfl⟩ : syracuseStep 1999685 = 374941) (by norm_num)
theorem B1499989 : Blo 1332985 1499989 := bbase (se 9 (by rfl) ⟨4394, by rfl⟩ : syracuseStep 1499989 = 8789) (by norm_num)
theorem B1999709 : Blo 1332985 1999709 := bbase (se 3 (by rfl) ⟨374945, by rfl⟩ : syracuseStep 1999709 = 749891) (by norm_num)
theorem B2532197 : Blo 1332985 2532197 := bbase (se 4 (by rfl) ⟨237393, by rfl⟩ : syracuseStep 2532197 = 474787) (by norm_num)
theorem B1999733 : Blo 1332985 1999733 := bbase (se 5 (by rfl) ⟨93737, by rfl⟩ : syracuseStep 1999733 = 187475) (by norm_num)
theorem B3375989 : Blo 1332985 3375989 := bbase (se 5 (by rfl) ⟨158249, by rfl⟩ : syracuseStep 3375989 = 316499) (by norm_num)
theorem B1500025 : Blo 1332985 1500025 := bbase (se 2 (by rfl) ⟨562509, by rfl⟩ : syracuseStep 1500025 = 1125019) (by norm_num)
theorem B1999757 : Blo 1332985 1999757 := bbase (se 3 (by rfl) ⟨374954, by rfl⟩ : syracuseStep 1999757 = 749909) (by norm_num)
theorem B1688465 : Blo 1332985 1688465 := bbase (se 2 (by rfl) ⟨633174, by rfl⟩ : syracuseStep 1688465 = 1266349) (by norm_num)
theorem B5063573 : Blo 1332985 5063573 := bbase (se 6 (by rfl) ⟨118677, by rfl⟩ : syracuseStep 5063573 = 237355) (by norm_num)
theorem B1500061 : Blo 1332985 1500061 := bbase (se 3 (by rfl) ⟨281261, by rfl⟩ : syracuseStep 1500061 = 562523) (by norm_num)
theorem B1999781 : Blo 1332985 1999781 := bbase (se 4 (by rfl) ⟨187479, by rfl⟩ : syracuseStep 1999781 = 374959) (by norm_num)
theorem B1999805 : Blo 1332985 1999805 := bbase (se 3 (by rfl) ⟨374963, by rfl⟩ : syracuseStep 1999805 = 749927) (by norm_num)
theorem B1500097 : Blo 1332985 1500097 := bbase (se 2 (by rfl) ⟨562536, by rfl⟩ : syracuseStep 1500097 = 1125073) (by norm_num)
theorem B1688521 : Blo 1332985 1688521 := bbase (se 2 (by rfl) ⟨633195, by rfl⟩ : syracuseStep 1688521 = 1266391) (by norm_num)
theorem B1999829 : Blo 1332985 1999829 := bbase (se 7 (by rfl) ⟨23435, by rfl⟩ : syracuseStep 1999829 = 46871) (by norm_num)
theorem B12329941 : Blo 1332985 12329941 := bbase (se 7 (by rfl) ⟨144491, by rfl⟩ : syracuseStep 12329941 = 288983) (by norm_num)
theorem B1500133 : Blo 1332985 1500133 := bbase (se 4 (by rfl) ⟨140637, by rfl⟩ : syracuseStep 1500133 = 281275) (by norm_num)
theorem B1999853 : Blo 1332985 1999853 := bbase (se 3 (by rfl) ⟨374972, by rfl⟩ : syracuseStep 1999853 = 749945) (by norm_num)
theorem B2999285 : Blo 1332985 2999285 := bbase (se 5 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 2999285 = 281183) (by norm_num)
theorem B1999877 : Blo 1332985 1999877 := bbase (se 4 (by rfl) ⟨187488, by rfl⟩ : syracuseStep 1999877 = 374977) (by norm_num)
theorem B1500169 : Blo 1332985 1500169 := bbase (se 2 (by rfl) ⟨562563, by rfl⟩ : syracuseStep 1500169 = 1125127) (by norm_num)
theorem B1999901 : Blo 1332985 1999901 := bbase (se 3 (by rfl) ⟨374981, by rfl⟩ : syracuseStep 1999901 = 749963) (by norm_num)
theorem B1688617 : Blo 1332985 1688617 := bbase (se 2 (by rfl) ⟨633231, by rfl⟩ : syracuseStep 1688617 = 1266463) (by norm_num)
theorem B1500205 : Blo 1332985 1500205 := bbase (se 3 (by rfl) ⟨281288, by rfl⟩ : syracuseStep 1500205 = 562577) (by norm_num)
theorem B1999925 : Blo 1332985 1999925 := bbase (se 5 (by rfl) ⟨93746, by rfl⟩ : syracuseStep 1999925 = 187493) (by norm_num)
theorem B3376181 : Blo 1332985 3376181 := bbase (se 5 (by rfl) ⟨158258, by rfl⟩ : syracuseStep 3376181 = 316517) (by norm_num)
theorem B2999357 : Blo 1332985 2999357 := bbase (se 3 (by rfl) ⟨562379, by rfl⟩ : syracuseStep 2999357 = 1124759) (by norm_num)
theorem B1999949 : Blo 1332985 1999949 := bbase (se 3 (by rfl) ⟨374990, by rfl⟩ : syracuseStep 1999949 = 749981) (by norm_num)
theorem B1500241 : Blo 1332985 1500241 := bbase (se 2 (by rfl) ⟨562590, by rfl⟩ : syracuseStep 1500241 = 1125181) (by norm_num)
theorem B1352785 : Blo 1332985 1352785 := bbase (se 2 (by rfl) ⟨507294, by rfl⟩ : syracuseStep 1352785 = 1014589) (by norm_num)
theorem B1352801 : Blo 1332985 1352801 := bbase (se 2 (by rfl) ⟨507300, by rfl⟩ : syracuseStep 1352801 = 1014601) (by norm_num)
theorem B1999973 : Blo 1332985 1999973 := bbase (se 4 (by rfl) ⟨187497, by rfl⟩ : syracuseStep 1999973 = 374995) (by norm_num)
theorem B1500277 : Blo 1332985 1500277 := bbase (se 5 (by rfl) ⟨70325, by rfl⟩ : syracuseStep 1500277 = 140651) (by norm_num)
theorem B6751349 : Blo 1332985 6751349 := bbase (se 5 (by rfl) ⟨316469, by rfl⟩ : syracuseStep 6751349 = 632939) (by norm_num)
theorem B1999997 : Blo 1332985 1999997 := bbase (se 3 (by rfl) ⟨374999, by rfl⟩ : syracuseStep 1999997 = 749999) (by norm_num)
theorem B2999429 : Blo 1332985 2999429 := bbase (se 4 (by rfl) ⟨281196, by rfl⟩ : syracuseStep 2999429 = 562393) (by norm_num)
theorem B2532485 : Blo 1332985 2532485 := bbase (se 4 (by rfl) ⟨237420, by rfl⟩ : syracuseStep 2532485 = 474841) (by norm_num)
theorem B2000021 : Blo 1332985 2000021 := bbase (se 6 (by rfl) ⟨46875, by rfl⟩ : syracuseStep 2000021 = 93751) (by norm_num)
theorem B1500313 : Blo 1332985 1500313 := bbase (se 2 (by rfl) ⟨562617, by rfl⟩ : syracuseStep 1500313 = 1125235) (by norm_num)
theorem B2000045 : Blo 1332985 2000045 := bbase (se 3 (by rfl) ⟨375008, by rfl⟩ : syracuseStep 2000045 = 750017) (by norm_num)
theorem B1500349 : Blo 1332985 1500349 := bbase (se 3 (by rfl) ⟨281315, by rfl⟩ : syracuseStep 1500349 = 562631) (by norm_num)
theorem B2000069 : Blo 1332985 2000069 := bbase (se 4 (by rfl) ⟨187506, by rfl⟩ : syracuseStep 2000069 = 375013) (by norm_num)
theorem B2999501 : Blo 1332985 2999501 := bbase (se 3 (by rfl) ⟨562406, by rfl⟩ : syracuseStep 2999501 = 1124813) (by norm_num)
theorem B1688789 : Blo 1332985 1688789 := bbase (se 7 (by rfl) ⟨19790, by rfl⟩ : syracuseStep 1688789 = 39581) (by norm_num)
theorem B2000093 : Blo 1332985 2000093 := bbase (se 3 (by rfl) ⟨375017, by rfl⟩ : syracuseStep 2000093 = 750035) (by norm_num)
theorem B1500385 : Blo 1332985 1500385 := bbase (se 2 (by rfl) ⟨562644, by rfl⟩ : syracuseStep 1500385 = 1125289) (by norm_num)
theorem B2000117 : Blo 1332985 2000117 := bbase (se 5 (by rfl) ⟨93755, by rfl⟩ : syracuseStep 2000117 = 187511) (by norm_num)
theorem B1500421 : Blo 1332985 1500421 := bbase (se 4 (by rfl) ⟨140664, by rfl⟩ : syracuseStep 1500421 = 281329) (by norm_num)
theorem B2000141 : Blo 1332985 2000141 := bbase (se 3 (by rfl) ⟨375026, by rfl⟩ : syracuseStep 2000141 = 750053) (by norm_num)
theorem B1688845 : Blo 1332985 1688845 := bbase (se 3 (by rfl) ⟨316658, by rfl⟩ : syracuseStep 1688845 = 633317) (by norm_num)
theorem B2999573 : Blo 1332985 2999573 := bbase (se 6 (by rfl) ⟨70302, by rfl⟩ : syracuseStep 2999573 = 140605) (by norm_num)
theorem B2532637 : Blo 1332985 2532637 := bbase (se 3 (by rfl) ⟨474869, by rfl⟩ : syracuseStep 2532637 = 949739) (by norm_num)
theorem B2000165 : Blo 1332985 2000165 := bbase (se 4 (by rfl) ⟨187515, by rfl⟩ : syracuseStep 2000165 = 375031) (by norm_num)
theorem B1500457 : Blo 1332985 1500457 := bbase (se 2 (by rfl) ⟨562671, by rfl⟩ : syracuseStep 1500457 = 1125343) (by norm_num)
theorem B2704693 : Blo 1332985 2704693 := bbase (se 5 (by rfl) ⟨126782, by rfl⟩ : syracuseStep 2704693 = 253565) (by norm_num)
theorem B2000189 : Blo 1332985 2000189 := bbase (se 3 (by rfl) ⟨375035, by rfl⟩ : syracuseStep 2000189 = 750071) (by norm_num)
theorem B1500493 : Blo 1332985 1500493 := bbase (se 3 (by rfl) ⟨281342, by rfl⟩ : syracuseStep 1500493 = 562685) (by norm_num)
theorem B2000213 : Blo 1332985 2000213 := bbase (se 12 (by rfl) ⟨732, by rfl⟩ : syracuseStep 2000213 = 1465) (by norm_num)
theorem B2999645 : Blo 1332985 2999645 := bbase (se 3 (by rfl) ⟨562433, by rfl⟩ : syracuseStep 2999645 = 1124867) (by norm_num)
theorem B2000237 : Blo 1332985 2000237 := bbase (se 3 (by rfl) ⟨375044, by rfl⟩ : syracuseStep 2000237 = 750089) (by norm_num)
theorem B1688941 : Blo 1332985 1688941 := bbase (se 3 (by rfl) ⟨316676, by rfl⟩ : syracuseStep 1688941 = 633353) (by norm_num)
theorem B1500529 : Blo 1332985 1500529 := bbase (se 2 (by rfl) ⟨562698, by rfl⟩ : syracuseStep 1500529 = 1125397) (by norm_num)
theorem B2000261 : Blo 1332985 2000261 := bbase (se 4 (by rfl) ⟨187524, by rfl⟩ : syracuseStep 2000261 = 375049) (by norm_num)
theorem B3376525 : Blo 1332985 3376525 := bbase (se 3 (by rfl) ⟨633098, by rfl⟩ : syracuseStep 3376525 = 1266197) (by norm_num)
theorem B1500565 : Blo 1332985 1500565 := bbase (se 6 (by rfl) ⟨35169, by rfl⟩ : syracuseStep 1500565 = 70339) (by norm_num)
theorem B2000285 : Blo 1332985 2000285 := bbase (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) (by norm_num)
theorem B2999717 : Blo 1332985 2999717 := bbase (se 4 (by rfl) ⟨281223, by rfl⟩ : syracuseStep 2999717 = 562447) (by norm_num)
theorem B2000309 : Blo 1332985 2000309 := bbase (se 5 (by rfl) ⟨93764, by rfl⟩ : syracuseStep 2000309 = 187529) (by norm_num)
theorem B1500601 : Blo 1332985 1500601 := bbase (se 2 (by rfl) ⟨562725, by rfl⟩ : syracuseStep 1500601 = 1125451) (by norm_num)
theorem B2000333 : Blo 1332985 2000333 := bbase (se 3 (by rfl) ⟨375062, by rfl⟩ : syracuseStep 2000333 = 750125) (by norm_num)
theorem B4498901 : Blo 1332985 4498901 := bbase (se 7 (by rfl) ⟨52721, by rfl⟩ : syracuseStep 4498901 = 105443) (by norm_num)
theorem B1500637 : Blo 1332985 1500637 := bbase (se 3 (by rfl) ⟨281369, by rfl⟩ : syracuseStep 1500637 = 562739) (by norm_num)
theorem B2000357 : Blo 1332985 2000357 := bbase (se 4 (by rfl) ⟨187533, by rfl⟩ : syracuseStep 2000357 = 375067) (by norm_num)
theorem B2999789 : Blo 1332985 2999789 := bbase (se 3 (by rfl) ⟨562460, by rfl⟩ : syracuseStep 2999789 = 1124921) (by norm_num)
theorem B2000381 : Blo 1332985 2000381 := bbase (se 3 (by rfl) ⟨375071, by rfl⟩ : syracuseStep 2000381 = 750143) (by norm_num)
theorem B3376637 : Blo 1332985 3376637 := bbase (se 3 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 3376637 = 1266239) (by norm_num)
theorem B1500673 : Blo 1332985 1500673 := bbase (se 2 (by rfl) ⟨562752, by rfl⟩ : syracuseStep 1500673 = 1125505) (by norm_num)
theorem B2000405 : Blo 1332985 2000405 := bbase (se 6 (by rfl) ⟨46884, by rfl⟩ : syracuseStep 2000405 = 93769) (by norm_num)
theorem B1689113 : Blo 1332985 1689113 := bbase (se 2 (by rfl) ⟨633417, by rfl⟩ : syracuseStep 1689113 = 1266835) (by norm_num)
theorem B1500709 : Blo 1332985 1500709 := bbase (se 4 (by rfl) ⟨140691, by rfl⟩ : syracuseStep 1500709 = 281383) (by norm_num)
theorem B2000429 : Blo 1332985 2000429 := bbase (se 3 (by rfl) ⟨375080, by rfl⟩ : syracuseStep 2000429 = 750161) (by norm_num)
theorem B2999861 : Blo 1332985 2999861 := bbase (se 5 (by rfl) ⟨140618, by rfl⟩ : syracuseStep 2999861 = 281237) (by norm_num)
theorem B2565685 : Blo 1332985 2565685 := bbase (se 5 (by rfl) ⟨120266, by rfl⟩ : syracuseStep 2565685 = 240533) (by norm_num)
theorem B2000453 : Blo 1332985 2000453 := bbase (se 4 (by rfl) ⟨187542, by rfl⟩ : syracuseStep 2000453 = 375085) (by norm_num)
theorem B1500745 : Blo 1332985 1500745 := bbase (se 2 (by rfl) ⟨562779, by rfl⟩ : syracuseStep 1500745 = 1125559) (by norm_num)
theorem B2532941 : Blo 1332985 2532941 := bbase (se 3 (by rfl) ⟨474926, by rfl⟩ : syracuseStep 2532941 = 949853) (by norm_num)
theorem B1689169 : Blo 1332985 1689169 := bbase (se 2 (by rfl) ⟨633438, by rfl⟩ : syracuseStep 1689169 = 1266877) (by norm_num)
theorem B2000477 : Blo 1332985 2000477 := bbase (se 3 (by rfl) ⟨375089, by rfl⟩ : syracuseStep 2000477 = 750179) (by norm_num)
theorem B1500781 : Blo 1332985 1500781 := bbase (se 3 (by rfl) ⟨281396, by rfl⟩ : syracuseStep 1500781 = 562793) (by norm_num)
theorem B2000501 : Blo 1332985 2000501 := bbase (se 5 (by rfl) ⟨93773, by rfl⟩ : syracuseStep 2000501 = 187547) (by norm_num)
theorem B2999933 : Blo 1332985 2999933 := bbase (se 3 (by rfl) ⟨562487, by rfl⟩ : syracuseStep 2999933 = 1124975) (by norm_num)
theorem B2000525 : Blo 1332985 2000525 := bbase (se 3 (by rfl) ⟨375098, by rfl⟩ : syracuseStep 2000525 = 750197) (by norm_num)
theorem B1500817 : Blo 1332985 1500817 := bbase (se 2 (by rfl) ⟨562806, by rfl⟩ : syracuseStep 1500817 = 1125613) (by norm_num)
theorem B2000549 : Blo 1332985 2000549 := bbase (se 4 (by rfl) ⟨187551, by rfl⟩ : syracuseStep 2000549 = 375103) (by norm_num)
theorem B6940325 : Blo 1332985 6940325 := bbase (se 4 (by rfl) ⟨650655, by rfl⟩ : syracuseStep 6940325 = 1301311) (by norm_num)
theorem B1689265 : Blo 1332985 1689265 := bbase (se 2 (by rfl) ⟨633474, by rfl⟩ : syracuseStep 1689265 = 1266949) (by norm_num)
theorem B1500853 : Blo 1332985 1500853 := bbase (se 5 (by rfl) ⟨70352, by rfl⟩ : syracuseStep 1500853 = 140705) (by norm_num)
theorem B2000573 : Blo 1332985 2000573 := bbase (se 3 (by rfl) ⟨375107, by rfl⟩ : syracuseStep 2000573 = 750215) (by norm_num)
theorem B3376829 : Blo 1332985 3376829 := bbase (se 3 (by rfl) ⟨633155, by rfl⟩ : syracuseStep 3376829 = 1266311) (by norm_num)
theorem B3000005 : Blo 1332985 3000005 := bbase (se 4 (by rfl) ⟨281250, by rfl⟩ : syracuseStep 3000005 = 562501) (by norm_num)
theorem B2000597 : Blo 1332985 2000597 := bbase (se 7 (by rfl) ⟨23444, by rfl⟩ : syracuseStep 2000597 = 46889) (by norm_num)
theorem B1500889 : Blo 1332985 1500889 := bbase (se 2 (by rfl) ⟨562833, by rfl⟩ : syracuseStep 1500889 = 1125667) (by norm_num)
theorem B2000621 : Blo 1332985 2000621 := bbase (se 3 (by rfl) ⟨375116, by rfl⟩ : syracuseStep 2000621 = 750233) (by norm_num)
theorem B1500925 : Blo 1332985 1500925 := bbase (se 3 (by rfl) ⟨281423, by rfl⟩ : syracuseStep 1500925 = 562847) (by norm_num)
theorem B2000645 : Blo 1332985 2000645 := bbase (se 4 (by rfl) ⟨187560, by rfl⟩ : syracuseStep 2000645 = 375121) (by norm_num)
theorem B1804037 : Blo 1332985 1804037 := bbase (se 4 (by rfl) ⟨169128, by rfl⟩ : syracuseStep 1804037 = 338257) (by norm_num)
theorem B3000077 : Blo 1332985 3000077 := bbase (se 3 (by rfl) ⟨562514, by rfl⟩ : syracuseStep 3000077 = 1125029) (by norm_num)
theorem B2000669 : Blo 1332985 2000669 := bbase (se 3 (by rfl) ⟨375125, by rfl⟩ : syracuseStep 2000669 = 750251) (by norm_num)
theorem B1500961 : Blo 1332985 1500961 := bbase (se 2 (by rfl) ⟨562860, by rfl⟩ : syracuseStep 1500961 = 1125721) (by norm_num)
theorem B2000693 : Blo 1332985 2000693 := bbase (se 5 (by rfl) ⟨93782, by rfl⟩ : syracuseStep 2000693 = 187565) (by norm_num)
theorem B1500997 : Blo 1332985 1500997 := bbase (se 4 (by rfl) ⟨140718, by rfl⟩ : syracuseStep 1500997 = 281437) (by norm_num)
theorem B2000717 : Blo 1332985 2000717 := bbase (se 3 (by rfl) ⟨375134, by rfl⟩ : syracuseStep 2000717 = 750269) (by norm_num)
theorem B3000149 : Blo 1332985 3000149 := bbase (se 9 (by rfl) ⟨8789, by rfl⟩ : syracuseStep 3000149 = 17579) (by norm_num)
theorem B1689437 : Blo 1332985 1689437 := bbase (se 3 (by rfl) ⟨316769, by rfl⟩ : syracuseStep 1689437 = 633539) (by norm_num)
theorem B2000741 : Blo 1332985 2000741 := bbase (se 4 (by rfl) ⟨187569, by rfl⟩ : syracuseStep 2000741 = 375139) (by norm_num)
theorem B1501033 : Blo 1332985 1501033 := bbase (se 2 (by rfl) ⟨562887, by rfl⟩ : syracuseStep 1501033 = 1125775) (by norm_num)
theorem B2000765 : Blo 1332985 2000765 := bbase (se 3 (by rfl) ⟨375143, by rfl⟩ : syracuseStep 2000765 = 750287) (by norm_num)
theorem B4499333 : Blo 1332985 4499333 := bbase (se 4 (by rfl) ⟨421812, by rfl⟩ : syracuseStep 4499333 = 843625) (by norm_num)
theorem B1501069 : Blo 1332985 1501069 := bbase (se 3 (by rfl) ⟨281450, by rfl⟩ : syracuseStep 1501069 = 562901) (by norm_num)
theorem B2000789 : Blo 1332985 2000789 := bbase (se 6 (by rfl) ⟨46893, by rfl⟩ : syracuseStep 2000789 = 93787) (by norm_num)
theorem B1689493 : Blo 1332985 1689493 := bbase (se 6 (by rfl) ⟨39597, by rfl⟩ : syracuseStep 1689493 = 79195) (by norm_num)
theorem B3000221 : Blo 1332985 3000221 := bbase (se 3 (by rfl) ⟨562541, by rfl⟩ : syracuseStep 3000221 = 1125083) (by norm_num)
theorem B2000813 : Blo 1332985 2000813 := bbase (se 3 (by rfl) ⟨375152, by rfl⟩ : syracuseStep 2000813 = 750305) (by norm_num)
theorem B1804205 : Blo 1332985 1804205 := bbase (se 3 (by rfl) ⟨338288, by rfl⟩ : syracuseStep 1804205 = 676577) (by norm_num)
theorem B1501105 : Blo 1332985 1501105 := bbase (se 2 (by rfl) ⟨562914, by rfl⟩ : syracuseStep 1501105 = 1125829) (by norm_num)
theorem B2000837 : Blo 1332985 2000837 := bbase (se 4 (by rfl) ⟨187578, by rfl⟩ : syracuseStep 2000837 = 375157) (by norm_num)
theorem B1501141 : Blo 1332985 1501141 := bbase (se 7 (by rfl) ⟨17591, by rfl⟩ : syracuseStep 1501141 = 35183) (by norm_num)
theorem B2000861 : Blo 1332985 2000861 := bbase (se 3 (by rfl) ⟨375161, by rfl⟩ : syracuseStep 2000861 = 750323) (by norm_num)
theorem B1804253 : Blo 1332985 1804253 := bbase (se 3 (by rfl) ⟨338297, by rfl⟩ : syracuseStep 1804253 = 676595) (by norm_num)
theorem B3000293 : Blo 1332985 3000293 := bbase (se 4 (by rfl) ⟨281277, by rfl⟩ : syracuseStep 3000293 = 562555) (by norm_num)
theorem B2000885 : Blo 1332985 2000885 := bbase (se 5 (by rfl) ⟨93791, by rfl⟩ : syracuseStep 2000885 = 187583) (by norm_num)
theorem B1501177 : Blo 1332985 1501177 := bbase (se 2 (by rfl) ⟨562941, by rfl⟩ : syracuseStep 1501177 = 1125883) (by norm_num)
theorem B1689589 : Blo 1332985 1689589 := bbase (se 5 (by rfl) ⟨79199, by rfl⟩ : syracuseStep 1689589 = 158399) (by norm_num)
theorem B2000909 : Blo 1332985 2000909 := bbase (se 3 (by rfl) ⟨375170, by rfl⟩ : syracuseStep 2000909 = 750341) (by norm_num)
theorem B3377173 : Blo 1332985 3377173 := bbase (se 6 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 3377173 = 158305) (by norm_num)
theorem B1501213 : Blo 1332985 1501213 := bbase (se 3 (by rfl) ⟨281477, by rfl⟩ : syracuseStep 1501213 = 562955) (by norm_num)
theorem B2000933 : Blo 1332985 2000933 := bbase (se 4 (by rfl) ⟨187587, by rfl⟩ : syracuseStep 2000933 = 375175) (by norm_num)
theorem B3000365 : Blo 1332985 3000365 := bbase (se 3 (by rfl) ⟨562568, by rfl⟩ : syracuseStep 3000365 = 1125137) (by norm_num)
theorem B4565045 : Blo 1332985 4565045 := bbase (se 5 (by rfl) ⟨213986, by rfl⟩ : syracuseStep 4565045 = 427973) (by norm_num)
theorem B9750581 : Blo 1332985 9750581 := bbase (se 5 (by rfl) ⟨457058, by rfl⟩ : syracuseStep 9750581 = 914117) (by norm_num)
theorem B2000957 : Blo 1332985 2000957 := bbase (se 3 (by rfl) ⟨375179, by rfl⟩ : syracuseStep 2000957 = 750359) (by norm_num)
theorem B1501249 : Blo 1332985 1501249 := bbase (se 2 (by rfl) ⟨562968, by rfl⟩ : syracuseStep 1501249 = 1125937) (by norm_num)
theorem B2000981 : Blo 1332985 2000981 := bbase (se 8 (by rfl) ⟨11724, by rfl⟩ : syracuseStep 2000981 = 23449) (by norm_num)
theorem B1501285 : Blo 1332985 1501285 := bbase (se 4 (by rfl) ⟨140745, by rfl⟩ : syracuseStep 1501285 = 281491) (by norm_num)
theorem B2001005 : Blo 1332985 2001005 := bbase (se 3 (by rfl) ⟨375188, by rfl⟩ : syracuseStep 2001005 = 750377) (by norm_num)
theorem B3000437 : Blo 1332985 3000437 := bbase (se 5 (by rfl) ⟨140645, by rfl⟩ : syracuseStep 3000437 = 281291) (by norm_num)
theorem B2001029 : Blo 1332985 2001029 := bbase (se 4 (by rfl) ⟨187596, by rfl⟩ : syracuseStep 2001029 = 375193) (by norm_num)
theorem B3377285 : Blo 1332985 3377285 := bbase (se 4 (by rfl) ⟨316620, by rfl⟩ : syracuseStep 3377285 = 633241) (by norm_num)
theorem B1501321 : Blo 1332985 1501321 := bbase (se 2 (by rfl) ⟨562995, by rfl⟩ : syracuseStep 1501321 = 1125991) (by norm_num)
theorem B2435221 : Blo 1332985 2435221 := bbase (se 6 (by rfl) ⟨57075, by rfl⟩ : syracuseStep 2435221 = 114151) (by norm_num)
theorem B2001053 : Blo 1332985 2001053 := bbase (se 3 (by rfl) ⟨375197, by rfl⟩ : syracuseStep 2001053 = 750395) (by norm_num)
theorem B1501357 : Blo 1332985 1501357 := bbase (se 3 (by rfl) ⟨281504, by rfl⟩ : syracuseStep 1501357 = 563009) (by norm_num)
theorem B9742517 : Blo 1332985 9742517 := bbase (se 5 (by rfl) ⟨456680, by rfl⟩ : syracuseStep 9742517 = 913361) (by norm_num)
theorem B2001077 : Blo 1332985 2001077 := bbase (se 5 (by rfl) ⟨93800, by rfl⟩ : syracuseStep 2001077 = 187601) (by norm_num)
theorem B3000509 : Blo 1332985 3000509 := bbase (se 3 (by rfl) ⟨562595, by rfl⟩ : syracuseStep 3000509 = 1125191) (by norm_num)
theorem B2001101 : Blo 1332985 2001101 := bbase (se 3 (by rfl) ⟨375206, by rfl⟩ : syracuseStep 2001101 = 750413) (by norm_num)
theorem B1501393 : Blo 1332985 1501393 := bbase (se 2 (by rfl) ⟨563022, by rfl⟩ : syracuseStep 1501393 = 1126045) (by norm_num)
theorem B2001125 : Blo 1332985 2001125 := bbase (se 4 (by rfl) ⟨187605, by rfl⟩ : syracuseStep 2001125 = 375211) (by norm_num)
theorem B3467501 : Blo 1332985 3467501 := bbase (se 3 (by rfl) ⟨650156, by rfl⟩ : syracuseStep 3467501 = 1300313) (by norm_num)
theorem B1501429 : Blo 1332985 1501429 := bbase (se 5 (by rfl) ⟨70379, by rfl⟩ : syracuseStep 1501429 = 140759) (by norm_num)
theorem B2001149 : Blo 1332985 2001149 := bbase (se 3 (by rfl) ⟨375215, by rfl⟩ : syracuseStep 2001149 = 750431) (by norm_num)
theorem B3000581 : Blo 1332985 3000581 := bbase (se 4 (by rfl) ⟨281304, by rfl⟩ : syracuseStep 3000581 = 562609) (by norm_num)
theorem B2001173 : Blo 1332985 2001173 := bbase (se 6 (by rfl) ⟨46902, by rfl⟩ : syracuseStep 2001173 = 93805) (by norm_num)
theorem B1501465 : Blo 1332985 1501465 := bbase (se 2 (by rfl) ⟨563049, by rfl⟩ : syracuseStep 1501465 = 1126099) (by norm_num)
theorem B4057381 : Blo 1332985 4057381 := bbase (se 4 (by rfl) ⟨380379, by rfl⟩ : syracuseStep 4057381 = 760759) (by norm_num)
theorem B2468141 : Blo 1332985 2468141 := bbase (se 3 (by rfl) ⟨462776, by rfl⟩ : syracuseStep 2468141 = 925553) (by norm_num)
theorem B2001197 : Blo 1332985 2001197 := bbase (se 3 (by rfl) ⟨375224, by rfl⟩ : syracuseStep 2001197 = 750449) (by norm_num)
theorem B4499765 : Blo 1332985 4499765 := bbase (se 5 (by rfl) ⟨210926, by rfl⟩ : syracuseStep 4499765 = 421853) (by norm_num)
theorem B7596341 : Blo 1332985 7596341 := bbase (se 5 (by rfl) ⟨356078, by rfl⟩ : syracuseStep 7596341 = 712157) (by norm_num)
theorem B2533693 : Blo 1332985 2533693 := bbase (se 3 (by rfl) ⟨475067, by rfl⟩ : syracuseStep 2533693 = 950135) (by norm_num)
theorem B1501501 : Blo 1332985 1501501 := bbase (se 3 (by rfl) ⟨281531, by rfl⟩ : syracuseStep 1501501 = 563063) (by norm_num)
theorem B2001221 : Blo 1332985 2001221 := bbase (se 4 (by rfl) ⟨187614, by rfl⟩ : syracuseStep 2001221 = 375229) (by norm_num)
theorem B3377477 : Blo 1332985 3377477 := bbase (se 4 (by rfl) ⟨316638, by rfl⟩ : syracuseStep 3377477 = 633277) (by norm_num)
theorem B3000653 : Blo 1332985 3000653 := bbase (se 3 (by rfl) ⟨562622, by rfl⟩ : syracuseStep 3000653 = 1125245) (by norm_num)
theorem B2001245 : Blo 1332985 2001245 := bbase (se 3 (by rfl) ⟨375233, by rfl⟩ : syracuseStep 2001245 = 750467) (by norm_num)
theorem B1501537 : Blo 1332985 1501537 := bbase (se 2 (by rfl) ⟨563076, by rfl⟩ : syracuseStep 1501537 = 1126153) (by norm_num)
theorem B2001269 : Blo 1332985 2001269 := bbase (se 5 (by rfl) ⟨93809, by rfl⟩ : syracuseStep 2001269 = 187619) (by norm_num)
theorem B2886013 : Blo 1332985 2886013 := bbase (se 3 (by rfl) ⟨541127, by rfl⟩ : syracuseStep 2886013 = 1082255) (by norm_num)
theorem B6752645 : Blo 1332985 6752645 := bbase (se 4 (by rfl) ⟨633060, by rfl⟩ : syracuseStep 6752645 = 1266121) (by norm_num)
theorem B1501573 : Blo 1332985 1501573 := bbase (se 4 (by rfl) ⟨140772, by rfl⟩ : syracuseStep 1501573 = 281545) (by norm_num)
theorem B2001293 : Blo 1332985 2001293 := bbase (se 3 (by rfl) ⟨375242, by rfl⟩ : syracuseStep 2001293 = 750485) (by norm_num)
theorem B3467669 : Blo 1332985 3467669 := bbase (se 6 (by rfl) ⟨81273, by rfl⟩ : syracuseStep 3467669 = 162547) (by norm_num)
theorem B3000725 : Blo 1332985 3000725 := bbase (se 6 (by rfl) ⟨70329, by rfl⟩ : syracuseStep 3000725 = 140659) (by norm_num)
theorem B6097301 : Blo 1332985 6097301 := bbase (se 6 (by rfl) ⟨142905, by rfl⟩ : syracuseStep 6097301 = 285811) (by norm_num)
theorem B2001317 : Blo 1332985 2001317 := bbase (se 4 (by rfl) ⟨187623, by rfl⟩ : syracuseStep 2001317 = 375247) (by norm_num)
theorem B1501609 : Blo 1332985 1501609 := bbase (se 2 (by rfl) ⟨563103, by rfl⟩ : syracuseStep 1501609 = 1126207) (by norm_num)
theorem B2001341 : Blo 1332985 2001341 := bbase (se 3 (by rfl) ⟨375251, by rfl⟩ : syracuseStep 2001341 = 750503) (by norm_num)
theorem B2533837 : Blo 1332985 2533837 := bbase (se 3 (by rfl) ⟨475094, by rfl⟩ : syracuseStep 2533837 = 950189) (by norm_num)
theorem B1501645 : Blo 1332985 1501645 := bbase (se 3 (by rfl) ⟨281558, by rfl⟩ : syracuseStep 1501645 = 563117) (by norm_num)
theorem B2001365 : Blo 1332985 2001365 := bbase (se 7 (by rfl) ⟨23453, by rfl⟩ : syracuseStep 2001365 = 46907) (by norm_num)
theorem B3000797 : Blo 1332985 3000797 := bbase (se 3 (by rfl) ⟨562649, by rfl⟩ : syracuseStep 3000797 = 1125299) (by norm_num)
theorem B2001389 : Blo 1332985 2001389 := bbase (se 3 (by rfl) ⟨375260, by rfl⟩ : syracuseStep 2001389 = 750521) (by norm_num)
theorem B1501681 : Blo 1332985 1501681 := bbase (se 2 (by rfl) ⟨563130, by rfl⟩ : syracuseStep 1501681 = 1126261) (by norm_num)
theorem B2001413 : Blo 1332985 2001413 := bbase (se 4 (by rfl) ⟨187632, by rfl⟩ : syracuseStep 2001413 = 375265) (by norm_num)
theorem B1501717 : Blo 1332985 1501717 := bbase (se 6 (by rfl) ⟨35196, by rfl⟩ : syracuseStep 1501717 = 70393) (by norm_num)
theorem B2001437 : Blo 1332985 2001437 := bbase (se 3 (by rfl) ⟨375269, by rfl⟩ : syracuseStep 2001437 = 750539) (by norm_num)
theorem B3000869 : Blo 1332985 3000869 := bbase (se 4 (by rfl) ⟨281331, by rfl⟩ : syracuseStep 3000869 = 562663) (by norm_num)
theorem B2001461 : Blo 1332985 2001461 := bbase (se 5 (by rfl) ⟨93818, by rfl⟩ : syracuseStep 2001461 = 187637) (by norm_num)
theorem B1501753 : Blo 1332985 1501753 := bbase (se 2 (by rfl) ⟨563157, by rfl⟩ : syracuseStep 1501753 = 1126315) (by norm_num)
theorem B2001485 : Blo 1332985 2001485 := bbase (se 3 (by rfl) ⟨375278, by rfl⟩ : syracuseStep 2001485 = 750557) (by norm_num)
theorem B1501789 : Blo 1332985 1501789 := bbase (se 3 (by rfl) ⟨281585, by rfl⟩ : syracuseStep 1501789 = 563171) (by norm_num)
theorem B2001509 : Blo 1332985 2001509 := bbase (se 4 (by rfl) ⟨187641, by rfl⟩ : syracuseStep 2001509 = 375283) (by norm_num)
theorem B3000941 : Blo 1332985 3000941 := bbase (se 3 (by rfl) ⟨562676, by rfl⟩ : syracuseStep 3000941 = 1125353) (by norm_num)
theorem B2533997 : Blo 1332985 2533997 := bbase (se 3 (by rfl) ⟨475124, by rfl⟩ : syracuseStep 2533997 = 950249) (by norm_num)
theorem B8546933 : Blo 1332985 8546933 := bbase (se 5 (by rfl) ⟨400637, by rfl⟩ : syracuseStep 8546933 = 801275) (by norm_num)
theorem B2001533 : Blo 1332985 2001533 := bbase (se 3 (by rfl) ⟨375287, by rfl⟩ : syracuseStep 2001533 = 750575) (by norm_num)
theorem B1501825 : Blo 1332985 1501825 := bbase (se 2 (by rfl) ⟨563184, by rfl⟩ : syracuseStep 1501825 = 1126369) (by norm_num)
theorem B2001557 : Blo 1332985 2001557 := bbase (se 6 (by rfl) ⟨46911, by rfl⟩ : syracuseStep 2001557 = 93823) (by norm_num)
theorem B3377821 : Blo 1332985 3377821 := bbase (se 3 (by rfl) ⟨633341, by rfl⟩ : syracuseStep 3377821 = 1266683) (by norm_num)
theorem B2402989 : Blo 1332985 2402989 := bbase (se 3 (by rfl) ⟨450560, by rfl⟩ : syracuseStep 2402989 = 901121) (by norm_num)
theorem B2001581 : Blo 1332985 2001581 := bbase (se 3 (by rfl) ⟨375296, by rfl⟩ : syracuseStep 2001581 = 750593) (by norm_num)
theorem B3001013 : Blo 1332985 3001013 := bbase (se 5 (by rfl) ⟨140672, by rfl⟩ : syracuseStep 3001013 = 281345) (by norm_num)
theorem B2001605 : Blo 1332985 2001605 := bbase (se 4 (by rfl) ⟨187650, by rfl⟩ : syracuseStep 2001605 = 375301) (by norm_num)
theorem B2001629 : Blo 1332985 2001629 := bbase (se 3 (by rfl) ⟨375305, by rfl⟩ : syracuseStep 2001629 = 750611) (by norm_num)
theorem B4500197 : Blo 1332985 4500197 := bbase (se 4 (by rfl) ⟨421893, by rfl⟩ : syracuseStep 4500197 = 843787) (by norm_num)
theorem B2001653 : Blo 1332985 2001653 := bbase (se 5 (by rfl) ⟨93827, by rfl⟩ : syracuseStep 2001653 = 187655) (by norm_num)
theorem B3001085 : Blo 1332985 3001085 := bbase (se 3 (by rfl) ⟨562703, by rfl⟩ : syracuseStep 3001085 = 1125407) (by norm_num)
theorem B2534141 : Blo 1332985 2534141 := bbase (se 3 (by rfl) ⟨475151, by rfl⟩ : syracuseStep 2534141 = 950303) (by norm_num)
theorem B2001677 : Blo 1332985 2001677 := bbase (se 3 (by rfl) ⟨375314, by rfl⟩ : syracuseStep 2001677 = 750629) (by norm_num)
theorem B3377933 : Blo 1332985 3377933 := bbase (se 3 (by rfl) ⟨633362, by rfl⟩ : syracuseStep 3377933 = 1266725) (by norm_num)
theorem B2001701 : Blo 1332985 2001701 := bbase (se 4 (by rfl) ⟨187659, by rfl⟩ : syracuseStep 2001701 = 375319) (by norm_num)
theorem B2001725 : Blo 1332985 2001725 := bbase (se 3 (by rfl) ⟨375323, by rfl⟩ : syracuseStep 2001725 = 750647) (by norm_num)
theorem B3001157 : Blo 1332985 3001157 := bbase (se 4 (by rfl) ⟨281358, by rfl⟩ : syracuseStep 3001157 = 562717) (by norm_num)
theorem B2001749 : Blo 1332985 2001749 := bbase (se 9 (by rfl) ⟨5864, by rfl⟩ : syracuseStep 2001749 = 11729) (by norm_num)
theorem B1543009 : Blo 1332985 1543009 := bbase (se 2 (by rfl) ⟨578628, by rfl⟩ : syracuseStep 1543009 = 1157257) (by norm_num)
theorem B2001773 : Blo 1332985 2001773 := bbase (se 3 (by rfl) ⟨375332, by rfl⟩ : syracuseStep 2001773 = 750665) (by norm_num)
theorem B1444721 : Blo 1332985 1444721 := bbase (se 2 (by rfl) ⟨541770, by rfl⟩ : syracuseStep 1444721 = 1083541) (by norm_num)
theorem B2001797 : Blo 1332985 2001797 := bbase (se 4 (by rfl) ⟨187668, by rfl⟩ : syracuseStep 2001797 = 375337) (by norm_num)
theorem B3001229 : Blo 1332985 3001229 := bbase (se 3 (by rfl) ⟨562730, by rfl⟩ : syracuseStep 3001229 = 1125461) (by norm_num)
theorem B2001821 : Blo 1332985 2001821 := bbase (se 3 (by rfl) ⟨375341, by rfl⟩ : syracuseStep 2001821 = 750683) (by norm_num)
theorem B3795893 : Blo 1332985 3795893 := bbase (se 5 (by rfl) ⟨177932, by rfl⟩ : syracuseStep 3795893 = 355865) (by norm_num)
theorem B2001845 : Blo 1332985 2001845 := bbase (se 5 (by rfl) ⟨93836, by rfl⟩ : syracuseStep 2001845 = 187673) (by norm_num)
theorem B10136501 : Blo 1332985 10136501 := bbase (se 5 (by rfl) ⟨475148, by rfl⟩ : syracuseStep 10136501 = 950297) (by norm_num)
theorem B3378125 : Blo 1332985 3378125 := bbase (se 3 (by rfl) ⟨633398, by rfl⟩ : syracuseStep 3378125 = 1266797) (by norm_num)
theorem B2001869 : Blo 1332985 2001869 := bbase (se 3 (by rfl) ⟨375350, by rfl⟩ : syracuseStep 2001869 = 750701) (by norm_num)
theorem B3001301 : Blo 1332985 3001301 := bbase (se 7 (by rfl) ⟨35171, by rfl⟩ : syracuseStep 3001301 = 70343) (by norm_num)
theorem B5065685 : Blo 1332985 5065685 := bbase (se 7 (by rfl) ⟨59363, by rfl⟩ : syracuseStep 5065685 = 118727) (by norm_num)
theorem B1444825 : Blo 1332985 1444825 := bbase (se 2 (by rfl) ⟨541809, by rfl⟩ : syracuseStep 1444825 = 1083619) (by norm_num)
theorem B2001893 : Blo 1332985 2001893 := bbase (se 4 (by rfl) ⟨187677, by rfl⟩ : syracuseStep 2001893 = 375355) (by norm_num)
theorem B2001917 : Blo 1332985 2001917 := bbase (se 3 (by rfl) ⟨375359, by rfl⟩ : syracuseStep 2001917 = 750719) (by norm_num)
theorem B2001941 : Blo 1332985 2001941 := bbase (se 6 (by rfl) ⟨46920, by rfl⟩ : syracuseStep 2001941 = 93841) (by norm_num)
theorem B3001373 : Blo 1332985 3001373 := bbase (se 3 (by rfl) ⟨562757, by rfl⟩ : syracuseStep 3001373 = 1125515) (by norm_num)
theorem B2001965 : Blo 1332985 2001965 := bbase (se 3 (by rfl) ⟨375368, by rfl⟩ : syracuseStep 2001965 = 750737) (by norm_num)
theorem B2001989 : Blo 1332985 2001989 := bbase (se 4 (by rfl) ⟨187686, by rfl⟩ : syracuseStep 2001989 = 375373) (by norm_num)
theorem B2002013 : Blo 1332985 2002013 := bbase (se 3 (by rfl) ⟨375377, by rfl⟩ : syracuseStep 2002013 = 750755) (by norm_num)
theorem B3001445 : Blo 1332985 3001445 := bbase (se 4 (by rfl) ⟨281385, by rfl⟩ : syracuseStep 3001445 = 562771) (by norm_num)
theorem B3206245 : Blo 1332985 3206245 := bbase (se 4 (by rfl) ⟨300585, by rfl⟩ : syracuseStep 3206245 = 601171) (by norm_num)
theorem B3796085 : Blo 1332985 3796085 := bbase (se 5 (by rfl) ⟨177941, by rfl⟩ : syracuseStep 3796085 = 355883) (by norm_num)
theorem B2002037 : Blo 1332985 2002037 := bbase (se 5 (by rfl) ⟨93845, by rfl⟩ : syracuseStep 2002037 = 187691) (by norm_num)
theorem B3083405 : Blo 1332985 3083405 := bbase (se 3 (by rfl) ⟨578138, by rfl⟩ : syracuseStep 3083405 = 1156277) (by norm_num)
theorem B2002061 : Blo 1332985 2002061 := bbase (se 3 (by rfl) ⟨375386, by rfl⟩ : syracuseStep 2002061 = 750773) (by norm_num)
theorem B4500629 : Blo 1332985 4500629 := bbase (se 6 (by rfl) ⟨105483, by rfl⟩ : syracuseStep 4500629 = 210967) (by norm_num)
theorem B4942997 : Blo 1332985 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B2002085 : Blo 1332985 2002085 := bbase (se 4 (by rfl) ⟨187695, by rfl⟩ : syracuseStep 2002085 = 375391) (by norm_num)
theorem B3001517 : Blo 1332985 3001517 := bbase (se 3 (by rfl) ⟨562784, by rfl⟩ : syracuseStep 3001517 = 1125569) (by norm_num)
theorem B2002109 : Blo 1332985 2002109 := bbase (se 3 (by rfl) ⟨375395, by rfl⟩ : syracuseStep 2002109 = 750791) (by norm_num)
theorem B5696725 : Blo 1332985 5696725 := bbase (se 7 (by rfl) ⟨66758, by rfl⟩ : syracuseStep 5696725 = 133517) (by norm_num)
theorem B2002133 : Blo 1332985 2002133 := bbase (se 7 (by rfl) ⟨23462, by rfl⟩ : syracuseStep 2002133 = 46925) (by norm_num)
theorem B2002157 : Blo 1332985 2002157 := bbase (se 3 (by rfl) ⟨375404, by rfl⟩ : syracuseStep 2002157 = 750809) (by norm_num)
theorem B9612533 : Blo 1332985 9612533 := bbase (se 5 (by rfl) ⟨450587, by rfl⟩ : syracuseStep 9612533 = 901175) (by norm_num)
theorem B3001589 : Blo 1332985 3001589 := bbase (se 5 (by rfl) ⟨140699, by rfl⟩ : syracuseStep 3001589 = 281399) (by norm_num)
theorem B5065973 : Blo 1332985 5065973 := bbase (se 5 (by rfl) ⟨237467, by rfl⟩ : syracuseStep 5065973 = 474935) (by norm_num)
theorem B2084093 : Blo 1332985 2084093 := bbase (se 3 (by rfl) ⟨390767, by rfl⟩ : syracuseStep 2084093 = 781535) (by norm_num)
theorem B2002181 : Blo 1332985 2002181 := bbase (se 4 (by rfl) ⟨187704, by rfl⟩ : syracuseStep 2002181 = 375409) (by norm_num)
theorem B2002205 : Blo 1332985 2002205 := bbase (se 3 (by rfl) ⟨375413, by rfl⟩ : syracuseStep 2002205 = 750827) (by norm_num)
theorem B4164901 : Blo 1332985 4164901 := bbase (se 4 (by rfl) ⟨390459, by rfl⟩ : syracuseStep 4164901 = 780919) (by norm_num)
theorem B3378469 : Blo 1332985 3378469 := bbase (se 4 (by rfl) ⟨316731, by rfl⟩ : syracuseStep 3378469 = 633463) (by norm_num)
theorem B2002229 : Blo 1332985 2002229 := bbase (se 5 (by rfl) ⟨93854, by rfl⟩ : syracuseStep 2002229 = 187709) (by norm_num)
theorem B3001661 : Blo 1332985 3001661 := bbase (se 3 (by rfl) ⟨562811, by rfl⟩ : syracuseStep 3001661 = 1125623) (by norm_num)
theorem B2002253 : Blo 1332985 2002253 := bbase (se 3 (by rfl) ⟨375422, by rfl⟩ : syracuseStep 2002253 = 750845) (by norm_num)
theorem B10128725 : Blo 1332985 10128725 := bbase (se 11 (by rfl) ⟨7418, by rfl⟩ : syracuseStep 10128725 = 14837) (by norm_num)
theorem B2002277 : Blo 1332985 2002277 := bbase (se 4 (by rfl) ⟨187713, by rfl⟩ : syracuseStep 2002277 = 375427) (by norm_num)
theorem B2567533 : Blo 1332985 2567533 := bbase (se 3 (by rfl) ⟨481412, by rfl⟩ : syracuseStep 2567533 = 962825) (by norm_num)
theorem B2002301 : Blo 1332985 2002301 := bbase (se 3 (by rfl) ⟨375431, by rfl⟩ : syracuseStep 2002301 = 750863) (by norm_num)
theorem B3001733 : Blo 1332985 3001733 := bbase (se 4 (by rfl) ⟨281412, by rfl⟩ : syracuseStep 3001733 = 562825) (by norm_num)
theorem B3378581 : Blo 1332985 3378581 := bbase (se 6 (by rfl) ⟨79185, by rfl⟩ : syracuseStep 3378581 = 158371) (by norm_num)
theorem B2002325 : Blo 1332985 2002325 := bbase (se 6 (by rfl) ⟨46929, by rfl⟩ : syracuseStep 2002325 = 93859) (by norm_num)
theorem B2002349 : Blo 1332985 2002349 := bbase (se 3 (by rfl) ⟨375440, by rfl⟩ : syracuseStep 2002349 = 750881) (by norm_num)
theorem B2002373 : Blo 1332985 2002373 := bbase (se 4 (by rfl) ⟨187722, by rfl⟩ : syracuseStep 2002373 = 375445) (by norm_num)
theorem B3001805 : Blo 1332985 3001805 := bbase (se 3 (by rfl) ⟨562838, by rfl⟩ : syracuseStep 3001805 = 1125677) (by norm_num)
theorem B2002397 : Blo 1332985 2002397 := bbase (se 3 (by rfl) ⟨375449, by rfl⟩ : syracuseStep 2002397 = 750899) (by norm_num)
theorem B2002421 : Blo 1332985 2002421 := bbase (se 5 (by rfl) ⟨93863, by rfl⟩ : syracuseStep 2002421 = 187727) (by norm_num)
theorem B4271621 : Blo 1332985 4271621 := bbase (se 4 (by rfl) ⟨400464, by rfl⟩ : syracuseStep 4271621 = 800929) (by norm_num)
theorem B2002445 : Blo 1332985 2002445 := bbase (se 3 (by rfl) ⟨375458, by rfl⟩ : syracuseStep 2002445 = 750917) (by norm_num)
theorem B3001877 : Blo 1332985 3001877 := bbase (se 6 (by rfl) ⟨70356, by rfl⟩ : syracuseStep 3001877 = 140713) (by norm_num)
theorem B2002469 : Blo 1332985 2002469 := bbase (se 4 (by rfl) ⟨187731, by rfl⟩ : syracuseStep 2002469 = 375463) (by norm_num)
theorem B4501061 : Blo 1332985 4501061 := bbase (se 4 (by rfl) ⟨421974, by rfl⟩ : syracuseStep 4501061 = 843949) (by norm_num)
theorem B3378773 : Blo 1332985 3378773 := bbase (se 8 (by rfl) ⟨19797, by rfl⟩ : syracuseStep 3378773 = 39595) (by norm_num)
theorem B3001949 : Blo 1332985 3001949 := bbase (se 3 (by rfl) ⟨562865, by rfl⟩ : syracuseStep 3001949 = 1125731) (by norm_num)
theorem B6753941 : Blo 1332985 6753941 := bbase (se 6 (by rfl) ⟨158295, by rfl⟩ : syracuseStep 6753941 = 316591) (by norm_num)
theorem B3002021 : Blo 1332985 3002021 := bbase (se 4 (by rfl) ⟨281439, by rfl⟩ : syracuseStep 3002021 = 562879) (by norm_num)
theorem B3206861 : Blo 1332985 3206861 := bbase (se 3 (by rfl) ⟨601286, by rfl⟩ : syracuseStep 3206861 = 1202573) (by norm_num)
theorem B3002093 : Blo 1332985 3002093 := bbase (se 3 (by rfl) ⟨562892, by rfl⟩ : syracuseStep 3002093 = 1125785) (by norm_num)
theorem B3002165 : Blo 1332985 3002165 := bbase (se 5 (by rfl) ⟨140726, by rfl⟩ : syracuseStep 3002165 = 281453) (by norm_num)
theorem B3002237 : Blo 1332985 3002237 := bbase (se 3 (by rfl) ⟨562919, by rfl⟩ : syracuseStep 3002237 = 1125839) (by norm_num)
theorem B3207061 : Blo 1332985 3207061 := bbase (se 6 (by rfl) ⟨75165, by rfl⟩ : syracuseStep 3207061 = 150331) (by norm_num)
theorem B3379117 : Blo 1332985 3379117 := bbase (se 3 (by rfl) ⟨633584, by rfl⟩ : syracuseStep 3379117 = 1267169) (by norm_num)
theorem B3002309 : Blo 1332985 3002309 := bbase (se 4 (by rfl) ⟨281466, by rfl⟩ : syracuseStep 3002309 = 562933) (by norm_num)
theorem B4501493 : Blo 1332985 4501493 := bbase (se 5 (by rfl) ⟨211007, by rfl⟩ : syracuseStep 4501493 = 422015) (by norm_num)
theorem B3002381 : Blo 1332985 3002381 := bbase (se 3 (by rfl) ⟨562946, by rfl⟩ : syracuseStep 3002381 = 1125893) (by norm_num)
theorem B2404397 : Blo 1332985 2404397 := bbase (se 3 (by rfl) ⟨450824, by rfl⟩ : syracuseStep 2404397 = 901649) (by norm_num)
theorem B3797077 : Blo 1332985 3797077 := bbase (se 8 (by rfl) ⟨22248, by rfl⟩ : syracuseStep 3797077 = 44497) (by norm_num)
theorem B3002453 : Blo 1332985 3002453 := bbase (se 8 (by rfl) ⟨17592, by rfl⟩ : syracuseStep 3002453 = 35185) (by norm_num)
theorem B2404453 : Blo 1332985 2404453 := bbase (se 4 (by rfl) ⟨225417, by rfl⟩ : syracuseStep 2404453 = 450835) (by norm_num)
theorem B2281621 : Blo 1332985 2281621 := bbase (se 6 (by rfl) ⟨53475, by rfl⟩ : syracuseStep 2281621 = 106951) (by norm_num)
theorem B3002525 : Blo 1332985 3002525 := bbase (se 3 (by rfl) ⟨562973, by rfl⟩ : syracuseStep 3002525 = 1125947) (by norm_num)
theorem B3002597 : Blo 1332985 3002597 := bbase (se 4 (by rfl) ⟨281493, by rfl⟩ : syracuseStep 3002597 = 562987) (by norm_num)
theorem B3002669 : Blo 1332985 3002669 := bbase (se 3 (by rfl) ⟨563000, by rfl⟩ : syracuseStep 3002669 = 1126001) (by norm_num)
theorem B2601269 : Blo 1332985 2601269 := bbase (se 5 (by rfl) ⟨121934, by rfl⟩ : syracuseStep 2601269 = 243869) (by norm_num)
theorem B2167133 : Blo 1332985 2167133 := bbase (se 3 (by rfl) ⟨406337, by rfl⟩ : syracuseStep 2167133 = 812675) (by norm_num)
theorem B3002741 : Blo 1332985 3002741 := bbase (se 5 (by rfl) ⟨140753, by rfl⟩ : syracuseStep 3002741 = 281507) (by norm_num)
theorem B2281861 : Blo 1332985 2281861 := bbase (se 4 (by rfl) ⟨213924, by rfl⟩ : syracuseStep 2281861 = 427849) (by norm_num)
theorem B4272533 : Blo 1332985 4272533 := bbase (se 6 (by rfl) ⟨100137, by rfl⟩ : syracuseStep 4272533 = 200275) (by norm_num)
theorem B2847125 : Blo 1332985 2847125 := bbase (se 6 (by rfl) ⟨66729, by rfl⟩ : syracuseStep 2847125 = 133459) (by norm_num)
theorem B5067157 : Blo 1332985 5067157 := bbase (se 6 (by rfl) ⟨118761, by rfl⟩ : syracuseStep 5067157 = 237523) (by norm_num)
theorem B4501925 : Blo 1332985 4501925 := bbase (se 4 (by rfl) ⟨422055, by rfl⟩ : syracuseStep 4501925 = 844111) (by norm_num)
theorem B12825013 : Blo 1332985 12825013 := bbase (se 5 (by rfl) ⟨601172, by rfl⟩ : syracuseStep 12825013 = 1202345) (by norm_num)
theorem B11121077 : Blo 1332985 11121077 := bbase (se 5 (by rfl) ⟨521300, by rfl⟩ : syracuseStep 11121077 = 1042601) (by norm_num)
theorem B3420605 : Blo 1332985 3420605 := bbase (se 3 (by rfl) ⟨641363, by rfl⟩ : syracuseStep 3420605 = 1282727) (by norm_num)
theorem B3002813 : Blo 1332985 3002813 := bbase (se 3 (by rfl) ⟨563027, by rfl⟩ : syracuseStep 3002813 = 1126055) (by norm_num)
theorem B7598549 : Blo 1332985 7598549 := bbase (se 7 (by rfl) ⟨89045, by rfl⟩ : syracuseStep 7598549 = 178091) (by norm_num)
theorem B3002885 : Blo 1332985 3002885 := bbase (se 4 (by rfl) ⟨281520, by rfl⟩ : syracuseStep 3002885 = 563041) (by norm_num)
theorem B2847269 : Blo 1332985 2847269 := bbase (se 4 (by rfl) ⟨266931, by rfl⟩ : syracuseStep 2847269 = 533863) (by norm_num)
theorem B3002957 : Blo 1332985 3002957 := bbase (se 3 (by rfl) ⟨563054, by rfl⟩ : syracuseStep 3002957 = 1126109) (by norm_num)
theorem B1602137 : Blo 1332985 1602137 := bbase (se 2 (by rfl) ⟨600801, by rfl⟩ : syracuseStep 1602137 = 1201603) (by norm_num)
theorem B3003029 : Blo 1332985 3003029 := bbase (se 6 (by rfl) ⟨70383, by rfl⟩ : syracuseStep 3003029 = 140767) (by norm_num)
theorem B5067461 : Blo 1332985 5067461 := bbase (se 4 (by rfl) ⟨475074, by rfl⟩ : syracuseStep 5067461 = 950149) (by norm_num)
theorem B2249437 : Blo 1332985 2249437 := bbase (se 3 (by rfl) ⟨421769, by rfl⟩ : syracuseStep 2249437 = 843539) (by norm_num)
theorem B3003101 : Blo 1332985 3003101 := bbase (se 3 (by rfl) ⟨563081, by rfl⟩ : syracuseStep 3003101 = 1126163) (by norm_num)
theorem B1520365 : Blo 1332985 1520365 := bbase (se 3 (by rfl) ⟨285068, by rfl⟩ : syracuseStep 1520365 = 570137) (by norm_num)
theorem B2028325 : Blo 1332985 2028325 := bbase (se 4 (by rfl) ⟨190155, by rfl⟩ : syracuseStep 2028325 = 380311) (by norm_num)
theorem B3003173 : Blo 1332985 3003173 := bbase (se 4 (by rfl) ⟨281547, by rfl⟩ : syracuseStep 3003173 = 563095) (by norm_num)
theorem B2249525 : Blo 1332985 2249525 := bbase (se 5 (by rfl) ⟨105446, by rfl⟩ : syracuseStep 2249525 = 210893) (by norm_num)
theorem B4502357 : Blo 1332985 4502357 := bbase (se 9 (by rfl) ⟨13190, by rfl⟩ : syracuseStep 4502357 = 26381) (by norm_num)
theorem B3003245 : Blo 1332985 3003245 := bbase (se 3 (by rfl) ⟨563108, by rfl⟩ : syracuseStep 3003245 = 1126217) (by norm_num)
theorem B2847629 : Blo 1332985 2847629 := bbase (se 3 (by rfl) ⟨533930, by rfl⟩ : syracuseStep 2847629 = 1067861) (by norm_num)
theorem B1602445 : Blo 1332985 1602445 := bbase (se 3 (by rfl) ⟨300458, by rfl⟩ : syracuseStep 1602445 = 600917) (by norm_num)
theorem B6755237 : Blo 1332985 6755237 := bbase (se 4 (by rfl) ⟨633303, by rfl⟩ : syracuseStep 6755237 = 1266607) (by norm_num)
theorem B1602473 : Blo 1332985 1602473 := bbase (se 2 (by rfl) ⟨600927, by rfl⟩ : syracuseStep 1602473 = 1201855) (by norm_num)
theorem B2249653 : Blo 1332985 2249653 := bbase (se 5 (by rfl) ⟨105452, by rfl⟩ : syracuseStep 2249653 = 210905) (by norm_num)
theorem B3003317 : Blo 1332985 3003317 := bbase (se 5 (by rfl) ⟨140780, by rfl⟩ : syracuseStep 3003317 = 281561) (by norm_num)
theorem B3003389 : Blo 1332985 3003389 := bbase (se 3 (by rfl) ⟨563135, by rfl⟩ : syracuseStep 3003389 = 1126271) (by norm_num)
theorem B2249741 : Blo 1332985 2249741 := bbase (se 3 (by rfl) ⟨421826, by rfl⟩ : syracuseStep 2249741 = 843653) (by norm_num)
theorem B3003461 : Blo 1332985 3003461 := bbase (se 4 (by rfl) ⟨281574, by rfl⟩ : syracuseStep 3003461 = 563149) (by norm_num)
theorem B2249869 : Blo 1332985 2249869 := bbase (se 3 (by rfl) ⟨421850, by rfl⟩ : syracuseStep 2249869 = 843701) (by norm_num)
theorem B3003533 : Blo 1332985 3003533 := bbase (se 3 (by rfl) ⟨563162, by rfl⟩ : syracuseStep 3003533 = 1126325) (by norm_num)
theorem B3798181 : Blo 1332985 3798181 := bbase (se 4 (by rfl) ⟨356079, by rfl⟩ : syracuseStep 3798181 = 712159) (by norm_num)
theorem B3003605 : Blo 1332985 3003605 := bbase (se 7 (by rfl) ⟨35198, by rfl⟩ : syracuseStep 3003605 = 70397) (by norm_num)
theorem B2249957 : Blo 1332985 2249957 := bbase (se 4 (by rfl) ⟨210933, by rfl⟩ : syracuseStep 2249957 = 421867) (by norm_num)
theorem B4502789 : Blo 1332985 4502789 := bbase (se 4 (by rfl) ⟨422136, by rfl⟩ : syracuseStep 4502789 = 844273) (by norm_num)
theorem B3003677 : Blo 1332985 3003677 := bbase (se 3 (by rfl) ⟨563189, by rfl⟩ : syracuseStep 3003677 = 1126379) (by norm_num)
theorem B2250085 : Blo 1332985 2250085 := bbase (se 4 (by rfl) ⟨210945, by rfl⟩ : syracuseStep 2250085 = 421891) (by norm_num)
theorem B1602973 : Blo 1332985 1602973 := bbase (se 3 (by rfl) ⟨300557, by rfl⟩ : syracuseStep 1602973 = 601115) (by norm_num)
theorem B2250173 : Blo 1332985 2250173 := bbase (se 3 (by rfl) ⟨421907, by rfl⟩ : syracuseStep 2250173 = 843815) (by norm_num)
theorem B1897997 : Blo 1332985 1897997 := bbase (se 3 (by rfl) ⟨355874, by rfl⟩ : syracuseStep 1897997 = 711749) (by norm_num)
theorem B2250301 : Blo 1332985 2250301 := bbase (se 3 (by rfl) ⟨421931, by rfl⟩ : syracuseStep 2250301 = 843863) (by norm_num)
theorem B1521217 : Blo 1332985 1521217 := bbase (se 2 (by rfl) ⟨570456, by rfl⟩ : syracuseStep 1521217 = 1140913) (by norm_num)
theorem B2250389 : Blo 1332985 2250389 := bbase (se 6 (by rfl) ⟨52743, by rfl⟩ : syracuseStep 2250389 = 105487) (by norm_num)
theorem B4503221 : Blo 1332985 4503221 := bbase (se 5 (by rfl) ⟨211088, by rfl⟩ : syracuseStep 4503221 = 422177) (by norm_num)
theorem B4273877 : Blo 1332985 4273877 := bbase (se 7 (by rfl) ⟨50084, by rfl⟩ : syracuseStep 4273877 = 100169) (by norm_num)
theorem B2848517 : Blo 1332985 2848517 := bbase (se 4 (by rfl) ⟨267048, by rfl⟩ : syracuseStep 2848517 = 534097) (by norm_num)
theorem B2250517 : Blo 1332985 2250517 := bbase (se 6 (by rfl) ⟨52746, by rfl⟩ : syracuseStep 2250517 = 105493) (by norm_num)
theorem B5412629 : Blo 1332985 5412629 := bbase (se 6 (by rfl) ⟨126858, by rfl⟩ : syracuseStep 5412629 = 253717) (by norm_num)
theorem B2250605 : Blo 1332985 2250605 := bbase (se 3 (by rfl) ⟨421988, by rfl⟩ : syracuseStep 2250605 = 843977) (by norm_num)
theorem B2135965 : Blo 1332985 2135965 := bbase (se 3 (by rfl) ⟨400493, by rfl⟩ : syracuseStep 2135965 = 800987) (by norm_num)
theorem B2250733 : Blo 1332985 2250733 := bbase (se 3 (by rfl) ⟨422012, by rfl⟩ : syracuseStep 2250733 = 844025) (by norm_num)
theorem B6412277 : Blo 1332985 6412277 := bbase (se 5 (by rfl) ⟨300575, by rfl⟩ : syracuseStep 6412277 = 601151) (by norm_num)
theorem B2136061 : Blo 1332985 2136061 := bbase (se 3 (by rfl) ⟨400511, by rfl⟩ : syracuseStep 2136061 = 801023) (by norm_num)
theorem B2848765 : Blo 1332985 2848765 := bbase (se 3 (by rfl) ⟨534143, by rfl⟩ : syracuseStep 2848765 = 1068287) (by norm_num)
theorem B2250821 : Blo 1332985 2250821 := bbase (se 4 (by rfl) ⟨211014, by rfl⟩ : syracuseStep 2250821 = 422029) (by norm_num)
theorem B4110421 : Blo 1332985 4110421 := bbase (se 8 (by rfl) ⟨24084, by rfl⟩ : syracuseStep 4110421 = 48169) (by norm_num)
theorem B4503653 : Blo 1332985 4503653 := bbase (se 4 (by rfl) ⟨422217, by rfl⟩ : syracuseStep 4503653 = 844435) (by norm_num)
theorem B5699717 : Blo 1332985 5699717 := bbase (se 4 (by rfl) ⟨534348, by rfl⟩ : syracuseStep 5699717 = 1068697) (by norm_num)
theorem B2136221 : Blo 1332985 2136221 := bbase (se 3 (by rfl) ⟨400541, by rfl⟩ : syracuseStep 2136221 = 801083) (by norm_num)
theorem B1423541 : Blo 1332985 1423541 := bbase (se 5 (by rfl) ⟨66728, by rfl⟩ : syracuseStep 1423541 = 133457) (by norm_num)
theorem B6756533 : Blo 1332985 6756533 := bbase (se 5 (by rfl) ⟨316712, by rfl⟩ : syracuseStep 6756533 = 633425) (by norm_num)
theorem B2250949 : Blo 1332985 2250949 := bbase (se 4 (by rfl) ⟨211026, by rfl⟩ : syracuseStep 2250949 = 422053) (by norm_num)
theorem B4806901 : Blo 1332985 4806901 := bbase (se 5 (by rfl) ⟨225323, by rfl⟩ : syracuseStep 4806901 = 450647) (by norm_num)
theorem B1898749 : Blo 1332985 1898749 := bbase (se 3 (by rfl) ⟨356015, by rfl⟩ : syracuseStep 1898749 = 712031) (by norm_num)
theorem B2251037 : Blo 1332985 2251037 := bbase (se 3 (by rfl) ⟨422069, by rfl⟩ : syracuseStep 2251037 = 844139) (by norm_num)
theorem B6412661 : Blo 1332985 6412661 := bbase (se 5 (by rfl) ⟨300593, by rfl⟩ : syracuseStep 6412661 = 601187) (by norm_num)
theorem B8550805 : Blo 1332985 8550805 := bbase (se 6 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 8550805 = 400819) (by norm_num)
theorem B2251165 : Blo 1332985 2251165 := bbase (se 3 (by rfl) ⟨422093, by rfl⟩ : syracuseStep 2251165 = 844187) (by norm_num)
theorem B3422677 : Blo 1332985 3422677 := bbase (se 7 (by rfl) ⟨40109, by rfl⟩ : syracuseStep 3422677 = 80219) (by norm_num)
theorem B2251253 : Blo 1332985 2251253 := bbase (se 5 (by rfl) ⟨105527, by rfl⟩ : syracuseStep 2251253 = 211055) (by norm_num)
theorem B2849269 : Blo 1332985 2849269 := bbase (se 5 (by rfl) ⟨133559, by rfl⟩ : syracuseStep 2849269 = 267119) (by norm_num)
theorem B4504085 : Blo 1332985 4504085 := bbase (se 6 (by rfl) ⟨105564, by rfl⟩ : syracuseStep 4504085 = 211129) (by norm_num)
theorem B6748757 : Blo 1332985 6748757 := bbase (se 8 (by rfl) ⟨39543, by rfl⟩ : syracuseStep 6748757 = 79087) (by norm_num)
theorem B1423985 : Blo 1332985 1423985 := bbase (se 2 (by rfl) ⟨533994, by rfl⟩ : syracuseStep 1423985 = 1067989) (by norm_num)
theorem B2251381 : Blo 1332985 2251381 := bbase (se 5 (by rfl) ⟨105533, by rfl⟩ : syracuseStep 2251381 = 211067) (by norm_num)
theorem B3799685 : Blo 1332985 3799685 := bbase (se 4 (by rfl) ⟨356220, by rfl⟩ : syracuseStep 3799685 = 712441) (by norm_num)
theorem B5077637 : Blo 1332985 5077637 := bbase (se 4 (by rfl) ⟨476028, by rfl⟩ : syracuseStep 5077637 = 952057) (by norm_num)
theorem B2603677 : Blo 1332985 2603677 := bbase (se 3 (by rfl) ⟨488189, by rfl⟩ : syracuseStep 2603677 = 976379) (by norm_num)
theorem B4111013 : Blo 1332985 4111013 := bbase (se 4 (by rfl) ⟨385407, by rfl⟩ : syracuseStep 4111013 = 770815) (by norm_num)
theorem B2251469 : Blo 1332985 2251469 := bbase (se 3 (by rfl) ⟨422150, by rfl⟩ : syracuseStep 2251469 = 844301) (by norm_num)
theorem B2251597 : Blo 1332985 2251597 := bbase (se 3 (by rfl) ⟨422174, by rfl⟩ : syracuseStep 2251597 = 844349) (by norm_num)
theorem B1424233 : Blo 1332985 1424233 := bbase (se 2 (by rfl) ⟨534087, by rfl⟩ : syracuseStep 1424233 = 1068175) (by norm_num)
theorem B1923997 : Blo 1332985 1923997 := bbase (se 3 (by rfl) ⟨360749, by rfl⟩ : syracuseStep 1923997 = 721499) (by norm_num)
theorem B2251685 : Blo 1332985 2251685 := bbase (se 4 (by rfl) ⟨211095, by rfl⟩ : syracuseStep 2251685 = 422191) (by norm_num)
theorem B4504517 : Blo 1332985 4504517 := bbase (se 4 (by rfl) ⟨422298, by rfl⟩ : syracuseStep 4504517 = 844597) (by norm_num)
theorem B1899541 : Blo 1332985 1899541 := bbase (se 6 (by rfl) ⟨44520, by rfl⟩ : syracuseStep 1899541 = 89041) (by norm_num)
theorem B2251813 : Blo 1332985 2251813 := bbase (se 4 (by rfl) ⟨211107, by rfl⟩ : syracuseStep 2251813 = 422215) (by norm_num)
theorem B3423293 : Blo 1332985 3423293 := bbase (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) (by norm_num)
theorem B4275301 : Blo 1332985 4275301 := bbase (se 4 (by rfl) ⟨400809, by rfl⟩ : syracuseStep 4275301 = 801619) (by norm_num)
theorem B5700725 : Blo 1332985 5700725 := bbase (se 5 (by rfl) ⟨267221, by rfl⟩ : syracuseStep 5700725 = 534443) (by norm_num)
theorem B2251901 : Blo 1332985 2251901 := bbase (se 3 (by rfl) ⟨422231, by rfl⟩ : syracuseStep 2251901 = 844463) (by norm_num)
theorem B3374237 : Blo 1332985 3374237 := bbase (se 3 (by rfl) ⟨632669, by rfl⟩ : syracuseStep 3374237 = 1265339) (by norm_num)
theorem B5061797 : Blo 1332985 5061797 := bbase (se 4 (by rfl) ⟨474543, by rfl⟩ : syracuseStep 5061797 = 949087) (by norm_num)
theorem B7699637 : Blo 1332985 7699637 := bbase (se 5 (by rfl) ⟨360920, by rfl⟩ : syracuseStep 7699637 = 721841) (by norm_num)
theorem B7593173 : Blo 1332985 7593173 := bbase (se 7 (by rfl) ⟨88982, by rfl⟩ : syracuseStep 7593173 = 177965) (by norm_num)
theorem B2252029 : Blo 1332985 2252029 := bbase (se 3 (by rfl) ⟨422255, by rfl⟩ : syracuseStep 2252029 = 844511) (by norm_num)
theorem B2137349 : Blo 1332985 2137349 := bbase (se 4 (by rfl) ⟨200376, by rfl⟩ : syracuseStep 2137349 = 400753) (by norm_num)
theorem B7306517 : Blo 1332985 7306517 := bbase (se 6 (by rfl) ⟨171246, by rfl⟩ : syracuseStep 7306517 = 342493) (by norm_num)
theorem B1424677 : Blo 1332985 1424677 := bbase (se 4 (by rfl) ⟨133563, by rfl⟩ : syracuseStep 1424677 = 267127) (by norm_num)
theorem B1711441 : Blo 1332985 1711441 := bbase (se 2 (by rfl) ⟨641790, by rfl⟩ : syracuseStep 1711441 = 1283581) (by norm_num)
theorem B17096021 : Blo 1332985 17096021 := bbase (se 11 (by rfl) ⟨12521, by rfl⟩ : syracuseStep 17096021 = 25043) (by norm_num)
theorem B2252117 : Blo 1332985 2252117 := bbase (se 11 (by rfl) ⟨1649, by rfl⟩ : syracuseStep 2252117 = 3299) (by norm_num)
theorem B1424737 : Blo 1332985 1424737 := bbase (se 2 (by rfl) ⟨534276, by rfl⟩ : syracuseStep 1424737 = 1068553) (by norm_num)
theorem B1899877 : Blo 1332985 1899877 := bbase (se 4 (by rfl) ⟨178113, by rfl⟩ : syracuseStep 1899877 = 356227) (by norm_num)
theorem B2850157 : Blo 1332985 2850157 := bbase (se 3 (by rfl) ⟨534404, by rfl⟩ : syracuseStep 2850157 = 1068809) (by norm_num)
theorem B4504949 : Blo 1332985 4504949 := bbase (se 5 (by rfl) ⟨211169, by rfl⟩ : syracuseStep 4504949 = 422339) (by norm_num)
theorem B2530693 : Blo 1332985 2530693 := bbase (se 4 (by rfl) ⟨237252, by rfl⟩ : syracuseStep 2530693 = 474505) (by norm_num)
theorem B5062085 : Blo 1332985 5062085 := bbase (se 4 (by rfl) ⟨474570, by rfl⟩ : syracuseStep 5062085 = 949141) (by norm_num)
theorem B6757829 : Blo 1332985 6757829 := bbase (se 4 (by rfl) ⟨633546, by rfl⟩ : syracuseStep 6757829 = 1267093) (by norm_num)
theorem B2252245 : Blo 1332985 2252245 := bbase (se 7 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 2252245 = 52787) (by norm_num)
theorem B3374581 : Blo 1332985 3374581 := bbase (se 5 (by rfl) ⟨158183, by rfl⟩ : syracuseStep 3374581 = 316367) (by norm_num)
theorem B2252333 : Blo 1332985 2252333 := bbase (se 3 (by rfl) ⟨422312, by rfl⟩ : syracuseStep 2252333 = 844625) (by norm_num)
theorem B1900093 : Blo 1332985 1900093 := bbase (se 3 (by rfl) ⟨356267, by rfl⟩ : syracuseStep 1900093 = 712535) (by norm_num)
theorem B3374693 : Blo 1332985 3374693 := bbase (se 4 (by rfl) ⟨316377, by rfl⟩ : syracuseStep 3374693 = 632755) (by norm_num)
theorem B1687169 : Blo 1332985 1687169 := bbase (se 2 (by rfl) ⟨632688, by rfl⟩ : syracuseStep 1687169 = 1265377) (by norm_num)
theorem B3604117 : Blo 1332985 3604117 := bbase (se 6 (by rfl) ⟨84471, by rfl⟩ : syracuseStep 3604117 = 168943) (by norm_num)
theorem B1425053 : Blo 1332985 1425053 := bbase (se 3 (by rfl) ⟨267197, by rfl⟩ : syracuseStep 1425053 = 534395) (by norm_num)
theorem B2252461 : Blo 1332985 2252461 := bbase (se 3 (by rfl) ⟨422336, by rfl⟩ : syracuseStep 2252461 = 844673) (by norm_num)
theorem B2530997 : Blo 1332985 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B1687225 : Blo 1332985 1687225 := bbase (se 2 (by rfl) ⟨632709, by rfl⟩ : syracuseStep 1687225 = 1265419) (by norm_num)
theorem B2137861 : Blo 1332985 2137861 := bbase (se 4 (by rfl) ⟨200424, by rfl⟩ : syracuseStep 2137861 = 400849) (by norm_num)
theorem B2252549 : Blo 1332985 2252549 := bbase (se 4 (by rfl) ⟨211176, by rfl⟩ : syracuseStep 2252549 = 422353) (by norm_num)
theorem B1687321 : Blo 1332985 1687321 := bbase (se 2 (by rfl) ⟨632745, by rfl⟩ : syracuseStep 1687321 = 1265491) (by norm_num)
theorem B3374885 : Blo 1332985 3374885 := bbase (se 4 (by rfl) ⟨316395, by rfl⟩ : syracuseStep 3374885 = 632791) (by norm_num)
theorem B4505381 : Blo 1332985 4505381 := bbase (se 4 (by rfl) ⟨422379, by rfl⟩ : syracuseStep 4505381 = 844759) (by norm_num)
theorem B1711945 : Blo 1332985 1711945 := bbase (se 2 (by rfl) ⟨641979, by rfl⟩ : syracuseStep 1711945 = 1283959) (by norm_num)
theorem B2850653 : Blo 1332985 2850653 := bbase (se 3 (by rfl) ⟨534497, by rfl⟩ : syracuseStep 2850653 = 1068995) (by norm_num)
theorem B6750053 : Blo 1332985 6750053 := bbase (se 4 (by rfl) ⟨632817, by rfl⟩ : syracuseStep 6750053 = 1265635) (by norm_num)
theorem B2252677 : Blo 1332985 2252677 := bbase (se 4 (by rfl) ⟨211188, by rfl⟩ : syracuseStep 2252677 = 422377) (by norm_num)
theorem B4054949 : Blo 1332985 4054949 := bbase (se 4 (by rfl) ⟨380151, by rfl⟩ : syracuseStep 4054949 = 760303) (by norm_num)
theorem B12173237 : Blo 1332985 12173237 := bbase (se 5 (by rfl) ⟨570620, by rfl⟩ : syracuseStep 12173237 = 1141241) (by norm_num)
theorem B1900469 : Blo 1332985 1900469 := bbase (se 5 (by rfl) ⟨89084, by rfl⟩ : syracuseStep 1900469 = 178169) (by norm_num)
theorem B1687493 : Blo 1332985 1687493 := bbase (se 4 (by rfl) ⟨158202, by rfl⟩ : syracuseStep 1687493 = 316405) (by norm_num)
theorem B2252765 : Blo 1332985 2252765 := bbase (se 3 (by rfl) ⟨422393, by rfl⟩ : syracuseStep 2252765 = 844787) (by norm_num)
theorem B14073845 : Blo 1332985 14073845 := bbase (se 5 (by rfl) ⟨659711, by rfl⟩ : syracuseStep 14073845 = 1319423) (by norm_num)
theorem B1687549 : Blo 1332985 1687549 := bbase (se 3 (by rfl) ⟨316415, by rfl⟩ : syracuseStep 1687549 = 632831) (by norm_num)
theorem B5062769 : Blo 1332985 5062769 := bstep (se 2 (by rfl) ⟨1898538, by rfl⟩ : syracuseStep 5062769 = 3797077) B3797077
theorem B5480561 : Blo 1332985 5480561 := bstep (se 2 (by rfl) ⟨2055210, by rfl⟩ : syracuseStep 5480561 = 4110421) B4110421
theorem B12173453 : Blo 1332985 12173453 := bstep (se 3 (by rfl) ⟨2282522, by rfl⟩ : syracuseStep 12173453 = 4565045) B4565045
theorem B21627107 : Blo 1332985 21627107 := bstep (se 1 (by rfl) ⟨16220330, by rfl⟩ : syracuseStep 21627107 = 32440661) B32440661
theorem B3801325 : Blo 1332985 3801325 := bstep (se 3 (by rfl) ⟨712748, by rfl⟩ : syracuseStep 3801325 = 1425497) B1425497
theorem B7414051 : Blo 1332985 7414051 := bstep (se 1 (by rfl) ⟨5560538, by rfl⟩ : syracuseStep 7414051 = 11121077) B11121077
theorem B2531665 : Blo 1332985 2531665 := bstep (se 2 (by rfl) ⟨949374, by rfl⟩ : syracuseStep 2531665 = 1898749) B1898749
theorem B3801485 : Blo 1332985 3801485 := bstep (se 3 (by rfl) ⟨712778, by rfl⟩ : syracuseStep 3801485 = 1425557) B1425557
theorem B1802675 : Blo 1332985 1802675 := bstep (se 1 (by rfl) ⟨1352006, by rfl⟩ : syracuseStep 1802675 = 2704013) B2704013
theorem B1688035 : Blo 1332985 1688035 := bstep (se 1 (by rfl) ⟨1266026, by rfl⟩ : syracuseStep 1688035 = 2532053) B2532053
theorem B10125809 : Blo 1332985 10125809 := bstep (se 2 (by rfl) ⟨3797178, by rfl⟩ : syracuseStep 10125809 = 7594357) B7594357
theorem B1499683 : Blo 1332985 1499683 := bstep (se 1 (by rfl) ⟨1124762, by rfl⟩ : syracuseStep 1499683 = 2249525) B2249525
theorem B3375665 : Blo 1332985 3375665 := bstep (se 2 (by rfl) ⟨1265874, by rfl⟩ : syracuseStep 3375665 = 2531749) B2531749
theorem B1688131 : Blo 1332985 1688131 := bstep (se 1 (by rfl) ⟨1266098, by rfl⟩ : syracuseStep 1688131 = 2532197) B2532197
theorem B3375715 : Blo 1332985 3375715 := bstep (se 1 (by rfl) ⟨2531786, by rfl⟩ : syracuseStep 3375715 = 5063573) B5063573
theorem B4563569 : Blo 1332985 4563569 := bstep (se 2 (by rfl) ⟨1711338, by rfl⟩ : syracuseStep 4563569 = 3422677) B3422677
theorem B1999505 : Blo 1332985 1999505 := bstep (se 2 (by rfl) ⟨749814, by rfl⟩ : syracuseStep 1999505 = 1499629) B1499629
theorem B1999523 : Blo 1332985 1999523 := bstep (se 1 (by rfl) ⟨1499642, by rfl⟩ : syracuseStep 1999523 = 2999285) B2999285
theorem B1499827 : Blo 1332985 1499827 := bstep (se 1 (by rfl) ⟨1124870, by rfl⟩ : syracuseStep 1499827 = 2249741) B2249741
theorem B1999553 : Blo 1332985 1999553 := bstep (se 2 (by rfl) ⟨749832, by rfl⟩ : syracuseStep 1999553 = 1499665) B1499665
theorem B1999571 : Blo 1332985 1999571 := bstep (se 1 (by rfl) ⟨1499678, by rfl⟩ : syracuseStep 1999571 = 2999357) B2999357
theorem B1999601 : Blo 1332985 1999601 := bstep (se 2 (by rfl) ⟨749850, by rfl⟩ : syracuseStep 1999601 = 1499701) B1499701
theorem B3375857 : Blo 1332985 3375857 := bstep (se 2 (by rfl) ⟨1265946, by rfl⟩ : syracuseStep 3375857 = 2531893) B2531893
theorem B1999619 : Blo 1332985 1999619 := bstep (se 1 (by rfl) ⟨1499714, by rfl⟩ : syracuseStep 1999619 = 2999429) B2999429
theorem B1999649 : Blo 1332985 1999649 := bstep (se 2 (by rfl) ⟨749868, by rfl⟩ : syracuseStep 1999649 = 1499737) B1499737
theorem B6751025 : Blo 1332985 6751025 := bstep (se 2 (by rfl) ⟨2531634, by rfl⟩ : syracuseStep 6751025 = 5063269) B5063269
theorem B1999667 : Blo 1332985 1999667 := bstep (se 1 (by rfl) ⟨1499750, by rfl⟩ : syracuseStep 1999667 = 2999501) B2999501
theorem B1499971 : Blo 1332985 1499971 := bstep (se 1 (by rfl) ⟨1124978, by rfl⟩ : syracuseStep 1499971 = 2249957) B2249957
theorem B1999697 : Blo 1332985 1999697 := bstep (se 2 (by rfl) ⟨749886, by rfl⟩ : syracuseStep 1999697 = 1499773) B1499773
theorem B1999715 : Blo 1332985 1999715 := bstep (se 1 (by rfl) ⟨1499786, by rfl⟩ : syracuseStep 1999715 = 2999573) B2999573
theorem B1999745 : Blo 1332985 1999745 := bstep (se 2 (by rfl) ⟨749904, by rfl⟩ : syracuseStep 1999745 = 1499809) B1499809
theorem B1999763 : Blo 1332985 1999763 := bstep (se 1 (by rfl) ⟨1499822, by rfl⟩ : syracuseStep 1999763 = 2999645) B2999645
theorem B1999793 : Blo 1332985 1999793 := bstep (se 2 (by rfl) ⟨749922, by rfl⟩ : syracuseStep 1999793 = 1499845) B1499845
theorem B1999811 : Blo 1332985 1999811 := bstep (se 1 (by rfl) ⟨1499858, by rfl⟩ : syracuseStep 1999811 = 2999717) B2999717
theorem B2999249 : Blo 1332985 2999249 := bstep (se 2 (by rfl) ⟨1124718, by rfl⟩ : syracuseStep 2999249 = 2249437) B2249437
theorem B1500115 : Blo 1332985 1500115 := bstep (se 1 (by rfl) ⟨1125086, by rfl⟩ : syracuseStep 1500115 = 2250173) B2250173
theorem B1999841 : Blo 1332985 1999841 := bstep (se 2 (by rfl) ⟨749940, by rfl⟩ : syracuseStep 1999841 = 1499881) B1499881
theorem B2999267 : Blo 1332985 2999267 := bstep (se 1 (by rfl) ⟨2249450, by rfl⟩ : syracuseStep 2999267 = 4498901) B4498901
theorem B1999859 : Blo 1332985 1999859 := bstep (se 1 (by rfl) ⟨1499894, by rfl⟩ : syracuseStep 1999859 = 2999789) B2999789
theorem B1999889 : Blo 1332985 1999889 := bstep (se 2 (by rfl) ⟨749958, by rfl⟩ : syracuseStep 1999889 = 1499917) B1499917
theorem B1999907 : Blo 1332985 1999907 := bstep (se 1 (by rfl) ⟨1499930, by rfl⟩ : syracuseStep 1999907 = 2999861) B2999861
theorem B2704433 : Blo 1332985 2704433 := bstep (se 2 (by rfl) ⟨1014162, by rfl⟩ : syracuseStep 2704433 = 2028325) B2028325
theorem B1688627 : Blo 1332985 1688627 := bstep (se 1 (by rfl) ⟨1266470, by rfl⟩ : syracuseStep 1688627 = 2532941) B2532941
theorem B1999937 : Blo 1332985 1999937 := bstep (se 2 (by rfl) ⟨749976, by rfl⟩ : syracuseStep 1999937 = 1499953) B1499953
theorem B1999955 : Blo 1332985 1999955 := bstep (se 1 (by rfl) ⟨1499966, by rfl⟩ : syracuseStep 1999955 = 2999933) B2999933
theorem B1500259 : Blo 1332985 1500259 := bstep (se 1 (by rfl) ⟨1125194, by rfl⟩ : syracuseStep 1500259 = 2250389) B2250389
theorem B1999985 : Blo 1332985 1999985 := bstep (se 2 (by rfl) ⟨749994, by rfl⟩ : syracuseStep 1999985 = 1499989) B1499989
theorem B2057345 : Blo 1332985 2057345 := bstep (se 2 (by rfl) ⟨771504, by rfl⟩ : syracuseStep 2057345 = 1543009) B1543009
theorem B2000003 : Blo 1332985 2000003 := bstep (se 1 (by rfl) ⟨1500002, by rfl⟩ : syracuseStep 2000003 = 3000005) B3000005
theorem B2000033 : Blo 1332985 2000033 := bstep (se 2 (by rfl) ⟨750012, by rfl⟩ : syracuseStep 2000033 = 1500025) B1500025
theorem B2000051 : Blo 1332985 2000051 := bstep (se 1 (by rfl) ⟨1500038, by rfl⟩ : syracuseStep 2000051 = 3000077) B3000077
theorem B2565329 : Blo 1332985 2565329 := bstep (se 2 (by rfl) ⟨961998, by rfl⟩ : syracuseStep 2565329 = 1923997) B1923997
theorem B2000081 : Blo 1332985 2000081 := bstep (se 2 (by rfl) ⟨750030, by rfl⟩ : syracuseStep 2000081 = 1500061) B1500061
theorem B2000099 : Blo 1332985 2000099 := bstep (se 1 (by rfl) ⟨1500074, by rfl⟩ : syracuseStep 2000099 = 3000149) B3000149
theorem B2999537 : Blo 1332985 2999537 := bstep (se 2 (by rfl) ⟨1124826, by rfl⟩ : syracuseStep 2999537 = 2249653) B2249653
theorem B1500403 : Blo 1332985 1500403 := bstep (se 1 (by rfl) ⟨1125302, by rfl⟩ : syracuseStep 1500403 = 2250605) B2250605
theorem B2000129 : Blo 1332985 2000129 := bstep (se 2 (by rfl) ⟨750048, by rfl⟩ : syracuseStep 2000129 = 1500097) B1500097
theorem B2999555 : Blo 1332985 2999555 := bstep (se 1 (by rfl) ⟨2249666, by rfl⟩ : syracuseStep 2999555 = 4499333) B4499333
theorem B2000147 : Blo 1332985 2000147 := bstep (se 1 (by rfl) ⟨1500110, by rfl⟩ : syracuseStep 2000147 = 3000221) B3000221
theorem B1926433 : Blo 1332985 1926433 := bstep (se 2 (by rfl) ⟨722412, by rfl⟩ : syracuseStep 1926433 = 1444825) B1444825
theorem B2000177 : Blo 1332985 2000177 := bstep (se 2 (by rfl) ⟨750066, by rfl⟩ : syracuseStep 2000177 = 1500133) B1500133
theorem B2000195 : Blo 1332985 2000195 := bstep (se 1 (by rfl) ⟨1500146, by rfl⟩ : syracuseStep 2000195 = 3000293) B3000293
theorem B2000225 : Blo 1332985 2000225 := bstep (se 2 (by rfl) ⟨750084, by rfl⟩ : syracuseStep 2000225 = 1500169) B1500169
theorem B2532721 : Blo 1332985 2532721 := bstep (se 2 (by rfl) ⟨949770, by rfl⟩ : syracuseStep 2532721 = 1899541) B1899541
theorem B2000243 : Blo 1332985 2000243 := bstep (se 1 (by rfl) ⟨1500182, by rfl⟩ : syracuseStep 2000243 = 3000365) B3000365
theorem B1500547 : Blo 1332985 1500547 := bstep (se 1 (by rfl) ⟨1125410, by rfl⟩ : syracuseStep 1500547 = 2250821) B2250821
theorem B2000273 : Blo 1332985 2000273 := bstep (se 2 (by rfl) ⟨750102, by rfl⟩ : syracuseStep 2000273 = 1500205) B1500205
theorem B2000291 : Blo 1332985 2000291 := bstep (se 1 (by rfl) ⟨1500218, by rfl⟩ : syracuseStep 2000291 = 3000437) B3000437
theorem B2000321 : Blo 1332985 2000321 := bstep (se 2 (by rfl) ⟨750120, by rfl⟩ : syracuseStep 2000321 = 1500241) B1500241
theorem B1803713 : Blo 1332985 1803713 := bstep (se 2 (by rfl) ⟨676392, by rfl⟩ : syracuseStep 1803713 = 1352785) B1352785
theorem B2000339 : Blo 1332985 2000339 := bstep (se 1 (by rfl) ⟨1500254, by rfl⟩ : syracuseStep 2000339 = 3000509) B3000509
theorem B2000369 : Blo 1332985 2000369 := bstep (se 2 (by rfl) ⟨750138, by rfl⟩ : syracuseStep 2000369 = 1500277) B1500277
theorem B2311667 : Blo 1332985 2311667 := bstep (se 1 (by rfl) ⟨1733750, by rfl⟩ : syracuseStep 2311667 = 3467501) B3467501
theorem B2000387 : Blo 1332985 2000387 := bstep (se 1 (by rfl) ⟨1500290, by rfl⟩ : syracuseStep 2000387 = 3000581) B3000581
theorem B2999825 : Blo 1332985 2999825 := bstep (se 2 (by rfl) ⟨1124934, by rfl⟩ : syracuseStep 2999825 = 2249869) B2249869
theorem B1500691 : Blo 1332985 1500691 := bstep (se 1 (by rfl) ⟨1125518, by rfl⟩ : syracuseStep 1500691 = 2251037) B2251037
theorem B2000417 : Blo 1332985 2000417 := bstep (se 2 (by rfl) ⟨750156, by rfl⟩ : syracuseStep 2000417 = 1500313) B1500313
theorem B2999843 : Blo 1332985 2999843 := bstep (se 1 (by rfl) ⟨2249882, by rfl⟩ : syracuseStep 2999843 = 4499765) B4499765
theorem B5064227 : Blo 1332985 5064227 := bstep (se 1 (by rfl) ⟨3798170, by rfl⟩ : syracuseStep 5064227 = 7596341) B7596341
theorem B5064241 : Blo 1332985 5064241 := bstep (se 2 (by rfl) ⟨1899090, by rfl⟩ : syracuseStep 5064241 = 3798181) B3798181
theorem B2000435 : Blo 1332985 2000435 := bstep (se 1 (by rfl) ⟨1500326, by rfl⟩ : syracuseStep 2000435 = 3000653) B3000653
theorem B2000465 : Blo 1332985 2000465 := bstep (se 2 (by rfl) ⟨750174, by rfl⟩ : syracuseStep 2000465 = 1500349) B1500349
theorem B2000483 : Blo 1332985 2000483 := bstep (se 1 (by rfl) ⟨1500362, by rfl⟩ : syracuseStep 2000483 = 3000725) B3000725
theorem B4064867 : Blo 1332985 4064867 := bstep (se 1 (by rfl) ⟨3048650, by rfl⟩ : syracuseStep 4064867 = 6097301) B6097301
theorem B7595633 : Blo 1332985 7595633 := bstep (se 2 (by rfl) ⟨2848362, by rfl⟩ : syracuseStep 7595633 = 5696725) B5696725
theorem B2000513 : Blo 1332985 2000513 := bstep (se 2 (by rfl) ⟨750192, by rfl⟩ : syracuseStep 2000513 = 1500385) B1500385
theorem B2000531 : Blo 1332985 2000531 := bstep (se 1 (by rfl) ⟨1500398, by rfl⟩ : syracuseStep 2000531 = 3000797) B3000797
theorem B1500835 : Blo 1332985 1500835 := bstep (se 1 (by rfl) ⟨1125626, by rfl⟩ : syracuseStep 1500835 = 2251253) B2251253
theorem B4499117 : Blo 1332985 4499117 := bstep (se 3 (by rfl) ⟨843584, by rfl⟩ : syracuseStep 4499117 = 1687169) B1687169
theorem B2000561 : Blo 1332985 2000561 := bstep (se 2 (by rfl) ⟨750210, by rfl⟩ : syracuseStep 2000561 = 1500421) B1500421
theorem B2000579 : Blo 1332985 2000579 := bstep (se 1 (by rfl) ⟨1500434, by rfl⟩ : syracuseStep 2000579 = 3000869) B3000869
theorem B3376849 : Blo 1332985 3376849 := bstep (se 2 (by rfl) ⟨1266318, by rfl⟩ : syracuseStep 3376849 = 2532637) B2532637
theorem B2000609 : Blo 1332985 2000609 := bstep (se 2 (by rfl) ⟨750228, by rfl⟩ : syracuseStep 2000609 = 1500457) B1500457
theorem B4499171 : Blo 1332985 4499171 := bstep (se 1 (by rfl) ⟨3374378, by rfl⟩ : syracuseStep 4499171 = 6748757) B6748757
theorem B3606257 : Blo 1332985 3606257 := bstep (se 2 (by rfl) ⟨1352346, by rfl⟩ : syracuseStep 3606257 = 2704693) B2704693
theorem B2000627 : Blo 1332985 2000627 := bstep (se 1 (by rfl) ⟨1500470, by rfl⟩ : syracuseStep 2000627 = 3000941) B3000941
theorem B1689331 : Blo 1332985 1689331 := bstep (se 1 (by rfl) ⟨1266998, by rfl⟩ : syracuseStep 1689331 = 2533997) B2533997
theorem B2533123 : Blo 1332985 2533123 := bstep (se 1 (by rfl) ⟨1899842, by rfl⟩ : syracuseStep 2533123 = 3799685) B3799685
theorem B3385091 : Blo 1332985 3385091 := bstep (se 1 (by rfl) ⟨2538818, by rfl⟩ : syracuseStep 3385091 = 5077637) B5077637
theorem B10962701 : Blo 1332985 10962701 := bstep (se 3 (by rfl) ⟨2055506, by rfl⟩ : syracuseStep 10962701 = 4111013) B4111013
theorem B18507533 : Blo 1332985 18507533 := bstep (se 3 (by rfl) ⟨3470162, by rfl⟩ : syracuseStep 18507533 = 6940325) B6940325
theorem B2000657 : Blo 1332985 2000657 := bstep (se 2 (by rfl) ⟨750246, by rfl⟩ : syracuseStep 2000657 = 1500493) B1500493
theorem B2000675 : Blo 1332985 2000675 := bstep (se 1 (by rfl) ⟨1500506, by rfl⟩ : syracuseStep 2000675 = 3001013) B3001013
theorem B3000113 : Blo 1332985 3000113 := bstep (se 2 (by rfl) ⟨1125042, by rfl⟩ : syracuseStep 3000113 = 2250085) B2250085
theorem B2533169 : Blo 1332985 2533169 := bstep (se 2 (by rfl) ⟨949938, by rfl⟩ : syracuseStep 2533169 = 1899877) B1899877
theorem B1500979 : Blo 1332985 1500979 := bstep (se 1 (by rfl) ⟨1125734, by rfl⟩ : syracuseStep 1500979 = 2251469) B2251469
theorem B2000705 : Blo 1332985 2000705 := bstep (se 2 (by rfl) ⟨750264, by rfl⟩ : syracuseStep 2000705 = 1500529) B1500529
theorem B3000131 : Blo 1332985 3000131 := bstep (se 1 (by rfl) ⟨2250098, by rfl⟩ : syracuseStep 3000131 = 4500197) B4500197
theorem B2000723 : Blo 1332985 2000723 := bstep (se 1 (by rfl) ⟨1500542, by rfl⟩ : syracuseStep 2000723 = 3001085) B3001085
theorem B1689427 : Blo 1332985 1689427 := bstep (se 1 (by rfl) ⟨1267070, by rfl⟩ : syracuseStep 1689427 = 2534141) B2534141
theorem B2000753 : Blo 1332985 2000753 := bstep (se 2 (by rfl) ⟨750282, by rfl⟩ : syracuseStep 2000753 = 1500565) B1500565
theorem B2000771 : Blo 1332985 2000771 := bstep (se 1 (by rfl) ⟨1500578, by rfl⟩ : syracuseStep 2000771 = 3001157) B3001157
theorem B2000801 : Blo 1332985 2000801 := bstep (se 2 (by rfl) ⟨750300, by rfl⟩ : syracuseStep 2000801 = 1500601) B1500601
theorem B2000819 : Blo 1332985 2000819 := bstep (se 1 (by rfl) ⟨1500614, by rfl⟩ : syracuseStep 2000819 = 3001229) B3001229
theorem B1501123 : Blo 1332985 1501123 := bstep (se 1 (by rfl) ⟨1125842, by rfl⟩ : syracuseStep 1501123 = 2251685) B2251685
theorem B2000849 : Blo 1332985 2000849 := bstep (se 2 (by rfl) ⟨750318, by rfl⟩ : syracuseStep 2000849 = 1500637) B1500637
theorem B2000867 : Blo 1332985 2000867 := bstep (se 1 (by rfl) ⟨1500650, by rfl⟩ : syracuseStep 2000867 = 3001301) B3001301
theorem B3377123 : Blo 1332985 3377123 := bstep (se 1 (by rfl) ⟨2532842, by rfl⟩ : syracuseStep 3377123 = 5065685) B5065685
theorem B4499441 : Blo 1332985 4499441 := bstep (se 2 (by rfl) ⟨1687290, by rfl⟩ : syracuseStep 4499441 = 3374581) B3374581
theorem B2000897 : Blo 1332985 2000897 := bstep (se 2 (by rfl) ⟨750336, by rfl⟩ : syracuseStep 2000897 = 1500673) B1500673
theorem B4810765 : Blo 1332985 4810765 := bstep (se 3 (by rfl) ⟨902018, by rfl⟩ : syracuseStep 4810765 = 1804037) B1804037
theorem B2000915 : Blo 1332985 2000915 := bstep (se 1 (by rfl) ⟨1500686, by rfl⟩ : syracuseStep 2000915 = 3001373) B3001373
theorem B2000945 : Blo 1332985 2000945 := bstep (se 2 (by rfl) ⟨750354, by rfl⟩ : syracuseStep 2000945 = 1500709) B1500709
theorem B2000963 : Blo 1332985 2000963 := bstep (se 1 (by rfl) ⟨1500722, by rfl⟩ : syracuseStep 2000963 = 3001445) B3001445
theorem B3000401 : Blo 1332985 3000401 := bstep (se 2 (by rfl) ⟨1125150, by rfl⟩ : syracuseStep 3000401 = 2250301) B2250301
theorem B2533457 : Blo 1332985 2533457 := bstep (se 2 (by rfl) ⟨950046, by rfl⟩ : syracuseStep 2533457 = 1900093) B1900093
theorem B1501267 : Blo 1332985 1501267 := bstep (se 1 (by rfl) ⟨1125950, by rfl⟩ : syracuseStep 1501267 = 2251901) B2251901
theorem B2000993 : Blo 1332985 2000993 := bstep (se 2 (by rfl) ⟨750372, by rfl⟩ : syracuseStep 2000993 = 1500745) B1500745
theorem B3000419 : Blo 1332985 3000419 := bstep (se 1 (by rfl) ⟨2250314, by rfl⟩ : syracuseStep 3000419 = 4500629) B4500629
theorem B3295331 : Blo 1332985 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B2001011 : Blo 1332985 2001011 := bstep (se 1 (by rfl) ⟨1500758, by rfl⟩ : syracuseStep 2001011 = 3001517) B3001517
theorem B2001041 : Blo 1332985 2001041 := bstep (se 2 (by rfl) ⟨750390, by rfl⟩ : syracuseStep 2001041 = 1500781) B1500781
theorem B6408355 : Blo 1332985 6408355 := bstep (se 1 (by rfl) ⟨4806266, by rfl⟩ : syracuseStep 6408355 = 9612533) B9612533
theorem B2001059 : Blo 1332985 2001059 := bstep (se 1 (by rfl) ⟨1500794, by rfl⟩ : syracuseStep 2001059 = 3001589) B3001589
theorem B3377315 : Blo 1332985 3377315 := bstep (se 1 (by rfl) ⟨2532986, by rfl⟩ : syracuseStep 3377315 = 5065973) B5065973
theorem B2001089 : Blo 1332985 2001089 := bstep (se 2 (by rfl) ⟨750408, by rfl⟩ : syracuseStep 2001089 = 1500817) B1500817
theorem B2001107 : Blo 1332985 2001107 := bstep (se 1 (by rfl) ⟨1500830, by rfl⟩ : syracuseStep 2001107 = 3001661) B3001661
theorem B6752483 : Blo 1332985 6752483 := bstep (se 1 (by rfl) ⟨5064362, by rfl⟩ : syracuseStep 6752483 = 10128725) B10128725
theorem B11397347 : Blo 1332985 11397347 := bstep (se 1 (by rfl) ⟨8548010, by rfl⟩ : syracuseStep 11397347 = 17096021) B17096021
theorem B1501411 : Blo 1332985 1501411 := bstep (se 1 (by rfl) ⟨1126058, by rfl⟩ : syracuseStep 1501411 = 2252117) B2252117
theorem B2001137 : Blo 1332985 2001137 := bstep (se 2 (by rfl) ⟨750426, by rfl⟩ : syracuseStep 2001137 = 1500853) B1500853
theorem B2001155 : Blo 1332985 2001155 := bstep (se 1 (by rfl) ⟨1500866, by rfl⟩ : syracuseStep 2001155 = 3001733) B3001733
theorem B2001185 : Blo 1332985 2001185 := bstep (se 2 (by rfl) ⟨750444, by rfl⟩ : syracuseStep 2001185 = 1500889) B1500889
theorem B3852589 : Blo 1332985 3852589 := bstep (se 3 (by rfl) ⟨722360, by rfl⟩ : syracuseStep 3852589 = 1444721) B1444721
theorem B2001203 : Blo 1332985 2001203 := bstep (se 1 (by rfl) ⟨1500902, by rfl⟩ : syracuseStep 2001203 = 3001805) B3001805
theorem B2001233 : Blo 1332985 2001233 := bstep (se 2 (by rfl) ⟨750462, by rfl⟩ : syracuseStep 2001233 = 1500925) B1500925
theorem B2001251 : Blo 1332985 2001251 := bstep (se 1 (by rfl) ⟨1500938, by rfl⟩ : syracuseStep 2001251 = 3001877) B3001877
theorem B3000689 : Blo 1332985 3000689 := bstep (se 2 (by rfl) ⟨1125258, by rfl⟩ : syracuseStep 3000689 = 2250517) B2250517
theorem B1501555 : Blo 1332985 1501555 := bstep (se 1 (by rfl) ⟨1126166, by rfl⟩ : syracuseStep 1501555 = 2252333) B2252333
theorem B2001281 : Blo 1332985 2001281 := bstep (se 2 (by rfl) ⟨750480, by rfl⟩ : syracuseStep 2001281 = 1500961) B1500961
theorem B3000707 : Blo 1332985 3000707 := bstep (se 1 (by rfl) ⟨2250530, by rfl⟩ : syracuseStep 3000707 = 4501061) B4501061
theorem B2001299 : Blo 1332985 2001299 := bstep (se 1 (by rfl) ⟨1500974, by rfl⟩ : syracuseStep 2001299 = 3001949) B3001949
theorem B2001329 : Blo 1332985 2001329 := bstep (se 2 (by rfl) ⟨750498, by rfl⟩ : syracuseStep 2001329 = 1500997) B1500997
theorem B2001347 : Blo 1332985 2001347 := bstep (se 1 (by rfl) ⟨1501010, by rfl⟩ : syracuseStep 2001347 = 3002021) B3002021
theorem B4811213 : Blo 1332985 4811213 := bstep (se 3 (by rfl) ⟨902102, by rfl⟩ : syracuseStep 4811213 = 1804205) B1804205
theorem B2001377 : Blo 1332985 2001377 := bstep (se 2 (by rfl) ⟨750516, by rfl⟩ : syracuseStep 2001377 = 1501033) B1501033
theorem B2001395 : Blo 1332985 2001395 := bstep (se 1 (by rfl) ⟨1501046, by rfl⟩ : syracuseStep 2001395 = 3002093) B3002093
theorem B1501699 : Blo 1332985 1501699 := bstep (se 1 (by rfl) ⟨1126274, by rfl⟩ : syracuseStep 1501699 = 2252549) B2252549
theorem B4499981 : Blo 1332985 4499981 := bstep (se 3 (by rfl) ⟨843746, by rfl⟩ : syracuseStep 4499981 = 1687493) B1687493
theorem B2001425 : Blo 1332985 2001425 := bstep (se 2 (by rfl) ⟨750534, by rfl⟩ : syracuseStep 2001425 = 1501069) B1501069
theorem B2001443 : Blo 1332985 2001443 := bstep (se 1 (by rfl) ⟨1501082, by rfl⟩ : syracuseStep 2001443 = 3002165) B3002165
theorem B2001473 : Blo 1332985 2001473 := bstep (se 2 (by rfl) ⟨750552, by rfl⟩ : syracuseStep 2001473 = 1501105) B1501105
theorem B4500035 : Blo 1332985 4500035 := bstep (se 1 (by rfl) ⟨3375026, by rfl⟩ : syracuseStep 4500035 = 6750053) B6750053
theorem B4811341 : Blo 1332985 4811341 := bstep (se 3 (by rfl) ⟨902126, by rfl⟩ : syracuseStep 4811341 = 1804253) B1804253
theorem B2001491 : Blo 1332985 2001491 := bstep (se 1 (by rfl) ⟨1501118, by rfl⟩ : syracuseStep 2001491 = 3002237) B3002237
theorem B2001521 : Blo 1332985 2001521 := bstep (se 2 (by rfl) ⟨750570, by rfl⟩ : syracuseStep 2001521 = 1501141) B1501141
theorem B2001539 : Blo 1332985 2001539 := bstep (se 1 (by rfl) ⟨1501154, by rfl⟩ : syracuseStep 2001539 = 3002309) B3002309
theorem B37530253 : Blo 1332985 37530253 := bstep (se 3 (by rfl) ⟨7036922, by rfl⟩ : syracuseStep 37530253 = 14073845) B14073845
theorem B3000977 : Blo 1332985 3000977 := bstep (se 2 (by rfl) ⟨1125366, by rfl⟩ : syracuseStep 3000977 = 2250733) B2250733
theorem B1501843 : Blo 1332985 1501843 := bstep (se 1 (by rfl) ⟨1126382, by rfl⟩ : syracuseStep 1501843 = 2252765) B2252765
theorem B2001569 : Blo 1332985 2001569 := bstep (se 2 (by rfl) ⟨750588, by rfl⟩ : syracuseStep 2001569 = 1501177) B1501177
theorem B3000995 : Blo 1332985 3000995 := bstep (se 1 (by rfl) ⟨2250746, by rfl⟩ : syracuseStep 3000995 = 4501493) B4501493
theorem B2001587 : Blo 1332985 2001587 := bstep (se 1 (by rfl) ⟨1501190, by rfl⟩ : syracuseStep 2001587 = 3002381) B3002381
theorem B4270801 : Blo 1332985 4270801 := bstep (se 2 (by rfl) ⟨1601550, by rfl⟩ : syracuseStep 4270801 = 3203101) B3203101
theorem B2001617 : Blo 1332985 2001617 := bstep (se 2 (by rfl) ⟨750606, by rfl⟩ : syracuseStep 2001617 = 1501213) B1501213
theorem B2001635 : Blo 1332985 2001635 := bstep (se 1 (by rfl) ⟨1501226, by rfl⟩ : syracuseStep 2001635 = 3002453) B3002453
theorem B2001665 : Blo 1332985 2001665 := bstep (se 2 (by rfl) ⟨750624, by rfl⟩ : syracuseStep 2001665 = 1501249) B1501249
theorem B2001683 : Blo 1332985 2001683 := bstep (se 1 (by rfl) ⟨1501262, by rfl⟩ : syracuseStep 2001683 = 3002525) B3002525
theorem B2534179 : Blo 1332985 2534179 := bstep (se 1 (by rfl) ⟨1900634, by rfl⟩ : syracuseStep 2534179 = 3801269) B3801269
theorem B3205937 : Blo 1332985 3205937 := bstep (se 2 (by rfl) ⟨1202226, by rfl⟩ : syracuseStep 3205937 = 2404453) B2404453
theorem B2001713 : Blo 1332985 2001713 := bstep (se 2 (by rfl) ⟨750642, by rfl⟩ : syracuseStep 2001713 = 1501285) B1501285
theorem B2001731 : Blo 1332985 2001731 := bstep (se 1 (by rfl) ⟨1501298, by rfl⟩ : syracuseStep 2001731 = 3002597) B3002597
theorem B4500305 : Blo 1332985 4500305 := bstep (se 2 (by rfl) ⟨1687614, by rfl⟩ : syracuseStep 4500305 = 3375229) B3375229
theorem B2001761 : Blo 1332985 2001761 := bstep (se 2 (by rfl) ⟨750660, by rfl⟩ : syracuseStep 2001761 = 1501321) B1501321
theorem B3246961 : Blo 1332985 3246961 := bstep (se 2 (by rfl) ⟨1217610, by rfl⟩ : syracuseStep 3246961 = 2435221) B2435221
theorem B3042161 : Blo 1332985 3042161 := bstep (se 2 (by rfl) ⟨1140810, by rfl⟩ : syracuseStep 3042161 = 2281621) B2281621
theorem B2001779 : Blo 1332985 2001779 := bstep (se 1 (by rfl) ⟨1501334, by rfl⟩ : syracuseStep 2001779 = 3002669) B3002669
theorem B2001809 : Blo 1332985 2001809 := bstep (se 2 (by rfl) ⟨750678, by rfl⟩ : syracuseStep 2001809 = 1501357) B1501357
theorem B2001827 : Blo 1332985 2001827 := bstep (se 1 (by rfl) ⟨1501370, by rfl⟩ : syracuseStep 2001827 = 3002741) B3002741
theorem B3607469 : Blo 1332985 3607469 := bstep (se 3 (by rfl) ⟨676400, by rfl⟩ : syracuseStep 3607469 = 1352801) B1352801
theorem B3001265 : Blo 1332985 3001265 := bstep (se 2 (by rfl) ⟨1125474, by rfl⟩ : syracuseStep 3001265 = 2250949) B2250949
theorem B2001857 : Blo 1332985 2001857 := bstep (se 2 (by rfl) ⟨750696, by rfl⟩ : syracuseStep 2001857 = 1501393) B1501393
theorem B3001283 : Blo 1332985 3001283 := bstep (se 1 (by rfl) ⟨2250962, by rfl⟩ : syracuseStep 3001283 = 4501925) B4501925
theorem B2280403 : Blo 1332985 2280403 := bstep (se 1 (by rfl) ⟨1710302, by rfl⟩ : syracuseStep 2280403 = 3420605) B3420605
theorem B2001875 : Blo 1332985 2001875 := bstep (se 1 (by rfl) ⟨1501406, by rfl⟩ : syracuseStep 2001875 = 3002813) B3002813
theorem B5065699 : Blo 1332985 5065699 := bstep (se 1 (by rfl) ⟨3799274, by rfl⟩ : syracuseStep 5065699 = 7598549) B7598549
theorem B6409201 : Blo 1332985 6409201 := bstep (se 2 (by rfl) ⟨2403450, by rfl⟩ : syracuseStep 6409201 = 4806901) B4806901
theorem B2001905 : Blo 1332985 2001905 := bstep (se 2 (by rfl) ⟨750714, by rfl⟩ : syracuseStep 2001905 = 1501429) B1501429
theorem B2001923 : Blo 1332985 2001923 := bstep (se 1 (by rfl) ⟨1501442, by rfl⟩ : syracuseStep 2001923 = 3002885) B3002885
theorem B6753293 : Blo 1332985 6753293 := bstep (se 3 (by rfl) ⟨1266242, by rfl⟩ : syracuseStep 6753293 = 2532485) B2532485
theorem B2001953 : Blo 1332985 2001953 := bstep (se 2 (by rfl) ⟨750732, by rfl⟩ : syracuseStep 2001953 = 1501465) B1501465
theorem B7597091 : Blo 1332985 7597091 := bstep (se 1 (by rfl) ⟨5697818, by rfl⟩ : syracuseStep 7597091 = 11395637) B11395637
theorem B5409841 : Blo 1332985 5409841 := bstep (se 2 (by rfl) ⟨2028690, by rfl⟩ : syracuseStep 5409841 = 4057381) B4057381
theorem B2001971 : Blo 1332985 2001971 := bstep (se 1 (by rfl) ⟨1501478, by rfl⟩ : syracuseStep 2001971 = 3002957) B3002957
theorem B3378257 : Blo 1332985 3378257 := bstep (se 2 (by rfl) ⟨1266846, by rfl⟩ : syracuseStep 3378257 = 2533693) B2533693
theorem B2002001 : Blo 1332985 2002001 := bstep (se 2 (by rfl) ⟨750750, by rfl⟩ : syracuseStep 2002001 = 1501501) B1501501
theorem B2002019 : Blo 1332985 2002019 := bstep (se 1 (by rfl) ⟨1501514, by rfl⟩ : syracuseStep 2002019 = 3003029) B3003029
theorem B2002049 : Blo 1332985 2002049 := bstep (se 2 (by rfl) ⟨750768, by rfl⟩ : syracuseStep 2002049 = 1501537) B1501537
theorem B3378307 : Blo 1332985 3378307 := bstep (se 1 (by rfl) ⟨2533730, by rfl⟩ : syracuseStep 3378307 = 5067461) B5067461
theorem B3796109 : Blo 1332985 3796109 := bstep (se 3 (by rfl) ⟨711770, by rfl⟩ : syracuseStep 3796109 = 1423541) B1423541
theorem B2002067 : Blo 1332985 2002067 := bstep (se 1 (by rfl) ⟨1501550, by rfl⟩ : syracuseStep 2002067 = 3003101) B3003101
theorem B2002097 : Blo 1332985 2002097 := bstep (se 2 (by rfl) ⟨750786, by rfl⟩ : syracuseStep 2002097 = 1501573) B1501573
theorem B2002115 : Blo 1332985 2002115 := bstep (se 1 (by rfl) ⟨1501586, by rfl⟩ : syracuseStep 2002115 = 3003173) B3003173
theorem B3001553 : Blo 1332985 3001553 := bstep (se 2 (by rfl) ⟨1125582, by rfl⟩ : syracuseStep 3001553 = 2251165) B2251165
theorem B2002145 : Blo 1332985 2002145 := bstep (se 2 (by rfl) ⟨750804, by rfl⟩ : syracuseStep 2002145 = 1501609) B1501609
theorem B3001571 : Blo 1332985 3001571 := bstep (se 1 (by rfl) ⟨2251178, by rfl⟩ : syracuseStep 3001571 = 4502357) B4502357
theorem B17100017 : Blo 1332985 17100017 := bstep (se 2 (by rfl) ⟨6412506, by rfl⟩ : syracuseStep 17100017 = 12825013) B12825013
theorem B2002163 : Blo 1332985 2002163 := bstep (se 1 (by rfl) ⟨1501622, by rfl⟩ : syracuseStep 2002163 = 3003245) B3003245
theorem B3378449 : Blo 1332985 3378449 := bstep (se 2 (by rfl) ⟨1266918, by rfl⟩ : syracuseStep 3378449 = 2533837) B2533837
theorem B2002193 : Blo 1332985 2002193 := bstep (se 2 (by rfl) ⟨750822, by rfl⟩ : syracuseStep 2002193 = 1501645) B1501645
theorem B2002211 : Blo 1332985 2002211 := bstep (se 1 (by rfl) ⟨1501658, by rfl⟩ : syracuseStep 2002211 = 3003317) B3003317
theorem B2002241 : Blo 1332985 2002241 := bstep (se 2 (by rfl) ⟨750840, by rfl⟩ : syracuseStep 2002241 = 1501681) B1501681
theorem B2002259 : Blo 1332985 2002259 := bstep (se 1 (by rfl) ⟨1501694, by rfl⟩ : syracuseStep 2002259 = 3003389) B3003389
theorem B4500845 : Blo 1332985 4500845 := bstep (se 3 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 4500845 = 1687817) B1687817
theorem B2002289 : Blo 1332985 2002289 := bstep (se 2 (by rfl) ⟨750858, by rfl⟩ : syracuseStep 2002289 = 1501717) B1501717
theorem B2002307 : Blo 1332985 2002307 := bstep (se 1 (by rfl) ⟨1501730, by rfl⟩ : syracuseStep 2002307 = 3003461) B3003461
theorem B2002337 : Blo 1332985 2002337 := bstep (se 2 (by rfl) ⟨750876, by rfl⟩ : syracuseStep 2002337 = 1501753) B1501753
theorem B4500899 : Blo 1332985 4500899 := bstep (se 1 (by rfl) ⟨3375674, by rfl⟩ : syracuseStep 4500899 = 6751349) B6751349
theorem B2403761 : Blo 1332985 2403761 := bstep (se 2 (by rfl) ⟨901410, by rfl⟩ : syracuseStep 2403761 = 1802821) B1802821
theorem B2002355 : Blo 1332985 2002355 := bstep (se 1 (by rfl) ⟨1501766, by rfl⟩ : syracuseStep 2002355 = 3003533) B3003533
theorem B2002385 : Blo 1332985 2002385 := bstep (se 2 (by rfl) ⟨750894, by rfl⟩ : syracuseStep 2002385 = 1501789) B1501789
theorem B2002403 : Blo 1332985 2002403 := bstep (se 1 (by rfl) ⟨1501802, by rfl⟩ : syracuseStep 2002403 = 3003605) B3003605
theorem B3001841 : Blo 1332985 3001841 := bstep (se 2 (by rfl) ⟨1125690, by rfl⟩ : syracuseStep 3001841 = 2251381) B2251381
theorem B2002433 : Blo 1332985 2002433 := bstep (se 2 (by rfl) ⟨750912, by rfl⟩ : syracuseStep 2002433 = 1501825) B1501825
theorem B3001859 : Blo 1332985 3001859 := bstep (se 1 (by rfl) ⟨2251394, by rfl⟩ : syracuseStep 3001859 = 4502789) B4502789
theorem B2002451 : Blo 1332985 2002451 := bstep (se 1 (by rfl) ⟨1501838, by rfl⟩ : syracuseStep 2002451 = 3003677) B3003677
theorem B12815941 : Blo 1332985 12815941 := bstep (se 4 (by rfl) ⟨1201494, by rfl⟩ : syracuseStep 12815941 = 2402989) B2402989
theorem B5779021 : Blo 1332985 5779021 := bstep (se 3 (by rfl) ⟨1083566, by rfl⟩ : syracuseStep 5779021 = 2167133) B2167133
theorem B10268273 : Blo 1332985 10268273 := bstep (se 2 (by rfl) ⟨3850602, by rfl⟩ : syracuseStep 10268273 = 7701205) B7701205
theorem B2027153 : Blo 1332985 2027153 := bstep (se 2 (by rfl) ⟨760182, by rfl⟩ : syracuseStep 2027153 = 1520365) B1520365
theorem B4501169 : Blo 1332985 4501169 := bstep (se 2 (by rfl) ⟨1687938, by rfl⟩ : syracuseStep 4501169 = 3375877) B3375877
theorem B4566797 : Blo 1332985 4566797 := bstep (se 3 (by rfl) ⟨856274, by rfl⟩ : syracuseStep 4566797 = 1712549) B1712549
theorem B3002129 : Blo 1332985 3002129 := bstep (se 2 (by rfl) ⟨1125798, by rfl⟩ : syracuseStep 3002129 = 2251597) B2251597
theorem B3002147 : Blo 1332985 3002147 := bstep (se 1 (by rfl) ⟨2251610, by rfl⟩ : syracuseStep 3002147 = 4503221) B4503221
theorem B11390989 : Blo 1332985 11390989 := bstep (se 3 (by rfl) ⟨2135810, by rfl⟩ : syracuseStep 11390989 = 4271621) B4271621
theorem B6500387 : Blo 1332985 6500387 := bstep (se 1 (by rfl) ⟨4875290, by rfl⟩ : syracuseStep 6500387 = 9750581) B9750581
theorem B3002417 : Blo 1332985 3002417 := bstep (se 2 (by rfl) ⟨1125906, by rfl⟩ : syracuseStep 3002417 = 2251813) B2251813
theorem B3002435 : Blo 1332985 3002435 := bstep (se 1 (by rfl) ⟨2251826, by rfl⟩ : syracuseStep 3002435 = 4503653) B4503653
theorem B22212805 : Blo 1332985 22212805 := bstep (se 4 (by rfl) ⟨2082450, by rfl⟩ : syracuseStep 22212805 = 4164901) B4164901
theorem B4501709 : Blo 1332985 4501709 := bstep (se 3 (by rfl) ⟨844070, by rfl⟩ : syracuseStep 4501709 = 1688141) B1688141
theorem B4272365 : Blo 1332985 4272365 := bstep (se 3 (by rfl) ⟨801068, by rfl⟩ : syracuseStep 4272365 = 1602137) B1602137
theorem B4501763 : Blo 1332985 4501763 := bstep (se 1 (by rfl) ⟨3376322, by rfl⟩ : syracuseStep 4501763 = 6752645) B6752645
theorem B3797293 : Blo 1332985 3797293 := bstep (se 3 (by rfl) ⟨711992, by rfl⟩ : syracuseStep 3797293 = 1423985) B1423985
theorem B3002705 : Blo 1332985 3002705 := bstep (se 2 (by rfl) ⟨1126014, by rfl⟩ : syracuseStep 3002705 = 2252029) B2252029
theorem B3002723 : Blo 1332985 3002723 := bstep (se 1 (by rfl) ⟨2252042, by rfl⟩ : syracuseStep 3002723 = 4504085) B4504085
theorem B5697955 : Blo 1332985 5697955 := bstep (se 1 (by rfl) ⟨4273466, by rfl⟩ : syracuseStep 5697955 = 8546933) B8546933
theorem B17093045 : Blo 1332985 17093045 := bstep (se 5 (by rfl) ⟨801236, by rfl⟩ : syracuseStep 17093045 = 1602473) B1602473
theorem B2281921 : Blo 1332985 2281921 := bstep (se 2 (by rfl) ⟨855720, by rfl⟩ : syracuseStep 2281921 = 1711441) B1711441
theorem B4502033 : Blo 1332985 4502033 := bstep (se 2 (by rfl) ⟨1688262, by rfl⟩ : syracuseStep 4502033 = 3376525) B3376525
theorem B3002993 : Blo 1332985 3002993 := bstep (se 2 (by rfl) ⟨1126122, by rfl⟩ : syracuseStep 3002993 = 2252245) B2252245
theorem B3003011 : Blo 1332985 3003011 := bstep (se 1 (by rfl) ⟨2252258, by rfl⟩ : syracuseStep 3003011 = 4504517) B4504517
theorem B12169925 : Blo 1332985 12169925 := bstep (se 4 (by rfl) ⟨1140930, by rfl⟩ : syracuseStep 12169925 = 2281861) B2281861
theorem B2282195 : Blo 1332985 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B3420913 : Blo 1332985 3420913 := bstep (se 2 (by rfl) ⟨1282842, by rfl⟩ : syracuseStep 3420913 = 2565685) B2565685
theorem B2028289 : Blo 1332985 2028289 := bstep (se 2 (by rfl) ⟨760608, by rfl⟩ : syracuseStep 2028289 = 1521217) B1521217
theorem B2249491 : Blo 1332985 2249491 := bstep (se 1 (by rfl) ⟨1687118, by rfl⟩ : syracuseStep 2249491 = 3374237) B3374237
theorem B5133091 : Blo 1332985 5133091 := bstep (se 1 (by rfl) ⟨3849818, by rfl⟩ : syracuseStep 5133091 = 7699637) B7699637
theorem B8549189 : Blo 1332985 8549189 := bstep (se 4 (by rfl) ⟨801486, by rfl⟩ : syracuseStep 8549189 = 1602973) B1602973
theorem B4871011 : Blo 1332985 4871011 := bstep (se 1 (by rfl) ⟨3653258, by rfl⟩ : syracuseStep 4871011 = 7306517) B7306517
theorem B4805489 : Blo 1332985 4805489 := bstep (se 2 (by rfl) ⟨1802058, by rfl⟩ : syracuseStep 4805489 = 3604117) B3604117
theorem B3003281 : Blo 1332985 3003281 := bstep (se 2 (by rfl) ⟨1126230, by rfl⟩ : syracuseStep 3003281 = 2252461) B2252461
theorem B2249633 : Blo 1332985 2249633 := bstep (se 2 (by rfl) ⟨843612, by rfl⟩ : syracuseStep 2249633 = 1687225) B1687225
theorem B3003299 : Blo 1332985 3003299 := bstep (se 1 (by rfl) ⟨2252474, by rfl⟩ : syracuseStep 3003299 = 4504949) B4504949
theorem B2249761 : Blo 1332985 2249761 := bstep (se 2 (by rfl) ⟨843660, by rfl⟩ : syracuseStep 2249761 = 1687321) B1687321
theorem B4502573 : Blo 1332985 4502573 := bstep (se 3 (by rfl) ⟨844232, by rfl⟩ : syracuseStep 4502573 = 1688465) B1688465
theorem B2249795 : Blo 1332985 2249795 := bstep (se 1 (by rfl) ⟨1687346, by rfl⟩ : syracuseStep 2249795 = 3374693) B3374693
theorem B2282593 : Blo 1332985 2282593 := bstep (se 2 (by rfl) ⟨855972, by rfl⟩ : syracuseStep 2282593 = 1711945) B1711945
theorem B4502627 : Blo 1332985 4502627 := bstep (se 1 (by rfl) ⟨3376970, by rfl⟩ : syracuseStep 4502627 = 6753941) B6753941
theorem B5067917 : Blo 1332985 5067917 := bstep (se 3 (by rfl) ⟨950234, by rfl⟩ : syracuseStep 5067917 = 1900469) B1900469
theorem B3003569 : Blo 1332985 3003569 := bstep (se 2 (by rfl) ⟨1126338, by rfl⟩ : syracuseStep 3003569 = 2252677) B2252677
theorem B2249923 : Blo 1332985 2249923 := bstep (se 1 (by rfl) ⟨1687442, by rfl⟩ : syracuseStep 2249923 = 3374885) B3374885
theorem B3003587 : Blo 1332985 3003587 := bstep (se 1 (by rfl) ⟨2252690, by rfl⟩ : syracuseStep 3003587 = 4505381) B4505381
theorem B2847953 : Blo 1332985 2847953 := bstep (se 2 (by rfl) ⟨1067982, by rfl⟩ : syracuseStep 2847953 = 2135965) B2135965
theorem B8115491 : Blo 1332985 8115491 := bstep (se 1 (by rfl) ⟨6086618, by rfl⟩ : syracuseStep 8115491 = 12173237) B12173237
theorem B22230325 : Blo 1332985 22230325 := bstep (se 5 (by rfl) ⟨1042046, by rfl⟩ : syracuseStep 22230325 = 2084093) B2084093
theorem B11392325 : Blo 1332985 11392325 := bstep (se 4 (by rfl) ⟨1068030, by rfl⟩ : syracuseStep 11392325 = 2136061) B2136061
theorem B2250065 : Blo 1332985 2250065 := bstep (se 2 (by rfl) ⟨843774, by rfl⟩ : syracuseStep 2250065 = 1687549) B1687549
theorem B3798353 : Blo 1332985 3798353 := bstep (se 2 (by rfl) ⟨1424382, by rfl⟩ : syracuseStep 3798353 = 2848765) B2848765
theorem B4502897 : Blo 1332985 4502897 := bstep (se 2 (by rfl) ⟨1688586, by rfl⟩ : syracuseStep 4502897 = 3377173) B3377173
theorem B1602931 : Blo 1332985 1602931 := bstep (se 1 (by rfl) ⟨1202198, by rfl⟩ : syracuseStep 1602931 = 2404397) B2404397
theorem B2250193 : Blo 1332985 2250193 := bstep (se 2 (by rfl) ⟨843822, by rfl⟩ : syracuseStep 2250193 = 1687645) B1687645
theorem B2250227 : Blo 1332985 2250227 := bstep (se 1 (by rfl) ⟨1687670, by rfl⟩ : syracuseStep 2250227 = 3375341) B3375341
theorem B2135555 : Blo 1332985 2135555 := bstep (se 1 (by rfl) ⟨1601666, by rfl⟩ : syracuseStep 2135555 = 3203333) B3203333
theorem B1734179 : Blo 1332985 1734179 := bstep (se 1 (by rfl) ⟨1300634, by rfl⟩ : syracuseStep 1734179 = 2601269) B2601269
theorem B1898083 : Blo 1332985 1898083 := bstep (se 1 (by rfl) ⟨1423562, by rfl⟩ : syracuseStep 1898083 = 2847125) B2847125
theorem B2135651 : Blo 1332985 2135651 := bstep (se 1 (by rfl) ⟨1601738, by rfl⟩ : syracuseStep 2135651 = 3203477) B3203477
theorem B2848355 : Blo 1332985 2848355 := bstep (se 1 (by rfl) ⟨2136266, by rfl⟩ : syracuseStep 2848355 = 4272533) B4272533
theorem B2250355 : Blo 1332985 2250355 := bstep (se 1 (by rfl) ⟨1687766, by rfl⟩ : syracuseStep 2250355 = 3375533) B3375533
theorem B2135683 : Blo 1332985 2135683 := bstep (se 1 (by rfl) ⟨1601762, by rfl⟩ : syracuseStep 2135683 = 3203525) B3203525
theorem B10122893 : Blo 1332985 10122893 := bstep (se 3 (by rfl) ⟨1898042, by rfl⟩ : syracuseStep 10122893 = 3796085) B3796085
theorem B2250497 : Blo 1332985 2250497 := bstep (se 2 (by rfl) ⟨843936, by rfl⟩ : syracuseStep 2250497 = 1687873) B1687873
theorem B1332995 : Blo 1332985 1332995 := bstep (se 1 (by rfl) ⟨999746, by rfl⟩ : syracuseStep 1332995 = 1999493) B1999493
theorem B1333011 : Blo 1332985 1333011 := bstep (se 1 (by rfl) ⟨999758, by rfl⟩ : syracuseStep 1333011 = 1999517) B1999517
theorem B1333027 : Blo 1332985 1333027 := bstep (se 1 (by rfl) ⟨999770, by rfl⟩ : syracuseStep 1333027 = 1999541) B1999541
theorem B1333043 : Blo 1332985 1333043 := bstep (se 1 (by rfl) ⟨999782, by rfl⟩ : syracuseStep 1333043 = 1999565) B1999565
theorem B1333059 : Blo 1332985 1333059 := bstep (se 1 (by rfl) ⟨999794, by rfl⟩ : syracuseStep 1333059 = 1999589) B1999589
theorem B1333075 : Blo 1332985 1333075 := bstep (se 1 (by rfl) ⟨999806, by rfl⟩ : syracuseStep 1333075 = 1999613) B1999613
theorem B1333091 : Blo 1332985 1333091 := bstep (se 1 (by rfl) ⟨999818, by rfl⟩ : syracuseStep 1333091 = 1999637) B1999637
theorem B11401073 : Blo 1332985 11401073 := bstep (se 2 (by rfl) ⟨4275402, by rfl⟩ : syracuseStep 11401073 = 8550805) B8550805
theorem B6756209 : Blo 1332985 6756209 := bstep (se 2 (by rfl) ⟨2533578, by rfl⟩ : syracuseStep 6756209 = 5067157) B5067157
theorem B1333107 : Blo 1332985 1333107 := bstep (se 1 (by rfl) ⟨999830, by rfl⟩ : syracuseStep 1333107 = 1999661) B1999661
theorem B2250625 : Blo 1332985 2250625 := bstep (se 2 (by rfl) ⟨843984, by rfl⟩ : syracuseStep 2250625 = 1687969) B1687969
theorem B1333123 : Blo 1332985 1333123 := bstep (se 1 (by rfl) ⟨999842, by rfl⟩ : syracuseStep 1333123 = 1999685) B1999685
theorem B4503437 : Blo 1332985 4503437 := bstep (se 3 (by rfl) ⟨844394, by rfl⟩ : syracuseStep 4503437 = 1688789) B1688789
theorem B1333139 : Blo 1332985 1333139 := bstep (se 1 (by rfl) ⟨999854, by rfl⟩ : syracuseStep 1333139 = 1999709) B1999709
theorem B1333155 : Blo 1332985 1333155 := bstep (se 1 (by rfl) ⟨999866, by rfl⟩ : syracuseStep 1333155 = 1999733) B1999733
theorem B2250659 : Blo 1332985 2250659 := bstep (se 1 (by rfl) ⟨1687994, by rfl⟩ : syracuseStep 2250659 = 3375989) B3375989
theorem B1333171 : Blo 1332985 1333171 := bstep (se 1 (by rfl) ⟨999878, by rfl⟩ : syracuseStep 1333171 = 1999757) B1999757
theorem B1898419 : Blo 1332985 1898419 := bstep (se 1 (by rfl) ⟨1423814, by rfl⟩ : syracuseStep 1898419 = 2847629) B2847629
theorem B1333187 : Blo 1332985 1333187 := bstep (se 1 (by rfl) ⟨999890, by rfl⟩ : syracuseStep 1333187 = 1999781) B1999781
theorem B4503491 : Blo 1332985 4503491 := bstep (se 1 (by rfl) ⟨3377618, by rfl⟩ : syracuseStep 4503491 = 6755237) B6755237
theorem B1333203 : Blo 1332985 1333203 := bstep (se 1 (by rfl) ⟨999902, by rfl⟩ : syracuseStep 1333203 = 1999805) B1999805
theorem B1333219 : Blo 1332985 1333219 := bstep (se 1 (by rfl) ⟨999914, by rfl⟩ : syracuseStep 1333219 = 1999829) B1999829
theorem B3799025 : Blo 1332985 3799025 := bstep (se 2 (by rfl) ⟨1424634, by rfl⟩ : syracuseStep 3799025 = 2849269) B2849269
theorem B1333235 : Blo 1332985 1333235 := bstep (se 1 (by rfl) ⟨999926, by rfl⟩ : syracuseStep 1333235 = 1999853) B1999853
theorem B1333251 : Blo 1332985 1333251 := bstep (se 1 (by rfl) ⟨999938, by rfl⟩ : syracuseStep 1333251 = 1999877) B1999877
theorem B1333267 : Blo 1332985 1333267 := bstep (se 1 (by rfl) ⟨999950, by rfl⟩ : syracuseStep 1333267 = 1999901) B1999901
theorem B1333283 : Blo 1332985 1333283 := bstep (se 1 (by rfl) ⟨999962, by rfl⟩ : syracuseStep 1333283 = 1999925) B1999925
theorem B2250787 : Blo 1332985 2250787 := bstep (se 1 (by rfl) ⟨1688090, by rfl⟩ : syracuseStep 2250787 = 3376181) B3376181
theorem B1333299 : Blo 1332985 1333299 := bstep (se 1 (by rfl) ⟨999974, by rfl⟩ : syracuseStep 1333299 = 1999949) B1999949
theorem B1333315 : Blo 1332985 1333315 := bstep (se 1 (by rfl) ⟨999986, by rfl⟩ : syracuseStep 1333315 = 1999973) B1999973
theorem B1333331 : Blo 1332985 1333331 := bstep (se 1 (by rfl) ⟨999998, by rfl⟩ : syracuseStep 1333331 = 1999997) B1999997
theorem B1333347 : Blo 1332985 1333347 := bstep (se 1 (by rfl) ⟨1000010, by rfl⟩ : syracuseStep 1333347 = 2000021) B2000021
theorem B1333363 : Blo 1332985 1333363 := bstep (se 1 (by rfl) ⟨1000022, by rfl⟩ : syracuseStep 1333363 = 2000045) B2000045
theorem B1333379 : Blo 1332985 1333379 := bstep (se 1 (by rfl) ⟨1000034, by rfl⟩ : syracuseStep 1333379 = 2000069) B2000069
theorem B1333395 : Blo 1332985 1333395 := bstep (se 1 (by rfl) ⟨1000046, by rfl⟩ : syracuseStep 1333395 = 2000093) B2000093
theorem B1333411 : Blo 1332985 1333411 := bstep (se 1 (by rfl) ⟨1000058, by rfl⟩ : syracuseStep 1333411 = 2000117) B2000117
theorem B2250929 : Blo 1332985 2250929 := bstep (se 2 (by rfl) ⟨844098, by rfl⟩ : syracuseStep 2250929 = 1688197) B1688197
theorem B1333427 : Blo 1332985 1333427 := bstep (se 1 (by rfl) ⟨1000070, by rfl⟩ : syracuseStep 1333427 = 2000141) B2000141
theorem B1333443 : Blo 1332985 1333443 := bstep (se 1 (by rfl) ⟨1000082, by rfl⟩ : syracuseStep 1333443 = 2000165) B2000165
theorem B4503761 : Blo 1332985 4503761 := bstep (se 2 (by rfl) ⟨1688910, by rfl⟩ : syracuseStep 4503761 = 3377821) B3377821
theorem B3471569 : Blo 1332985 3471569 := bstep (se 2 (by rfl) ⟨1301838, by rfl⟩ : syracuseStep 3471569 = 2603677) B2603677
theorem B1333459 : Blo 1332985 1333459 := bstep (se 1 (by rfl) ⟨1000094, by rfl⟩ : syracuseStep 1333459 = 2000189) B2000189
theorem B1333475 : Blo 1332985 1333475 := bstep (se 1 (by rfl) ⟨1000106, by rfl⟩ : syracuseStep 1333475 = 2000213) B2000213
theorem B1333491 : Blo 1332985 1333491 := bstep (se 1 (by rfl) ⟨1000118, by rfl⟩ : syracuseStep 1333491 = 2000237) B2000237
theorem B1333507 : Blo 1332985 1333507 := bstep (se 1 (by rfl) ⟨1000130, by rfl⟩ : syracuseStep 1333507 = 2000261) B2000261
theorem B1333523 : Blo 1332985 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B1333539 : Blo 1332985 1333539 := bstep (se 1 (by rfl) ⟨1000154, by rfl⟩ : syracuseStep 1333539 = 2000309) B2000309
theorem B2251057 : Blo 1332985 2251057 := bstep (se 2 (by rfl) ⟨844146, by rfl⟩ : syracuseStep 2251057 = 1688293) B1688293
theorem B1333555 : Blo 1332985 1333555 := bstep (se 1 (by rfl) ⟨1000166, by rfl⟩ : syracuseStep 1333555 = 2000333) B2000333
theorem B1333571 : Blo 1332985 1333571 := bstep (se 1 (by rfl) ⟨1000178, by rfl⟩ : syracuseStep 1333571 = 2000357) B2000357
theorem B1333587 : Blo 1332985 1333587 := bstep (se 1 (by rfl) ⟨1000190, by rfl⟩ : syracuseStep 1333587 = 2000381) B2000381
theorem B2251091 : Blo 1332985 2251091 := bstep (se 1 (by rfl) ⟨1688318, by rfl⟩ : syracuseStep 2251091 = 3376637) B3376637
theorem B1333603 : Blo 1332985 1333603 := bstep (se 1 (by rfl) ⟨1000202, by rfl⟩ : syracuseStep 1333603 = 2000405) B2000405
theorem B1333619 : Blo 1332985 1333619 := bstep (se 1 (by rfl) ⟨1000214, by rfl⟩ : syracuseStep 1333619 = 2000429) B2000429
theorem B1333635 : Blo 1332985 1333635 := bstep (se 1 (by rfl) ⟨1000226, by rfl⟩ : syracuseStep 1333635 = 2000453) B2000453
theorem B9247117 : Blo 1332985 9247117 := bstep (se 3 (by rfl) ⟨1733834, by rfl⟩ : syracuseStep 9247117 = 3467669) B3467669
theorem B1333651 : Blo 1332985 1333651 := bstep (se 1 (by rfl) ⟨1000238, by rfl⟩ : syracuseStep 1333651 = 2000477) B2000477
theorem B1333667 : Blo 1332985 1333667 := bstep (se 1 (by rfl) ⟨1000250, by rfl⟩ : syracuseStep 1333667 = 2000501) B2000501
theorem B1333683 : Blo 1332985 1333683 := bstep (se 1 (by rfl) ⟨1000262, by rfl⟩ : syracuseStep 1333683 = 2000525) B2000525
theorem B1333699 : Blo 1332985 1333699 := bstep (se 1 (by rfl) ⟨1000274, by rfl⟩ : syracuseStep 1333699 = 2000549) B2000549
theorem B1333715 : Blo 1332985 1333715 := bstep (se 1 (by rfl) ⟨1000286, by rfl⟩ : syracuseStep 1333715 = 2000573) B2000573
theorem B2251219 : Blo 1332985 2251219 := bstep (se 1 (by rfl) ⟨1688414, by rfl⟩ : syracuseStep 2251219 = 3376829) B3376829
theorem B1898977 : Blo 1332985 1898977 := bstep (se 2 (by rfl) ⟨712116, by rfl⟩ : syracuseStep 1898977 = 1424233) B1424233
theorem B1333731 : Blo 1332985 1333731 := bstep (se 1 (by rfl) ⟨1000298, by rfl⟩ : syracuseStep 1333731 = 2000597) B2000597
theorem B2849251 : Blo 1332985 2849251 := bstep (se 1 (by rfl) ⟨2136938, by rfl⟩ : syracuseStep 2849251 = 4273877) B4273877
theorem B1333747 : Blo 1332985 1333747 := bstep (se 1 (by rfl) ⟨1000310, by rfl⟩ : syracuseStep 1333747 = 2000621) B2000621
theorem B1899011 : Blo 1332985 1899011 := bstep (se 1 (by rfl) ⟨1424258, by rfl⟩ : syracuseStep 1899011 = 2848517) B2848517
theorem B1333763 : Blo 1332985 1333763 := bstep (se 1 (by rfl) ⟨1000322, by rfl⟩ : syracuseStep 1333763 = 2000645) B2000645
theorem B2136593 : Blo 1332985 2136593 := bstep (se 2 (by rfl) ⟨801222, by rfl⟩ : syracuseStep 2136593 = 1602445) B1602445
theorem B1333779 : Blo 1332985 1333779 := bstep (se 1 (by rfl) ⟨1000334, by rfl⟩ : syracuseStep 1333779 = 2000669) B2000669
theorem B1333795 : Blo 1332985 1333795 := bstep (se 1 (by rfl) ⟨1000346, by rfl⟩ : syracuseStep 1333795 = 2000693) B2000693
theorem B1333811 : Blo 1332985 1333811 := bstep (se 1 (by rfl) ⟨1000358, by rfl⟩ : syracuseStep 1333811 = 2000717) B2000717
theorem B1333827 : Blo 1332985 1333827 := bstep (se 1 (by rfl) ⟨1000370, by rfl⟩ : syracuseStep 1333827 = 2000741) B2000741
theorem B1333843 : Blo 1332985 1333843 := bstep (se 1 (by rfl) ⟨1000382, by rfl⟩ : syracuseStep 1333843 = 2000765) B2000765
theorem B2251361 : Blo 1332985 2251361 := bstep (se 2 (by rfl) ⟨844260, by rfl⟩ : syracuseStep 2251361 = 1688521) B1688521
theorem B1333859 : Blo 1332985 1333859 := bstep (se 1 (by rfl) ⟨1000394, by rfl⟩ : syracuseStep 1333859 = 2000789) B2000789
theorem B16439921 : Blo 1332985 16439921 := bstep (se 2 (by rfl) ⟨6164970, by rfl⟩ : syracuseStep 16439921 = 12329941) B12329941
theorem B1333875 : Blo 1332985 1333875 := bstep (se 1 (by rfl) ⟨1000406, by rfl⟩ : syracuseStep 1333875 = 2000813) B2000813
theorem B1333891 : Blo 1332985 1333891 := bstep (se 1 (by rfl) ⟨1000418, by rfl⟩ : syracuseStep 1333891 = 2000837) B2000837
theorem B1333907 : Blo 1332985 1333907 := bstep (se 1 (by rfl) ⟨1000430, by rfl⟩ : syracuseStep 1333907 = 2000861) B2000861
theorem B1333923 : Blo 1332985 1333923 := bstep (se 1 (by rfl) ⟨1000442, by rfl⟩ : syracuseStep 1333923 = 2000885) B2000885
theorem B4274851 : Blo 1332985 4274851 := bstep (se 1 (by rfl) ⟨3206138, by rfl⟩ : syracuseStep 4274851 = 6412277) B6412277
theorem B1333939 : Blo 1332985 1333939 := bstep (se 1 (by rfl) ⟨1000454, by rfl⟩ : syracuseStep 1333939 = 2000909) B2000909
theorem B1333955 : Blo 1332985 1333955 := bstep (se 1 (by rfl) ⟨1000466, by rfl⟩ : syracuseStep 1333955 = 2000933) B2000933
theorem B5061325 : Blo 1332985 5061325 := bstep (se 3 (by rfl) ⟨948998, by rfl⟩ : syracuseStep 5061325 = 1897997) B1897997
theorem B1333971 : Blo 1332985 1333971 := bstep (se 1 (by rfl) ⟨1000478, by rfl⟩ : syracuseStep 1333971 = 2000957) B2000957
theorem B2251489 : Blo 1332985 2251489 := bstep (se 2 (by rfl) ⟨844308, by rfl⟩ : syracuseStep 2251489 = 1688617) B1688617
theorem B1333987 : Blo 1332985 1333987 := bstep (se 1 (by rfl) ⟨1000490, by rfl⟩ : syracuseStep 1333987 = 2000981) B2000981
theorem B4504301 : Blo 1332985 4504301 := bstep (se 3 (by rfl) ⟨844556, by rfl⟩ : syracuseStep 4504301 = 1689113) B1689113
theorem B1334003 : Blo 1332985 1334003 := bstep (se 1 (by rfl) ⟨1000502, by rfl⟩ : syracuseStep 1334003 = 2001005) B2001005
theorem B1334019 : Blo 1332985 1334019 := bstep (se 1 (by rfl) ⟨1000514, by rfl⟩ : syracuseStep 1334019 = 2001029) B2001029
theorem B2251523 : Blo 1332985 2251523 := bstep (se 1 (by rfl) ⟨1688642, by rfl⟩ : syracuseStep 2251523 = 3377285) B3377285
theorem B3799811 : Blo 1332985 3799811 := bstep (se 1 (by rfl) ⟨2849858, by rfl⟩ : syracuseStep 3799811 = 5699717) B5699717
theorem B7592717 : Blo 1332985 7592717 := bstep (se 3 (by rfl) ⟨1423634, by rfl⟩ : syracuseStep 7592717 = 2847269) B2847269
theorem B1424147 : Blo 1332985 1424147 := bstep (se 1 (by rfl) ⟨1068110, by rfl⟩ : syracuseStep 1424147 = 2136221) B2136221
theorem B1334035 : Blo 1332985 1334035 := bstep (se 1 (by rfl) ⟨1000526, by rfl⟩ : syracuseStep 1334035 = 2001053) B2001053
theorem B6495011 : Blo 1332985 6495011 := bstep (se 1 (by rfl) ⟨4871258, by rfl⟩ : syracuseStep 6495011 = 9742517) B9742517
theorem B1334051 : Blo 1332985 1334051 := bstep (se 1 (by rfl) ⟨1000538, by rfl⟩ : syracuseStep 1334051 = 2001077) B2001077
theorem B4504355 : Blo 1332985 4504355 := bstep (se 1 (by rfl) ⟨3378266, by rfl⟩ : syracuseStep 4504355 = 6756533) B6756533
theorem B4274993 : Blo 1332985 4274993 := bstep (se 2 (by rfl) ⟨1603122, by rfl⟩ : syracuseStep 4274993 = 3206245) B3206245
theorem B5700401 : Blo 1332985 5700401 := bstep (se 2 (by rfl) ⟨2137650, by rfl⟩ : syracuseStep 5700401 = 4275301) B4275301
theorem B1334067 : Blo 1332985 1334067 := bstep (se 1 (by rfl) ⟨1000550, by rfl⟩ : syracuseStep 1334067 = 2001101) B2001101
theorem B32889653 : Blo 1332985 32889653 := bstep (se 5 (by rfl) ⟨1541702, by rfl⟩ : syracuseStep 32889653 = 3083405) B3083405
theorem B1334083 : Blo 1332985 1334083 := bstep (se 1 (by rfl) ⟨1000562, by rfl⟩ : syracuseStep 1334083 = 2001125) B2001125
theorem B1334099 : Blo 1332985 1334099 := bstep (se 1 (by rfl) ⟨1000574, by rfl⟩ : syracuseStep 1334099 = 2001149) B2001149
theorem B1334115 : Blo 1332985 1334115 := bstep (se 1 (by rfl) ⟨1000586, by rfl⟩ : syracuseStep 1334115 = 2001173) B2001173
theorem B1645427 : Blo 1332985 1645427 := bstep (se 1 (by rfl) ⟨1234070, by rfl⟩ : syracuseStep 1645427 = 2468141) B2468141
theorem B1334131 : Blo 1332985 1334131 := bstep (se 1 (by rfl) ⟨1000598, by rfl⟩ : syracuseStep 1334131 = 2001197) B2001197
theorem B1334147 : Blo 1332985 1334147 := bstep (se 1 (by rfl) ⟨1000610, by rfl⟩ : syracuseStep 1334147 = 2001221) B2001221
theorem B2251651 : Blo 1332985 2251651 := bstep (se 1 (by rfl) ⟨1688738, by rfl⟩ : syracuseStep 2251651 = 3377477) B3377477
theorem B1334163 : Blo 1332985 1334163 := bstep (se 1 (by rfl) ⟨1000622, by rfl⟩ : syracuseStep 1334163 = 2001245) B2001245
theorem B1334179 : Blo 1332985 1334179 := bstep (se 1 (by rfl) ⟨1000634, by rfl⟩ : syracuseStep 1334179 = 2001269) B2001269
theorem B4275107 : Blo 1332985 4275107 := bstep (se 1 (by rfl) ⟨3206330, by rfl⟩ : syracuseStep 4275107 = 6412661) B6412661
theorem B1334195 : Blo 1332985 1334195 := bstep (se 1 (by rfl) ⟨1000646, by rfl⟩ : syracuseStep 1334195 = 2001293) B2001293
theorem B1334211 : Blo 1332985 1334211 := bstep (se 1 (by rfl) ⟨1000658, by rfl⟩ : syracuseStep 1334211 = 2001317) B2001317
theorem B1334227 : Blo 1332985 1334227 := bstep (se 1 (by rfl) ⟨1000670, by rfl⟩ : syracuseStep 1334227 = 2001341) B2001341
theorem B1334243 : Blo 1332985 1334243 := bstep (se 1 (by rfl) ⟨1000682, by rfl⟩ : syracuseStep 1334243 = 2001365) B2001365
theorem B1334259 : Blo 1332985 1334259 := bstep (se 1 (by rfl) ⟨1000694, by rfl⟩ : syracuseStep 1334259 = 2001389) B2001389
theorem B1334275 : Blo 1332985 1334275 := bstep (se 1 (by rfl) ⟨1000706, by rfl⟩ : syracuseStep 1334275 = 2001413) B2001413
theorem B2251793 : Blo 1332985 2251793 := bstep (se 2 (by rfl) ⟨844422, by rfl⟩ : syracuseStep 2251793 = 1688845) B1688845
theorem B1334291 : Blo 1332985 1334291 := bstep (se 1 (by rfl) ⟨1000718, by rfl⟩ : syracuseStep 1334291 = 2001437) B2001437
theorem B1334307 : Blo 1332985 1334307 := bstep (se 1 (by rfl) ⟨1000730, by rfl⟩ : syracuseStep 1334307 = 2001461) B2001461
theorem B1899569 : Blo 1332985 1899569 := bstep (se 2 (by rfl) ⟨712338, by rfl⟩ : syracuseStep 1899569 = 1424677) B1424677
theorem B4504625 : Blo 1332985 4504625 := bstep (se 2 (by rfl) ⟨1689234, by rfl⟩ : syracuseStep 4504625 = 3378469) B3378469
theorem B1334323 : Blo 1332985 1334323 := bstep (se 1 (by rfl) ⟨1000742, by rfl⟩ : syracuseStep 1334323 = 2001485) B2001485
theorem B1334339 : Blo 1332985 1334339 := bstep (se 1 (by rfl) ⟨1000754, by rfl⟩ : syracuseStep 1334339 = 2001509) B2001509
theorem B3800141 : Blo 1332985 3800141 := bstep (se 3 (by rfl) ⟨712526, by rfl⟩ : syracuseStep 3800141 = 1425053) B1425053
theorem B1334355 : Blo 1332985 1334355 := bstep (se 1 (by rfl) ⟨1000766, by rfl⟩ : syracuseStep 1334355 = 2001533) B2001533
theorem B1334371 : Blo 1332985 1334371 := bstep (se 1 (by rfl) ⟨1000778, by rfl⟩ : syracuseStep 1334371 = 2001557) B2001557
theorem B1334387 : Blo 1332985 1334387 := bstep (se 1 (by rfl) ⟨1000790, by rfl⟩ : syracuseStep 1334387 = 2001581) B2001581
theorem B1899649 : Blo 1332985 1899649 := bstep (se 2 (by rfl) ⟨712368, by rfl⟩ : syracuseStep 1899649 = 1424737) B1424737
theorem B1334403 : Blo 1332985 1334403 := bstep (se 1 (by rfl) ⟨1000802, by rfl⟩ : syracuseStep 1334403 = 2001605) B2001605
theorem B3423377 : Blo 1332985 3423377 := bstep (se 2 (by rfl) ⟨1283766, by rfl⟩ : syracuseStep 3423377 = 2567533) B2567533
theorem B2251921 : Blo 1332985 2251921 := bstep (se 2 (by rfl) ⟨844470, by rfl⟩ : syracuseStep 2251921 = 1688941) B1688941
theorem B1334419 : Blo 1332985 1334419 := bstep (se 1 (by rfl) ⟨1000814, by rfl⟩ : syracuseStep 1334419 = 2001629) B2001629
theorem B3800209 : Blo 1332985 3800209 := bstep (se 2 (by rfl) ⟨1425078, by rfl⟩ : syracuseStep 3800209 = 2850157) B2850157
theorem B1334435 : Blo 1332985 1334435 := bstep (se 1 (by rfl) ⟨1000826, by rfl⟩ : syracuseStep 1334435 = 2001653) B2001653
theorem B3374257 : Blo 1332985 3374257 := bstep (se 2 (by rfl) ⟨1265346, by rfl⟩ : syracuseStep 3374257 = 2530693) B2530693
theorem B1334451 : Blo 1332985 1334451 := bstep (se 1 (by rfl) ⟨1000838, by rfl⟩ : syracuseStep 1334451 = 2001677) B2001677
theorem B2251955 : Blo 1332985 2251955 := bstep (se 1 (by rfl) ⟨1688966, by rfl⟩ : syracuseStep 2251955 = 3377933) B3377933
theorem B1334467 : Blo 1332985 1334467 := bstep (se 1 (by rfl) ⟨1000850, by rfl⟩ : syracuseStep 1334467 = 2001701) B2001701
theorem B1334483 : Blo 1332985 1334483 := bstep (se 1 (by rfl) ⟨1000862, by rfl⟩ : syracuseStep 1334483 = 2001725) B2001725
theorem B1334499 : Blo 1332985 1334499 := bstep (se 1 (by rfl) ⟨1000874, by rfl⟩ : syracuseStep 1334499 = 2001749) B2001749
theorem B1334515 : Blo 1332985 1334515 := bstep (se 1 (by rfl) ⟨1000886, by rfl⟩ : syracuseStep 1334515 = 2001773) B2001773
theorem B1334531 : Blo 1332985 1334531 := bstep (se 1 (by rfl) ⟨1000898, by rfl⟩ : syracuseStep 1334531 = 2001797) B2001797
theorem B8543501 : Blo 1332985 8543501 := bstep (se 3 (by rfl) ⟨1601906, by rfl⟩ : syracuseStep 8543501 = 3203813) B3203813
theorem B1334547 : Blo 1332985 1334547 := bstep (se 1 (by rfl) ⟨1000910, by rfl⟩ : syracuseStep 1334547 = 2001821) B2001821
theorem B2530595 : Blo 1332985 2530595 := bstep (se 1 (by rfl) ⟨1897946, by rfl⟩ : syracuseStep 2530595 = 3795893) B3795893
theorem B1334563 : Blo 1332985 1334563 := bstep (se 1 (by rfl) ⟨1000922, by rfl⟩ : syracuseStep 1334563 = 2001845) B2001845
theorem B6757667 : Blo 1332985 6757667 := bstep (se 1 (by rfl) ⟨5068250, by rfl⟩ : syracuseStep 6757667 = 10136501) B10136501
theorem B2252083 : Blo 1332985 2252083 := bstep (se 1 (by rfl) ⟨1689062, by rfl⟩ : syracuseStep 2252083 = 3378125) B3378125
theorem B1334579 : Blo 1332985 1334579 := bstep (se 1 (by rfl) ⟨1000934, by rfl⟩ : syracuseStep 1334579 = 2001869) B2001869
theorem B1334595 : Blo 1332985 1334595 := bstep (se 1 (by rfl) ⟨1000946, by rfl⟩ : syracuseStep 1334595 = 2001893) B2001893
theorem B15392069 : Blo 1332985 15392069 := bstep (se 4 (by rfl) ⟨1443006, by rfl⟩ : syracuseStep 15392069 = 2886013) B2886013
theorem B1334611 : Blo 1332985 1334611 := bstep (se 1 (by rfl) ⟨1000958, by rfl⟩ : syracuseStep 1334611 = 2001917) B2001917
theorem B1334627 : Blo 1332985 1334627 := bstep (se 1 (by rfl) ⟨1000970, by rfl⟩ : syracuseStep 1334627 = 2001941) B2001941
theorem B1334643 : Blo 1332985 1334643 := bstep (se 1 (by rfl) ⟨1000982, by rfl⟩ : syracuseStep 1334643 = 2001965) B2001965
theorem B1334659 : Blo 1332985 1334659 := bstep (se 1 (by rfl) ⟨1000994, by rfl⟩ : syracuseStep 1334659 = 2001989) B2001989
theorem B14433677 : Blo 1332985 14433677 := bstep (se 3 (by rfl) ⟨2706314, by rfl⟩ : syracuseStep 14433677 = 5412629) B5412629
theorem B1334675 : Blo 1332985 1334675 := bstep (se 1 (by rfl) ⟨1001006, by rfl⟩ : syracuseStep 1334675 = 2002013) B2002013
theorem B3800483 : Blo 1332985 3800483 := bstep (se 1 (by rfl) ⟨2850362, by rfl⟩ : syracuseStep 3800483 = 5700725) B5700725
theorem B1334691 : Blo 1332985 1334691 := bstep (se 1 (by rfl) ⟨1001018, by rfl⟩ : syracuseStep 1334691 = 2002037) B2002037
theorem B1334707 : Blo 1332985 1334707 := bstep (se 1 (by rfl) ⟨1001030, by rfl⟩ : syracuseStep 1334707 = 2002061) B2002061
theorem B2252225 : Blo 1332985 2252225 := bstep (se 2 (by rfl) ⟨844584, by rfl⟩ : syracuseStep 2252225 = 1689169) B1689169
theorem B3374531 : Blo 1332985 3374531 := bstep (se 1 (by rfl) ⟨2530898, by rfl⟩ : syracuseStep 3374531 = 5061797) B5061797
theorem B1334723 : Blo 1332985 1334723 := bstep (se 1 (by rfl) ⟨1001042, by rfl⟩ : syracuseStep 1334723 = 2002085) B2002085
theorem B1334739 : Blo 1332985 1334739 := bstep (se 1 (by rfl) ⟨1001054, by rfl⟩ : syracuseStep 1334739 = 2002109) B2002109
theorem B5062115 : Blo 1332985 5062115 := bstep (se 1 (by rfl) ⟨3796586, by rfl⟩ : syracuseStep 5062115 = 7593173) B7593173
theorem B1334755 : Blo 1332985 1334755 := bstep (se 1 (by rfl) ⟨1001066, by rfl⟩ : syracuseStep 1334755 = 2002133) B2002133
theorem B1334771 : Blo 1332985 1334771 := bstep (se 1 (by rfl) ⟨1001078, by rfl⟩ : syracuseStep 1334771 = 2002157) B2002157
theorem B1424899 : Blo 1332985 1424899 := bstep (se 1 (by rfl) ⟨1068674, by rfl⟩ : syracuseStep 1424899 = 2137349) B2137349
theorem B1334787 : Blo 1332985 1334787 := bstep (se 1 (by rfl) ⟨1001090, by rfl⟩ : syracuseStep 1334787 = 2002181) B2002181
theorem B1334803 : Blo 1332985 1334803 := bstep (se 1 (by rfl) ⟨1001102, by rfl⟩ : syracuseStep 1334803 = 2002205) B2002205
theorem B1334819 : Blo 1332985 1334819 := bstep (se 1 (by rfl) ⟨1001114, by rfl⟩ : syracuseStep 1334819 = 2002229) B2002229
theorem B1334835 : Blo 1332985 1334835 := bstep (se 1 (by rfl) ⟨1001126, by rfl⟩ : syracuseStep 1334835 = 2002253) B2002253
theorem B2252353 : Blo 1332985 2252353 := bstep (se 2 (by rfl) ⟨844632, by rfl⟩ : syracuseStep 2252353 = 1689265) B1689265
theorem B1334851 : Blo 1332985 1334851 := bstep (se 1 (by rfl) ⟨1001138, by rfl⟩ : syracuseStep 1334851 = 2002277) B2002277
theorem B4505165 : Blo 1332985 4505165 := bstep (se 3 (by rfl) ⟨844718, by rfl⟩ : syracuseStep 4505165 = 1689437) B1689437
theorem B1334867 : Blo 1332985 1334867 := bstep (se 1 (by rfl) ⟨1001150, by rfl⟩ : syracuseStep 1334867 = 2002301) B2002301
theorem B2252387 : Blo 1332985 2252387 := bstep (se 1 (by rfl) ⟨1689290, by rfl⟩ : syracuseStep 2252387 = 3378581) B3378581
theorem B1334883 : Blo 1332985 1334883 := bstep (se 1 (by rfl) ⟨1001162, by rfl⟩ : syracuseStep 1334883 = 2002325) B2002325
theorem B1334899 : Blo 1332985 1334899 := bstep (se 1 (by rfl) ⟨1001174, by rfl⟩ : syracuseStep 1334899 = 2002349) B2002349
theorem B3374723 : Blo 1332985 3374723 := bstep (se 1 (by rfl) ⟨2531042, by rfl⟩ : syracuseStep 3374723 = 5062085) B5062085
theorem B4505219 : Blo 1332985 4505219 := bstep (se 1 (by rfl) ⟨3378914, by rfl⟩ : syracuseStep 4505219 = 6757829) B6757829
theorem B1334915 : Blo 1332985 1334915 := bstep (se 1 (by rfl) ⟨1001186, by rfl⟩ : syracuseStep 1334915 = 2002373) B2002373
theorem B1334931 : Blo 1332985 1334931 := bstep (se 1 (by rfl) ⟨1001198, by rfl⟩ : syracuseStep 1334931 = 2002397) B2002397
theorem B1334947 : Blo 1332985 1334947 := bstep (se 1 (by rfl) ⟨1001210, by rfl⟩ : syracuseStep 1334947 = 2002421) B2002421
theorem B2850481 : Blo 1332985 2850481 := bstep (se 2 (by rfl) ⟨1068930, by rfl⟩ : syracuseStep 2850481 = 2137861) B2137861
theorem B1334963 : Blo 1332985 1334963 := bstep (se 1 (by rfl) ⟨1001222, by rfl⟩ : syracuseStep 1334963 = 2002445) B2002445
theorem B1334979 : Blo 1332985 1334979 := bstep (se 1 (by rfl) ⟨1001234, by rfl⟩ : syracuseStep 1334979 = 2002469) B2002469
theorem B2252515 : Blo 1332985 2252515 := bstep (se 1 (by rfl) ⟨1689386, by rfl⟩ : syracuseStep 2252515 = 3378773) B3378773
theorem B1687331 : Blo 1332985 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B2137907 : Blo 1332985 2137907 := bstep (se 1 (by rfl) ⟨1603430, by rfl⟩ : syracuseStep 2137907 = 3206861) B3206861
theorem B4276081 : Blo 1332985 4276081 := bstep (se 2 (by rfl) ⟨1603530, by rfl⟩ : syracuseStep 4276081 = 3207061) B3207061
theorem B2252657 : Blo 1332985 2252657 := bstep (se 2 (by rfl) ⟨844746, by rfl⟩ : syracuseStep 2252657 = 1689493) B1689493
theorem B4505489 : Blo 1332985 4505489 := bstep (se 2 (by rfl) ⟨1689558, by rfl⟩ : syracuseStep 4505489 = 3379117) B3379117
theorem B1900435 : Blo 1332985 1900435 := bstep (se 1 (by rfl) ⟨1425326, by rfl⟩ : syracuseStep 1900435 = 2850653) B2850653
theorem B2703299 : Blo 1332985 2703299 := bstep (se 1 (by rfl) ⟨2027474, by rfl⟩ : syracuseStep 2703299 = 4054949) B4054949
theorem B2252785 : Blo 1332985 2252785 := bstep (se 2 (by rfl) ⟨844794, by rfl⟩ : syracuseStep 2252785 = 1689589) B1689589
theorem B15187985 : Blo 1332985 15187985 := bstep (se 2 (by rfl) ⟨5695494, by rfl⟩ : syracuseStep 15187985 = 11390989) B11390989
theorem B6414353 : Blo 1332985 6414353 := bstep (se 2 (by rfl) ⟨2405382, by rfl⟩ : syracuseStep 6414353 = 4810765) B4810765
theorem B4333591 : Blo 1332985 4333591 := bstep (se 1 (by rfl) ⟨3250193, by rfl⟩ : syracuseStep 4333591 = 6500387) B6500387
theorem B3375179 : Blo 1332985 3375179 := bstep (se 1 (by rfl) ⟨2531384, by rfl⟩ : syracuseStep 3375179 = 5062769) B5062769
theorem B3653707 : Blo 1332985 3653707 := bstep (se 1 (by rfl) ⟨2740280, by rfl⟩ : syracuseStep 3653707 = 5480561) B5480561
theorem B14418071 : Blo 1332985 14418071 := bstep (se 1 (by rfl) ⟨10813553, by rfl⟩ : syracuseStep 14418071 = 21627107) B21627107
theorem B8544473 : Blo 1332985 8544473 := bstep (se 2 (by rfl) ⟨3204177, by rfl⟩ : syracuseStep 8544473 = 6408355) B6408355
theorem B11395363 : Blo 1332985 11395363 := bstep (se 1 (by rfl) ⟨8546522, by rfl⟩ : syracuseStep 11395363 = 17093045) B17093045
theorem B6750539 : Blo 1332985 6750539 := bstep (se 1 (by rfl) ⟨5062904, by rfl⟩ : syracuseStep 6750539 = 10125809) B10125809
theorem B18497909 : Blo 1332985 18497909 := bstep (se 5 (by rfl) ⟨867089, by rfl⟩ : syracuseStep 18497909 = 1734179) B1734179
theorem B5063057 : Blo 1332985 5063057 := bstep (se 2 (by rfl) ⟨1898646, by rfl⟩ : syracuseStep 5063057 = 3797293) B3797293
theorem B5136785 : Blo 1332985 5136785 := bstep (se 2 (by rfl) ⟨1926294, by rfl⟩ : syracuseStep 5136785 = 3852589) B3852589
theorem B3375553 : Blo 1332985 3375553 := bstep (se 2 (by rfl) ⟨1265832, by rfl⟩ : syracuseStep 3375553 = 2531665) B2531665
theorem B12329489 : Blo 1332985 12329489 := bstep (se 2 (by rfl) ⟨4623558, by rfl⟩ : syracuseStep 12329489 = 9247117) B9247117
theorem B6840877 : Blo 1332985 6840877 := bstep (se 3 (by rfl) ⟨1282664, by rfl⟩ : syracuseStep 6840877 = 2565329) B2565329
theorem B3203659 : Blo 1332985 3203659 := bstep (se 1 (by rfl) ⟨2402744, by rfl⟩ : syracuseStep 3203659 = 4805489) B4805489
theorem B1499755 : Blo 1332985 1499755 := bstep (se 1 (by rfl) ⟨1124816, by rfl⟩ : syracuseStep 1499755 = 2249633) B2249633
theorem B2531969 : Blo 1332985 2531969 := bstep (se 2 (by rfl) ⟨949488, by rfl⟩ : syracuseStep 2531969 = 1898977) B1898977
theorem B1999499 : Blo 1332985 1999499 := bstep (se 1 (by rfl) ⟨1499624, by rfl⟩ : syracuseStep 1999499 = 2999249) B2999249
theorem B1999511 : Blo 1332985 1999511 := bstep (se 1 (by rfl) ⟨1499633, by rfl⟩ : syracuseStep 1999511 = 2999267) B2999267
theorem B1499863 : Blo 1332985 1499863 := bstep (se 1 (by rfl) ⟨1124897, by rfl⟩ : syracuseStep 1499863 = 2249795) B2249795
theorem B1999577 : Blo 1332985 1999577 := bstep (se 2 (by rfl) ⟨749841, by rfl⟩ : syracuseStep 1999577 = 1499683) B1499683
theorem B6415121 : Blo 1332985 6415121 := bstep (se 2 (by rfl) ⟨2405670, by rfl⟩ : syracuseStep 6415121 = 4811341) B4811341
theorem B1999691 : Blo 1332985 1999691 := bstep (se 1 (by rfl) ⟨1499768, by rfl⟩ : syracuseStep 1999691 = 2999537) B2999537
theorem B1999703 : Blo 1332985 1999703 := bstep (se 1 (by rfl) ⟨1499777, by rfl⟩ : syracuseStep 1999703 = 2999555) B2999555
theorem B7594883 : Blo 1332985 7594883 := bstep (se 1 (by rfl) ⟨5696162, by rfl⟩ : syracuseStep 7594883 = 11392325) B11392325
theorem B1500043 : Blo 1332985 1500043 := bstep (se 1 (by rfl) ⟨1125032, by rfl⟩ : syracuseStep 1500043 = 2250065) B2250065
theorem B2532235 : Blo 1332985 2532235 := bstep (se 1 (by rfl) ⟨1899176, by rfl⟩ : syracuseStep 2532235 = 3798353) B3798353
theorem B1999769 : Blo 1332985 1999769 := bstep (se 2 (by rfl) ⟨749913, by rfl⟩ : syracuseStep 1999769 = 1499827) B1499827
theorem B5694401 : Blo 1332985 5694401 := bstep (se 2 (by rfl) ⟨2135400, by rfl⟩ : syracuseStep 5694401 = 4270801) B4270801
theorem B1541111 : Blo 1332985 1541111 := bstep (se 1 (by rfl) ⟨1155833, by rfl⟩ : syracuseStep 1541111 = 2311667) B2311667
theorem B1500151 : Blo 1332985 1500151 := bstep (se 1 (by rfl) ⟨1125113, by rfl⟩ : syracuseStep 1500151 = 2250227) B2250227
theorem B2704385 : Blo 1332985 2704385 := bstep (se 2 (by rfl) ⟨1014144, by rfl⟩ : syracuseStep 2704385 = 2028289) B2028289
theorem B1999883 : Blo 1332985 1999883 := bstep (se 1 (by rfl) ⟨1499912, by rfl⟩ : syracuseStep 1999883 = 2999825) B2999825
theorem B1999895 : Blo 1332985 1999895 := bstep (se 1 (by rfl) ⟨1499921, by rfl⟩ : syracuseStep 1999895 = 2999843) B2999843
theorem B3376151 : Blo 1332985 3376151 := bstep (se 1 (by rfl) ⟨2532113, by rfl⟩ : syracuseStep 3376151 = 5064227) B5064227
theorem B2999321 : Blo 1332985 2999321 := bstep (se 2 (by rfl) ⟨1124745, by rfl⟩ : syracuseStep 2999321 = 2249491) B2249491
theorem B5063755 : Blo 1332985 5063755 := bstep (se 1 (by rfl) ⟨3797816, by rfl⟩ : syracuseStep 5063755 = 7595633) B7595633
theorem B1999961 : Blo 1332985 1999961 := bstep (se 2 (by rfl) ⟨749985, by rfl⟩ : syracuseStep 1999961 = 1499971) B1499971
theorem B2999411 : Blo 1332985 2999411 := bstep (se 1 (by rfl) ⟨2249558, by rfl⟩ : syracuseStep 2999411 = 4499117) B4499117
theorem B2999447 : Blo 1332985 2999447 := bstep (se 1 (by rfl) ⟨2249585, by rfl⟩ : syracuseStep 2999447 = 4499171) B4499171
theorem B1500331 : Blo 1332985 1500331 := bstep (se 1 (by rfl) ⟨1125248, by rfl⟩ : syracuseStep 1500331 = 2250497) B2250497
theorem B4809901 : Blo 1332985 4809901 := bstep (se 3 (by rfl) ⟨901856, by rfl⟩ : syracuseStep 4809901 = 1803713) B1803713
theorem B7308467 : Blo 1332985 7308467 := bstep (se 1 (by rfl) ⟨5481350, by rfl⟩ : syracuseStep 7308467 = 10962701) B10962701
theorem B2000075 : Blo 1332985 2000075 := bstep (se 1 (by rfl) ⟨1500056, by rfl⟩ : syracuseStep 2000075 = 3000113) B3000113
theorem B1688779 : Blo 1332985 1688779 := bstep (se 1 (by rfl) ⟨1266584, by rfl⟩ : syracuseStep 1688779 = 2533169) B2533169
theorem B2000087 : Blo 1332985 2000087 := bstep (se 1 (by rfl) ⟨1500065, by rfl⟩ : syracuseStep 2000087 = 3000131) B3000131
theorem B1500439 : Blo 1332985 1500439 := bstep (se 1 (by rfl) ⟨1125329, by rfl⟩ : syracuseStep 1500439 = 2250659) B2250659
theorem B2000153 : Blo 1332985 2000153 := bstep (se 2 (by rfl) ⟨750057, by rfl⟩ : syracuseStep 2000153 = 1500115) B1500115
theorem B8545601 : Blo 1332985 8545601 := bstep (se 2 (by rfl) ⟨3204600, by rfl⟩ : syracuseStep 8545601 = 6409201) B6409201
theorem B2999627 : Blo 1332985 2999627 := bstep (se 1 (by rfl) ⟨2249720, by rfl⟩ : syracuseStep 2999627 = 4499441) B4499441
theorem B2532683 : Blo 1332985 2532683 := bstep (se 1 (by rfl) ⟨1899512, by rfl⟩ : syracuseStep 2532683 = 3799025) B3799025
theorem B5064029 : Blo 1332985 5064029 := bstep (se 3 (by rfl) ⟨949505, by rfl⟩ : syracuseStep 5064029 = 1899011) B1899011
theorem B2999681 : Blo 1332985 2999681 := bstep (se 2 (by rfl) ⟨1124880, by rfl⟩ : syracuseStep 2999681 = 2249761) B2249761
theorem B2000267 : Blo 1332985 2000267 := bstep (se 1 (by rfl) ⟨1500200, by rfl⟩ : syracuseStep 2000267 = 3000401) B3000401
theorem B2000279 : Blo 1332985 2000279 := bstep (se 1 (by rfl) ⟨1500209, by rfl⟩ : syracuseStep 2000279 = 3000419) B3000419
theorem B2196887 : Blo 1332985 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B1500619 : Blo 1332985 1500619 := bstep (se 1 (by rfl) ⟨1125464, by rfl⟩ : syracuseStep 1500619 = 2250929) B2250929
theorem B2000345 : Blo 1332985 2000345 := bstep (se 2 (by rfl) ⟨750129, by rfl⟩ : syracuseStep 2000345 = 1500259) B1500259
theorem B2532865 : Blo 1332985 2532865 := bstep (se 2 (by rfl) ⟨949824, by rfl⟩ : syracuseStep 2532865 = 1899649) B1899649
theorem B1500727 : Blo 1332985 1500727 := bstep (se 1 (by rfl) ⟨1125545, by rfl⟩ : syracuseStep 1500727 = 2251091) B2251091
theorem B4499009 : Blo 1332985 4499009 := bstep (se 2 (by rfl) ⟨1687128, by rfl⟩ : syracuseStep 4499009 = 3374257) B3374257
theorem B2000459 : Blo 1332985 2000459 := bstep (se 1 (by rfl) ⟨1500344, by rfl⟩ : syracuseStep 2000459 = 3000689) B3000689
theorem B2000471 : Blo 1332985 2000471 := bstep (se 1 (by rfl) ⟨1500353, by rfl⟩ : syracuseStep 2000471 = 3000707) B3000707
theorem B2999897 : Blo 1332985 2999897 := bstep (se 2 (by rfl) ⟨1124961, by rfl⟩ : syracuseStep 2999897 = 2249923) B2249923
theorem B5695069 : Blo 1332985 5695069 := bstep (se 3 (by rfl) ⟨1067825, by rfl⟩ : syracuseStep 5695069 = 2135651) B2135651
theorem B2000537 : Blo 1332985 2000537 := bstep (se 2 (by rfl) ⟨750201, by rfl⟩ : syracuseStep 2000537 = 1500403) B1500403
theorem B2999987 : Blo 1332985 2999987 := bstep (se 1 (by rfl) ⟨2249990, by rfl⟩ : syracuseStep 2999987 = 4499981) B4499981
theorem B3000023 : Blo 1332985 3000023 := bstep (se 1 (by rfl) ⟨2250017, by rfl⟩ : syracuseStep 3000023 = 4500035) B4500035
theorem B1500907 : Blo 1332985 1500907 := bstep (se 1 (by rfl) ⟨1125680, by rfl⟩ : syracuseStep 1500907 = 2251361) B2251361
theorem B29640433 : Blo 1332985 29640433 := bstep (se 2 (by rfl) ⟨11115162, by rfl⟩ : syracuseStep 29640433 = 22230325) B22230325
theorem B2000651 : Blo 1332985 2000651 := bstep (se 1 (by rfl) ⟨1500488, by rfl⟩ : syracuseStep 2000651 = 3000977) B3000977
theorem B2000663 : Blo 1332985 2000663 := bstep (se 1 (by rfl) ⟨1500497, by rfl⟩ : syracuseStep 2000663 = 3000995) B3000995
theorem B3376961 : Blo 1332985 3376961 := bstep (se 2 (by rfl) ⟨1266360, by rfl⟩ : syracuseStep 3376961 = 2532721) B2532721
theorem B1501015 : Blo 1332985 1501015 := bstep (se 1 (by rfl) ⟨1125761, by rfl⟩ : syracuseStep 1501015 = 2251523) B2251523
theorem B2533207 : Blo 1332985 2533207 := bstep (se 1 (by rfl) ⟨1899905, by rfl⟩ : syracuseStep 2533207 = 3799811) B3799811
theorem B2000729 : Blo 1332985 2000729 := bstep (se 2 (by rfl) ⟨750273, by rfl⟩ : syracuseStep 2000729 = 1500547) B1500547
theorem B3000203 : Blo 1332985 3000203 := bstep (se 1 (by rfl) ⟨2250152, by rfl⟩ : syracuseStep 3000203 = 4500305) B4500305
theorem B3000257 : Blo 1332985 3000257 := bstep (se 2 (by rfl) ⟨1125096, by rfl⟩ : syracuseStep 3000257 = 2250193) B2250193
theorem B2000843 : Blo 1332985 2000843 := bstep (se 1 (by rfl) ⟨1500632, by rfl⟩ : syracuseStep 2000843 = 3001265) B3001265
theorem B2000855 : Blo 1332985 2000855 := bstep (se 1 (by rfl) ⟨1500641, by rfl⟩ : syracuseStep 2000855 = 3001283) B3001283
theorem B1501195 : Blo 1332985 1501195 := bstep (se 1 (by rfl) ⟨1125896, by rfl⟩ : syracuseStep 1501195 = 2251793) B2251793
theorem B5064727 : Blo 1332985 5064727 := bstep (se 1 (by rfl) ⟨3798545, by rfl⟩ : syracuseStep 5064727 = 7597091) B7597091
theorem B2000921 : Blo 1332985 2000921 := bstep (se 2 (by rfl) ⟨750345, by rfl⟩ : syracuseStep 2000921 = 1500691) B1500691
theorem B2533427 : Blo 1332985 2533427 := bstep (se 1 (by rfl) ⟨1900070, by rfl⟩ : syracuseStep 2533427 = 3800141) B3800141
theorem B6752321 : Blo 1332985 6752321 := bstep (se 2 (by rfl) ⟨2532120, by rfl⟩ : syracuseStep 6752321 = 5064241) B5064241
theorem B4499549 : Blo 1332985 4499549 := bstep (se 3 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 4499549 = 1687331) B1687331
theorem B1501303 : Blo 1332985 1501303 := bstep (se 1 (by rfl) ⟨1125977, by rfl⟩ : syracuseStep 1501303 = 2251955) B2251955
theorem B2001035 : Blo 1332985 2001035 := bstep (se 1 (by rfl) ⟨1500776, by rfl⟩ : syracuseStep 2001035 = 3001553) B3001553
theorem B2001047 : Blo 1332985 2001047 := bstep (se 1 (by rfl) ⟨1500785, by rfl⟩ : syracuseStep 2001047 = 3001571) B3001571
theorem B3000473 : Blo 1332985 3000473 := bstep (se 2 (by rfl) ⟨1125177, by rfl⟩ : syracuseStep 3000473 = 2250355) B2250355
theorem B5695667 : Blo 1332985 5695667 := bstep (se 1 (by rfl) ⟨4271750, by rfl⟩ : syracuseStep 5695667 = 8543501) B8543501
theorem B2001113 : Blo 1332985 2001113 := bstep (se 2 (by rfl) ⟨750417, by rfl⟩ : syracuseStep 2001113 = 1500835) B1500835
theorem B3000563 : Blo 1332985 3000563 := bstep (se 1 (by rfl) ⟨2250422, by rfl⟩ : syracuseStep 3000563 = 4500845) B4500845
theorem B3000599 : Blo 1332985 3000599 := bstep (se 1 (by rfl) ⟨2250449, by rfl⟩ : syracuseStep 3000599 = 4500899) B4500899
theorem B2533655 : Blo 1332985 2533655 := bstep (se 1 (by rfl) ⟨1900241, by rfl⟩ : syracuseStep 2533655 = 3800483) B3800483
theorem B1501483 : Blo 1332985 1501483 := bstep (se 1 (by rfl) ⟨1126112, by rfl⟩ : syracuseStep 1501483 = 2252225) B2252225
theorem B2001227 : Blo 1332985 2001227 := bstep (se 1 (by rfl) ⟨1500920, by rfl⟩ : syracuseStep 2001227 = 3001841) B3001841
theorem B2001239 : Blo 1332985 2001239 := bstep (se 1 (by rfl) ⟨1500929, by rfl⟩ : syracuseStep 2001239 = 3001859) B3001859
theorem B3377497 : Blo 1332985 3377497 := bstep (se 2 (by rfl) ⟨1266561, by rfl⟩ : syracuseStep 3377497 = 2533123) B2533123
theorem B1501591 : Blo 1332985 1501591 := bstep (se 1 (by rfl) ⟨1126193, by rfl⟩ : syracuseStep 1501591 = 2252387) B2252387
theorem B2001305 : Blo 1332985 2001305 := bstep (se 2 (by rfl) ⟨750489, by rfl⟩ : syracuseStep 2001305 = 1500979) B1500979
theorem B3000779 : Blo 1332985 3000779 := bstep (se 1 (by rfl) ⟨2250584, by rfl⟩ : syracuseStep 3000779 = 4501169) B4501169
theorem B3000833 : Blo 1332985 3000833 := bstep (se 2 (by rfl) ⟨1125312, by rfl⟩ : syracuseStep 3000833 = 2250625) B2250625
theorem B2001419 : Blo 1332985 2001419 := bstep (se 1 (by rfl) ⟨1501064, by rfl⟩ : syracuseStep 2001419 = 3002129) B3002129
theorem B2001431 : Blo 1332985 2001431 := bstep (se 1 (by rfl) ⟨1501073, by rfl⟩ : syracuseStep 2001431 = 3002147) B3002147
theorem B2533913 : Blo 1332985 2533913 := bstep (se 2 (by rfl) ⟨950217, by rfl⟩ : syracuseStep 2533913 = 1900435) B1900435
theorem B1501771 : Blo 1332985 1501771 := bstep (se 1 (by rfl) ⟨1126328, by rfl⟩ : syracuseStep 1501771 = 2252657) B2252657
theorem B2001497 : Blo 1332985 2001497 := bstep (se 2 (by rfl) ⟨750561, by rfl⟩ : syracuseStep 2001497 = 1501123) B1501123
theorem B2001611 : Blo 1332985 2001611 := bstep (se 1 (by rfl) ⟨1501208, by rfl⟩ : syracuseStep 2001611 = 3002417) B3002417
theorem B2001623 : Blo 1332985 2001623 := bstep (se 1 (by rfl) ⟨1501217, by rfl⟩ : syracuseStep 2001623 = 3002435) B3002435
theorem B3001049 : Blo 1332985 3001049 := bstep (se 2 (by rfl) ⟨1125393, by rfl⟩ : syracuseStep 3001049 = 2250787) B2250787
theorem B2001689 : Blo 1332985 2001689 := bstep (se 2 (by rfl) ⟨750633, by rfl⟩ : syracuseStep 2001689 = 1501267) B1501267
theorem B7211821 : Blo 1332985 7211821 := bstep (se 3 (by rfl) ⟨1352216, by rfl⟩ : syracuseStep 7211821 = 2704433) B2704433
theorem B5065517 : Blo 1332985 5065517 := bstep (se 3 (by rfl) ⟨949784, by rfl⟩ : syracuseStep 5065517 = 1899569) B1899569
theorem B3001139 : Blo 1332985 3001139 := bstep (se 1 (by rfl) ⟨2250854, by rfl⟩ : syracuseStep 3001139 = 4501709) B4501709
theorem B3001175 : Blo 1332985 3001175 := bstep (se 1 (by rfl) ⟨2250881, by rfl⟩ : syracuseStep 3001175 = 4501763) B4501763
theorem B15190901 : Blo 1332985 15190901 := bstep (se 5 (by rfl) ⟨712073, by rfl⟩ : syracuseStep 15190901 = 1424147) B1424147
theorem B2001803 : Blo 1332985 2001803 := bstep (se 1 (by rfl) ⟨1501352, by rfl⟩ : syracuseStep 2001803 = 3002705) B3002705
theorem B2001815 : Blo 1332985 2001815 := bstep (se 1 (by rfl) ⟨1501361, by rfl⟩ : syracuseStep 2001815 = 3002723) B3002723
theorem B29617073 : Blo 1332985 29617073 := bstep (se 2 (by rfl) ⟨11106402, by rfl⟩ : syracuseStep 29617073 = 22212805) B22212805
theorem B2534323 : Blo 1332985 2534323 := bstep (se 1 (by rfl) ⟨1900742, by rfl⟩ : syracuseStep 2534323 = 3801485) B3801485
theorem B2001881 : Blo 1332985 2001881 := bstep (se 2 (by rfl) ⟨750705, by rfl⟩ : syracuseStep 2001881 = 1501411) B1501411
theorem B3001355 : Blo 1332985 3001355 := bstep (se 1 (by rfl) ⟨2251016, by rfl⟩ : syracuseStep 3001355 = 4502033) B4502033
theorem B3001409 : Blo 1332985 3001409 := bstep (se 2 (by rfl) ⟨1125528, by rfl⟩ : syracuseStep 3001409 = 2251057) B2251057
theorem B3042379 : Blo 1332985 3042379 := bstep (se 1 (by rfl) ⟨2281784, by rfl⟩ : syracuseStep 3042379 = 4563569) B4563569
theorem B2001995 : Blo 1332985 2001995 := bstep (se 1 (by rfl) ⟨1501496, by rfl⟩ : syracuseStep 2001995 = 3002993) B3002993
theorem B2002007 : Blo 1332985 2002007 := bstep (se 1 (by rfl) ⟨1501505, by rfl⟩ : syracuseStep 2002007 = 3003011) B3003011
theorem B8113283 : Blo 1332985 8113283 := bstep (se 1 (by rfl) ⟨6084962, by rfl⟩ : syracuseStep 8113283 = 12169925) B12169925
theorem B2002073 : Blo 1332985 2002073 := bstep (se 2 (by rfl) ⟨750777, by rfl⟩ : syracuseStep 2002073 = 1501555) B1501555
theorem B4500683 : Blo 1332985 4500683 := bstep (se 1 (by rfl) ⟨3375512, by rfl⟩ : syracuseStep 4500683 = 6751025) B6751025
theorem B7597273 : Blo 1332985 7597273 := bstep (se 2 (by rfl) ⟨2848977, by rfl⟩ : syracuseStep 7597273 = 5697955) B5697955
theorem B2002187 : Blo 1332985 2002187 := bstep (se 1 (by rfl) ⟨1501640, by rfl⟩ : syracuseStep 2002187 = 3003281) B3003281
theorem B2002199 : Blo 1332985 2002199 := bstep (se 1 (by rfl) ⟨1501649, by rfl⟩ : syracuseStep 2002199 = 3003299) B3003299
theorem B3001625 : Blo 1332985 3001625 := bstep (se 2 (by rfl) ⟨1125609, by rfl⟩ : syracuseStep 3001625 = 2251219) B2251219
theorem B2002265 : Blo 1332985 2002265 := bstep (se 2 (by rfl) ⟨750849, by rfl⟩ : syracuseStep 2002265 = 1501699) B1501699
theorem B3001715 : Blo 1332985 3001715 := bstep (se 1 (by rfl) ⟨2251286, by rfl⟩ : syracuseStep 3001715 = 4502573) B4502573
theorem B3001751 : Blo 1332985 3001751 := bstep (se 1 (by rfl) ⟨2251313, by rfl⟩ : syracuseStep 3001751 = 4502627) B4502627
theorem B1371563 : Blo 1332985 1371563 := bstep (se 1 (by rfl) ⟨1028672, by rfl⟩ : syracuseStep 1371563 = 2057345) B2057345
theorem B3378611 : Blo 1332985 3378611 := bstep (se 1 (by rfl) ⟨2533958, by rfl⟩ : syracuseStep 3378611 = 5067917) B5067917
theorem B2002379 : Blo 1332985 2002379 := bstep (se 1 (by rfl) ⟨1501784, by rfl⟩ : syracuseStep 2002379 = 3003569) B3003569
theorem B2002391 : Blo 1332985 2002391 := bstep (se 1 (by rfl) ⟨1501793, by rfl⟩ : syracuseStep 2002391 = 3003587) B3003587
theorem B4500953 : Blo 1332985 4500953 := bstep (se 2 (by rfl) ⟨1687857, by rfl⟩ : syracuseStep 4500953 = 3375715) B3375715
theorem B50040337 : Blo 1332985 50040337 := bstep (se 2 (by rfl) ⟨18765126, by rfl⟩ : syracuseStep 50040337 = 37530253) B37530253
theorem B5410327 : Blo 1332985 5410327 := bstep (se 1 (by rfl) ⟨4057745, by rfl⟩ : syracuseStep 5410327 = 8115491) B8115491
theorem B2002457 : Blo 1332985 2002457 := bstep (se 2 (by rfl) ⟨750921, by rfl⟩ : syracuseStep 2002457 = 1501843) B1501843
theorem B3001931 : Blo 1332985 3001931 := bstep (se 1 (by rfl) ⟨2251448, by rfl⟩ : syracuseStep 3001931 = 4502897) B4502897
theorem B3001985 : Blo 1332985 3001985 := bstep (se 2 (by rfl) ⟨1125744, by rfl⟩ : syracuseStep 3001985 = 2251489) B2251489
theorem B6844121 : Blo 1332985 6844121 := bstep (se 2 (by rfl) ⟨2566545, by rfl⟩ : syracuseStep 6844121 = 5133091) B5133091
theorem B3378905 : Blo 1332985 3378905 := bstep (se 2 (by rfl) ⟨1267089, by rfl⟩ : syracuseStep 3378905 = 2534179) B2534179
theorem B6410029 : Blo 1332985 6410029 := bstep (se 3 (by rfl) ⟨1201880, by rfl⟩ : syracuseStep 6410029 = 2403761) B2403761
theorem B4329281 : Blo 1332985 4329281 := bstep (se 2 (by rfl) ⟨1623480, by rfl⟩ : syracuseStep 4329281 = 3246961) B3246961
theorem B2404171 : Blo 1332985 2404171 := bstep (se 1 (by rfl) ⟨1803128, by rfl⟩ : syracuseStep 2404171 = 3606257) B3606257
theorem B2256727 : Blo 1332985 2256727 := bstep (se 1 (by rfl) ⟨1692545, by rfl⟩ : syracuseStep 2256727 = 3385091) B3385091
theorem B3002201 : Blo 1332985 3002201 := bstep (se 2 (by rfl) ⟨1125825, by rfl⟩ : syracuseStep 3002201 = 2251651) B2251651
theorem B3002291 : Blo 1332985 3002291 := bstep (se 1 (by rfl) ⟨2251718, by rfl⟩ : syracuseStep 3002291 = 4503437) B4503437
theorem B3002327 : Blo 1332985 3002327 := bstep (se 1 (by rfl) ⟨2251745, by rfl⟩ : syracuseStep 3002327 = 4503491) B4503491
theorem B6754265 : Blo 1332985 6754265 := bstep (se 2 (by rfl) ⟨2532849, by rfl⟩ : syracuseStep 6754265 = 5065699) B5065699
theorem B7213121 : Blo 1332985 7213121 := bstep (se 2 (by rfl) ⟨2704920, by rfl⟩ : syracuseStep 7213121 = 5409841) B5409841
theorem B3043457 : Blo 1332985 3043457 := bstep (se 2 (by rfl) ⟨1141296, by rfl⟩ : syracuseStep 3043457 = 2282593) B2282593
theorem B3002507 : Blo 1332985 3002507 := bstep (se 1 (by rfl) ⟨2251880, by rfl⟩ : syracuseStep 3002507 = 4503761) B4503761
theorem B2314379 : Blo 1332985 2314379 := bstep (se 1 (by rfl) ⟨1735784, by rfl⟩ : syracuseStep 2314379 = 3471569) B3471569
theorem B4501655 : Blo 1332985 4501655 := bstep (se 1 (by rfl) ⟨3376241, by rfl⟩ : syracuseStep 4501655 = 6752483) B6752483
theorem B7598231 : Blo 1332985 7598231 := bstep (se 1 (by rfl) ⟨5698673, by rfl⟩ : syracuseStep 7598231 = 11397347) B11397347
theorem B3002561 : Blo 1332985 3002561 := bstep (se 2 (by rfl) ⟨1125960, by rfl⟩ : syracuseStep 3002561 = 2251921) B2251921
theorem B5066945 : Blo 1332985 5066945 := bstep (se 2 (by rfl) ⟨1900104, by rfl⟩ : syracuseStep 5066945 = 3800209) B3800209
theorem B3207475 : Blo 1332985 3207475 := bstep (se 1 (by rfl) ⟨2405606, by rfl⟩ : syracuseStep 3207475 = 4811213) B4811213
theorem B2568577 : Blo 1332985 2568577 := bstep (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) B1926433
theorem B3002777 : Blo 1332985 3002777 := bstep (se 2 (by rfl) ⟨1126041, by rfl⟩ : syracuseStep 3002777 = 2252083) B2252083
theorem B3002867 : Blo 1332985 3002867 := bstep (se 1 (by rfl) ⟨2252150, by rfl⟩ : syracuseStep 3002867 = 4504301) B4504301
theorem B4330007 : Blo 1332985 4330007 := bstep (se 1 (by rfl) ⟨3247505, by rfl⟩ : syracuseStep 4330007 = 6495011) B6495011
theorem B3002903 : Blo 1332985 3002903 := bstep (se 1 (by rfl) ⟨2252177, by rfl⟩ : syracuseStep 3002903 = 4504355) B4504355
theorem B21926435 : Blo 1332985 21926435 := bstep (se 1 (by rfl) ⟨16444826, by rfl⟩ : syracuseStep 21926435 = 32889653) B32889653
theorem B2028107 : Blo 1332985 2028107 := bstep (se 1 (by rfl) ⟨1521080, by rfl⟩ : syracuseStep 2028107 = 3042161) B3042161
theorem B2404979 : Blo 1332985 2404979 := bstep (se 1 (by rfl) ⟨1803734, by rfl⟩ : syracuseStep 2404979 = 3607469) B3607469
theorem B4502195 : Blo 1332985 4502195 := bstep (se 1 (by rfl) ⟨3376646, by rfl⟩ : syracuseStep 4502195 = 6753293) B6753293
theorem B3003083 : Blo 1332985 3003083 := bstep (se 1 (by rfl) ⟨2252312, by rfl⟩ : syracuseStep 3003083 = 4504625) B4504625
theorem B49353421 : Blo 1332985 49353421 := bstep (se 3 (by rfl) ⟨9253766, by rfl⟩ : syracuseStep 49353421 = 18507533) B18507533
theorem B3003137 : Blo 1332985 3003137 := bstep (se 2 (by rfl) ⟨1126176, by rfl⟩ : syracuseStep 3003137 = 2252353) B2252353
theorem B2282251 : Blo 1332985 2282251 := bstep (se 1 (by rfl) ⟨1711688, by rfl⟩ : syracuseStep 2282251 = 3423377) B3423377
theorem B7705361 : Blo 1332985 7705361 := bstep (se 2 (by rfl) ⟨2889510, by rfl⟩ : syracuseStep 7705361 = 5779021) B5779021
theorem B8549165 : Blo 1332985 8549165 := bstep (se 3 (by rfl) ⟨1602968, by rfl⟩ : syracuseStep 8549165 = 3205937) B3205937
theorem B11400011 : Blo 1332985 11400011 := bstep (se 1 (by rfl) ⟨8550008, by rfl⟩ : syracuseStep 11400011 = 17100017) B17100017
theorem B2847577 : Blo 1332985 2847577 := bstep (se 2 (by rfl) ⟨1067841, by rfl⟩ : syracuseStep 2847577 = 2135683) B2135683
theorem B10261379 : Blo 1332985 10261379 := bstep (se 1 (by rfl) ⟨7696034, by rfl⟩ : syracuseStep 10261379 = 15392069) B15392069
theorem B9622451 : Blo 1332985 9622451 := bstep (se 1 (by rfl) ⟨7216838, by rfl⟩ : syracuseStep 9622451 = 14433677) B14433677
theorem B4502465 : Blo 1332985 4502465 := bstep (se 2 (by rfl) ⟨1688424, by rfl⟩ : syracuseStep 4502465 = 3376849) B3376849
theorem B2249687 : Blo 1332985 2249687 := bstep (se 1 (by rfl) ⟨1687265, by rfl⟩ : syracuseStep 2249687 = 3374531) B3374531
theorem B3003353 : Blo 1332985 3003353 := bstep (se 2 (by rfl) ⟨1126257, by rfl⟩ : syracuseStep 3003353 = 2252515) B2252515
theorem B4387805 : Blo 1332985 4387805 := bstep (se 3 (by rfl) ⟨822713, by rfl⟩ : syracuseStep 4387805 = 1645427) B1645427
theorem B12170245 : Blo 1332985 12170245 := bstep (se 4 (by rfl) ⟨1140960, by rfl⟩ : syracuseStep 12170245 = 2281921) B2281921
theorem B3003443 : Blo 1332985 3003443 := bstep (se 1 (by rfl) ⟨2252582, by rfl⟩ : syracuseStep 3003443 = 4505165) B4505165
theorem B6845515 : Blo 1332985 6845515 := bstep (se 1 (by rfl) ⟨5134136, by rfl⟩ : syracuseStep 6845515 = 10268273) B10268273
theorem B2249815 : Blo 1332985 2249815 := bstep (se 1 (by rfl) ⟨1687361, by rfl⟩ : syracuseStep 2249815 = 3374723) B3374723
theorem B3003479 : Blo 1332985 3003479 := bstep (se 1 (by rfl) ⟨2252609, by rfl⟩ : syracuseStep 3003479 = 4505219) B4505219
theorem B12162149 : Blo 1332985 12162149 := bstep (se 4 (by rfl) ⟨1140201, by rfl⟩ : syracuseStep 12162149 = 2280403) B2280403
theorem B3044531 : Blo 1332985 3044531 := bstep (se 1 (by rfl) ⟨2283398, by rfl⟩ : syracuseStep 3044531 = 4566797) B4566797
theorem B3003659 : Blo 1332985 3003659 := bstep (se 1 (by rfl) ⟨2252744, by rfl⟩ : syracuseStep 3003659 = 4505489) B4505489
theorem B3003713 : Blo 1332985 3003713 := bstep (se 2 (by rfl) ⟨1126392, by rfl⟩ : syracuseStep 3003713 = 2252785) B2252785
theorem B8115635 : Blo 1332985 8115635 := bstep (se 1 (by rfl) ⟨6086726, by rfl⟩ : syracuseStep 8115635 = 12173453) B12173453
theorem B4503005 : Blo 1332985 4503005 := bstep (se 3 (by rfl) ⟨844313, by rfl⟩ : syracuseStep 4503005 = 1688627) B1688627
theorem B6755885 : Blo 1332985 6755885 := bstep (se 3 (by rfl) ⟨1266728, by rfl⟩ : syracuseStep 6755885 = 2533457) B2533457
theorem B5068433 : Blo 1332985 5068433 := bstep (se 2 (by rfl) ⟨1900662, by rfl⟩ : syracuseStep 5068433 = 3801325) B3801325
theorem B2250443 : Blo 1332985 2250443 := bstep (se 1 (by rfl) ⟨1687832, by rfl⟩ : syracuseStep 2250443 = 3375665) B3375665
theorem B9885401 : Blo 1332985 9885401 := bstep (se 2 (by rfl) ⟨3707025, by rfl⟩ : syracuseStep 9885401 = 7414051) B7414051
theorem B1333003 : Blo 1332985 1333003 := bstep (se 1 (by rfl) ⟨999752, by rfl⟩ : syracuseStep 1333003 = 1999505) B1999505
theorem B1333015 : Blo 1332985 1333015 := bstep (se 1 (by rfl) ⟨999761, by rfl⟩ : syracuseStep 1333015 = 1999523) B1999523
theorem B1333035 : Blo 1332985 1333035 := bstep (se 1 (by rfl) ⟨999776, by rfl⟩ : syracuseStep 1333035 = 1999553) B1999553
theorem B1333047 : Blo 1332985 1333047 := bstep (se 1 (by rfl) ⟨999785, by rfl⟩ : syracuseStep 1333047 = 1999571) B1999571
theorem B1333067 : Blo 1332985 1333067 := bstep (se 1 (by rfl) ⟨999800, by rfl⟩ : syracuseStep 1333067 = 1999601) B1999601
theorem B2250571 : Blo 1332985 2250571 := bstep (se 1 (by rfl) ⟨1687928, by rfl⟩ : syracuseStep 2250571 = 3375857) B3375857
theorem B1333079 : Blo 1332985 1333079 := bstep (se 1 (by rfl) ⟨999809, by rfl⟩ : syracuseStep 1333079 = 1999619) B1999619
theorem B1333099 : Blo 1332985 1333099 := bstep (se 1 (by rfl) ⟨999824, by rfl⟩ : syracuseStep 1333099 = 1999649) B1999649
theorem B1333111 : Blo 1332985 1333111 := bstep (se 1 (by rfl) ⟨999833, by rfl⟩ : syracuseStep 1333111 = 1999667) B1999667
theorem B5699459 : Blo 1332985 5699459 := bstep (se 1 (by rfl) ⟨4274594, by rfl⟩ : syracuseStep 5699459 = 8549189) B8549189
theorem B1333131 : Blo 1332985 1333131 := bstep (se 1 (by rfl) ⟨999848, by rfl⟩ : syracuseStep 1333131 = 1999697) B1999697
theorem B1333143 : Blo 1332985 1333143 := bstep (se 1 (by rfl) ⟨999857, by rfl⟩ : syracuseStep 1333143 = 1999715) B1999715
theorem B1333163 : Blo 1332985 1333163 := bstep (se 1 (by rfl) ⟨999872, by rfl⟩ : syracuseStep 1333163 = 1999745) B1999745
theorem B1333175 : Blo 1332985 1333175 := bstep (se 1 (by rfl) ⟨999881, by rfl⟩ : syracuseStep 1333175 = 1999763) B1999763
theorem B1333195 : Blo 1332985 1333195 := bstep (se 1 (by rfl) ⟨999896, by rfl⟩ : syracuseStep 1333195 = 1999793) B1999793
theorem B11392973 : Blo 1332985 11392973 := bstep (se 3 (by rfl) ⟨2136182, by rfl⟩ : syracuseStep 11392973 = 4272365) B4272365
theorem B1333207 : Blo 1332985 1333207 := bstep (se 1 (by rfl) ⟨999905, by rfl⟩ : syracuseStep 1333207 = 1999811) B1999811
theorem B2250713 : Blo 1332985 2250713 := bstep (se 2 (by rfl) ⟨844017, by rfl⟩ : syracuseStep 2250713 = 1688035) B1688035
theorem B3799001 : Blo 1332985 3799001 := bstep (se 2 (by rfl) ⟨1424625, by rfl⟩ : syracuseStep 3799001 = 2849251) B2849251
theorem B1333227 : Blo 1332985 1333227 := bstep (se 1 (by rfl) ⟨999920, by rfl⟩ : syracuseStep 1333227 = 1999841) B1999841
theorem B1333239 : Blo 1332985 1333239 := bstep (se 1 (by rfl) ⟨999929, by rfl⟩ : syracuseStep 1333239 = 1999859) B1999859
theorem B1333259 : Blo 1332985 1333259 := bstep (se 1 (by rfl) ⟨999944, by rfl⟩ : syracuseStep 1333259 = 1999889) B1999889
theorem B1333271 : Blo 1332985 1333271 := bstep (se 1 (by rfl) ⟨999953, by rfl⟩ : syracuseStep 1333271 = 1999907) B1999907
theorem B1333291 : Blo 1332985 1333291 := bstep (se 1 (by rfl) ⟨999968, by rfl⟩ : syracuseStep 1333291 = 1999937) B1999937
theorem B1333303 : Blo 1332985 1333303 := bstep (se 1 (by rfl) ⟨999977, by rfl⟩ : syracuseStep 1333303 = 1999955) B1999955
theorem B1333323 : Blo 1332985 1333323 := bstep (se 1 (by rfl) ⟨999992, by rfl⟩ : syracuseStep 1333323 = 1999985) B1999985
theorem B1333335 : Blo 1332985 1333335 := bstep (se 1 (by rfl) ⟨1000001, by rfl⟩ : syracuseStep 1333335 = 2000003) B2000003
theorem B2250841 : Blo 1332985 2250841 := bstep (se 2 (by rfl) ⟨844065, by rfl⟩ : syracuseStep 2250841 = 1688131) B1688131
theorem B1333355 : Blo 1332985 1333355 := bstep (se 1 (by rfl) ⟨1000016, by rfl⟩ : syracuseStep 1333355 = 2000033) B2000033
theorem B1333367 : Blo 1332985 1333367 := bstep (se 1 (by rfl) ⟨1000025, by rfl⟩ : syracuseStep 1333367 = 2000051) B2000051
theorem B1333387 : Blo 1332985 1333387 := bstep (se 1 (by rfl) ⟨1000040, by rfl⟩ : syracuseStep 1333387 = 2000081) B2000081
theorem B1898635 : Blo 1332985 1898635 := bstep (se 1 (by rfl) ⟨1423976, by rfl⟩ : syracuseStep 1898635 = 2847953) B2847953
theorem B1333399 : Blo 1332985 1333399 := bstep (se 1 (by rfl) ⟨1000049, by rfl⟩ : syracuseStep 1333399 = 2000099) B2000099
theorem B1333419 : Blo 1332985 1333419 := bstep (se 1 (by rfl) ⟨1000064, by rfl⟩ : syracuseStep 1333419 = 2000129) B2000129
theorem B1333431 : Blo 1332985 1333431 := bstep (se 1 (by rfl) ⟨1000073, by rfl⟩ : syracuseStep 1333431 = 2000147) B2000147
theorem B1333451 : Blo 1332985 1333451 := bstep (se 1 (by rfl) ⟨1000088, by rfl⟩ : syracuseStep 1333451 = 2000177) B2000177
theorem B1333463 : Blo 1332985 1333463 := bstep (se 1 (by rfl) ⟨1000097, by rfl⟩ : syracuseStep 1333463 = 2000195) B2000195
theorem B5699801 : Blo 1332985 5699801 := bstep (se 2 (by rfl) ⟨2137425, by rfl⟩ : syracuseStep 5699801 = 4274851) B4274851
theorem B1333483 : Blo 1332985 1333483 := bstep (se 1 (by rfl) ⟨1000112, by rfl⟩ : syracuseStep 1333483 = 2000225) B2000225
theorem B1333495 : Blo 1332985 1333495 := bstep (se 1 (by rfl) ⟨1000121, by rfl⟩ : syracuseStep 1333495 = 2000243) B2000243
theorem B15202565 : Blo 1332985 15202565 := bstep (se 4 (by rfl) ⟨1425240, by rfl⟩ : syracuseStep 15202565 = 2850481) B2850481
theorem B1333515 : Blo 1332985 1333515 := bstep (se 1 (by rfl) ⟨1000136, by rfl⟩ : syracuseStep 1333515 = 2000273) B2000273
theorem B6748433 : Blo 1332985 6748433 := bstep (se 2 (by rfl) ⟨2530662, by rfl⟩ : syracuseStep 6748433 = 5061325) B5061325
theorem B1333527 : Blo 1332985 1333527 := bstep (se 1 (by rfl) ⟨1000145, by rfl⟩ : syracuseStep 1333527 = 2000291) B2000291
theorem B1333547 : Blo 1332985 1333547 := bstep (se 1 (by rfl) ⟨1000160, by rfl⟩ : syracuseStep 1333547 = 2000321) B2000321
theorem B1333559 : Blo 1332985 1333559 := bstep (se 1 (by rfl) ⟨1000169, by rfl⟩ : syracuseStep 1333559 = 2000339) B2000339
theorem B4561217 : Blo 1332985 4561217 := bstep (se 2 (by rfl) ⟨1710456, by rfl⟩ : syracuseStep 4561217 = 3420913) B3420913
theorem B1333579 : Blo 1332985 1333579 := bstep (se 1 (by rfl) ⟨1000184, by rfl⟩ : syracuseStep 1333579 = 2000369) B2000369
theorem B1423703 : Blo 1332985 1423703 := bstep (se 1 (by rfl) ⟨1067777, by rfl⟩ : syracuseStep 1423703 = 2135555) B2135555
theorem B1333591 : Blo 1332985 1333591 := bstep (se 1 (by rfl) ⟨1000193, by rfl⟩ : syracuseStep 1333591 = 2000387) B2000387
theorem B1333611 : Blo 1332985 1333611 := bstep (se 1 (by rfl) ⟨1000208, by rfl⟩ : syracuseStep 1333611 = 2000417) B2000417
theorem B1333623 : Blo 1332985 1333623 := bstep (se 1 (by rfl) ⟨1000217, by rfl⟩ : syracuseStep 1333623 = 2000435) B2000435
theorem B1333643 : Blo 1332985 1333643 := bstep (se 1 (by rfl) ⟨1000232, by rfl⟩ : syracuseStep 1333643 = 2000465) B2000465
theorem B1333655 : Blo 1332985 1333655 := bstep (se 1 (by rfl) ⟨1000241, by rfl⟩ : syracuseStep 1333655 = 2000483) B2000483
theorem B1898903 : Blo 1332985 1898903 := bstep (se 1 (by rfl) ⟨1424177, by rfl⟩ : syracuseStep 1898903 = 2848355) B2848355
theorem B2709911 : Blo 1332985 2709911 := bstep (se 1 (by rfl) ⟨2032433, by rfl⟩ : syracuseStep 2709911 = 4064867) B4064867
theorem B1333675 : Blo 1332985 1333675 := bstep (se 1 (by rfl) ⟨1000256, by rfl⟩ : syracuseStep 1333675 = 2000513) B2000513
theorem B6748595 : Blo 1332985 6748595 := bstep (se 1 (by rfl) ⟨5061446, by rfl⟩ : syracuseStep 6748595 = 10122893) B10122893
theorem B1333687 : Blo 1332985 1333687 := bstep (se 1 (by rfl) ⟨1000265, by rfl⟩ : syracuseStep 1333687 = 2000531) B2000531
theorem B1333707 : Blo 1332985 1333707 := bstep (se 1 (by rfl) ⟨1000280, by rfl⟩ : syracuseStep 1333707 = 2000561) B2000561
theorem B1333719 : Blo 1332985 1333719 := bstep (se 1 (by rfl) ⟨1000289, by rfl⟩ : syracuseStep 1333719 = 2000579) B2000579
theorem B6494681 : Blo 1332985 6494681 := bstep (se 2 (by rfl) ⟨2435505, by rfl⟩ : syracuseStep 6494681 = 4871011) B4871011
theorem B4807133 : Blo 1332985 4807133 := bstep (se 3 (by rfl) ⟨901337, by rfl⟩ : syracuseStep 4807133 = 1802675) B1802675
theorem B1333739 : Blo 1332985 1333739 := bstep (se 1 (by rfl) ⟨1000304, by rfl⟩ : syracuseStep 1333739 = 2000609) B2000609
theorem B1333751 : Blo 1332985 1333751 := bstep (se 1 (by rfl) ⟨1000313, by rfl⟩ : syracuseStep 1333751 = 2000627) B2000627
theorem B1333771 : Blo 1332985 1333771 := bstep (se 1 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 1333771 = 2000657) B2000657
theorem B1333783 : Blo 1332985 1333783 := bstep (se 1 (by rfl) ⟨1000337, by rfl⟩ : syracuseStep 1333783 = 2000675) B2000675
theorem B1333803 : Blo 1332985 1333803 := bstep (se 1 (by rfl) ⟨1000352, by rfl⟩ : syracuseStep 1333803 = 2000705) B2000705
theorem B1333815 : Blo 1332985 1333815 := bstep (se 1 (by rfl) ⟨1000361, by rfl⟩ : syracuseStep 1333815 = 2000723) B2000723
theorem B1333835 : Blo 1332985 1333835 := bstep (se 1 (by rfl) ⟨1000376, by rfl⟩ : syracuseStep 1333835 = 2000753) B2000753
theorem B7600715 : Blo 1332985 7600715 := bstep (se 1 (by rfl) ⟨5700536, by rfl⟩ : syracuseStep 7600715 = 11401073) B11401073
theorem B4504139 : Blo 1332985 4504139 := bstep (se 1 (by rfl) ⟨3378104, by rfl⟩ : syracuseStep 4504139 = 6756209) B6756209
theorem B1333847 : Blo 1332985 1333847 := bstep (se 1 (by rfl) ⟨1000385, by rfl⟩ : syracuseStep 1333847 = 2000771) B2000771
theorem B1333867 : Blo 1332985 1333867 := bstep (se 1 (by rfl) ⟨1000400, by rfl⟩ : syracuseStep 1333867 = 2000801) B2000801
theorem B1333879 : Blo 1332985 1333879 := bstep (se 1 (by rfl) ⟨1000409, by rfl⟩ : syracuseStep 1333879 = 2000819) B2000819
theorem B1333899 : Blo 1332985 1333899 := bstep (se 1 (by rfl) ⟨1000424, by rfl⟩ : syracuseStep 1333899 = 2000849) B2000849
theorem B1333911 : Blo 1332985 1333911 := bstep (se 1 (by rfl) ⟨1000433, by rfl⟩ : syracuseStep 1333911 = 2000867) B2000867
theorem B2251415 : Blo 1332985 2251415 := bstep (se 1 (by rfl) ⟨1688561, by rfl⟩ : syracuseStep 2251415 = 3377123) B3377123
theorem B1333931 : Blo 1332985 1333931 := bstep (se 1 (by rfl) ⟨1000448, by rfl⟩ : syracuseStep 1333931 = 2000897) B2000897
theorem B1333943 : Blo 1332985 1333943 := bstep (se 1 (by rfl) ⟨1000457, by rfl⟩ : syracuseStep 1333943 = 2000915) B2000915
theorem B1333963 : Blo 1332985 1333963 := bstep (se 1 (by rfl) ⟨1000472, by rfl⟩ : syracuseStep 1333963 = 2000945) B2000945
theorem B1333975 : Blo 1332985 1333975 := bstep (se 1 (by rfl) ⟨1000481, by rfl⟩ : syracuseStep 1333975 = 2000963) B2000963
theorem B1333995 : Blo 1332985 1333995 := bstep (se 1 (by rfl) ⟨1000496, by rfl⟩ : syracuseStep 1333995 = 2000993) B2000993
theorem B1334007 : Blo 1332985 1334007 := bstep (se 1 (by rfl) ⟨1000505, by rfl⟩ : syracuseStep 1334007 = 2001011) B2001011
theorem B1334027 : Blo 1332985 1334027 := bstep (se 1 (by rfl) ⟨1000520, by rfl⟩ : syracuseStep 1334027 = 2001041) B2001041
theorem B1334039 : Blo 1332985 1334039 := bstep (se 1 (by rfl) ⟨1000529, by rfl⟩ : syracuseStep 1334039 = 2001059) B2001059
theorem B2251543 : Blo 1332985 2251543 := bstep (se 1 (by rfl) ⟨1688657, by rfl⟩ : syracuseStep 2251543 = 3377315) B3377315
theorem B1334059 : Blo 1332985 1334059 := bstep (se 1 (by rfl) ⟨1000544, by rfl⟩ : syracuseStep 1334059 = 2001089) B2001089
theorem B1334071 : Blo 1332985 1334071 := bstep (se 1 (by rfl) ⟨1000553, by rfl⟩ : syracuseStep 1334071 = 2001107) B2001107
theorem B1334091 : Blo 1332985 1334091 := bstep (se 1 (by rfl) ⟨1000568, by rfl⟩ : syracuseStep 1334091 = 2001137) B2001137
theorem B1334103 : Blo 1332985 1334103 := bstep (se 1 (by rfl) ⟨1000577, by rfl⟩ : syracuseStep 1334103 = 2001155) B2001155
theorem B4504409 : Blo 1332985 4504409 := bstep (se 2 (by rfl) ⟨1689153, by rfl⟩ : syracuseStep 4504409 = 3378307) B3378307
theorem B1334123 : Blo 1332985 1334123 := bstep (se 1 (by rfl) ⟨1000592, by rfl⟩ : syracuseStep 1334123 = 2001185) B2001185
theorem B1334135 : Blo 1332985 1334135 := bstep (se 1 (by rfl) ⟨1000601, by rfl⟩ : syracuseStep 1334135 = 2001203) B2001203
theorem B1334155 : Blo 1332985 1334155 := bstep (se 1 (by rfl) ⟨1000616, by rfl⟩ : syracuseStep 1334155 = 2001233) B2001233
theorem B1334167 : Blo 1332985 1334167 := bstep (se 1 (by rfl) ⟨1000625, by rfl⟩ : syracuseStep 1334167 = 2001251) B2001251
theorem B1334187 : Blo 1332985 1334187 := bstep (se 1 (by rfl) ⟨1000640, by rfl⟩ : syracuseStep 1334187 = 2001281) B2001281
theorem B1334199 : Blo 1332985 1334199 := bstep (se 1 (by rfl) ⟨1000649, by rfl⟩ : syracuseStep 1334199 = 2001299) B2001299
theorem B1334219 : Blo 1332985 1334219 := bstep (se 1 (by rfl) ⟨1000664, by rfl⟩ : syracuseStep 1334219 = 2001329) B2001329
theorem B1334231 : Blo 1332985 1334231 := bstep (se 1 (by rfl) ⟨1000673, by rfl⟩ : syracuseStep 1334231 = 2001347) B2001347
theorem B1334251 : Blo 1332985 1334251 := bstep (se 1 (by rfl) ⟨1000688, by rfl⟩ : syracuseStep 1334251 = 2001377) B2001377
theorem B1334263 : Blo 1332985 1334263 := bstep (se 1 (by rfl) ⟨1000697, by rfl⟩ : syracuseStep 1334263 = 2001395) B2001395
theorem B1424395 : Blo 1332985 1424395 := bstep (se 1 (by rfl) ⟨1068296, by rfl⟩ : syracuseStep 1424395 = 2136593) B2136593
theorem B1334283 : Blo 1332985 1334283 := bstep (se 1 (by rfl) ⟨1000712, by rfl⟩ : syracuseStep 1334283 = 2001425) B2001425
theorem B1334295 : Blo 1332985 1334295 := bstep (se 1 (by rfl) ⟨1000721, by rfl⟩ : syracuseStep 1334295 = 2001443) B2001443
theorem B1334315 : Blo 1332985 1334315 := bstep (se 1 (by rfl) ⟨1000736, by rfl⟩ : syracuseStep 1334315 = 2001473) B2001473
theorem B5405741 : Blo 1332985 5405741 := bstep (se 3 (by rfl) ⟨1013576, by rfl⟩ : syracuseStep 5405741 = 2027153) B2027153
theorem B1334327 : Blo 1332985 1334327 := bstep (se 1 (by rfl) ⟨1000745, by rfl⟩ : syracuseStep 1334327 = 2001491) B2001491
theorem B10959947 : Blo 1332985 10959947 := bstep (se 1 (by rfl) ⟨8219960, by rfl⟩ : syracuseStep 10959947 = 16439921) B16439921
theorem B1334347 : Blo 1332985 1334347 := bstep (se 1 (by rfl) ⟨1000760, by rfl⟩ : syracuseStep 1334347 = 2001521) B2001521
theorem B1334359 : Blo 1332985 1334359 := bstep (se 1 (by rfl) ⟨1000769, by rfl⟩ : syracuseStep 1334359 = 2001539) B2001539
theorem B1334379 : Blo 1332985 1334379 := bstep (se 1 (by rfl) ⟨1000784, by rfl⟩ : syracuseStep 1334379 = 2001569) B2001569
theorem B1334391 : Blo 1332985 1334391 := bstep (se 1 (by rfl) ⟨1000793, by rfl⟩ : syracuseStep 1334391 = 2001587) B2001587
theorem B1334411 : Blo 1332985 1334411 := bstep (se 1 (by rfl) ⟨1000808, by rfl⟩ : syracuseStep 1334411 = 2001617) B2001617
theorem B1334423 : Blo 1332985 1334423 := bstep (se 1 (by rfl) ⟨1000817, by rfl⟩ : syracuseStep 1334423 = 2001635) B2001635
theorem B2137241 : Blo 1332985 2137241 := bstep (se 2 (by rfl) ⟨801465, by rfl⟩ : syracuseStep 2137241 = 1602931) B1602931
theorem B1334443 : Blo 1332985 1334443 := bstep (se 1 (by rfl) ⟨1000832, by rfl⟩ : syracuseStep 1334443 = 2001665) B2001665
theorem B5061811 : Blo 1332985 5061811 := bstep (se 1 (by rfl) ⟨3796358, by rfl⟩ : syracuseStep 5061811 = 7592717) B7592717
theorem B1334455 : Blo 1332985 1334455 := bstep (se 1 (by rfl) ⟨1000841, by rfl⟩ : syracuseStep 1334455 = 2001683) B2001683
theorem B2849995 : Blo 1332985 2849995 := bstep (se 1 (by rfl) ⟨2137496, by rfl⟩ : syracuseStep 2849995 = 4274993) B4274993
theorem B1334475 : Blo 1332985 1334475 := bstep (se 1 (by rfl) ⟨1000856, by rfl⟩ : syracuseStep 1334475 = 2001713) B2001713
theorem B3800267 : Blo 1332985 3800267 := bstep (se 1 (by rfl) ⟨2850200, by rfl⟩ : syracuseStep 3800267 = 5700401) B5700401
theorem B1334487 : Blo 1332985 1334487 := bstep (se 1 (by rfl) ⟨1000865, by rfl⟩ : syracuseStep 1334487 = 2001731) B2001731
theorem B6085853 : Blo 1332985 6085853 := bstep (se 3 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 6085853 = 2282195) B2282195
theorem B1334507 : Blo 1332985 1334507 := bstep (se 1 (by rfl) ⟨1000880, by rfl⟩ : syracuseStep 1334507 = 2001761) B2001761
theorem B1334519 : Blo 1332985 1334519 := bstep (se 1 (by rfl) ⟨1000889, by rfl⟩ : syracuseStep 1334519 = 2001779) B2001779
theorem B1334539 : Blo 1332985 1334539 := bstep (se 1 (by rfl) ⟨1000904, by rfl⟩ : syracuseStep 1334539 = 2001809) B2001809
theorem B2850071 : Blo 1332985 2850071 := bstep (se 1 (by rfl) ⟨2137553, by rfl⟩ : syracuseStep 2850071 = 4275107) B4275107
theorem B1334551 : Blo 1332985 1334551 := bstep (se 1 (by rfl) ⟨1000913, by rfl⟩ : syracuseStep 1334551 = 2001827) B2001827
theorem B1334571 : Blo 1332985 1334571 := bstep (se 1 (by rfl) ⟨1000928, by rfl⟩ : syracuseStep 1334571 = 2001857) B2001857
theorem B1334583 : Blo 1332985 1334583 := bstep (se 1 (by rfl) ⟨1000937, by rfl⟩ : syracuseStep 1334583 = 2001875) B2001875
theorem B1334603 : Blo 1332985 1334603 := bstep (se 1 (by rfl) ⟨1000952, by rfl⟩ : syracuseStep 1334603 = 2001905) B2001905
theorem B1334615 : Blo 1332985 1334615 := bstep (se 1 (by rfl) ⟨1000961, by rfl⟩ : syracuseStep 1334615 = 2001923) B2001923
theorem B1899865 : Blo 1332985 1899865 := bstep (se 2 (by rfl) ⟨712449, by rfl⟩ : syracuseStep 1899865 = 1424899) B1424899
theorem B1334635 : Blo 1332985 1334635 := bstep (se 1 (by rfl) ⟨1000976, by rfl⟩ : syracuseStep 1334635 = 2001953) B2001953
theorem B1334647 : Blo 1332985 1334647 := bstep (se 1 (by rfl) ⟨1000985, by rfl⟩ : syracuseStep 1334647 = 2001971) B2001971
theorem B2252171 : Blo 1332985 2252171 := bstep (se 1 (by rfl) ⟨1689128, by rfl⟩ : syracuseStep 2252171 = 3378257) B3378257
theorem B1334667 : Blo 1332985 1334667 := bstep (se 1 (by rfl) ⟨1001000, by rfl⟩ : syracuseStep 1334667 = 2002001) B2002001
theorem B1334679 : Blo 1332985 1334679 := bstep (se 1 (by rfl) ⟨1001009, by rfl⟩ : syracuseStep 1334679 = 2002019) B2002019
theorem B1334699 : Blo 1332985 1334699 := bstep (se 1 (by rfl) ⟨1001024, by rfl⟩ : syracuseStep 1334699 = 2002049) B2002049
theorem B17087921 : Blo 1332985 17087921 := bstep (se 2 (by rfl) ⟨6407970, by rfl⟩ : syracuseStep 17087921 = 12815941) B12815941
theorem B2530739 : Blo 1332985 2530739 := bstep (se 1 (by rfl) ⟨1898054, by rfl⟩ : syracuseStep 2530739 = 3796109) B3796109
theorem B1334711 : Blo 1332985 1334711 := bstep (se 1 (by rfl) ⟨1001033, by rfl⟩ : syracuseStep 1334711 = 2002067) B2002067
theorem B1334731 : Blo 1332985 1334731 := bstep (se 1 (by rfl) ⟨1001048, by rfl⟩ : syracuseStep 1334731 = 2002097) B2002097
theorem B1334743 : Blo 1332985 1334743 := bstep (se 1 (by rfl) ⟨1001057, by rfl⟩ : syracuseStep 1334743 = 2002115) B2002115
theorem B2530777 : Blo 1332985 2530777 := bstep (se 2 (by rfl) ⟨949041, by rfl⟩ : syracuseStep 2530777 = 1898083) B1898083
theorem B1334763 : Blo 1332985 1334763 := bstep (se 1 (by rfl) ⟨1001072, by rfl⟩ : syracuseStep 1334763 = 2002145) B2002145
theorem B1334775 : Blo 1332985 1334775 := bstep (se 1 (by rfl) ⟨1001081, by rfl⟩ : syracuseStep 1334775 = 2002163) B2002163
theorem B2252299 : Blo 1332985 2252299 := bstep (se 1 (by rfl) ⟨1689224, by rfl⟩ : syracuseStep 2252299 = 3378449) B3378449
theorem B1334795 : Blo 1332985 1334795 := bstep (se 1 (by rfl) ⟨1001096, by rfl⟩ : syracuseStep 1334795 = 2002193) B2002193
theorem B1687063 : Blo 1332985 1687063 := bstep (se 1 (by rfl) ⟨1265297, by rfl⟩ : syracuseStep 1687063 = 2530595) B2530595
theorem B1334807 : Blo 1332985 1334807 := bstep (se 1 (by rfl) ⟨1001105, by rfl⟩ : syracuseStep 1334807 = 2002211) B2002211
theorem B4505111 : Blo 1332985 4505111 := bstep (se 1 (by rfl) ⟨3378833, by rfl⟩ : syracuseStep 4505111 = 6757667) B6757667
theorem B1334827 : Blo 1332985 1334827 := bstep (se 1 (by rfl) ⟨1001120, by rfl⟩ : syracuseStep 1334827 = 2002241) B2002241
theorem B1334839 : Blo 1332985 1334839 := bstep (se 1 (by rfl) ⟨1001129, by rfl⟩ : syracuseStep 1334839 = 2002259) B2002259
theorem B1334859 : Blo 1332985 1334859 := bstep (se 1 (by rfl) ⟨1001144, by rfl⟩ : syracuseStep 1334859 = 2002289) B2002289
theorem B1334871 : Blo 1332985 1334871 := bstep (se 1 (by rfl) ⟨1001153, by rfl⟩ : syracuseStep 1334871 = 2002307) B2002307
theorem B1334891 : Blo 1332985 1334891 := bstep (se 1 (by rfl) ⟨1001168, by rfl⟩ : syracuseStep 1334891 = 2002337) B2002337
theorem B1334903 : Blo 1332985 1334903 := bstep (se 1 (by rfl) ⟨1001177, by rfl⟩ : syracuseStep 1334903 = 2002355) B2002355
theorem B1334923 : Blo 1332985 1334923 := bstep (se 1 (by rfl) ⟨1001192, by rfl⟩ : syracuseStep 1334923 = 2002385) B2002385
theorem B3374743 : Blo 1332985 3374743 := bstep (se 1 (by rfl) ⟨2531057, by rfl⟩ : syracuseStep 3374743 = 5062115) B5062115
theorem B1334935 : Blo 1332985 1334935 := bstep (se 1 (by rfl) ⟨1001201, by rfl⟩ : syracuseStep 1334935 = 2002403) B2002403
theorem B2252441 : Blo 1332985 2252441 := bstep (se 2 (by rfl) ⟨844665, by rfl⟩ : syracuseStep 2252441 = 1689331) B1689331
theorem B1334955 : Blo 1332985 1334955 := bstep (se 1 (by rfl) ⟨1001216, by rfl⟩ : syracuseStep 1334955 = 2002433) B2002433
theorem B1334967 : Blo 1332985 1334967 := bstep (se 1 (by rfl) ⟨1001225, by rfl⟩ : syracuseStep 1334967 = 2002451) B2002451
theorem B2252569 : Blo 1332985 2252569 := bstep (se 2 (by rfl) ⟨844713, by rfl⟩ : syracuseStep 2252569 = 1689427) B1689427
theorem B5701441 : Blo 1332985 5701441 := bstep (se 2 (by rfl) ⟨2138040, by rfl⟩ : syracuseStep 5701441 = 4276081) B4276081
theorem B7208797 : Blo 1332985 7208797 := bstep (se 3 (by rfl) ⟨1351649, by rfl⟩ : syracuseStep 7208797 = 2703299) B2703299
theorem B1425271 : Blo 1332985 1425271 := bstep (se 1 (by rfl) ⟨1068953, by rfl⟩ : syracuseStep 1425271 = 2137907) B2137907
theorem B2531225 : Blo 1332985 2531225 := bstep (se 2 (by rfl) ⟨949209, by rfl⟩ : syracuseStep 2531225 = 1898419) B1898419
theorem B10125323 : Blo 1332985 10125323 := bstep (se 1 (by rfl) ⟨7593992, by rfl⟩ : syracuseStep 10125323 = 15187985) B15187985
theorem B4276235 : Blo 1332985 4276235 := bstep (se 1 (by rfl) ⟨3207176, by rfl⟩ : syracuseStep 4276235 = 6414353) B6414353
theorem B4808747 : Blo 1332985 4808747 := bstep (se 1 (by rfl) ⟨3606560, by rfl⟩ : syracuseStep 4808747 = 7213121) B7213121
theorem B2531513 : Blo 1332985 2531513 := bstep (se 2 (by rfl) ⟨949317, by rfl⟩ : syracuseStep 2531513 = 1898635) B1898635
theorem B3375371 : Blo 1332985 3375371 := bstep (se 1 (by rfl) ⟨2531528, by rfl⟩ : syracuseStep 3375371 = 5063057) B5063057
theorem B3424523 : Blo 1332985 3424523 := bstep (se 1 (by rfl) ⟨2568392, by rfl⟩ : syracuseStep 3424523 = 5136785) B5136785
theorem B1352071 : Blo 1332985 1352071 := bstep (se 1 (by rfl) ⟨1014053, by rfl⟩ : syracuseStep 1352071 = 2028107) B2028107
theorem B4276633 : Blo 1332985 4276633 := bstep (se 2 (by rfl) ⟨1603737, by rfl⟩ : syracuseStep 4276633 = 3207475) B3207475
theorem B1687979 : Blo 1332985 1687979 := bstep (se 1 (by rfl) ⟨1265984, by rfl⟩ : syracuseStep 1687979 = 2531969) B2531969
theorem B3424769 : Blo 1332985 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B5136907 : Blo 1332985 5136907 := bstep (se 1 (by rfl) ⟨3852680, by rfl⟩ : syracuseStep 5136907 = 7705361) B7705361
theorem B4276747 : Blo 1332985 4276747 := bstep (se 1 (by rfl) ⟨3207560, by rfl⟩ : syracuseStep 4276747 = 6415121) B6415121
theorem B6840919 : Blo 1332985 6840919 := bstep (se 1 (by rfl) ⟨5130689, by rfl⟩ : syracuseStep 6840919 = 10261379) B10261379
theorem B5063255 : Blo 1332985 5063255 := bstep (se 1 (by rfl) ⟨3797441, by rfl⟩ : syracuseStep 5063255 = 7594883) B7594883
theorem B6414967 : Blo 1332985 6414967 := bstep (se 1 (by rfl) ⟨4811225, by rfl⟩ : syracuseStep 6414967 = 9622451) B9622451
theorem B1499791 : Blo 1332985 1499791 := bstep (se 1 (by rfl) ⟨1124843, by rfl⟩ : syracuseStep 1499791 = 2249687) B2249687
theorem B1999547 : Blo 1332985 1999547 := bstep (se 1 (by rfl) ⟨1499660, by rfl⟩ : syracuseStep 1999547 = 2999321) B2999321
theorem B1999607 : Blo 1332985 1999607 := bstep (se 1 (by rfl) ⟨1499705, by rfl⟩ : syracuseStep 1999607 = 2999411) B2999411
theorem B1999631 : Blo 1332985 1999631 := bstep (se 1 (by rfl) ⟨1499723, by rfl⟩ : syracuseStep 1999631 = 2999447) B2999447
theorem B1999673 : Blo 1332985 1999673 := bstep (se 2 (by rfl) ⟨749877, by rfl⟩ : syracuseStep 1999673 = 1499755) B1499755
theorem B1999751 : Blo 1332985 1999751 := bstep (se 1 (by rfl) ⟨1499813, by rfl⟩ : syracuseStep 1999751 = 2999627) B2999627
theorem B1688455 : Blo 1332985 1688455 := bstep (se 1 (by rfl) ⟨1266341, by rfl⟩ : syracuseStep 1688455 = 2532683) B2532683
theorem B3376019 : Blo 1332985 3376019 := bstep (se 1 (by rfl) ⟨2532014, by rfl⟩ : syracuseStep 3376019 = 5064029) B5064029
theorem B1999787 : Blo 1332985 1999787 := bstep (se 1 (by rfl) ⟨1499840, by rfl⟩ : syracuseStep 1999787 = 2999681) B2999681
theorem B1999817 : Blo 1332985 1999817 := bstep (se 2 (by rfl) ⟨749931, by rfl⟩ : syracuseStep 1999817 = 1499863) B1499863
theorem B2999339 : Blo 1332985 2999339 := bstep (se 1 (by rfl) ⟨2249504, by rfl⟩ : syracuseStep 2999339 = 4499009) B4499009
theorem B1999931 : Blo 1332985 1999931 := bstep (se 1 (by rfl) ⟨1499948, by rfl⟩ : syracuseStep 1999931 = 2999897) B2999897
theorem B5063741 : Blo 1332985 5063741 := bstep (se 3 (by rfl) ⟨949451, by rfl⟩ : syracuseStep 5063741 = 1898903) B1898903
theorem B5858365 : Blo 1332985 5858365 := bstep (se 3 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 5858365 = 2196887) B2196887
theorem B1999991 : Blo 1332985 1999991 := bstep (se 1 (by rfl) ⟨1499993, by rfl⟩ : syracuseStep 1999991 = 2999987) B2999987
theorem B1500295 : Blo 1332985 1500295 := bstep (se 1 (by rfl) ⟨1125221, by rfl⟩ : syracuseStep 1500295 = 2250443) B2250443
theorem B2000015 : Blo 1332985 2000015 := bstep (se 1 (by rfl) ⟨1500011, by rfl⟩ : syracuseStep 2000015 = 3000023) B3000023
theorem B2000057 : Blo 1332985 2000057 := bstep (se 2 (by rfl) ⟨750021, by rfl⟩ : syracuseStep 2000057 = 1500043) B1500043
theorem B3376313 : Blo 1332985 3376313 := bstep (se 2 (by rfl) ⟨1266117, by rfl⟩ : syracuseStep 3376313 = 2532235) B2532235
theorem B2000135 : Blo 1332985 2000135 := bstep (se 1 (by rfl) ⟨1500101, by rfl⟩ : syracuseStep 2000135 = 3000203) B3000203
theorem B2000171 : Blo 1332985 2000171 := bstep (se 1 (by rfl) ⟨1500128, by rfl⟩ : syracuseStep 2000171 = 3000257) B3000257
theorem B7595315 : Blo 1332985 7595315 := bstep (se 1 (by rfl) ⟨5696486, by rfl⟩ : syracuseStep 7595315 = 11392973) B11392973
theorem B1500475 : Blo 1332985 1500475 := bstep (se 1 (by rfl) ⟨1125356, by rfl⟩ : syracuseStep 1500475 = 2250713) B2250713
theorem B2000201 : Blo 1332985 2000201 := bstep (se 2 (by rfl) ⟨750075, by rfl⟩ : syracuseStep 2000201 = 1500151) B1500151
theorem B1688951 : Blo 1332985 1688951 := bstep (se 1 (by rfl) ⟨1266713, by rfl⟩ : syracuseStep 1688951 = 2533427) B2533427
theorem B2999699 : Blo 1332985 2999699 := bstep (se 1 (by rfl) ⟨2249774, by rfl⟩ : syracuseStep 2999699 = 4499549) B4499549
theorem B6751673 : Blo 1332985 6751673 := bstep (se 2 (by rfl) ⟨2531877, by rfl⟩ : syracuseStep 6751673 = 5063755) B5063755
theorem B2000315 : Blo 1332985 2000315 := bstep (se 1 (by rfl) ⟨1500236, by rfl⟩ : syracuseStep 2000315 = 3000473) B3000473
theorem B2999753 : Blo 1332985 2999753 := bstep (se 2 (by rfl) ⟨1124907, by rfl⟩ : syracuseStep 2999753 = 2249815) B2249815
theorem B2000375 : Blo 1332985 2000375 := bstep (se 1 (by rfl) ⟨1500281, by rfl⟩ : syracuseStep 2000375 = 3000563) B3000563
theorem B10135043 : Blo 1332985 10135043 := bstep (se 1 (by rfl) ⟨7601282, by rfl⟩ : syracuseStep 10135043 = 15202565) B15202565
theorem B4498955 : Blo 1332985 4498955 := bstep (se 1 (by rfl) ⟨3374216, by rfl⟩ : syracuseStep 4498955 = 6748433) B6748433
theorem B2000399 : Blo 1332985 2000399 := bstep (se 1 (by rfl) ⟨1500299, by rfl⟩ : syracuseStep 2000399 = 3000599) B3000599
theorem B1689103 : Blo 1332985 1689103 := bstep (se 1 (by rfl) ⟨1266827, by rfl⟩ : syracuseStep 1689103 = 2533655) B2533655
theorem B3040811 : Blo 1332985 3040811 := bstep (se 1 (by rfl) ⟨2280608, by rfl⟩ : syracuseStep 3040811 = 4561217) B4561217
theorem B2000441 : Blo 1332985 2000441 := bstep (se 2 (by rfl) ⟨750165, by rfl⟩ : syracuseStep 2000441 = 1500331) B1500331
theorem B4499063 : Blo 1332985 4499063 := bstep (se 1 (by rfl) ⟨3374297, by rfl⟩ : syracuseStep 4499063 = 6748595) B6748595
theorem B2000519 : Blo 1332985 2000519 := bstep (se 1 (by rfl) ⟨1500389, by rfl⟩ : syracuseStep 2000519 = 3000779) B3000779
theorem B3204755 : Blo 1332985 3204755 := bstep (se 1 (by rfl) ⟨2403566, by rfl⟩ : syracuseStep 3204755 = 4807133) B4807133
theorem B2000555 : Blo 1332985 2000555 := bstep (se 1 (by rfl) ⟨1500416, by rfl⟩ : syracuseStep 2000555 = 3000833) B3000833
theorem B1689275 : Blo 1332985 1689275 := bstep (se 1 (by rfl) ⟨1266956, by rfl⟩ : syracuseStep 1689275 = 2533913) B2533913
theorem B2000585 : Blo 1332985 2000585 := bstep (se 2 (by rfl) ⟨750219, by rfl⟩ : syracuseStep 2000585 = 1500439) B1500439
theorem B12822245 : Blo 1332985 12822245 := bstep (se 4 (by rfl) ⟨1202085, by rfl⟩ : syracuseStep 12822245 = 2404171) B2404171
theorem B1500943 : Blo 1332985 1500943 := bstep (se 1 (by rfl) ⟨1125707, by rfl⟩ : syracuseStep 1500943 = 2251415) B2251415
theorem B2000699 : Blo 1332985 2000699 := bstep (se 1 (by rfl) ⟨1500524, by rfl⟩ : syracuseStep 2000699 = 3001049) B3001049
theorem B3377011 : Blo 1332985 3377011 := bstep (se 1 (by rfl) ⟨2532758, by rfl⟩ : syracuseStep 3377011 = 5065517) B5065517
theorem B2000759 : Blo 1332985 2000759 := bstep (se 1 (by rfl) ⟨1500569, by rfl⟩ : syracuseStep 2000759 = 3001139) B3001139
theorem B2000783 : Blo 1332985 2000783 := bstep (se 1 (by rfl) ⟨1500587, by rfl⟩ : syracuseStep 2000783 = 3001175) B3001175
theorem B10127267 : Blo 1332985 10127267 := bstep (se 1 (by rfl) ⟨7595450, by rfl⟩ : syracuseStep 10127267 = 15190901) B15190901
theorem B2000825 : Blo 1332985 2000825 := bstep (se 2 (by rfl) ⟨750309, by rfl⟩ : syracuseStep 2000825 = 1500619) B1500619
theorem B19744715 : Blo 1332985 19744715 := bstep (se 1 (by rfl) ⟨14808536, by rfl⟩ : syracuseStep 19744715 = 29617073) B29617073
theorem B3377153 : Blo 1332985 3377153 := bstep (se 2 (by rfl) ⟨1266432, by rfl⟩ : syracuseStep 3377153 = 2532865) B2532865
theorem B2000903 : Blo 1332985 2000903 := bstep (se 1 (by rfl) ⟨1500677, by rfl⟩ : syracuseStep 2000903 = 3001355) B3001355
theorem B2000939 : Blo 1332985 2000939 := bstep (se 1 (by rfl) ⟨1500704, by rfl⟩ : syracuseStep 2000939 = 3001409) B3001409
theorem B2000969 : Blo 1332985 2000969 := bstep (se 2 (by rfl) ⟨750363, by rfl⟩ : syracuseStep 2000969 = 1500727) B1500727
theorem B5408855 : Blo 1332985 5408855 := bstep (se 1 (by rfl) ⟨4056641, by rfl⟩ : syracuseStep 5408855 = 8113283) B8113283
theorem B3000455 : Blo 1332985 3000455 := bstep (se 1 (by rfl) ⟨2250341, by rfl⟩ : syracuseStep 3000455 = 4500683) B4500683
theorem B2533511 : Blo 1332985 2533511 := bstep (se 1 (by rfl) ⟨1900133, by rfl⟩ : syracuseStep 2533511 = 3800267) B3800267
theorem B4057235 : Blo 1332985 4057235 := bstep (se 1 (by rfl) ⟨3042926, by rfl⟩ : syracuseStep 4057235 = 6085853) B6085853
theorem B2001083 : Blo 1332985 2001083 := bstep (se 1 (by rfl) ⟨1500812, by rfl⟩ : syracuseStep 2001083 = 3001625) B3001625
theorem B4499657 : Blo 1332985 4499657 := bstep (se 2 (by rfl) ⟨1687371, by rfl⟩ : syracuseStep 4499657 = 3374743) B3374743
theorem B2001143 : Blo 1332985 2001143 := bstep (se 1 (by rfl) ⟨1500857, by rfl⟩ : syracuseStep 2001143 = 3001715) B3001715
theorem B1501447 : Blo 1332985 1501447 := bstep (se 1 (by rfl) ⟨1126085, by rfl⟩ : syracuseStep 1501447 = 2252171) B2252171
theorem B2001167 : Blo 1332985 2001167 := bstep (se 1 (by rfl) ⟨1500875, by rfl⟩ : syracuseStep 2001167 = 3001751) B3001751
theorem B46803253 : Blo 1332985 46803253 := bstep (se 5 (by rfl) ⟨2193902, by rfl⟩ : syracuseStep 46803253 = 4387805) B4387805
theorem B2001209 : Blo 1332985 2001209 := bstep (se 2 (by rfl) ⟨750453, by rfl⟩ : syracuseStep 2001209 = 1500907) B1500907
theorem B3000635 : Blo 1332985 3000635 := bstep (se 1 (by rfl) ⟨2250476, by rfl⟩ : syracuseStep 3000635 = 4500953) B4500953
theorem B39520577 : Blo 1332985 39520577 := bstep (se 2 (by rfl) ⟨14820216, by rfl⟩ : syracuseStep 39520577 = 29640433) B29640433
theorem B2001287 : Blo 1332985 2001287 := bstep (se 1 (by rfl) ⟨1500965, by rfl⟩ : syracuseStep 2001287 = 3001931) B3001931
theorem B8546705 : Blo 1332985 8546705 := bstep (se 2 (by rfl) ⟨3205014, by rfl⟩ : syracuseStep 8546705 = 6410029) B6410029
theorem B2001323 : Blo 1332985 2001323 := bstep (se 1 (by rfl) ⟨1500992, by rfl⟩ : syracuseStep 2001323 = 3001985) B3001985
theorem B3000761 : Blo 1332985 3000761 := bstep (se 2 (by rfl) ⟨1125285, by rfl⟩ : syracuseStep 3000761 = 2250571) B2250571
theorem B1501627 : Blo 1332985 1501627 := bstep (se 1 (by rfl) ⟨1126220, by rfl⟩ : syracuseStep 1501627 = 2252441) B2252441
theorem B2001353 : Blo 1332985 2001353 := bstep (se 2 (by rfl) ⟨750507, by rfl⟩ : syracuseStep 2001353 = 1501015) B1501015
theorem B3377609 : Blo 1332985 3377609 := bstep (se 2 (by rfl) ⟨1266603, by rfl⟩ : syracuseStep 3377609 = 2533207) B2533207
theorem B3008969 : Blo 1332985 3008969 := bstep (se 2 (by rfl) ⟨1128363, by rfl⟩ : syracuseStep 3008969 = 2256727) B2256727
theorem B9611729 : Blo 1332985 9611729 := bstep (se 2 (by rfl) ⟨3604398, by rfl⟩ : syracuseStep 9611729 = 7208797) B7208797
theorem B2886187 : Blo 1332985 2886187 := bstep (se 1 (by rfl) ⟨2164640, by rfl⟩ : syracuseStep 2886187 = 4329281) B4329281
theorem B2001467 : Blo 1332985 2001467 := bstep (se 1 (by rfl) ⟨1501100, by rfl⟩ : syracuseStep 2001467 = 3002201) B3002201
theorem B2001527 : Blo 1332985 2001527 := bstep (se 1 (by rfl) ⟨1501145, by rfl⟩ : syracuseStep 2001527 = 3002291) B3002291
theorem B2001551 : Blo 1332985 2001551 := bstep (se 1 (by rfl) ⟨1501163, by rfl⟩ : syracuseStep 2001551 = 3002327) B3002327
theorem B7211693 : Blo 1332985 7211693 := bstep (se 3 (by rfl) ⟨1352192, by rfl⟩ : syracuseStep 7211693 = 2704385) B2704385
theorem B2001593 : Blo 1332985 2001593 := bstep (se 2 (by rfl) ⟨750597, by rfl⟩ : syracuseStep 2001593 = 1501195) B1501195
theorem B6752969 : Blo 1332985 6752969 := bstep (se 2 (by rfl) ⟨2532363, by rfl⟩ : syracuseStep 6752969 = 5064727) B5064727
theorem B5778121 : Blo 1332985 5778121 := bstep (se 2 (by rfl) ⟨2166795, by rfl⟩ : syracuseStep 5778121 = 4333591) B4333591
theorem B7596773 : Blo 1332985 7596773 := bstep (se 4 (by rfl) ⟨712197, by rfl⟩ : syracuseStep 7596773 = 1424395) B1424395
theorem B2001671 : Blo 1332985 2001671 := bstep (se 1 (by rfl) ⟨1501253, by rfl⟩ : syracuseStep 2001671 = 3002507) B3002507
theorem B9612047 : Blo 1332985 9612047 := bstep (se 1 (by rfl) ⟨7209035, by rfl⟩ : syracuseStep 9612047 = 14418071) B14418071
theorem B3001103 : Blo 1332985 3001103 := bstep (se 1 (by rfl) ⟨2250827, by rfl⟩ : syracuseStep 3001103 = 4501655) B4501655
theorem B5065487 : Blo 1332985 5065487 := bstep (se 1 (by rfl) ⟨3799115, by rfl⟩ : syracuseStep 5065487 = 7598231) B7598231
theorem B3001121 : Blo 1332985 3001121 := bstep (se 2 (by rfl) ⟨1125420, by rfl⟩ : syracuseStep 3001121 = 2250841) B2250841
theorem B2001707 : Blo 1332985 2001707 := bstep (se 1 (by rfl) ⟨1501280, by rfl⟩ : syracuseStep 2001707 = 3002561) B3002561
theorem B3377963 : Blo 1332985 3377963 := bstep (se 1 (by rfl) ⟨2533472, by rfl⟩ : syracuseStep 3377963 = 5066945) B5066945
theorem B5696315 : Blo 1332985 5696315 := bstep (se 1 (by rfl) ⟨4272236, by rfl⟩ : syracuseStep 5696315 = 8544473) B8544473
theorem B2001737 : Blo 1332985 2001737 := bstep (se 2 (by rfl) ⟨750651, by rfl⟩ : syracuseStep 2001737 = 1501303) B1501303
theorem B4500359 : Blo 1332985 4500359 := bstep (se 1 (by rfl) ⟨3375269, by rfl⟩ : syracuseStep 4500359 = 6750539) B6750539
theorem B12331939 : Blo 1332985 12331939 := bstep (se 1 (by rfl) ⟨9248954, by rfl⟩ : syracuseStep 12331939 = 18497909) B18497909
theorem B2001851 : Blo 1332985 2001851 := bstep (se 1 (by rfl) ⟨1501388, by rfl⟩ : syracuseStep 2001851 = 3002777) B3002777
theorem B2001911 : Blo 1332985 2001911 := bstep (se 1 (by rfl) ⟨1501433, by rfl⟩ : syracuseStep 2001911 = 3002867) B3002867
theorem B8219659 : Blo 1332985 8219659 := bstep (se 1 (by rfl) ⟨6164744, by rfl⟩ : syracuseStep 8219659 = 12329489) B12329489
theorem B2886671 : Blo 1332985 2886671 := bstep (se 1 (by rfl) ⟨2165003, by rfl⟩ : syracuseStep 2886671 = 4330007) B4330007
theorem B2001935 : Blo 1332985 2001935 := bstep (se 1 (by rfl) ⟨1501451, by rfl⟩ : syracuseStep 2001935 = 3002903) B3002903
theorem B6171677 : Blo 1332985 6171677 := bstep (se 3 (by rfl) ⟨1157189, by rfl⟩ : syracuseStep 6171677 = 2314379) B2314379
theorem B2001977 : Blo 1332985 2001977 := bstep (se 2 (by rfl) ⟨750741, by rfl⟩ : syracuseStep 2001977 = 1501483) B1501483
theorem B3001463 : Blo 1332985 3001463 := bstep (se 1 (by rfl) ⟨2251097, by rfl⟩ : syracuseStep 3001463 = 4502195) B4502195
theorem B2002055 : Blo 1332985 2002055 := bstep (se 1 (by rfl) ⟨1501541, by rfl⟩ : syracuseStep 2002055 = 3003083) B3003083
theorem B2002091 : Blo 1332985 2002091 := bstep (se 1 (by rfl) ⟨1501568, by rfl⟩ : syracuseStep 2002091 = 3003137) B3003137
theorem B2002121 : Blo 1332985 2002121 := bstep (se 2 (by rfl) ⟨750795, by rfl⟩ : syracuseStep 2002121 = 1501591) B1501591
theorem B4500737 : Blo 1332985 4500737 := bstep (se 2 (by rfl) ⟨1687776, by rfl⟩ : syracuseStep 4500737 = 3375553) B3375553
theorem B3001643 : Blo 1332985 3001643 := bstep (se 1 (by rfl) ⟨2251232, by rfl⟩ : syracuseStep 3001643 = 4502465) B4502465
theorem B2002235 : Blo 1332985 2002235 := bstep (se 1 (by rfl) ⟨1501676, by rfl⟩ : syracuseStep 2002235 = 3003353) B3003353
theorem B2002295 : Blo 1332985 2002295 := bstep (se 1 (by rfl) ⟨1501721, by rfl⟩ : syracuseStep 2002295 = 3003443) B3003443
theorem B2002319 : Blo 1332985 2002319 := bstep (se 1 (by rfl) ⟨1501739, by rfl⟩ : syracuseStep 2002319 = 3003479) B3003479
theorem B9121169 : Blo 1332985 9121169 := bstep (se 2 (by rfl) ⟨3420438, by rfl⟩ : syracuseStep 9121169 = 6840877) B6840877
theorem B4271545 : Blo 1332985 4271545 := bstep (se 2 (by rfl) ⟨1601829, by rfl⟩ : syracuseStep 4271545 = 3203659) B3203659
theorem B2002361 : Blo 1332985 2002361 := bstep (se 2 (by rfl) ⟨750885, by rfl⟩ : syracuseStep 2002361 = 1501771) B1501771
theorem B2002439 : Blo 1332985 2002439 := bstep (se 1 (by rfl) ⟨1501829, by rfl⟩ : syracuseStep 2002439 = 3003659) B3003659
theorem B5697067 : Blo 1332985 5697067 := bstep (se 1 (by rfl) ⟨4272800, by rfl⟩ : syracuseStep 5697067 = 8545601) B8545601
theorem B2002475 : Blo 1332985 2002475 := bstep (se 1 (by rfl) ⟨1501856, by rfl⟩ : syracuseStep 2002475 = 3003713) B3003713
theorem B3796541 : Blo 1332985 3796541 := bstep (se 3 (by rfl) ⟨711851, by rfl⟩ : syracuseStep 3796541 = 1423703) B1423703
theorem B5410423 : Blo 1332985 5410423 := bstep (se 1 (by rfl) ⟨4057817, by rfl⟩ : syracuseStep 5410423 = 8115635) B8115635
theorem B3002003 : Blo 1332985 3002003 := bstep (se 1 (by rfl) ⟨2251502, by rfl⟩ : syracuseStep 3002003 = 4503005) B4503005
theorem B3043001 : Blo 1332985 3043001 := bstep (se 2 (by rfl) ⟨1141125, by rfl⟩ : syracuseStep 3043001 = 2282251) B2282251
theorem B3002057 : Blo 1332985 3002057 := bstep (se 2 (by rfl) ⟨1125771, by rfl⟩ : syracuseStep 3002057 = 2251543) B2251543
theorem B3378955 : Blo 1332985 3378955 := bstep (se 1 (by rfl) ⟨2534216, by rfl⟩ : syracuseStep 3378955 = 5068433) B5068433
theorem B3796769 : Blo 1332985 3796769 := bstep (se 2 (by rfl) ⟨1423788, by rfl⟩ : syracuseStep 3796769 = 2847577) B2847577
theorem B6590267 : Blo 1332985 6590267 := bstep (se 1 (by rfl) ⟨4942700, by rfl⟩ : syracuseStep 6590267 = 9885401) B9885401
theorem B3379097 : Blo 1332985 3379097 := bstep (se 2 (by rfl) ⟨1267161, by rfl⟩ : syracuseStep 3379097 = 2534323) B2534323
theorem B4501547 : Blo 1332985 4501547 := bstep (se 1 (by rfl) ⟨3376160, by rfl⟩ : syracuseStep 4501547 = 6752321) B6752321
theorem B58470493 : Blo 1332985 58470493 := bstep (se 3 (by rfl) ⟨10963217, by rfl⟩ : syracuseStep 58470493 = 21926435) B21926435
theorem B3797111 : Blo 1332985 3797111 := bstep (se 1 (by rfl) ⟨2847833, by rfl⟩ : syracuseStep 3797111 = 5695667) B5695667
theorem B1806607 : Blo 1332985 1806607 := bstep (se 1 (by rfl) ⟨1354955, by rfl⟩ : syracuseStep 1806607 = 2709911) B2709911
theorem B10129697 : Blo 1332985 10129697 := bstep (se 2 (by rfl) ⟨3798636, by rfl⟩ : syracuseStep 10129697 = 7597273) B7597273
theorem B4329787 : Blo 1332985 4329787 := bstep (se 1 (by rfl) ⟨3247340, by rfl⟩ : syracuseStep 4329787 = 6494681) B6494681
theorem B5067143 : Blo 1332985 5067143 := bstep (se 1 (by rfl) ⟨3800357, by rfl⟩ : syracuseStep 5067143 = 7600715) B7600715
theorem B3002759 : Blo 1332985 3002759 := bstep (se 1 (by rfl) ⟨2252069, by rfl⟩ : syracuseStep 3002759 = 4504139) B4504139
theorem B3002939 : Blo 1332985 3002939 := bstep (se 1 (by rfl) ⟨2252204, by rfl⟩ : syracuseStep 3002939 = 4504409) B4504409
theorem B3003065 : Blo 1332985 3003065 := bstep (se 2 (by rfl) ⟨1126149, by rfl⟩ : syracuseStep 3003065 = 2252299) B2252299
theorem B66720449 : Blo 1332985 66720449 := bstep (se 2 (by rfl) ⟨25020168, by rfl⟩ : syracuseStep 66720449 = 50040337) B50040337
theorem B2249417 : Blo 1332985 2249417 := bstep (se 2 (by rfl) ⟨843531, by rfl⟩ : syracuseStep 2249417 = 1687063) B1687063
theorem B7213769 : Blo 1332985 7213769 := bstep (se 2 (by rfl) ⟨2705163, by rfl⟩ : syracuseStep 7213769 = 5410327) B5410327
theorem B11391947 : Blo 1332985 11391947 := bstep (se 1 (by rfl) ⟨8543960, by rfl⟩ : syracuseStep 11391947 = 17087921) B17087921
theorem B3003407 : Blo 1332985 3003407 := bstep (se 1 (by rfl) ⟨2252555, by rfl⟩ : syracuseStep 3003407 = 4505111) B4505111
theorem B3003425 : Blo 1332985 3003425 := bstep (se 2 (by rfl) ⟨1126284, by rfl⟩ : syracuseStep 3003425 = 2252569) B2252569
theorem B15185069 : Blo 1332985 15185069 := bstep (se 3 (by rfl) ⟨2847200, by rfl⟩ : syracuseStep 15185069 = 5694401) B5694401
theorem B10130669 : Blo 1332985 10130669 := bstep (se 3 (by rfl) ⟨1899500, by rfl⟩ : syracuseStep 10130669 = 3799001) B3799001
theorem B4502843 : Blo 1332985 4502843 := bstep (se 1 (by rfl) ⟨3377132, by rfl⟩ : syracuseStep 4502843 = 6754265) B6754265
theorem B4109629 : Blo 1332985 4109629 := bstep (se 3 (by rfl) ⟨770555, by rfl⟩ : syracuseStep 4109629 = 1541111) B1541111
theorem B2250119 : Blo 1332985 2250119 := bstep (se 1 (by rfl) ⟨1687589, by rfl⟩ : syracuseStep 2250119 = 3375179) B3375179
theorem B2028971 : Blo 1332985 2028971 := bstep (se 1 (by rfl) ⟨1521728, by rfl⟩ : syracuseStep 2028971 = 3043457) B3043457
theorem B4871609 : Blo 1332985 4871609 := bstep (se 2 (by rfl) ⟨1826853, by rfl⟩ : syracuseStep 4871609 = 3653707) B3653707
theorem B15193817 : Blo 1332985 15193817 := bstep (se 2 (by rfl) ⟨5697681, by rfl⟩ : syracuseStep 15193817 = 11395363) B11395363
theorem B16226021 : Blo 1332985 16226021 := bstep (se 4 (by rfl) ⟨1521189, by rfl⟩ : syracuseStep 16226021 = 3042379) B3042379
theorem B36509413 : Blo 1332985 36509413 := bstep (se 4 (by rfl) ⟨3422757, by rfl⟩ : syracuseStep 36509413 = 6845515) B6845515
theorem B1603319 : Blo 1332985 1603319 := bstep (se 1 (by rfl) ⟨1202489, by rfl⟩ : syracuseStep 1603319 = 2404979) B2404979
theorem B1332999 : Blo 1332985 1332999 := bstep (se 1 (by rfl) ⟨999749, by rfl⟩ : syracuseStep 1332999 = 1999499) B1999499
theorem B1333007 : Blo 1332985 1333007 := bstep (se 1 (by rfl) ⟨999755, by rfl⟩ : syracuseStep 1333007 = 1999511) B1999511
theorem B4503329 : Blo 1332985 4503329 := bstep (se 2 (by rfl) ⟨1688748, by rfl⟩ : syracuseStep 4503329 = 3377497) B3377497
theorem B1333051 : Blo 1332985 1333051 := bstep (se 1 (by rfl) ⟨999788, by rfl⟩ : syracuseStep 1333051 = 1999577) B1999577
theorem B5699443 : Blo 1332985 5699443 := bstep (se 1 (by rfl) ⟨4274582, by rfl⟩ : syracuseStep 5699443 = 8549165) B8549165
theorem B1333127 : Blo 1332985 1333127 := bstep (se 1 (by rfl) ⟨999845, by rfl⟩ : syracuseStep 1333127 = 1999691) B1999691
theorem B7600007 : Blo 1332985 7600007 := bstep (se 1 (by rfl) ⟨5700005, by rfl⟩ : syracuseStep 7600007 = 11400011) B11400011
theorem B1333135 : Blo 1332985 1333135 := bstep (se 1 (by rfl) ⟨999851, by rfl⟩ : syracuseStep 1333135 = 1999703) B1999703
theorem B1333179 : Blo 1332985 1333179 := bstep (se 1 (by rfl) ⟨999884, by rfl⟩ : syracuseStep 1333179 = 1999769) B1999769
theorem B1333255 : Blo 1332985 1333255 := bstep (se 1 (by rfl) ⟨999941, by rfl⟩ : syracuseStep 1333255 = 1999883) B1999883
theorem B1333263 : Blo 1332985 1333263 := bstep (se 1 (by rfl) ⟨999947, by rfl⟩ : syracuseStep 1333263 = 1999895) B1999895
theorem B2250767 : Blo 1332985 2250767 := bstep (se 1 (by rfl) ⟨1688075, by rfl⟩ : syracuseStep 2250767 = 3376151) B3376151
theorem B1333307 : Blo 1332985 1333307 := bstep (se 1 (by rfl) ⟨999980, by rfl⟩ : syracuseStep 1333307 = 1999961) B1999961
theorem B7600189 : Blo 1332985 7600189 := bstep (se 3 (by rfl) ⟨1425035, by rfl⟩ : syracuseStep 7600189 = 2850071) B2850071
theorem B8108099 : Blo 1332985 8108099 := bstep (se 1 (by rfl) ⟨6081074, by rfl⟩ : syracuseStep 8108099 = 12162149) B12162149
theorem B4872311 : Blo 1332985 4872311 := bstep (se 1 (by rfl) ⟨3654233, by rfl⟩ : syracuseStep 4872311 = 7308467) B7308467
theorem B2029687 : Blo 1332985 2029687 := bstep (se 1 (by rfl) ⟨1522265, by rfl⟩ : syracuseStep 2029687 = 3044531) B3044531
theorem B1333383 : Blo 1332985 1333383 := bstep (se 1 (by rfl) ⟨1000037, by rfl⟩ : syracuseStep 1333383 = 2000075) B2000075
theorem B1333391 : Blo 1332985 1333391 := bstep (se 1 (by rfl) ⟨1000043, by rfl⟩ : syracuseStep 1333391 = 2000087) B2000087
theorem B1333435 : Blo 1332985 1333435 := bstep (se 1 (by rfl) ⟨1000076, by rfl⟩ : syracuseStep 1333435 = 2000153) B2000153
theorem B1333511 : Blo 1332985 1333511 := bstep (se 1 (by rfl) ⟨1000133, by rfl⟩ : syracuseStep 1333511 = 2000267) B2000267
theorem B1333519 : Blo 1332985 1333519 := bstep (se 1 (by rfl) ⟨1000139, by rfl⟩ : syracuseStep 1333519 = 2000279) B2000279
theorem B65804561 : Blo 1332985 65804561 := bstep (se 2 (by rfl) ⟨24676710, by rfl⟩ : syracuseStep 65804561 = 49353421) B49353421
theorem B1333563 : Blo 1332985 1333563 := bstep (se 1 (by rfl) ⟨1000172, by rfl⟩ : syracuseStep 1333563 = 2000345) B2000345
theorem B4503923 : Blo 1332985 4503923 := bstep (se 1 (by rfl) ⟨3377942, by rfl⟩ : syracuseStep 4503923 = 6755885) B6755885
theorem B1333639 : Blo 1332985 1333639 := bstep (se 1 (by rfl) ⟨1000229, by rfl⟩ : syracuseStep 1333639 = 2000459) B2000459
theorem B1333647 : Blo 1332985 1333647 := bstep (se 1 (by rfl) ⟨1000235, by rfl⟩ : syracuseStep 1333647 = 2000471) B2000471
theorem B9615761 : Blo 1332985 9615761 := bstep (se 2 (by rfl) ⟨3605910, by rfl⟩ : syracuseStep 9615761 = 7211821) B7211821
theorem B1333691 : Blo 1332985 1333691 := bstep (se 1 (by rfl) ⟨1000268, by rfl⟩ : syracuseStep 1333691 = 2000537) B2000537
theorem B1333767 : Blo 1332985 1333767 := bstep (se 1 (by rfl) ⟨1000325, by rfl⟩ : syracuseStep 1333767 = 2000651) B2000651
theorem B1333775 : Blo 1332985 1333775 := bstep (se 1 (by rfl) ⟨1000331, by rfl⟩ : syracuseStep 1333775 = 2000663) B2000663
theorem B2251307 : Blo 1332985 2251307 := bstep (se 1 (by rfl) ⟨1688480, by rfl⟩ : syracuseStep 2251307 = 3376961) B3376961
theorem B1333819 : Blo 1332985 1333819 := bstep (se 1 (by rfl) ⟨1000364, by rfl⟩ : syracuseStep 1333819 = 2000729) B2000729
theorem B3799639 : Blo 1332985 3799639 := bstep (se 1 (by rfl) ⟨2849729, by rfl⟩ : syracuseStep 3799639 = 5699459) B5699459
theorem B1333895 : Blo 1332985 1333895 := bstep (se 1 (by rfl) ⟨1000421, by rfl⟩ : syracuseStep 1333895 = 2000843) B2000843
theorem B1333903 : Blo 1332985 1333903 := bstep (se 1 (by rfl) ⟨1000427, by rfl⟩ : syracuseStep 1333903 = 2000855) B2000855
theorem B16226993 : Blo 1332985 16226993 := bstep (se 2 (by rfl) ⟨6085122, by rfl⟩ : syracuseStep 16226993 = 12170245) B12170245
theorem B1333947 : Blo 1332985 1333947 := bstep (se 1 (by rfl) ⟨1000460, by rfl⟩ : syracuseStep 1333947 = 2000921) B2000921
theorem B1334023 : Blo 1332985 1334023 := bstep (se 1 (by rfl) ⟨1000517, by rfl⟩ : syracuseStep 1334023 = 2001035) B2001035
theorem B1334031 : Blo 1332985 1334031 := bstep (se 1 (by rfl) ⟨1000523, by rfl⟩ : syracuseStep 1334031 = 2001047) B2001047
theorem B1334075 : Blo 1332985 1334075 := bstep (se 1 (by rfl) ⟨1000556, by rfl⟩ : syracuseStep 1334075 = 2001113) B2001113
theorem B3799867 : Blo 1332985 3799867 := bstep (se 1 (by rfl) ⟨2849900, by rfl⟩ : syracuseStep 3799867 = 5699801) B5699801
theorem B1334151 : Blo 1332985 1334151 := bstep (se 1 (by rfl) ⟨1000613, by rfl⟩ : syracuseStep 1334151 = 2001227) B2001227
theorem B1334159 : Blo 1332985 1334159 := bstep (se 1 (by rfl) ⟨1000619, by rfl⟩ : syracuseStep 1334159 = 2001239) B2001239
theorem B6413201 : Blo 1332985 6413201 := bstep (se 2 (by rfl) ⟨2404950, by rfl⟩ : syracuseStep 6413201 = 4809901) B4809901
theorem B6749081 : Blo 1332985 6749081 := bstep (se 2 (by rfl) ⟨2530905, by rfl⟩ : syracuseStep 6749081 = 5061811) B5061811
theorem B2251705 : Blo 1332985 2251705 := bstep (se 2 (by rfl) ⟨844389, by rfl⟩ : syracuseStep 2251705 = 1688779) B1688779
theorem B3799993 : Blo 1332985 3799993 := bstep (se 2 (by rfl) ⟨1424997, by rfl⟩ : syracuseStep 3799993 = 2849995) B2849995
theorem B1334203 : Blo 1332985 1334203 := bstep (se 1 (by rfl) ⟨1000652, by rfl⟩ : syracuseStep 1334203 = 2001305) B2001305
theorem B1334279 : Blo 1332985 1334279 := bstep (se 1 (by rfl) ⟨1000709, by rfl⟩ : syracuseStep 1334279 = 2001419) B2001419
theorem B1334287 : Blo 1332985 1334287 := bstep (se 1 (by rfl) ⟨1000715, by rfl⟩ : syracuseStep 1334287 = 2001431) B2001431
theorem B1334331 : Blo 1332985 1334331 := bstep (se 1 (by rfl) ⟨1000748, by rfl⟩ : syracuseStep 1334331 = 2001497) B2001497
theorem B14630005 : Blo 1332985 14630005 := bstep (se 5 (by rfl) ⟨685781, by rfl⟩ : syracuseStep 14630005 = 1371563) B1371563
theorem B10132613 : Blo 1332985 10132613 := bstep (se 4 (by rfl) ⟨949932, by rfl⟩ : syracuseStep 10132613 = 1899865) B1899865
theorem B1334407 : Blo 1332985 1334407 := bstep (se 1 (by rfl) ⟨1000805, by rfl⟩ : syracuseStep 1334407 = 2001611) B2001611
theorem B1334415 : Blo 1332985 1334415 := bstep (se 1 (by rfl) ⟨1000811, by rfl⟩ : syracuseStep 1334415 = 2001623) B2001623
theorem B1334459 : Blo 1332985 1334459 := bstep (se 1 (by rfl) ⟨1000844, by rfl⟩ : syracuseStep 1334459 = 2001689) B2001689
theorem B1334535 : Blo 1332985 1334535 := bstep (se 1 (by rfl) ⟨1000901, by rfl⟩ : syracuseStep 1334535 = 2001803) B2001803
theorem B1334543 : Blo 1332985 1334543 := bstep (se 1 (by rfl) ⟨1000907, by rfl⟩ : syracuseStep 1334543 = 2001815) B2001815
theorem B3374369 : Blo 1332985 3374369 := bstep (se 2 (by rfl) ⟨1265388, by rfl⟩ : syracuseStep 3374369 = 2530777) B2530777
theorem B1334587 : Blo 1332985 1334587 := bstep (se 1 (by rfl) ⟨1000940, by rfl⟩ : syracuseStep 1334587 = 2001881) B2001881
theorem B3603827 : Blo 1332985 3603827 := bstep (se 1 (by rfl) ⟨2702870, by rfl⟩ : syracuseStep 3603827 = 5405741) B5405741
theorem B7306631 : Blo 1332985 7306631 := bstep (se 1 (by rfl) ⟨5479973, by rfl⟩ : syracuseStep 7306631 = 10959947) B10959947
theorem B1334663 : Blo 1332985 1334663 := bstep (se 1 (by rfl) ⟨1000997, by rfl⟩ : syracuseStep 1334663 = 2001995) B2001995
theorem B1334671 : Blo 1332985 1334671 := bstep (se 1 (by rfl) ⟨1001003, by rfl⟩ : syracuseStep 1334671 = 2002007) B2002007
theorem B1424827 : Blo 1332985 1424827 := bstep (se 1 (by rfl) ⟨1068620, by rfl⟩ : syracuseStep 1424827 = 2137241) B2137241
theorem B1334715 : Blo 1332985 1334715 := bstep (se 1 (by rfl) ⟨1001036, by rfl⟩ : syracuseStep 1334715 = 2002073) B2002073
theorem B7593425 : Blo 1332985 7593425 := bstep (se 2 (by rfl) ⟨2847534, by rfl⟩ : syracuseStep 7593425 = 5695069) B5695069
theorem B1334791 : Blo 1332985 1334791 := bstep (se 1 (by rfl) ⟨1001093, by rfl⟩ : syracuseStep 1334791 = 2002187) B2002187
theorem B1334799 : Blo 1332985 1334799 := bstep (se 1 (by rfl) ⟨1001099, by rfl⟩ : syracuseStep 1334799 = 2002199) B2002199
theorem B1334843 : Blo 1332985 1334843 := bstep (se 1 (by rfl) ⟨1001132, by rfl⟩ : syracuseStep 1334843 = 2002265) B2002265
theorem B1687159 : Blo 1332985 1687159 := bstep (se 1 (by rfl) ⟨1265369, by rfl⟩ : syracuseStep 1687159 = 2530739) B2530739
theorem B2252407 : Blo 1332985 2252407 := bstep (se 1 (by rfl) ⟨1689305, by rfl⟩ : syracuseStep 2252407 = 3378611) B3378611
theorem B1334919 : Blo 1332985 1334919 := bstep (se 1 (by rfl) ⟨1001189, by rfl⟩ : syracuseStep 1334919 = 2002379) B2002379
theorem B1334927 : Blo 1332985 1334927 := bstep (se 1 (by rfl) ⟨1001195, by rfl⟩ : syracuseStep 1334927 = 2002391) B2002391
theorem B1334971 : Blo 1332985 1334971 := bstep (se 1 (by rfl) ⟨1001228, by rfl⟩ : syracuseStep 1334971 = 2002457) B2002457
theorem B7601921 : Blo 1332985 7601921 := bstep (se 2 (by rfl) ⟨2850720, by rfl⟩ : syracuseStep 7601921 = 5701441) B5701441
theorem B4562747 : Blo 1332985 4562747 := bstep (se 1 (by rfl) ⟨3422060, by rfl⟩ : syracuseStep 4562747 = 6844121) B6844121
theorem B2252603 : Blo 1332985 2252603 := bstep (se 1 (by rfl) ⟨1689452, by rfl⟩ : syracuseStep 2252603 = 3378905) B3378905
theorem B1900361 : Blo 1332985 1900361 := bstep (se 2 (by rfl) ⟨712635, by rfl⟩ : syracuseStep 1900361 = 1425271) B1425271
theorem B1687483 : Blo 1332985 1687483 := bstep (se 1 (by rfl) ⟨1265612, by rfl⟩ : syracuseStep 1687483 = 2531225) B2531225
theorem B6750215 : Blo 1332985 6750215 := bstep (se 1 (by rfl) ⟨5062661, by rfl⟩ : syracuseStep 6750215 = 10125323) B10125323
theorem B2850823 : Blo 1332985 2850823 := bstep (se 1 (by rfl) ⟨2138117, by rfl⟩ : syracuseStep 2850823 = 4276235) B4276235
theorem B2531407 : Blo 1332985 2531407 := bstep (se 1 (by rfl) ⟨1898555, by rfl⟩ : syracuseStep 2531407 = 3797111) B3797111
theorem B10133585 : Blo 1332985 10133585 := bstep (se 2 (by rfl) ⟨3800094, by rfl⟩ : syracuseStep 10133585 = 7600189) B7600189
theorem B36528245 : Blo 1332985 36528245 := bstep (se 5 (by rfl) ⟨1712261, by rfl⟩ : syracuseStep 36528245 = 3424523) B3424523
theorem B2408809 : Blo 1332985 2408809 := bstep (se 2 (by rfl) ⟨903303, by rfl⟩ : syracuseStep 2408809 = 1806607) B1806607
theorem B3375503 : Blo 1332985 3375503 := bstep (se 1 (by rfl) ⟨2531627, by rfl⟩ : syracuseStep 3375503 = 5063255) B5063255
theorem B1499611 : Blo 1332985 1499611 := bstep (se 1 (by rfl) ⟨1124708, by rfl⟩ : syracuseStep 1499611 = 2249417) B2249417
theorem B4809179 : Blo 1332985 4809179 := bstep (se 1 (by rfl) ⟨3606884, by rfl⟩ : syracuseStep 4809179 = 7213769) B7213769
theorem B6750701 : Blo 1332985 6750701 := bstep (se 3 (by rfl) ⟨1265756, by rfl⟩ : syracuseStep 6750701 = 2531513) B2531513
theorem B5702177 : Blo 1332985 5702177 := bstep (se 2 (by rfl) ⟨2138316, by rfl⟩ : syracuseStep 5702177 = 4276633) B4276633
theorem B7594631 : Blo 1332985 7594631 := bstep (se 1 (by rfl) ⟨5695973, by rfl⟩ : syracuseStep 7594631 = 11391947) B11391947
theorem B6849209 : Blo 1332985 6849209 := bstep (se 2 (by rfl) ⟨2568453, by rfl⟩ : syracuseStep 6849209 = 5136907) B5136907
theorem B5702329 : Blo 1332985 5702329 := bstep (se 2 (by rfl) ⟨2138373, by rfl⟩ : syracuseStep 5702329 = 4276747) B4276747
theorem B1999559 : Blo 1332985 1999559 := bstep (se 1 (by rfl) ⟨1499669, by rfl⟩ : syracuseStep 1999559 = 2999339) B2999339
theorem B3375827 : Blo 1332985 3375827 := bstep (se 1 (by rfl) ⟨2531870, by rfl⟩ : syracuseStep 3375827 = 5063741) B5063741
theorem B8553289 : Blo 1332985 8553289 := bstep (se 2 (by rfl) ⟨3207483, by rfl⟩ : syracuseStep 8553289 = 6414967) B6414967
theorem B1999721 : Blo 1332985 1999721 := bstep (se 2 (by rfl) ⟨749895, by rfl⟩ : syracuseStep 1999721 = 1499791) B1499791
theorem B5063543 : Blo 1332985 5063543 := bstep (se 1 (by rfl) ⟨3797657, by rfl⟩ : syracuseStep 5063543 = 7595315) B7595315
theorem B1500079 : Blo 1332985 1500079 := bstep (se 1 (by rfl) ⟨1125059, by rfl⟩ : syracuseStep 1500079 = 2250119) B2250119
theorem B1999799 : Blo 1332985 1999799 := bstep (se 1 (by rfl) ⟨1499849, by rfl⟩ : syracuseStep 1999799 = 2999699) B2999699
theorem B1352647 : Blo 1332985 1352647 := bstep (se 1 (by rfl) ⟨1014485, by rfl⟩ : syracuseStep 1352647 = 2028971) B2028971
theorem B1999835 : Blo 1332985 1999835 := bstep (se 1 (by rfl) ⟨1499876, by rfl⟩ : syracuseStep 1999835 = 2999753) B2999753
theorem B2999303 : Blo 1332985 2999303 := bstep (se 1 (by rfl) ⟨2249477, by rfl⟩ : syracuseStep 2999303 = 4498955) B4498955
theorem B2999375 : Blo 1332985 2999375 := bstep (se 1 (by rfl) ⟨2249531, by rfl⟩ : syracuseStep 2999375 = 4499063) B4499063
theorem B16442585 : Blo 1332985 16442585 := bstep (se 2 (by rfl) ⟨6165969, by rfl⟩ : syracuseStep 16442585 = 12331939) B12331939
theorem B6751511 : Blo 1332985 6751511 := bstep (se 1 (by rfl) ⟨5063633, by rfl⟩ : syracuseStep 6751511 = 10127267) B10127267
theorem B1500511 : Blo 1332985 1500511 := bstep (se 1 (by rfl) ⟨1125383, by rfl⟩ : syracuseStep 1500511 = 2250767) B2250767
theorem B3605903 : Blo 1332985 3605903 := bstep (se 1 (by rfl) ⟨2704427, by rfl⟩ : syracuseStep 3605903 = 5408855) B5408855
theorem B2000303 : Blo 1332985 2000303 := bstep (se 1 (by rfl) ⟨1500227, by rfl⟩ : syracuseStep 2000303 = 3000455) B3000455
theorem B1689007 : Blo 1332985 1689007 := bstep (se 1 (by rfl) ⟨1266755, by rfl⟩ : syracuseStep 1689007 = 2533511) B2533511
theorem B2704823 : Blo 1332985 2704823 := bstep (se 1 (by rfl) ⟨2028617, by rfl⟩ : syracuseStep 2704823 = 4057235) B4057235
theorem B2999771 : Blo 1332985 2999771 := bstep (se 1 (by rfl) ⟨2249828, by rfl⟩ : syracuseStep 2999771 = 4499657) B4499657
theorem B19506673 : Blo 1332985 19506673 := bstep (se 2 (by rfl) ⟨7315002, by rfl⟩ : syracuseStep 19506673 = 14630005) B14630005
theorem B2000393 : Blo 1332985 2000393 := bstep (se 2 (by rfl) ⟨750147, by rfl⟩ : syracuseStep 2000393 = 1500295) B1500295
theorem B43869707 : Blo 1332985 43869707 := bstep (se 1 (by rfl) ⟨32902280, by rfl⟩ : syracuseStep 43869707 = 65804561) B65804561
theorem B2000423 : Blo 1332985 2000423 := bstep (se 1 (by rfl) ⟨1500317, by rfl⟩ : syracuseStep 2000423 = 3000635) B3000635
theorem B26347051 : Blo 1332985 26347051 := bstep (se 1 (by rfl) ⟨19760288, by rfl⟩ : syracuseStep 26347051 = 39520577) B39520577
theorem B2000507 : Blo 1332985 2000507 := bstep (se 1 (by rfl) ⟨1500380, by rfl⟩ : syracuseStep 2000507 = 3000761) B3000761
theorem B6407819 : Blo 1332985 6407819 := bstep (se 1 (by rfl) ⟨4805864, by rfl⟩ : syracuseStep 6407819 = 9611729) B9611729
theorem B1500871 : Blo 1332985 1500871 := bstep (se 1 (by rfl) ⟨1125653, by rfl⟩ : syracuseStep 1500871 = 2251307) B2251307
theorem B2000633 : Blo 1332985 2000633 := bstep (se 2 (by rfl) ⟨750237, by rfl⟩ : syracuseStep 2000633 = 1500475) B1500475
theorem B5064515 : Blo 1332985 5064515 := bstep (se 1 (by rfl) ⟨3798386, by rfl⟩ : syracuseStep 5064515 = 7596773) B7596773
theorem B6408031 : Blo 1332985 6408031 := bstep (se 1 (by rfl) ⟨4806023, by rfl⟩ : syracuseStep 6408031 = 9612047) B9612047
theorem B2000735 : Blo 1332985 2000735 := bstep (se 1 (by rfl) ⟨1500551, by rfl⟩ : syracuseStep 2000735 = 3001103) B3001103
theorem B3376991 : Blo 1332985 3376991 := bstep (se 1 (by rfl) ⟨2532743, by rfl⟩ : syracuseStep 3376991 = 5065487) B5065487
theorem B2000747 : Blo 1332985 2000747 := bstep (se 1 (by rfl) ⟨1500560, by rfl⟩ : syracuseStep 2000747 = 3001121) B3001121
theorem B5695393 : Blo 1332985 5695393 := bstep (se 2 (by rfl) ⟨2135772, by rfl⟩ : syracuseStep 5695393 = 4271545) B4271545
theorem B3000239 : Blo 1332985 3000239 := bstep (se 1 (by rfl) ⟨2250179, by rfl⟩ : syracuseStep 3000239 = 4500359) B4500359
theorem B4499387 : Blo 1332985 4499387 := bstep (se 1 (by rfl) ⟨3374540, by rfl⟩ : syracuseStep 4499387 = 6749081) B6749081
theorem B4114451 : Blo 1332985 4114451 := bstep (se 1 (by rfl) ⟨3085838, by rfl⟩ : syracuseStep 4114451 = 6171677) B6171677
theorem B7211045 : Blo 1332985 7211045 := bstep (se 4 (by rfl) ⟨676035, by rfl⟩ : syracuseStep 7211045 = 1352071) B1352071
theorem B7596089 : Blo 1332985 7596089 := bstep (se 2 (by rfl) ⟨2848533, by rfl⟩ : syracuseStep 7596089 = 5697067) B5697067
theorem B2000975 : Blo 1332985 2000975 := bstep (se 1 (by rfl) ⟨1500731, by rfl⟩ : syracuseStep 2000975 = 3001463) B3001463
theorem B3000491 : Blo 1332985 3000491 := bstep (se 1 (by rfl) ⟨2250368, by rfl⟩ : syracuseStep 3000491 = 4500737) B4500737
theorem B2001095 : Blo 1332985 2001095 := bstep (se 1 (by rfl) ⟨1500821, by rfl⟩ : syracuseStep 2001095 = 3001643) B3001643
theorem B2402551 : Blo 1332985 2402551 := bstep (se 1 (by rfl) ⟨1801913, by rfl⟩ : syracuseStep 2402551 = 3603827) B3603827
theorem B6080779 : Blo 1332985 6080779 := bstep (se 1 (by rfl) ⟨4560584, by rfl⟩ : syracuseStep 6080779 = 9121169) B9121169
theorem B48679217 : Blo 1332985 48679217 := bstep (se 2 (by rfl) ⟨18254706, by rfl⟩ : syracuseStep 48679217 = 36509413) B36509413
theorem B2001257 : Blo 1332985 2001257 := bstep (se 2 (by rfl) ⟨750471, by rfl⟩ : syracuseStep 2001257 = 1500943) B1500943
theorem B2001335 : Blo 1332985 2001335 := bstep (se 1 (by rfl) ⟨1501001, by rfl⟩ : syracuseStep 2001335 = 3002003) B3002003
theorem B2001371 : Blo 1332985 2001371 := bstep (se 1 (by rfl) ⟨1501028, by rfl⟩ : syracuseStep 2001371 = 3002057) B3002057
theorem B3041831 : Blo 1332985 3041831 := bstep (se 1 (by rfl) ⟨2281373, by rfl⟩ : syracuseStep 3041831 = 4562747) B4562747
theorem B4393511 : Blo 1332985 4393511 := bstep (se 1 (by rfl) ⟨3295133, by rfl⟩ : syracuseStep 4393511 = 6590267) B6590267
theorem B1501735 : Blo 1332985 1501735 := bstep (se 1 (by rfl) ⟨1126301, by rfl⟩ : syracuseStep 1501735 = 2252603) B2252603
theorem B3001031 : Blo 1332985 3001031 := bstep (se 1 (by rfl) ⟨2250773, by rfl⟩ : syracuseStep 3001031 = 4501547) B4501547
theorem B3205831 : Blo 1332985 3205831 := bstep (se 1 (by rfl) ⟨2404373, by rfl⟩ : syracuseStep 3205831 = 4808747) B4808747
theorem B6753131 : Blo 1332985 6753131 := bstep (se 1 (by rfl) ⟨5064848, by rfl⟩ : syracuseStep 6753131 = 10129697) B10129697
theorem B3378095 : Blo 1332985 3378095 := bstep (se 1 (by rfl) ⟨2533571, by rfl⟩ : syracuseStep 3378095 = 5067143) B5067143
theorem B2001839 : Blo 1332985 2001839 := bstep (se 1 (by rfl) ⟨1501379, by rfl⟩ : syracuseStep 2001839 = 3002759) B3002759
theorem B2001929 : Blo 1332985 2001929 := bstep (se 2 (by rfl) ⟨750723, by rfl⟩ : syracuseStep 2001929 = 1501447) B1501447
theorem B2001959 : Blo 1332985 2001959 := bstep (se 1 (by rfl) ⟨1501469, by rfl⟩ : syracuseStep 2001959 = 3002939) B3002939
theorem B2002043 : Blo 1332985 2002043 := bstep (se 1 (by rfl) ⟨1501532, by rfl⟩ : syracuseStep 2002043 = 3003065) B3003065
theorem B2002169 : Blo 1332985 2002169 := bstep (se 2 (by rfl) ⟨750813, by rfl⟩ : syracuseStep 2002169 = 1501627) B1501627
theorem B10824997 : Blo 1332985 10824997 := bstep (se 4 (by rfl) ⟨1014843, by rfl⟩ : syracuseStep 10824997 = 2029687) B2029687
theorem B2002271 : Blo 1332985 2002271 := bstep (se 1 (by rfl) ⟨1501703, by rfl⟩ : syracuseStep 2002271 = 3003407) B3003407
theorem B2002283 : Blo 1332985 2002283 := bstep (se 1 (by rfl) ⟨1501712, by rfl⟩ : syracuseStep 2002283 = 3003425) B3003425
theorem B5066185 : Blo 1332985 5066185 := bstep (se 2 (by rfl) ⟨1899819, by rfl⟩ : syracuseStep 5066185 = 3799639) B3799639
theorem B6753779 : Blo 1332985 6753779 := bstep (se 1 (by rfl) ⟨5065334, by rfl⟩ : syracuseStep 6753779 = 10130669) B10130669
theorem B3001895 : Blo 1332985 3001895 := bstep (se 1 (by rfl) ⟨2251421, by rfl⟩ : syracuseStep 3001895 = 4502843) B4502843
theorem B7704161 : Blo 1332985 7704161 := bstep (se 2 (by rfl) ⟨2889060, by rfl⟩ : syracuseStep 7704161 = 5778121) B5778121
theorem B3247739 : Blo 1332985 3247739 := bstep (se 1 (by rfl) ⟨2435804, by rfl⟩ : syracuseStep 3247739 = 4871609) B4871609
theorem B4501115 : Blo 1332985 4501115 := bstep (se 1 (by rfl) ⟨3375836, by rfl⟩ : syracuseStep 4501115 = 6751673) B6751673
theorem B2027207 : Blo 1332985 2027207 := bstep (se 1 (by rfl) ⟨1520405, by rfl⟩ : syracuseStep 2027207 = 3040811) B3040811
theorem B5066489 : Blo 1332985 5066489 := bstep (se 2 (by rfl) ⟨1899933, by rfl⟩ : syracuseStep 5066489 = 3799867) B3799867
theorem B4501277 : Blo 1332985 4501277 := bstep (se 3 (by rfl) ⟨843989, by rfl⟩ : syracuseStep 4501277 = 1687979) B1687979
theorem B10129211 : Blo 1332985 10129211 := bstep (se 1 (by rfl) ⟨7596908, by rfl⟩ : syracuseStep 10129211 = 15193817) B15193817
theorem B10817347 : Blo 1332985 10817347 := bstep (se 1 (by rfl) ⟨8113010, by rfl⟩ : syracuseStep 10817347 = 16226021) B16226021
theorem B8548163 : Blo 1332985 8548163 := bstep (se 1 (by rfl) ⟨6411122, by rfl⟩ : syracuseStep 8548163 = 12822245) B12822245
theorem B3002219 : Blo 1332985 3002219 := bstep (se 1 (by rfl) ⟨2251664, by rfl⟩ : syracuseStep 3002219 = 4503329) B4503329
theorem B3002273 : Blo 1332985 3002273 := bstep (se 2 (by rfl) ⟨1125852, by rfl⟩ : syracuseStep 3002273 = 2251705) B2251705
theorem B5066657 : Blo 1332985 5066657 := bstep (se 2 (by rfl) ⟨1899996, by rfl⟩ : syracuseStep 5066657 = 3799993) B3799993
theorem B5066671 : Blo 1332985 5066671 := bstep (se 1 (by rfl) ⟨3800003, by rfl⟩ : syracuseStep 5066671 = 7600007) B7600007
theorem B3248207 : Blo 1332985 3248207 := bstep (se 1 (by rfl) ⟨2436155, by rfl⟩ : syracuseStep 3248207 = 4872311) B4872311
theorem B7811153 : Blo 1332985 7811153 := bstep (se 2 (by rfl) ⟨2929182, by rfl⟩ : syracuseStep 7811153 = 5858365) B5858365
theorem B3002615 : Blo 1332985 3002615 := bstep (se 1 (by rfl) ⟨2251961, by rfl⟩ : syracuseStep 3002615 = 4503923) B4503923
theorem B5697803 : Blo 1332985 5697803 := bstep (se 1 (by rfl) ⟨4273352, by rfl⟩ : syracuseStep 5697803 = 8546705) B8546705
theorem B6410507 : Blo 1332985 6410507 := bstep (se 1 (by rfl) ⟨4807880, by rfl⟩ : syracuseStep 6410507 = 9615761) B9615761
theorem B10817995 : Blo 1332985 10817995 := bstep (se 1 (by rfl) ⟨8113496, by rfl⟩ : syracuseStep 10817995 = 16226993) B16226993
theorem B19231181 : Blo 1332985 19231181 := bstep (se 3 (by rfl) ⟨3605846, by rfl⟩ : syracuseStep 19231181 = 7211693) B7211693
theorem B4501979 : Blo 1332985 4501979 := bstep (se 1 (by rfl) ⟨3376484, by rfl⟩ : syracuseStep 4501979 = 6752969) B6752969
theorem B3797543 : Blo 1332985 3797543 := bstep (se 1 (by rfl) ⟨2848157, by rfl⟩ : syracuseStep 3797543 = 5696315) B5696315
theorem B6755075 : Blo 1332985 6755075 := bstep (se 1 (by rfl) ⟨5066306, by rfl⟩ : syracuseStep 6755075 = 10132613) B10132613
theorem B2249545 : Blo 1332985 2249545 := bstep (se 2 (by rfl) ⟨843579, by rfl⟩ : syracuseStep 2249545 = 1687159) B1687159
theorem B7213897 : Blo 1332985 7213897 := bstep (se 2 (by rfl) ⟨2705211, by rfl⟩ : syracuseStep 7213897 = 5410423) B5410423
theorem B3003209 : Blo 1332985 3003209 := bstep (se 2 (by rfl) ⟨1126203, by rfl⟩ : syracuseStep 3003209 = 2252407) B2252407
theorem B2249579 : Blo 1332985 2249579 := bstep (se 1 (by rfl) ⟨1687184, by rfl⟩ : syracuseStep 2249579 = 3374369) B3374369
theorem B5067629 : Blo 1332985 5067629 := bstep (se 3 (by rfl) ⟨950180, by rfl⟩ : syracuseStep 5067629 = 1900361) B1900361
theorem B4871087 : Blo 1332985 4871087 := bstep (se 1 (by rfl) ⟨3653315, by rfl⟩ : syracuseStep 4871087 = 7306631) B7306631
theorem B2028667 : Blo 1332985 2028667 := bstep (se 1 (by rfl) ⟨1521500, by rfl⟩ : syracuseStep 2028667 = 3043001) B3043001
theorem B4502681 : Blo 1332985 4502681 := bstep (se 2 (by rfl) ⟨1688505, by rfl⟩ : syracuseStep 4502681 = 3377011) B3377011
theorem B7599257 : Blo 1332985 7599257 := bstep (se 2 (by rfl) ⟨2849721, by rfl⟩ : syracuseStep 7599257 = 5699443) B5699443
theorem B5067947 : Blo 1332985 5067947 := bstep (se 1 (by rfl) ⟨3800960, by rfl⟩ : syracuseStep 5067947 = 7601921) B7601921
theorem B2249977 : Blo 1332985 2249977 := bstep (se 2 (by rfl) ⟨843741, by rfl⟩ : syracuseStep 2249977 = 1687483) B1687483
theorem B77960657 : Blo 1332985 77960657 := bstep (se 2 (by rfl) ⟨29235246, by rfl⟩ : syracuseStep 77960657 = 58470493) B58470493
theorem B2250247 : Blo 1332985 2250247 := bstep (se 1 (by rfl) ⟨1687685, by rfl⟩ : syracuseStep 2250247 = 3375371) B3375371
theorem B2283179 : Blo 1332985 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B62404337 : Blo 1332985 62404337 := bstep (se 2 (by rfl) ⟨23401626, by rfl⟩ : syracuseStep 62404337 = 46803253) B46803253
theorem B5773049 : Blo 1332985 5773049 := bstep (se 2 (by rfl) ⟨2164893, by rfl⟩ : syracuseStep 5773049 = 4329787) B4329787
theorem B36484901 : Blo 1332985 36484901 := bstep (se 4 (by rfl) ⟨3420459, by rfl⟩ : syracuseStep 36484901 = 6840919) B6840919
theorem B1333031 : Blo 1332985 1333031 := bstep (se 1 (by rfl) ⟨999773, by rfl⟩ : syracuseStep 1333031 = 1999547) B1999547
theorem B44480299 : Blo 1332985 44480299 := bstep (se 1 (by rfl) ⟨33360224, by rfl⟩ : syracuseStep 44480299 = 66720449) B66720449
theorem B1333071 : Blo 1332985 1333071 := bstep (se 1 (by rfl) ⟨999803, by rfl⟩ : syracuseStep 1333071 = 1999607) B1999607
theorem B1333087 : Blo 1332985 1333087 := bstep (se 1 (by rfl) ⟨999815, by rfl⟩ : syracuseStep 1333087 = 1999631) B1999631
theorem B1333115 : Blo 1332985 1333115 := bstep (se 1 (by rfl) ⟨999836, by rfl⟩ : syracuseStep 1333115 = 1999673) B1999673
theorem B1333167 : Blo 1332985 1333167 := bstep (se 1 (by rfl) ⟨999875, by rfl⟩ : syracuseStep 1333167 = 1999751) B1999751
theorem B2250679 : Blo 1332985 2250679 := bstep (se 1 (by rfl) ⟨1688009, by rfl⟩ : syracuseStep 2250679 = 3376019) B3376019
theorem B1333191 : Blo 1332985 1333191 := bstep (se 1 (by rfl) ⟨999893, by rfl⟩ : syracuseStep 1333191 = 1999787) B1999787
theorem B1333211 : Blo 1332985 1333211 := bstep (se 1 (by rfl) ⟨999908, by rfl⟩ : syracuseStep 1333211 = 1999817) B1999817
theorem B1333287 : Blo 1332985 1333287 := bstep (se 1 (by rfl) ⟨999965, by rfl⟩ : syracuseStep 1333287 = 1999931) B1999931
theorem B3848249 : Blo 1332985 3848249 := bstep (se 2 (by rfl) ⟨1443093, by rfl⟩ : syracuseStep 3848249 = 2886187) B2886187
theorem B1333327 : Blo 1332985 1333327 := bstep (se 1 (by rfl) ⟨999995, by rfl⟩ : syracuseStep 1333327 = 1999991) B1999991
theorem B1333343 : Blo 1332985 1333343 := bstep (se 1 (by rfl) ⟨1000007, by rfl⟩ : syracuseStep 1333343 = 2000015) B2000015
theorem B10123379 : Blo 1332985 10123379 := bstep (se 1 (by rfl) ⟨7592534, by rfl⟩ : syracuseStep 10123379 = 15185069) B15185069
theorem B1333371 : Blo 1332985 1333371 := bstep (se 1 (by rfl) ⟨1000028, by rfl⟩ : syracuseStep 1333371 = 2000057) B2000057
theorem B2250875 : Blo 1332985 2250875 := bstep (se 1 (by rfl) ⟨1688156, by rfl⟩ : syracuseStep 2250875 = 3376313) B3376313
theorem B1333423 : Blo 1332985 1333423 := bstep (se 1 (by rfl) ⟨1000067, by rfl⟩ : syracuseStep 1333423 = 2000135) B2000135
theorem B1333447 : Blo 1332985 1333447 := bstep (se 1 (by rfl) ⟨1000085, by rfl⟩ : syracuseStep 1333447 = 2000171) B2000171
theorem B1333467 : Blo 1332985 1333467 := bstep (se 1 (by rfl) ⟨1000100, by rfl⟩ : syracuseStep 1333467 = 2000201) B2000201
theorem B1333543 : Blo 1332985 1333543 := bstep (se 1 (by rfl) ⟨1000157, by rfl⟩ : syracuseStep 1333543 = 2000315) B2000315
theorem B4503869 : Blo 1332985 4503869 := bstep (se 3 (by rfl) ⟨844475, by rfl⟩ : syracuseStep 4503869 = 1688951) B1688951
theorem B1333583 : Blo 1332985 1333583 := bstep (se 1 (by rfl) ⟨1000187, by rfl⟩ : syracuseStep 1333583 = 2000375) B2000375
theorem B6756695 : Blo 1332985 6756695 := bstep (se 1 (by rfl) ⟨5067521, by rfl⟩ : syracuseStep 6756695 = 10135043) B10135043
theorem B1333599 : Blo 1332985 1333599 := bstep (se 1 (by rfl) ⟨1000199, by rfl⟩ : syracuseStep 1333599 = 2000399) B2000399
theorem B1333627 : Blo 1332985 1333627 := bstep (se 1 (by rfl) ⟨1000220, by rfl⟩ : syracuseStep 1333627 = 2000441) B2000441
theorem B1333679 : Blo 1332985 1333679 := bstep (se 1 (by rfl) ⟨1000259, by rfl⟩ : syracuseStep 1333679 = 2000519) B2000519
theorem B2136503 : Blo 1332985 2136503 := bstep (se 1 (by rfl) ⟨1602377, by rfl⟩ : syracuseStep 2136503 = 3204755) B3204755
theorem B1333703 : Blo 1332985 1333703 := bstep (se 1 (by rfl) ⟨1000277, by rfl⟩ : syracuseStep 1333703 = 2000555) B2000555
theorem B1333723 : Blo 1332985 1333723 := bstep (se 1 (by rfl) ⟨1000292, by rfl⟩ : syracuseStep 1333723 = 2000585) B2000585
theorem B2251273 : Blo 1332985 2251273 := bstep (se 2 (by rfl) ⟨844227, by rfl⟩ : syracuseStep 2251273 = 1688455) B1688455
theorem B1333799 : Blo 1332985 1333799 := bstep (se 1 (by rfl) ⟨1000349, by rfl⟩ : syracuseStep 1333799 = 2000699) B2000699
theorem B1333839 : Blo 1332985 1333839 := bstep (se 1 (by rfl) ⟨1000379, by rfl⟩ : syracuseStep 1333839 = 2000759) B2000759
theorem B1333855 : Blo 1332985 1333855 := bstep (se 1 (by rfl) ⟨1000391, by rfl⟩ : syracuseStep 1333855 = 2000783) B2000783
theorem B1333883 : Blo 1332985 1333883 := bstep (se 1 (by rfl) ⟨1000412, by rfl⟩ : syracuseStep 1333883 = 2000825) B2000825
theorem B13163143 : Blo 1332985 13163143 := bstep (se 1 (by rfl) ⟨9872357, by rfl⟩ : syracuseStep 13163143 = 19744715) B19744715
theorem B2251435 : Blo 1332985 2251435 := bstep (se 1 (by rfl) ⟨1688576, by rfl⟩ : syracuseStep 2251435 = 3377153) B3377153
theorem B1333935 : Blo 1332985 1333935 := bstep (se 1 (by rfl) ⟨1000451, by rfl⟩ : syracuseStep 1333935 = 2000903) B2000903
theorem B10959545 : Blo 1332985 10959545 := bstep (se 2 (by rfl) ⟨4109829, by rfl⟩ : syracuseStep 10959545 = 8219659) B8219659
theorem B1333959 : Blo 1332985 1333959 := bstep (se 1 (by rfl) ⟨1000469, by rfl⟩ : syracuseStep 1333959 = 2000939) B2000939
theorem B5405399 : Blo 1332985 5405399 := bstep (se 1 (by rfl) ⟨4054049, by rfl⟩ : syracuseStep 5405399 = 8108099) B8108099
theorem B1333979 : Blo 1332985 1333979 := bstep (se 1 (by rfl) ⟨1000484, by rfl⟩ : syracuseStep 1333979 = 2000969) B2000969
theorem B1334055 : Blo 1332985 1334055 := bstep (se 1 (by rfl) ⟨1000541, by rfl⟩ : syracuseStep 1334055 = 2001083) B2001083
theorem B1334095 : Blo 1332985 1334095 := bstep (se 1 (by rfl) ⟨1000571, by rfl⟩ : syracuseStep 1334095 = 2001143) B2001143
theorem B1334111 : Blo 1332985 1334111 := bstep (se 1 (by rfl) ⟨1000583, by rfl⟩ : syracuseStep 1334111 = 2001167) B2001167
theorem B1334139 : Blo 1332985 1334139 := bstep (se 1 (by rfl) ⟨1000604, by rfl⟩ : syracuseStep 1334139 = 2001209) B2001209
theorem B1334191 : Blo 1332985 1334191 := bstep (se 1 (by rfl) ⟨1000643, by rfl⟩ : syracuseStep 1334191 = 2001287) B2001287
theorem B1334215 : Blo 1332985 1334215 := bstep (se 1 (by rfl) ⟨1000661, by rfl⟩ : syracuseStep 1334215 = 2001323) B2001323
theorem B1334235 : Blo 1332985 1334235 := bstep (se 1 (by rfl) ⟨1000676, by rfl⟩ : syracuseStep 1334235 = 2001353) B2001353
theorem B2251739 : Blo 1332985 2251739 := bstep (se 1 (by rfl) ⟨1688804, by rfl⟩ : syracuseStep 2251739 = 3377609) B3377609
theorem B2005979 : Blo 1332985 2005979 := bstep (se 1 (by rfl) ⟨1504484, by rfl⟩ : syracuseStep 2005979 = 3008969) B3008969
theorem B1334311 : Blo 1332985 1334311 := bstep (se 1 (by rfl) ⟨1000733, by rfl⟩ : syracuseStep 1334311 = 2001467) B2001467
theorem B1334351 : Blo 1332985 1334351 := bstep (se 1 (by rfl) ⟨1000763, by rfl⟩ : syracuseStep 1334351 = 2001527) B2001527
theorem B5479505 : Blo 1332985 5479505 := bstep (se 2 (by rfl) ⟨2054814, by rfl⟩ : syracuseStep 5479505 = 4109629) B4109629
theorem B1334367 : Blo 1332985 1334367 := bstep (se 1 (by rfl) ⟨1000775, by rfl⟩ : syracuseStep 1334367 = 2001551) B2001551
theorem B1334395 : Blo 1332985 1334395 := bstep (se 1 (by rfl) ⟨1000796, by rfl⟩ : syracuseStep 1334395 = 2001593) B2001593
theorem B4504733 : Blo 1332985 4504733 := bstep (se 3 (by rfl) ⟨844637, by rfl⟩ : syracuseStep 4504733 = 1689275) B1689275
theorem B1334447 : Blo 1332985 1334447 := bstep (se 1 (by rfl) ⟨1000835, by rfl⟩ : syracuseStep 1334447 = 2001671) B2001671
theorem B1334471 : Blo 1332985 1334471 := bstep (se 1 (by rfl) ⟨1000853, by rfl⟩ : syracuseStep 1334471 = 2001707) B2001707
theorem B2251975 : Blo 1332985 2251975 := bstep (se 1 (by rfl) ⟨1688981, by rfl⟩ : syracuseStep 2251975 = 3377963) B3377963
theorem B1334491 : Blo 1332985 1334491 := bstep (se 1 (by rfl) ⟨1000868, by rfl⟩ : syracuseStep 1334491 = 2001737) B2001737
theorem B1899769 : Blo 1332985 1899769 := bstep (se 2 (by rfl) ⟨712413, by rfl⟩ : syracuseStep 1899769 = 1424827) B1424827
theorem B4275467 : Blo 1332985 4275467 := bstep (se 1 (by rfl) ⟨3206600, by rfl⟩ : syracuseStep 4275467 = 6413201) B6413201
theorem B1334567 : Blo 1332985 1334567 := bstep (se 1 (by rfl) ⟨1000925, by rfl⟩ : syracuseStep 1334567 = 2001851) B2001851
theorem B4275517 : Blo 1332985 4275517 := bstep (se 3 (by rfl) ⟨801659, by rfl⟩ : syracuseStep 4275517 = 1603319) B1603319
theorem B1334607 : Blo 1332985 1334607 := bstep (se 1 (by rfl) ⟨1000955, by rfl⟩ : syracuseStep 1334607 = 2001911) B2001911
theorem B1924447 : Blo 1332985 1924447 := bstep (se 1 (by rfl) ⟨1443335, by rfl⟩ : syracuseStep 1924447 = 2886671) B2886671
theorem B1334623 : Blo 1332985 1334623 := bstep (se 1 (by rfl) ⟨1000967, by rfl⟩ : syracuseStep 1334623 = 2001935) B2001935
theorem B2252137 : Blo 1332985 2252137 := bstep (se 2 (by rfl) ⟨844551, by rfl⟩ : syracuseStep 2252137 = 1689103) B1689103
theorem B1334651 : Blo 1332985 1334651 := bstep (se 1 (by rfl) ⟨1000988, by rfl⟩ : syracuseStep 1334651 = 2001977) B2001977
theorem B1334703 : Blo 1332985 1334703 := bstep (se 1 (by rfl) ⟨1001027, by rfl⟩ : syracuseStep 1334703 = 2002055) B2002055
theorem B1334727 : Blo 1332985 1334727 := bstep (se 1 (by rfl) ⟨1001045, by rfl⟩ : syracuseStep 1334727 = 2002091) B2002091
theorem B1334747 : Blo 1332985 1334747 := bstep (se 1 (by rfl) ⟨1001060, by rfl⟩ : syracuseStep 1334747 = 2002121) B2002121
theorem B1334823 : Blo 1332985 1334823 := bstep (se 1 (by rfl) ⟨1001117, by rfl⟩ : syracuseStep 1334823 = 2002235) B2002235
theorem B1334863 : Blo 1332985 1334863 := bstep (se 1 (by rfl) ⟨1001147, by rfl⟩ : syracuseStep 1334863 = 2002295) B2002295
theorem B1334879 : Blo 1332985 1334879 := bstep (se 1 (by rfl) ⟨1001159, by rfl⟩ : syracuseStep 1334879 = 2002319) B2002319
theorem B1334907 : Blo 1332985 1334907 := bstep (se 1 (by rfl) ⟨1001180, by rfl⟩ : syracuseStep 1334907 = 2002361) B2002361
theorem B5062283 : Blo 1332985 5062283 := bstep (se 1 (by rfl) ⟨3796712, by rfl⟩ : syracuseStep 5062283 = 7593425) B7593425
theorem B1334959 : Blo 1332985 1334959 := bstep (se 1 (by rfl) ⟨1001219, by rfl⟩ : syracuseStep 1334959 = 2002439) B2002439
theorem B4505273 : Blo 1332985 4505273 := bstep (se 2 (by rfl) ⟨1689477, by rfl⟩ : syracuseStep 4505273 = 3378955) B3378955
theorem B1334983 : Blo 1332985 1334983 := bstep (se 1 (by rfl) ⟨1001237, by rfl⟩ : syracuseStep 1334983 = 2002475) B2002475
theorem B2531027 : Blo 1332985 2531027 := bstep (se 1 (by rfl) ⟨1898270, by rfl⟩ : syracuseStep 2531027 = 3796541) B3796541
theorem B2531179 : Blo 1332985 2531179 := bstep (se 1 (by rfl) ⟨1898384, by rfl⟩ : syracuseStep 2531179 = 3796769) B3796769
theorem B2252731 : Blo 1332985 2252731 := bstep (se 1 (by rfl) ⟨1689548, by rfl⟩ : syracuseStep 2252731 = 3379097) B3379097
theorem B3801097 : Blo 1332985 3801097 := bstep (se 2 (by rfl) ⟨1425411, by rfl⟩ : syracuseStep 3801097 = 2850823) B2850823
theorem B3375209 : Blo 1332985 3375209 := bstep (se 2 (by rfl) ⟨1265703, by rfl⟩ : syracuseStep 3375209 = 2531407) B2531407
theorem B140517605 : Blo 1332985 140517605 := bstep (se 4 (by rfl) ⟨13173525, by rfl⟩ : syracuseStep 140517605 = 26347051) B26347051
theorem B12820787 : Blo 1332985 12820787 := bstep (se 1 (by rfl) ⟨9615590, by rfl⟩ : syracuseStep 12820787 = 19231181) B19231181
theorem B3203401 : Blo 1332985 3203401 := bstep (se 2 (by rfl) ⟨1201275, by rfl⟩ : syracuseStep 3203401 = 2402551) B2402551
theorem B3801451 : Blo 1332985 3801451 := bstep (se 1 (by rfl) ⟨2851088, by rfl⟩ : syracuseStep 3801451 = 5702177) B5702177
theorem B5063087 : Blo 1332985 5063087 := bstep (se 1 (by rfl) ⟨3797315, by rfl⟩ : syracuseStep 5063087 = 7594631) B7594631
theorem B3211745 : Blo 1332985 3211745 := bstep (se 2 (by rfl) ⟨1204404, by rfl⟩ : syracuseStep 3211745 = 2408809) B2408809
theorem B1499719 : Blo 1332985 1499719 := bstep (se 1 (by rfl) ⟨1124789, by rfl⟩ : syracuseStep 1499719 = 2249579) B2249579
theorem B3375695 : Blo 1332985 3375695 := bstep (se 1 (by rfl) ⟨2531771, by rfl⟩ : syracuseStep 3375695 = 5063543) B5063543
theorem B1999481 : Blo 1332985 1999481 := bstep (se 2 (by rfl) ⟨749805, by rfl⟩ : syracuseStep 1999481 = 1499611) B1499611
theorem B1999535 : Blo 1332985 1999535 := bstep (se 1 (by rfl) ⟨1499651, by rfl⟩ : syracuseStep 1999535 = 2999303) B2999303
theorem B1999583 : Blo 1332985 1999583 := bstep (se 1 (by rfl) ⟨1499687, by rfl⟩ : syracuseStep 1999583 = 2999375) B2999375
theorem B10961723 : Blo 1332985 10961723 := bstep (se 1 (by rfl) ⟨8221292, by rfl⟩ : syracuseStep 10961723 = 16442585) B16442585
theorem B7603105 : Blo 1332985 7603105 := bstep (se 2 (by rfl) ⟨2851164, by rfl⟩ : syracuseStep 7603105 = 5702329) B5702329
theorem B1803215 : Blo 1332985 1803215 := bstep (se 1 (by rfl) ⟨1352411, by rfl⟩ : syracuseStep 1803215 = 2704823) B2704823
theorem B1999847 : Blo 1332985 1999847 := bstep (se 1 (by rfl) ⟨1499885, by rfl⟩ : syracuseStep 1999847 = 2999771) B2999771
theorem B29246471 : Blo 1332985 29246471 := bstep (se 1 (by rfl) ⟨21934853, by rfl⟩ : syracuseStep 29246471 = 43869707) B43869707
theorem B2999393 : Blo 1332985 2999393 := bstep (se 2 (by rfl) ⟨1124772, by rfl⟩ : syracuseStep 2999393 = 2249545) B2249545
theorem B9618529 : Blo 1332985 9618529 := bstep (se 2 (by rfl) ⟨3606948, by rfl⟩ : syracuseStep 9618529 = 7213897) B7213897
theorem B11404385 : Blo 1332985 11404385 := bstep (se 2 (by rfl) ⟨4276644, by rfl⟩ : syracuseStep 11404385 = 8553289) B8553289
theorem B24323267 : Blo 1332985 24323267 := bstep (se 1 (by rfl) ⟨18242450, by rfl⟩ : syracuseStep 24323267 = 36484901) B36484901
theorem B3376343 : Blo 1332985 3376343 := bstep (se 1 (by rfl) ⟨2532257, by rfl⟩ : syracuseStep 3376343 = 5064515) B5064515
theorem B2000105 : Blo 1332985 2000105 := bstep (se 2 (by rfl) ⟨750039, by rfl⟩ : syracuseStep 2000105 = 1500079) B1500079
theorem B1803529 : Blo 1332985 1803529 := bstep (se 2 (by rfl) ⟨676323, by rfl⟩ : syracuseStep 1803529 = 1352647) B1352647
theorem B2000159 : Blo 1332985 2000159 := bstep (se 1 (by rfl) ⟨1500119, by rfl⟩ : syracuseStep 2000159 = 3000239) B3000239
theorem B2999591 : Blo 1332985 2999591 := bstep (se 1 (by rfl) ⟨2249693, by rfl⟩ : syracuseStep 2999591 = 4499387) B4499387
theorem B5064059 : Blo 1332985 5064059 := bstep (se 1 (by rfl) ⟨3798044, by rfl⟩ : syracuseStep 5064059 = 7596089) B7596089
theorem B1500583 : Blo 1332985 1500583 := bstep (se 1 (by rfl) ⟨1125437, by rfl⟩ : syracuseStep 1500583 = 2250875) B2250875
theorem B10126781 : Blo 1332985 10126781 := bstep (se 3 (by rfl) ⟨1898771, by rfl⟩ : syracuseStep 10126781 = 3797543) B3797543
theorem B8111549 : Blo 1332985 8111549 := bstep (se 3 (by rfl) ⟨1520915, by rfl⟩ : syracuseStep 8111549 = 3041831) B3041831
theorem B2000327 : Blo 1332985 2000327 := bstep (se 1 (by rfl) ⟨1500245, by rfl⟩ : syracuseStep 2000327 = 3000491) B3000491
theorem B2704889 : Blo 1332985 2704889 := bstep (se 2 (by rfl) ⟨1014333, by rfl⟩ : syracuseStep 2704889 = 2028667) B2028667
theorem B2999969 : Blo 1332985 2999969 := bstep (se 2 (by rfl) ⟨1124988, by rfl⟩ : syracuseStep 2999969 = 2249977) B2249977
theorem B2533025 : Blo 1332985 2533025 := bstep (se 2 (by rfl) ⟨949884, by rfl⟩ : syracuseStep 2533025 = 1899769) B1899769
theorem B2565929 : Blo 1332985 2565929 := bstep (se 2 (by rfl) ⟨962223, by rfl⟩ : syracuseStep 2565929 = 1924447) B1924447
theorem B2000681 : Blo 1332985 2000681 := bstep (se 2 (by rfl) ⟨750255, by rfl⟩ : syracuseStep 2000681 = 1500511) B1500511
theorem B2000687 : Blo 1332985 2000687 := bstep (se 1 (by rfl) ⟨1500515, by rfl⟩ : syracuseStep 2000687 = 3001031) B3001031
theorem B1501159 : Blo 1332985 1501159 := bstep (se 1 (by rfl) ⟨1125869, by rfl⟩ : syracuseStep 1501159 = 2251739) B2251739
theorem B3000329 : Blo 1332985 3000329 := bstep (se 2 (by rfl) ⟨1125123, by rfl⟩ : syracuseStep 3000329 = 2250247) B2250247
theorem B2001161 : Blo 1332985 2001161 := bstep (se 2 (by rfl) ⟨750435, by rfl⟩ : syracuseStep 2001161 = 1500871) B1500871
theorem B2001263 : Blo 1332985 2001263 := bstep (se 1 (by rfl) ⟨1500947, by rfl⟩ : syracuseStep 2001263 = 3001895) B3001895
theorem B2165159 : Blo 1332985 2165159 := bstep (se 1 (by rfl) ⟨1623869, by rfl⟩ : syracuseStep 2165159 = 3247739) B3247739
theorem B3000743 : Blo 1332985 3000743 := bstep (se 1 (by rfl) ⟨2250557, by rfl⟩ : syracuseStep 3000743 = 4501115) B4501115
theorem B3377659 : Blo 1332985 3377659 := bstep (se 1 (by rfl) ⟨2533244, by rfl⟩ : syracuseStep 3377659 = 5066489) B5066489
theorem B3000851 : Blo 1332985 3000851 := bstep (se 1 (by rfl) ⟨2250638, by rfl⟩ : syracuseStep 3000851 = 4501277) B4501277
theorem B6752807 : Blo 1332985 6752807 := bstep (se 1 (by rfl) ⟨5064605, by rfl⟩ : syracuseStep 6752807 = 10129211) B10129211
theorem B2001479 : Blo 1332985 2001479 := bstep (se 1 (by rfl) ⟨1501109, by rfl⟩ : syracuseStep 2001479 = 3002219) B3002219
theorem B3000905 : Blo 1332985 3000905 := bstep (se 2 (by rfl) ⟨1125339, by rfl⟩ : syracuseStep 3000905 = 2250679) B2250679
theorem B2001515 : Blo 1332985 2001515 := bstep (se 1 (by rfl) ⟨1501136, by rfl⟩ : syracuseStep 2001515 = 3002273) B3002273
theorem B3377771 : Blo 1332985 3377771 := bstep (se 1 (by rfl) ⟨2533328, by rfl⟩ : syracuseStep 3377771 = 5066657) B5066657
theorem B4500143 : Blo 1332985 4500143 := bstep (se 1 (by rfl) ⟨3375107, by rfl⟩ : syracuseStep 4500143 = 6750215) B6750215
theorem B2165471 : Blo 1332985 2165471 := bstep (se 1 (by rfl) ⟨1624103, by rfl⟩ : syracuseStep 2165471 = 3248207) B3248207
theorem B2001743 : Blo 1332985 2001743 := bstep (se 1 (by rfl) ⟨1501307, by rfl⟩ : syracuseStep 2001743 = 3002615) B3002615
theorem B3001319 : Blo 1332985 3001319 := bstep (se 1 (by rfl) ⟨2250989, by rfl⟩ : syracuseStep 3001319 = 4501979) B4501979
theorem B4500467 : Blo 1332985 4500467 := bstep (se 1 (by rfl) ⟨3375350, by rfl⟩ : syracuseStep 4500467 = 6750701) B6750701
theorem B4566139 : Blo 1332985 4566139 := bstep (se 1 (by rfl) ⟨3424604, by rfl⟩ : syracuseStep 4566139 = 6849209) B6849209
theorem B2002139 : Blo 1332985 2002139 := bstep (se 1 (by rfl) ⟨1501604, by rfl⟩ : syracuseStep 2002139 = 3003209) B3003209
theorem B3378419 : Blo 1332985 3378419 := bstep (se 1 (by rfl) ⟨2533814, by rfl⟩ : syracuseStep 3378419 = 5067629) B5067629
theorem B3247391 : Blo 1332985 3247391 := bstep (se 1 (by rfl) ⟨2435543, by rfl⟩ : syracuseStep 3247391 = 4871087) B4871087
theorem B3001697 : Blo 1332985 3001697 := bstep (se 2 (by rfl) ⟨1125636, by rfl⟩ : syracuseStep 3001697 = 2251273) B2251273
theorem B2002313 : Blo 1332985 2002313 := bstep (se 2 (by rfl) ⟨750867, by rfl⟩ : syracuseStep 2002313 = 1501735) B1501735
theorem B3001787 : Blo 1332985 3001787 := bstep (se 1 (by rfl) ⟨2251340, by rfl⟩ : syracuseStep 3001787 = 4502681) B4502681
theorem B5066171 : Blo 1332985 5066171 := bstep (se 1 (by rfl) ⟨3799628, by rfl⟩ : syracuseStep 5066171 = 7599257) B7599257
theorem B3378631 : Blo 1332985 3378631 := bstep (se 1 (by rfl) ⟨2533973, by rfl⟩ : syracuseStep 3378631 = 5067947) B5067947
theorem B17550857 : Blo 1332985 17550857 := bstep (se 2 (by rfl) ⟨6581571, by rfl⟩ : syracuseStep 17550857 = 13163143) B13163143
theorem B4501007 : Blo 1332985 4501007 := bstep (se 1 (by rfl) ⟨3375755, by rfl⟩ : syracuseStep 4501007 = 6751511) B6751511
theorem B3001913 : Blo 1332985 3001913 := bstep (se 2 (by rfl) ⟨1125717, by rfl⟩ : syracuseStep 3001913 = 2251435) B2251435
theorem B2403935 : Blo 1332985 2403935 := bstep (se 1 (by rfl) ⟨1802951, by rfl⟩ : syracuseStep 2403935 = 3605903) B3605903
theorem B51973771 : Blo 1332985 51973771 := bstep (se 1 (by rfl) ⟨38980328, by rfl⟩ : syracuseStep 51973771 = 77960657) B77960657
theorem B4271879 : Blo 1332985 4271879 := bstep (se 1 (by rfl) ⟨3203909, by rfl⟩ : syracuseStep 4271879 = 6407819) B6407819
theorem B5697341 : Blo 1332985 5697341 := bstep (se 3 (by rfl) ⟨1068251, by rfl⟩ : syracuseStep 5697341 = 2136503) B2136503
theorem B41602891 : Blo 1332985 41602891 := bstep (se 1 (by rfl) ⟨31202168, by rfl⟩ : syracuseStep 41602891 = 62404337) B62404337
theorem B12824477 : Blo 1332985 12824477 := bstep (se 3 (by rfl) ⟨2404589, by rfl⟩ : syracuseStep 12824477 = 4809179) B4809179
theorem B32452811 : Blo 1332985 32452811 := bstep (se 1 (by rfl) ⟨24339608, by rfl⟩ : syracuseStep 32452811 = 48679217) B48679217
theorem B3002579 : Blo 1332985 3002579 := bstep (se 1 (by rfl) ⟨2251934, by rfl⟩ : syracuseStep 3002579 = 4503869) B4503869
theorem B3002633 : Blo 1332985 3002633 := bstep (se 2 (by rfl) ⟨1125987, by rfl⟩ : syracuseStep 3002633 = 2251975) B2251975
theorem B2929007 : Blo 1332985 2929007 := bstep (se 1 (by rfl) ⟨2196755, by rfl⟩ : syracuseStep 2929007 = 4393511) B4393511
theorem B3002849 : Blo 1332985 3002849 := bstep (se 2 (by rfl) ⟨1126068, by rfl⟩ : syracuseStep 3002849 = 2252137) B2252137
theorem B4502087 : Blo 1332985 4502087 := bstep (se 1 (by rfl) ⟨3376565, by rfl⟩ : syracuseStep 4502087 = 6753131) B6753131
theorem B6754913 : Blo 1332985 6754913 := bstep (se 2 (by rfl) ⟨2533092, by rfl⟩ : syracuseStep 6754913 = 5066185) B5066185
theorem B3003155 : Blo 1332985 3003155 := bstep (se 1 (by rfl) ⟨2252366, by rfl⟩ : syracuseStep 3003155 = 4504733) B4504733
theorem B4502519 : Blo 1332985 4502519 := bstep (se 1 (by rfl) ⟨3376889, by rfl⟩ : syracuseStep 4502519 = 6753779) B6753779
theorem B59307065 : Blo 1332985 59307065 := bstep (se 2 (by rfl) ⟨22240149, by rfl⟩ : syracuseStep 59307065 = 44480299) B44480299
theorem B14423129 : Blo 1332985 14423129 := bstep (se 2 (by rfl) ⟨5408673, by rfl⟩ : syracuseStep 14423129 = 10817347) B10817347
theorem B3003515 : Blo 1332985 3003515 := bstep (se 1 (by rfl) ⟨2252636, by rfl⟩ : syracuseStep 3003515 = 4505273) B4505273
theorem B5698775 : Blo 1332985 5698775 := bstep (se 1 (by rfl) ⟨4274081, by rfl⟩ : syracuseStep 5698775 = 8548163) B8548163
theorem B6755561 : Blo 1332985 6755561 := bstep (se 2 (by rfl) ⟨2533335, by rfl⟩ : syracuseStep 6755561 = 5066671) B5066671
theorem B3003641 : Blo 1332985 3003641 := bstep (se 2 (by rfl) ⟨1126365, by rfl⟩ : syracuseStep 3003641 = 2252731) B2252731
theorem B6755723 : Blo 1332985 6755723 := bstep (se 1 (by rfl) ⟨5066792, by rfl⟩ : syracuseStep 6755723 = 10133585) B10133585
theorem B5207435 : Blo 1332985 5207435 := bstep (se 1 (by rfl) ⟨3905576, by rfl⟩ : syracuseStep 5207435 = 7811153) B7811153
theorem B24352163 : Blo 1332985 24352163 := bstep (se 1 (by rfl) ⟨18264122, by rfl⟩ : syracuseStep 24352163 = 36528245) B36528245
theorem B10261997 : Blo 1332985 10261997 := bstep (se 3 (by rfl) ⟨1924124, by rfl⟩ : syracuseStep 10261997 = 3848249) B3848249
theorem B3798535 : Blo 1332985 3798535 := bstep (se 1 (by rfl) ⟨2848901, by rfl⟩ : syracuseStep 3798535 = 5697803) B5697803
theorem B2250335 : Blo 1332985 2250335 := bstep (se 1 (by rfl) ⟨1687751, by rfl⟩ : syracuseStep 2250335 = 3375503) B3375503
theorem B8107705 : Blo 1332985 8107705 := bstep (se 2 (by rfl) ⟨3040389, by rfl⟩ : syracuseStep 8107705 = 6080779) B6080779
theorem B1333039 : Blo 1332985 1333039 := bstep (se 1 (by rfl) ⟨999779, by rfl⟩ : syracuseStep 1333039 = 1999559) B1999559
theorem B2250551 : Blo 1332985 2250551 := bstep (se 1 (by rfl) ⟨1687913, by rfl⟩ : syracuseStep 2250551 = 3375827) B3375827
theorem B702199637 : Blo 1332985 702199637 := bstep (se 9 (by rfl) ⟨2057225, by rfl⟩ : syracuseStep 702199637 = 4114451) B4114451
theorem B4503383 : Blo 1332985 4503383 := bstep (se 1 (by rfl) ⟨3377537, by rfl⟩ : syracuseStep 4503383 = 6755075) B6755075
theorem B1333147 : Blo 1332985 1333147 := bstep (se 1 (by rfl) ⟨999860, by rfl⟩ : syracuseStep 1333147 = 1999721) B1999721
theorem B14423993 : Blo 1332985 14423993 := bstep (se 2 (by rfl) ⟨5408997, by rfl⟩ : syracuseStep 14423993 = 10817995) B10817995
theorem B1333199 : Blo 1332985 1333199 := bstep (se 1 (by rfl) ⟨999899, by rfl⟩ : syracuseStep 1333199 = 1999799) B1999799
theorem B1333223 : Blo 1332985 1333223 := bstep (se 1 (by rfl) ⟨999917, by rfl⟩ : syracuseStep 1333223 = 1999835) B1999835
theorem B17094685 : Blo 1332985 17094685 := bstep (se 3 (by rfl) ⟨3205253, by rfl⟩ : syracuseStep 17094685 = 6410507) B6410507
theorem B4274441 : Blo 1332985 4274441 := bstep (se 2 (by rfl) ⟨1602915, by rfl⟩ : syracuseStep 4274441 = 3205831) B3205831
theorem B1333535 : Blo 1332985 1333535 := bstep (se 1 (by rfl) ⟨1000151, by rfl⟩ : syracuseStep 1333535 = 2000303) B2000303
theorem B1333595 : Blo 1332985 1333595 := bstep (se 1 (by rfl) ⟨1000196, by rfl⟩ : syracuseStep 1333595 = 2000393) B2000393
theorem B1333615 : Blo 1332985 1333615 := bstep (se 1 (by rfl) ⟨1000211, by rfl⟩ : syracuseStep 1333615 = 2000423) B2000423
theorem B1333671 : Blo 1332985 1333671 := bstep (se 1 (by rfl) ⟨1000253, by rfl⟩ : syracuseStep 1333671 = 2000507) B2000507
theorem B3848699 : Blo 1332985 3848699 := bstep (se 1 (by rfl) ⟨2886524, by rfl⟩ : syracuseStep 3848699 = 5773049) B5773049
theorem B1333755 : Blo 1332985 1333755 := bstep (se 1 (by rfl) ⟨1000316, by rfl⟩ : syracuseStep 1333755 = 2000633) B2000633
theorem B1333823 : Blo 1332985 1333823 := bstep (se 1 (by rfl) ⟨1000367, by rfl⟩ : syracuseStep 1333823 = 2000735) B2000735
theorem B2251327 : Blo 1332985 2251327 := bstep (se 1 (by rfl) ⟨1688495, by rfl⟩ : syracuseStep 2251327 = 3376991) B3376991
theorem B1333831 : Blo 1332985 1333831 := bstep (se 1 (by rfl) ⟨1000373, by rfl⟩ : syracuseStep 1333831 = 2000747) B2000747
theorem B4807363 : Blo 1332985 4807363 := bstep (se 1 (by rfl) ⟨3605522, by rfl⟩ : syracuseStep 4807363 = 7211045) B7211045
theorem B1333983 : Blo 1332985 1333983 := bstep (se 1 (by rfl) ⟨1000487, by rfl⟩ : syracuseStep 1333983 = 2000975) B2000975
theorem B6748919 : Blo 1332985 6748919 := bstep (se 1 (by rfl) ⟨5061689, by rfl⟩ : syracuseStep 6748919 = 10123379) B10123379
theorem B1334063 : Blo 1332985 1334063 := bstep (se 1 (by rfl) ⟨1000547, by rfl⟩ : syracuseStep 1334063 = 2001095) B2001095
theorem B4504463 : Blo 1332985 4504463 := bstep (se 1 (by rfl) ⟨3378347, by rfl⟩ : syracuseStep 4504463 = 6756695) B6756695
theorem B1334171 : Blo 1332985 1334171 := bstep (se 1 (by rfl) ⟨1000628, by rfl⟩ : syracuseStep 1334171 = 2001257) B2001257
theorem B1334223 : Blo 1332985 1334223 := bstep (se 1 (by rfl) ⟨1000667, by rfl⟩ : syracuseStep 1334223 = 2001335) B2001335
theorem B1334247 : Blo 1332985 1334247 := bstep (se 1 (by rfl) ⟨1000685, by rfl⟩ : syracuseStep 1334247 = 2001371) B2001371
theorem B14433329 : Blo 1332985 14433329 := bstep (se 2 (by rfl) ⟨5412498, by rfl⟩ : syracuseStep 14433329 = 10824997) B10824997
theorem B5700689 : Blo 1332985 5700689 := bstep (se 2 (by rfl) ⟨2137758, by rfl⟩ : syracuseStep 5700689 = 4275517) B4275517
theorem B24353909 : Blo 1332985 24353909 := bstep (se 5 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 24353909 = 2283179) B2283179
theorem B7306363 : Blo 1332985 7306363 := bstep (se 1 (by rfl) ⟨5479772, by rfl⟩ : syracuseStep 7306363 = 10959545) B10959545
theorem B3603599 : Blo 1332985 3603599 := bstep (se 1 (by rfl) ⟨2702699, by rfl⟩ : syracuseStep 3603599 = 5405399) B5405399
theorem B5405885 : Blo 1332985 5405885 := bstep (se 3 (by rfl) ⟨1013603, by rfl⟩ : syracuseStep 5405885 = 2027207) B2027207
theorem B6749405 : Blo 1332985 6749405 := bstep (se 3 (by rfl) ⟨1265513, by rfl⟩ : syracuseStep 6749405 = 2531027) B2531027
theorem B2252009 : Blo 1332985 2252009 := bstep (se 2 (by rfl) ⟨844503, by rfl⟩ : syracuseStep 2252009 = 1689007) B1689007
theorem B2252063 : Blo 1332985 2252063 := bstep (se 1 (by rfl) ⟨1689047, by rfl⟩ : syracuseStep 2252063 = 3378095) B3378095
theorem B1334559 : Blo 1332985 1334559 := bstep (se 1 (by rfl) ⟨1000919, by rfl⟩ : syracuseStep 1334559 = 2001839) B2001839
theorem B26008897 : Blo 1332985 26008897 := bstep (se 2 (by rfl) ⟨9753336, by rfl⟩ : syracuseStep 26008897 = 19506673) B19506673
theorem B1334619 : Blo 1332985 1334619 := bstep (se 1 (by rfl) ⟨1000964, by rfl⟩ : syracuseStep 1334619 = 2001929) B2001929
theorem B1334639 : Blo 1332985 1334639 := bstep (se 1 (by rfl) ⟨1000979, by rfl⟩ : syracuseStep 1334639 = 2001959) B2001959
theorem B3653003 : Blo 1332985 3653003 := bstep (se 1 (by rfl) ⟨2739752, by rfl⟩ : syracuseStep 3653003 = 5479505) B5479505
theorem B1334695 : Blo 1332985 1334695 := bstep (se 1 (by rfl) ⟨1001021, by rfl⟩ : syracuseStep 1334695 = 2002043) B2002043
theorem B1334779 : Blo 1332985 1334779 := bstep (se 1 (by rfl) ⟨1001084, by rfl⟩ : syracuseStep 1334779 = 2002169) B2002169
theorem B2850311 : Blo 1332985 2850311 := bstep (se 1 (by rfl) ⟨2137733, by rfl⟩ : syracuseStep 2850311 = 4275467) B4275467
theorem B1334847 : Blo 1332985 1334847 := bstep (se 1 (by rfl) ⟨1001135, by rfl⟩ : syracuseStep 1334847 = 2002271) B2002271
theorem B1334855 : Blo 1332985 1334855 := bstep (se 1 (by rfl) ⟨1001141, by rfl⟩ : syracuseStep 1334855 = 2002283) B2002283
theorem B5136107 : Blo 1332985 5136107 := bstep (se 1 (by rfl) ⟨3852080, by rfl⟩ : syracuseStep 5136107 = 7704161) B7704161
theorem B3374855 : Blo 1332985 3374855 := bstep (se 1 (by rfl) ⟨2531141, by rfl⟩ : syracuseStep 3374855 = 5062283) B5062283
theorem B8544041 : Blo 1332985 8544041 := bstep (se 2 (by rfl) ⟨3204015, by rfl⟩ : syracuseStep 8544041 = 6408031) B6408031
theorem B3374905 : Blo 1332985 3374905 := bstep (se 2 (by rfl) ⟨1265589, by rfl⟩ : syracuseStep 3374905 = 2531179) B2531179
theorem B7593857 : Blo 1332985 7593857 := bstep (se 2 (by rfl) ⟨2847696, by rfl⟩ : syracuseStep 7593857 = 5695393) B5695393
theorem B5349277 : Blo 1332985 5349277 := bstep (se 3 (by rfl) ⟨1002989, by rfl⟩ : syracuseStep 5349277 = 2005979) B2005979
theorem B21635207 : Blo 1332985 21635207 := bstep (se 1 (by rfl) ⟨16226405, by rfl⟩ : syracuseStep 21635207 = 32452811) B32452811
theorem B3375391 : Blo 1332985 3375391 := bstep (se 1 (by rfl) ⟨2531543, by rfl⟩ : syracuseStep 3375391 = 5063087) B5063087
theorem B7307815 : Blo 1332985 7307815 := bstep (se 1 (by rfl) ⟨5480861, by rfl⟩ : syracuseStep 7307815 = 10961723) B10961723
theorem B15196733 : Blo 1332985 15196733 := bstep (se 3 (by rfl) ⟨2849387, by rfl⟩ : syracuseStep 15196733 = 5698775) B5698775
theorem B19497647 : Blo 1332985 19497647 := bstep (se 1 (by rfl) ⟨14623235, by rfl⟩ : syracuseStep 19497647 = 29246471) B29246471
theorem B1999595 : Blo 1332985 1999595 := bstep (se 1 (by rfl) ⟨1499696, by rfl⟩ : syracuseStep 1999595 = 2999393) B2999393
theorem B7602923 : Blo 1332985 7602923 := bstep (se 1 (by rfl) ⟨5702192, by rfl⟩ : syracuseStep 7602923 = 11404385) B11404385
theorem B8659709 : Blo 1332985 8659709 := bstep (se 3 (by rfl) ⟨1623695, by rfl⟩ : syracuseStep 8659709 = 3247391) B3247391
theorem B1999625 : Blo 1332985 1999625 := bstep (se 2 (by rfl) ⟨749859, by rfl⟩ : syracuseStep 1999625 = 1499719) B1499719
theorem B1999727 : Blo 1332985 1999727 := bstep (se 1 (by rfl) ⟨1499795, by rfl⟩ : syracuseStep 1999727 = 2999591) B2999591
theorem B3376039 : Blo 1332985 3376039 := bstep (se 1 (by rfl) ⟨2532029, by rfl⟩ : syracuseStep 3376039 = 5064059) B5064059
theorem B6751187 : Blo 1332985 6751187 := bstep (se 1 (by rfl) ⟨5063390, by rfl⟩ : syracuseStep 6751187 = 10126781) B10126781
theorem B6841331 : Blo 1332985 6841331 := bstep (se 1 (by rfl) ⟨5130998, by rfl⟩ : syracuseStep 6841331 = 10261997) B10261997
theorem B1803259 : Blo 1332985 1803259 := bstep (se 1 (by rfl) ⟨1352444, by rfl⟩ : syracuseStep 1803259 = 2704889) B2704889
theorem B9741341 : Blo 1332985 9741341 := bstep (se 3 (by rfl) ⟨1826501, by rfl⟩ : syracuseStep 9741341 = 3653003) B3653003
theorem B1500223 : Blo 1332985 1500223 := bstep (se 1 (by rfl) ⟨1125167, by rfl⟩ : syracuseStep 1500223 = 2250335) B2250335
theorem B1999979 : Blo 1332985 1999979 := bstep (se 1 (by rfl) ⟨1499984, by rfl⟩ : syracuseStep 1999979 = 2999969) B2999969
theorem B1688683 : Blo 1332985 1688683 := bstep (se 1 (by rfl) ⟨1266512, by rfl⟩ : syracuseStep 1688683 = 2533025) B2533025
theorem B1500367 : Blo 1332985 1500367 := bstep (se 1 (by rfl) ⟨1125275, by rfl⟩ : syracuseStep 1500367 = 2250551) B2250551
theorem B468133091 : Blo 1332985 468133091 := bstep (se 1 (by rfl) ⟨351099818, by rfl⟩ : syracuseStep 468133091 = 702199637) B702199637
theorem B2000219 : Blo 1332985 2000219 := bstep (se 1 (by rfl) ⟨1500164, by rfl⟩ : syracuseStep 2000219 = 3000329) B3000329
theorem B9618821 : Blo 1332985 9618821 := bstep (se 4 (by rfl) ⟨901764, by rfl⟩ : syracuseStep 9618821 = 1803529) B1803529
theorem B9741817 : Blo 1332985 9741817 := bstep (se 2 (by rfl) ⟨3653181, by rfl⟩ : syracuseStep 9741817 = 7306363) B7306363
theorem B1443439 : Blo 1332985 1443439 := bstep (se 1 (by rfl) ⟨1082579, by rfl⟩ : syracuseStep 1443439 = 2165159) B2165159
theorem B2000495 : Blo 1332985 2000495 := bstep (se 1 (by rfl) ⟨1500371, by rfl⟩ : syracuseStep 2000495 = 3000743) B3000743
theorem B2565799 : Blo 1332985 2565799 := bstep (se 1 (by rfl) ⟨1924349, by rfl⟩ : syracuseStep 2565799 = 3848699) B3848699
theorem B2000567 : Blo 1332985 2000567 := bstep (se 1 (by rfl) ⟨1500425, by rfl⟩ : syracuseStep 2000567 = 3000851) B3000851
theorem B2000603 : Blo 1332985 2000603 := bstep (se 1 (by rfl) ⟨1500452, by rfl⟩ : syracuseStep 2000603 = 3000905) B3000905
theorem B34678529 : Blo 1332985 34678529 := bstep (se 2 (by rfl) ⟨13004448, by rfl⟩ : syracuseStep 34678529 = 26008897) B26008897
theorem B3000095 : Blo 1332985 3000095 := bstep (se 1 (by rfl) ⟨2250071, by rfl⟩ : syracuseStep 3000095 = 4500143) B4500143
theorem B1443647 : Blo 1332985 1443647 := bstep (se 1 (by rfl) ⟨1082735, by rfl⟩ : syracuseStep 1443647 = 2165471) B2165471
theorem B4499279 : Blo 1332985 4499279 := bstep (se 1 (by rfl) ⟨3374459, by rfl⟩ : syracuseStep 4499279 = 6748919) B6748919
theorem B2000777 : Blo 1332985 2000777 := bstep (se 2 (by rfl) ⟨750291, by rfl⟩ : syracuseStep 2000777 = 1500583) B1500583
theorem B2000879 : Blo 1332985 2000879 := bstep (se 1 (by rfl) ⟨1500659, by rfl⟩ : syracuseStep 2000879 = 3001319) B3001319
theorem B3000311 : Blo 1332985 3000311 := bstep (se 1 (by rfl) ⟨2250233, by rfl⟩ : syracuseStep 3000311 = 4500467) B4500467
theorem B5064713 : Blo 1332985 5064713 := bstep (se 2 (by rfl) ⟨1899267, by rfl⟩ : syracuseStep 5064713 = 3798535) B3798535
theorem B2402399 : Blo 1332985 2402399 := bstep (se 1 (by rfl) ⟨1801799, by rfl⟩ : syracuseStep 2402399 = 3603599) B3603599
theorem B6842477 : Blo 1332985 6842477 := bstep (se 3 (by rfl) ⟨1282964, by rfl⟩ : syracuseStep 6842477 = 2565929) B2565929
theorem B4499603 : Blo 1332985 4499603 := bstep (se 1 (by rfl) ⟨3374702, by rfl⟩ : syracuseStep 4499603 = 6749405) B6749405
theorem B1501339 : Blo 1332985 1501339 := bstep (se 1 (by rfl) ⟨1126004, by rfl⟩ : syracuseStep 1501339 = 2252009) B2252009
theorem B69298361 : Blo 1332985 69298361 := bstep (se 2 (by rfl) ⟨25986885, by rfl⟩ : syracuseStep 69298361 = 51973771) B51973771
theorem B1501375 : Blo 1332985 1501375 := bstep (se 1 (by rfl) ⟨1126031, by rfl⟩ : syracuseStep 1501375 = 2252063) B2252063
theorem B2001131 : Blo 1332985 2001131 := bstep (se 1 (by rfl) ⟨1500848, by rfl⟩ : syracuseStep 2001131 = 3001697) B3001697
theorem B2001191 : Blo 1332985 2001191 := bstep (se 1 (by rfl) ⟨1500893, by rfl⟩ : syracuseStep 2001191 = 3001787) B3001787
theorem B3377447 : Blo 1332985 3377447 := bstep (se 1 (by rfl) ⟨2533085, by rfl⟩ : syracuseStep 3377447 = 5066171) B5066171
theorem B11700571 : Blo 1332985 11700571 := bstep (se 1 (by rfl) ⟨8775428, by rfl⟩ : syracuseStep 11700571 = 17550857) B17550857
theorem B3000671 : Blo 1332985 3000671 := bstep (se 1 (by rfl) ⟨2250503, by rfl⟩ : syracuseStep 3000671 = 4501007) B4501007
theorem B2001275 : Blo 1332985 2001275 := bstep (se 1 (by rfl) ⟨1500956, by rfl⟩ : syracuseStep 2001275 = 3001913) B3001913
theorem B4499873 : Blo 1332985 4499873 := bstep (se 2 (by rfl) ⟨1687452, by rfl⟩ : syracuseStep 4499873 = 3374905) B3374905
theorem B55470521 : Blo 1332985 55470521 := bstep (se 2 (by rfl) ⟨20801445, by rfl⟩ : syracuseStep 55470521 = 41602891) B41602891
theorem B5696027 : Blo 1332985 5696027 := bstep (se 1 (by rfl) ⟨4272020, by rfl⟩ : syracuseStep 5696027 = 8544041) B8544041
theorem B2001545 : Blo 1332985 2001545 := bstep (se 2 (by rfl) ⟨750579, by rfl⟩ : syracuseStep 2001545 = 1501159) B1501159
theorem B22792913 : Blo 1332985 22792913 := bstep (se 2 (by rfl) ⟨8547342, by rfl⟩ : syracuseStep 22792913 = 17094685) B17094685
theorem B38488877 : Blo 1332985 38488877 := bstep (se 3 (by rfl) ⟨7216664, by rfl⟩ : syracuseStep 38488877 = 14433329) B14433329
theorem B2001719 : Blo 1332985 2001719 := bstep (se 1 (by rfl) ⟨1501289, by rfl⟩ : syracuseStep 2001719 = 3002579) B3002579
theorem B93678403 : Blo 1332985 93678403 := bstep (se 1 (by rfl) ⟨70258802, by rfl⟩ : syracuseStep 93678403 = 140517605) B140517605
theorem B2001755 : Blo 1332985 2001755 := bstep (se 1 (by rfl) ⟨1501316, by rfl⟩ : syracuseStep 2001755 = 3002633) B3002633
theorem B8547191 : Blo 1332985 8547191 := bstep (se 1 (by rfl) ⟨6410393, by rfl⟩ : syracuseStep 8547191 = 12820787) B12820787
theorem B1952671 : Blo 1332985 1952671 := bstep (se 1 (by rfl) ⟨1464503, by rfl⟩ : syracuseStep 1952671 = 2929007) B2929007
theorem B2001899 : Blo 1332985 2001899 := bstep (se 1 (by rfl) ⟨1501424, by rfl⟩ : syracuseStep 2001899 = 3002849) B3002849
theorem B3001391 : Blo 1332985 3001391 := bstep (se 1 (by rfl) ⟨2251043, by rfl⟩ : syracuseStep 3001391 = 4502087) B4502087
theorem B4271201 : Blo 1332985 4271201 := bstep (se 2 (by rfl) ⟨1601700, by rfl⟩ : syracuseStep 4271201 = 3203401) B3203401
theorem B2002103 : Blo 1332985 2002103 := bstep (se 1 (by rfl) ⟨1501577, by rfl⟩ : syracuseStep 2002103 = 3003155) B3003155
theorem B3001679 : Blo 1332985 3001679 := bstep (se 1 (by rfl) ⟨2251259, by rfl⟩ : syracuseStep 3001679 = 4502519) B4502519
theorem B39538043 : Blo 1332985 39538043 := bstep (se 1 (by rfl) ⟨29653532, by rfl⟩ : syracuseStep 39538043 = 59307065) B59307065
theorem B2002343 : Blo 1332985 2002343 := bstep (se 1 (by rfl) ⟨1501757, by rfl⟩ : syracuseStep 2002343 = 3003515) B3003515
theorem B3001769 : Blo 1332985 3001769 := bstep (se 2 (by rfl) ⟨1125663, by rfl⟩ : syracuseStep 3001769 = 2251327) B2251327
theorem B16215511 : Blo 1332985 16215511 := bstep (se 1 (by rfl) ⟨12161633, by rfl⟩ : syracuseStep 16215511 = 24323267) B24323267
theorem B2002427 : Blo 1332985 2002427 := bstep (se 1 (by rfl) ⟨1501820, by rfl⟩ : syracuseStep 2002427 = 3003641) B3003641
theorem B6409817 : Blo 1332985 6409817 := bstep (se 2 (by rfl) ⟨2403681, by rfl⟩ : syracuseStep 6409817 = 4807363) B4807363
theorem B21630797 : Blo 1332985 21630797 := bstep (se 3 (by rfl) ⟨4055774, by rfl⟩ : syracuseStep 21630797 = 8111549) B8111549
theorem B10137473 : Blo 1332985 10137473 := bstep (se 2 (by rfl) ⟨3801552, by rfl⟩ : syracuseStep 10137473 = 7603105) B7603105
theorem B3002255 : Blo 1332985 3002255 := bstep (se 1 (by rfl) ⟨2251691, by rfl⟩ : syracuseStep 3002255 = 4503383) B4503383
theorem B8564653 : Blo 1332985 8564653 := bstep (se 3 (by rfl) ⟨1605872, by rfl⟩ : syracuseStep 8564653 = 3211745) B3211745
theorem B12824705 : Blo 1332985 12824705 := bstep (se 2 (by rfl) ⟨4809264, by rfl⟩ : syracuseStep 12824705 = 9618529) B9618529
theorem B4501871 : Blo 1332985 4501871 := bstep (se 1 (by rfl) ⟨3376403, by rfl⟩ : syracuseStep 4501871 = 6752807) B6752807
theorem B3002975 : Blo 1332985 3002975 := bstep (se 1 (by rfl) ⟨2252231, by rfl⟩ : syracuseStep 3002975 = 4504463) B4504463
theorem B10810273 : Blo 1332985 10810273 := bstep (se 2 (by rfl) ⟨4053852, by rfl⟩ : syracuseStep 10810273 = 8107705) B8107705
theorem B1602623 : Blo 1332985 1602623 := bstep (se 1 (by rfl) ⟨1201967, by rfl⟩ : syracuseStep 1602623 = 2403935) B2403935
theorem B2249903 : Blo 1332985 2249903 := bstep (se 1 (by rfl) ⟨1687427, by rfl⟩ : syracuseStep 2249903 = 3374855) B3374855
theorem B2847919 : Blo 1332985 2847919 := bstep (se 1 (by rfl) ⟨2135939, by rfl⟩ : syracuseStep 2847919 = 4271879) B4271879
theorem B7132369 : Blo 1332985 7132369 := bstep (se 2 (by rfl) ⟨2674638, by rfl⟩ : syracuseStep 7132369 = 5349277) B5349277
theorem B3798227 : Blo 1332985 3798227 := bstep (se 1 (by rfl) ⟨2848670, by rfl⟩ : syracuseStep 3798227 = 5697341) B5697341
theorem B8549651 : Blo 1332985 8549651 := bstep (se 1 (by rfl) ⟨6412238, by rfl⟩ : syracuseStep 8549651 = 12824477) B12824477
theorem B5068129 : Blo 1332985 5068129 := bstep (se 2 (by rfl) ⟨1900548, by rfl⟩ : syracuseStep 5068129 = 3801097) B3801097
theorem B2250139 : Blo 1332985 2250139 := bstep (se 1 (by rfl) ⟨1687604, by rfl⟩ : syracuseStep 2250139 = 3375209) B3375209
theorem B2250463 : Blo 1332985 2250463 := bstep (se 1 (by rfl) ⟨1687847, by rfl⟩ : syracuseStep 2250463 = 3375695) B3375695
theorem B4503275 : Blo 1332985 4503275 := bstep (se 1 (by rfl) ⟨3377456, by rfl⟩ : syracuseStep 4503275 = 6754913) B6754913
theorem B1332987 : Blo 1332985 1332987 := bstep (se 1 (by rfl) ⟨999740, by rfl⟩ : syracuseStep 1332987 = 1999481) B1999481
theorem B1333023 : Blo 1332985 1333023 := bstep (se 1 (by rfl) ⟨999767, by rfl⟩ : syracuseStep 1333023 = 1999535) B1999535
theorem B5068601 : Blo 1332985 5068601 := bstep (se 2 (by rfl) ⟨1900725, by rfl⟩ : syracuseStep 5068601 = 3801451) B3801451
theorem B1333055 : Blo 1332985 1333055 := bstep (se 1 (by rfl) ⟨999791, by rfl⟩ : syracuseStep 1333055 = 1999583) B1999583
theorem B24352741 : Blo 1332985 24352741 := bstep (se 4 (by rfl) ⟨2283069, by rfl⟩ : syracuseStep 24352741 = 4566139) B4566139
theorem B1333231 : Blo 1332985 1333231 := bstep (se 1 (by rfl) ⟨999923, by rfl⟩ : syracuseStep 1333231 = 1999847) B1999847
theorem B4503545 : Blo 1332985 4503545 := bstep (se 2 (by rfl) ⟨1688829, by rfl⟩ : syracuseStep 4503545 = 3377659) B3377659
theorem B9615419 : Blo 1332985 9615419 := bstep (se 1 (by rfl) ⟨7211564, by rfl⟩ : syracuseStep 9615419 = 14423129) B14423129
theorem B2250895 : Blo 1332985 2250895 := bstep (se 1 (by rfl) ⟨1688171, by rfl⟩ : syracuseStep 2250895 = 3376343) B3376343
theorem B1333403 : Blo 1332985 1333403 := bstep (se 1 (by rfl) ⟨1000052, by rfl⟩ : syracuseStep 1333403 = 2000105) B2000105
theorem B4503707 : Blo 1332985 4503707 := bstep (se 1 (by rfl) ⟨3377780, by rfl⟩ : syracuseStep 4503707 = 6755561) B6755561
theorem B1333439 : Blo 1332985 1333439 := bstep (se 1 (by rfl) ⟨1000079, by rfl⟩ : syracuseStep 1333439 = 2000159) B2000159
theorem B4503815 : Blo 1332985 4503815 := bstep (se 1 (by rfl) ⟨3377861, by rfl⟩ : syracuseStep 4503815 = 6755723) B6755723
theorem B3471623 : Blo 1332985 3471623 := bstep (se 1 (by rfl) ⟨2603717, by rfl⟩ : syracuseStep 3471623 = 5207435) B5207435
theorem B16234775 : Blo 1332985 16234775 := bstep (se 1 (by rfl) ⟨12176081, by rfl⟩ : syracuseStep 16234775 = 24352163) B24352163
theorem B1333551 : Blo 1332985 1333551 := bstep (se 1 (by rfl) ⟨1000163, by rfl⟩ : syracuseStep 1333551 = 2000327) B2000327
theorem B1333787 : Blo 1332985 1333787 := bstep (se 1 (by rfl) ⟨1000340, by rfl⟩ : syracuseStep 1333787 = 2000681) B2000681
theorem B1333791 : Blo 1332985 1333791 := bstep (se 1 (by rfl) ⟨1000343, by rfl⟩ : syracuseStep 1333791 = 2000687) B2000687
theorem B9615995 : Blo 1332985 9615995 := bstep (se 1 (by rfl) ⟨7211996, by rfl⟩ : syracuseStep 9615995 = 14423993) B14423993
theorem B1334107 : Blo 1332985 1334107 := bstep (se 1 (by rfl) ⟨1000580, by rfl⟩ : syracuseStep 1334107 = 2001161) B2001161
theorem B2849627 : Blo 1332985 2849627 := bstep (se 1 (by rfl) ⟨2137220, by rfl⟩ : syracuseStep 2849627 = 4274441) B4274441
theorem B1334175 : Blo 1332985 1334175 := bstep (se 1 (by rfl) ⟨1000631, by rfl⟩ : syracuseStep 1334175 = 2001263) B2001263
theorem B1334319 : Blo 1332985 1334319 := bstep (se 1 (by rfl) ⟨1000739, by rfl⟩ : syracuseStep 1334319 = 2001479) B2001479
theorem B1334343 : Blo 1332985 1334343 := bstep (se 1 (by rfl) ⟨1000757, by rfl⟩ : syracuseStep 1334343 = 2001515) B2001515
theorem B2251847 : Blo 1332985 2251847 := bstep (se 1 (by rfl) ⟨1688885, by rfl⟩ : syracuseStep 2251847 = 3377771) B3377771
theorem B1334495 : Blo 1332985 1334495 := bstep (se 1 (by rfl) ⟨1000871, by rfl⟩ : syracuseStep 1334495 = 2001743) B2001743
theorem B4504841 : Blo 1332985 4504841 := bstep (se 2 (by rfl) ⟨1689315, by rfl⟩ : syracuseStep 4504841 = 3378631) B3378631
theorem B13696285 : Blo 1332985 13696285 := bstep (se 3 (by rfl) ⟨2568053, by rfl⟩ : syracuseStep 13696285 = 5136107) B5136107
theorem B3800459 : Blo 1332985 3800459 := bstep (se 1 (by rfl) ⟨2850344, by rfl⟩ : syracuseStep 3800459 = 5700689) B5700689
theorem B16235939 : Blo 1332985 16235939 := bstep (se 1 (by rfl) ⟨12176954, by rfl⟩ : syracuseStep 16235939 = 24353909) B24353909
theorem B3603923 : Blo 1332985 3603923 := bstep (se 1 (by rfl) ⟨2702942, by rfl⟩ : syracuseStep 3603923 = 5405885) B5405885
theorem B1334759 : Blo 1332985 1334759 := bstep (se 1 (by rfl) ⟨1001069, by rfl⟩ : syracuseStep 1334759 = 2002139) B2002139
theorem B2252279 : Blo 1332985 2252279 := bstep (se 1 (by rfl) ⟨1689209, by rfl⟩ : syracuseStep 2252279 = 3378419) B3378419
theorem B1334875 : Blo 1332985 1334875 := bstep (se 1 (by rfl) ⟨1001156, by rfl⟩ : syracuseStep 1334875 = 2002313) B2002313
theorem B1900207 : Blo 1332985 1900207 := bstep (se 1 (by rfl) ⟨1425155, by rfl⟩ : syracuseStep 1900207 = 2850311) B2850311
theorem B4808573 : Blo 1332985 4808573 := bstep (se 3 (by rfl) ⟨901607, by rfl⟩ : syracuseStep 4808573 = 1803215) B1803215
theorem B5062571 : Blo 1332985 5062571 := bstep (se 1 (by rfl) ⟨3796928, by rfl⟩ : syracuseStep 5062571 = 7593857) B7593857
theorem B25976909 : Blo 1332985 25976909 := bstep (se 3 (by rfl) ⟨4870670, by rfl⟩ : syracuseStep 25976909 = 9741341) B9741341
theorem B6406397 : Blo 1332985 6406397 := bstep (se 3 (by rfl) ⟨1201199, by rfl⟩ : syracuseStep 6406397 = 2402399) B2402399
theorem B1499935 : Blo 1332985 1499935 := bstep (se 1 (by rfl) ⟨1124951, by rfl⟩ : syracuseStep 1499935 = 2249903) B2249903
theorem B2532151 : Blo 1332985 2532151 := bstep (se 1 (by rfl) ⟨1899113, by rfl⟩ : syracuseStep 2532151 = 3798227) B3798227
theorem B10134557 : Blo 1332985 10134557 := bstep (se 3 (by rfl) ⟨1900229, by rfl⟩ : syracuseStep 10134557 = 3800459) B3800459
theorem B124904537 : Blo 1332985 124904537 := bstep (se 2 (by rfl) ⟨46839201, by rfl⟩ : syracuseStep 124904537 = 93678403) B93678403
theorem B23119019 : Blo 1332985 23119019 := bstep (se 1 (by rfl) ⟨17339264, by rfl⟩ : syracuseStep 23119019 = 34678529) B34678529
theorem B2000063 : Blo 1332985 2000063 := bstep (se 1 (by rfl) ⟨1500047, by rfl⟩ : syracuseStep 2000063 = 3000095) B3000095
theorem B2999519 : Blo 1332985 2999519 := bstep (se 1 (by rfl) ⟨2249639, by rfl⟩ : syracuseStep 2999519 = 4499279) B4499279
theorem B2000207 : Blo 1332985 2000207 := bstep (se 1 (by rfl) ⟨1500155, by rfl⟩ : syracuseStep 2000207 = 3000311) B3000311
theorem B3376475 : Blo 1332985 3376475 := bstep (se 1 (by rfl) ⟨2532356, by rfl⟩ : syracuseStep 3376475 = 5064713) B5064713
theorem B2000297 : Blo 1332985 2000297 := bstep (se 2 (by rfl) ⟨750111, by rfl⟩ : syracuseStep 2000297 = 1500223) B1500223
theorem B2999735 : Blo 1332985 2999735 := bstep (se 1 (by rfl) ⟨2249801, by rfl⟩ : syracuseStep 2999735 = 4499603) B4499603
theorem B10823183 : Blo 1332985 10823183 := bstep (se 1 (by rfl) ⟨8117387, by rfl⟩ : syracuseStep 10823183 = 16234775) B16234775
theorem B2000447 : Blo 1332985 2000447 := bstep (se 1 (by rfl) ⟨1500335, by rfl⟩ : syracuseStep 2000447 = 3000671) B3000671
theorem B2000489 : Blo 1332985 2000489 := bstep (se 2 (by rfl) ⟨750183, by rfl⟩ : syracuseStep 2000489 = 1500367) B1500367
theorem B2999915 : Blo 1332985 2999915 := bstep (se 1 (by rfl) ⟨2249936, by rfl⟩ : syracuseStep 2999915 = 4499873) B4499873
theorem B18261713 : Blo 1332985 18261713 := bstep (se 2 (by rfl) ⟨6848142, by rfl⟩ : syracuseStep 18261713 = 13696285) B13696285
theorem B25659251 : Blo 1332985 25659251 := bstep (se 1 (by rfl) ⟨19244438, by rfl⟩ : syracuseStep 25659251 = 38488877) B38488877
theorem B3000185 : Blo 1332985 3000185 := bstep (se 2 (by rfl) ⟨1125069, by rfl⟩ : syracuseStep 3000185 = 2250139) B2250139
theorem B21620681 : Blo 1332985 21620681 := bstep (se 2 (by rfl) ⟨8107755, by rfl⟩ : syracuseStep 21620681 = 16215511) B16215511
theorem B2000927 : Blo 1332985 2000927 := bstep (se 1 (by rfl) ⟨1500695, by rfl⟩ : syracuseStep 2000927 = 3001391) B3001391
theorem B1501231 : Blo 1332985 1501231 := bstep (se 1 (by rfl) ⟨1125923, by rfl⟩ : syracuseStep 1501231 = 2251847) B2251847
theorem B2001119 : Blo 1332985 2001119 := bstep (se 1 (by rfl) ⟨1500839, by rfl⟩ : syracuseStep 2001119 = 3001679) B3001679
theorem B2533609 : Blo 1332985 2533609 := bstep (se 2 (by rfl) ⟨950103, by rfl⟩ : syracuseStep 2533609 = 1900207) B1900207
theorem B10823959 : Blo 1332985 10823959 := bstep (se 1 (by rfl) ⟨8117969, by rfl⟩ : syracuseStep 10823959 = 16235939) B16235939
theorem B2001179 : Blo 1332985 2001179 := bstep (se 1 (by rfl) ⟨1500884, by rfl⟩ : syracuseStep 2001179 = 3001769) B3001769
theorem B3000617 : Blo 1332985 3000617 := bstep (se 2 (by rfl) ⟨1125231, by rfl⟩ : syracuseStep 3000617 = 2250463) B2250463
theorem B2402615 : Blo 1332985 2402615 := bstep (se 1 (by rfl) ⟨1801961, by rfl⟩ : syracuseStep 2402615 = 3603923) B3603923
theorem B1501519 : Blo 1332985 1501519 := bstep (se 1 (by rfl) ⟨1126139, by rfl⟩ : syracuseStep 1501519 = 2252279) B2252279
theorem B14420531 : Blo 1332985 14420531 := bstep (se 1 (by rfl) ⟨10815398, by rfl⟩ : syracuseStep 14420531 = 21630797) B21630797
theorem B3205715 : Blo 1332985 3205715 := bstep (se 1 (by rfl) ⟨2404286, by rfl⟩ : syracuseStep 3205715 = 4808573) B4808573
theorem B2001503 : Blo 1332985 2001503 := bstep (se 1 (by rfl) ⟨1501127, by rfl⟩ : syracuseStep 2001503 = 3002255) B3002255
theorem B3001193 : Blo 1332985 3001193 := bstep (se 2 (by rfl) ⟨1125447, by rfl⟩ : syracuseStep 3001193 = 2250895) B2250895
theorem B2001785 : Blo 1332985 2001785 := bstep (se 2 (by rfl) ⟨750669, by rfl⟩ : syracuseStep 2001785 = 1501339) B1501339
theorem B3001247 : Blo 1332985 3001247 := bstep (se 1 (by rfl) ⟨2250935, by rfl⟩ : syracuseStep 3001247 = 4501871) B4501871
theorem B2001833 : Blo 1332985 2001833 := bstep (se 2 (by rfl) ⟨750687, by rfl⟩ : syracuseStep 2001833 = 1501375) B1501375
theorem B4500521 : Blo 1332985 4500521 := bstep (se 2 (by rfl) ⟨1687695, by rfl⟩ : syracuseStep 4500521 = 3375391) B3375391
theorem B2001983 : Blo 1332985 2001983 := bstep (se 1 (by rfl) ⟨1501487, by rfl⟩ : syracuseStep 2001983 = 3002975) B3002975
theorem B15600761 : Blo 1332985 15600761 := bstep (se 2 (by rfl) ⟨5850285, by rfl⟩ : syracuseStep 15600761 = 11700571) B11700571
theorem B4500791 : Blo 1332985 4500791 := bstep (se 1 (by rfl) ⟨3375593, by rfl⟩ : syracuseStep 4500791 = 6751187) B6751187
theorem B9743753 : Blo 1332985 9743753 := bstep (se 2 (by rfl) ⟨3653907, by rfl⟩ : syracuseStep 9743753 = 7307815) B7307815
theorem B13684261 : Blo 1332985 13684261 := bstep (se 4 (by rfl) ⟨1282899, by rfl⟩ : syracuseStep 13684261 = 2565799) B2565799
theorem B3002183 : Blo 1332985 3002183 := bstep (se 1 (by rfl) ⟨2251637, by rfl⟩ : syracuseStep 3002183 = 4503275) B4503275
theorem B3379067 : Blo 1332985 3379067 := bstep (se 1 (by rfl) ⟨2534300, by rfl⟩ : syracuseStep 3379067 = 5068601) B5068601
theorem B14413697 : Blo 1332985 14413697 := bstep (se 2 (by rfl) ⟨5405136, by rfl⟩ : syracuseStep 14413697 = 10810273) B10810273
theorem B4501385 : Blo 1332985 4501385 := bstep (se 2 (by rfl) ⟨1688019, by rfl⟩ : syracuseStep 4501385 = 3376039) B3376039
theorem B2404345 : Blo 1332985 2404345 := bstep (se 2 (by rfl) ⟨901629, by rfl⟩ : syracuseStep 2404345 = 1803259) B1803259
theorem B3002363 : Blo 1332985 3002363 := bstep (se 1 (by rfl) ⟨2251772, by rfl⟩ : syracuseStep 3002363 = 4503545) B4503545
theorem B6410279 : Blo 1332985 6410279 := bstep (se 1 (by rfl) ⟨4807709, by rfl⟩ : syracuseStep 6410279 = 9615419) B9615419
theorem B3002471 : Blo 1332985 3002471 := bstep (se 1 (by rfl) ⟨2251853, by rfl⟩ : syracuseStep 3002471 = 4503707) B4503707
theorem B46198907 : Blo 1332985 46198907 := bstep (se 1 (by rfl) ⟨34649180, by rfl⟩ : syracuseStep 46198907 = 69298361) B69298361
theorem B3002543 : Blo 1332985 3002543 := bstep (se 1 (by rfl) ⟨2251907, by rfl⟩ : syracuseStep 3002543 = 4503815) B4503815
theorem B2314415 : Blo 1332985 2314415 := bstep (se 1 (by rfl) ⟨1735811, by rfl⟩ : syracuseStep 2314415 = 3471623) B3471623
theorem B3797225 : Blo 1332985 3797225 := bstep (se 2 (by rfl) ⟨1423959, by rfl⟩ : syracuseStep 3797225 = 2847919) B2847919
theorem B3797351 : Blo 1332985 3797351 := bstep (se 1 (by rfl) ⟨2848013, by rfl⟩ : syracuseStep 3797351 = 5696027) B5696027
theorem B6410663 : Blo 1332985 6410663 := bstep (se 1 (by rfl) ⟨4807997, by rfl⟩ : syracuseStep 6410663 = 9615995) B9615995
theorem B5698127 : Blo 1332985 5698127 := bstep (se 1 (by rfl) ⟨4273595, by rfl⟩ : syracuseStep 5698127 = 8547191) B8547191
theorem B12989089 : Blo 1332985 12989089 := bstep (se 2 (by rfl) ⟨4870908, by rfl⟩ : syracuseStep 12989089 = 9741817) B9741817
theorem B2847467 : Blo 1332985 2847467 := bstep (se 1 (by rfl) ⟨2135600, by rfl⟩ : syracuseStep 2847467 = 4271201) B4271201
theorem B3003227 : Blo 1332985 3003227 := bstep (se 1 (by rfl) ⟨2252420, by rfl⟩ : syracuseStep 3003227 = 4504841) B4504841
theorem B7599005 : Blo 1332985 7599005 := bstep (se 3 (by rfl) ⟨1424813, by rfl⟩ : syracuseStep 7599005 = 2849627) B2849627
theorem B26358695 : Blo 1332985 26358695 := bstep (se 1 (by rfl) ⟨19769021, by rfl⟩ : syracuseStep 26358695 = 39538043) B39538043
theorem B4273211 : Blo 1332985 4273211 := bstep (se 1 (by rfl) ⟨3204908, by rfl⟩ : syracuseStep 4273211 = 6409817) B6409817
theorem B32470321 : Blo 1332985 32470321 := bstep (se 2 (by rfl) ⟨12176370, by rfl⟩ : syracuseStep 32470321 = 24352741) B24352741
theorem B8549803 : Blo 1332985 8549803 := bstep (se 1 (by rfl) ⟨6412352, by rfl⟩ : syracuseStep 8549803 = 12824705) B12824705
theorem B14423471 : Blo 1332985 14423471 := bstep (se 1 (by rfl) ⟨10817603, by rfl⟩ : syracuseStep 14423471 = 21635207) B21635207
theorem B4273661 : Blo 1332985 4273661 := bstep (se 3 (by rfl) ⟨801311, by rfl⟩ : syracuseStep 4273661 = 1602623) B1602623
theorem B10131155 : Blo 1332985 10131155 := bstep (se 1 (by rfl) ⟨7598366, by rfl⟩ : syracuseStep 10131155 = 15196733) B15196733
theorem B12998431 : Blo 1332985 12998431 := bstep (se 1 (by rfl) ⟨9748823, by rfl⟩ : syracuseStep 12998431 = 19497647) B19497647
theorem B1333063 : Blo 1332985 1333063 := bstep (se 1 (by rfl) ⟨999797, by rfl⟩ : syracuseStep 1333063 = 1999595) B1999595
theorem B5068615 : Blo 1332985 5068615 := bstep (se 1 (by rfl) ⟨3801461, by rfl⟩ : syracuseStep 5068615 = 7602923) B7602923
theorem B5773139 : Blo 1332985 5773139 := bstep (se 1 (by rfl) ⟨4329854, by rfl⟩ : syracuseStep 5773139 = 8659709) B8659709
theorem B1333083 : Blo 1332985 1333083 := bstep (se 1 (by rfl) ⟨999812, by rfl⟩ : syracuseStep 1333083 = 1999625) B1999625
theorem B1333151 : Blo 1332985 1333151 := bstep (se 1 (by rfl) ⟨999863, by rfl⟩ : syracuseStep 1333151 = 1999727) B1999727
theorem B7698341 : Blo 1332985 7698341 := bstep (se 4 (by rfl) ⟨721719, by rfl⟩ : syracuseStep 7698341 = 1443439) B1443439
theorem B4560887 : Blo 1332985 4560887 := bstep (se 1 (by rfl) ⟨3420665, by rfl⟩ : syracuseStep 4560887 = 6841331) B6841331
theorem B1333319 : Blo 1332985 1333319 := bstep (se 1 (by rfl) ⟨999989, by rfl⟩ : syracuseStep 1333319 = 1999979) B1999979
theorem B312088727 : Blo 1332985 312088727 := bstep (se 1 (by rfl) ⟨234066545, by rfl⟩ : syracuseStep 312088727 = 468133091) B468133091
theorem B5699767 : Blo 1332985 5699767 := bstep (se 1 (by rfl) ⟨4274825, by rfl⟩ : syracuseStep 5699767 = 8549651) B8549651
theorem B1333479 : Blo 1332985 1333479 := bstep (se 1 (by rfl) ⟨1000109, by rfl⟩ : syracuseStep 1333479 = 2000219) B2000219
theorem B6412547 : Blo 1332985 6412547 := bstep (se 1 (by rfl) ⟨4809410, by rfl⟩ : syracuseStep 6412547 = 9618821) B9618821
theorem B1333663 : Blo 1332985 1333663 := bstep (se 1 (by rfl) ⟨1000247, by rfl⟩ : syracuseStep 1333663 = 2000495) B2000495
theorem B1333711 : Blo 1332985 1333711 := bstep (se 1 (by rfl) ⟨1000283, by rfl⟩ : syracuseStep 1333711 = 2000567) B2000567
theorem B1333735 : Blo 1332985 1333735 := bstep (se 1 (by rfl) ⟨1000301, by rfl⟩ : syracuseStep 1333735 = 2000603) B2000603
theorem B147921389 : Blo 1332985 147921389 := bstep (se 3 (by rfl) ⟨27735260, by rfl⟩ : syracuseStep 147921389 = 55470521) B55470521
theorem B2603561 : Blo 1332985 2603561 := bstep (se 2 (by rfl) ⟨976335, by rfl⟩ : syracuseStep 2603561 = 1952671) B1952671
theorem B1333851 : Blo 1332985 1333851 := bstep (se 1 (by rfl) ⟨1000388, by rfl⟩ : syracuseStep 1333851 = 2000777) B2000777
theorem B1333919 : Blo 1332985 1333919 := bstep (se 1 (by rfl) ⟨1000439, by rfl⟩ : syracuseStep 1333919 = 2000879) B2000879
theorem B4561651 : Blo 1332985 4561651 := bstep (se 1 (by rfl) ⟨3421238, by rfl⟩ : syracuseStep 4561651 = 6842477) B6842477
theorem B2251577 : Blo 1332985 2251577 := bstep (se 2 (by rfl) ⟨844341, by rfl⟩ : syracuseStep 2251577 = 1688683) B1688683
theorem B1334087 : Blo 1332985 1334087 := bstep (se 1 (by rfl) ⟨1000565, by rfl⟩ : syracuseStep 1334087 = 2001131) B2001131
theorem B1334127 : Blo 1332985 1334127 := bstep (se 1 (by rfl) ⟨1000595, by rfl⟩ : syracuseStep 1334127 = 2001191) B2001191
theorem B2251631 : Blo 1332985 2251631 := bstep (se 1 (by rfl) ⟨1688723, by rfl⟩ : syracuseStep 2251631 = 3377447) B3377447
theorem B1334183 : Blo 1332985 1334183 := bstep (se 1 (by rfl) ⟨1000637, by rfl⟩ : syracuseStep 1334183 = 2001275) B2001275
theorem B9509825 : Blo 1332985 9509825 := bstep (se 2 (by rfl) ⟨3566184, by rfl⟩ : syracuseStep 9509825 = 7132369) B7132369
theorem B1334363 : Blo 1332985 1334363 := bstep (se 1 (by rfl) ⟨1000772, by rfl⟩ : syracuseStep 1334363 = 2001545) B2001545
theorem B6757505 : Blo 1332985 6757505 := bstep (se 2 (by rfl) ⟨2534064, by rfl⟩ : syracuseStep 6757505 = 5068129) B5068129
theorem B15195275 : Blo 1332985 15195275 := bstep (se 1 (by rfl) ⟨11396456, by rfl⟩ : syracuseStep 15195275 = 22792913) B22792913
theorem B1334479 : Blo 1332985 1334479 := bstep (se 1 (by rfl) ⟨1000859, by rfl⟩ : syracuseStep 1334479 = 2001719) B2001719
theorem B1334503 : Blo 1332985 1334503 := bstep (se 1 (by rfl) ⟨1000877, by rfl⟩ : syracuseStep 1334503 = 2001755) B2001755
theorem B1334599 : Blo 1332985 1334599 := bstep (se 1 (by rfl) ⟨1000949, by rfl⟩ : syracuseStep 1334599 = 2001899) B2001899
theorem B1334735 : Blo 1332985 1334735 := bstep (se 1 (by rfl) ⟨1001051, by rfl⟩ : syracuseStep 1334735 = 2002103) B2002103
theorem B3849725 : Blo 1332985 3849725 := bstep (se 3 (by rfl) ⟨721823, by rfl⟩ : syracuseStep 3849725 = 1443647) B1443647
theorem B1334895 : Blo 1332985 1334895 := bstep (se 1 (by rfl) ⟨1001171, by rfl⟩ : syracuseStep 1334895 = 2002343) B2002343
theorem B1334951 : Blo 1332985 1334951 := bstep (se 1 (by rfl) ⟨1001213, by rfl⟩ : syracuseStep 1334951 = 2002427) B2002427
theorem B11419537 : Blo 1332985 11419537 := bstep (se 2 (by rfl) ⟨4282326, by rfl⟩ : syracuseStep 11419537 = 8564653) B8564653
theorem B6758315 : Blo 1332985 6758315 := bstep (se 1 (by rfl) ⟨5068736, by rfl⟩ : syracuseStep 6758315 = 10137473) B10137473
theorem B3375047 : Blo 1332985 3375047 := bstep (se 1 (by rfl) ⟨2531285, by rfl⟩ : syracuseStep 3375047 = 5062571) B5062571
theorem B2531483 : Blo 1332985 2531483 := bstep (se 1 (by rfl) ⟨1898612, by rfl⟩ : syracuseStep 2531483 = 3797225) B3797225
theorem B69271757 : Blo 1332985 69271757 := bstep (se 3 (by rfl) ⟨12988454, by rfl⟩ : syracuseStep 69271757 = 25976909) B25976909
theorem B2531567 : Blo 1332985 2531567 := bstep (se 1 (by rfl) ⟨1898675, by rfl⟩ : syracuseStep 2531567 = 3797351) B3797351
theorem B17572463 : Blo 1332985 17572463 := bstep (se 1 (by rfl) ⟨13179347, by rfl⟩ : syracuseStep 17572463 = 26358695) B26358695
theorem B1999679 : Blo 1332985 1999679 := bstep (se 1 (by rfl) ⟨1499759, by rfl⟩ : syracuseStep 1999679 = 2999519) B2999519
theorem B17318785 : Blo 1332985 17318785 := bstep (se 2 (by rfl) ⟨6494544, by rfl⟩ : syracuseStep 17318785 = 12989089) B12989089
theorem B1999823 : Blo 1332985 1999823 := bstep (se 1 (by rfl) ⟨1499867, by rfl⟩ : syracuseStep 1999823 = 2999735) B2999735
theorem B1999913 : Blo 1332985 1999913 := bstep (se 2 (by rfl) ⟨749967, by rfl⟩ : syracuseStep 1999913 = 1499935) B1499935
theorem B1999943 : Blo 1332985 1999943 := bstep (se 1 (by rfl) ⟨1499957, by rfl⟩ : syracuseStep 1999943 = 2999915) B2999915
theorem B3376201 : Blo 1332985 3376201 := bstep (se 2 (by rfl) ⟨1266075, by rfl⟩ : syracuseStep 3376201 = 2532151) B2532151
theorem B12174475 : Blo 1332985 12174475 := bstep (se 1 (by rfl) ⟨9130856, by rfl⟩ : syracuseStep 12174475 = 18261713) B18261713
theorem B17106167 : Blo 1332985 17106167 := bstep (se 1 (by rfl) ⟨12829625, by rfl⟩ : syracuseStep 17106167 = 25659251) B25659251
theorem B2000123 : Blo 1332985 2000123 := bstep (se 1 (by rfl) ⟨1500092, by rfl⟩ : syracuseStep 2000123 = 3000185) B3000185
theorem B10265933 : Blo 1332985 10265933 := bstep (se 3 (by rfl) ⟨1924862, by rfl⟩ : syracuseStep 10265933 = 3849725) B3849725
theorem B3040591 : Blo 1332985 3040591 := bstep (se 1 (by rfl) ⟨2280443, by rfl⟩ : syracuseStep 3040591 = 4560887) B4560887
theorem B2000411 : Blo 1332985 2000411 := bstep (se 1 (by rfl) ⟨1500308, by rfl⟩ : syracuseStep 2000411 = 3000617) B3000617
theorem B1501051 : Blo 1332985 1501051 := bstep (se 1 (by rfl) ⟨1125788, by rfl⟩ : syracuseStep 1501051 = 2251577) B2251577
theorem B2000795 : Blo 1332985 2000795 := bstep (se 1 (by rfl) ⟨1500596, by rfl⟩ : syracuseStep 2000795 = 3001193) B3001193
theorem B1501087 : Blo 1332985 1501087 := bstep (se 1 (by rfl) ⟨1125815, by rfl⟩ : syracuseStep 1501087 = 2251631) B2251631
theorem B2000831 : Blo 1332985 2000831 := bstep (se 1 (by rfl) ⟨1500623, by rfl⟩ : syracuseStep 2000831 = 3001247) B3001247
theorem B3000347 : Blo 1332985 3000347 := bstep (se 1 (by rfl) ⟨2250260, by rfl⟩ : syracuseStep 3000347 = 4500521) B4500521
theorem B18245681 : Blo 1332985 18245681 := bstep (se 2 (by rfl) ⟨6842130, by rfl⟩ : syracuseStep 18245681 = 13684261) B13684261
theorem B3000527 : Blo 1332985 3000527 := bstep (se 1 (by rfl) ⟨2250395, by rfl⟩ : syracuseStep 3000527 = 4500791) B4500791
theorem B2001455 : Blo 1332985 2001455 := bstep (se 1 (by rfl) ⟨1501091, by rfl⟩ : syracuseStep 2001455 = 3002183) B3002183
theorem B3000923 : Blo 1332985 3000923 := bstep (se 1 (by rfl) ⟨2250692, by rfl⟩ : syracuseStep 3000923 = 4501385) B4501385
theorem B3205793 : Blo 1332985 3205793 := bstep (se 2 (by rfl) ⟨1202172, by rfl⟩ : syracuseStep 3205793 = 2404345) B2404345
theorem B2001575 : Blo 1332985 2001575 := bstep (se 1 (by rfl) ⟨1501181, by rfl⟩ : syracuseStep 2001575 = 3002363) B3002363
theorem B2001641 : Blo 1332985 2001641 := bstep (se 2 (by rfl) ⟨750615, by rfl⟩ : syracuseStep 2001641 = 1501231) B1501231
theorem B2001647 : Blo 1332985 2001647 := bstep (se 1 (by rfl) ⟨1501235, by rfl⟩ : syracuseStep 2001647 = 3002471) B3002471
theorem B2001695 : Blo 1332985 2001695 := bstep (se 1 (by rfl) ⟨1501271, by rfl⟩ : syracuseStep 2001695 = 3002543) B3002543
theorem B1542943 : Blo 1332985 1542943 := bstep (se 1 (by rfl) ⟨1157207, by rfl⟩ : syracuseStep 1542943 = 2314415) B2314415
theorem B4270931 : Blo 1332985 4270931 := bstep (se 1 (by rfl) ⟨3203198, by rfl⟩ : syracuseStep 4270931 = 6406397) B6406397
theorem B3378145 : Blo 1332985 3378145 := bstep (se 2 (by rfl) ⟨1266804, by rfl⟩ : syracuseStep 3378145 = 2533609) B2533609
theorem B832236605 : Blo 1332985 832236605 := bstep (se 3 (by rfl) ⟨156044363, by rfl⟩ : syracuseStep 832236605 = 312088727) B312088727
theorem B2002025 : Blo 1332985 2002025 := bstep (se 2 (by rfl) ⟨750759, by rfl⟩ : syracuseStep 2002025 = 1501519) B1501519
theorem B2002151 : Blo 1332985 2002151 := bstep (se 1 (by rfl) ⟨1501613, by rfl⟩ : syracuseStep 2002151 = 3003227) B3003227
theorem B5066003 : Blo 1332985 5066003 := bstep (se 1 (by rfl) ⟨3799502, by rfl⟩ : syracuseStep 5066003 = 7599005) B7599005
theorem B15412679 : Blo 1332985 15412679 := bstep (se 1 (by rfl) ⟨11559509, by rfl⟩ : syracuseStep 15412679 = 23119019) B23119019
theorem B6082201 : Blo 1332985 6082201 := bstep (se 2 (by rfl) ⟨2280825, by rfl⟩ : syracuseStep 6082201 = 4561651) B4561651
theorem B6754103 : Blo 1332985 6754103 := bstep (se 1 (by rfl) ⟨5065577, by rfl⟩ : syracuseStep 6754103 = 10131155) B10131155
theorem B14413787 : Blo 1332985 14413787 := bstep (se 1 (by rfl) ⟨10810340, by rfl⟩ : syracuseStep 14413787 = 21620681) B21620681
theorem B6942829 : Blo 1332985 6942829 := bstep (se 3 (by rfl) ⟨1301780, by rfl⟩ : syracuseStep 6942829 = 2603561) B2603561
theorem B1601743 : Blo 1332985 1601743 := bstep (se 1 (by rfl) ⟨1201307, by rfl⟩ : syracuseStep 1601743 = 2402615) B2402615
theorem B8548573 : Blo 1332985 8548573 := bstep (se 3 (by rfl) ⟨1602857, by rfl⟩ : syracuseStep 8548573 = 3205715) B3205715
theorem B9613687 : Blo 1332985 9613687 := bstep (se 1 (by rfl) ⟨7210265, by rfl⟩ : syracuseStep 9613687 = 14420531) B14420531
theorem B11399737 : Blo 1332985 11399737 := bstep (se 2 (by rfl) ⟨4274901, by rfl⟩ : syracuseStep 11399737 = 8549803) B8549803
theorem B10400507 : Blo 1332985 10400507 := bstep (se 1 (by rfl) ⟨7800380, by rfl⟩ : syracuseStep 10400507 = 15600761) B15600761
theorem B10130183 : Blo 1332985 10130183 := bstep (se 1 (by rfl) ⟨7597637, by rfl⟩ : syracuseStep 10130183 = 15195275) B15195275
theorem B17331241 : Blo 1332985 17331241 := bstep (se 2 (by rfl) ⟨6499215, by rfl⟩ : syracuseStep 17331241 = 12998431) B12998431
theorem B15226049 : Blo 1332985 15226049 := bstep (se 2 (by rfl) ⟨5709768, by rfl⟩ : syracuseStep 15226049 = 11419537) B11419537
theorem B2250031 : Blo 1332985 2250031 := bstep (se 1 (by rfl) ⟨1687523, by rfl⟩ : syracuseStep 2250031 = 3375047) B3375047
theorem B4273519 : Blo 1332985 4273519 := bstep (se 1 (by rfl) ⟨3205139, by rfl⟩ : syracuseStep 4273519 = 6410279) B6410279
theorem B30799271 : Blo 1332985 30799271 := bstep (se 1 (by rfl) ⟨23099453, by rfl⟩ : syracuseStep 30799271 = 46198907) B46198907
theorem B7599689 : Blo 1332985 7599689 := bstep (se 2 (by rfl) ⟨2849883, by rfl⟩ : syracuseStep 7599689 = 5699767) B5699767
theorem B4273775 : Blo 1332985 4273775 := bstep (se 1 (by rfl) ⟨3205331, by rfl⟩ : syracuseStep 4273775 = 6410663) B6410663
theorem B14431945 : Blo 1332985 14431945 := bstep (se 2 (by rfl) ⟨5411979, by rfl⟩ : syracuseStep 14431945 = 10823959) B10823959
theorem B3798751 : Blo 1332985 3798751 := bstep (se 1 (by rfl) ⟨2849063, by rfl⟩ : syracuseStep 3798751 = 5698127) B5698127
theorem B1898311 : Blo 1332985 1898311 := bstep (se 1 (by rfl) ⟨1423733, by rfl⟩ : syracuseStep 1898311 = 2847467) B2847467
theorem B6756371 : Blo 1332985 6756371 := bstep (se 1 (by rfl) ⟨5067278, by rfl⟩ : syracuseStep 6756371 = 10134557) B10134557
theorem B2848807 : Blo 1332985 2848807 := bstep (se 1 (by rfl) ⟨2136605, by rfl⟩ : syracuseStep 2848807 = 4273211) B4273211
theorem B83269691 : Blo 1332985 83269691 := bstep (se 1 (by rfl) ⟨62452268, by rfl⟩ : syracuseStep 83269691 = 124904537) B124904537
theorem B1333375 : Blo 1332985 1333375 := bstep (se 1 (by rfl) ⟨1000031, by rfl⟩ : syracuseStep 1333375 = 2000063) B2000063
theorem B1333471 : Blo 1332985 1333471 := bstep (se 1 (by rfl) ⟨1000103, by rfl⟩ : syracuseStep 1333471 = 2000207) B2000207
theorem B2250983 : Blo 1332985 2250983 := bstep (se 1 (by rfl) ⟨1688237, by rfl⟩ : syracuseStep 2250983 = 3376475) B3376475
theorem B1333531 : Blo 1332985 1333531 := bstep (se 1 (by rfl) ⟨1000148, by rfl⟩ : syracuseStep 1333531 = 2000297) B2000297
theorem B9615647 : Blo 1332985 9615647 := bstep (se 1 (by rfl) ⟨7211735, by rfl⟩ : syracuseStep 9615647 = 14423471) B14423471
theorem B2849107 : Blo 1332985 2849107 := bstep (se 1 (by rfl) ⟨2136830, by rfl⟩ : syracuseStep 2849107 = 4273661) B4273661
theorem B7215455 : Blo 1332985 7215455 := bstep (se 1 (by rfl) ⟨5411591, by rfl⟩ : syracuseStep 7215455 = 10823183) B10823183
theorem B1333631 : Blo 1332985 1333631 := bstep (se 1 (by rfl) ⟨1000223, by rfl⟩ : syracuseStep 1333631 = 2000447) B2000447
theorem B1333659 : Blo 1332985 1333659 := bstep (se 1 (by rfl) ⟨1000244, by rfl⟩ : syracuseStep 1333659 = 2000489) B2000489
theorem B3848759 : Blo 1332985 3848759 := bstep (se 1 (by rfl) ⟨2886569, by rfl⟩ : syracuseStep 3848759 = 5773139) B5773139
theorem B1333951 : Blo 1332985 1333951 := bstep (se 1 (by rfl) ⟨1000463, by rfl⟩ : syracuseStep 1333951 = 2000927) B2000927
theorem B1334079 : Blo 1332985 1334079 := bstep (se 1 (by rfl) ⟨1000559, by rfl⟩ : syracuseStep 1334079 = 2001119) B2001119
theorem B4275031 : Blo 1332985 4275031 := bstep (se 1 (by rfl) ⟨3206273, by rfl⟩ : syracuseStep 4275031 = 6412547) B6412547
theorem B1334119 : Blo 1332985 1334119 := bstep (se 1 (by rfl) ⟨1000589, by rfl⟩ : syracuseStep 1334119 = 2001179) B2001179
theorem B98614259 : Blo 1332985 98614259 := bstep (se 1 (by rfl) ⟨73960694, by rfl⟩ : syracuseStep 98614259 = 147921389) B147921389
theorem B1334335 : Blo 1332985 1334335 := bstep (se 1 (by rfl) ⟨1000751, by rfl⟩ : syracuseStep 1334335 = 2001503) B2001503
theorem B43293761 : Blo 1332985 43293761 := bstep (se 2 (by rfl) ⟨16235160, by rfl⟩ : syracuseStep 43293761 = 32470321) B32470321
theorem B1334523 : Blo 1332985 1334523 := bstep (se 1 (by rfl) ⟨1000892, by rfl⟩ : syracuseStep 1334523 = 2001785) B2001785
theorem B1334555 : Blo 1332985 1334555 := bstep (se 1 (by rfl) ⟨1000916, by rfl⟩ : syracuseStep 1334555 = 2001833) B2001833
theorem B6339883 : Blo 1332985 6339883 := bstep (se 1 (by rfl) ⟨4754912, by rfl⟩ : syracuseStep 6339883 = 9509825) B9509825
theorem B1334655 : Blo 1332985 1334655 := bstep (se 1 (by rfl) ⟨1000991, by rfl⟩ : syracuseStep 1334655 = 2001983) B2001983
theorem B4505003 : Blo 1332985 4505003 := bstep (se 1 (by rfl) ⟨3378752, by rfl⟩ : syracuseStep 4505003 = 6757505) B6757505
theorem B6495835 : Blo 1332985 6495835 := bstep (se 1 (by rfl) ⟨4871876, by rfl⟩ : syracuseStep 6495835 = 9743753) B9743753
theorem B6758153 : Blo 1332985 6758153 := bstep (se 2 (by rfl) ⟨2534307, by rfl⟩ : syracuseStep 6758153 = 5068615) B5068615
theorem B20528909 : Blo 1332985 20528909 := bstep (se 3 (by rfl) ⟨3849170, by rfl⟩ : syracuseStep 20528909 = 7698341) B7698341
theorem B2252711 : Blo 1332985 2252711 := bstep (se 1 (by rfl) ⟨1689533, by rfl⟩ : syracuseStep 2252711 = 3379067) B3379067
theorem B9609131 : Blo 1332985 9609131 := bstep (se 1 (by rfl) ⟨7206848, by rfl⟩ : syracuseStep 9609131 = 14413697) B14413697
theorem B4505543 : Blo 1332985 4505543 := bstep (se 1 (by rfl) ⟨3379157, by rfl⟩ : syracuseStep 4505543 = 6758315) B6758315
theorem B1687655 : Blo 1332985 1687655 := bstep (se 1 (by rfl) ⟨1265741, by rfl⟩ : syracuseStep 1687655 = 2531483) B2531483
theorem B9257105 : Blo 1332985 9257105 := bstep (se 2 (by rfl) ⟨3471414, by rfl⟩ : syracuseStep 9257105 = 6942829) B6942829
theorem B1687711 : Blo 1332985 1687711 := bstep (se 1 (by rfl) ⟨1265783, by rfl⟩ : syracuseStep 1687711 = 2531567) B2531567
theorem B11714975 : Blo 1332985 11714975 := bstep (se 1 (by rfl) ⟨8786231, by rfl⟩ : syracuseStep 11714975 = 17572463) B17572463
theorem B10150699 : Blo 1332985 10150699 := bstep (se 1 (by rfl) ⟨7613024, by rfl⟩ : syracuseStep 10150699 = 15226049) B15226049
theorem B11404111 : Blo 1332985 11404111 := bstep (se 1 (by rfl) ⟨8553083, by rfl⟩ : syracuseStep 11404111 = 17106167) B17106167
theorem B2057257 : Blo 1332985 2057257 := bstep (se 2 (by rfl) ⟨771471, by rfl⟩ : syracuseStep 2057257 = 1542943) B1542943
theorem B2000231 : Blo 1332985 2000231 := bstep (se 1 (by rfl) ⟨1500173, by rfl⟩ : syracuseStep 2000231 = 3000347) B3000347
theorem B2000351 : Blo 1332985 2000351 := bstep (se 1 (by rfl) ⟨1500263, by rfl⟩ : syracuseStep 2000351 = 3000527) B3000527
theorem B1500655 : Blo 1332985 1500655 := bstep (se 1 (by rfl) ⟨1125491, by rfl⟩ : syracuseStep 1500655 = 2250983) B2250983
theorem B4810303 : Blo 1332985 4810303 := bstep (se 1 (by rfl) ⟨3607727, by rfl⟩ : syracuseStep 4810303 = 7215455) B7215455
theorem B2565839 : Blo 1332985 2565839 := bstep (se 1 (by rfl) ⟨1924379, by rfl⟩ : syracuseStep 2565839 = 3848759) B3848759
theorem B2000615 : Blo 1332985 2000615 := bstep (se 1 (by rfl) ⟨1500461, by rfl⟩ : syracuseStep 2000615 = 3000923) B3000923
theorem B3000041 : Blo 1332985 3000041 := bstep (se 2 (by rfl) ⟨1125015, by rfl⟩ : syracuseStep 3000041 = 2250031) B2250031
theorem B65742839 : Blo 1332985 65742839 := bstep (se 1 (by rfl) ⟨49307129, by rfl⟩ : syracuseStep 65742839 = 98614259) B98614259
theorem B28862507 : Blo 1332985 28862507 := bstep (se 1 (by rfl) ⟨21646880, by rfl⟩ : syracuseStep 28862507 = 43293761) B43293761
theorem B8661113 : Blo 1332985 8661113 := bstep (se 2 (by rfl) ⟨3247917, by rfl⟩ : syracuseStep 8661113 = 6495835) B6495835
theorem B3377335 : Blo 1332985 3377335 := bstep (se 1 (by rfl) ⟨2533001, by rfl⟩ : syracuseStep 3377335 = 5066003) B5066003
theorem B5065001 : Blo 1332985 5065001 := bstep (se 2 (by rfl) ⟨1899375, by rfl⟩ : syracuseStep 5065001 = 3798751) B3798751
theorem B10275119 : Blo 1332985 10275119 := bstep (se 1 (by rfl) ⟨7706339, by rfl⟩ : syracuseStep 10275119 = 15412679) B15412679
theorem B2001401 : Blo 1332985 2001401 := bstep (se 2 (by rfl) ⟨750525, by rfl⟩ : syracuseStep 2001401 = 1501051) B1501051
theorem B2001449 : Blo 1332985 2001449 := bstep (se 2 (by rfl) ⟨750543, by rfl⟩ : syracuseStep 2001449 = 1501087) B1501087
theorem B1501807 : Blo 1332985 1501807 := bstep (se 1 (by rfl) ⟨1126355, by rfl⟩ : syracuseStep 1501807 = 2252711) B2252711
theorem B46181171 : Blo 1332985 46181171 := bstep (se 1 (by rfl) ⟨34635878, by rfl⟩ : syracuseStep 46181171 = 69271757) B69271757
theorem B11398097 : Blo 1332985 11398097 := bstep (se 2 (by rfl) ⟨4274286, by rfl⟩ : syracuseStep 11398097 = 8548573) B8548573
theorem B6933671 : Blo 1332985 6933671 := bstep (se 1 (by rfl) ⟨5200253, by rfl⟩ : syracuseStep 6933671 = 10400507) B10400507
theorem B6753455 : Blo 1332985 6753455 := bstep (se 1 (by rfl) ⟨5065091, by rfl⟩ : syracuseStep 6753455 = 10130183) B10130183
theorem B15199649 : Blo 1332985 15199649 := bstep (se 2 (by rfl) ⟨5699868, by rfl⟩ : syracuseStep 15199649 = 11399737) B11399737
theorem B6843955 : Blo 1332985 6843955 := bstep (se 1 (by rfl) ⟨5132966, by rfl⟩ : syracuseStep 6843955 = 10265933) B10265933
theorem B20532847 : Blo 1332985 20532847 := bstep (se 1 (by rfl) ⟨15399635, by rfl⟩ : syracuseStep 20532847 = 30799271) B30799271
theorem B5066459 : Blo 1332985 5066459 := bstep (se 1 (by rfl) ⟨3799844, by rfl⟩ : syracuseStep 5066459 = 7599689) B7599689
theorem B55513127 : Blo 1332985 55513127 := bstep (se 1 (by rfl) ⟨41634845, by rfl⟩ : syracuseStep 55513127 = 83269691) B83269691
theorem B4501601 : Blo 1332985 4501601 := bstep (se 2 (by rfl) ⟨1688100, by rfl⟩ : syracuseStep 4501601 = 3376201) B3376201
theorem B16232633 : Blo 1332985 16232633 := bstep (se 2 (by rfl) ⟨6087237, by rfl⟩ : syracuseStep 16232633 = 12174475) B12174475
theorem B6410431 : Blo 1332985 6410431 := bstep (se 1 (by rfl) ⟨4807823, by rfl⟩ : syracuseStep 6410431 = 9615647) B9615647
theorem B5698025 : Blo 1332985 5698025 := bstep (se 2 (by rfl) ⟨2136759, by rfl⟩ : syracuseStep 5698025 = 4273519) B4273519
theorem B2847287 : Blo 1332985 2847287 := bstep (se 1 (by rfl) ⟨2135465, by rfl⟩ : syracuseStep 2847287 = 4270931) B4270931
theorem B554824403 : Blo 1332985 554824403 := bstep (se 1 (by rfl) ⟨416118302, by rfl⟩ : syracuseStep 554824403 = 832236605) B832236605
theorem B3003335 : Blo 1332985 3003335 := bstep (se 1 (by rfl) ⟨2252501, by rfl⟩ : syracuseStep 3003335 = 4505003) B4505003
theorem B13685939 : Blo 1332985 13685939 := bstep (se 1 (by rfl) ⟨10264454, by rfl⟩ : syracuseStep 13685939 = 20528909) B20528909
theorem B4502735 : Blo 1332985 4502735 := bstep (se 1 (by rfl) ⟨3377051, by rfl⟩ : syracuseStep 4502735 = 6754103) B6754103
theorem B3003695 : Blo 1332985 3003695 := bstep (se 1 (by rfl) ⟨2252771, by rfl⟩ : syracuseStep 3003695 = 4505543) B4505543
theorem B3798409 : Blo 1332985 3798409 := bstep (se 2 (by rfl) ⟨1424403, by rfl⟩ : syracuseStep 3798409 = 2848807) B2848807
theorem B2135657 : Blo 1332985 2135657 := bstep (se 2 (by rfl) ⟨800871, by rfl⟩ : syracuseStep 2135657 = 1601743) B1601743
theorem B3798809 : Blo 1332985 3798809 := bstep (se 2 (by rfl) ⟨1424553, by rfl⟩ : syracuseStep 3798809 = 2849107) B2849107
theorem B12818249 : Blo 1332985 12818249 := bstep (se 2 (by rfl) ⟨4806843, by rfl⟩ : syracuseStep 12818249 = 9613687) B9613687
theorem B1333119 : Blo 1332985 1333119 := bstep (se 1 (by rfl) ⟨999839, by rfl⟩ : syracuseStep 1333119 = 1999679) B1999679
theorem B1333215 : Blo 1332985 1333215 := bstep (se 1 (by rfl) ⟨999911, by rfl⟩ : syracuseStep 1333215 = 1999823) B1999823
theorem B1333275 : Blo 1332985 1333275 := bstep (se 1 (by rfl) ⟨999956, by rfl⟩ : syracuseStep 1333275 = 1999913) B1999913
theorem B1333295 : Blo 1332985 1333295 := bstep (se 1 (by rfl) ⟨999971, by rfl⟩ : syracuseStep 1333295 = 1999943) B1999943
theorem B1333415 : Blo 1332985 1333415 := bstep (se 1 (by rfl) ⟨1000061, by rfl⟩ : syracuseStep 1333415 = 2000123) B2000123
theorem B1333607 : Blo 1332985 1333607 := bstep (se 1 (by rfl) ⟨1000205, by rfl⟩ : syracuseStep 1333607 = 2000411) B2000411
theorem B2849183 : Blo 1332985 2849183 := bstep (se 1 (by rfl) ⟨2136887, by rfl⟩ : syracuseStep 2849183 = 4273775) B4273775
theorem B5700041 : Blo 1332985 5700041 := bstep (se 2 (by rfl) ⟨2137515, by rfl⟩ : syracuseStep 5700041 = 4275031) B4275031
theorem B23091713 : Blo 1332985 23091713 := bstep (se 2 (by rfl) ⟨8659392, by rfl⟩ : syracuseStep 23091713 = 17318785) B17318785
theorem B1333863 : Blo 1332985 1333863 := bstep (se 1 (by rfl) ⟨1000397, by rfl⟩ : syracuseStep 1333863 = 2000795) B2000795
theorem B1333887 : Blo 1332985 1333887 := bstep (se 1 (by rfl) ⟨1000415, by rfl⟩ : syracuseStep 1333887 = 2000831) B2000831
theorem B4504193 : Blo 1332985 4504193 := bstep (se 2 (by rfl) ⟨1689072, by rfl⟩ : syracuseStep 4504193 = 3378145) B3378145
theorem B4504247 : Blo 1332985 4504247 := bstep (se 1 (by rfl) ⟨3378185, by rfl⟩ : syracuseStep 4504247 = 6756371) B6756371
theorem B12163787 : Blo 1332985 12163787 := bstep (se 1 (by rfl) ⟨9122840, by rfl⟩ : syracuseStep 12163787 = 18245681) B18245681
theorem B23108321 : Blo 1332985 23108321 := bstep (se 2 (by rfl) ⟨8665620, by rfl⟩ : syracuseStep 23108321 = 17331241) B17331241
theorem B1334303 : Blo 1332985 1334303 := bstep (se 1 (by rfl) ⟨1000727, by rfl⟩ : syracuseStep 1334303 = 2001455) B2001455
theorem B8453177 : Blo 1332985 8453177 := bstep (se 2 (by rfl) ⟨3169941, by rfl⟩ : syracuseStep 8453177 = 6339883) B6339883
theorem B4054121 : Blo 1332985 4054121 := bstep (se 2 (by rfl) ⟨1520295, by rfl⟩ : syracuseStep 4054121 = 3040591) B3040591
theorem B2137195 : Blo 1332985 2137195 := bstep (se 1 (by rfl) ⟨1602896, by rfl⟩ : syracuseStep 2137195 = 3205793) B3205793
theorem B1334383 : Blo 1332985 1334383 := bstep (se 1 (by rfl) ⟨1000787, by rfl⟩ : syracuseStep 1334383 = 2001575) B2001575
theorem B1334427 : Blo 1332985 1334427 := bstep (se 1 (by rfl) ⟨1000820, by rfl⟩ : syracuseStep 1334427 = 2001641) B2001641
theorem B1334431 : Blo 1332985 1334431 := bstep (se 1 (by rfl) ⟨1000823, by rfl⟩ : syracuseStep 1334431 = 2001647) B2001647
theorem B1334463 : Blo 1332985 1334463 := bstep (se 1 (by rfl) ⟨1000847, by rfl⟩ : syracuseStep 1334463 = 2001695) B2001695
theorem B1334683 : Blo 1332985 1334683 := bstep (se 1 (by rfl) ⟨1001012, by rfl⟩ : syracuseStep 1334683 = 2002025) B2002025
theorem B1334767 : Blo 1332985 1334767 := bstep (se 1 (by rfl) ⟨1001075, by rfl⟩ : syracuseStep 1334767 = 2002151) B2002151
theorem B8109601 : Blo 1332985 8109601 := bstep (se 2 (by rfl) ⟨3041100, by rfl⟩ : syracuseStep 8109601 = 6082201) B6082201
theorem B19242593 : Blo 1332985 19242593 := bstep (se 2 (by rfl) ⟨7215972, by rfl⟩ : syracuseStep 19242593 = 14431945) B14431945
theorem B2531081 : Blo 1332985 2531081 := bstep (se 2 (by rfl) ⟨949155, by rfl⟩ : syracuseStep 2531081 = 1898311) B1898311
theorem B25624349 : Blo 1332985 25624349 := bstep (se 3 (by rfl) ⟨4804565, by rfl⟩ : syracuseStep 25624349 = 9609131) B9609131
theorem B4505435 : Blo 1332985 4505435 := bstep (se 1 (by rfl) ⟨3379076, by rfl⟩ : syracuseStep 4505435 = 6758153) B6758153
theorem B9609191 : Blo 1332985 9609191 := bstep (se 1 (by rfl) ⟨7206893, by rfl⟩ : syracuseStep 9609191 = 14413787) B14413787
theorem B10821755 : Blo 1332985 10821755 := bstep (se 1 (by rfl) ⟨8116316, by rfl⟩ : syracuseStep 10821755 = 16232633) B16232633
theorem B13534265 : Blo 1332985 13534265 := bstep (se 2 (by rfl) ⟨5075349, by rfl⟩ : syracuseStep 13534265 = 10150699) B10150699
theorem B15205481 : Blo 1332985 15205481 := bstep (se 2 (by rfl) ⟨5702055, by rfl⟩ : syracuseStep 15205481 = 11404111) B11404111
theorem B2000027 : Blo 1332985 2000027 := bstep (se 1 (by rfl) ⟨1500020, by rfl⟩ : syracuseStep 2000027 = 3000041) B3000041
theorem B2532539 : Blo 1332985 2532539 := bstep (se 1 (by rfl) ⟨1899404, by rfl⟩ : syracuseStep 2532539 = 3798809) B3798809
theorem B8545499 : Blo 1332985 8545499 := bstep (se 1 (by rfl) ⟨6409124, by rfl⟩ : syracuseStep 8545499 = 12818249) B12818249
theorem B43828559 : Blo 1332985 43828559 := bstep (se 1 (by rfl) ⟨32871419, by rfl⟩ : syracuseStep 43828559 = 65742839) B65742839
theorem B3376667 : Blo 1332985 3376667 := bstep (se 1 (by rfl) ⟨2532500, by rfl⟩ : syracuseStep 3376667 = 5065001) B5065001
theorem B6850079 : Blo 1332985 6850079 := bstep (se 1 (by rfl) ⟨5137559, by rfl⟩ : syracuseStep 6850079 = 10275119) B10275119
theorem B5695085 : Blo 1332985 5695085 := bstep (se 3 (by rfl) ⟨1067828, by rfl⟩ : syracuseStep 5695085 = 2135657) B2135657
theorem B15394475 : Blo 1332985 15394475 := bstep (se 1 (by rfl) ⟨11545856, by rfl⟩ : syracuseStep 15394475 = 23091713) B23091713
theorem B5064545 : Blo 1332985 5064545 := bstep (se 2 (by rfl) ⟨1899204, by rfl⟩ : syracuseStep 5064545 = 3798409) B3798409
theorem B30787447 : Blo 1332985 30787447 := bstep (se 1 (by rfl) ⟨23090585, by rfl⟩ : syracuseStep 30787447 = 46181171) B46181171
theorem B2000873 : Blo 1332985 2000873 := bstep (se 2 (by rfl) ⟨750327, by rfl⟩ : syracuseStep 2000873 = 1500655) B1500655
theorem B4622447 : Blo 1332985 4622447 := bstep (se 1 (by rfl) ⟨3466835, by rfl⟩ : syracuseStep 4622447 = 6933671) B6933671
theorem B3377639 : Blo 1332985 3377639 := bstep (se 1 (by rfl) ⟨2533229, by rfl⟩ : syracuseStep 3377639 = 5066459) B5066459
theorem B17082899 : Blo 1332985 17082899 := bstep (se 1 (by rfl) ⟨12812174, by rfl⟩ : syracuseStep 17082899 = 25624349) B25624349
theorem B3001067 : Blo 1332985 3001067 := bstep (se 1 (by rfl) ⟨2250800, by rfl⟩ : syracuseStep 3001067 = 4501601) B4501601
theorem B6171403 : Blo 1332985 6171403 := bstep (se 1 (by rfl) ⟨4628552, by rfl⟩ : syracuseStep 6171403 = 9257105) B9257105
theorem B10972037 : Blo 1332985 10972037 := bstep (se 4 (by rfl) ⟨1028628, by rfl⟩ : syracuseStep 10972037 = 2057257) B2057257
theorem B8547241 : Blo 1332985 8547241 := bstep (se 2 (by rfl) ⟨3205215, by rfl⟩ : syracuseStep 8547241 = 6410431) B6410431
theorem B4500413 : Blo 1332985 4500413 := bstep (se 3 (by rfl) ⟨843827, by rfl⟩ : syracuseStep 4500413 = 1687655) B1687655
theorem B7809983 : Blo 1332985 7809983 := bstep (se 1 (by rfl) ⟨5857487, by rfl⟩ : syracuseStep 7809983 = 11714975) B11714975
theorem B2002223 : Blo 1332985 2002223 := bstep (se 1 (by rfl) ⟨1501667, by rfl⟩ : syracuseStep 2002223 = 3003335) B3003335
theorem B3001823 : Blo 1332985 3001823 := bstep (se 1 (by rfl) ⟨2251367, by rfl⟩ : syracuseStep 3001823 = 4502735) B4502735
theorem B2002409 : Blo 1332985 2002409 := bstep (se 2 (by rfl) ⟨750903, by rfl⟩ : syracuseStep 2002409 = 1501807) B1501807
theorem B2002463 : Blo 1332985 2002463 := bstep (se 1 (by rfl) ⟨1501847, by rfl⟩ : syracuseStep 2002463 = 3003695) B3003695
theorem B3002795 : Blo 1332985 3002795 := bstep (se 1 (by rfl) ⟨2252096, by rfl⟩ : syracuseStep 3002795 = 4504193) B4504193
theorem B3002831 : Blo 1332985 3002831 := bstep (se 1 (by rfl) ⟨2252123, by rfl⟩ : syracuseStep 3002831 = 4504247) B4504247
theorem B15405547 : Blo 1332985 15405547 := bstep (se 1 (by rfl) ⟨11554160, by rfl⟩ : syracuseStep 15405547 = 23108321) B23108321
theorem B7598731 : Blo 1332985 7598731 := bstep (se 1 (by rfl) ⟨5699048, by rfl⟩ : syracuseStep 7598731 = 11398097) B11398097
theorem B4502303 : Blo 1332985 4502303 := bstep (se 1 (by rfl) ⟨3376727, by rfl⟩ : syracuseStep 4502303 = 6753455) B6753455
theorem B3003623 : Blo 1332985 3003623 := bstep (se 1 (by rfl) ⟨2252717, by rfl⟩ : syracuseStep 3003623 = 4505435) B4505435
theorem B37008751 : Blo 1332985 37008751 := bstep (se 1 (by rfl) ⟨27756563, by rfl⟩ : syracuseStep 37008751 = 55513127) B55513127
theorem B43251205 : Blo 1332985 43251205 := bstep (se 4 (by rfl) ⟨4054800, by rfl⟩ : syracuseStep 43251205 = 8109601) B8109601
theorem B2250281 : Blo 1332985 2250281 := bstep (se 2 (by rfl) ⟨843855, by rfl⟩ : syracuseStep 2250281 = 1687711) B1687711
theorem B4503113 : Blo 1332985 4503113 := bstep (se 2 (by rfl) ⟨1688667, by rfl⟩ : syracuseStep 4503113 = 3377335) B3377335
theorem B3798683 : Blo 1332985 3798683 := bstep (se 1 (by rfl) ⟨2849012, by rfl⟩ : syracuseStep 3798683 = 5698025) B5698025
theorem B1898191 : Blo 1332985 1898191 := bstep (se 1 (by rfl) ⟨1423643, by rfl⟩ : syracuseStep 1898191 = 2847287) B2847287
theorem B369882935 : Blo 1332985 369882935 := bstep (se 1 (by rfl) ⟨277412201, by rfl⟩ : syracuseStep 369882935 = 554824403) B554824403
theorem B9123959 : Blo 1332985 9123959 := bstep (se 1 (by rfl) ⟨6842969, by rfl⟩ : syracuseStep 9123959 = 13685939) B13685939
theorem B1333487 : Blo 1332985 1333487 := bstep (se 1 (by rfl) ⟨1000115, by rfl⟩ : syracuseStep 1333487 = 2000231) B2000231
theorem B1333567 : Blo 1332985 1333567 := bstep (se 1 (by rfl) ⟨1000175, by rfl⟩ : syracuseStep 1333567 = 2000351) B2000351
theorem B1710559 : Blo 1332985 1710559 := bstep (se 1 (by rfl) ⟨1282919, by rfl⟩ : syracuseStep 1710559 = 2565839) B2565839
theorem B1333743 : Blo 1332985 1333743 := bstep (se 1 (by rfl) ⟨1000307, by rfl⟩ : syracuseStep 1333743 = 2000615) B2000615
theorem B19241671 : Blo 1332985 19241671 := bstep (se 1 (by rfl) ⟨14431253, by rfl⟩ : syracuseStep 19241671 = 28862507) B28862507
theorem B5774075 : Blo 1332985 5774075 := bstep (se 1 (by rfl) ⟨4330556, by rfl⟩ : syracuseStep 5774075 = 8661113) B8661113
theorem B2849593 : Blo 1332985 2849593 := bstep (se 2 (by rfl) ⟨1068597, by rfl⟩ : syracuseStep 2849593 = 2137195) B2137195
theorem B1899455 : Blo 1332985 1899455 := bstep (se 1 (by rfl) ⟨1424591, by rfl⟩ : syracuseStep 1899455 = 2849183) B2849183
theorem B3800027 : Blo 1332985 3800027 := bstep (se 1 (by rfl) ⟨2850020, by rfl⟩ : syracuseStep 3800027 = 5700041) B5700041
theorem B1334267 : Blo 1332985 1334267 := bstep (se 1 (by rfl) ⟨1000700, by rfl⟩ : syracuseStep 1334267 = 2001401) B2001401
theorem B1334299 : Blo 1332985 1334299 := bstep (se 1 (by rfl) ⟨1000724, by rfl⟩ : syracuseStep 1334299 = 2001449) B2001449
theorem B8109191 : Blo 1332985 8109191 := bstep (se 1 (by rfl) ⟨6081893, by rfl⟩ : syracuseStep 8109191 = 12163787) B12163787
theorem B5635451 : Blo 1332985 5635451 := bstep (se 1 (by rfl) ⟨4226588, by rfl⟩ : syracuseStep 5635451 = 8453177) B8453177
theorem B9125273 : Blo 1332985 9125273 := bstep (se 2 (by rfl) ⟨3421977, by rfl⟩ : syracuseStep 9125273 = 6843955) B6843955
theorem B2702747 : Blo 1332985 2702747 := bstep (se 1 (by rfl) ⟨2027060, by rfl⟩ : syracuseStep 2702747 = 4054121) B4054121
theorem B6413737 : Blo 1332985 6413737 := bstep (se 2 (by rfl) ⟨2405151, by rfl⟩ : syracuseStep 6413737 = 4810303) B4810303
theorem B27377129 : Blo 1332985 27377129 := bstep (se 2 (by rfl) ⟨10266423, by rfl⟩ : syracuseStep 27377129 = 20532847) B20532847
theorem B10133099 : Blo 1332985 10133099 := bstep (se 1 (by rfl) ⟨7599824, by rfl⟩ : syracuseStep 10133099 = 15199649) B15199649
theorem B12828395 : Blo 1332985 12828395 := bstep (se 1 (by rfl) ⟨9621296, by rfl⟩ : syracuseStep 12828395 = 19242593) B19242593
theorem B1687387 : Blo 1332985 1687387 := bstep (se 1 (by rfl) ⟨1265540, by rfl⟩ : syracuseStep 1687387 = 2531081) B2531081
theorem B6406127 : Blo 1332985 6406127 := bstep (se 1 (by rfl) ⟨4804595, by rfl⟩ : syracuseStep 6406127 = 9609191) B9609191
theorem B24330557 : Blo 1332985 24330557 := bstep (se 3 (by rfl) ⟨4561979, by rfl⟩ : syracuseStep 24330557 = 9123959) B9123959
theorem B1688359 : Blo 1332985 1688359 := bstep (se 1 (by rfl) ⟨1266269, by rfl⟩ : syracuseStep 1688359 = 2532539) B2532539
theorem B1500187 : Blo 1332985 1500187 := bstep (se 1 (by rfl) ⟨1125140, by rfl⟩ : syracuseStep 1500187 = 2250281) B2250281
theorem B2532455 : Blo 1332985 2532455 := bstep (se 1 (by rfl) ⟨1899341, by rfl⟩ : syracuseStep 2532455 = 3798683) B3798683
theorem B246588623 : Blo 1332985 246588623 := bstep (se 1 (by rfl) ⟨184941467, by rfl⟩ : syracuseStep 246588623 = 369882935) B369882935
theorem B11396321 : Blo 1332985 11396321 := bstep (se 2 (by rfl) ⟨4273620, by rfl⟩ : syracuseStep 11396321 = 8547241) B8547241
theorem B3376363 : Blo 1332985 3376363 := bstep (se 1 (by rfl) ⟨2532272, by rfl⟩ : syracuseStep 3376363 = 5064545) B5064545
theorem B11388599 : Blo 1332985 11388599 := bstep (se 1 (by rfl) ⟨8541449, by rfl⟩ : syracuseStep 11388599 = 17082899) B17082899
theorem B2000711 : Blo 1332985 2000711 := bstep (se 1 (by rfl) ⟨1500533, by rfl⟩ : syracuseStep 2000711 = 3001067) B3001067
theorem B3000275 : Blo 1332985 3000275 := bstep (se 1 (by rfl) ⟨2250206, by rfl⟩ : syracuseStep 3000275 = 4500413) B4500413
theorem B2533351 : Blo 1332985 2533351 := bstep (se 1 (by rfl) ⟨1900013, by rfl⟩ : syracuseStep 2533351 = 3800027) B3800027
theorem B2001215 : Blo 1332985 2001215 := bstep (se 1 (by rfl) ⟨1500911, by rfl⟩ : syracuseStep 2001215 = 3001823) B3001823
theorem B5065213 : Blo 1332985 5065213 := bstep (se 3 (by rfl) ⟨949727, by rfl⟩ : syracuseStep 5065213 = 1899455) B1899455
theorem B4270751 : Blo 1332985 4270751 := bstep (se 1 (by rfl) ⟨3203063, by rfl⟩ : syracuseStep 4270751 = 6406127) B6406127
theorem B2001863 : Blo 1332985 2001863 := bstep (se 1 (by rfl) ⟨1501397, by rfl⟩ : syracuseStep 2001863 = 3002795) B3002795
theorem B2001887 : Blo 1332985 2001887 := bstep (se 1 (by rfl) ⟨1501415, by rfl⟩ : syracuseStep 2001887 = 3002831) B3002831
theorem B3001535 : Blo 1332985 3001535 := bstep (se 1 (by rfl) ⟨2251151, by rfl⟩ : syracuseStep 3001535 = 4502303) B4502303
theorem B2280745 : Blo 1332985 2280745 := bstep (se 2 (by rfl) ⟨855279, by rfl⟩ : syracuseStep 2280745 = 1710559) B1710559
theorem B20540729 : Blo 1332985 20540729 := bstep (se 2 (by rfl) ⟨7702773, by rfl⟩ : syracuseStep 20540729 = 15405547) B15405547
theorem B9022843 : Blo 1332985 9022843 := bstep (se 1 (by rfl) ⟨6767132, by rfl⟩ : syracuseStep 9022843 = 13534265) B13534265
theorem B10136987 : Blo 1332985 10136987 := bstep (se 1 (by rfl) ⟨7602740, by rfl⟩ : syracuseStep 10136987 = 15205481) B15205481
theorem B5696999 : Blo 1332985 5696999 := bstep (se 1 (by rfl) ⟨4272749, by rfl⟩ : syracuseStep 5696999 = 8545499) B8545499
theorem B2002415 : Blo 1332985 2002415 := bstep (se 1 (by rfl) ⟨1501811, by rfl⟩ : syracuseStep 2002415 = 3003623) B3003623
theorem B15027869 : Blo 1332985 15027869 := bstep (se 3 (by rfl) ⟨2817725, by rfl⟩ : syracuseStep 15027869 = 5635451) B5635451
theorem B8228537 : Blo 1332985 8228537 := bstep (se 2 (by rfl) ⟨3085701, by rfl⟩ : syracuseStep 8228537 = 6171403) B6171403
theorem B4566719 : Blo 1332985 4566719 := bstep (se 1 (by rfl) ⟨3425039, by rfl⟩ : syracuseStep 4566719 = 6850079) B6850079
theorem B3002075 : Blo 1332985 3002075 := bstep (se 1 (by rfl) ⟨2251556, by rfl⟩ : syracuseStep 3002075 = 4503113) B4503113
theorem B3796723 : Blo 1332985 3796723 := bstep (se 1 (by rfl) ⟨2847542, by rfl⟩ : syracuseStep 3796723 = 5695085) B5695085
theorem B49345001 : Blo 1332985 49345001 := bstep (se 2 (by rfl) ⟨18504375, by rfl⟩ : syracuseStep 49345001 = 37008751) B37008751
theorem B5206655 : Blo 1332985 5206655 := bstep (se 1 (by rfl) ⟨3904991, by rfl⟩ : syracuseStep 5206655 = 7809983) B7809983
theorem B57668273 : Blo 1332985 57668273 := bstep (se 2 (by rfl) ⟨21625602, by rfl⟩ : syracuseStep 57668273 = 43251205) B43251205
theorem B6083515 : Blo 1332985 6083515 := bstep (se 1 (by rfl) ⟨4562636, by rfl⟩ : syracuseStep 6083515 = 9125273) B9125273
theorem B29258765 : Blo 1332985 29258765 := bstep (se 3 (by rfl) ⟨5486018, by rfl⟩ : syracuseStep 29258765 = 10972037) B10972037
theorem B6755399 : Blo 1332985 6755399 := bstep (se 1 (by rfl) ⟨5066549, by rfl⟩ : syracuseStep 6755399 = 10133099) B10133099
theorem B2249849 : Blo 1332985 2249849 := bstep (se 2 (by rfl) ⟨843693, by rfl⟩ : syracuseStep 2249849 = 1687387) B1687387
theorem B7214503 : Blo 1332985 7214503 := bstep (se 1 (by rfl) ⟨5410877, by rfl⟩ : syracuseStep 7214503 = 10821755) B10821755
theorem B12326525 : Blo 1332985 12326525 := bstep (se 3 (by rfl) ⟨2311223, by rfl⟩ : syracuseStep 12326525 = 4622447) B4622447
theorem B21624509 : Blo 1332985 21624509 := bstep (se 3 (by rfl) ⟨4054595, by rfl⟩ : syracuseStep 21624509 = 8109191) B8109191
theorem B1333351 : Blo 1332985 1333351 := bstep (se 1 (by rfl) ⟨1000013, by rfl⟩ : syracuseStep 1333351 = 2000027) B2000027
theorem B10131641 : Blo 1332985 10131641 := bstep (se 2 (by rfl) ⟨3799365, by rfl⟩ : syracuseStep 10131641 = 7598731) B7598731
theorem B29219039 : Blo 1332985 29219039 := bstep (se 1 (by rfl) ⟨21914279, by rfl⟩ : syracuseStep 29219039 = 43828559) B43828559
theorem B25655561 : Blo 1332985 25655561 := bstep (se 2 (by rfl) ⟨9620835, by rfl⟩ : syracuseStep 25655561 = 19241671) B19241671
theorem B2251111 : Blo 1332985 2251111 := bstep (se 1 (by rfl) ⟨1688333, by rfl⟩ : syracuseStep 2251111 = 3376667) B3376667
theorem B7207325 : Blo 1332985 7207325 := bstep (se 3 (by rfl) ⟨1351373, by rfl⟩ : syracuseStep 7207325 = 2702747) B2702747
theorem B3799457 : Blo 1332985 3799457 := bstep (se 2 (by rfl) ⟨1424796, by rfl⟩ : syracuseStep 3799457 = 2849593) B2849593
theorem B10262983 : Blo 1332985 10262983 := bstep (se 1 (by rfl) ⟨7697237, by rfl⟩ : syracuseStep 10262983 = 15394475) B15394475
theorem B1333915 : Blo 1332985 1333915 := bstep (se 1 (by rfl) ⟨1000436, by rfl⟩ : syracuseStep 1333915 = 2000873) B2000873
theorem B2251759 : Blo 1332985 2251759 := bstep (se 1 (by rfl) ⟨1688819, by rfl⟩ : syracuseStep 2251759 = 3377639) B3377639
theorem B3849383 : Blo 1332985 3849383 := bstep (se 1 (by rfl) ⟨2887037, by rfl⟩ : syracuseStep 3849383 = 5774075) B5774075
theorem B8551649 : Blo 1332985 8551649 := bstep (se 2 (by rfl) ⟨3206868, by rfl⟩ : syracuseStep 8551649 = 6413737) B6413737
theorem B34209053 : Blo 1332985 34209053 := bstep (se 3 (by rfl) ⟨6414197, by rfl⟩ : syracuseStep 34209053 = 12828395) B12828395
theorem B1334815 : Blo 1332985 1334815 := bstep (se 1 (by rfl) ⟨1001111, by rfl⟩ : syracuseStep 1334815 = 2002223) B2002223
theorem B2530921 : Blo 1332985 2530921 := bstep (se 2 (by rfl) ⟨949095, by rfl⟩ : syracuseStep 2530921 = 1898191) B1898191
theorem B18251419 : Blo 1332985 18251419 := bstep (se 1 (by rfl) ⟨13688564, by rfl⟩ : syracuseStep 18251419 = 27377129) B27377129
theorem B1334939 : Blo 1332985 1334939 := bstep (se 1 (by rfl) ⟨1001204, by rfl⟩ : syracuseStep 1334939 = 2002409) B2002409
theorem B1334975 : Blo 1332985 1334975 := bstep (se 1 (by rfl) ⟨1001231, by rfl⟩ : syracuseStep 1334975 = 2002463) B2002463
theorem B41049929 : Blo 1332985 41049929 := bstep (se 2 (by rfl) ⟨15393723, by rfl⟩ : syracuseStep 41049929 = 30787447) B30787447
theorem B16220371 : Blo 1332985 16220371 := bstep (se 1 (by rfl) ⟨12165278, by rfl⟩ : syracuseStep 16220371 = 24330557) B24330557
theorem B38445515 : Blo 1332985 38445515 := bstep (se 1 (by rfl) ⟨28834136, by rfl⟩ : syracuseStep 38445515 = 57668273) B57668273
theorem B19505843 : Blo 1332985 19505843 := bstep (se 1 (by rfl) ⟨14629382, by rfl⟩ : syracuseStep 19505843 = 29258765) B29258765
theorem B1688303 : Blo 1332985 1688303 := bstep (se 1 (by rfl) ⟨1266227, by rfl⟩ : syracuseStep 1688303 = 2532455) B2532455
theorem B1499899 : Blo 1332985 1499899 := bstep (se 1 (by rfl) ⟨1124924, by rfl⟩ : syracuseStep 1499899 = 2249849) B2249849
theorem B8217683 : Blo 1332985 8217683 := bstep (se 1 (by rfl) ⟨6163262, by rfl⟩ : syracuseStep 8217683 = 12326525) B12326525
theorem B8111353 : Blo 1332985 8111353 := bstep (se 2 (by rfl) ⟨3041757, by rfl⟩ : syracuseStep 8111353 = 6083515) B6083515
theorem B2000183 : Blo 1332985 2000183 := bstep (se 1 (by rfl) ⟨1500137, by rfl⟩ : syracuseStep 2000183 = 3000275) B3000275
theorem B2000249 : Blo 1332985 2000249 := bstep (se 2 (by rfl) ⟨750093, by rfl⟩ : syracuseStep 2000249 = 1500187) B1500187
theorem B2532971 : Blo 1332985 2532971 := bstep (se 1 (by rfl) ⟨1899728, by rfl⟩ : syracuseStep 2532971 = 3799457) B3799457
theorem B3040993 : Blo 1332985 3040993 := bstep (se 2 (by rfl) ⟨1140372, by rfl⟩ : syracuseStep 3040993 = 2280745) B2280745
theorem B9619337 : Blo 1332985 9619337 := bstep (se 2 (by rfl) ⟨3607251, by rfl⟩ : syracuseStep 9619337 = 7214503) B7214503
theorem B2566255 : Blo 1332985 2566255 := bstep (se 1 (by rfl) ⟨1924691, by rfl⟩ : syracuseStep 2566255 = 3849383) B3849383
theorem B2001023 : Blo 1332985 2001023 := bstep (se 1 (by rfl) ⟨1500767, by rfl⟩ : syracuseStep 2001023 = 3001535) B3001535
theorem B2001383 : Blo 1332985 2001383 := bstep (se 1 (by rfl) ⟨1501037, by rfl⟩ : syracuseStep 2001383 = 3002075) B3002075
theorem B3377801 : Blo 1332985 3377801 := bstep (se 2 (by rfl) ⟨1266675, by rfl⟩ : syracuseStep 3377801 = 2533351) B2533351
theorem B3001481 : Blo 1332985 3001481 := bstep (se 2 (by rfl) ⟨1125555, by rfl⟩ : syracuseStep 3001481 = 2251111) B2251111
theorem B13683977 : Blo 1332985 13683977 := bstep (se 2 (by rfl) ⟨5131491, by rfl⟩ : syracuseStep 13683977 = 10262983) B10262983
theorem B6753617 : Blo 1332985 6753617 := bstep (se 2 (by rfl) ⟨2532606, by rfl⟩ : syracuseStep 6753617 = 5065213) B5065213
theorem B164392415 : Blo 1332985 164392415 := bstep (se 1 (by rfl) ⟨123294311, by rfl⟩ : syracuseStep 164392415 = 246588623) B246588623
theorem B7597547 : Blo 1332985 7597547 := bstep (se 1 (by rfl) ⟨5698160, by rfl⟩ : syracuseStep 7597547 = 11396321) B11396321
theorem B3002345 : Blo 1332985 3002345 := bstep (se 2 (by rfl) ⟨1125879, by rfl⟩ : syracuseStep 3002345 = 2251759) B2251759
theorem B6754427 : Blo 1332985 6754427 := bstep (se 1 (by rfl) ⟨5065820, by rfl⟩ : syracuseStep 6754427 = 10131641) B10131641
theorem B4804883 : Blo 1332985 4804883 := bstep (se 1 (by rfl) ⟨3603662, by rfl⟩ : syracuseStep 4804883 = 7207325) B7207325
theorem B4501817 : Blo 1332985 4501817 := bstep (se 2 (by rfl) ⟨1688181, by rfl⟩ : syracuseStep 4501817 = 3376363) B3376363
theorem B2847167 : Blo 1332985 2847167 := bstep (se 1 (by rfl) ⟨2135375, by rfl⟩ : syracuseStep 2847167 = 4270751) B4270751
theorem B12030457 : Blo 1332985 12030457 := bstep (se 2 (by rfl) ⟨4511421, by rfl⟩ : syracuseStep 12030457 = 9022843) B9022843
theorem B24335225 : Blo 1332985 24335225 := bstep (se 2 (by rfl) ⟨9125709, by rfl⟩ : syracuseStep 24335225 = 18251419) B18251419
theorem B13693819 : Blo 1332985 13693819 := bstep (se 1 (by rfl) ⟨10270364, by rfl⟩ : syracuseStep 13693819 = 20540729) B20540729
theorem B3797999 : Blo 1332985 3797999 := bstep (se 1 (by rfl) ⟨2848499, by rfl⟩ : syracuseStep 3797999 = 5696999) B5696999
theorem B5485691 : Blo 1332985 5485691 := bstep (se 1 (by rfl) ⟨4114268, by rfl⟩ : syracuseStep 5485691 = 8228537) B8228537
theorem B3044479 : Blo 1332985 3044479 := bstep (se 1 (by rfl) ⟨2283359, by rfl⟩ : syracuseStep 3044479 = 4566719) B4566719
theorem B27366619 : Blo 1332985 27366619 := bstep (se 1 (by rfl) ⟨20524964, by rfl⟩ : syracuseStep 27366619 = 41049929) B41049929
theorem B32896667 : Blo 1332985 32896667 := bstep (se 1 (by rfl) ⟨24672500, by rfl⟩ : syracuseStep 32896667 = 49345001) B49345001
theorem B3471103 : Blo 1332985 3471103 := bstep (se 1 (by rfl) ⟨2603327, by rfl⟩ : syracuseStep 3471103 = 5206655) B5206655
theorem B4503599 : Blo 1332985 4503599 := bstep (se 1 (by rfl) ⟨3377699, by rfl⟩ : syracuseStep 4503599 = 6755399) B6755399
theorem B2251145 : Blo 1332985 2251145 := bstep (se 2 (by rfl) ⟨844179, by rfl⟩ : syracuseStep 2251145 = 1688359) B1688359
theorem B7592399 : Blo 1332985 7592399 := bstep (se 1 (by rfl) ⟨5694299, by rfl⟩ : syracuseStep 7592399 = 11388599) B11388599
theorem B14416339 : Blo 1332985 14416339 := bstep (se 1 (by rfl) ⟨10812254, by rfl⟩ : syracuseStep 14416339 = 21624509) B21624509
theorem B1333807 : Blo 1332985 1333807 := bstep (se 1 (by rfl) ⟨1000355, by rfl⟩ : syracuseStep 1333807 = 2000711) B2000711
theorem B19479359 : Blo 1332985 19479359 := bstep (se 1 (by rfl) ⟨14609519, by rfl⟩ : syracuseStep 19479359 = 29219039) B29219039
theorem B17103707 : Blo 1332985 17103707 := bstep (se 1 (by rfl) ⟨12827780, by rfl⟩ : syracuseStep 17103707 = 25655561) B25655561
theorem B1334143 : Blo 1332985 1334143 := bstep (se 1 (by rfl) ⟨1000607, by rfl⟩ : syracuseStep 1334143 = 2001215) B2001215
theorem B1334575 : Blo 1332985 1334575 := bstep (se 1 (by rfl) ⟨1000931, by rfl⟩ : syracuseStep 1334575 = 2001863) B2001863
theorem B1334591 : Blo 1332985 1334591 := bstep (se 1 (by rfl) ⟨1000943, by rfl⟩ : syracuseStep 1334591 = 2001887) B2001887
theorem B3374561 : Blo 1332985 3374561 := bstep (se 2 (by rfl) ⟨1265460, by rfl⟩ : syracuseStep 3374561 = 2530921) B2530921
theorem B5701099 : Blo 1332985 5701099 := bstep (se 1 (by rfl) ⟨4275824, by rfl⟩ : syracuseStep 5701099 = 8551649) B8551649
theorem B22806035 : Blo 1332985 22806035 := bstep (se 1 (by rfl) ⟨17104526, by rfl⟩ : syracuseStep 22806035 = 34209053) B34209053
theorem B6757991 : Blo 1332985 6757991 := bstep (se 1 (by rfl) ⟨5068493, by rfl⟩ : syracuseStep 6757991 = 10136987) B10136987
theorem B5062297 : Blo 1332985 5062297 := bstep (se 2 (by rfl) ⟨1898361, by rfl⟩ : syracuseStep 5062297 = 3796723) B3796723
theorem B1334943 : Blo 1332985 1334943 := bstep (se 1 (by rfl) ⟨1001207, by rfl⟩ : syracuseStep 1334943 = 2002415) B2002415
theorem B10018579 : Blo 1332985 10018579 := bstep (se 1 (by rfl) ⟨7513934, by rfl⟩ : syracuseStep 10018579 = 15027869) B15027869
theorem B3203255 : Blo 1332985 3203255 := bstep (se 1 (by rfl) ⟨2402441, by rfl⟩ : syracuseStep 3203255 = 4804883) B4804883
theorem B21627161 : Blo 1332985 21627161 := bstep (se 2 (by rfl) ⟨8110185, by rfl⟩ : syracuseStep 21627161 = 16220371) B16220371
theorem B2531999 : Blo 1332985 2531999 := bstep (se 1 (by rfl) ⟨1898999, by rfl⟩ : syracuseStep 2531999 = 3797999) B3797999
theorem B16040609 : Blo 1332985 16040609 := bstep (se 2 (by rfl) ⟨6015228, by rfl⟩ : syracuseStep 16040609 = 12030457) B12030457
theorem B1999865 : Blo 1332985 1999865 := bstep (se 2 (by rfl) ⟨749949, by rfl⟩ : syracuseStep 1999865 = 1499899) B1499899
theorem B21931111 : Blo 1332985 21931111 := bstep (se 1 (by rfl) ⟨16448333, by rfl⟩ : syracuseStep 21931111 = 32896667) B32896667
theorem B1500763 : Blo 1332985 1500763 := bstep (se 1 (by rfl) ⟨1125572, by rfl⟩ : syracuseStep 1500763 = 2251145) B2251145
theorem B36488825 : Blo 1332985 36488825 := bstep (se 2 (by rfl) ⟨13683309, by rfl⟩ : syracuseStep 36488825 = 27366619) B27366619
theorem B10815137 : Blo 1332985 10815137 := bstep (se 2 (by rfl) ⟨4055676, by rfl⟩ : syracuseStep 10815137 = 8111353) B8111353
theorem B12986239 : Blo 1332985 12986239 := bstep (se 1 (by rfl) ⟨9739679, by rfl⟩ : syracuseStep 12986239 = 19479359) B19479359
theorem B2000987 : Blo 1332985 2000987 := bstep (se 1 (by rfl) ⟨1500740, by rfl⟩ : syracuseStep 2000987 = 3001481) B3001481
theorem B109594943 : Blo 1332985 109594943 := bstep (se 1 (by rfl) ⟨82196207, by rfl⟩ : syracuseStep 109594943 = 164392415) B164392415
theorem B5065031 : Blo 1332985 5065031 := bstep (se 1 (by rfl) ⟨3798773, by rfl⟩ : syracuseStep 5065031 = 7597547) B7597547
theorem B25651565 : Blo 1332985 25651565 := bstep (se 3 (by rfl) ⟨4809668, by rfl⟩ : syracuseStep 25651565 = 9619337) B9619337
theorem B2001563 : Blo 1332985 2001563 := bstep (se 1 (by rfl) ⟨1501172, by rfl⟩ : syracuseStep 2001563 = 3002345) B3002345
theorem B3001211 : Blo 1332985 3001211 := bstep (se 1 (by rfl) ⟨2250908, by rfl⟩ : syracuseStep 3001211 = 4501817) B4501817
theorem B13003895 : Blo 1332985 13003895 := bstep (se 1 (by rfl) ⟨9752921, by rfl⟩ : syracuseStep 13003895 = 19505843) B19505843
theorem B16223483 : Blo 1332985 16223483 := bstep (se 1 (by rfl) ⟨12167612, by rfl⟩ : syracuseStep 16223483 = 24335225) B24335225
theorem B19221785 : Blo 1332985 19221785 := bstep (se 2 (by rfl) ⟨7208169, by rfl⟩ : syracuseStep 19221785 = 14416339) B14416339
theorem B3002399 : Blo 1332985 3002399 := bstep (se 1 (by rfl) ⟨2251799, by rfl⟩ : syracuseStep 3002399 = 4503599) B4503599
theorem B4059305 : Blo 1332985 4059305 := bstep (se 2 (by rfl) ⟨1522239, by rfl⟩ : syracuseStep 4059305 = 3044479) B3044479
theorem B6754589 : Blo 1332985 6754589 := bstep (se 3 (by rfl) ⟨1266485, by rfl⟩ : syracuseStep 6754589 = 2532971) B2532971
theorem B4502141 : Blo 1332985 4502141 := bstep (se 3 (by rfl) ⟨844151, by rfl⟩ : syracuseStep 4502141 = 1688303) B1688303
theorem B9122651 : Blo 1332985 9122651 := bstep (se 1 (by rfl) ⟨6841988, by rfl⟩ : syracuseStep 9122651 = 13683977) B13683977
theorem B4502411 : Blo 1332985 4502411 := bstep (se 1 (by rfl) ⟨3376808, by rfl⟩ : syracuseStep 4502411 = 6753617) B6753617
theorem B2249707 : Blo 1332985 2249707 := bstep (se 1 (by rfl) ⟨1687280, by rfl⟩ : syracuseStep 2249707 = 3374561) B3374561
theorem B13358105 : Blo 1332985 13358105 := bstep (se 2 (by rfl) ⟨5009289, by rfl⟩ : syracuseStep 13358105 = 10018579) B10018579
theorem B4502951 : Blo 1332985 4502951 := bstep (se 1 (by rfl) ⟨3377213, by rfl⟩ : syracuseStep 4502951 = 6754427) B6754427
theorem B3421673 : Blo 1332985 3421673 := bstep (se 2 (by rfl) ⟨1283127, by rfl⟩ : syracuseStep 3421673 = 2566255) B2566255
theorem B1898111 : Blo 1332985 1898111 := bstep (se 1 (by rfl) ⟨1423583, by rfl⟩ : syracuseStep 1898111 = 2847167) B2847167
theorem B25630343 : Blo 1332985 25630343 := bstep (se 1 (by rfl) ⟨19222757, by rfl⟩ : syracuseStep 25630343 = 38445515) B38445515
theorem B14628509 : Blo 1332985 14628509 := bstep (se 3 (by rfl) ⟨2742845, by rfl⟩ : syracuseStep 14628509 = 5485691) B5485691
theorem B5478455 : Blo 1332985 5478455 := bstep (se 1 (by rfl) ⟨4108841, by rfl⟩ : syracuseStep 5478455 = 8217683) B8217683
theorem B1333455 : Blo 1332985 1333455 := bstep (se 1 (by rfl) ⟨1000091, by rfl⟩ : syracuseStep 1333455 = 2000183) B2000183
theorem B1333499 : Blo 1332985 1333499 := bstep (se 1 (by rfl) ⟨1000124, by rfl⟩ : syracuseStep 1333499 = 2000249) B2000249
theorem B18258425 : Blo 1332985 18258425 := bstep (se 2 (by rfl) ⟨6846909, by rfl⟩ : syracuseStep 18258425 = 13693819) B13693819
theorem B1334015 : Blo 1332985 1334015 := bstep (se 1 (by rfl) ⟨1000511, by rfl⟩ : syracuseStep 1334015 = 2001023) B2001023
theorem B5061599 : Blo 1332985 5061599 := bstep (se 1 (by rfl) ⟨3796199, by rfl⟩ : syracuseStep 5061599 = 7592399) B7592399
theorem B1334255 : Blo 1332985 1334255 := bstep (se 1 (by rfl) ⟨1000691, by rfl⟩ : syracuseStep 1334255 = 2001383) B2001383
theorem B2251867 : Blo 1332985 2251867 := bstep (se 1 (by rfl) ⟨1688900, by rfl⟩ : syracuseStep 2251867 = 3377801) B3377801
theorem B11402471 : Blo 1332985 11402471 := bstep (se 1 (by rfl) ⟨8551853, by rfl⟩ : syracuseStep 11402471 = 17103707) B17103707
theorem B7601465 : Blo 1332985 7601465 := bstep (se 2 (by rfl) ⟨2850549, by rfl⟩ : syracuseStep 7601465 = 5701099) B5701099
theorem B6749729 : Blo 1332985 6749729 := bstep (se 2 (by rfl) ⟨2531148, by rfl⟩ : syracuseStep 6749729 = 5062297) B5062297
theorem B4054657 : Blo 1332985 4054657 := bstep (se 2 (by rfl) ⟨1520496, by rfl⟩ : syracuseStep 4054657 = 3040993) B3040993
theorem B4628137 : Blo 1332985 4628137 := bstep (se 2 (by rfl) ⟨1735551, by rfl⟩ : syracuseStep 4628137 = 3471103) B3471103
theorem B15204023 : Blo 1332985 15204023 := bstep (se 1 (by rfl) ⟨11403017, by rfl⟩ : syracuseStep 15204023 = 22806035) B22806035
theorem B4505327 : Blo 1332985 4505327 := bstep (se 1 (by rfl) ⟨3378995, by rfl⟩ : syracuseStep 4505327 = 6757991) B6757991
theorem B14418107 : Blo 1332985 14418107 := bstep (se 1 (by rfl) ⟨10813580, by rfl⟩ : syracuseStep 14418107 = 21627161) B21627161
theorem B8905403 : Blo 1332985 8905403 := bstep (se 1 (by rfl) ⟨6679052, by rfl⟩ : syracuseStep 8905403 = 13358105) B13358105
theorem B7210091 : Blo 1332985 7210091 := bstep (se 1 (by rfl) ⟨5407568, by rfl⟩ : syracuseStep 7210091 = 10815137) B10815137
theorem B2999609 : Blo 1332985 2999609 := bstep (se 2 (by rfl) ⟨1124853, by rfl⟩ : syracuseStep 2999609 = 2249707) B2249707
theorem B3376687 : Blo 1332985 3376687 := bstep (se 1 (by rfl) ⟨2532515, by rfl⟩ : syracuseStep 3376687 = 5065031) B5065031
theorem B6751997 : Blo 1332985 6751997 := bstep (se 3 (by rfl) ⟨1265999, by rfl⟩ : syracuseStep 6751997 = 2531999) B2531999
theorem B2000807 : Blo 1332985 2000807 := bstep (se 1 (by rfl) ⟨1500605, by rfl⟩ : syracuseStep 2000807 = 3001211) B3001211
theorem B8669263 : Blo 1332985 8669263 := bstep (se 1 (by rfl) ⟨6501947, by rfl⟩ : syracuseStep 8669263 = 13003895) B13003895
theorem B2001017 : Blo 1332985 2001017 := bstep (se 2 (by rfl) ⟨750381, by rfl⟩ : syracuseStep 2001017 = 1500763) B1500763
theorem B10815655 : Blo 1332985 10815655 := bstep (se 1 (by rfl) ⟨8111741, by rfl⟩ : syracuseStep 10815655 = 16223483) B16223483
theorem B12814523 : Blo 1332985 12814523 := bstep (se 1 (by rfl) ⟨9610892, by rfl⟩ : syracuseStep 12814523 = 19221785) B19221785
theorem B6170849 : Blo 1332985 6170849 := bstep (se 2 (by rfl) ⟨2314068, by rfl⟩ : syracuseStep 6170849 = 4628137) B4628137
theorem B4499819 : Blo 1332985 4499819 := bstep (se 1 (by rfl) ⟨3374864, by rfl⟩ : syracuseStep 4499819 = 6749729) B6749729
theorem B10136015 : Blo 1332985 10136015 := bstep (se 1 (by rfl) ⟨7602011, by rfl⟩ : syracuseStep 10136015 = 15204023) B15204023
theorem B2001599 : Blo 1332985 2001599 := bstep (se 1 (by rfl) ⟨1501199, by rfl⟩ : syracuseStep 2001599 = 3002399) B3002399
theorem B2706203 : Blo 1332985 2706203 := bstep (se 1 (by rfl) ⟨2029652, by rfl⟩ : syracuseStep 2706203 = 4059305) B4059305
theorem B3001427 : Blo 1332985 3001427 := bstep (se 1 (by rfl) ⟨2251070, by rfl⟩ : syracuseStep 3001427 = 4502141) B4502141
theorem B10693739 : Blo 1332985 10693739 := bstep (se 1 (by rfl) ⟨8020304, by rfl⟩ : syracuseStep 10693739 = 16040609) B16040609
theorem B6081767 : Blo 1332985 6081767 := bstep (se 1 (by rfl) ⟨4561325, by rfl⟩ : syracuseStep 6081767 = 9122651) B9122651
theorem B3001607 : Blo 1332985 3001607 := bstep (se 1 (by rfl) ⟨2251205, by rfl⟩ : syracuseStep 3001607 = 4502411) B4502411
theorem B3001967 : Blo 1332985 3001967 := bstep (se 1 (by rfl) ⟨2251475, by rfl⟩ : syracuseStep 3001967 = 4502951) B4502951
theorem B2281115 : Blo 1332985 2281115 := bstep (se 1 (by rfl) ⟨1710836, by rfl⟩ : syracuseStep 2281115 = 3421673) B3421673
theorem B24325883 : Blo 1332985 24325883 := bstep (se 1 (by rfl) ⟨18244412, by rfl⟩ : syracuseStep 24325883 = 36488825) B36488825
theorem B9752339 : Blo 1332985 9752339 := bstep (se 1 (by rfl) ⟨7314254, by rfl⟩ : syracuseStep 9752339 = 14628509) B14628509
theorem B3002489 : Blo 1332985 3002489 := bstep (se 2 (by rfl) ⟨1125933, by rfl⟩ : syracuseStep 3002489 = 2251867) B2251867
theorem B29241481 : Blo 1332985 29241481 := bstep (se 2 (by rfl) ⟨10965555, by rfl⟩ : syracuseStep 29241481 = 21931111) B21931111
theorem B17101043 : Blo 1332985 17101043 := bstep (se 1 (by rfl) ⟨12825782, by rfl⟩ : syracuseStep 17101043 = 25651565) B25651565
theorem B5067643 : Blo 1332985 5067643 := bstep (se 1 (by rfl) ⟨3800732, by rfl⟩ : syracuseStep 5067643 = 7601465) B7601465
theorem B3003551 : Blo 1332985 3003551 := bstep (se 1 (by rfl) ⟨2252663, by rfl⟩ : syracuseStep 3003551 = 4505327) B4505327
theorem B17314985 : Blo 1332985 17314985 := bstep (se 2 (by rfl) ⟨6493119, by rfl⟩ : syracuseStep 17314985 = 12986239) B12986239
theorem B2135503 : Blo 1332985 2135503 := bstep (se 1 (by rfl) ⟨1601627, by rfl⟩ : syracuseStep 2135503 = 3203255) B3203255
theorem B4503059 : Blo 1332985 4503059 := bstep (se 1 (by rfl) ⟨3377294, by rfl⟩ : syracuseStep 4503059 = 6754589) B6754589
theorem B1333243 : Blo 1332985 1333243 := bstep (se 1 (by rfl) ⟨999932, by rfl⟩ : syracuseStep 1333243 = 1999865) B1999865
theorem B17086895 : Blo 1332985 17086895 := bstep (se 1 (by rfl) ⟨12815171, by rfl⟩ : syracuseStep 17086895 = 25630343) B25630343
theorem B3652303 : Blo 1332985 3652303 := bstep (se 1 (by rfl) ⟨2739227, by rfl⟩ : syracuseStep 3652303 = 5478455) B5478455
theorem B1333991 : Blo 1332985 1333991 := bstep (se 1 (by rfl) ⟨1000493, by rfl⟩ : syracuseStep 1333991 = 2000987) B2000987
theorem B73063295 : Blo 1332985 73063295 := bstep (se 1 (by rfl) ⟨54797471, by rfl⟩ : syracuseStep 73063295 = 109594943) B109594943
theorem B12172283 : Blo 1332985 12172283 := bstep (se 1 (by rfl) ⟨9129212, by rfl⟩ : syracuseStep 12172283 = 18258425) B18258425
theorem B5061629 : Blo 1332985 5061629 := bstep (se 3 (by rfl) ⟨949055, by rfl⟩ : syracuseStep 5061629 = 1898111) B1898111
theorem B1334375 : Blo 1332985 1334375 := bstep (se 1 (by rfl) ⟨1000781, by rfl⟩ : syracuseStep 1334375 = 2001563) B2001563
theorem B3374399 : Blo 1332985 3374399 := bstep (se 1 (by rfl) ⟨2530799, by rfl⟩ : syracuseStep 3374399 = 5061599) B5061599
theorem B7601647 : Blo 1332985 7601647 := bstep (se 1 (by rfl) ⟨5701235, by rfl⟩ : syracuseStep 7601647 = 11402471) B11402471
theorem B5406209 : Blo 1332985 5406209 := bstep (se 2 (by rfl) ⟨2027328, by rfl⟩ : syracuseStep 5406209 = 4054657) B4054657
theorem B11559017 : Blo 1332985 11559017 := bstep (se 2 (by rfl) ⟨4334631, by rfl⟩ : syracuseStep 11559017 = 8669263) B8669263
theorem B19226909 : Blo 1332985 19226909 := bstep (se 3 (by rfl) ⟨3605045, by rfl⟩ : syracuseStep 19226909 = 7210091) B7210091
theorem B28516637 : Blo 1332985 28516637 := bstep (se 3 (by rfl) ⟨5346869, by rfl⟩ : syracuseStep 28516637 = 10693739) B10693739
theorem B11543323 : Blo 1332985 11543323 := bstep (se 1 (by rfl) ⟨8657492, by rfl⟩ : syracuseStep 11543323 = 17314985) B17314985
theorem B1999739 : Blo 1332985 1999739 := bstep (se 1 (by rfl) ⟨1499804, by rfl⟩ : syracuseStep 1999739 = 2999609) B2999609
theorem B4113899 : Blo 1332985 4113899 := bstep (se 1 (by rfl) ⟨3085424, by rfl⟩ : syracuseStep 4113899 = 6170849) B6170849
theorem B2999879 : Blo 1332985 2999879 := bstep (se 1 (by rfl) ⟨2249909, by rfl⟩ : syracuseStep 2999879 = 4499819) B4499819
theorem B1804135 : Blo 1332985 1804135 := bstep (se 1 (by rfl) ⟨1353101, by rfl⟩ : syracuseStep 1804135 = 2706203) B2706203
theorem B10135529 : Blo 1332985 10135529 := bstep (se 2 (by rfl) ⟨3800823, by rfl⟩ : syracuseStep 10135529 = 7601647) B7601647
theorem B2000951 : Blo 1332985 2000951 := bstep (se 1 (by rfl) ⟨1500713, by rfl⟩ : syracuseStep 2000951 = 3001427) B3001427
theorem B2001071 : Blo 1332985 2001071 := bstep (se 1 (by rfl) ⟨1500803, by rfl⟩ : syracuseStep 2001071 = 3001607) B3001607
theorem B2001311 : Blo 1332985 2001311 := bstep (se 1 (by rfl) ⟨1500983, by rfl⟩ : syracuseStep 2001311 = 3001967) B3001967
theorem B11389349 : Blo 1332985 11389349 := bstep (se 4 (by rfl) ⟨1067751, by rfl⟩ : syracuseStep 11389349 = 2135503) B2135503
theorem B2001659 : Blo 1332985 2001659 := bstep (se 1 (by rfl) ⟨1501244, by rfl⟩ : syracuseStep 2001659 = 3002489) B3002489
theorem B9612071 : Blo 1332985 9612071 := bstep (se 1 (by rfl) ⟨7209053, by rfl⟩ : syracuseStep 9612071 = 14418107) B14418107
theorem B38988641 : Blo 1332985 38988641 := bstep (se 2 (by rfl) ⟨14620740, by rfl⟩ : syracuseStep 38988641 = 29241481) B29241481
theorem B14420873 : Blo 1332985 14420873 := bstep (se 2 (by rfl) ⟨5407827, by rfl⟩ : syracuseStep 14420873 = 10815655) B10815655
theorem B2002367 : Blo 1332985 2002367 := bstep (se 1 (by rfl) ⟨1501775, by rfl⟩ : syracuseStep 2002367 = 3003551) B3003551
theorem B4869737 : Blo 1332985 4869737 := bstep (se 2 (by rfl) ⟨1826151, by rfl⟩ : syracuseStep 4869737 = 3652303) B3652303
theorem B3002039 : Blo 1332985 3002039 := bstep (se 1 (by rfl) ⟨2251529, by rfl⟩ : syracuseStep 3002039 = 4503059) B4503059
theorem B4501331 : Blo 1332985 4501331 := bstep (se 1 (by rfl) ⟨3375998, by rfl⟩ : syracuseStep 4501331 = 6751997) B6751997
theorem B11391263 : Blo 1332985 11391263 := bstep (se 1 (by rfl) ⟨8543447, by rfl⟩ : syracuseStep 11391263 = 17086895) B17086895
theorem B8114855 : Blo 1332985 8114855 := bstep (se 1 (by rfl) ⟨6086141, by rfl⟩ : syracuseStep 8114855 = 12172283) B12172283
theorem B4502249 : Blo 1332985 4502249 := bstep (se 2 (by rfl) ⟨1688343, by rfl⟩ : syracuseStep 4502249 = 3376687) B3376687
theorem B2249599 : Blo 1332985 2249599 := bstep (se 1 (by rfl) ⟨1687199, by rfl⟩ : syracuseStep 2249599 = 3374399) B3374399
theorem B1520743 : Blo 1332985 1520743 := bstep (se 1 (by rfl) ⟨1140557, by rfl⟩ : syracuseStep 1520743 = 2281115) B2281115
theorem B16217255 : Blo 1332985 16217255 := bstep (se 1 (by rfl) ⟨12162941, by rfl⟩ : syracuseStep 16217255 = 24325883) B24325883
theorem B6501559 : Blo 1332985 6501559 := bstep (se 1 (by rfl) ⟨4876169, by rfl⟩ : syracuseStep 6501559 = 9752339) B9752339
theorem B11400695 : Blo 1332985 11400695 := bstep (se 1 (by rfl) ⟨8550521, by rfl⟩ : syracuseStep 11400695 = 17101043) B17101043
theorem B5936935 : Blo 1332985 5936935 := bstep (se 1 (by rfl) ⟨4452701, by rfl⟩ : syracuseStep 5936935 = 8905403) B8905403
theorem B6756857 : Blo 1332985 6756857 := bstep (se 2 (by rfl) ⟨2533821, by rfl⟩ : syracuseStep 6756857 = 5067643) B5067643
theorem B1333871 : Blo 1332985 1333871 := bstep (se 1 (by rfl) ⟨1000403, by rfl⟩ : syracuseStep 1333871 = 2000807) B2000807
theorem B1334011 : Blo 1332985 1334011 := bstep (se 1 (by rfl) ⟨1000508, by rfl⟩ : syracuseStep 1334011 = 2001017) B2001017
theorem B8543015 : Blo 1332985 8543015 := bstep (se 1 (by rfl) ⟨6407261, by rfl⟩ : syracuseStep 8543015 = 12814523) B12814523
theorem B6757343 : Blo 1332985 6757343 := bstep (se 1 (by rfl) ⟨5068007, by rfl⟩ : syracuseStep 6757343 = 10136015) B10136015
theorem B1334399 : Blo 1332985 1334399 := bstep (se 1 (by rfl) ⟨1000799, by rfl⟩ : syracuseStep 1334399 = 2001599) B2001599
theorem B48708863 : Blo 1332985 48708863 := bstep (se 1 (by rfl) ⟨36531647, by rfl⟩ : syracuseStep 48708863 = 73063295) B73063295
theorem B3374419 : Blo 1332985 3374419 := bstep (se 1 (by rfl) ⟨2530814, by rfl⟩ : syracuseStep 3374419 = 5061629) B5061629
theorem B4054511 : Blo 1332985 4054511 := bstep (se 1 (by rfl) ⟨3040883, by rfl⟩ : syracuseStep 4054511 = 6081767) B6081767
theorem B3604139 : Blo 1332985 3604139 := bstep (se 1 (by rfl) ⟨2703104, by rfl⟩ : syracuseStep 3604139 = 5406209) B5406209
theorem B7594175 : Blo 1332985 7594175 := bstep (se 1 (by rfl) ⟨5695631, by rfl⟩ : syracuseStep 7594175 = 11391263) B11391263
theorem B1999919 : Blo 1332985 1999919 := bstep (se 1 (by rfl) ⟨1499939, by rfl⟩ : syracuseStep 1999919 = 2999879) B2999879
theorem B2999465 : Blo 1332985 2999465 := bstep (se 2 (by rfl) ⟨1124799, by rfl⟩ : syracuseStep 2999465 = 2249599) B2249599
theorem B8668745 : Blo 1332985 8668745 := bstep (se 2 (by rfl) ⟨3250779, by rfl⟩ : syracuseStep 8668745 = 6501559) B6501559
theorem B86558453 : Blo 1332985 86558453 := bstep (se 5 (by rfl) ⟨4057427, by rfl⟩ : syracuseStep 86558453 = 8114855) B8114855
theorem B4499225 : Blo 1332985 4499225 := bstep (se 2 (by rfl) ⟨1687209, by rfl⟩ : syracuseStep 4499225 = 3374419) B3374419
theorem B5695343 : Blo 1332985 5695343 := bstep (se 1 (by rfl) ⟨4271507, by rfl⟩ : syracuseStep 5695343 = 8543015) B8543015
theorem B6408047 : Blo 1332985 6408047 := bstep (se 1 (by rfl) ⟨4806035, by rfl⟩ : syracuseStep 6408047 = 9612071) B9612071
theorem B38455661 : Blo 1332985 38455661 := bstep (se 3 (by rfl) ⟨7210436, by rfl⟩ : syracuseStep 38455661 = 14420873) B14420873
theorem B7915913 : Blo 1332985 7915913 := bstep (se 2 (by rfl) ⟨2968467, by rfl⟩ : syracuseStep 7915913 = 5936935) B5936935
theorem B3246491 : Blo 1332985 3246491 := bstep (se 1 (by rfl) ⟨2434868, by rfl⟩ : syracuseStep 3246491 = 4869737) B4869737
theorem B2402759 : Blo 1332985 2402759 := bstep (se 1 (by rfl) ⟨1802069, by rfl⟩ : syracuseStep 2402759 = 3604139) B3604139
theorem B2001359 : Blo 1332985 2001359 := bstep (se 1 (by rfl) ⟨1501019, by rfl⟩ : syracuseStep 2001359 = 3002039) B3002039
theorem B3000887 : Blo 1332985 3000887 := bstep (se 1 (by rfl) ⟨2250665, by rfl⟩ : syracuseStep 3000887 = 4501331) B4501331
theorem B3001499 : Blo 1332985 3001499 := bstep (se 1 (by rfl) ⟨2251124, by rfl⟩ : syracuseStep 3001499 = 4502249) B4502249
theorem B2027657 : Blo 1332985 2027657 := bstep (se 2 (by rfl) ⟨760371, by rfl⟩ : syracuseStep 2027657 = 1520743) B1520743
theorem B2405513 : Blo 1332985 2405513 := bstep (se 2 (by rfl) ⟨902067, by rfl⟩ : syracuseStep 2405513 = 1804135) B1804135
theorem B7706011 : Blo 1332985 7706011 := bstep (se 1 (by rfl) ⟨5779508, by rfl⟩ : syracuseStep 7706011 = 11559017) B11559017
theorem B12817939 : Blo 1332985 12817939 := bstep (se 1 (by rfl) ⟨9613454, by rfl⟩ : syracuseStep 12817939 = 19226909) B19226909
theorem B1333159 : Blo 1332985 1333159 := bstep (se 1 (by rfl) ⟨999869, by rfl⟩ : syracuseStep 1333159 = 1999739) B1999739
theorem B76044365 : Blo 1332985 76044365 := bstep (se 3 (by rfl) ⟨14258318, by rfl⟩ : syracuseStep 76044365 = 28516637) B28516637
theorem B10811503 : Blo 1332985 10811503 := bstep (se 1 (by rfl) ⟨8108627, by rfl⟩ : syracuseStep 10811503 = 16217255) B16217255
theorem B2742599 : Blo 1332985 2742599 := bstep (se 1 (by rfl) ⟨2056949, by rfl⟩ : syracuseStep 2742599 = 4113899) B4113899
theorem B7600463 : Blo 1332985 7600463 := bstep (se 1 (by rfl) ⟨5700347, by rfl⟩ : syracuseStep 7600463 = 11400695) B11400695
theorem B15391097 : Blo 1332985 15391097 := bstep (se 2 (by rfl) ⟨5771661, by rfl⟩ : syracuseStep 15391097 = 11543323) B11543323
theorem B6757019 : Blo 1332985 6757019 := bstep (se 1 (by rfl) ⟨5067764, by rfl⟩ : syracuseStep 6757019 = 10135529) B10135529
theorem B1333967 : Blo 1332985 1333967 := bstep (se 1 (by rfl) ⟨1000475, by rfl⟩ : syracuseStep 1333967 = 2000951) B2000951
theorem B1334047 : Blo 1332985 1334047 := bstep (se 1 (by rfl) ⟨1000535, by rfl⟩ : syracuseStep 1334047 = 2001071) B2001071
theorem B1334207 : Blo 1332985 1334207 := bstep (se 1 (by rfl) ⟨1000655, by rfl⟩ : syracuseStep 1334207 = 2001311) B2001311
theorem B7592899 : Blo 1332985 7592899 := bstep (se 1 (by rfl) ⟨5694674, by rfl⟩ : syracuseStep 7592899 = 11389349) B11389349
theorem B4504571 : Blo 1332985 4504571 := bstep (se 1 (by rfl) ⟨3378428, by rfl⟩ : syracuseStep 4504571 = 6756857) B6756857
theorem B1334439 : Blo 1332985 1334439 := bstep (se 1 (by rfl) ⟨1000829, by rfl⟩ : syracuseStep 1334439 = 2001659) B2001659
theorem B25992427 : Blo 1332985 25992427 := bstep (se 1 (by rfl) ⟨19494320, by rfl⟩ : syracuseStep 25992427 = 38988641) B38988641
theorem B4504895 : Blo 1332985 4504895 := bstep (se 1 (by rfl) ⟨3378671, by rfl⟩ : syracuseStep 4504895 = 6757343) B6757343
theorem B32472575 : Blo 1332985 32472575 := bstep (se 1 (by rfl) ⟨24354431, by rfl⟩ : syracuseStep 32472575 = 48708863) B48708863
theorem B1334911 : Blo 1332985 1334911 := bstep (se 1 (by rfl) ⟨1001183, by rfl⟩ : syracuseStep 1334911 = 2002367) B2002367
theorem B2703007 : Blo 1332985 2703007 := bstep (se 1 (by rfl) ⟨2027255, by rfl⟩ : syracuseStep 2703007 = 4054511) B4054511
theorem B1351771 : Blo 1332985 1351771 := bstep (se 1 (by rfl) ⟨1013828, by rfl⟩ : syracuseStep 1351771 = 2027657) B2027657
theorem B5062783 : Blo 1332985 5062783 := bstep (se 1 (by rfl) ⟨3797087, by rfl⟩ : syracuseStep 5062783 = 7594175) B7594175
theorem B1999643 : Blo 1332985 1999643 := bstep (se 1 (by rfl) ⟨1499732, by rfl⟩ : syracuseStep 1999643 = 2999465) B2999465
theorem B57705635 : Blo 1332985 57705635 := bstep (se 1 (by rfl) ⟨43279226, by rfl⟩ : syracuseStep 57705635 = 86558453) B86558453
theorem B2999483 : Blo 1332985 2999483 := bstep (se 1 (by rfl) ⟨2249612, by rfl⟩ : syracuseStep 2999483 = 4499225) B4499225
theorem B1828399 : Blo 1332985 1828399 := bstep (se 1 (by rfl) ⟨1371299, by rfl⟩ : syracuseStep 1828399 = 2742599) B2742599
theorem B5277275 : Blo 1332985 5277275 := bstep (se 1 (by rfl) ⟨3957956, by rfl⟩ : syracuseStep 5277275 = 7915913) B7915913
theorem B2164327 : Blo 1332985 2164327 := bstep (se 1 (by rfl) ⟨1623245, by rfl⟩ : syracuseStep 2164327 = 3246491) B3246491
theorem B2000591 : Blo 1332985 2000591 := bstep (se 1 (by rfl) ⟨1500443, by rfl⟩ : syracuseStep 2000591 = 3000887) B3000887
theorem B10274681 : Blo 1332985 10274681 := bstep (se 2 (by rfl) ⟨3853005, by rfl⟩ : syracuseStep 10274681 = 7706011) B7706011
theorem B17090585 : Blo 1332985 17090585 := bstep (se 2 (by rfl) ⟨6408969, by rfl⟩ : syracuseStep 17090585 = 12817939) B12817939
theorem B2000999 : Blo 1332985 2000999 := bstep (se 1 (by rfl) ⟨1500749, by rfl⟩ : syracuseStep 2000999 = 3001499) B3001499
theorem B5779163 : Blo 1332985 5779163 := bstep (se 1 (by rfl) ⟨4334372, by rfl⟩ : syracuseStep 5779163 = 8668745) B8668745
theorem B3796895 : Blo 1332985 3796895 := bstep (se 1 (by rfl) ⟨2847671, by rfl⟩ : syracuseStep 3796895 = 5695343) B5695343
theorem B4272031 : Blo 1332985 4272031 := bstep (se 1 (by rfl) ⟨3204023, by rfl⟩ : syracuseStep 4272031 = 6408047) B6408047
theorem B50696243 : Blo 1332985 50696243 := bstep (se 1 (by rfl) ⟨38022182, by rfl⟩ : syracuseStep 50696243 = 76044365) B76044365
theorem B5066975 : Blo 1332985 5066975 := bstep (se 1 (by rfl) ⟨3800231, by rfl⟩ : syracuseStep 5066975 = 7600463) B7600463
theorem B25637107 : Blo 1332985 25637107 := bstep (se 1 (by rfl) ⟨19227830, by rfl⟩ : syracuseStep 25637107 = 38455661) B38455661
theorem B10260731 : Blo 1332985 10260731 := bstep (se 1 (by rfl) ⟨7695548, by rfl⟩ : syracuseStep 10260731 = 15391097) B15391097
theorem B1601839 : Blo 1332985 1601839 := bstep (se 1 (by rfl) ⟨1201379, by rfl⟩ : syracuseStep 1601839 = 2402759) B2402759
theorem B34656569 : Blo 1332985 34656569 := bstep (se 2 (by rfl) ⟨12996213, by rfl⟩ : syracuseStep 34656569 = 25992427) B25992427
theorem B3003047 : Blo 1332985 3003047 := bstep (se 1 (by rfl) ⟨2252285, by rfl⟩ : syracuseStep 3003047 = 4504571) B4504571
theorem B3003263 : Blo 1332985 3003263 := bstep (se 1 (by rfl) ⟨2252447, by rfl⟩ : syracuseStep 3003263 = 4504895) B4504895
theorem B21648383 : Blo 1332985 21648383 := bstep (se 1 (by rfl) ⟨16236287, by rfl⟩ : syracuseStep 21648383 = 32472575) B32472575
theorem B14415337 : Blo 1332985 14415337 := bstep (se 2 (by rfl) ⟨5405751, by rfl⟩ : syracuseStep 14415337 = 10811503) B10811503
theorem B1333279 : Blo 1332985 1333279 := bstep (se 1 (by rfl) ⟨999959, by rfl⟩ : syracuseStep 1333279 = 1999919) B1999919
theorem B1603675 : Blo 1332985 1603675 := bstep (se 1 (by rfl) ⟨1202756, by rfl⟩ : syracuseStep 1603675 = 2405513) B2405513
theorem B10123865 : Blo 1332985 10123865 := bstep (se 2 (by rfl) ⟨3796449, by rfl⟩ : syracuseStep 10123865 = 7592899) B7592899
theorem B1334239 : Blo 1332985 1334239 := bstep (se 1 (by rfl) ⟨1000679, by rfl⟩ : syracuseStep 1334239 = 2001359) B2001359
theorem B4504679 : Blo 1332985 4504679 := bstep (se 1 (by rfl) ⟨3378509, by rfl⟩ : syracuseStep 4504679 = 6757019) B6757019
theorem B3604009 : Blo 1332985 3604009 := bstep (se 2 (by rfl) ⟨1351503, by rfl⟩ : syracuseStep 3604009 = 2703007) B2703007
theorem B2138233 : Blo 1332985 2138233 := bstep (se 2 (by rfl) ⟨801837, by rfl⟩ : syracuseStep 2138233 = 1603675) B1603675
theorem B6840487 : Blo 1332985 6840487 := bstep (se 1 (by rfl) ⟨5130365, by rfl⟩ : syracuseStep 6840487 = 10260731) B10260731
theorem B6750377 : Blo 1332985 6750377 := bstep (se 2 (by rfl) ⟨2531391, by rfl⟩ : syracuseStep 6750377 = 5062783) B5062783
theorem B11543077 : Blo 1332985 11543077 := bstep (se 4 (by rfl) ⟨1082163, by rfl⟩ : syracuseStep 11543077 = 2164327) B2164327
theorem B38470423 : Blo 1332985 38470423 := bstep (se 1 (by rfl) ⟨28852817, by rfl⟩ : syracuseStep 38470423 = 57705635) B57705635
theorem B1999655 : Blo 1332985 1999655 := bstep (se 1 (by rfl) ⟨1499741, by rfl⟩ : syracuseStep 1999655 = 2999483) B2999483
theorem B6849787 : Blo 1332985 6849787 := bstep (se 1 (by rfl) ⟨5137340, by rfl⟩ : syracuseStep 6849787 = 10274681) B10274681
theorem B28837781 : Blo 1332985 28837781 := bstep (se 6 (by rfl) ⟨675885, by rfl⟩ : syracuseStep 28837781 = 1351771) B1351771
theorem B22784165 : Blo 1332985 22784165 := bstep (se 4 (by rfl) ⟨2136015, by rfl⟩ : syracuseStep 22784165 = 4272031) B4272031
theorem B3852775 : Blo 1332985 3852775 := bstep (se 1 (by rfl) ⟨2889581, by rfl⟩ : syracuseStep 3852775 = 5779163) B5779163
theorem B3377983 : Blo 1332985 3377983 := bstep (se 1 (by rfl) ⟨2533487, by rfl⟩ : syracuseStep 3377983 = 5066975) B5066975
theorem B23104379 : Blo 1332985 23104379 := bstep (se 1 (by rfl) ⟨17328284, by rfl⟩ : syracuseStep 23104379 = 34656569) B34656569
theorem B2002031 : Blo 1332985 2002031 := bstep (se 1 (by rfl) ⟨1501523, by rfl⟩ : syracuseStep 2002031 = 3003047) B3003047
theorem B2002175 : Blo 1332985 2002175 := bstep (se 1 (by rfl) ⟨1501631, by rfl⟩ : syracuseStep 2002175 = 3003263) B3003263
theorem B3518183 : Blo 1332985 3518183 := bstep (se 1 (by rfl) ⟨2638637, by rfl⟩ : syracuseStep 3518183 = 5277275) B5277275
theorem B4805345 : Blo 1332985 4805345 := bstep (se 2 (by rfl) ⟨1802004, by rfl⟩ : syracuseStep 4805345 = 3604009) B3604009
theorem B2437865 : Blo 1332985 2437865 := bstep (se 2 (by rfl) ⟨914199, by rfl⟩ : syracuseStep 2437865 = 1828399) B1828399
theorem B3003119 : Blo 1332985 3003119 := bstep (se 1 (by rfl) ⟨2252339, by rfl⟩ : syracuseStep 3003119 = 4504679) B4504679
theorem B33797495 : Blo 1332985 33797495 := bstep (se 1 (by rfl) ⟨25348121, by rfl⟩ : syracuseStep 33797495 = 50696243) B50696243
theorem B34182809 : Blo 1332985 34182809 := bstep (se 2 (by rfl) ⟨12818553, by rfl⟩ : syracuseStep 34182809 = 25637107) B25637107
theorem B1333095 : Blo 1332985 1333095 := bstep (se 1 (by rfl) ⟨999821, by rfl⟩ : syracuseStep 1333095 = 1999643) B1999643
theorem B14432255 : Blo 1332985 14432255 := bstep (se 1 (by rfl) ⟨10824191, by rfl⟩ : syracuseStep 14432255 = 21648383) B21648383
theorem B1333727 : Blo 1332985 1333727 := bstep (se 1 (by rfl) ⟨1000295, by rfl⟩ : syracuseStep 1333727 = 2000591) B2000591
theorem B11393723 : Blo 1332985 11393723 := bstep (se 1 (by rfl) ⟨8545292, by rfl⟩ : syracuseStep 11393723 = 17090585) B17090585
theorem B1333999 : Blo 1332985 1333999 := bstep (se 1 (by rfl) ⟨1000499, by rfl⟩ : syracuseStep 1333999 = 2000999) B2000999
theorem B8543141 : Blo 1332985 8543141 := bstep (se 4 (by rfl) ⟨800919, by rfl⟩ : syracuseStep 8543141 = 1601839) B1601839
theorem B6749243 : Blo 1332985 6749243 := bstep (se 1 (by rfl) ⟨5061932, by rfl⟩ : syracuseStep 6749243 = 10123865) B10123865
theorem B76881797 : Blo 1332985 76881797 := bstep (se 4 (by rfl) ⟨7207668, by rfl⟩ : syracuseStep 76881797 = 14415337) B14415337
theorem B2531263 : Blo 1332985 2531263 := bstep (se 1 (by rfl) ⟨1898447, by rfl⟩ : syracuseStep 2531263 = 3796895) B3796895
theorem B2850977 : Blo 1332985 2850977 := bstep (se 2 (by rfl) ⟨1069116, by rfl⟩ : syracuseStep 2850977 = 2138233) B2138233
theorem B3203563 : Blo 1332985 3203563 := bstep (se 1 (by rfl) ⟨2402672, by rfl⟩ : syracuseStep 3203563 = 4805345) B4805345
theorem B5137033 : Blo 1332985 5137033 := bstep (se 2 (by rfl) ⟨1926387, by rfl⟩ : syracuseStep 5137033 = 3852775) B3852775
theorem B15189443 : Blo 1332985 15189443 := bstep (se 1 (by rfl) ⟨11392082, by rfl⟩ : syracuseStep 15189443 = 22784165) B22784165
theorem B7595815 : Blo 1332985 7595815 := bstep (se 1 (by rfl) ⟨5696861, by rfl⟩ : syracuseStep 7595815 = 11393723) B11393723
theorem B5695427 : Blo 1332985 5695427 := bstep (se 1 (by rfl) ⟨4271570, by rfl⟩ : syracuseStep 5695427 = 8543141) B8543141
theorem B4499495 : Blo 1332985 4499495 := bstep (se 1 (by rfl) ⟨3374621, by rfl⟩ : syracuseStep 4499495 = 6749243) B6749243
theorem B2345455 : Blo 1332985 2345455 := bstep (se 1 (by rfl) ⟨1759091, by rfl⟩ : syracuseStep 2345455 = 3518183) B3518183
theorem B4500251 : Blo 1332985 4500251 := bstep (se 1 (by rfl) ⟨3375188, by rfl⟩ : syracuseStep 4500251 = 6750377) B6750377
theorem B9120649 : Blo 1332985 9120649 := bstep (se 2 (by rfl) ⟨3420243, by rfl⟩ : syracuseStep 9120649 = 6840487) B6840487
theorem B1625243 : Blo 1332985 1625243 := bstep (se 1 (by rfl) ⟨1218932, by rfl⟩ : syracuseStep 1625243 = 2437865) B2437865
theorem B2002079 : Blo 1332985 2002079 := bstep (se 1 (by rfl) ⟨1501559, by rfl⟩ : syracuseStep 2002079 = 3003119) B3003119
theorem B22531663 : Blo 1332985 22531663 := bstep (se 1 (by rfl) ⟨16898747, by rfl⟩ : syracuseStep 22531663 = 33797495) B33797495
theorem B51293897 : Blo 1332985 51293897 := bstep (se 2 (by rfl) ⟨19235211, by rfl⟩ : syracuseStep 51293897 = 38470423) B38470423
theorem B9621503 : Blo 1332985 9621503 := bstep (se 1 (by rfl) ⟨7216127, by rfl⟩ : syracuseStep 9621503 = 14432255) B14432255
theorem B51254531 : Blo 1332985 51254531 := bstep (se 1 (by rfl) ⟨38440898, by rfl⟩ : syracuseStep 51254531 = 76881797) B76881797
theorem B1333103 : Blo 1332985 1333103 := bstep (se 1 (by rfl) ⟨999827, by rfl⟩ : syracuseStep 1333103 = 1999655) B1999655
theorem B15390769 : Blo 1332985 15390769 := bstep (se 2 (by rfl) ⟨5771538, by rfl⟩ : syracuseStep 15390769 = 11543077) B11543077
theorem B4503977 : Blo 1332985 4503977 := bstep (se 2 (by rfl) ⟨1688991, by rfl⟩ : syracuseStep 4503977 = 3377983) B3377983
theorem B22788539 : Blo 1332985 22788539 := bstep (se 1 (by rfl) ⟨17091404, by rfl⟩ : syracuseStep 22788539 = 34182809) B34182809
theorem B19225187 : Blo 1332985 19225187 := bstep (se 1 (by rfl) ⟨14418890, by rfl⟩ : syracuseStep 19225187 = 28837781) B28837781
theorem B9133049 : Blo 1332985 9133049 := bstep (se 2 (by rfl) ⟨3424893, by rfl⟩ : syracuseStep 9133049 = 6849787) B6849787
theorem B1334687 : Blo 1332985 1334687 := bstep (se 1 (by rfl) ⟨1001015, by rfl⟩ : syracuseStep 1334687 = 2002031) B2002031
theorem B1334783 : Blo 1332985 1334783 := bstep (se 1 (by rfl) ⟨1001087, by rfl⟩ : syracuseStep 1334783 = 2002175) B2002175
theorem B61611677 : Blo 1332985 61611677 := bstep (se 3 (by rfl) ⟨11552189, by rfl⟩ : syracuseStep 61611677 = 23104379) B23104379
theorem B3375017 : Blo 1332985 3375017 := bstep (se 2 (by rfl) ⟨1265631, by rfl⟩ : syracuseStep 3375017 = 2531263) B2531263
theorem B20521025 : Blo 1332985 20521025 := bstep (se 2 (by rfl) ⟨7695384, by rfl⟩ : syracuseStep 20521025 = 15390769) B15390769
theorem B4333981 : Blo 1332985 4333981 := bstep (se 3 (by rfl) ⟨812621, by rfl⟩ : syracuseStep 4333981 = 1625243) B1625243
theorem B7602605 : Blo 1332985 7602605 := bstep (se 3 (by rfl) ⟨1425488, by rfl⟩ : syracuseStep 7602605 = 2850977) B2850977
theorem B34169687 : Blo 1332985 34169687 := bstep (se 1 (by rfl) ⟨25627265, by rfl⟩ : syracuseStep 34169687 = 51254531) B51254531
theorem B6849377 : Blo 1332985 6849377 := bstep (se 2 (by rfl) ⟨2568516, by rfl⟩ : syracuseStep 6849377 = 5137033) B5137033
theorem B10126295 : Blo 1332985 10126295 := bstep (se 1 (by rfl) ⟨7594721, by rfl⟩ : syracuseStep 10126295 = 15189443) B15189443
theorem B2999663 : Blo 1332985 2999663 := bstep (se 1 (by rfl) ⟨2249747, by rfl⟩ : syracuseStep 2999663 = 4499495) B4499495
theorem B3000167 : Blo 1332985 3000167 := bstep (se 1 (by rfl) ⟨2250125, by rfl⟩ : syracuseStep 3000167 = 4500251) B4500251
theorem B6088699 : Blo 1332985 6088699 := bstep (se 1 (by rfl) ⟨4566524, by rfl⟩ : syracuseStep 6088699 = 9133049) B9133049
theorem B30042217 : Blo 1332985 30042217 := bstep (se 2 (by rfl) ⟨11265831, by rfl⟩ : syracuseStep 30042217 = 22531663) B22531663
theorem B10127753 : Blo 1332985 10127753 := bstep (se 2 (by rfl) ⟨3797907, by rfl⟩ : syracuseStep 10127753 = 7595815) B7595815
theorem B34195931 : Blo 1332985 34195931 := bstep (se 1 (by rfl) ⟨25646948, by rfl⟩ : syracuseStep 34195931 = 51293897) B51293897
theorem B4271417 : Blo 1332985 4271417 := bstep (se 2 (by rfl) ⟨1601781, by rfl⟩ : syracuseStep 4271417 = 3203563) B3203563
theorem B6414335 : Blo 1332985 6414335 := bstep (se 1 (by rfl) ⟨4810751, by rfl⟩ : syracuseStep 6414335 = 9621503) B9621503
theorem B12160865 : Blo 1332985 12160865 := bstep (se 2 (by rfl) ⟨4560324, by rfl⟩ : syracuseStep 12160865 = 9120649) B9120649
theorem B3796951 : Blo 1332985 3796951 := bstep (se 1 (by rfl) ⟨2847713, by rfl⟩ : syracuseStep 3796951 = 5695427) B5695427
theorem B3002651 : Blo 1332985 3002651 := bstep (se 1 (by rfl) ⟨2251988, by rfl⟩ : syracuseStep 3002651 = 4503977) B4503977
theorem B15192359 : Blo 1332985 15192359 := bstep (se 1 (by rfl) ⟨11394269, by rfl⟩ : syracuseStep 15192359 = 22788539) B22788539
theorem B12816791 : Blo 1332985 12816791 := bstep (se 1 (by rfl) ⟨9612593, by rfl⟩ : syracuseStep 12816791 = 19225187) B19225187
theorem B2250011 : Blo 1332985 2250011 := bstep (se 1 (by rfl) ⟨1687508, by rfl⟩ : syracuseStep 2250011 = 3375017) B3375017
theorem B1334719 : Blo 1332985 1334719 := bstep (se 1 (by rfl) ⟨1001039, by rfl⟩ : syracuseStep 1334719 = 2002079) B2002079
theorem B41074451 : Blo 1332985 41074451 := bstep (se 1 (by rfl) ⟨30805838, by rfl⟩ : syracuseStep 41074451 = 61611677) B61611677
theorem B12509093 : Blo 1332985 12509093 := bstep (se 4 (by rfl) ⟨1172727, by rfl⟩ : syracuseStep 12509093 = 2345455) B2345455
theorem B13680683 : Blo 1332985 13680683 := bstep (se 1 (by rfl) ⟨10260512, by rfl⟩ : syracuseStep 13680683 = 20521025) B20521025
theorem B8544527 : Blo 1332985 8544527 := bstep (se 1 (by rfl) ⟨6408395, by rfl⟩ : syracuseStep 8544527 = 12816791) B12816791
theorem B6750863 : Blo 1332985 6750863 := bstep (se 1 (by rfl) ⟨5063147, by rfl⟩ : syracuseStep 6750863 = 10126295) B10126295
theorem B1500007 : Blo 1332985 1500007 := bstep (se 1 (by rfl) ⟨1125005, by rfl⟩ : syracuseStep 1500007 = 2250011) B2250011
theorem B1999775 : Blo 1332985 1999775 := bstep (se 1 (by rfl) ⟨1499831, by rfl⟩ : syracuseStep 1999775 = 2999663) B2999663
theorem B2000111 : Blo 1332985 2000111 := bstep (se 1 (by rfl) ⟨1500083, by rfl⟩ : syracuseStep 2000111 = 3000167) B3000167
theorem B6751835 : Blo 1332985 6751835 := bstep (se 1 (by rfl) ⟨5063876, by rfl⟩ : syracuseStep 6751835 = 10127753) B10127753
theorem B4276223 : Blo 1332985 4276223 := bstep (se 1 (by rfl) ⟨3207167, by rfl⟩ : syracuseStep 4276223 = 6414335) B6414335
theorem B2001767 : Blo 1332985 2001767 := bstep (se 1 (by rfl) ⟨1501325, by rfl⟩ : syracuseStep 2001767 = 3002651) B3002651
theorem B10128239 : Blo 1332985 10128239 := bstep (se 1 (by rfl) ⟨7596179, by rfl⟩ : syracuseStep 10128239 = 15192359) B15192359
theorem B5778641 : Blo 1332985 5778641 := bstep (se 2 (by rfl) ⟨2166990, by rfl⟩ : syracuseStep 5778641 = 4333981) B4333981
theorem B4566251 : Blo 1332985 4566251 := bstep (se 1 (by rfl) ⟨3424688, by rfl⟩ : syracuseStep 4566251 = 6849377) B6849377
theorem B2847611 : Blo 1332985 2847611 := bstep (se 1 (by rfl) ⟨2135708, by rfl⟩ : syracuseStep 2847611 = 4271417) B4271417
theorem B32428973 : Blo 1332985 32428973 := bstep (se 3 (by rfl) ⟨6080432, by rfl⟩ : syracuseStep 32428973 = 12160865) B12160865
theorem B27382967 : Blo 1332985 27382967 := bstep (se 1 (by rfl) ⟨20537225, by rfl⟩ : syracuseStep 27382967 = 41074451) B41074451
theorem B40056289 : Blo 1332985 40056289 := bstep (se 2 (by rfl) ⟨15021108, by rfl⟩ : syracuseStep 40056289 = 30042217) B30042217
theorem B5068403 : Blo 1332985 5068403 := bstep (se 1 (by rfl) ⟨3801302, by rfl⟩ : syracuseStep 5068403 = 7602605) B7602605
theorem B22779791 : Blo 1332985 22779791 := bstep (se 1 (by rfl) ⟨17084843, by rfl⟩ : syracuseStep 22779791 = 34169687) B34169687
theorem B22797287 : Blo 1332985 22797287 := bstep (se 1 (by rfl) ⟨17097965, by rfl⟩ : syracuseStep 22797287 = 34195931) B34195931
theorem B33357581 : Blo 1332985 33357581 := bstep (se 3 (by rfl) ⟨6254546, by rfl⟩ : syracuseStep 33357581 = 12509093) B12509093
theorem B5062601 : Blo 1332985 5062601 := bstep (se 2 (by rfl) ⟨1898475, by rfl⟩ : syracuseStep 5062601 = 3796951) B3796951
theorem B8118265 : Blo 1332985 8118265 := bstep (se 2 (by rfl) ⟨3044349, by rfl⟩ : syracuseStep 8118265 = 6088699) B6088699
theorem B15409709 : Blo 1332985 15409709 := bstep (se 3 (by rfl) ⟨2889320, by rfl⟩ : syracuseStep 15409709 = 5778641) B5778641
theorem B21619315 : Blo 1332985 21619315 := bstep (se 1 (by rfl) ⟨16214486, by rfl⟩ : syracuseStep 21619315 = 32428973) B32428973
theorem B2000009 : Blo 1332985 2000009 := bstep (se 2 (by rfl) ⟨750003, by rfl⟩ : syracuseStep 2000009 = 1500007) B1500007
theorem B6752159 : Blo 1332985 6752159 := bstep (se 1 (by rfl) ⟨5064119, by rfl⟩ : syracuseStep 6752159 = 10128239) B10128239
theorem B15198191 : Blo 1332985 15198191 := bstep (se 1 (by rfl) ⟨11398643, by rfl⟩ : syracuseStep 15198191 = 22797287) B22797287
theorem B213633541 : Blo 1332985 213633541 := bstep (se 4 (by rfl) ⟨20028144, by rfl⟩ : syracuseStep 213633541 = 40056289) B40056289
theorem B10824353 : Blo 1332985 10824353 := bstep (se 2 (by rfl) ⟨4059132, by rfl⟩ : syracuseStep 10824353 = 8118265) B8118265
theorem B9120455 : Blo 1332985 9120455 := bstep (se 1 (by rfl) ⟨6840341, by rfl⟩ : syracuseStep 9120455 = 13680683) B13680683
theorem B5696351 : Blo 1332985 5696351 := bstep (se 1 (by rfl) ⟨4272263, by rfl⟩ : syracuseStep 5696351 = 8544527) B8544527
theorem B4500575 : Blo 1332985 4500575 := bstep (se 1 (by rfl) ⟨3375431, by rfl⟩ : syracuseStep 4500575 = 6750863) B6750863
theorem B12176669 : Blo 1332985 12176669 := bstep (se 3 (by rfl) ⟨2283125, by rfl⟩ : syracuseStep 12176669 = 4566251) B4566251
theorem B18255311 : Blo 1332985 18255311 := bstep (se 1 (by rfl) ⟨13691483, by rfl⟩ : syracuseStep 18255311 = 27382967) B27382967
theorem B4501223 : Blo 1332985 4501223 := bstep (se 1 (by rfl) ⟨3375917, by rfl⟩ : syracuseStep 4501223 = 6751835) B6751835
theorem B3378935 : Blo 1332985 3378935 := bstep (se 1 (by rfl) ⟨2534201, by rfl⟩ : syracuseStep 3378935 = 5068403) B5068403
theorem B22238387 : Blo 1332985 22238387 := bstep (se 1 (by rfl) ⟨16678790, by rfl⟩ : syracuseStep 22238387 = 33357581) B33357581
theorem B1898407 : Blo 1332985 1898407 := bstep (se 1 (by rfl) ⟨1423805, by rfl⟩ : syracuseStep 1898407 = 2847611) B2847611
theorem B1333183 : Blo 1332985 1333183 := bstep (se 1 (by rfl) ⟨999887, by rfl⟩ : syracuseStep 1333183 = 1999775) B1999775
theorem B1333407 : Blo 1332985 1333407 := bstep (se 1 (by rfl) ⟨1000055, by rfl⟩ : syracuseStep 1333407 = 2000111) B2000111
theorem B15186527 : Blo 1332985 15186527 := bstep (se 1 (by rfl) ⟨11389895, by rfl⟩ : syracuseStep 15186527 = 22779791) B22779791
theorem B1334511 : Blo 1332985 1334511 := bstep (se 1 (by rfl) ⟨1000883, by rfl⟩ : syracuseStep 1334511 = 2001767) B2001767
theorem B3375067 : Blo 1332985 3375067 := bstep (se 1 (by rfl) ⟨2531300, by rfl⟩ : syracuseStep 3375067 = 5062601) B5062601
theorem B2850815 : Blo 1332985 2850815 := bstep (se 1 (by rfl) ⟨2138111, by rfl⟩ : syracuseStep 2850815 = 4276223) B4276223
theorem B10273139 : Blo 1332985 10273139 := bstep (se 1 (by rfl) ⟨7704854, by rfl⟩ : syracuseStep 10273139 = 15409709) B15409709
theorem B284844721 : Blo 1332985 284844721 := bstep (se 2 (by rfl) ⟨106816770, by rfl⟩ : syracuseStep 284844721 = 213633541) B213633541
theorem B6080303 : Blo 1332985 6080303 := bstep (se 1 (by rfl) ⟨4560227, by rfl⟩ : syracuseStep 6080303 = 9120455) B9120455
theorem B3000383 : Blo 1332985 3000383 := bstep (se 1 (by rfl) ⟨2250287, by rfl⟩ : syracuseStep 3000383 = 4500575) B4500575
theorem B3000815 : Blo 1332985 3000815 := bstep (se 1 (by rfl) ⟨2250611, by rfl⟩ : syracuseStep 3000815 = 4501223) B4501223
theorem B4500089 : Blo 1332985 4500089 := bstep (se 2 (by rfl) ⟨1687533, by rfl⟩ : syracuseStep 4500089 = 3375067) B3375067
theorem B4501439 : Blo 1332985 4501439 := bstep (se 1 (by rfl) ⟨3376079, by rfl⟩ : syracuseStep 4501439 = 6752159) B6752159
theorem B3797567 : Blo 1332985 3797567 := bstep (se 1 (by rfl) ⟨2848175, by rfl⟩ : syracuseStep 3797567 = 5696351) B5696351
theorem B12170207 : Blo 1332985 12170207 := bstep (se 1 (by rfl) ⟨9127655, by rfl⟩ : syracuseStep 12170207 = 18255311) B18255311
theorem B1333339 : Blo 1332985 1333339 := bstep (se 1 (by rfl) ⟨1000004, by rfl⟩ : syracuseStep 1333339 = 2000009) B2000009
theorem B14825591 : Blo 1332985 14825591 := bstep (se 1 (by rfl) ⟨11119193, by rfl⟩ : syracuseStep 14825591 = 22238387) B22238387
theorem B28825753 : Blo 1332985 28825753 := bstep (se 2 (by rfl) ⟨10809657, by rfl⟩ : syracuseStep 28825753 = 21619315) B21619315
theorem B10132127 : Blo 1332985 10132127 := bstep (se 1 (by rfl) ⟨7599095, by rfl⟩ : syracuseStep 10132127 = 15198191) B15198191
theorem B10124351 : Blo 1332985 10124351 := bstep (se 1 (by rfl) ⟨7593263, by rfl⟩ : syracuseStep 10124351 = 15186527) B15186527
theorem B7216235 : Blo 1332985 7216235 := bstep (se 1 (by rfl) ⟨5412176, by rfl⟩ : syracuseStep 7216235 = 10824353) B10824353
theorem B8117779 : Blo 1332985 8117779 := bstep (se 1 (by rfl) ⟨6088334, by rfl⟩ : syracuseStep 8117779 = 12176669) B12176669
theorem B10124837 : Blo 1332985 10124837 := bstep (se 4 (by rfl) ⟨949203, by rfl⟩ : syracuseStep 10124837 = 1898407) B1898407
theorem B2252623 : Blo 1332985 2252623 := bstep (se 1 (by rfl) ⟨1689467, by rfl⟩ : syracuseStep 2252623 = 3378935) B3378935
theorem B7602173 : Blo 1332985 7602173 := bstep (se 3 (by rfl) ⟨1425407, by rfl⟩ : syracuseStep 7602173 = 2850815) B2850815
theorem B6848759 : Blo 1332985 6848759 := bstep (se 1 (by rfl) ⟨5136569, by rfl⟩ : syracuseStep 6848759 = 10273139) B10273139
theorem B2531711 : Blo 1332985 2531711 := bstep (se 1 (by rfl) ⟨1898783, by rfl⟩ : syracuseStep 2531711 = 3797567) B3797567
theorem B2000255 : Blo 1332985 2000255 := bstep (se 1 (by rfl) ⟨1500191, by rfl⟩ : syracuseStep 2000255 = 3000383) B3000383
theorem B2000543 : Blo 1332985 2000543 := bstep (se 1 (by rfl) ⟨1500407, by rfl⟩ : syracuseStep 2000543 = 3000815) B3000815
theorem B3000059 : Blo 1332985 3000059 := bstep (se 1 (by rfl) ⟨2250044, by rfl⟩ : syracuseStep 3000059 = 4500089) B4500089
theorem B10823705 : Blo 1332985 10823705 := bstep (se 2 (by rfl) ⟨4058889, by rfl⟩ : syracuseStep 10823705 = 8117779) B8117779
theorem B4810823 : Blo 1332985 4810823 := bstep (se 1 (by rfl) ⟨3608117, by rfl⟩ : syracuseStep 4810823 = 7216235) B7216235
theorem B16214141 : Blo 1332985 16214141 := bstep (se 3 (by rfl) ⟨3040151, by rfl⟩ : syracuseStep 16214141 = 6080303) B6080303
theorem B3000959 : Blo 1332985 3000959 := bstep (se 1 (by rfl) ⟨2250719, by rfl⟩ : syracuseStep 3000959 = 4501439) B4501439
theorem B379792961 : Blo 1332985 379792961 := bstep (se 2 (by rfl) ⟨142422360, by rfl⟩ : syracuseStep 379792961 = 284844721) B284844721
theorem B9883727 : Blo 1332985 9883727 := bstep (se 1 (by rfl) ⟨7412795, by rfl⟩ : syracuseStep 9883727 = 14825591) B14825591
theorem B6754751 : Blo 1332985 6754751 := bstep (se 1 (by rfl) ⟨5066063, by rfl⟩ : syracuseStep 6754751 = 10132127) B10132127
theorem B3003497 : Blo 1332985 3003497 := bstep (se 2 (by rfl) ⟨1126311, by rfl⟩ : syracuseStep 3003497 = 2252623) B2252623
theorem B32453885 : Blo 1332985 32453885 := bstep (se 3 (by rfl) ⟨6085103, by rfl⟩ : syracuseStep 32453885 = 12170207) B12170207
theorem B5068115 : Blo 1332985 5068115 := bstep (se 1 (by rfl) ⟨3801086, by rfl⟩ : syracuseStep 5068115 = 7602173) B7602173
theorem B38434337 : Blo 1332985 38434337 := bstep (se 2 (by rfl) ⟨14412876, by rfl⟩ : syracuseStep 38434337 = 28825753) B28825753
theorem B6749567 : Blo 1332985 6749567 := bstep (se 1 (by rfl) ⟨5062175, by rfl⟩ : syracuseStep 6749567 = 10124351) B10124351
theorem B6749891 : Blo 1332985 6749891 := bstep (se 1 (by rfl) ⟨5062418, by rfl⟩ : syracuseStep 6749891 = 10124837) B10124837
theorem B1687807 : Blo 1332985 1687807 := bstep (se 1 (by rfl) ⟨1265855, by rfl⟩ : syracuseStep 1687807 = 2531711) B2531711
theorem B43237709 : Blo 1332985 43237709 := bstep (se 3 (by rfl) ⟨8107070, by rfl⟩ : syracuseStep 43237709 = 16214141) B16214141
theorem B21635923 : Blo 1332985 21635923 := bstep (se 1 (by rfl) ⟨16226942, by rfl⟩ : syracuseStep 21635923 = 32453885) B32453885
theorem B2000039 : Blo 1332985 2000039 := bstep (se 1 (by rfl) ⟨1500029, by rfl⟩ : syracuseStep 2000039 = 3000059) B3000059
theorem B2000639 : Blo 1332985 2000639 := bstep (se 1 (by rfl) ⟨1500479, by rfl⟩ : syracuseStep 2000639 = 3000959) B3000959
theorem B4499711 : Blo 1332985 4499711 := bstep (se 1 (by rfl) ⟨3374783, by rfl⟩ : syracuseStep 4499711 = 6749567) B6749567
theorem B4499927 : Blo 1332985 4499927 := bstep (se 1 (by rfl) ⟨3374945, by rfl⟩ : syracuseStep 4499927 = 6749891) B6749891
theorem B6589151 : Blo 1332985 6589151 := bstep (se 1 (by rfl) ⟨4941863, by rfl⟩ : syracuseStep 6589151 = 9883727) B9883727
theorem B18263357 : Blo 1332985 18263357 := bstep (se 3 (by rfl) ⟨3424379, by rfl⟩ : syracuseStep 18263357 = 6848759) B6848759
theorem B2002331 : Blo 1332985 2002331 := bstep (se 1 (by rfl) ⟨1501748, by rfl⟩ : syracuseStep 2002331 = 3003497) B3003497
theorem B3378743 : Blo 1332985 3378743 := bstep (se 1 (by rfl) ⟨2534057, by rfl⟩ : syracuseStep 3378743 = 5068115) B5068115
theorem B3207215 : Blo 1332985 3207215 := bstep (se 1 (by rfl) ⟨2405411, by rfl⟩ : syracuseStep 3207215 = 4810823) B4810823
theorem B253195307 : Blo 1332985 253195307 := bstep (se 1 (by rfl) ⟨189896480, by rfl⟩ : syracuseStep 253195307 = 379792961) B379792961
theorem B4503167 : Blo 1332985 4503167 := bstep (se 1 (by rfl) ⟨3377375, by rfl⟩ : syracuseStep 4503167 = 6754751) B6754751
theorem B1333503 : Blo 1332985 1333503 := bstep (se 1 (by rfl) ⟨1000127, by rfl⟩ : syracuseStep 1333503 = 2000255) B2000255
theorem B25622891 : Blo 1332985 25622891 := bstep (se 1 (by rfl) ⟨19217168, by rfl⟩ : syracuseStep 25622891 = 38434337) B38434337
theorem B1333695 : Blo 1332985 1333695 := bstep (se 1 (by rfl) ⟨1000271, by rfl⟩ : syracuseStep 1333695 = 2000543) B2000543
theorem B7215803 : Blo 1332985 7215803 := bstep (se 1 (by rfl) ⟨5411852, by rfl⟩ : syracuseStep 7215803 = 10823705) B10823705
theorem B8552573 : Blo 1332985 8552573 := bstep (se 3 (by rfl) ⟨1603607, by rfl⟩ : syracuseStep 8552573 = 3207215) B3207215
theorem B168796871 : Blo 1332985 168796871 := bstep (se 1 (by rfl) ⟨126597653, by rfl⟩ : syracuseStep 168796871 = 253195307) B253195307
theorem B2999807 : Blo 1332985 2999807 := bstep (se 1 (by rfl) ⟨2249855, by rfl⟩ : syracuseStep 2999807 = 4499711) B4499711
theorem B17081927 : Blo 1332985 17081927 := bstep (se 1 (by rfl) ⟨12811445, by rfl⟩ : syracuseStep 17081927 = 25622891) B25622891
theorem B2999951 : Blo 1332985 2999951 := bstep (se 1 (by rfl) ⟨2249963, by rfl⟩ : syracuseStep 2999951 = 4499927) B4499927
theorem B4810535 : Blo 1332985 4810535 := bstep (se 1 (by rfl) ⟨3607901, by rfl⟩ : syracuseStep 4810535 = 7215803) B7215803
theorem B4392767 : Blo 1332985 4392767 := bstep (se 1 (by rfl) ⟨3294575, by rfl⟩ : syracuseStep 4392767 = 6589151) B6589151
theorem B12175571 : Blo 1332985 12175571 := bstep (se 1 (by rfl) ⟨9131678, by rfl⟩ : syracuseStep 12175571 = 18263357) B18263357
theorem B3002111 : Blo 1332985 3002111 := bstep (se 1 (by rfl) ⟨2251583, by rfl⟩ : syracuseStep 3002111 = 4503167) B4503167
theorem B28847897 : Blo 1332985 28847897 := bstep (se 2 (by rfl) ⟨10817961, by rfl⟩ : syracuseStep 28847897 = 21635923) B21635923
theorem B28825139 : Blo 1332985 28825139 := bstep (se 1 (by rfl) ⟨21618854, by rfl⟩ : syracuseStep 28825139 = 43237709) B43237709
theorem B2250409 : Blo 1332985 2250409 := bstep (se 2 (by rfl) ⟨843903, by rfl⟩ : syracuseStep 2250409 = 1687807) B1687807
theorem B1333359 : Blo 1332985 1333359 := bstep (se 1 (by rfl) ⟨1000019, by rfl⟩ : syracuseStep 1333359 = 2000039) B2000039
theorem B1333759 : Blo 1332985 1333759 := bstep (se 1 (by rfl) ⟨1000319, by rfl⟩ : syracuseStep 1333759 = 2000639) B2000639
theorem B1334887 : Blo 1332985 1334887 := bstep (se 1 (by rfl) ⟨1001165, by rfl⟩ : syracuseStep 1334887 = 2002331) B2002331
theorem B2252495 : Blo 1332985 2252495 := bstep (se 1 (by rfl) ⟨1689371, by rfl⟩ : syracuseStep 2252495 = 3378743) B3378743
theorem B5701715 : Blo 1332985 5701715 := bstep (se 1 (by rfl) ⟨4276286, by rfl⟩ : syracuseStep 5701715 = 8552573) B8552573
theorem B1999871 : Blo 1332985 1999871 := bstep (se 1 (by rfl) ⟨1499903, by rfl⟩ : syracuseStep 1999871 = 2999807) B2999807
theorem B11387951 : Blo 1332985 11387951 := bstep (se 1 (by rfl) ⟨8540963, by rfl⟩ : syracuseStep 11387951 = 17081927) B17081927
theorem B1999967 : Blo 1332985 1999967 := bstep (se 1 (by rfl) ⟨1499975, by rfl⟩ : syracuseStep 1999967 = 2999951) B2999951
theorem B3000545 : Blo 1332985 3000545 := bstep (se 2 (by rfl) ⟨1125204, by rfl⟩ : syracuseStep 3000545 = 2250409) B2250409
theorem B1501663 : Blo 1332985 1501663 := bstep (se 1 (by rfl) ⟨1126247, by rfl⟩ : syracuseStep 1501663 = 2252495) B2252495
theorem B2001407 : Blo 1332985 2001407 := bstep (se 1 (by rfl) ⟨1501055, by rfl⟩ : syracuseStep 2001407 = 3002111) B3002111
theorem B3207023 : Blo 1332985 3207023 := bstep (se 1 (by rfl) ⟨2405267, by rfl⟩ : syracuseStep 3207023 = 4810535) B4810535
theorem B19231931 : Blo 1332985 19231931 := bstep (se 1 (by rfl) ⟨14423948, by rfl⟩ : syracuseStep 19231931 = 28847897) B28847897
theorem B112531247 : Blo 1332985 112531247 := bstep (se 1 (by rfl) ⟨84398435, by rfl⟩ : syracuseStep 112531247 = 168796871) B168796871
theorem B19216759 : Blo 1332985 19216759 := bstep (se 1 (by rfl) ⟨14412569, by rfl⟩ : syracuseStep 19216759 = 28825139) B28825139
theorem B8117047 : Blo 1332985 8117047 := bstep (se 1 (by rfl) ⟨6087785, by rfl⟩ : syracuseStep 8117047 = 12175571) B12175571
theorem B11714045 : Blo 1332985 11714045 := bstep (se 3 (by rfl) ⟨2196383, by rfl⟩ : syracuseStep 11714045 = 4392767) B4392767
theorem B3801143 : Blo 1332985 3801143 := bstep (se 1 (by rfl) ⟨2850857, by rfl⟩ : syracuseStep 3801143 = 5701715) B5701715
theorem B12821287 : Blo 1332985 12821287 := bstep (se 1 (by rfl) ⟨9615965, by rfl⟩ : syracuseStep 12821287 = 19231931) B19231931
theorem B10822729 : Blo 1332985 10822729 := bstep (se 2 (by rfl) ⟨4058523, by rfl⟩ : syracuseStep 10822729 = 8117047) B8117047
theorem B31237453 : Blo 1332985 31237453 := bstep (se 3 (by rfl) ⟨5857022, by rfl⟩ : syracuseStep 31237453 = 11714045) B11714045
theorem B2000363 : Blo 1332985 2000363 := bstep (se 1 (by rfl) ⟨1500272, by rfl⟩ : syracuseStep 2000363 = 3000545) B3000545
theorem B2002217 : Blo 1332985 2002217 := bstep (se 2 (by rfl) ⟨750831, by rfl⟩ : syracuseStep 2002217 = 1501663) B1501663
theorem B25622345 : Blo 1332985 25622345 := bstep (se 2 (by rfl) ⟨9608379, by rfl⟩ : syracuseStep 25622345 = 19216759) B19216759
theorem B1333247 : Blo 1332985 1333247 := bstep (se 1 (by rfl) ⟨999935, by rfl⟩ : syracuseStep 1333247 = 1999871) B1999871
theorem B7591967 : Blo 1332985 7591967 := bstep (se 1 (by rfl) ⟨5693975, by rfl⟩ : syracuseStep 7591967 = 11387951) B11387951
theorem B1333311 : Blo 1332985 1333311 := bstep (se 1 (by rfl) ⟨999983, by rfl⟩ : syracuseStep 1333311 = 1999967) B1999967
theorem B75020831 : Blo 1332985 75020831 := bstep (se 1 (by rfl) ⟨56265623, by rfl⟩ : syracuseStep 75020831 = 112531247) B112531247
theorem B1334271 : Blo 1332985 1334271 := bstep (se 1 (by rfl) ⟨1000703, by rfl⟩ : syracuseStep 1334271 = 2001407) B2001407
theorem B2138015 : Blo 1332985 2138015 := bstep (se 1 (by rfl) ⟨1603511, by rfl⟩ : syracuseStep 2138015 = 3207023) B3207023
theorem B17081563 : Blo 1332985 17081563 := bstep (se 1 (by rfl) ⟨12811172, by rfl⟩ : syracuseStep 17081563 = 25622345) B25622345
theorem B50013887 : Blo 1332985 50013887 := bstep (se 1 (by rfl) ⟨37510415, by rfl⟩ : syracuseStep 50013887 = 75020831) B75020831
theorem B2534095 : Blo 1332985 2534095 := bstep (se 1 (by rfl) ⟨1900571, by rfl⟩ : syracuseStep 2534095 = 3801143) B3801143
theorem B14430305 : Blo 1332985 14430305 := bstep (se 2 (by rfl) ⟨5411364, by rfl⟩ : syracuseStep 14430305 = 10822729) B10822729
theorem B1333575 : Blo 1332985 1333575 := bstep (se 1 (by rfl) ⟨1000181, by rfl⟩ : syracuseStep 1333575 = 2000363) B2000363
theorem B17095049 : Blo 1332985 17095049 := bstep (se 2 (by rfl) ⟨6410643, by rfl⟩ : syracuseStep 17095049 = 12821287) B12821287
theorem B5061311 : Blo 1332985 5061311 := bstep (se 1 (by rfl) ⟨3795983, by rfl⟩ : syracuseStep 5061311 = 7591967) B7591967
theorem B166599749 : Blo 1332985 166599749 := bstep (se 4 (by rfl) ⟨15618726, by rfl⟩ : syracuseStep 166599749 = 31237453) B31237453
theorem B1334811 : Blo 1332985 1334811 := bstep (se 1 (by rfl) ⟨1001108, by rfl⟩ : syracuseStep 1334811 = 2002217) B2002217
theorem B5701373 : Blo 1332985 5701373 := bstep (se 3 (by rfl) ⟨1069007, by rfl⟩ : syracuseStep 5701373 = 2138015) B2138015
theorem B11396699 : Blo 1332985 11396699 := bstep (se 1 (by rfl) ⟨8547524, by rfl⟩ : syracuseStep 11396699 = 17095049) B17095049
theorem B22775417 : Blo 1332985 22775417 := bstep (se 2 (by rfl) ⟨8540781, by rfl⟩ : syracuseStep 22775417 = 17081563) B17081563
theorem B533481461 : Blo 1332985 533481461 := bstep (se 5 (by rfl) ⟨25006943, by rfl⟩ : syracuseStep 533481461 = 50013887) B50013887
theorem B9620203 : Blo 1332985 9620203 := bstep (se 1 (by rfl) ⟨7215152, by rfl⟩ : syracuseStep 9620203 = 14430305) B14430305
theorem B3378793 : Blo 1332985 3378793 := bstep (se 2 (by rfl) ⟨1267047, by rfl⟩ : syracuseStep 3378793 = 2534095) B2534095
theorem B3374207 : Blo 1332985 3374207 := bstep (se 1 (by rfl) ⟨2530655, by rfl⟩ : syracuseStep 3374207 = 5061311) B5061311
theorem B111066499 : Blo 1332985 111066499 := bstep (se 1 (by rfl) ⟨83299874, by rfl⟩ : syracuseStep 111066499 = 166599749) B166599749
theorem B3800915 : Blo 1332985 3800915 := bstep (se 1 (by rfl) ⟨2850686, by rfl⟩ : syracuseStep 3800915 = 5701373) B5701373
theorem B148088665 : Blo 1332985 148088665 := bstep (se 2 (by rfl) ⟨55533249, by rfl⟩ : syracuseStep 148088665 = 111066499) B111066499
theorem B2533943 : Blo 1332985 2533943 := bstep (se 1 (by rfl) ⟨1900457, by rfl⟩ : syracuseStep 2533943 = 3800915) B3800915
theorem B7597799 : Blo 1332985 7597799 := bstep (se 1 (by rfl) ⟨5698349, by rfl⟩ : syracuseStep 7597799 = 11396699) B11396699
theorem B15183611 : Blo 1332985 15183611 := bstep (se 1 (by rfl) ⟨11387708, by rfl⟩ : syracuseStep 15183611 = 22775417) B22775417
theorem B2249471 : Blo 1332985 2249471 := bstep (se 1 (by rfl) ⟨1687103, by rfl⟩ : syracuseStep 2249471 = 3374207) B3374207
theorem B12826937 : Blo 1332985 12826937 := bstep (se 2 (by rfl) ⟨4810101, by rfl⟩ : syracuseStep 12826937 = 9620203) B9620203
theorem B355654307 : Blo 1332985 355654307 := bstep (se 1 (by rfl) ⟨266740730, by rfl⟩ : syracuseStep 355654307 = 533481461) B533481461
theorem B4505057 : Blo 1332985 4505057 := bstep (se 2 (by rfl) ⟨1689396, by rfl⟩ : syracuseStep 4505057 = 3378793) B3378793
theorem B1499647 : Blo 1332985 1499647 := bstep (se 1 (by rfl) ⟨1124735, by rfl⟩ : syracuseStep 1499647 = 2249471) B2249471
theorem B237102871 : Blo 1332985 237102871 := bstep (se 1 (by rfl) ⟨177827153, by rfl⟩ : syracuseStep 237102871 = 355654307) B355654307
theorem B5065199 : Blo 1332985 5065199 := bstep (se 1 (by rfl) ⟨3798899, by rfl⟩ : syracuseStep 5065199 = 7597799) B7597799
theorem B3003371 : Blo 1332985 3003371 := bstep (se 1 (by rfl) ⟨2252528, by rfl⟩ : syracuseStep 3003371 = 4505057) B4505057
theorem B10122407 : Blo 1332985 10122407 := bstep (se 1 (by rfl) ⟨7591805, by rfl⟩ : syracuseStep 10122407 = 15183611) B15183611
theorem B6757181 : Blo 1332985 6757181 := bstep (se 3 (by rfl) ⟨1266971, by rfl⟩ : syracuseStep 6757181 = 2533943) B2533943
theorem B8551291 : Blo 1332985 8551291 := bstep (se 1 (by rfl) ⟨6413468, by rfl⟩ : syracuseStep 8551291 = 12826937) B12826937
theorem B197451553 : Blo 1332985 197451553 := bstep (se 2 (by rfl) ⟨74044332, by rfl⟩ : syracuseStep 197451553 = 148088665) B148088665
theorem B1999529 : Blo 1332985 1999529 := bstep (se 2 (by rfl) ⟨749823, by rfl⟩ : syracuseStep 1999529 = 1499647) B1499647
theorem B3376799 : Blo 1332985 3376799 := bstep (se 1 (by rfl) ⟨2532599, by rfl⟩ : syracuseStep 3376799 = 5065199) B5065199
theorem B263268737 : Blo 1332985 263268737 := bstep (se 2 (by rfl) ⟨98725776, by rfl⟩ : syracuseStep 263268737 = 197451553) B197451553
theorem B2002247 : Blo 1332985 2002247 := bstep (se 1 (by rfl) ⟨1501685, by rfl⟩ : syracuseStep 2002247 = 3003371) B3003371
theorem B6748271 : Blo 1332985 6748271 := bstep (se 1 (by rfl) ⟨5061203, by rfl⟩ : syracuseStep 6748271 = 10122407) B10122407
theorem B11401721 : Blo 1332985 11401721 := bstep (se 2 (by rfl) ⟨4275645, by rfl⟩ : syracuseStep 11401721 = 8551291) B8551291
theorem B4504787 : Blo 1332985 4504787 := bstep (se 1 (by rfl) ⟨3378590, by rfl⟩ : syracuseStep 4504787 = 6757181) B6757181
theorem B316137161 : Blo 1332985 316137161 := bstep (se 2 (by rfl) ⟨118551435, by rfl⟩ : syracuseStep 316137161 = 237102871) B237102871
theorem B4498847 : Blo 1332985 4498847 := bstep (se 1 (by rfl) ⟨3374135, by rfl⟩ : syracuseStep 4498847 = 6748271) B6748271
theorem B210758107 : Blo 1332985 210758107 := bstep (se 1 (by rfl) ⟨158068580, by rfl⟩ : syracuseStep 210758107 = 316137161) B316137161
theorem B3003191 : Blo 1332985 3003191 := bstep (se 1 (by rfl) ⟨2252393, by rfl⟩ : syracuseStep 3003191 = 4504787) B4504787
theorem B1333019 : Blo 1332985 1333019 := bstep (se 1 (by rfl) ⟨999764, by rfl⟩ : syracuseStep 1333019 = 1999529) B1999529
theorem B2251199 : Blo 1332985 2251199 := bstep (se 1 (by rfl) ⟨1688399, by rfl⟩ : syracuseStep 2251199 = 3376799) B3376799
theorem B175512491 : Blo 1332985 175512491 := bstep (se 1 (by rfl) ⟨131634368, by rfl⟩ : syracuseStep 175512491 = 263268737) B263268737
theorem B7601147 : Blo 1332985 7601147 := bstep (se 1 (by rfl) ⟨5700860, by rfl⟩ : syracuseStep 7601147 = 11401721) B11401721
theorem B1334831 : Blo 1332985 1334831 := bstep (se 1 (by rfl) ⟨1001123, by rfl⟩ : syracuseStep 1334831 = 2002247) B2002247
theorem B281010809 : Blo 1332985 281010809 := bstep (se 2 (by rfl) ⟨105379053, by rfl⟩ : syracuseStep 281010809 = 210758107) B210758107
theorem B2999231 : Blo 1332985 2999231 := bstep (se 1 (by rfl) ⟨2249423, by rfl⟩ : syracuseStep 2999231 = 4498847) B4498847
theorem B1500799 : Blo 1332985 1500799 := bstep (se 1 (by rfl) ⟨1125599, by rfl⟩ : syracuseStep 1500799 = 2251199) B2251199
theorem B117008327 : Blo 1332985 117008327 := bstep (se 1 (by rfl) ⟨87756245, by rfl⟩ : syracuseStep 117008327 = 175512491) B175512491
theorem B2002127 : Blo 1332985 2002127 := bstep (se 1 (by rfl) ⟨1501595, by rfl⟩ : syracuseStep 2002127 = 3003191) B3003191
theorem B5067431 : Blo 1332985 5067431 := bstep (se 1 (by rfl) ⟨3800573, by rfl⟩ : syracuseStep 5067431 = 7601147) B7601147
theorem B1999487 : Blo 1332985 1999487 := bstep (se 1 (by rfl) ⟨1499615, by rfl⟩ : syracuseStep 1999487 = 2999231) B2999231
theorem B78005551 : Blo 1332985 78005551 := bstep (se 1 (by rfl) ⟨58504163, by rfl⟩ : syracuseStep 78005551 = 117008327) B117008327
theorem B2001065 : Blo 1332985 2001065 := bstep (se 2 (by rfl) ⟨750399, by rfl⟩ : syracuseStep 2001065 = 1500799) B1500799
theorem B3378287 : Blo 1332985 3378287 := bstep (se 1 (by rfl) ⟨2533715, by rfl⟩ : syracuseStep 3378287 = 5067431) B5067431
theorem B187340539 : Blo 1332985 187340539 := bstep (se 1 (by rfl) ⟨140505404, by rfl⟩ : syracuseStep 187340539 = 281010809) B281010809
theorem B1334751 : Blo 1332985 1334751 := bstep (se 1 (by rfl) ⟨1001063, by rfl⟩ : syracuseStep 1334751 = 2002127) B2002127
theorem B104007401 : Blo 1332985 104007401 := bstep (se 2 (by rfl) ⟨39002775, by rfl⟩ : syracuseStep 104007401 = 78005551) B78005551
theorem B249787385 : Blo 1332985 249787385 := bstep (se 2 (by rfl) ⟨93670269, by rfl⟩ : syracuseStep 249787385 = 187340539) B187340539
theorem B1332991 : Blo 1332985 1332991 := bstep (se 1 (by rfl) ⟨999743, by rfl⟩ : syracuseStep 1332991 = 1999487) B1999487
theorem B1334043 : Blo 1332985 1334043 := bstep (se 1 (by rfl) ⟨1000532, by rfl⟩ : syracuseStep 1334043 = 2001065) B2001065
theorem B2252191 : Blo 1332985 2252191 := bstep (se 1 (by rfl) ⟨1689143, by rfl⟩ : syracuseStep 2252191 = 3378287) B3378287
theorem B69338267 : Blo 1332985 69338267 := bstep (se 1 (by rfl) ⟨52003700, by rfl⟩ : syracuseStep 69338267 = 104007401) B104007401
theorem B3002921 : Blo 1332985 3002921 := bstep (se 2 (by rfl) ⟨1126095, by rfl⟩ : syracuseStep 3002921 = 2252191) B2252191
theorem B166524923 : Blo 1332985 166524923 := bstep (se 1 (by rfl) ⟨124893692, by rfl⟩ : syracuseStep 166524923 = 249787385) B249787385
theorem B2001947 : Blo 1332985 2001947 := bstep (se 1 (by rfl) ⟨1501460, by rfl⟩ : syracuseStep 2001947 = 3002921) B3002921
theorem B46225511 : Blo 1332985 46225511 := bstep (se 1 (by rfl) ⟨34669133, by rfl⟩ : syracuseStep 46225511 = 69338267) B69338267
theorem B111016615 : Blo 1332985 111016615 := bstep (se 1 (by rfl) ⟨83262461, by rfl⟩ : syracuseStep 111016615 = 166524923) B166524923
theorem B148022153 : Blo 1332985 148022153 := bstep (se 2 (by rfl) ⟨55508307, by rfl⟩ : syracuseStep 148022153 = 111016615) B111016615
theorem B30817007 : Blo 1332985 30817007 := bstep (se 1 (by rfl) ⟨23112755, by rfl⟩ : syracuseStep 30817007 = 46225511) B46225511
theorem B1334631 : Blo 1332985 1334631 := bstep (se 1 (by rfl) ⟨1000973, by rfl⟩ : syracuseStep 1334631 = 2001947) B2001947
theorem B98681435 : Blo 1332985 98681435 := bstep (se 1 (by rfl) ⟨74011076, by rfl⟩ : syracuseStep 98681435 = 148022153) B148022153
theorem B20544671 : Blo 1332985 20544671 := bstep (se 1 (by rfl) ⟨15408503, by rfl⟩ : syracuseStep 20544671 = 30817007) B30817007
theorem B65787623 : Blo 1332985 65787623 := bstep (se 1 (by rfl) ⟨49340717, by rfl⟩ : syracuseStep 65787623 = 98681435) B98681435
theorem B13696447 : Blo 1332985 13696447 := bstep (se 1 (by rfl) ⟨10272335, by rfl⟩ : syracuseStep 13696447 = 20544671) B20544671
theorem B18261929 : Blo 1332985 18261929 := bstep (se 2 (by rfl) ⟨6848223, by rfl⟩ : syracuseStep 18261929 = 13696447) B13696447
theorem B43858415 : Blo 1332985 43858415 := bstep (se 1 (by rfl) ⟨32893811, by rfl⟩ : syracuseStep 43858415 = 65787623) B65787623
theorem B12174619 : Blo 1332985 12174619 := bstep (se 1 (by rfl) ⟨9130964, by rfl⟩ : syracuseStep 12174619 = 18261929) B18261929
theorem B29238943 : Blo 1332985 29238943 := bstep (se 1 (by rfl) ⟨21929207, by rfl⟩ : syracuseStep 29238943 = 43858415) B43858415
theorem B16232825 : Blo 1332985 16232825 := bstep (se 2 (by rfl) ⟨6087309, by rfl⟩ : syracuseStep 16232825 = 12174619) B12174619
theorem B38985257 : Blo 1332985 38985257 := bstep (se 2 (by rfl) ⟨14619471, by rfl⟩ : syracuseStep 38985257 = 29238943) B29238943
theorem B43287533 : Blo 1332985 43287533 := bstep (se 3 (by rfl) ⟨8116412, by rfl⟩ : syracuseStep 43287533 = 16232825) B16232825
theorem B103960685 : Blo 1332985 103960685 := bstep (se 3 (by rfl) ⟨19492628, by rfl⟩ : syracuseStep 103960685 = 38985257) B38985257
theorem B277228493 : Blo 1332985 277228493 := bstep (se 3 (by rfl) ⟨51980342, by rfl⟩ : syracuseStep 277228493 = 103960685) B103960685
theorem B28858355 : Blo 1332985 28858355 := bstep (se 1 (by rfl) ⟨21643766, by rfl⟩ : syracuseStep 28858355 = 43287533) B43287533
theorem B19238903 : Blo 1332985 19238903 := bstep (se 1 (by rfl) ⟨14429177, by rfl⟩ : syracuseStep 19238903 = 28858355) B28858355
theorem B184818995 : Blo 1332985 184818995 := bstep (se 1 (by rfl) ⟨138614246, by rfl⟩ : syracuseStep 184818995 = 277228493) B277228493
theorem B123212663 : Blo 1332985 123212663 := bstep (se 1 (by rfl) ⟨92409497, by rfl⟩ : syracuseStep 123212663 = 184818995) B184818995
theorem B12825935 : Blo 1332985 12825935 := bstep (se 1 (by rfl) ⟨9619451, by rfl⟩ : syracuseStep 12825935 = 19238903) B19238903
theorem B82141775 : Blo 1332985 82141775 := bstep (se 1 (by rfl) ⟨61606331, by rfl⟩ : syracuseStep 82141775 = 123212663) B123212663
theorem B8550623 : Blo 1332985 8550623 := bstep (se 1 (by rfl) ⟨6412967, by rfl⟩ : syracuseStep 8550623 = 12825935) B12825935
theorem B22801661 : Blo 1332985 22801661 := bstep (se 3 (by rfl) ⟨4275311, by rfl⟩ : syracuseStep 22801661 = 8550623) B8550623
theorem B54761183 : Blo 1332985 54761183 := bstep (se 1 (by rfl) ⟨41070887, by rfl⟩ : syracuseStep 54761183 = 82141775) B82141775
theorem B36507455 : Blo 1332985 36507455 := bstep (se 1 (by rfl) ⟨27380591, by rfl⟩ : syracuseStep 36507455 = 54761183) B54761183
theorem B15201107 : Blo 1332985 15201107 := bstep (se 1 (by rfl) ⟨11400830, by rfl⟩ : syracuseStep 15201107 = 22801661) B22801661
theorem B10134071 : Blo 1332985 10134071 := bstep (se 1 (by rfl) ⟨7600553, by rfl⟩ : syracuseStep 10134071 = 15201107) B15201107
theorem B24338303 : Blo 1332985 24338303 := bstep (se 1 (by rfl) ⟨18253727, by rfl⟩ : syracuseStep 24338303 = 36507455) B36507455
theorem B16225535 : Blo 1332985 16225535 := bstep (se 1 (by rfl) ⟨12169151, by rfl⟩ : syracuseStep 16225535 = 24338303) B24338303
theorem B6756047 : Blo 1332985 6756047 := bstep (se 1 (by rfl) ⟨5067035, by rfl⟩ : syracuseStep 6756047 = 10134071) B10134071
theorem B10817023 : Blo 1332985 10817023 := bstep (se 1 (by rfl) ⟨8112767, by rfl⟩ : syracuseStep 10817023 = 16225535) B16225535
theorem B4504031 : Blo 1332985 4504031 := bstep (se 1 (by rfl) ⟨3378023, by rfl⟩ : syracuseStep 4504031 = 6756047) B6756047
theorem B3002687 : Blo 1332985 3002687 := bstep (se 1 (by rfl) ⟨2252015, by rfl⟩ : syracuseStep 3002687 = 4504031) B4504031
theorem B14422697 : Blo 1332985 14422697 := bstep (se 2 (by rfl) ⟨5408511, by rfl⟩ : syracuseStep 14422697 = 10817023) B10817023
theorem B2001791 : Blo 1332985 2001791 := bstep (se 1 (by rfl) ⟨1501343, by rfl⟩ : syracuseStep 2001791 = 3002687) B3002687
theorem B9615131 : Blo 1332985 9615131 := bstep (se 1 (by rfl) ⟨7211348, by rfl⟩ : syracuseStep 9615131 = 14422697) B14422697
theorem B6410087 : Blo 1332985 6410087 := bstep (se 1 (by rfl) ⟨4807565, by rfl⟩ : syracuseStep 6410087 = 9615131) B9615131
theorem B1334527 : Blo 1332985 1334527 := bstep (se 1 (by rfl) ⟨1000895, by rfl⟩ : syracuseStep 1334527 = 2001791) B2001791
theorem B4273391 : Blo 1332985 4273391 := bstep (se 1 (by rfl) ⟨3205043, by rfl⟩ : syracuseStep 4273391 = 6410087) B6410087
theorem B2848927 : Blo 1332985 2848927 := bstep (se 1 (by rfl) ⟨2136695, by rfl⟩ : syracuseStep 2848927 = 4273391) B4273391
theorem B3798569 : Blo 1332985 3798569 := bstep (se 2 (by rfl) ⟨1424463, by rfl⟩ : syracuseStep 3798569 = 2848927) B2848927
theorem B2532379 : Blo 1332985 2532379 := bstep (se 1 (by rfl) ⟨1899284, by rfl⟩ : syracuseStep 2532379 = 3798569) B3798569
theorem B3376505 : Blo 1332985 3376505 := bstep (se 2 (by rfl) ⟨1266189, by rfl⟩ : syracuseStep 3376505 = 2532379) B2532379
theorem B2251003 : Blo 1332985 2251003 := bstep (se 1 (by rfl) ⟨1688252, by rfl⟩ : syracuseStep 2251003 = 3376505) B3376505
theorem B3001337 : Blo 1332985 3001337 := bstep (se 2 (by rfl) ⟨1125501, by rfl⟩ : syracuseStep 3001337 = 2251003) B2251003
theorem B2000891 : Blo 1332985 2000891 := bstep (se 1 (by rfl) ⟨1500668, by rfl⟩ : syracuseStep 2000891 = 3001337) B3001337
theorem B1333927 : Blo 1332985 1333927 := bstep (se 1 (by rfl) ⟨1000445, by rfl⟩ : syracuseStep 1333927 = 2000891) B2000891

theorem C0 (j : ℕ) (h1 : 333246 ≤ j) (h2 : j ≤ 333745) : Blo 1332985 (4 * j + 3) := by
  interval_cases j
  · exact B1332987
  · exact B1332991
  · exact B1332995
  · exact B1332999
  · exact B1333003
  · exact B1333007
  · exact B1333011
  · exact B1333015
  · exact B1333019
  · exact B1333023
  · exact B1333027
  · exact B1333031
  · exact B1333035
  · exact B1333039
  · exact B1333043
  · exact B1333047
  · exact B1333051
  · exact B1333055
  · exact B1333059
  · exact B1333063
  · exact B1333067
  · exact B1333071
  · exact B1333075
  · exact B1333079
  · exact B1333083
  · exact B1333087
  · exact B1333091
  · exact B1333095
  · exact B1333099
  · exact B1333103
  · exact B1333107
  · exact B1333111
  · exact B1333115
  · exact B1333119
  · exact B1333123
  · exact B1333127
  · exact B1333131
  · exact B1333135
  · exact B1333139
  · exact B1333143
  · exact B1333147
  · exact B1333151
  · exact B1333155
  · exact B1333159
  · exact B1333163
  · exact B1333167
  · exact B1333171
  · exact B1333175
  · exact B1333179
  · exact B1333183
  · exact B1333187
  · exact B1333191
  · exact B1333195
  · exact B1333199
  · exact B1333203
  · exact B1333207
  · exact B1333211
  · exact B1333215
  · exact B1333219
  · exact B1333223
  · exact B1333227
  · exact B1333231
  · exact B1333235
  · exact B1333239
  · exact B1333243
  · exact B1333247
  · exact B1333251
  · exact B1333255
  · exact B1333259
  · exact B1333263
  · exact B1333267
  · exact B1333271
  · exact B1333275
  · exact B1333279
  · exact B1333283
  · exact B1333287
  · exact B1333291
  · exact B1333295
  · exact B1333299
  · exact B1333303
  · exact B1333307
  · exact B1333311
  · exact B1333315
  · exact B1333319
  · exact B1333323
  · exact B1333327
  · exact B1333331
  · exact B1333335
  · exact B1333339
  · exact B1333343
  · exact B1333347
  · exact B1333351
  · exact B1333355
  · exact B1333359
  · exact B1333363
  · exact B1333367
  · exact B1333371
  · exact B1333375
  · exact B1333379
  · exact B1333383
  · exact B1333387
  · exact B1333391
  · exact B1333395
  · exact B1333399
  · exact B1333403
  · exact B1333407
  · exact B1333411
  · exact B1333415
  · exact B1333419
  · exact B1333423
  · exact B1333427
  · exact B1333431
  · exact B1333435
  · exact B1333439
  · exact B1333443
  · exact B1333447
  · exact B1333451
  · exact B1333455
  · exact B1333459
  · exact B1333463
  · exact B1333467
  · exact B1333471
  · exact B1333475
  · exact B1333479
  · exact B1333483
  · exact B1333487
  · exact B1333491
  · exact B1333495
  · exact B1333499
  · exact B1333503
  · exact B1333507
  · exact B1333511
  · exact B1333515
  · exact B1333519
  · exact B1333523
  · exact B1333527
  · exact B1333531
  · exact B1333535
  · exact B1333539
  · exact B1333543
  · exact B1333547
  · exact B1333551
  · exact B1333555
  · exact B1333559
  · exact B1333563
  · exact B1333567
  · exact B1333571
  · exact B1333575
  · exact B1333579
  · exact B1333583
  · exact B1333587
  · exact B1333591
  · exact B1333595
  · exact B1333599
  · exact B1333603
  · exact B1333607
  · exact B1333611
  · exact B1333615
  · exact B1333619
  · exact B1333623
  · exact B1333627
  · exact B1333631
  · exact B1333635
  · exact B1333639
  · exact B1333643
  · exact B1333647
  · exact B1333651
  · exact B1333655
  · exact B1333659
  · exact B1333663
  · exact B1333667
  · exact B1333671
  · exact B1333675
  · exact B1333679
  · exact B1333683
  · exact B1333687
  · exact B1333691
  · exact B1333695
  · exact B1333699
  · exact B1333703
  · exact B1333707
  · exact B1333711
  · exact B1333715
  · exact B1333719
  · exact B1333723
  · exact B1333727
  · exact B1333731
  · exact B1333735
  · exact B1333739
  · exact B1333743
  · exact B1333747
  · exact B1333751
  · exact B1333755
  · exact B1333759
  · exact B1333763
  · exact B1333767
  · exact B1333771
  · exact B1333775
  · exact B1333779
  · exact B1333783
  · exact B1333787
  · exact B1333791
  · exact B1333795
  · exact B1333799
  · exact B1333803
  · exact B1333807
  · exact B1333811
  · exact B1333815
  · exact B1333819
  · exact B1333823
  · exact B1333827
  · exact B1333831
  · exact B1333835
  · exact B1333839
  · exact B1333843
  · exact B1333847
  · exact B1333851
  · exact B1333855
  · exact B1333859
  · exact B1333863
  · exact B1333867
  · exact B1333871
  · exact B1333875
  · exact B1333879
  · exact B1333883
  · exact B1333887
  · exact B1333891
  · exact B1333895
  · exact B1333899
  · exact B1333903
  · exact B1333907
  · exact B1333911
  · exact B1333915
  · exact B1333919
  · exact B1333923
  · exact B1333927
  · exact B1333931
  · exact B1333935
  · exact B1333939
  · exact B1333943
  · exact B1333947
  · exact B1333951
  · exact B1333955
  · exact B1333959
  · exact B1333963
  · exact B1333967
  · exact B1333971
  · exact B1333975
  · exact B1333979
  · exact B1333983
  · exact B1333987
  · exact B1333991
  · exact B1333995
  · exact B1333999
  · exact B1334003
  · exact B1334007
  · exact B1334011
  · exact B1334015
  · exact B1334019
  · exact B1334023
  · exact B1334027
  · exact B1334031
  · exact B1334035
  · exact B1334039
  · exact B1334043
  · exact B1334047
  · exact B1334051
  · exact B1334055
  · exact B1334059
  · exact B1334063
  · exact B1334067
  · exact B1334071
  · exact B1334075
  · exact B1334079
  · exact B1334083
  · exact B1334087
  · exact B1334091
  · exact B1334095
  · exact B1334099
  · exact B1334103
  · exact B1334107
  · exact B1334111
  · exact B1334115
  · exact B1334119
  · exact B1334123
  · exact B1334127
  · exact B1334131
  · exact B1334135
  · exact B1334139
  · exact B1334143
  · exact B1334147
  · exact B1334151
  · exact B1334155
  · exact B1334159
  · exact B1334163
  · exact B1334167
  · exact B1334171
  · exact B1334175
  · exact B1334179
  · exact B1334183
  · exact B1334187
  · exact B1334191
  · exact B1334195
  · exact B1334199
  · exact B1334203
  · exact B1334207
  · exact B1334211
  · exact B1334215
  · exact B1334219
  · exact B1334223
  · exact B1334227
  · exact B1334231
  · exact B1334235
  · exact B1334239
  · exact B1334243
  · exact B1334247
  · exact B1334251
  · exact B1334255
  · exact B1334259
  · exact B1334263
  · exact B1334267
  · exact B1334271
  · exact B1334275
  · exact B1334279
  · exact B1334283
  · exact B1334287
  · exact B1334291
  · exact B1334295
  · exact B1334299
  · exact B1334303
  · exact B1334307
  · exact B1334311
  · exact B1334315
  · exact B1334319
  · exact B1334323
  · exact B1334327
  · exact B1334331
  · exact B1334335
  · exact B1334339
  · exact B1334343
  · exact B1334347
  · exact B1334351
  · exact B1334355
  · exact B1334359
  · exact B1334363
  · exact B1334367
  · exact B1334371
  · exact B1334375
  · exact B1334379
  · exact B1334383
  · exact B1334387
  · exact B1334391
  · exact B1334395
  · exact B1334399
  · exact B1334403
  · exact B1334407
  · exact B1334411
  · exact B1334415
  · exact B1334419
  · exact B1334423
  · exact B1334427
  · exact B1334431
  · exact B1334435
  · exact B1334439
  · exact B1334443
  · exact B1334447
  · exact B1334451
  · exact B1334455
  · exact B1334459
  · exact B1334463
  · exact B1334467
  · exact B1334471
  · exact B1334475
  · exact B1334479
  · exact B1334483
  · exact B1334487
  · exact B1334491
  · exact B1334495
  · exact B1334499
  · exact B1334503
  · exact B1334507
  · exact B1334511
  · exact B1334515
  · exact B1334519
  · exact B1334523
  · exact B1334527
  · exact B1334531
  · exact B1334535
  · exact B1334539
  · exact B1334543
  · exact B1334547
  · exact B1334551
  · exact B1334555
  · exact B1334559
  · exact B1334563
  · exact B1334567
  · exact B1334571
  · exact B1334575
  · exact B1334579
  · exact B1334583
  · exact B1334587
  · exact B1334591
  · exact B1334595
  · exact B1334599
  · exact B1334603
  · exact B1334607
  · exact B1334611
  · exact B1334615
  · exact B1334619
  · exact B1334623
  · exact B1334627
  · exact B1334631
  · exact B1334635
  · exact B1334639
  · exact B1334643
  · exact B1334647
  · exact B1334651
  · exact B1334655
  · exact B1334659
  · exact B1334663
  · exact B1334667
  · exact B1334671
  · exact B1334675
  · exact B1334679
  · exact B1334683
  · exact B1334687
  · exact B1334691
  · exact B1334695
  · exact B1334699
  · exact B1334703
  · exact B1334707
  · exact B1334711
  · exact B1334715
  · exact B1334719
  · exact B1334723
  · exact B1334727
  · exact B1334731
  · exact B1334735
  · exact B1334739
  · exact B1334743
  · exact B1334747
  · exact B1334751
  · exact B1334755
  · exact B1334759
  · exact B1334763
  · exact B1334767
  · exact B1334771
  · exact B1334775
  · exact B1334779
  · exact B1334783
  · exact B1334787
  · exact B1334791
  · exact B1334795
  · exact B1334799
  · exact B1334803
  · exact B1334807
  · exact B1334811
  · exact B1334815
  · exact B1334819
  · exact B1334823
  · exact B1334827
  · exact B1334831
  · exact B1334835
  · exact B1334839
  · exact B1334843
  · exact B1334847
  · exact B1334851
  · exact B1334855
  · exact B1334859
  · exact B1334863
  · exact B1334867
  · exact B1334871
  · exact B1334875
  · exact B1334879
  · exact B1334883
  · exact B1334887
  · exact B1334891
  · exact B1334895
  · exact B1334899
  · exact B1334903
  · exact B1334907
  · exact B1334911
  · exact B1334915
  · exact B1334919
  · exact B1334923
  · exact B1334927
  · exact B1334931
  · exact B1334935
  · exact B1334939
  · exact B1334943
  · exact B1334947
  · exact B1334951
  · exact B1334955
  · exact B1334959
  · exact B1334963
  · exact B1334967
  · exact B1334971
  · exact B1334975
  · exact B1334979
  · exact B1334983

theorem solution (m : ℕ) (hlo : 1332985 ≤ m) (hhi : m ≤ 1334985) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 333246 ≤ j := by omega
    have hj2 : j ≤ 333745 := by omega
    have hb : Blo 1332985 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
