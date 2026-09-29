-- Prove2me | solution 1 for syracuse_descends_range_127788_131788
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:33.562359+00:00
-- url     : https://prove2.me/submissions/1d68d924-061a-446c-a5a3-77288c782add

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


theorem B327685 : Blo 127788 327685 := bbase (se 4 (by rfl) ⟨30720, by rfl⟩ : syracuseStep 327685 = 61441) (by norm_num)
theorem B196613 : Blo 127788 196613 := bbase (se 4 (by rfl) ⟨18432, by rfl⟩ : syracuseStep 196613 = 36865) (by norm_num)
theorem B196637 : Blo 127788 196637 := bbase (se 3 (by rfl) ⟨36869, by rfl⟩ : syracuseStep 196637 = 73739) (by norm_num)
theorem B163873 : Blo 127788 163873 := bbase (se 2 (by rfl) ⟨61452, by rfl⟩ : syracuseStep 163873 = 122905) (by norm_num)
theorem B294965 : Blo 127788 294965 := bbase (se 5 (by rfl) ⟨13826, by rfl⟩ : syracuseStep 294965 = 27653) (by norm_num)
theorem B196661 : Blo 127788 196661 := bbase (se 5 (by rfl) ⟨9218, by rfl⟩ : syracuseStep 196661 = 18437) (by norm_num)
theorem B196685 : Blo 127788 196685 := bbase (se 3 (by rfl) ⟨36878, by rfl⟩ : syracuseStep 196685 = 73757) (by norm_num)
theorem B196709 : Blo 127788 196709 := bbase (se 4 (by rfl) ⟨18441, by rfl⟩ : syracuseStep 196709 = 36883) (by norm_num)
theorem B327797 : Blo 127788 327797 := bbase (se 5 (by rfl) ⟨15365, by rfl⟩ : syracuseStep 327797 = 30731) (by norm_num)
theorem B295037 : Blo 127788 295037 := bbase (se 3 (by rfl) ⟨55319, by rfl⟩ : syracuseStep 295037 = 110639) (by norm_num)
theorem B196733 : Blo 127788 196733 := bbase (se 3 (by rfl) ⟨36887, by rfl⟩ : syracuseStep 196733 = 73775) (by norm_num)
theorem B131221 : Blo 127788 131221 := bbase (se 6 (by rfl) ⟨3075, by rfl⟩ : syracuseStep 131221 = 6151) (by norm_num)
theorem B196757 : Blo 127788 196757 := bbase (se 6 (by rfl) ⟨4611, by rfl⟩ : syracuseStep 196757 = 9223) (by norm_num)
theorem B196781 : Blo 127788 196781 := bbase (se 3 (by rfl) ⟨36896, by rfl⟩ : syracuseStep 196781 = 73793) (by norm_num)
theorem B196805 : Blo 127788 196805 := bbase (se 4 (by rfl) ⟨18450, by rfl⟩ : syracuseStep 196805 = 36901) (by norm_num)
theorem B295109 : Blo 127788 295109 := bbase (se 4 (by rfl) ⟨27666, by rfl⟩ : syracuseStep 295109 = 55333) (by norm_num)
theorem B262349 : Blo 127788 262349 := bbase (se 3 (by rfl) ⟨49190, by rfl⟩ : syracuseStep 262349 = 98381) (by norm_num)
theorem B164045 : Blo 127788 164045 := bbase (se 3 (by rfl) ⟨30758, by rfl⟩ : syracuseStep 164045 = 61517) (by norm_num)
theorem B196829 : Blo 127788 196829 := bbase (se 3 (by rfl) ⟨36905, by rfl⟩ : syracuseStep 196829 = 73811) (by norm_num)
theorem B196853 : Blo 127788 196853 := bbase (se 5 (by rfl) ⟨9227, by rfl⟩ : syracuseStep 196853 = 18455) (by norm_num)
theorem B164101 : Blo 127788 164101 := bbase (se 4 (by rfl) ⟨15384, by rfl⟩ : syracuseStep 164101 = 30769) (by norm_num)
theorem B295181 : Blo 127788 295181 := bbase (se 3 (by rfl) ⟨55346, by rfl⟩ : syracuseStep 295181 = 110693) (by norm_num)
theorem B196877 : Blo 127788 196877 := bbase (se 3 (by rfl) ⟨36914, by rfl⟩ : syracuseStep 196877 = 73829) (by norm_num)
theorem B196901 : Blo 127788 196901 := bbase (se 4 (by rfl) ⟨18459, by rfl⟩ : syracuseStep 196901 = 36919) (by norm_num)
theorem B327989 : Blo 127788 327989 := bbase (se 5 (by rfl) ⟨15374, by rfl⟩ : syracuseStep 327989 = 30749) (by norm_num)
theorem B196925 : Blo 127788 196925 := bbase (se 3 (by rfl) ⟨36923, by rfl⟩ : syracuseStep 196925 = 73847) (by norm_num)
theorem B295253 : Blo 127788 295253 := bbase (se 10 (by rfl) ⟨432, by rfl⟩ : syracuseStep 295253 = 865) (by norm_num)
theorem B196949 : Blo 127788 196949 := bbase (se 10 (by rfl) ⟨288, by rfl⟩ : syracuseStep 196949 = 577) (by norm_num)
theorem B164197 : Blo 127788 164197 := bbase (se 4 (by rfl) ⟨15393, by rfl⟩ : syracuseStep 164197 = 30787) (by norm_num)
theorem B196973 : Blo 127788 196973 := bbase (se 3 (by rfl) ⟨36932, by rfl⟩ : syracuseStep 196973 = 73865) (by norm_num)
theorem B196997 : Blo 127788 196997 := bbase (se 4 (by rfl) ⟨18468, by rfl⟩ : syracuseStep 196997 = 36937) (by norm_num)
theorem B295325 : Blo 127788 295325 := bbase (se 3 (by rfl) ⟨55373, by rfl⟩ : syracuseStep 295325 = 110747) (by norm_num)
theorem B197021 : Blo 127788 197021 := bbase (se 3 (by rfl) ⟨36941, by rfl⟩ : syracuseStep 197021 = 73883) (by norm_num)
theorem B197045 : Blo 127788 197045 := bbase (se 5 (by rfl) ⟨9236, by rfl⟩ : syracuseStep 197045 = 18473) (by norm_num)
theorem B197069 : Blo 127788 197069 := bbase (se 3 (by rfl) ⟨36950, by rfl⟩ : syracuseStep 197069 = 73901) (by norm_num)
theorem B295397 : Blo 127788 295397 := bbase (se 4 (by rfl) ⟨27693, by rfl⟩ : syracuseStep 295397 = 55387) (by norm_num)
theorem B197093 : Blo 127788 197093 := bbase (se 4 (by rfl) ⟨18477, by rfl⟩ : syracuseStep 197093 = 36955) (by norm_num)
theorem B197117 : Blo 127788 197117 := bbase (se 3 (by rfl) ⟨36959, by rfl⟩ : syracuseStep 197117 = 73919) (by norm_num)
theorem B164369 : Blo 127788 164369 := bbase (se 2 (by rfl) ⟨61638, by rfl⟩ : syracuseStep 164369 = 123277) (by norm_num)
theorem B197141 : Blo 127788 197141 := bbase (se 6 (by rfl) ⟨4620, by rfl⟩ : syracuseStep 197141 = 9241) (by norm_num)
theorem B295469 : Blo 127788 295469 := bbase (se 3 (by rfl) ⟨55400, by rfl⟩ : syracuseStep 295469 = 110801) (by norm_num)
theorem B197165 : Blo 127788 197165 := bbase (se 3 (by rfl) ⟨36968, by rfl⟩ : syracuseStep 197165 = 73937) (by norm_num)
theorem B197189 : Blo 127788 197189 := bbase (se 4 (by rfl) ⟨18486, by rfl⟩ : syracuseStep 197189 = 36973) (by norm_num)
theorem B164425 : Blo 127788 164425 := bbase (se 2 (by rfl) ⟨61659, by rfl⟩ : syracuseStep 164425 = 123319) (by norm_num)
theorem B197213 : Blo 127788 197213 := bbase (se 3 (by rfl) ⟨36977, by rfl⟩ : syracuseStep 197213 = 73955) (by norm_num)
theorem B295541 : Blo 127788 295541 := bbase (se 5 (by rfl) ⟨13853, by rfl⟩ : syracuseStep 295541 = 27707) (by norm_num)
theorem B197237 : Blo 127788 197237 := bbase (se 5 (by rfl) ⟨9245, by rfl⟩ : syracuseStep 197237 = 18491) (by norm_num)
theorem B328333 : Blo 127788 328333 := bbase (se 3 (by rfl) ⟨61562, by rfl⟩ : syracuseStep 328333 = 123125) (by norm_num)
theorem B197261 : Blo 127788 197261 := bbase (se 3 (by rfl) ⟨36986, by rfl⟩ : syracuseStep 197261 = 73973) (by norm_num)
theorem B197285 : Blo 127788 197285 := bbase (se 4 (by rfl) ⟨18495, by rfl⟩ : syracuseStep 197285 = 36991) (by norm_num)
theorem B164521 : Blo 127788 164521 := bbase (se 2 (by rfl) ⟨61695, by rfl⟩ : syracuseStep 164521 = 123391) (by norm_num)
theorem B623285 : Blo 127788 623285 := bbase (se 5 (by rfl) ⟨29216, by rfl⟩ : syracuseStep 623285 = 58433) (by norm_num)
theorem B295613 : Blo 127788 295613 := bbase (se 3 (by rfl) ⟨55427, by rfl⟩ : syracuseStep 295613 = 110855) (by norm_num)
theorem B197309 : Blo 127788 197309 := bbase (se 3 (by rfl) ⟨36995, by rfl⟩ : syracuseStep 197309 = 73991) (by norm_num)
theorem B197333 : Blo 127788 197333 := bbase (se 7 (by rfl) ⟨2312, by rfl⟩ : syracuseStep 197333 = 4625) (by norm_num)
theorem B328421 : Blo 127788 328421 := bbase (se 4 (by rfl) ⟨30789, by rfl⟩ : syracuseStep 328421 = 61579) (by norm_num)
theorem B197357 : Blo 127788 197357 := bbase (se 3 (by rfl) ⟨37004, by rfl⟩ : syracuseStep 197357 = 74009) (by norm_num)
theorem B328445 : Blo 127788 328445 := bbase (se 3 (by rfl) ⟨61583, by rfl⟩ : syracuseStep 328445 = 123167) (by norm_num)
theorem B295685 : Blo 127788 295685 := bbase (se 4 (by rfl) ⟨27720, by rfl⟩ : syracuseStep 295685 = 55441) (by norm_num)
theorem B197381 : Blo 127788 197381 := bbase (se 4 (by rfl) ⟨18504, by rfl⟩ : syracuseStep 197381 = 37009) (by norm_num)
theorem B197405 : Blo 127788 197405 := bbase (se 3 (by rfl) ⟨37013, by rfl⟩ : syracuseStep 197405 = 74027) (by norm_num)
theorem B197429 : Blo 127788 197429 := bbase (se 5 (by rfl) ⟨9254, by rfl⟩ : syracuseStep 197429 = 18509) (by norm_num)
theorem B295757 : Blo 127788 295757 := bbase (se 3 (by rfl) ⟨55454, by rfl⟩ : syracuseStep 295757 = 110909) (by norm_num)
theorem B197453 : Blo 127788 197453 := bbase (se 3 (by rfl) ⟨37022, by rfl⟩ : syracuseStep 197453 = 74045) (by norm_num)
theorem B262997 : Blo 127788 262997 := bbase (se 9 (by rfl) ⟨770, by rfl⟩ : syracuseStep 262997 = 1541) (by norm_num)
theorem B164693 : Blo 127788 164693 := bbase (se 9 (by rfl) ⟨482, by rfl⟩ : syracuseStep 164693 = 965) (by norm_num)
theorem B197477 : Blo 127788 197477 := bbase (se 4 (by rfl) ⟨18513, by rfl⟩ : syracuseStep 197477 = 37027) (by norm_num)
theorem B623477 : Blo 127788 623477 := bbase (se 5 (by rfl) ⟨29225, by rfl⟩ : syracuseStep 623477 = 58451) (by norm_num)
theorem B197501 : Blo 127788 197501 := bbase (se 3 (by rfl) ⟨37031, by rfl⟩ : syracuseStep 197501 = 74063) (by norm_num)
theorem B656261 : Blo 127788 656261 := bbase (se 4 (by rfl) ⟨61524, by rfl⟩ : syracuseStep 656261 = 123049) (by norm_num)
theorem B164749 : Blo 127788 164749 := bbase (se 3 (by rfl) ⟨30890, by rfl⟩ : syracuseStep 164749 = 61781) (by norm_num)
theorem B295829 : Blo 127788 295829 := bbase (se 6 (by rfl) ⟨6933, by rfl⟩ : syracuseStep 295829 = 13867) (by norm_num)
theorem B197525 : Blo 127788 197525 := bbase (se 6 (by rfl) ⟨4629, by rfl⟩ : syracuseStep 197525 = 9259) (by norm_num)
theorem B197549 : Blo 127788 197549 := bbase (se 3 (by rfl) ⟨37040, by rfl⟩ : syracuseStep 197549 = 74081) (by norm_num)
theorem B263093 : Blo 127788 263093 := bbase (se 5 (by rfl) ⟨12332, by rfl⟩ : syracuseStep 263093 = 24665) (by norm_num)
theorem B328637 : Blo 127788 328637 := bbase (se 3 (by rfl) ⟨61619, by rfl⟩ : syracuseStep 328637 = 123239) (by norm_num)
theorem B197573 : Blo 127788 197573 := bbase (se 4 (by rfl) ⟨18522, by rfl⟩ : syracuseStep 197573 = 37045) (by norm_num)
theorem B328661 : Blo 127788 328661 := bbase (se 7 (by rfl) ⟨3851, by rfl⟩ : syracuseStep 328661 = 7703) (by norm_num)
theorem B295901 : Blo 127788 295901 := bbase (se 3 (by rfl) ⟨55481, by rfl⟩ : syracuseStep 295901 = 110963) (by norm_num)
theorem B197597 : Blo 127788 197597 := bbase (se 3 (by rfl) ⟨37049, by rfl⟩ : syracuseStep 197597 = 74099) (by norm_num)
theorem B164845 : Blo 127788 164845 := bbase (se 3 (by rfl) ⟨30908, by rfl⟩ : syracuseStep 164845 = 61817) (by norm_num)
theorem B197621 : Blo 127788 197621 := bbase (se 5 (by rfl) ⟨9263, by rfl⟩ : syracuseStep 197621 = 18527) (by norm_num)
theorem B197645 : Blo 127788 197645 := bbase (se 3 (by rfl) ⟨37058, by rfl⟩ : syracuseStep 197645 = 74117) (by norm_num)
theorem B295973 : Blo 127788 295973 := bbase (se 4 (by rfl) ⟨27747, by rfl⟩ : syracuseStep 295973 = 55495) (by norm_num)
theorem B197669 : Blo 127788 197669 := bbase (se 4 (by rfl) ⟨18531, by rfl⟩ : syracuseStep 197669 = 37063) (by norm_num)
theorem B984149 : Blo 127788 984149 := bbase (se 8 (by rfl) ⟨5766, by rfl⟩ : syracuseStep 984149 = 11533) (by norm_num)
theorem B296045 : Blo 127788 296045 := bbase (se 3 (by rfl) ⟨55508, by rfl⟩ : syracuseStep 296045 = 111017) (by norm_num)
theorem B165017 : Blo 127788 165017 := bbase (se 2 (by rfl) ⟨61881, by rfl⟩ : syracuseStep 165017 = 123763) (by norm_num)
theorem B296117 : Blo 127788 296117 := bbase (se 5 (by rfl) ⟨13880, by rfl⟩ : syracuseStep 296117 = 27761) (by norm_num)
theorem B165073 : Blo 127788 165073 := bbase (se 2 (by rfl) ⟨61902, by rfl⟩ : syracuseStep 165073 = 123805) (by norm_num)
theorem B623861 : Blo 127788 623861 := bbase (se 5 (by rfl) ⟨29243, by rfl⟩ : syracuseStep 623861 = 58487) (by norm_num)
theorem B296189 : Blo 127788 296189 := bbase (se 3 (by rfl) ⟨55535, by rfl⟩ : syracuseStep 296189 = 111071) (by norm_num)
theorem B328981 : Blo 127788 328981 := bbase (se 6 (by rfl) ⟨7710, by rfl⟩ : syracuseStep 328981 = 15421) (by norm_num)
theorem B558373 : Blo 127788 558373 := bbase (se 4 (by rfl) ⟨52347, by rfl⟩ : syracuseStep 558373 = 104695) (by norm_num)
theorem B165169 : Blo 127788 165169 := bbase (se 2 (by rfl) ⟨61938, by rfl⟩ : syracuseStep 165169 = 123877) (by norm_num)
theorem B296261 : Blo 127788 296261 := bbase (se 4 (by rfl) ⟨27774, by rfl⟩ : syracuseStep 296261 = 55549) (by norm_num)
theorem B296309 : Blo 127788 296309 := bbase (se 5 (by rfl) ⟨13889, by rfl⟩ : syracuseStep 296309 = 27779) (by norm_num)
theorem B329093 : Blo 127788 329093 := bbase (se 4 (by rfl) ⟨30852, by rfl⟩ : syracuseStep 329093 = 61705) (by norm_num)
theorem B296333 : Blo 127788 296333 := bbase (se 3 (by rfl) ⟨55562, by rfl⟩ : syracuseStep 296333 = 111125) (by norm_num)
theorem B296405 : Blo 127788 296405 := bbase (se 7 (by rfl) ⟨3473, by rfl⟩ : syracuseStep 296405 = 6947) (by norm_num)
theorem B165341 : Blo 127788 165341 := bbase (se 3 (by rfl) ⟨31001, by rfl⟩ : syracuseStep 165341 = 62003) (by norm_num)
theorem B165397 : Blo 127788 165397 := bbase (se 6 (by rfl) ⟨3876, by rfl⟩ : syracuseStep 165397 = 7753) (by norm_num)
theorem B296477 : Blo 127788 296477 := bbase (se 3 (by rfl) ⟨55589, by rfl⟩ : syracuseStep 296477 = 111179) (by norm_num)
theorem B329285 : Blo 127788 329285 := bbase (se 4 (by rfl) ⟨30870, by rfl⟩ : syracuseStep 329285 = 61741) (by norm_num)
theorem B558677 : Blo 127788 558677 := bbase (se 8 (by rfl) ⟨3273, by rfl⟩ : syracuseStep 558677 = 6547) (by norm_num)
theorem B165493 : Blo 127788 165493 := bbase (se 5 (by rfl) ⟨7757, by rfl⟩ : syracuseStep 165493 = 15515) (by norm_num)
theorem B394885 : Blo 127788 394885 := bbase (se 4 (by rfl) ⟨37020, by rfl⟩ : syracuseStep 394885 = 74041) (by norm_num)
theorem B394949 : Blo 127788 394949 := bbase (se 4 (by rfl) ⟨37026, by rfl⟩ : syracuseStep 394949 = 74053) (by norm_num)
theorem B132845 : Blo 127788 132845 := bbase (se 3 (by rfl) ⟨24908, by rfl⟩ : syracuseStep 132845 = 49817) (by norm_num)
theorem B165665 : Blo 127788 165665 := bbase (se 2 (by rfl) ⟨62124, by rfl⟩ : syracuseStep 165665 = 124249) (by norm_num)
theorem B493397 : Blo 127788 493397 := bbase (se 9 (by rfl) ⟨1445, by rfl⟩ : syracuseStep 493397 = 2891) (by norm_num)
theorem B165721 : Blo 127788 165721 := bbase (se 2 (by rfl) ⟨62145, by rfl⟩ : syracuseStep 165721 = 124291) (by norm_num)
theorem B329629 : Blo 127788 329629 := bbase (se 3 (by rfl) ⟨61805, by rfl⟩ : syracuseStep 329629 = 123611) (by norm_num)
theorem B165817 : Blo 127788 165817 := bbase (se 2 (by rfl) ⟨62181, by rfl⟩ : syracuseStep 165817 = 124363) (by norm_num)
theorem B296893 : Blo 127788 296893 := bbase (se 3 (by rfl) ⟨55667, by rfl⟩ : syracuseStep 296893 = 111335) (by norm_num)
theorem B329741 : Blo 127788 329741 := bbase (se 3 (by rfl) ⟨61826, by rfl⟩ : syracuseStep 329741 = 123653) (by norm_num)
theorem B165989 : Blo 127788 165989 := bbase (se 4 (by rfl) ⟨15561, by rfl⟩ : syracuseStep 165989 = 31123) (by norm_num)
theorem B493685 : Blo 127788 493685 := bbase (se 5 (by rfl) ⟨23141, by rfl⟩ : syracuseStep 493685 = 46283) (by norm_num)
theorem B657557 : Blo 127788 657557 := bbase (se 6 (by rfl) ⟨15411, by rfl⟩ : syracuseStep 657557 = 30823) (by norm_num)
theorem B166045 : Blo 127788 166045 := bbase (se 3 (by rfl) ⟨31133, by rfl⟩ : syracuseStep 166045 = 62267) (by norm_num)
theorem B329933 : Blo 127788 329933 := bbase (se 3 (by rfl) ⟨61862, by rfl⟩ : syracuseStep 329933 = 123725) (by norm_num)
theorem B166141 : Blo 127788 166141 := bbase (se 3 (by rfl) ⟨31151, by rfl⟩ : syracuseStep 166141 = 62303) (by norm_num)
theorem B264485 : Blo 127788 264485 := bbase (se 4 (by rfl) ⟨24795, by rfl⟩ : syracuseStep 264485 = 49591) (by norm_num)
theorem B166313 : Blo 127788 166313 := bbase (se 2 (by rfl) ⟨62367, by rfl⟩ : syracuseStep 166313 = 124735) (by norm_num)
theorem B166369 : Blo 127788 166369 := bbase (se 2 (by rfl) ⟨62388, by rfl⟩ : syracuseStep 166369 = 124777) (by norm_num)
theorem B330277 : Blo 127788 330277 := bbase (se 4 (by rfl) ⟨30963, by rfl⟩ : syracuseStep 330277 = 61927) (by norm_num)
theorem B166465 : Blo 127788 166465 := bbase (se 2 (by rfl) ⟨62424, by rfl⟩ : syracuseStep 166465 = 124849) (by norm_num)
theorem B658037 : Blo 127788 658037 := bbase (se 5 (by rfl) ⟨30845, by rfl⟩ : syracuseStep 658037 = 61691) (by norm_num)
theorem B330389 : Blo 127788 330389 := bbase (se 6 (by rfl) ⟨7743, by rfl⟩ : syracuseStep 330389 = 15487) (by norm_num)
theorem B166637 : Blo 127788 166637 := bbase (se 3 (by rfl) ⟨31244, by rfl⟩ : syracuseStep 166637 = 62489) (by norm_num)
theorem B396053 : Blo 127788 396053 := bbase (se 6 (by rfl) ⟨9282, by rfl⟩ : syracuseStep 396053 = 18565) (by norm_num)
theorem B166693 : Blo 127788 166693 := bbase (se 4 (by rfl) ⟨15627, by rfl⟩ : syracuseStep 166693 = 31255) (by norm_num)
theorem B363317 : Blo 127788 363317 := bbase (se 5 (by rfl) ⟨17030, by rfl⟩ : syracuseStep 363317 = 34061) (by norm_num)
theorem B330581 : Blo 127788 330581 := bbase (se 9 (by rfl) ⟨968, by rfl⟩ : syracuseStep 330581 = 1937) (by norm_num)
theorem B166765 : Blo 127788 166765 := bbase (se 3 (by rfl) ⟨31268, by rfl⟩ : syracuseStep 166765 = 62537) (by norm_num)
theorem B166789 : Blo 127788 166789 := bbase (se 4 (by rfl) ⟨15636, by rfl⟩ : syracuseStep 166789 = 31273) (by norm_num)
theorem B330925 : Blo 127788 330925 := bbase (se 3 (by rfl) ⟨62048, by rfl⟩ : syracuseStep 330925 = 124097) (by norm_num)
theorem B494869 : Blo 127788 494869 := bbase (se 6 (by rfl) ⟨11598, by rfl⟩ : syracuseStep 494869 = 23197) (by norm_num)
theorem B331037 : Blo 127788 331037 := bbase (se 3 (by rfl) ⟨62069, by rfl⟩ : syracuseStep 331037 = 124139) (by norm_num)
theorem B658853 : Blo 127788 658853 := bbase (se 4 (by rfl) ⟨61767, by rfl⟩ : syracuseStep 658853 = 123535) (by norm_num)
theorem B331229 : Blo 127788 331229 := bbase (se 3 (by rfl) ⟨62105, by rfl⟩ : syracuseStep 331229 = 124211) (by norm_num)
theorem B495173 : Blo 127788 495173 := bbase (se 4 (by rfl) ⟨46422, by rfl⟩ : syracuseStep 495173 = 92845) (by norm_num)
theorem B265909 : Blo 127788 265909 := bbase (se 5 (by rfl) ⟨12464, by rfl⟩ : syracuseStep 265909 = 24929) (by norm_num)
theorem B659141 : Blo 127788 659141 := bbase (se 4 (by rfl) ⟨61794, by rfl⟩ : syracuseStep 659141 = 123589) (by norm_num)
theorem B265933 : Blo 127788 265933 := bbase (se 3 (by rfl) ⟨49862, by rfl⟩ : syracuseStep 265933 = 99725) (by norm_num)
theorem B331573 : Blo 127788 331573 := bbase (se 5 (by rfl) ⟨15542, by rfl⟩ : syracuseStep 331573 = 31085) (by norm_num)
theorem B331685 : Blo 127788 331685 := bbase (se 4 (by rfl) ⟨31095, by rfl⟩ : syracuseStep 331685 = 62191) (by norm_num)
theorem B331877 : Blo 127788 331877 := bbase (se 4 (by rfl) ⟨31113, by rfl⟩ : syracuseStep 331877 = 62227) (by norm_num)
theorem B135397 : Blo 127788 135397 := bbase (se 4 (by rfl) ⟨12693, by rfl⟩ : syracuseStep 135397 = 25387) (by norm_num)
theorem B233861 : Blo 127788 233861 := bbase (se 4 (by rfl) ⟨21924, by rfl⟩ : syracuseStep 233861 = 43849) (by norm_num)
theorem B332221 : Blo 127788 332221 := bbase (se 3 (by rfl) ⟨62291, by rfl⟩ : syracuseStep 332221 = 124583) (by norm_num)
theorem B365093 : Blo 127788 365093 := bbase (se 4 (by rfl) ⟨34227, by rfl⟩ : syracuseStep 365093 = 68455) (by norm_num)
theorem B332333 : Blo 127788 332333 := bbase (se 3 (by rfl) ⟨62312, by rfl⟩ : syracuseStep 332333 = 124625) (by norm_num)
theorem B168517 : Blo 127788 168517 := bbase (se 4 (by rfl) ⟨15798, by rfl⟩ : syracuseStep 168517 = 31597) (by norm_num)
theorem B660149 : Blo 127788 660149 := bbase (se 5 (by rfl) ⟨30944, by rfl⟩ : syracuseStep 660149 = 61889) (by norm_num)
theorem B332525 : Blo 127788 332525 := bbase (se 3 (by rfl) ⟨62348, by rfl⟩ : syracuseStep 332525 = 124697) (by norm_num)
theorem B135941 : Blo 127788 135941 := bbase (se 4 (by rfl) ⟨12744, by rfl⟩ : syracuseStep 135941 = 25489) (by norm_num)
theorem B168809 : Blo 127788 168809 := bbase (se 2 (by rfl) ⟨63303, by rfl⟩ : syracuseStep 168809 = 126607) (by norm_num)
theorem B332693 : Blo 127788 332693 := bbase (se 6 (by rfl) ⟨7797, by rfl⟩ : syracuseStep 332693 = 15595) (by norm_num)
theorem B332765 : Blo 127788 332765 := bbase (se 3 (by rfl) ⟨62393, by rfl⟩ : syracuseStep 332765 = 124787) (by norm_num)
theorem B332869 : Blo 127788 332869 := bbase (se 4 (by rfl) ⟨31206, by rfl⟩ : syracuseStep 332869 = 62413) (by norm_num)
theorem B332981 : Blo 127788 332981 := bbase (se 5 (by rfl) ⟨15608, by rfl⟩ : syracuseStep 332981 = 31217) (by norm_num)
theorem B988469 : Blo 127788 988469 := bbase (se 5 (by rfl) ⟨46334, by rfl⟩ : syracuseStep 988469 = 92669) (by norm_num)
theorem B136513 : Blo 127788 136513 := bbase (se 2 (by rfl) ⟨51192, by rfl⟩ : syracuseStep 136513 = 102385) (by norm_num)
theorem B333173 : Blo 127788 333173 := bbase (se 5 (by rfl) ⟨15617, by rfl⟩ : syracuseStep 333173 = 31235) (by norm_num)
theorem B136585 : Blo 127788 136585 := bbase (se 2 (by rfl) ⟨51219, by rfl⟩ : syracuseStep 136585 = 102439) (by norm_num)
theorem B628165 : Blo 127788 628165 := bbase (se 4 (by rfl) ⟨58890, by rfl⟩ : syracuseStep 628165 = 117781) (by norm_num)
theorem B431621 : Blo 127788 431621 := bbase (se 4 (by rfl) ⟨40464, by rfl⟩ : syracuseStep 431621 = 80929) (by norm_num)
theorem B235037 : Blo 127788 235037 := bbase (se 3 (by rfl) ⟨44069, by rfl⟩ : syracuseStep 235037 = 88139) (by norm_num)
theorem B136765 : Blo 127788 136765 := bbase (se 3 (by rfl) ⟨25643, by rfl⟩ : syracuseStep 136765 = 51287) (by norm_num)
theorem B497285 : Blo 127788 497285 := bbase (se 4 (by rfl) ⟨46620, by rfl⟩ : syracuseStep 497285 = 93241) (by norm_num)
theorem B366277 : Blo 127788 366277 := bbase (se 4 (by rfl) ⟨34338, by rfl⟩ : syracuseStep 366277 = 68677) (by norm_num)
theorem B333517 : Blo 127788 333517 := bbase (se 3 (by rfl) ⟨62534, by rfl⟩ : syracuseStep 333517 = 125069) (by norm_num)
theorem B235325 : Blo 127788 235325 := bbase (se 3 (by rfl) ⟨44123, by rfl⟩ : syracuseStep 235325 = 88247) (by norm_num)
theorem B366437 : Blo 127788 366437 := bbase (se 4 (by rfl) ⟨34353, by rfl⟩ : syracuseStep 366437 = 68707) (by norm_num)
theorem B497573 : Blo 127788 497573 := bbase (se 4 (by rfl) ⟨46647, by rfl⟩ : syracuseStep 497573 = 93295) (by norm_num)
theorem B432053 : Blo 127788 432053 := bbase (se 5 (by rfl) ⟨20252, by rfl⟩ : syracuseStep 432053 = 40505) (by norm_num)
theorem B661445 : Blo 127788 661445 := bbase (se 4 (by rfl) ⟨62010, by rfl⟩ : syracuseStep 661445 = 124021) (by norm_num)
theorem B137209 : Blo 127788 137209 := bbase (se 2 (by rfl) ⟨51453, by rfl⟩ : syracuseStep 137209 = 102907) (by norm_num)
theorem B563221 : Blo 127788 563221 := bbase (se 6 (by rfl) ⟨13200, by rfl⟩ : syracuseStep 563221 = 26401) (by norm_num)
theorem B366677 : Blo 127788 366677 := bbase (se 8 (by rfl) ⟨2148, by rfl⟩ : syracuseStep 366677 = 4297) (by norm_num)
theorem B137333 : Blo 127788 137333 := bbase (se 5 (by rfl) ⟨6437, by rfl⟩ : syracuseStep 137333 = 12875) (by norm_num)
theorem B366869 : Blo 127788 366869 := bbase (se 6 (by rfl) ⟨8598, by rfl⟩ : syracuseStep 366869 = 17197) (by norm_num)
theorem B432485 : Blo 127788 432485 := bbase (se 4 (by rfl) ⟨40545, by rfl⟩ : syracuseStep 432485 = 81091) (by norm_num)
theorem B137585 : Blo 127788 137585 := bbase (se 2 (by rfl) ⟨51594, by rfl⟩ : syracuseStep 137585 = 103189) (by norm_num)
theorem B432917 : Blo 127788 432917 := bbase (se 6 (by rfl) ⟨10146, by rfl⟩ : syracuseStep 432917 = 20293) (by norm_num)
theorem B138029 : Blo 127788 138029 := bbase (se 3 (by rfl) ⟨25880, by rfl⟩ : syracuseStep 138029 = 51761) (by norm_num)
theorem B138277 : Blo 127788 138277 := bbase (se 4 (by rfl) ⟨12963, by rfl⟩ : syracuseStep 138277 = 25927) (by norm_num)
theorem B498757 : Blo 127788 498757 := bbase (se 4 (by rfl) ⟨46758, by rfl⟩ : syracuseStep 498757 = 93517) (by norm_num)
theorem B236629 : Blo 127788 236629 := bbase (se 8 (by rfl) ⟨1386, by rfl⟩ : syracuseStep 236629 = 2773) (by norm_num)
theorem B466037 : Blo 127788 466037 := bbase (se 5 (by rfl) ⟨21845, by rfl⟩ : syracuseStep 466037 = 43691) (by norm_num)
theorem B433349 : Blo 127788 433349 := bbase (se 4 (by rfl) ⟨40626, by rfl⟩ : syracuseStep 433349 = 81253) (by norm_num)
theorem B662741 : Blo 127788 662741 := bbase (se 7 (by rfl) ⟨7766, by rfl⟩ : syracuseStep 662741 = 15533) (by norm_num)
theorem B236773 : Blo 127788 236773 := bbase (se 4 (by rfl) ⟨22197, by rfl⟩ : syracuseStep 236773 = 44395) (by norm_num)
theorem B367861 : Blo 127788 367861 := bbase (se 5 (by rfl) ⟨17243, by rfl⟩ : syracuseStep 367861 = 34487) (by norm_num)
theorem B466165 : Blo 127788 466165 := bbase (se 5 (by rfl) ⟨21851, by rfl⟩ : syracuseStep 466165 = 43703) (by norm_num)
theorem B335117 : Blo 127788 335117 := bbase (se 3 (by rfl) ⟨62834, by rfl⟩ : syracuseStep 335117 = 125669) (by norm_num)
theorem B499061 : Blo 127788 499061 := bbase (se 5 (by rfl) ⟨23393, by rfl⟩ : syracuseStep 499061 = 46787) (by norm_num)
theorem B269693 : Blo 127788 269693 := bbase (se 3 (by rfl) ⟨50567, by rfl⟩ : syracuseStep 269693 = 101135) (by norm_num)
theorem B138721 : Blo 127788 138721 := bbase (se 2 (by rfl) ⟨52020, by rfl⟩ : syracuseStep 138721 = 104041) (by norm_num)
theorem B237077 : Blo 127788 237077 := bbase (se 6 (by rfl) ⟨5556, by rfl⟩ : syracuseStep 237077 = 11113) (by norm_num)
theorem B138781 : Blo 127788 138781 := bbase (se 3 (by rfl) ⟨26021, by rfl⟩ : syracuseStep 138781 = 52043) (by norm_num)
theorem B433781 : Blo 127788 433781 := bbase (se 5 (by rfl) ⟨20333, by rfl⟩ : syracuseStep 433781 = 40667) (by norm_num)
theorem B2989781 : Blo 127788 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B139097 : Blo 127788 139097 := bbase (se 2 (by rfl) ⟨52161, by rfl⟩ : syracuseStep 139097 = 104323) (by norm_num)
theorem B1253333 : Blo 127788 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B434213 : Blo 127788 434213 := bbase (se 4 (by rfl) ⟨40707, by rfl⟩ : syracuseStep 434213 = 81415) (by norm_num)
theorem B2367701 : Blo 127788 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B139541 : Blo 127788 139541 := bbase (se 6 (by rfl) ⟨3270, by rfl⟩ : syracuseStep 139541 = 6541) (by norm_num)
theorem B205109 : Blo 127788 205109 := bbase (se 5 (by rfl) ⟨9614, by rfl⟩ : syracuseStep 205109 = 19229) (by norm_num)
theorem B368965 : Blo 127788 368965 := bbase (se 4 (by rfl) ⟨34590, by rfl⟩ : syracuseStep 368965 = 69181) (by norm_num)
theorem B139601 : Blo 127788 139601 := bbase (se 2 (by rfl) ⟨52350, by rfl⟩ : syracuseStep 139601 = 104701) (by norm_num)
theorem B827765 : Blo 127788 827765 := bbase (se 5 (by rfl) ⟨38801, by rfl⟩ : syracuseStep 827765 = 77603) (by norm_num)
theorem B139729 : Blo 127788 139729 := bbase (se 2 (by rfl) ⟨52398, by rfl⟩ : syracuseStep 139729 = 104797) (by norm_num)
theorem B434645 : Blo 127788 434645 := bbase (se 7 (by rfl) ⟨5093, by rfl⟩ : syracuseStep 434645 = 10187) (by norm_num)
theorem B664037 : Blo 127788 664037 := bbase (se 4 (by rfl) ⟨62253, by rfl⟩ : syracuseStep 664037 = 124507) (by norm_num)
theorem B205301 : Blo 127788 205301 := bbase (se 5 (by rfl) ⟨9623, by rfl⟩ : syracuseStep 205301 = 19247) (by norm_num)
theorem B991925 : Blo 127788 991925 := bbase (se 5 (by rfl) ⟨46496, by rfl⟩ : syracuseStep 991925 = 92993) (by norm_num)
theorem B697045 : Blo 127788 697045 := bbase (se 7 (by rfl) ⟨8168, by rfl⟩ : syracuseStep 697045 = 16337) (by norm_num)
theorem B172909 : Blo 127788 172909 := bbase (se 3 (by rfl) ⟨32420, by rfl⟩ : syracuseStep 172909 = 64841) (by norm_num)
theorem B435077 : Blo 127788 435077 := bbase (se 4 (by rfl) ⟨40788, by rfl⟩ : syracuseStep 435077 = 81577) (by norm_num)
theorem B140173 : Blo 127788 140173 := bbase (se 3 (by rfl) ⟨26282, by rfl⟩ : syracuseStep 140173 = 52565) (by norm_num)
theorem B140293 : Blo 127788 140293 := bbase (se 4 (by rfl) ⟨13152, by rfl⟩ : syracuseStep 140293 = 26305) (by norm_num)
theorem B140545 : Blo 127788 140545 := bbase (se 2 (by rfl) ⟨52704, by rfl⟩ : syracuseStep 140545 = 105409) (by norm_num)
theorem B140549 : Blo 127788 140549 := bbase (se 4 (by rfl) ⟨13176, by rfl⟩ : syracuseStep 140549 = 26353) (by norm_num)
theorem B435509 : Blo 127788 435509 := bbase (se 5 (by rfl) ⟨20414, by rfl⟩ : syracuseStep 435509 = 40829) (by norm_num)
theorem B435941 : Blo 127788 435941 := bbase (se 4 (by rfl) ⟨40869, by rfl⟩ : syracuseStep 435941 = 81739) (by norm_num)
theorem B632549 : Blo 127788 632549 := bbase (se 4 (by rfl) ⟨59301, by rfl⟩ : syracuseStep 632549 = 118603) (by norm_num)
theorem B665333 : Blo 127788 665333 := bbase (se 5 (by rfl) ⟨31187, by rfl⟩ : syracuseStep 665333 = 62375) (by norm_num)
theorem B206621 : Blo 127788 206621 := bbase (se 3 (by rfl) ⟨38741, by rfl⟩ : syracuseStep 206621 = 77483) (by norm_num)
theorem B370469 : Blo 127788 370469 := bbase (se 4 (by rfl) ⟨34731, by rfl⟩ : syracuseStep 370469 = 69463) (by norm_num)
theorem B206717 : Blo 127788 206717 := bbase (se 3 (by rfl) ⟨38759, by rfl⟩ : syracuseStep 206717 = 77519) (by norm_num)
theorem B206749 : Blo 127788 206749 := bbase (se 3 (by rfl) ⟨38765, by rfl⟩ : syracuseStep 206749 = 77531) (by norm_num)
theorem B141221 : Blo 127788 141221 := bbase (se 4 (by rfl) ⟨13239, by rfl⟩ : syracuseStep 141221 = 26479) (by norm_num)
theorem B436373 : Blo 127788 436373 := bbase (se 6 (by rfl) ⟨10227, by rfl⟩ : syracuseStep 436373 = 20455) (by norm_num)
theorem B698645 : Blo 127788 698645 := bbase (se 6 (by rfl) ⟨16374, by rfl⟩ : syracuseStep 698645 = 32749) (by norm_num)
theorem B1419605 : Blo 127788 1419605 := bbase (se 10 (by rfl) ⟨2079, by rfl⟩ : syracuseStep 1419605 = 4159) (by norm_num)
theorem B272965 : Blo 127788 272965 := bbase (se 4 (by rfl) ⟨25590, by rfl⟩ : syracuseStep 272965 = 51181) (by norm_num)
theorem B436805 : Blo 127788 436805 := bbase (se 4 (by rfl) ⟨40950, by rfl⟩ : syracuseStep 436805 = 81901) (by norm_num)
theorem B141913 : Blo 127788 141913 := bbase (se 2 (by rfl) ⟨53217, by rfl⟩ : syracuseStep 141913 = 106435) (by norm_num)
theorem B404165 : Blo 127788 404165 := bbase (se 4 (by rfl) ⟨37890, by rfl⟩ : syracuseStep 404165 = 75781) (by norm_num)
theorem B273341 : Blo 127788 273341 := bbase (se 3 (by rfl) ⟨51251, by rfl⟩ : syracuseStep 273341 = 102503) (by norm_num)
theorem B437237 : Blo 127788 437237 := bbase (se 5 (by rfl) ⟨20495, by rfl⟩ : syracuseStep 437237 = 40991) (by norm_num)
theorem B666629 : Blo 127788 666629 := bbase (se 4 (by rfl) ⟨62496, by rfl⟩ : syracuseStep 666629 = 124993) (by norm_num)
theorem B175213 : Blo 127788 175213 := bbase (se 3 (by rfl) ⟨32852, by rfl⟩ : syracuseStep 175213 = 65705) (by norm_num)
theorem B208013 : Blo 127788 208013 := bbase (se 3 (by rfl) ⟨39002, by rfl⟩ : syracuseStep 208013 = 78005) (by norm_num)
theorem B797845 : Blo 127788 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B273709 : Blo 127788 273709 := bbase (se 3 (by rfl) ⟨51320, by rfl⟩ : syracuseStep 273709 = 102641) (by norm_num)
theorem B372053 : Blo 127788 372053 := bbase (se 11 (by rfl) ⟨272, by rfl⟩ : syracuseStep 372053 = 545) (by norm_num)
theorem B208261 : Blo 127788 208261 := bbase (se 4 (by rfl) ⟨19524, by rfl⟩ : syracuseStep 208261 = 39049) (by norm_num)
theorem B437669 : Blo 127788 437669 := bbase (se 4 (by rfl) ⟨41031, by rfl⟩ : syracuseStep 437669 = 82063) (by norm_num)
theorem B438005 : Blo 127788 438005 := bbase (se 5 (by rfl) ⟨20531, by rfl⟩ : syracuseStep 438005 = 41063) (by norm_num)
theorem B438101 : Blo 127788 438101 := bbase (se 9 (by rfl) ⟨1283, by rfl⟩ : syracuseStep 438101 = 2567) (by norm_num)
theorem B372725 : Blo 127788 372725 := bbase (se 5 (by rfl) ⟨17471, by rfl⟩ : syracuseStep 372725 = 34943) (by norm_num)
theorem B667685 : Blo 127788 667685 := bbase (se 4 (by rfl) ⟨62595, by rfl⟩ : syracuseStep 667685 = 125191) (by norm_num)
theorem B634949 : Blo 127788 634949 := bbase (se 4 (by rfl) ⟨59526, by rfl⟩ : syracuseStep 634949 = 119053) (by norm_num)
theorem B208973 : Blo 127788 208973 := bbase (se 3 (by rfl) ⟨39182, by rfl⟩ : syracuseStep 208973 = 78365) (by norm_num)
theorem B438533 : Blo 127788 438533 := bbase (se 4 (by rfl) ⟨41112, by rfl⟩ : syracuseStep 438533 = 82225) (by norm_num)
theorem B176413 : Blo 127788 176413 := bbase (se 3 (by rfl) ⟨33077, by rfl⟩ : syracuseStep 176413 = 66155) (by norm_num)
theorem B471413 : Blo 127788 471413 := bbase (se 5 (by rfl) ⟨22097, by rfl⟩ : syracuseStep 471413 = 44195) (by norm_num)
theorem B373157 : Blo 127788 373157 := bbase (se 4 (by rfl) ⟨34983, by rfl⟩ : syracuseStep 373157 = 69967) (by norm_num)
theorem B143797 : Blo 127788 143797 := bbase (se 5 (by rfl) ⟨6740, by rfl⟩ : syracuseStep 143797 = 13481) (by norm_num)
theorem B143833 : Blo 127788 143833 := bbase (se 2 (by rfl) ⟨53937, by rfl⟩ : syracuseStep 143833 = 107875) (by norm_num)
theorem B143869 : Blo 127788 143869 := bbase (se 3 (by rfl) ⟨26975, by rfl⟩ : syracuseStep 143869 = 53951) (by norm_num)
theorem B143905 : Blo 127788 143905 := bbase (se 2 (by rfl) ⟨53964, by rfl⟩ : syracuseStep 143905 = 107929) (by norm_num)
theorem B143941 : Blo 127788 143941 := bbase (se 4 (by rfl) ⟨13494, by rfl⟩ : syracuseStep 143941 = 26989) (by norm_num)
theorem B143977 : Blo 127788 143977 := bbase (se 2 (by rfl) ⟨53991, by rfl⟩ : syracuseStep 143977 = 107983) (by norm_num)
theorem B144013 : Blo 127788 144013 := bbase (se 3 (by rfl) ⟨27002, by rfl⟩ : syracuseStep 144013 = 54005) (by norm_num)
theorem B144049 : Blo 127788 144049 := bbase (se 2 (by rfl) ⟨54018, by rfl⟩ : syracuseStep 144049 = 108037) (by norm_num)
theorem B438965 : Blo 127788 438965 := bbase (se 5 (by rfl) ⟨20576, by rfl⟩ : syracuseStep 438965 = 41153) (by norm_num)
theorem B144085 : Blo 127788 144085 := bbase (se 7 (by rfl) ⟨1688, by rfl⟩ : syracuseStep 144085 = 3377) (by norm_num)
theorem B209645 : Blo 127788 209645 := bbase (se 3 (by rfl) ⟨39308, by rfl⟩ : syracuseStep 209645 = 78617) (by norm_num)
theorem B144121 : Blo 127788 144121 := bbase (se 2 (by rfl) ⟨54045, by rfl⟩ : syracuseStep 144121 = 108091) (by norm_num)
theorem B275213 : Blo 127788 275213 := bbase (se 3 (by rfl) ⟨51602, by rfl⟩ : syracuseStep 275213 = 103205) (by norm_num)
theorem B144157 : Blo 127788 144157 := bbase (se 3 (by rfl) ⟨27029, by rfl⟩ : syracuseStep 144157 = 54059) (by norm_num)
theorem B144193 : Blo 127788 144193 := bbase (se 2 (by rfl) ⟨54072, by rfl⟩ : syracuseStep 144193 = 108145) (by norm_num)
theorem B144229 : Blo 127788 144229 := bbase (se 4 (by rfl) ⟨13521, by rfl⟩ : syracuseStep 144229 = 27043) (by norm_num)
theorem B144265 : Blo 127788 144265 := bbase (se 2 (by rfl) ⟨54099, by rfl⟩ : syracuseStep 144265 = 108199) (by norm_num)
theorem B275357 : Blo 127788 275357 := bbase (se 3 (by rfl) ⟨51629, by rfl⟩ : syracuseStep 275357 = 103259) (by norm_num)
theorem B177061 : Blo 127788 177061 := bbase (se 4 (by rfl) ⟨16599, by rfl⟩ : syracuseStep 177061 = 33199) (by norm_num)
theorem B242605 : Blo 127788 242605 := bbase (se 3 (by rfl) ⟨45488, by rfl⟩ : syracuseStep 242605 = 90977) (by norm_num)
theorem B144301 : Blo 127788 144301 := bbase (se 3 (by rfl) ⟨27056, by rfl⟩ : syracuseStep 144301 = 54113) (by norm_num)
theorem B144337 : Blo 127788 144337 := bbase (se 2 (by rfl) ⟨54126, by rfl⟩ : syracuseStep 144337 = 108253) (by norm_num)
theorem B144373 : Blo 127788 144373 := bbase (se 5 (by rfl) ⟨6767, by rfl⟩ : syracuseStep 144373 = 13535) (by norm_num)
theorem B766997 : Blo 127788 766997 := bbase (se 6 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 766997 = 35953) (by norm_num)
theorem B144409 : Blo 127788 144409 := bbase (se 2 (by rfl) ⟨54153, by rfl⟩ : syracuseStep 144409 = 108307) (by norm_num)
theorem B144445 : Blo 127788 144445 := bbase (se 3 (by rfl) ⟨27083, by rfl⟩ : syracuseStep 144445 = 54167) (by norm_num)
theorem B144481 : Blo 127788 144481 := bbase (se 2 (by rfl) ⟨54180, by rfl⟩ : syracuseStep 144481 = 108361) (by norm_num)
theorem B439397 : Blo 127788 439397 := bbase (se 4 (by rfl) ⟨41193, by rfl⟩ : syracuseStep 439397 = 82387) (by norm_num)
theorem B144517 : Blo 127788 144517 := bbase (se 4 (by rfl) ⟨13548, by rfl⟩ : syracuseStep 144517 = 27097) (by norm_num)
theorem B373909 : Blo 127788 373909 := bbase (se 6 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 373909 = 17527) (by norm_num)
theorem B144553 : Blo 127788 144553 := bbase (se 2 (by rfl) ⟨54207, by rfl⟩ : syracuseStep 144553 = 108415) (by norm_num)
theorem B144589 : Blo 127788 144589 := bbase (se 3 (by rfl) ⟨27110, by rfl⟩ : syracuseStep 144589 = 54221) (by norm_num)
theorem B242909 : Blo 127788 242909 := bbase (se 3 (by rfl) ⟨45545, by rfl⟩ : syracuseStep 242909 = 91091) (by norm_num)
theorem B210157 : Blo 127788 210157 := bbase (se 3 (by rfl) ⟨39404, by rfl⟩ : syracuseStep 210157 = 78809) (by norm_num)
theorem B144625 : Blo 127788 144625 := bbase (se 2 (by rfl) ⟨54234, by rfl⟩ : syracuseStep 144625 = 108469) (by norm_num)
theorem B275717 : Blo 127788 275717 := bbase (se 4 (by rfl) ⟨25848, by rfl⟩ : syracuseStep 275717 = 51697) (by norm_num)
theorem B144661 : Blo 127788 144661 := bbase (se 6 (by rfl) ⟨3390, by rfl⟩ : syracuseStep 144661 = 6781) (by norm_num)
theorem B144697 : Blo 127788 144697 := bbase (se 2 (by rfl) ⟨54261, by rfl⟩ : syracuseStep 144697 = 108523) (by norm_num)
theorem B144733 : Blo 127788 144733 := bbase (se 3 (by rfl) ⟨27137, by rfl⟩ : syracuseStep 144733 = 54275) (by norm_num)
theorem B144769 : Blo 127788 144769 := bbase (se 2 (by rfl) ⟨54288, by rfl⟩ : syracuseStep 144769 = 108577) (by norm_num)
theorem B144805 : Blo 127788 144805 := bbase (se 4 (by rfl) ⟨13575, by rfl⟩ : syracuseStep 144805 = 27151) (by norm_num)
theorem B144841 : Blo 127788 144841 := bbase (se 2 (by rfl) ⟨54315, by rfl⟩ : syracuseStep 144841 = 108631) (by norm_num)
theorem B308701 : Blo 127788 308701 := bbase (se 3 (by rfl) ⟨57881, by rfl⟩ : syracuseStep 308701 = 115763) (by norm_num)
theorem B144877 : Blo 127788 144877 := bbase (se 3 (by rfl) ⟨27164, by rfl⟩ : syracuseStep 144877 = 54329) (by norm_num)
theorem B144913 : Blo 127788 144913 := bbase (se 2 (by rfl) ⟨54342, by rfl⟩ : syracuseStep 144913 = 108685) (by norm_num)
theorem B734741 : Blo 127788 734741 := bbase (se 6 (by rfl) ⟨17220, by rfl⟩ : syracuseStep 734741 = 34441) (by norm_num)
theorem B439829 : Blo 127788 439829 := bbase (se 6 (by rfl) ⟨10308, by rfl⟩ : syracuseStep 439829 = 20617) (by norm_num)
theorem B144949 : Blo 127788 144949 := bbase (se 5 (by rfl) ⟨6794, by rfl⟩ : syracuseStep 144949 = 13589) (by norm_num)
theorem B144985 : Blo 127788 144985 := bbase (se 2 (by rfl) ⟨54369, by rfl⟩ : syracuseStep 144985 = 108739) (by norm_num)
theorem B145021 : Blo 127788 145021 := bbase (se 3 (by rfl) ⟨27191, by rfl⟩ : syracuseStep 145021 = 54383) (by norm_num)
theorem B145057 : Blo 127788 145057 := bbase (se 2 (by rfl) ⟨54396, by rfl⟩ : syracuseStep 145057 = 108793) (by norm_num)
theorem B210613 : Blo 127788 210613 := bbase (se 5 (by rfl) ⟨9872, by rfl⟩ : syracuseStep 210613 = 19745) (by norm_num)
theorem B145093 : Blo 127788 145093 := bbase (se 4 (by rfl) ⟨13602, by rfl⟩ : syracuseStep 145093 = 27205) (by norm_num)
theorem B145129 : Blo 127788 145129 := bbase (se 2 (by rfl) ⟨54423, by rfl⟩ : syracuseStep 145129 = 108847) (by norm_num)
theorem B145165 : Blo 127788 145165 := bbase (se 3 (by rfl) ⟨27218, by rfl⟩ : syracuseStep 145165 = 54437) (by norm_num)
theorem B145201 : Blo 127788 145201 := bbase (se 2 (by rfl) ⟨54450, by rfl⟩ : syracuseStep 145201 = 108901) (by norm_num)
theorem B145237 : Blo 127788 145237 := bbase (se 9 (by rfl) ⟨425, by rfl⟩ : syracuseStep 145237 = 851) (by norm_num)
theorem B145273 : Blo 127788 145273 := bbase (se 2 (by rfl) ⟨54477, by rfl⟩ : syracuseStep 145273 = 108955) (by norm_num)
theorem B833429 : Blo 127788 833429 := bbase (se 6 (by rfl) ⟨19533, by rfl⟩ : syracuseStep 833429 = 39067) (by norm_num)
theorem B145309 : Blo 127788 145309 := bbase (se 3 (by rfl) ⟨27245, by rfl⟩ : syracuseStep 145309 = 54491) (by norm_num)
theorem B145345 : Blo 127788 145345 := bbase (se 2 (by rfl) ⟨54504, by rfl⟩ : syracuseStep 145345 = 109009) (by norm_num)
theorem B440261 : Blo 127788 440261 := bbase (se 4 (by rfl) ⟨41274, by rfl⟩ : syracuseStep 440261 = 82549) (by norm_num)
theorem B243661 : Blo 127788 243661 := bbase (se 3 (by rfl) ⟨45686, by rfl⟩ : syracuseStep 243661 = 91373) (by norm_num)
theorem B669653 : Blo 127788 669653 := bbase (se 7 (by rfl) ⟨7847, by rfl⟩ : syracuseStep 669653 = 15695) (by norm_num)
theorem B145381 : Blo 127788 145381 := bbase (se 4 (by rfl) ⟨13629, by rfl⟩ : syracuseStep 145381 = 27259) (by norm_num)
theorem B145417 : Blo 127788 145417 := bbase (se 2 (by rfl) ⟨54531, by rfl⟩ : syracuseStep 145417 = 109063) (by norm_num)
theorem B145453 : Blo 127788 145453 := bbase (se 3 (by rfl) ⟨27272, by rfl⟩ : syracuseStep 145453 = 54545) (by norm_num)
theorem B145489 : Blo 127788 145489 := bbase (se 2 (by rfl) ⟨54558, by rfl⟩ : syracuseStep 145489 = 109117) (by norm_num)
theorem B243805 : Blo 127788 243805 := bbase (se 3 (by rfl) ⟨45713, by rfl⟩ : syracuseStep 243805 = 91427) (by norm_num)
theorem B145525 : Blo 127788 145525 := bbase (se 5 (by rfl) ⟨6821, by rfl⟩ : syracuseStep 145525 = 13643) (by norm_num)
theorem B276605 : Blo 127788 276605 := bbase (se 3 (by rfl) ⟨51863, by rfl⟩ : syracuseStep 276605 = 103727) (by norm_num)
theorem B145561 : Blo 127788 145561 := bbase (se 2 (by rfl) ⟨54585, by rfl⟩ : syracuseStep 145561 = 109171) (by norm_num)
theorem B145597 : Blo 127788 145597 := bbase (se 3 (by rfl) ⟨27299, by rfl⟩ : syracuseStep 145597 = 54599) (by norm_num)
theorem B145633 : Blo 127788 145633 := bbase (se 2 (by rfl) ⟨54612, by rfl⟩ : syracuseStep 145633 = 109225) (by norm_num)
theorem B243965 : Blo 127788 243965 := bbase (se 3 (by rfl) ⟨45743, by rfl⟩ : syracuseStep 243965 = 91487) (by norm_num)
theorem B145669 : Blo 127788 145669 := bbase (se 4 (by rfl) ⟨13656, by rfl⟩ : syracuseStep 145669 = 27313) (by norm_num)
theorem B145705 : Blo 127788 145705 := bbase (se 2 (by rfl) ⟨54639, by rfl⟩ : syracuseStep 145705 = 109279) (by norm_num)
theorem B145741 : Blo 127788 145741 := bbase (se 3 (by rfl) ⟨27326, by rfl⟩ : syracuseStep 145741 = 54653) (by norm_num)
theorem B145777 : Blo 127788 145777 := bbase (se 2 (by rfl) ⟨54666, by rfl⟩ : syracuseStep 145777 = 109333) (by norm_num)
theorem B440693 : Blo 127788 440693 := bbase (se 5 (by rfl) ⟨20657, by rfl⟩ : syracuseStep 440693 = 41315) (by norm_num)
theorem B276853 : Blo 127788 276853 := bbase (se 5 (by rfl) ⟨12977, by rfl⟩ : syracuseStep 276853 = 25955) (by norm_num)
theorem B244109 : Blo 127788 244109 := bbase (se 3 (by rfl) ⟨45770, by rfl⟩ : syracuseStep 244109 = 91541) (by norm_num)
theorem B145813 : Blo 127788 145813 := bbase (se 6 (by rfl) ⟨3417, by rfl⟩ : syracuseStep 145813 = 6835) (by norm_num)
theorem B145849 : Blo 127788 145849 := bbase (se 2 (by rfl) ⟨54693, by rfl⟩ : syracuseStep 145849 = 109387) (by norm_num)
theorem B145885 : Blo 127788 145885 := bbase (se 3 (by rfl) ⟨27353, by rfl⟩ : syracuseStep 145885 = 54707) (by norm_num)
theorem B145921 : Blo 127788 145921 := bbase (se 2 (by rfl) ⟨54720, by rfl⟩ : syracuseStep 145921 = 109441) (by norm_num)
theorem B145957 : Blo 127788 145957 := bbase (se 4 (by rfl) ⟨13683, by rfl⟩ : syracuseStep 145957 = 27367) (by norm_num)
theorem B145993 : Blo 127788 145993 := bbase (se 2 (by rfl) ⟨54747, by rfl⟩ : syracuseStep 145993 = 109495) (by norm_num)
theorem B146029 : Blo 127788 146029 := bbase (se 3 (by rfl) ⟨27380, by rfl⟩ : syracuseStep 146029 = 54761) (by norm_num)
theorem B146065 : Blo 127788 146065 := bbase (se 2 (by rfl) ⟨54774, by rfl⟩ : syracuseStep 146065 = 109549) (by norm_num)
theorem B244397 : Blo 127788 244397 := bbase (se 3 (by rfl) ⟨45824, by rfl⟩ : syracuseStep 244397 = 91649) (by norm_num)
theorem B735925 : Blo 127788 735925 := bbase (se 5 (by rfl) ⟨34496, by rfl⟩ : syracuseStep 735925 = 68993) (by norm_num)
theorem B146101 : Blo 127788 146101 := bbase (se 5 (by rfl) ⟨6848, by rfl⟩ : syracuseStep 146101 = 13697) (by norm_num)
theorem B146137 : Blo 127788 146137 := bbase (se 2 (by rfl) ⟨54801, by rfl⟩ : syracuseStep 146137 = 109603) (by norm_num)
theorem B146173 : Blo 127788 146173 := bbase (se 3 (by rfl) ⟨27407, by rfl⟩ : syracuseStep 146173 = 54815) (by norm_num)
theorem B146209 : Blo 127788 146209 := bbase (se 2 (by rfl) ⟨54828, by rfl⟩ : syracuseStep 146209 = 109657) (by norm_num)
theorem B441125 : Blo 127788 441125 := bbase (se 4 (by rfl) ⟨41355, by rfl⟩ : syracuseStep 441125 = 82711) (by norm_num)
theorem B244549 : Blo 127788 244549 := bbase (se 4 (by rfl) ⟨22926, by rfl⟩ : syracuseStep 244549 = 45853) (by norm_num)
theorem B310085 : Blo 127788 310085 := bbase (se 4 (by rfl) ⟨29070, by rfl⟩ : syracuseStep 310085 = 58141) (by norm_num)
theorem B146245 : Blo 127788 146245 := bbase (se 4 (by rfl) ⟨13710, by rfl⟩ : syracuseStep 146245 = 27421) (by norm_num)
theorem B146281 : Blo 127788 146281 := bbase (se 2 (by rfl) ⟨54855, by rfl⟩ : syracuseStep 146281 = 109711) (by norm_num)
theorem B277357 : Blo 127788 277357 := bbase (se 3 (by rfl) ⟨52004, by rfl⟩ : syracuseStep 277357 = 104009) (by norm_num)
theorem B146317 : Blo 127788 146317 := bbase (se 3 (by rfl) ⟨27434, by rfl⟩ : syracuseStep 146317 = 54869) (by norm_num)
theorem B146353 : Blo 127788 146353 := bbase (se 2 (by rfl) ⟨54882, by rfl⟩ : syracuseStep 146353 = 109765) (by norm_num)
theorem B277453 : Blo 127788 277453 := bbase (se 3 (by rfl) ⟨52022, by rfl⟩ : syracuseStep 277453 = 104045) (by norm_num)
theorem B146389 : Blo 127788 146389 := bbase (se 7 (by rfl) ⟨1715, by rfl⟩ : syracuseStep 146389 = 3431) (by norm_num)
theorem B146425 : Blo 127788 146425 := bbase (se 2 (by rfl) ⟨54909, by rfl⟩ : syracuseStep 146425 = 109819) (by norm_num)
theorem B310277 : Blo 127788 310277 := bbase (se 4 (by rfl) ⟨29088, by rfl⟩ : syracuseStep 310277 = 58177) (by norm_num)
theorem B1424405 : Blo 127788 1424405 := bbase (se 6 (by rfl) ⟨33384, by rfl⟩ : syracuseStep 1424405 = 66769) (by norm_num)
theorem B146461 : Blo 127788 146461 := bbase (se 3 (by rfl) ⟨27461, by rfl⟩ : syracuseStep 146461 = 54923) (by norm_num)
theorem B146497 : Blo 127788 146497 := bbase (se 2 (by rfl) ⟨54936, by rfl⟩ : syracuseStep 146497 = 109873) (by norm_num)
theorem B146533 : Blo 127788 146533 := bbase (se 4 (by rfl) ⟨13737, by rfl⟩ : syracuseStep 146533 = 27475) (by norm_num)
theorem B244853 : Blo 127788 244853 := bbase (se 5 (by rfl) ⟨11477, by rfl⟩ : syracuseStep 244853 = 22955) (by norm_num)
theorem B146569 : Blo 127788 146569 := bbase (se 2 (by rfl) ⟨54963, by rfl⟩ : syracuseStep 146569 = 109927) (by norm_num)
theorem B146605 : Blo 127788 146605 := bbase (se 3 (by rfl) ⟨27488, by rfl⟩ : syracuseStep 146605 = 54977) (by norm_num)
theorem B146641 : Blo 127788 146641 := bbase (se 2 (by rfl) ⟨54990, by rfl⟩ : syracuseStep 146641 = 109981) (by norm_num)
theorem B441557 : Blo 127788 441557 := bbase (se 7 (by rfl) ⟨5174, by rfl⟩ : syracuseStep 441557 = 10349) (by norm_num)
theorem B146677 : Blo 127788 146677 := bbase (se 5 (by rfl) ⟨6875, by rfl⟩ : syracuseStep 146677 = 13751) (by norm_num)
theorem B2243861 : Blo 127788 2243861 := bbase (se 6 (by rfl) ⟨52590, by rfl⟩ : syracuseStep 2243861 = 105181) (by norm_num)
theorem B146713 : Blo 127788 146713 := bbase (se 2 (by rfl) ⟨55017, by rfl⟩ : syracuseStep 146713 = 110035) (by norm_num)
theorem B146749 : Blo 127788 146749 := bbase (se 3 (by rfl) ⟨27515, by rfl⟩ : syracuseStep 146749 = 55031) (by norm_num)
theorem B146785 : Blo 127788 146785 := bbase (se 2 (by rfl) ⟨55044, by rfl⟩ : syracuseStep 146785 = 110089) (by norm_num)
theorem B146821 : Blo 127788 146821 := bbase (se 4 (by rfl) ⟨13764, by rfl⟩ : syracuseStep 146821 = 27529) (by norm_num)
theorem B179605 : Blo 127788 179605 := bbase (se 6 (by rfl) ⟨4209, by rfl⟩ : syracuseStep 179605 = 8419) (by norm_num)
theorem B146857 : Blo 127788 146857 := bbase (se 2 (by rfl) ⟨55071, by rfl⟩ : syracuseStep 146857 = 110143) (by norm_num)
theorem B146893 : Blo 127788 146893 := bbase (se 3 (by rfl) ⟨27542, by rfl⟩ : syracuseStep 146893 = 55085) (by norm_num)
theorem B146929 : Blo 127788 146929 := bbase (se 2 (by rfl) ⟨55098, by rfl⟩ : syracuseStep 146929 = 110197) (by norm_num)
theorem B146965 : Blo 127788 146965 := bbase (se 6 (by rfl) ⟨3444, by rfl⟩ : syracuseStep 146965 = 6889) (by norm_num)
theorem B147001 : Blo 127788 147001 := bbase (se 2 (by rfl) ⟨55125, by rfl⟩ : syracuseStep 147001 = 110251) (by norm_num)
theorem B147037 : Blo 127788 147037 := bbase (se 3 (by rfl) ⟨27569, by rfl⟩ : syracuseStep 147037 = 55139) (by norm_num)
theorem B147073 : Blo 127788 147073 := bbase (se 2 (by rfl) ⟨55152, by rfl⟩ : syracuseStep 147073 = 110305) (by norm_num)
theorem B441989 : Blo 127788 441989 := bbase (se 4 (by rfl) ⟨41436, by rfl⟩ : syracuseStep 441989 = 82873) (by norm_num)
theorem B147109 : Blo 127788 147109 := bbase (se 4 (by rfl) ⟨13791, by rfl⟩ : syracuseStep 147109 = 27583) (by norm_num)
theorem B147145 : Blo 127788 147145 := bbase (se 2 (by rfl) ⟨55179, by rfl⟩ : syracuseStep 147145 = 110359) (by norm_num)
theorem B278245 : Blo 127788 278245 := bbase (se 4 (by rfl) ⟨26085, by rfl⟩ : syracuseStep 278245 = 52171) (by norm_num)
theorem B147181 : Blo 127788 147181 := bbase (se 3 (by rfl) ⟨27596, by rfl⟩ : syracuseStep 147181 = 55193) (by norm_num)
theorem B147217 : Blo 127788 147217 := bbase (se 2 (by rfl) ⟨55206, by rfl⟩ : syracuseStep 147217 = 110413) (by norm_num)
theorem B147253 : Blo 127788 147253 := bbase (se 5 (by rfl) ⟨6902, by rfl⟩ : syracuseStep 147253 = 13805) (by norm_num)
theorem B147289 : Blo 127788 147289 := bbase (se 2 (by rfl) ⟨55233, by rfl⟩ : syracuseStep 147289 = 110467) (by norm_num)
theorem B245605 : Blo 127788 245605 := bbase (se 4 (by rfl) ⟨23025, by rfl⟩ : syracuseStep 245605 = 46051) (by norm_num)
theorem B147325 : Blo 127788 147325 := bbase (se 3 (by rfl) ⟨27623, by rfl⟩ : syracuseStep 147325 = 55247) (by norm_num)
theorem B147361 : Blo 127788 147361 := bbase (se 2 (by rfl) ⟨55260, by rfl⟩ : syracuseStep 147361 = 110521) (by norm_num)
theorem B147397 : Blo 127788 147397 := bbase (se 4 (by rfl) ⟨13818, by rfl⟩ : syracuseStep 147397 = 27637) (by norm_num)
theorem B147425 : Blo 127788 147425 := bbase (se 2 (by rfl) ⟨55284, by rfl⟩ : syracuseStep 147425 = 110569) (by norm_num)
theorem B147433 : Blo 127788 147433 := bbase (se 2 (by rfl) ⟨55287, by rfl⟩ : syracuseStep 147433 = 110575) (by norm_num)
theorem B245749 : Blo 127788 245749 := bbase (se 5 (by rfl) ⟨11519, by rfl⟩ : syracuseStep 245749 = 23039) (by norm_num)
theorem B147469 : Blo 127788 147469 := bbase (se 3 (by rfl) ⟨27650, by rfl⟩ : syracuseStep 147469 = 55301) (by norm_num)
theorem B147505 : Blo 127788 147505 := bbase (se 2 (by rfl) ⟨55314, by rfl⟩ : syracuseStep 147505 = 110629) (by norm_num)
theorem B442421 : Blo 127788 442421 := bbase (se 5 (by rfl) ⟨20738, by rfl⟩ : syracuseStep 442421 = 41477) (by norm_num)
theorem B147541 : Blo 127788 147541 := bbase (se 8 (by rfl) ⟨864, by rfl⟩ : syracuseStep 147541 = 1729) (by norm_num)
theorem B147577 : Blo 127788 147577 := bbase (se 2 (by rfl) ⟨55341, by rfl⟩ : syracuseStep 147577 = 110683) (by norm_num)
theorem B245909 : Blo 127788 245909 := bbase (se 6 (by rfl) ⟨5763, by rfl⟩ : syracuseStep 245909 = 11527) (by norm_num)
theorem B147613 : Blo 127788 147613 := bbase (se 3 (by rfl) ⟨27677, by rfl⟩ : syracuseStep 147613 = 55355) (by norm_num)
theorem B147649 : Blo 127788 147649 := bbase (se 2 (by rfl) ⟨55368, by rfl⟩ : syracuseStep 147649 = 110737) (by norm_num)
theorem B278741 : Blo 127788 278741 := bbase (se 7 (by rfl) ⟨3266, by rfl⟩ : syracuseStep 278741 = 6533) (by norm_num)
theorem B147685 : Blo 127788 147685 := bbase (se 4 (by rfl) ⟨13845, by rfl⟩ : syracuseStep 147685 = 27691) (by norm_num)
theorem B213229 : Blo 127788 213229 := bbase (se 3 (by rfl) ⟨39980, by rfl⟩ : syracuseStep 213229 = 79961) (by norm_num)
theorem B147721 : Blo 127788 147721 := bbase (se 2 (by rfl) ⟨55395, by rfl⟩ : syracuseStep 147721 = 110791) (by norm_num)
theorem B999701 : Blo 127788 999701 := bbase (se 6 (by rfl) ⟨23430, by rfl⟩ : syracuseStep 999701 = 46861) (by norm_num)
theorem B246053 : Blo 127788 246053 := bbase (se 4 (by rfl) ⟨23067, by rfl⟩ : syracuseStep 246053 = 46135) (by norm_num)
theorem B147757 : Blo 127788 147757 := bbase (se 3 (by rfl) ⟨27704, by rfl⟩ : syracuseStep 147757 = 55409) (by norm_num)
theorem B147793 : Blo 127788 147793 := bbase (se 2 (by rfl) ⟨55422, by rfl⟩ : syracuseStep 147793 = 110845) (by norm_num)
theorem B147829 : Blo 127788 147829 := bbase (se 5 (by rfl) ⟨6929, by rfl⟩ : syracuseStep 147829 = 13859) (by norm_num)
theorem B1589653 : Blo 127788 1589653 := bbase (se 6 (by rfl) ⟨37257, by rfl⟩ : syracuseStep 1589653 = 74515) (by norm_num)
theorem B147865 : Blo 127788 147865 := bbase (se 2 (by rfl) ⟨55449, by rfl⟩ : syracuseStep 147865 = 110899) (by norm_num)
theorem B147901 : Blo 127788 147901 := bbase (se 3 (by rfl) ⟨27731, by rfl⟩ : syracuseStep 147901 = 55463) (by norm_num)
theorem B147937 : Blo 127788 147937 := bbase (se 2 (by rfl) ⟨55476, by rfl⟩ : syracuseStep 147937 = 110953) (by norm_num)
theorem B442853 : Blo 127788 442853 := bbase (se 4 (by rfl) ⟨41517, by rfl⟩ : syracuseStep 442853 = 83035) (by norm_num)
theorem B147973 : Blo 127788 147973 := bbase (se 4 (by rfl) ⟨13872, by rfl⟩ : syracuseStep 147973 = 27745) (by norm_num)
theorem B311845 : Blo 127788 311845 := bbase (se 4 (by rfl) ⟨29235, by rfl⟩ : syracuseStep 311845 = 58471) (by norm_num)
theorem B148009 : Blo 127788 148009 := bbase (se 2 (by rfl) ⟨55503, by rfl⟩ : syracuseStep 148009 = 111007) (by norm_num)
theorem B246341 : Blo 127788 246341 := bbase (se 4 (by rfl) ⟨23094, by rfl⟩ : syracuseStep 246341 = 46189) (by norm_num)
theorem B148045 : Blo 127788 148045 := bbase (se 3 (by rfl) ⟨27758, by rfl⟩ : syracuseStep 148045 = 55517) (by norm_num)
theorem B148081 : Blo 127788 148081 := bbase (se 2 (by rfl) ⟨55530, by rfl⟩ : syracuseStep 148081 = 111061) (by norm_num)
theorem B737909 : Blo 127788 737909 := bbase (se 5 (by rfl) ⟨34589, by rfl⟩ : syracuseStep 737909 = 69179) (by norm_num)
theorem B148117 : Blo 127788 148117 := bbase (se 6 (by rfl) ⟨3471, by rfl⟩ : syracuseStep 148117 = 6943) (by norm_num)
theorem B148153 : Blo 127788 148153 := bbase (se 2 (by rfl) ⟨55557, by rfl⟩ : syracuseStep 148153 = 111115) (by norm_num)
theorem B246493 : Blo 127788 246493 := bbase (se 3 (by rfl) ⟨46217, by rfl⟩ : syracuseStep 246493 = 92435) (by norm_num)
theorem B148189 : Blo 127788 148189 := bbase (se 3 (by rfl) ⟨27785, by rfl⟩ : syracuseStep 148189 = 55571) (by norm_num)
theorem B148225 : Blo 127788 148225 := bbase (se 2 (by rfl) ⟨55584, by rfl⟩ : syracuseStep 148225 = 111169) (by norm_num)
theorem B148261 : Blo 127788 148261 := bbase (se 4 (by rfl) ⟨13899, by rfl⟩ : syracuseStep 148261 = 27799) (by norm_num)
theorem B443285 : Blo 127788 443285 := bbase (se 6 (by rfl) ⟨10389, by rfl⟩ : syracuseStep 443285 = 20779) (by norm_num)
theorem B148429 : Blo 127788 148429 := bbase (se 3 (by rfl) ⟨27830, by rfl⟩ : syracuseStep 148429 = 55661) (by norm_num)
theorem B246797 : Blo 127788 246797 := bbase (se 3 (by rfl) ⟨46274, by rfl⟩ : syracuseStep 246797 = 92549) (by norm_num)
theorem B148493 : Blo 127788 148493 := bbase (se 3 (by rfl) ⟨27842, by rfl⟩ : syracuseStep 148493 = 55685) (by norm_num)
theorem B279629 : Blo 127788 279629 := bbase (se 3 (by rfl) ⟨52430, by rfl⟩ : syracuseStep 279629 = 104861) (by norm_num)
theorem B312461 : Blo 127788 312461 := bbase (se 3 (by rfl) ⟨58586, by rfl⟩ : syracuseStep 312461 = 117173) (by norm_num)
theorem B279749 : Blo 127788 279749 := bbase (se 4 (by rfl) ⟨26226, by rfl⟩ : syracuseStep 279749 = 52453) (by norm_num)
theorem B1525013 : Blo 127788 1525013 := bbase (se 6 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 1525013 = 71485) (by norm_num)
theorem B443717 : Blo 127788 443717 := bbase (se 4 (by rfl) ⟨41598, by rfl⟩ : syracuseStep 443717 = 83197) (by norm_num)
theorem B148921 : Blo 127788 148921 := bbase (se 2 (by rfl) ⟨55845, by rfl⟩ : syracuseStep 148921 = 111691) (by norm_num)
theorem B1066517 : Blo 127788 1066517 := bbase (se 6 (by rfl) ⟨24996, by rfl⟩ : syracuseStep 1066517 = 49993) (by norm_num)
theorem B673429 : Blo 127788 673429 := bbase (se 6 (by rfl) ⟨15783, by rfl⟩ : syracuseStep 673429 = 31567) (by norm_num)
theorem B444149 : Blo 127788 444149 := bbase (se 5 (by rfl) ⟨20819, by rfl⟩ : syracuseStep 444149 = 41639) (by norm_num)
theorem B247549 : Blo 127788 247549 := bbase (se 3 (by rfl) ⟨46415, by rfl⟩ : syracuseStep 247549 = 92831) (by norm_num)
theorem B182045 : Blo 127788 182045 := bbase (se 3 (by rfl) ⟨34133, by rfl⟩ : syracuseStep 182045 = 68267) (by norm_num)
theorem B280381 : Blo 127788 280381 := bbase (se 3 (by rfl) ⟨52571, by rfl⟩ : syracuseStep 280381 = 105143) (by norm_num)
theorem B280397 : Blo 127788 280397 := bbase (se 3 (by rfl) ⟨52574, by rfl⟩ : syracuseStep 280397 = 105149) (by norm_num)
theorem B182125 : Blo 127788 182125 := bbase (se 3 (by rfl) ⟨34148, by rfl⟩ : syracuseStep 182125 = 68297) (by norm_num)
theorem B247693 : Blo 127788 247693 := bbase (se 3 (by rfl) ⟨46442, by rfl⟩ : syracuseStep 247693 = 92885) (by norm_num)
theorem B313237 : Blo 127788 313237 := bbase (se 6 (by rfl) ⟨7341, by rfl⟩ : syracuseStep 313237 = 14683) (by norm_num)
theorem B182245 : Blo 127788 182245 := bbase (se 4 (by rfl) ⟨17085, by rfl⟩ : syracuseStep 182245 = 34171) (by norm_num)
theorem B247853 : Blo 127788 247853 := bbase (se 3 (by rfl) ⟨46472, by rfl⟩ : syracuseStep 247853 = 92945) (by norm_num)
theorem B182341 : Blo 127788 182341 := bbase (se 4 (by rfl) ⟨17094, by rfl⟩ : syracuseStep 182341 = 34189) (by norm_num)
theorem B1099925 : Blo 127788 1099925 := bbase (se 6 (by rfl) ⟨25779, by rfl⟩ : syracuseStep 1099925 = 51559) (by norm_num)
theorem B444581 : Blo 127788 444581 := bbase (se 4 (by rfl) ⟨41679, by rfl⟩ : syracuseStep 444581 = 83359) (by norm_num)
theorem B247997 : Blo 127788 247997 := bbase (se 3 (by rfl) ⟨46499, by rfl⟩ : syracuseStep 247997 = 92999) (by norm_num)
theorem B313685 : Blo 127788 313685 := bbase (se 10 (by rfl) ⟨459, by rfl⟩ : syracuseStep 313685 = 919) (by norm_num)
theorem B412037 : Blo 127788 412037 := bbase (se 4 (by rfl) ⟨38628, by rfl⟩ : syracuseStep 412037 = 77257) (by norm_num)
theorem B248285 : Blo 127788 248285 := bbase (se 3 (by rfl) ⟨46553, by rfl⟩ : syracuseStep 248285 = 93107) (by norm_num)
theorem B182837 : Blo 127788 182837 := bbase (se 5 (by rfl) ⟨8570, by rfl⟩ : syracuseStep 182837 = 17141) (by norm_num)
theorem B313949 : Blo 127788 313949 := bbase (se 3 (by rfl) ⟨58865, by rfl⟩ : syracuseStep 313949 = 117731) (by norm_num)
theorem B215669 : Blo 127788 215669 := bbase (se 5 (by rfl) ⟨10109, by rfl⟩ : syracuseStep 215669 = 20219) (by norm_num)
theorem B248437 : Blo 127788 248437 := bbase (se 5 (by rfl) ⟨11645, by rfl⟩ : syracuseStep 248437 = 23291) (by norm_num)
theorem B281269 : Blo 127788 281269 := bbase (se 5 (by rfl) ⟨13184, by rfl⟩ : syracuseStep 281269 = 26369) (by norm_num)
theorem B215797 : Blo 127788 215797 := bbase (se 5 (by rfl) ⟨10115, by rfl⟩ : syracuseStep 215797 = 20231) (by norm_num)
theorem B740117 : Blo 127788 740117 := bbase (se 6 (by rfl) ⟨17346, by rfl⟩ : syracuseStep 740117 = 34693) (by norm_num)
theorem B281389 : Blo 127788 281389 := bbase (se 3 (by rfl) ⟨52760, by rfl⟩ : syracuseStep 281389 = 105521) (by norm_num)
theorem B215885 : Blo 127788 215885 := bbase (se 3 (by rfl) ⟨40478, by rfl⟩ : syracuseStep 215885 = 80957) (by norm_num)
theorem B248741 : Blo 127788 248741 := bbase (se 4 (by rfl) ⟨23319, by rfl⟩ : syracuseStep 248741 = 46639) (by norm_num)
theorem B216013 : Blo 127788 216013 := bbase (se 3 (by rfl) ⟨40502, by rfl⟩ : syracuseStep 216013 = 81005) (by norm_num)
theorem B216101 : Blo 127788 216101 := bbase (se 4 (by rfl) ⟨20259, by rfl⟩ : syracuseStep 216101 = 40519) (by norm_num)
theorem B2477141 : Blo 127788 2477141 := bbase (se 8 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 2477141 = 29029) (by norm_num)
theorem B183389 : Blo 127788 183389 := bbase (se 3 (by rfl) ⟨34385, by rfl⟩ : syracuseStep 183389 = 68771) (by norm_num)
theorem B216229 : Blo 127788 216229 := bbase (se 4 (by rfl) ⟨20271, by rfl⟩ : syracuseStep 216229 = 40543) (by norm_num)
theorem B216317 : Blo 127788 216317 := bbase (se 3 (by rfl) ⟨40559, by rfl⟩ : syracuseStep 216317 = 81119) (by norm_num)
theorem B314621 : Blo 127788 314621 := bbase (se 3 (by rfl) ⟨58991, by rfl⟩ : syracuseStep 314621 = 117983) (by norm_num)
theorem B412933 : Blo 127788 412933 := bbase (se 4 (by rfl) ⟨38712, by rfl⟩ : syracuseStep 412933 = 77425) (by norm_num)
theorem B216445 : Blo 127788 216445 := bbase (se 3 (by rfl) ⟨40583, by rfl⟩ : syracuseStep 216445 = 81167) (by norm_num)
theorem B216533 : Blo 127788 216533 := bbase (se 7 (by rfl) ⟨2537, by rfl⟩ : syracuseStep 216533 = 5075) (by norm_num)
theorem B216661 : Blo 127788 216661 := bbase (se 8 (by rfl) ⟨1269, by rfl⟩ : syracuseStep 216661 = 2539) (by norm_num)
theorem B413333 : Blo 127788 413333 := bbase (se 6 (by rfl) ⟨9687, by rfl⟩ : syracuseStep 413333 = 19375) (by norm_num)
theorem B249493 : Blo 127788 249493 := bbase (se 6 (by rfl) ⟨5847, by rfl⟩ : syracuseStep 249493 = 11695) (by norm_num)
theorem B216749 : Blo 127788 216749 := bbase (se 3 (by rfl) ⟨40640, by rfl⟩ : syracuseStep 216749 = 81281) (by norm_num)
theorem B249637 : Blo 127788 249637 := bbase (se 4 (by rfl) ⟨23403, by rfl⟩ : syracuseStep 249637 = 46807) (by norm_num)
theorem B216877 : Blo 127788 216877 := bbase (se 3 (by rfl) ⟨40664, by rfl⟩ : syracuseStep 216877 = 81329) (by norm_num)
theorem B184141 : Blo 127788 184141 := bbase (se 3 (by rfl) ⟨34526, by rfl⟩ : syracuseStep 184141 = 69053) (by norm_num)
theorem B2117461 : Blo 127788 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B216965 : Blo 127788 216965 := bbase (se 4 (by rfl) ⟨20340, by rfl⟩ : syracuseStep 216965 = 40681) (by norm_num)
theorem B249797 : Blo 127788 249797 := bbase (se 4 (by rfl) ⟨23418, by rfl⟩ : syracuseStep 249797 = 46837) (by norm_num)
theorem B217093 : Blo 127788 217093 := bbase (se 4 (by rfl) ⟨20352, by rfl⟩ : syracuseStep 217093 = 40705) (by norm_num)
theorem B249941 : Blo 127788 249941 := bbase (se 8 (by rfl) ⟨1464, by rfl⟩ : syracuseStep 249941 = 2929) (by norm_num)
theorem B217181 : Blo 127788 217181 := bbase (se 3 (by rfl) ⟨40721, by rfl⟩ : syracuseStep 217181 = 81443) (by norm_num)
theorem B315589 : Blo 127788 315589 := bbase (se 4 (by rfl) ⟨29586, by rfl⟩ : syracuseStep 315589 = 59173) (by norm_num)
theorem B217309 : Blo 127788 217309 := bbase (se 3 (by rfl) ⟨40745, by rfl⟩ : syracuseStep 217309 = 81491) (by norm_num)
theorem B217397 : Blo 127788 217397 := bbase (se 5 (by rfl) ⟨10190, by rfl⟩ : syracuseStep 217397 = 20381) (by norm_num)
theorem B250229 : Blo 127788 250229 := bbase (se 5 (by rfl) ⟨11729, by rfl⟩ : syracuseStep 250229 = 23459) (by norm_num)
theorem B217525 : Blo 127788 217525 := bbase (se 5 (by rfl) ⟨10196, by rfl⟩ : syracuseStep 217525 = 20393) (by norm_num)
theorem B217613 : Blo 127788 217613 := bbase (se 3 (by rfl) ⟨40802, by rfl⟩ : syracuseStep 217613 = 81605) (by norm_num)
theorem B184933 : Blo 127788 184933 := bbase (se 4 (by rfl) ⟨17337, by rfl⟩ : syracuseStep 184933 = 34675) (by norm_num)
theorem B217741 : Blo 127788 217741 := bbase (se 3 (by rfl) ⟨40826, by rfl⟩ : syracuseStep 217741 = 81653) (by norm_num)
theorem B217829 : Blo 127788 217829 := bbase (se 4 (by rfl) ⟨20421, by rfl⟩ : syracuseStep 217829 = 40843) (by norm_num)
theorem B217957 : Blo 127788 217957 := bbase (se 4 (by rfl) ⟨20433, by rfl⟩ : syracuseStep 217957 = 40867) (by norm_num)
theorem B185269 : Blo 127788 185269 := bbase (se 5 (by rfl) ⟨8684, by rfl⟩ : syracuseStep 185269 = 17369) (by norm_num)
theorem B250805 : Blo 127788 250805 := bbase (se 5 (by rfl) ⟨11756, by rfl⟩ : syracuseStep 250805 = 23513) (by norm_num)
theorem B218045 : Blo 127788 218045 := bbase (se 3 (by rfl) ⟨40883, by rfl⟩ : syracuseStep 218045 = 81767) (by norm_num)
theorem B316381 : Blo 127788 316381 := bbase (se 3 (by rfl) ⟨59321, by rfl⟩ : syracuseStep 316381 = 118643) (by norm_num)
theorem B218173 : Blo 127788 218173 := bbase (se 3 (by rfl) ⟨40907, by rfl⟩ : syracuseStep 218173 = 81815) (by norm_num)
theorem B250997 : Blo 127788 250997 := bbase (se 5 (by rfl) ⟨11765, by rfl⟩ : syracuseStep 250997 = 23531) (by norm_num)
theorem B185485 : Blo 127788 185485 := bbase (se 3 (by rfl) ⟨34778, by rfl⟩ : syracuseStep 185485 = 69557) (by norm_num)
theorem B218261 : Blo 127788 218261 := bbase (se 6 (by rfl) ⟨5115, by rfl⟩ : syracuseStep 218261 = 10231) (by norm_num)
theorem B218389 : Blo 127788 218389 := bbase (se 6 (by rfl) ⟨5118, by rfl⟩ : syracuseStep 218389 = 10237) (by norm_num)
theorem B218477 : Blo 127788 218477 := bbase (se 3 (by rfl) ⟨40964, by rfl⟩ : syracuseStep 218477 = 81929) (by norm_num)
theorem B1037717 : Blo 127788 1037717 := bbase (se 6 (by rfl) ⟨24321, by rfl⟩ : syracuseStep 1037717 = 48643) (by norm_num)
theorem B218605 : Blo 127788 218605 := bbase (se 3 (by rfl) ⟨40988, by rfl⟩ : syracuseStep 218605 = 81977) (by norm_num)
theorem B185861 : Blo 127788 185861 := bbase (se 4 (by rfl) ⟨17424, by rfl⟩ : syracuseStep 185861 = 34849) (by norm_num)
theorem B349733 : Blo 127788 349733 := bbase (se 4 (by rfl) ⟨32787, by rfl⟩ : syracuseStep 349733 = 65575) (by norm_num)
theorem B218693 : Blo 127788 218693 := bbase (se 4 (by rfl) ⟨20502, by rfl⟩ : syracuseStep 218693 = 41005) (by norm_num)
theorem B218821 : Blo 127788 218821 := bbase (se 4 (by rfl) ⟨20514, by rfl⟩ : syracuseStep 218821 = 41029) (by norm_num)
theorem B218909 : Blo 127788 218909 := bbase (se 3 (by rfl) ⟨41045, by rfl⟩ : syracuseStep 218909 = 82091) (by norm_num)
theorem B219037 : Blo 127788 219037 := bbase (se 3 (by rfl) ⟨41069, by rfl⟩ : syracuseStep 219037 = 82139) (by norm_num)
theorem B186349 : Blo 127788 186349 := bbase (se 3 (by rfl) ⟨34940, by rfl⟩ : syracuseStep 186349 = 69881) (by norm_num)
theorem B219125 : Blo 127788 219125 := bbase (se 5 (by rfl) ⟨10271, by rfl⟩ : syracuseStep 219125 = 20543) (by norm_num)
theorem B219253 : Blo 127788 219253 := bbase (se 5 (by rfl) ⟨10277, by rfl⟩ : syracuseStep 219253 = 20555) (by norm_num)
theorem B219277 : Blo 127788 219277 := bbase (se 3 (by rfl) ⟨41114, by rfl⟩ : syracuseStep 219277 = 82229) (by norm_num)
theorem B219341 : Blo 127788 219341 := bbase (se 3 (by rfl) ⟨41126, by rfl⟩ : syracuseStep 219341 = 82253) (by norm_num)
theorem B1497365 : Blo 127788 1497365 := bbase (se 6 (by rfl) ⟨35094, by rfl⟩ : syracuseStep 1497365 = 70189) (by norm_num)
theorem B219469 : Blo 127788 219469 := bbase (se 3 (by rfl) ⟨41150, by rfl⟩ : syracuseStep 219469 = 82301) (by norm_num)
theorem B219557 : Blo 127788 219557 := bbase (se 4 (by rfl) ⟨20583, by rfl⟩ : syracuseStep 219557 = 41167) (by norm_num)
theorem B154081 : Blo 127788 154081 := bbase (se 2 (by rfl) ⟨57780, by rfl⟩ : syracuseStep 154081 = 115561) (by norm_num)
theorem B219685 : Blo 127788 219685 := bbase (se 4 (by rfl) ⟨20595, by rfl⟩ : syracuseStep 219685 = 41191) (by norm_num)
theorem B1235573 : Blo 127788 1235573 := bbase (se 5 (by rfl) ⟨57917, by rfl⟩ : syracuseStep 1235573 = 115835) (by norm_num)
theorem B219773 : Blo 127788 219773 := bbase (se 3 (by rfl) ⟨41207, by rfl⟩ : syracuseStep 219773 = 82415) (by norm_num)
theorem B219901 : Blo 127788 219901 := bbase (se 3 (by rfl) ⟨41231, by rfl⟩ : syracuseStep 219901 = 82463) (by norm_num)
theorem B219989 : Blo 127788 219989 := bbase (se 9 (by rfl) ⟨644, by rfl⟩ : syracuseStep 219989 = 1289) (by norm_num)
theorem B187285 : Blo 127788 187285 := bbase (se 6 (by rfl) ⟨4389, by rfl⟩ : syracuseStep 187285 = 8779) (by norm_num)
theorem B220117 : Blo 127788 220117 := bbase (se 7 (by rfl) ⟨2579, by rfl⟩ : syracuseStep 220117 = 5159) (by norm_num)
theorem B547829 : Blo 127788 547829 := bbase (se 5 (by rfl) ⟨25679, by rfl⟩ : syracuseStep 547829 = 51359) (by norm_num)
theorem B220205 : Blo 127788 220205 := bbase (se 3 (by rfl) ⟨41288, by rfl⟩ : syracuseStep 220205 = 82577) (by norm_num)
theorem B220333 : Blo 127788 220333 := bbase (se 3 (by rfl) ⟨41312, by rfl⟩ : syracuseStep 220333 = 82625) (by norm_num)
theorem B220421 : Blo 127788 220421 := bbase (se 4 (by rfl) ⟨20664, by rfl⟩ : syracuseStep 220421 = 41329) (by norm_num)
theorem B548117 : Blo 127788 548117 := bbase (se 6 (by rfl) ⟨12846, by rfl⟩ : syracuseStep 548117 = 25693) (by norm_num)
theorem B417125 : Blo 127788 417125 := bbase (se 4 (by rfl) ⟨39105, by rfl⟩ : syracuseStep 417125 = 78211) (by norm_num)
theorem B220549 : Blo 127788 220549 := bbase (se 4 (by rfl) ⟨20676, by rfl⟩ : syracuseStep 220549 = 41353) (by norm_num)
theorem B155081 : Blo 127788 155081 := bbase (se 2 (by rfl) ⟨58155, by rfl⟩ : syracuseStep 155081 = 116311) (by norm_num)
theorem B220637 : Blo 127788 220637 := bbase (se 3 (by rfl) ⟨41369, by rfl⟩ : syracuseStep 220637 = 82739) (by norm_num)
theorem B155129 : Blo 127788 155129 := bbase (se 2 (by rfl) ⟨58173, by rfl⟩ : syracuseStep 155129 = 116347) (by norm_num)
theorem B220765 : Blo 127788 220765 := bbase (se 3 (by rfl) ⟨41393, by rfl⟩ : syracuseStep 220765 = 82787) (by norm_num)
theorem B220853 : Blo 127788 220853 := bbase (se 5 (by rfl) ⟨10352, by rfl⟩ : syracuseStep 220853 = 20705) (by norm_num)
theorem B220981 : Blo 127788 220981 := bbase (se 5 (by rfl) ⟨10358, by rfl⟩ : syracuseStep 220981 = 20717) (by norm_num)
theorem B614213 : Blo 127788 614213 := bbase (se 4 (by rfl) ⟨57582, by rfl⟩ : syracuseStep 614213 = 115165) (by norm_num)
theorem B221069 : Blo 127788 221069 := bbase (se 3 (by rfl) ⟨41450, by rfl⟩ : syracuseStep 221069 = 82901) (by norm_num)
theorem B319405 : Blo 127788 319405 := bbase (se 3 (by rfl) ⟨59888, by rfl⟩ : syracuseStep 319405 = 119777) (by norm_num)
theorem B548869 : Blo 127788 548869 := bbase (se 4 (by rfl) ⟨51456, by rfl⟩ : syracuseStep 548869 = 102913) (by norm_num)
theorem B221197 : Blo 127788 221197 := bbase (se 3 (by rfl) ⟨41474, by rfl⟩ : syracuseStep 221197 = 82949) (by norm_num)
theorem B647189 : Blo 127788 647189 := bbase (se 6 (by rfl) ⟨15168, by rfl⟩ : syracuseStep 647189 = 30337) (by norm_num)
theorem B155677 : Blo 127788 155677 := bbase (se 3 (by rfl) ⟨29189, by rfl⟩ : syracuseStep 155677 = 58379) (by norm_num)
theorem B221285 : Blo 127788 221285 := bbase (se 4 (by rfl) ⟨20745, by rfl⟩ : syracuseStep 221285 = 41491) (by norm_num)
theorem B254173 : Blo 127788 254173 := bbase (se 3 (by rfl) ⟨47657, by rfl⟩ : syracuseStep 254173 = 95315) (by norm_num)
theorem B221413 : Blo 127788 221413 := bbase (se 4 (by rfl) ⟨20757, by rfl⟩ : syracuseStep 221413 = 41515) (by norm_num)
theorem B221501 : Blo 127788 221501 := bbase (se 3 (by rfl) ⟨41531, by rfl⟩ : syracuseStep 221501 = 83063) (by norm_num)
theorem B680293 : Blo 127788 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B418213 : Blo 127788 418213 := bbase (se 4 (by rfl) ⟨39207, by rfl⟩ : syracuseStep 418213 = 78415) (by norm_num)
theorem B221629 : Blo 127788 221629 := bbase (se 3 (by rfl) ⟨41555, by rfl⟩ : syracuseStep 221629 = 83111) (by norm_num)
theorem B156157 : Blo 127788 156157 := bbase (se 3 (by rfl) ⟨29279, by rfl⟩ : syracuseStep 156157 = 58559) (by norm_num)
theorem B221717 : Blo 127788 221717 := bbase (se 6 (by rfl) ⟨5196, by rfl⟩ : syracuseStep 221717 = 10393) (by norm_num)
theorem B221845 : Blo 127788 221845 := bbase (se 6 (by rfl) ⟨5199, by rfl⟩ : syracuseStep 221845 = 10399) (by norm_num)
theorem B549605 : Blo 127788 549605 := bbase (se 4 (by rfl) ⟨51525, by rfl⟩ : syracuseStep 549605 = 103051) (by norm_num)
theorem B221933 : Blo 127788 221933 := bbase (se 3 (by rfl) ⟨41612, by rfl⟩ : syracuseStep 221933 = 83225) (by norm_num)
theorem B287549 : Blo 127788 287549 := bbase (se 3 (by rfl) ⟨53915, by rfl⟩ : syracuseStep 287549 = 107831) (by norm_num)
theorem B222061 : Blo 127788 222061 := bbase (se 3 (by rfl) ⟨41636, by rfl⟩ : syracuseStep 222061 = 83273) (by norm_num)
theorem B287621 : Blo 127788 287621 := bbase (se 4 (by rfl) ⟨26964, by rfl⟩ : syracuseStep 287621 = 53929) (by norm_num)
theorem B222149 : Blo 127788 222149 := bbase (se 4 (by rfl) ⟨20826, by rfl⟩ : syracuseStep 222149 = 41653) (by norm_num)
theorem B287693 : Blo 127788 287693 := bbase (se 3 (by rfl) ⟨53942, by rfl⟩ : syracuseStep 287693 = 107885) (by norm_num)
theorem B287765 : Blo 127788 287765 := bbase (se 6 (by rfl) ⟨6744, by rfl⟩ : syracuseStep 287765 = 13489) (by norm_num)
theorem B222277 : Blo 127788 222277 := bbase (se 4 (by rfl) ⟨20838, by rfl⟩ : syracuseStep 222277 = 41677) (by norm_num)
theorem B287837 : Blo 127788 287837 := bbase (se 3 (by rfl) ⟨53969, by rfl⟩ : syracuseStep 287837 = 107939) (by norm_num)
theorem B222365 : Blo 127788 222365 := bbase (se 3 (by rfl) ⟨41693, by rfl⟩ : syracuseStep 222365 = 83387) (by norm_num)
theorem B287909 : Blo 127788 287909 := bbase (se 4 (by rfl) ⟨26991, by rfl⟩ : syracuseStep 287909 = 53983) (by norm_num)
theorem B287981 : Blo 127788 287981 := bbase (se 3 (by rfl) ⟨53996, by rfl⟩ : syracuseStep 287981 = 107993) (by norm_num)
theorem B648485 : Blo 127788 648485 := bbase (se 4 (by rfl) ⟨60795, by rfl⟩ : syracuseStep 648485 = 121591) (by norm_num)
theorem B288053 : Blo 127788 288053 := bbase (se 5 (by rfl) ⟨13502, by rfl⟩ : syracuseStep 288053 = 27005) (by norm_num)
theorem B877877 : Blo 127788 877877 := bbase (se 5 (by rfl) ⟨41150, by rfl⟩ : syracuseStep 877877 = 82301) (by norm_num)
theorem B157037 : Blo 127788 157037 := bbase (se 3 (by rfl) ⟨29444, by rfl⟩ : syracuseStep 157037 = 58889) (by norm_num)
theorem B288125 : Blo 127788 288125 := bbase (se 3 (by rfl) ⟨54023, by rfl⟩ : syracuseStep 288125 = 108047) (by norm_num)
theorem B222629 : Blo 127788 222629 := bbase (se 4 (by rfl) ⟨20871, by rfl⟩ : syracuseStep 222629 = 41743) (by norm_num)
theorem B288197 : Blo 127788 288197 := bbase (se 4 (by rfl) ⟨27018, by rfl⟩ : syracuseStep 288197 = 54037) (by norm_num)
theorem B157153 : Blo 127788 157153 := bbase (se 2 (by rfl) ⟨58932, by rfl⟩ : syracuseStep 157153 = 117865) (by norm_num)
theorem B976373 : Blo 127788 976373 := bbase (se 5 (by rfl) ⟨45767, by rfl⟩ : syracuseStep 976373 = 91535) (by norm_num)
theorem B222725 : Blo 127788 222725 := bbase (se 4 (by rfl) ⟨20880, by rfl⟩ : syracuseStep 222725 = 41761) (by norm_num)
theorem B288269 : Blo 127788 288269 := bbase (se 3 (by rfl) ⟨54050, by rfl⟩ : syracuseStep 288269 = 108101) (by norm_num)
theorem B419381 : Blo 127788 419381 := bbase (se 5 (by rfl) ⟨19658, by rfl⟩ : syracuseStep 419381 = 39317) (by norm_num)
theorem B288341 : Blo 127788 288341 := bbase (se 8 (by rfl) ⟨1689, by rfl⟩ : syracuseStep 288341 = 3379) (by norm_num)
theorem B288413 : Blo 127788 288413 := bbase (se 3 (by rfl) ⟨54077, by rfl⟩ : syracuseStep 288413 = 108155) (by norm_num)
theorem B157349 : Blo 127788 157349 := bbase (se 4 (by rfl) ⟨14751, by rfl⟩ : syracuseStep 157349 = 29503) (by norm_num)
theorem B288485 : Blo 127788 288485 := bbase (se 4 (by rfl) ⟨27045, by rfl⟩ : syracuseStep 288485 = 54091) (by norm_num)
theorem B288557 : Blo 127788 288557 := bbase (se 3 (by rfl) ⟨54104, by rfl⟩ : syracuseStep 288557 = 108209) (by norm_num)
theorem B288629 : Blo 127788 288629 := bbase (se 5 (by rfl) ⟨13529, by rfl⟩ : syracuseStep 288629 = 27059) (by norm_num)
theorem B419717 : Blo 127788 419717 := bbase (se 4 (by rfl) ⟨39348, by rfl⟩ : syracuseStep 419717 = 78697) (by norm_num)
theorem B288701 : Blo 127788 288701 := bbase (se 3 (by rfl) ⟨54131, by rfl⟩ : syracuseStep 288701 = 108263) (by norm_num)
theorem B288773 : Blo 127788 288773 := bbase (se 4 (by rfl) ⟨27072, by rfl⟩ : syracuseStep 288773 = 54145) (by norm_num)
theorem B1107989 : Blo 127788 1107989 := bbase (se 6 (by rfl) ⟨25968, by rfl⟩ : syracuseStep 1107989 = 51937) (by norm_num)
theorem B288845 : Blo 127788 288845 := bbase (se 3 (by rfl) ⟨54158, by rfl⟩ : syracuseStep 288845 = 108317) (by norm_num)
theorem B288917 : Blo 127788 288917 := bbase (se 6 (by rfl) ⟨6771, by rfl⟩ : syracuseStep 288917 = 13543) (by norm_num)
theorem B354469 : Blo 127788 354469 := bbase (se 4 (by rfl) ⟨33231, by rfl⟩ : syracuseStep 354469 = 66463) (by norm_num)
theorem B157897 : Blo 127788 157897 := bbase (se 2 (by rfl) ⟨59211, by rfl⟩ : syracuseStep 157897 = 118423) (by norm_num)
theorem B3565781 : Blo 127788 3565781 := bbase (se 7 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 3565781 = 83573) (by norm_num)
theorem B288989 : Blo 127788 288989 := bbase (se 3 (by rfl) ⟨54185, by rfl⟩ : syracuseStep 288989 = 108371) (by norm_num)
theorem B485621 : Blo 127788 485621 := bbase (se 5 (by rfl) ⟨22763, by rfl⟩ : syracuseStep 485621 = 45527) (by norm_num)
theorem B289061 : Blo 127788 289061 := bbase (se 4 (by rfl) ⟨27099, by rfl⟩ : syracuseStep 289061 = 54199) (by norm_num)
theorem B158041 : Blo 127788 158041 := bbase (se 2 (by rfl) ⟨59265, by rfl⟩ : syracuseStep 158041 = 118531) (by norm_num)
theorem B289133 : Blo 127788 289133 := bbase (se 3 (by rfl) ⟨54212, by rfl⟩ : syracuseStep 289133 = 108425) (by norm_num)
theorem B158089 : Blo 127788 158089 := bbase (se 2 (by rfl) ⟨59283, by rfl⟩ : syracuseStep 158089 = 118567) (by norm_num)
theorem B289205 : Blo 127788 289205 := bbase (se 5 (by rfl) ⟨13556, by rfl⟩ : syracuseStep 289205 = 27113) (by norm_num)
theorem B289277 : Blo 127788 289277 := bbase (se 3 (by rfl) ⟨54239, by rfl⟩ : syracuseStep 289277 = 108479) (by norm_num)
theorem B485909 : Blo 127788 485909 := bbase (se 6 (by rfl) ⟨11388, by rfl⟩ : syracuseStep 485909 = 22777) (by norm_num)
theorem B649781 : Blo 127788 649781 := bbase (se 5 (by rfl) ⟨30458, by rfl⟩ : syracuseStep 649781 = 60917) (by norm_num)
theorem B289349 : Blo 127788 289349 := bbase (se 4 (by rfl) ⟨27126, by rfl⟩ : syracuseStep 289349 = 54253) (by norm_num)
theorem B289421 : Blo 127788 289421 := bbase (se 3 (by rfl) ⟨54266, by rfl⟩ : syracuseStep 289421 = 108533) (by norm_num)
theorem B289493 : Blo 127788 289493 := bbase (se 7 (by rfl) ⟨3392, by rfl⟩ : syracuseStep 289493 = 6785) (by norm_num)
theorem B289565 : Blo 127788 289565 := bbase (se 3 (by rfl) ⟨54293, by rfl⟩ : syracuseStep 289565 = 108587) (by norm_num)
theorem B289637 : Blo 127788 289637 := bbase (se 4 (by rfl) ⟨27153, by rfl⟩ : syracuseStep 289637 = 54307) (by norm_num)
theorem B289709 : Blo 127788 289709 := bbase (se 3 (by rfl) ⟨54320, by rfl⟩ : syracuseStep 289709 = 108641) (by norm_num)
theorem B256981 : Blo 127788 256981 := bbase (se 7 (by rfl) ⟨3011, by rfl⟩ : syracuseStep 256981 = 6023) (by norm_num)
theorem B289781 : Blo 127788 289781 := bbase (se 5 (by rfl) ⟨13583, by rfl⟩ : syracuseStep 289781 = 27167) (by norm_num)
theorem B289853 : Blo 127788 289853 := bbase (se 3 (by rfl) ⟨54347, by rfl⟩ : syracuseStep 289853 = 108695) (by norm_num)
theorem B289925 : Blo 127788 289925 := bbase (se 4 (by rfl) ⟨27180, by rfl⟩ : syracuseStep 289925 = 54361) (by norm_num)
theorem B421013 : Blo 127788 421013 := bbase (se 6 (by rfl) ⟨9867, by rfl⟩ : syracuseStep 421013 = 19735) (by norm_num)
theorem B191693 : Blo 127788 191693 := bbase (se 3 (by rfl) ⟨35942, by rfl⟩ : syracuseStep 191693 = 71885) (by norm_num)
theorem B289997 : Blo 127788 289997 := bbase (se 3 (by rfl) ⟨54374, by rfl⟩ : syracuseStep 289997 = 108749) (by norm_num)
theorem B191717 : Blo 127788 191717 := bbase (se 4 (by rfl) ⟨17973, by rfl⟩ : syracuseStep 191717 = 35947) (by norm_num)
theorem B191741 : Blo 127788 191741 := bbase (se 3 (by rfl) ⟨35951, by rfl⟩ : syracuseStep 191741 = 71903) (by norm_num)
theorem B191765 : Blo 127788 191765 := bbase (se 6 (by rfl) ⟨4494, by rfl⟩ : syracuseStep 191765 = 8989) (by norm_num)
theorem B290069 : Blo 127788 290069 := bbase (se 6 (by rfl) ⟨6798, by rfl⟩ : syracuseStep 290069 = 13597) (by norm_num)
theorem B191789 : Blo 127788 191789 := bbase (se 3 (by rfl) ⟨35960, by rfl⟩ : syracuseStep 191789 = 71921) (by norm_num)
theorem B191813 : Blo 127788 191813 := bbase (se 4 (by rfl) ⟨17982, by rfl⟩ : syracuseStep 191813 = 35965) (by norm_num)
theorem B191837 : Blo 127788 191837 := bbase (se 3 (by rfl) ⟨35969, by rfl⟩ : syracuseStep 191837 = 71939) (by norm_num)
theorem B290141 : Blo 127788 290141 := bbase (se 3 (by rfl) ⟨54401, by rfl⟩ : syracuseStep 290141 = 108803) (by norm_num)
theorem B191861 : Blo 127788 191861 := bbase (se 5 (by rfl) ⟨8993, by rfl⟩ : syracuseStep 191861 = 17987) (by norm_num)
theorem B421237 : Blo 127788 421237 := bbase (se 5 (by rfl) ⟨19745, by rfl⟩ : syracuseStep 421237 = 39491) (by norm_num)
theorem B191885 : Blo 127788 191885 := bbase (se 3 (by rfl) ⟨35978, by rfl⟩ : syracuseStep 191885 = 71957) (by norm_num)
theorem B191909 : Blo 127788 191909 := bbase (se 4 (by rfl) ⟨17991, by rfl⟩ : syracuseStep 191909 = 35983) (by norm_num)
theorem B290213 : Blo 127788 290213 := bbase (se 4 (by rfl) ⟨27207, by rfl⟩ : syracuseStep 290213 = 54415) (by norm_num)
theorem B191933 : Blo 127788 191933 := bbase (se 3 (by rfl) ⟨35987, by rfl⟩ : syracuseStep 191933 = 71975) (by norm_num)
theorem B585157 : Blo 127788 585157 := bbase (se 4 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 585157 = 109717) (by norm_num)
theorem B323021 : Blo 127788 323021 := bbase (se 3 (by rfl) ⟨60566, by rfl⟩ : syracuseStep 323021 = 121133) (by norm_num)
theorem B191957 : Blo 127788 191957 := bbase (se 7 (by rfl) ⟨2249, by rfl⟩ : syracuseStep 191957 = 4499) (by norm_num)
theorem B191981 : Blo 127788 191981 := bbase (se 3 (by rfl) ⟨35996, by rfl⟩ : syracuseStep 191981 = 71993) (by norm_num)
theorem B290285 : Blo 127788 290285 := bbase (se 3 (by rfl) ⟨54428, by rfl⟩ : syracuseStep 290285 = 108857) (by norm_num)
theorem B224765 : Blo 127788 224765 := bbase (se 3 (by rfl) ⟨42143, by rfl⟩ : syracuseStep 224765 = 84287) (by norm_num)
theorem B192005 : Blo 127788 192005 := bbase (se 4 (by rfl) ⟨18000, by rfl⟩ : syracuseStep 192005 = 36001) (by norm_num)
theorem B192029 : Blo 127788 192029 := bbase (se 3 (by rfl) ⟨36005, by rfl⟩ : syracuseStep 192029 = 72011) (by norm_num)
theorem B192053 : Blo 127788 192053 := bbase (se 5 (by rfl) ⟨9002, by rfl⟩ : syracuseStep 192053 = 18005) (by norm_num)
theorem B290357 : Blo 127788 290357 := bbase (se 5 (by rfl) ⟨13610, by rfl⟩ : syracuseStep 290357 = 27221) (by norm_num)
theorem B355909 : Blo 127788 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B192077 : Blo 127788 192077 := bbase (se 3 (by rfl) ⟨36014, by rfl⟩ : syracuseStep 192077 = 72029) (by norm_num)
theorem B192101 : Blo 127788 192101 := bbase (se 4 (by rfl) ⟨18009, by rfl⟩ : syracuseStep 192101 = 36019) (by norm_num)
theorem B192125 : Blo 127788 192125 := bbase (se 3 (by rfl) ⟨36023, by rfl⟩ : syracuseStep 192125 = 72047) (by norm_num)
theorem B290429 : Blo 127788 290429 := bbase (se 3 (by rfl) ⟨54455, by rfl⟩ : syracuseStep 290429 = 108911) (by norm_num)
theorem B192149 : Blo 127788 192149 := bbase (se 6 (by rfl) ⟨4503, by rfl⟩ : syracuseStep 192149 = 9007) (by norm_num)
theorem B192173 : Blo 127788 192173 := bbase (se 3 (by rfl) ⟨36032, by rfl⟩ : syracuseStep 192173 = 72065) (by norm_num)
theorem B487093 : Blo 127788 487093 := bbase (se 5 (by rfl) ⟨22832, by rfl⟩ : syracuseStep 487093 = 45665) (by norm_num)
theorem B192197 : Blo 127788 192197 := bbase (se 4 (by rfl) ⟨18018, by rfl⟩ : syracuseStep 192197 = 36037) (by norm_num)
theorem B290501 : Blo 127788 290501 := bbase (se 4 (by rfl) ⟨27234, by rfl⟩ : syracuseStep 290501 = 54469) (by norm_num)
theorem B192221 : Blo 127788 192221 := bbase (se 3 (by rfl) ⟨36041, by rfl⟩ : syracuseStep 192221 = 72083) (by norm_num)
theorem B454373 : Blo 127788 454373 := bbase (se 4 (by rfl) ⟨42597, by rfl⟩ : syracuseStep 454373 = 85195) (by norm_num)
theorem B192245 : Blo 127788 192245 := bbase (se 5 (by rfl) ⟨9011, by rfl⟩ : syracuseStep 192245 = 18023) (by norm_num)
theorem B192269 : Blo 127788 192269 := bbase (se 3 (by rfl) ⟨36050, by rfl⟩ : syracuseStep 192269 = 72101) (by norm_num)
theorem B290573 : Blo 127788 290573 := bbase (se 3 (by rfl) ⟨54482, by rfl⟩ : syracuseStep 290573 = 108965) (by norm_num)
theorem B192293 : Blo 127788 192293 := bbase (se 4 (by rfl) ⟨18027, by rfl⟩ : syracuseStep 192293 = 36055) (by norm_num)
theorem B716597 : Blo 127788 716597 := bbase (se 5 (by rfl) ⟨33590, by rfl⟩ : syracuseStep 716597 = 67181) (by norm_num)
theorem B192317 : Blo 127788 192317 := bbase (se 3 (by rfl) ⟨36059, by rfl⟩ : syracuseStep 192317 = 72119) (by norm_num)
theorem B651077 : Blo 127788 651077 := bbase (se 4 (by rfl) ⟨61038, by rfl⟩ : syracuseStep 651077 = 122077) (by norm_num)
theorem B192341 : Blo 127788 192341 := bbase (se 9 (by rfl) ⟨563, by rfl⟩ : syracuseStep 192341 = 1127) (by norm_num)
theorem B290645 : Blo 127788 290645 := bbase (se 9 (by rfl) ⟨851, by rfl⟩ : syracuseStep 290645 = 1703) (by norm_num)
theorem B192365 : Blo 127788 192365 := bbase (se 3 (by rfl) ⟨36068, by rfl⟩ : syracuseStep 192365 = 72137) (by norm_num)
theorem B192389 : Blo 127788 192389 := bbase (se 4 (by rfl) ⟨18036, by rfl⟩ : syracuseStep 192389 = 36073) (by norm_num)
theorem B192413 : Blo 127788 192413 := bbase (se 3 (by rfl) ⟨36077, by rfl⟩ : syracuseStep 192413 = 72155) (by norm_num)
theorem B290717 : Blo 127788 290717 := bbase (se 3 (by rfl) ⟨54509, by rfl⟩ : syracuseStep 290717 = 109019) (by norm_num)
theorem B192437 : Blo 127788 192437 := bbase (se 5 (by rfl) ⟨9020, by rfl⟩ : syracuseStep 192437 = 18041) (by norm_num)
theorem B159673 : Blo 127788 159673 := bbase (se 2 (by rfl) ⟨59877, by rfl⟩ : syracuseStep 159673 = 119755) (by norm_num)
theorem B552901 : Blo 127788 552901 := bbase (se 4 (by rfl) ⟨51834, by rfl⟩ : syracuseStep 552901 = 103669) (by norm_num)
theorem B192461 : Blo 127788 192461 := bbase (se 3 (by rfl) ⟨36086, by rfl⟩ : syracuseStep 192461 = 72173) (by norm_num)
theorem B192485 : Blo 127788 192485 := bbase (se 4 (by rfl) ⟨18045, by rfl⟩ : syracuseStep 192485 = 36091) (by norm_num)
theorem B487397 : Blo 127788 487397 := bbase (se 4 (by rfl) ⟨45693, by rfl⟩ : syracuseStep 487397 = 91387) (by norm_num)
theorem B290789 : Blo 127788 290789 := bbase (se 4 (by rfl) ⟨27261, by rfl⟩ : syracuseStep 290789 = 54523) (by norm_num)
theorem B192509 : Blo 127788 192509 := bbase (se 3 (by rfl) ⟨36095, by rfl⟩ : syracuseStep 192509 = 72191) (by norm_num)
theorem B192533 : Blo 127788 192533 := bbase (se 6 (by rfl) ⟨4512, by rfl⟩ : syracuseStep 192533 = 9025) (by norm_num)
theorem B192557 : Blo 127788 192557 := bbase (se 3 (by rfl) ⟨36104, by rfl⟩ : syracuseStep 192557 = 72209) (by norm_num)
theorem B290861 : Blo 127788 290861 := bbase (se 3 (by rfl) ⟨54536, by rfl⟩ : syracuseStep 290861 = 109073) (by norm_num)
theorem B192581 : Blo 127788 192581 := bbase (se 4 (by rfl) ⟨18054, by rfl⟩ : syracuseStep 192581 = 36109) (by norm_num)
theorem B192605 : Blo 127788 192605 := bbase (se 3 (by rfl) ⟨36113, by rfl⟩ : syracuseStep 192605 = 72227) (by norm_num)
theorem B192629 : Blo 127788 192629 := bbase (se 5 (by rfl) ⟨9029, by rfl⟩ : syracuseStep 192629 = 18059) (by norm_num)
theorem B290933 : Blo 127788 290933 := bbase (se 5 (by rfl) ⟨13637, by rfl⟩ : syracuseStep 290933 = 27275) (by norm_num)
theorem B192653 : Blo 127788 192653 := bbase (se 3 (by rfl) ⟨36122, by rfl⟩ : syracuseStep 192653 = 72245) (by norm_num)
theorem B356501 : Blo 127788 356501 := bbase (se 6 (by rfl) ⟨8355, by rfl⟩ : syracuseStep 356501 = 16711) (by norm_num)
theorem B192677 : Blo 127788 192677 := bbase (se 4 (by rfl) ⟨18063, by rfl⟩ : syracuseStep 192677 = 36127) (by norm_num)
theorem B192701 : Blo 127788 192701 := bbase (se 3 (by rfl) ⟨36131, by rfl⟩ : syracuseStep 192701 = 72263) (by norm_num)
theorem B291005 : Blo 127788 291005 := bbase (se 3 (by rfl) ⟨54563, by rfl⟩ : syracuseStep 291005 = 109127) (by norm_num)
theorem B323797 : Blo 127788 323797 := bbase (se 7 (by rfl) ⟨3794, by rfl⟩ : syracuseStep 323797 = 7589) (by norm_num)
theorem B192725 : Blo 127788 192725 := bbase (se 7 (by rfl) ⟨2258, by rfl⟩ : syracuseStep 192725 = 4517) (by norm_num)
theorem B192749 : Blo 127788 192749 := bbase (se 3 (by rfl) ⟨36140, by rfl⟩ : syracuseStep 192749 = 72281) (by norm_num)
theorem B192773 : Blo 127788 192773 := bbase (se 4 (by rfl) ⟨18072, by rfl⟩ : syracuseStep 192773 = 36145) (by norm_num)
theorem B291077 : Blo 127788 291077 := bbase (se 4 (by rfl) ⟨27288, by rfl⟩ : syracuseStep 291077 = 54577) (by norm_num)
theorem B192797 : Blo 127788 192797 := bbase (se 3 (by rfl) ⟨36149, by rfl⟩ : syracuseStep 192797 = 72299) (by norm_num)
theorem B192821 : Blo 127788 192821 := bbase (se 5 (by rfl) ⟨9038, by rfl⟩ : syracuseStep 192821 = 18077) (by norm_num)
theorem B323909 : Blo 127788 323909 := bbase (se 4 (by rfl) ⟨30366, by rfl⟩ : syracuseStep 323909 = 60733) (by norm_num)
theorem B192845 : Blo 127788 192845 := bbase (se 3 (by rfl) ⟨36158, by rfl⟩ : syracuseStep 192845 = 72317) (by norm_num)
theorem B291149 : Blo 127788 291149 := bbase (se 3 (by rfl) ⟨54590, by rfl⟩ : syracuseStep 291149 = 109181) (by norm_num)
theorem B192869 : Blo 127788 192869 := bbase (se 4 (by rfl) ⟨18081, by rfl⟩ : syracuseStep 192869 = 36163) (by norm_num)
theorem B192893 : Blo 127788 192893 := bbase (se 3 (by rfl) ⟨36167, by rfl⟩ : syracuseStep 192893 = 72335) (by norm_num)
theorem B192917 : Blo 127788 192917 := bbase (se 6 (by rfl) ⟨4521, by rfl⟩ : syracuseStep 192917 = 9043) (by norm_num)
theorem B291221 : Blo 127788 291221 := bbase (se 6 (by rfl) ⟨6825, by rfl⟩ : syracuseStep 291221 = 13651) (by norm_num)
theorem B422309 : Blo 127788 422309 := bbase (se 4 (by rfl) ⟨39591, by rfl⟩ : syracuseStep 422309 = 79183) (by norm_num)
theorem B192941 : Blo 127788 192941 := bbase (se 3 (by rfl) ⟨36176, by rfl⟩ : syracuseStep 192941 = 72353) (by norm_num)
theorem B389557 : Blo 127788 389557 := bbase (se 5 (by rfl) ⟨18260, by rfl⟩ : syracuseStep 389557 = 36521) (by norm_num)
theorem B750005 : Blo 127788 750005 := bbase (se 5 (by rfl) ⟨35156, by rfl⟩ : syracuseStep 750005 = 70313) (by norm_num)
theorem B192965 : Blo 127788 192965 := bbase (se 4 (by rfl) ⟨18090, by rfl⟩ : syracuseStep 192965 = 36181) (by norm_num)
theorem B192989 : Blo 127788 192989 := bbase (se 3 (by rfl) ⟨36185, by rfl⟩ : syracuseStep 192989 = 72371) (by norm_num)
theorem B291293 : Blo 127788 291293 := bbase (se 3 (by rfl) ⟨54617, by rfl⟩ : syracuseStep 291293 = 109235) (by norm_num)
theorem B193013 : Blo 127788 193013 := bbase (se 5 (by rfl) ⟨9047, by rfl⟩ : syracuseStep 193013 = 18095) (by norm_num)
theorem B324101 : Blo 127788 324101 := bbase (se 4 (by rfl) ⟨30384, by rfl⟩ : syracuseStep 324101 = 60769) (by norm_num)
theorem B193037 : Blo 127788 193037 := bbase (se 3 (by rfl) ⟨36194, by rfl⟩ : syracuseStep 193037 = 72389) (by norm_num)
theorem B193061 : Blo 127788 193061 := bbase (se 4 (by rfl) ⟨18099, by rfl⟩ : syracuseStep 193061 = 36199) (by norm_num)
theorem B291365 : Blo 127788 291365 := bbase (se 4 (by rfl) ⟨27315, by rfl⟩ : syracuseStep 291365 = 54631) (by norm_num)
theorem B193085 : Blo 127788 193085 := bbase (se 3 (by rfl) ⟨36203, by rfl⟩ : syracuseStep 193085 = 72407) (by norm_num)
theorem B193109 : Blo 127788 193109 := bbase (se 8 (by rfl) ⟨1131, by rfl⟩ : syracuseStep 193109 = 2263) (by norm_num)
theorem B193133 : Blo 127788 193133 := bbase (se 3 (by rfl) ⟨36212, by rfl⟩ : syracuseStep 193133 = 72425) (by norm_num)
theorem B291437 : Blo 127788 291437 := bbase (se 3 (by rfl) ⟨54644, by rfl⟩ : syracuseStep 291437 = 109289) (by norm_num)
theorem B193157 : Blo 127788 193157 := bbase (se 4 (by rfl) ⟨18108, by rfl⟩ : syracuseStep 193157 = 36217) (by norm_num)
theorem B160393 : Blo 127788 160393 := bbase (se 2 (by rfl) ⟨60147, by rfl⟩ : syracuseStep 160393 = 120295) (by norm_num)
theorem B193181 : Blo 127788 193181 := bbase (se 3 (by rfl) ⟨36221, by rfl⟩ : syracuseStep 193181 = 72443) (by norm_num)
theorem B193205 : Blo 127788 193205 := bbase (se 5 (by rfl) ⟨9056, by rfl⟩ : syracuseStep 193205 = 18113) (by norm_num)
theorem B291509 : Blo 127788 291509 := bbase (se 5 (by rfl) ⟨13664, by rfl⟩ : syracuseStep 291509 = 27329) (by norm_num)
theorem B193229 : Blo 127788 193229 := bbase (se 3 (by rfl) ⟨36230, by rfl⟩ : syracuseStep 193229 = 72461) (by norm_num)
theorem B193253 : Blo 127788 193253 := bbase (se 4 (by rfl) ⟨18117, by rfl⟩ : syracuseStep 193253 = 36235) (by norm_num)
theorem B193277 : Blo 127788 193277 := bbase (se 3 (by rfl) ⟨36239, by rfl⟩ : syracuseStep 193277 = 72479) (by norm_num)
theorem B291581 : Blo 127788 291581 := bbase (se 3 (by rfl) ⟨54671, by rfl⟩ : syracuseStep 291581 = 109343) (by norm_num)
theorem B193301 : Blo 127788 193301 := bbase (se 6 (by rfl) ⟨4530, by rfl⟩ : syracuseStep 193301 = 9061) (by norm_num)
theorem B193325 : Blo 127788 193325 := bbase (se 3 (by rfl) ⟨36248, by rfl⟩ : syracuseStep 193325 = 72497) (by norm_num)
theorem B193349 : Blo 127788 193349 := bbase (se 4 (by rfl) ⟨18126, by rfl⟩ : syracuseStep 193349 = 36253) (by norm_num)
theorem B291653 : Blo 127788 291653 := bbase (se 4 (by rfl) ⟨27342, by rfl⟩ : syracuseStep 291653 = 54685) (by norm_num)
theorem B324445 : Blo 127788 324445 := bbase (se 3 (by rfl) ⟨60833, by rfl⟩ : syracuseStep 324445 = 121667) (by norm_num)
theorem B193373 : Blo 127788 193373 := bbase (se 3 (by rfl) ⟨36257, by rfl⟩ : syracuseStep 193373 = 72515) (by norm_num)
theorem B193397 : Blo 127788 193397 := bbase (se 5 (by rfl) ⟨9065, by rfl⟩ : syracuseStep 193397 = 18131) (by norm_num)
theorem B193421 : Blo 127788 193421 := bbase (se 3 (by rfl) ⟨36266, by rfl⟩ : syracuseStep 193421 = 72533) (by norm_num)
theorem B291725 : Blo 127788 291725 := bbase (se 3 (by rfl) ⟨54698, by rfl⟩ : syracuseStep 291725 = 109397) (by norm_num)
theorem B193445 : Blo 127788 193445 := bbase (se 4 (by rfl) ⟨18135, by rfl⟩ : syracuseStep 193445 = 36271) (by norm_num)
theorem B193469 : Blo 127788 193469 := bbase (se 3 (by rfl) ⟨36275, by rfl⟩ : syracuseStep 193469 = 72551) (by norm_num)
theorem B324557 : Blo 127788 324557 := bbase (se 3 (by rfl) ⟨60854, by rfl⟩ : syracuseStep 324557 = 121709) (by norm_num)
theorem B193493 : Blo 127788 193493 := bbase (se 7 (by rfl) ⟨2267, by rfl⟩ : syracuseStep 193493 = 4535) (by norm_num)
theorem B291797 : Blo 127788 291797 := bbase (se 7 (by rfl) ⟨3419, by rfl⟩ : syracuseStep 291797 = 6839) (by norm_num)
theorem B193517 : Blo 127788 193517 := bbase (se 3 (by rfl) ⟨36284, by rfl⟩ : syracuseStep 193517 = 72569) (by norm_num)
theorem B193541 : Blo 127788 193541 := bbase (se 4 (by rfl) ⟨18144, by rfl⟩ : syracuseStep 193541 = 36289) (by norm_num)
theorem B193565 : Blo 127788 193565 := bbase (se 3 (by rfl) ⟨36293, by rfl⟩ : syracuseStep 193565 = 72587) (by norm_num)
theorem B291869 : Blo 127788 291869 := bbase (se 3 (by rfl) ⟨54725, by rfl⟩ : syracuseStep 291869 = 109451) (by norm_num)
theorem B193589 : Blo 127788 193589 := bbase (se 5 (by rfl) ⟨9074, by rfl⟩ : syracuseStep 193589 = 18149) (by norm_num)
theorem B193613 : Blo 127788 193613 := bbase (se 3 (by rfl) ⟨36302, by rfl⟩ : syracuseStep 193613 = 72605) (by norm_num)
theorem B652373 : Blo 127788 652373 := bbase (se 8 (by rfl) ⟨3822, by rfl⟩ : syracuseStep 652373 = 7645) (by norm_num)
theorem B193637 : Blo 127788 193637 := bbase (se 4 (by rfl) ⟨18153, by rfl⟩ : syracuseStep 193637 = 36307) (by norm_num)
theorem B291941 : Blo 127788 291941 := bbase (se 4 (by rfl) ⟨27369, by rfl⟩ : syracuseStep 291941 = 54739) (by norm_num)
theorem B193661 : Blo 127788 193661 := bbase (se 3 (by rfl) ⟨36311, by rfl⟩ : syracuseStep 193661 = 72623) (by norm_num)
theorem B324749 : Blo 127788 324749 := bbase (se 3 (by rfl) ⟨60890, by rfl⟩ : syracuseStep 324749 = 121781) (by norm_num)
theorem B193685 : Blo 127788 193685 := bbase (se 6 (by rfl) ⟨4539, by rfl⟩ : syracuseStep 193685 = 9079) (by norm_num)
theorem B193709 : Blo 127788 193709 := bbase (se 3 (by rfl) ⟨36320, by rfl⟩ : syracuseStep 193709 = 72641) (by norm_num)
theorem B292013 : Blo 127788 292013 := bbase (se 3 (by rfl) ⟨54752, by rfl⟩ : syracuseStep 292013 = 109505) (by norm_num)
theorem B193733 : Blo 127788 193733 := bbase (se 4 (by rfl) ⟨18162, by rfl⟩ : syracuseStep 193733 = 36325) (by norm_num)
theorem B193757 : Blo 127788 193757 := bbase (se 3 (by rfl) ⟨36329, by rfl⟩ : syracuseStep 193757 = 72659) (by norm_num)
theorem B193781 : Blo 127788 193781 := bbase (se 5 (by rfl) ⟨9083, by rfl⟩ : syracuseStep 193781 = 18167) (by norm_num)
theorem B292085 : Blo 127788 292085 := bbase (se 5 (by rfl) ⟨13691, by rfl⟩ : syracuseStep 292085 = 27383) (by norm_num)
theorem B193805 : Blo 127788 193805 := bbase (se 3 (by rfl) ⟨36338, by rfl⟩ : syracuseStep 193805 = 72677) (by norm_num)
theorem B193829 : Blo 127788 193829 := bbase (se 4 (by rfl) ⟨18171, by rfl⟩ : syracuseStep 193829 = 36343) (by norm_num)
theorem B193853 : Blo 127788 193853 := bbase (se 3 (by rfl) ⟨36347, by rfl⟩ : syracuseStep 193853 = 72695) (by norm_num)
theorem B292157 : Blo 127788 292157 := bbase (se 3 (by rfl) ⟨54779, by rfl⟩ : syracuseStep 292157 = 109559) (by norm_num)
theorem B193877 : Blo 127788 193877 := bbase (se 13 (by rfl) ⟨35, by rfl⟩ : syracuseStep 193877 = 71) (by norm_num)
theorem B193901 : Blo 127788 193901 := bbase (se 3 (by rfl) ⟨36356, by rfl⟩ : syracuseStep 193901 = 72713) (by norm_num)
theorem B193925 : Blo 127788 193925 := bbase (se 4 (by rfl) ⟨18180, by rfl⟩ : syracuseStep 193925 = 36361) (by norm_num)
theorem B292229 : Blo 127788 292229 := bbase (se 4 (by rfl) ⟨27396, by rfl⟩ : syracuseStep 292229 = 54793) (by norm_num)
theorem B193949 : Blo 127788 193949 := bbase (se 3 (by rfl) ⟨36365, by rfl⟩ : syracuseStep 193949 = 72731) (by norm_num)
theorem B193973 : Blo 127788 193973 := bbase (se 5 (by rfl) ⟨9092, by rfl⟩ : syracuseStep 193973 = 18185) (by norm_num)
theorem B193997 : Blo 127788 193997 := bbase (se 3 (by rfl) ⟨36374, by rfl⟩ : syracuseStep 193997 = 72749) (by norm_num)
theorem B292301 : Blo 127788 292301 := bbase (se 3 (by rfl) ⟨54806, by rfl⟩ : syracuseStep 292301 = 109613) (by norm_num)
theorem B325093 : Blo 127788 325093 := bbase (se 4 (by rfl) ⟨30477, by rfl⟩ : syracuseStep 325093 = 60955) (by norm_num)
theorem B194021 : Blo 127788 194021 := bbase (se 4 (by rfl) ⟨18189, by rfl⟩ : syracuseStep 194021 = 36379) (by norm_num)
theorem B194045 : Blo 127788 194045 := bbase (se 3 (by rfl) ⟨36383, by rfl⟩ : syracuseStep 194045 = 72767) (by norm_num)
theorem B194069 : Blo 127788 194069 := bbase (se 6 (by rfl) ⟨4548, by rfl⟩ : syracuseStep 194069 = 9097) (by norm_num)
theorem B292373 : Blo 127788 292373 := bbase (se 6 (by rfl) ⟨6852, by rfl⟩ : syracuseStep 292373 = 13705) (by norm_num)
theorem B194093 : Blo 127788 194093 := bbase (se 3 (by rfl) ⟨36392, by rfl⟩ : syracuseStep 194093 = 72785) (by norm_num)
theorem B456245 : Blo 127788 456245 := bbase (se 5 (by rfl) ⟨21386, by rfl⟩ : syracuseStep 456245 = 42773) (by norm_num)
theorem B194117 : Blo 127788 194117 := bbase (se 4 (by rfl) ⟨18198, by rfl⟩ : syracuseStep 194117 = 36397) (by norm_num)
theorem B325205 : Blo 127788 325205 := bbase (se 8 (by rfl) ⟨1905, by rfl⟩ : syracuseStep 325205 = 3811) (by norm_num)
theorem B194141 : Blo 127788 194141 := bbase (se 3 (by rfl) ⟨36401, by rfl⟩ : syracuseStep 194141 = 72803) (by norm_num)
theorem B292445 : Blo 127788 292445 := bbase (se 3 (by rfl) ⟨54833, by rfl⟩ : syracuseStep 292445 = 109667) (by norm_num)
theorem B194165 : Blo 127788 194165 := bbase (se 5 (by rfl) ⟨9101, by rfl⟩ : syracuseStep 194165 = 18203) (by norm_num)
theorem B194189 : Blo 127788 194189 := bbase (se 3 (by rfl) ⟨36410, by rfl⟩ : syracuseStep 194189 = 72821) (by norm_num)
theorem B194213 : Blo 127788 194213 := bbase (se 4 (by rfl) ⟨18207, by rfl⟩ : syracuseStep 194213 = 36415) (by norm_num)
theorem B292517 : Blo 127788 292517 := bbase (se 4 (by rfl) ⟨27423, by rfl⟩ : syracuseStep 292517 = 54847) (by norm_num)
theorem B521909 : Blo 127788 521909 := bbase (se 5 (by rfl) ⟨24464, by rfl⟩ : syracuseStep 521909 = 48929) (by norm_num)
theorem B194237 : Blo 127788 194237 := bbase (se 3 (by rfl) ⟨36419, by rfl⟩ : syracuseStep 194237 = 72839) (by norm_num)
theorem B194261 : Blo 127788 194261 := bbase (se 7 (by rfl) ⟨2276, by rfl⟩ : syracuseStep 194261 = 4553) (by norm_num)
theorem B194285 : Blo 127788 194285 := bbase (se 3 (by rfl) ⟨36428, by rfl⟩ : syracuseStep 194285 = 72857) (by norm_num)
theorem B292589 : Blo 127788 292589 := bbase (se 3 (by rfl) ⟨54860, by rfl⟩ : syracuseStep 292589 = 109721) (by norm_num)
theorem B194309 : Blo 127788 194309 := bbase (se 4 (by rfl) ⟨18216, by rfl⟩ : syracuseStep 194309 = 36433) (by norm_num)
theorem B325397 : Blo 127788 325397 := bbase (se 6 (by rfl) ⟨7626, by rfl⟩ : syracuseStep 325397 = 15253) (by norm_num)
theorem B194333 : Blo 127788 194333 := bbase (se 3 (by rfl) ⟨36437, by rfl⟩ : syracuseStep 194333 = 72875) (by norm_num)
theorem B194357 : Blo 127788 194357 := bbase (se 5 (by rfl) ⟨9110, by rfl⟩ : syracuseStep 194357 = 18221) (by norm_num)
theorem B292661 : Blo 127788 292661 := bbase (se 5 (by rfl) ⟨13718, by rfl⟩ : syracuseStep 292661 = 27437) (by norm_num)
theorem B161605 : Blo 127788 161605 := bbase (se 4 (by rfl) ⟨15150, by rfl⟩ : syracuseStep 161605 = 30301) (by norm_num)
theorem B194381 : Blo 127788 194381 := bbase (se 3 (by rfl) ⟨36446, by rfl⟩ : syracuseStep 194381 = 72893) (by norm_num)
theorem B194389 : Blo 127788 194389 := bbase (se 9 (by rfl) ⟨569, by rfl⟩ : syracuseStep 194389 = 1139) (by norm_num)
theorem B194405 : Blo 127788 194405 := bbase (se 4 (by rfl) ⟨18225, by rfl⟩ : syracuseStep 194405 = 36451) (by norm_num)
theorem B259949 : Blo 127788 259949 := bbase (se 3 (by rfl) ⟨48740, by rfl⟩ : syracuseStep 259949 = 97481) (by norm_num)
theorem B194429 : Blo 127788 194429 := bbase (se 3 (by rfl) ⟨36455, by rfl⟩ : syracuseStep 194429 = 72911) (by norm_num)
theorem B292733 : Blo 127788 292733 := bbase (se 3 (by rfl) ⟨54887, by rfl⟩ : syracuseStep 292733 = 109775) (by norm_num)
theorem B194453 : Blo 127788 194453 := bbase (se 6 (by rfl) ⟨4557, by rfl⟩ : syracuseStep 194453 = 9115) (by norm_num)
theorem B194477 : Blo 127788 194477 := bbase (se 3 (by rfl) ⟨36464, by rfl⟩ : syracuseStep 194477 = 72929) (by norm_num)
theorem B194501 : Blo 127788 194501 := bbase (se 4 (by rfl) ⟨18234, by rfl⟩ : syracuseStep 194501 = 36469) (by norm_num)
theorem B292805 : Blo 127788 292805 := bbase (se 4 (by rfl) ⟨27450, by rfl⟩ : syracuseStep 292805 = 54901) (by norm_num)
theorem B194525 : Blo 127788 194525 := bbase (se 3 (by rfl) ⟨36473, by rfl⟩ : syracuseStep 194525 = 72947) (by norm_num)
theorem B161777 : Blo 127788 161777 := bbase (se 2 (by rfl) ⟨60666, by rfl⟩ : syracuseStep 161777 = 121333) (by norm_num)
theorem B194549 : Blo 127788 194549 := bbase (se 5 (by rfl) ⟨9119, by rfl⟩ : syracuseStep 194549 = 18239) (by norm_num)
theorem B194573 : Blo 127788 194573 := bbase (se 3 (by rfl) ⟨36482, by rfl⟩ : syracuseStep 194573 = 72965) (by norm_num)
theorem B292877 : Blo 127788 292877 := bbase (se 3 (by rfl) ⟨54914, by rfl⟩ : syracuseStep 292877 = 109829) (by norm_num)
theorem B489509 : Blo 127788 489509 := bbase (se 4 (by rfl) ⟨45891, by rfl⟩ : syracuseStep 489509 = 91783) (by norm_num)
theorem B194597 : Blo 127788 194597 := bbase (se 4 (by rfl) ⟨18243, by rfl⟩ : syracuseStep 194597 = 36487) (by norm_num)
theorem B161833 : Blo 127788 161833 := bbase (se 2 (by rfl) ⟨60687, by rfl⟩ : syracuseStep 161833 = 121375) (by norm_num)
theorem B194621 : Blo 127788 194621 := bbase (se 3 (by rfl) ⟨36491, by rfl⟩ : syracuseStep 194621 = 72983) (by norm_num)
theorem B194645 : Blo 127788 194645 := bbase (se 8 (by rfl) ⟨1140, by rfl⟩ : syracuseStep 194645 = 2281) (by norm_num)
theorem B292949 : Blo 127788 292949 := bbase (se 8 (by rfl) ⟨1716, by rfl⟩ : syracuseStep 292949 = 3433) (by norm_num)
theorem B325741 : Blo 127788 325741 := bbase (se 3 (by rfl) ⟨61076, by rfl⟩ : syracuseStep 325741 = 122153) (by norm_num)
theorem B194669 : Blo 127788 194669 := bbase (se 3 (by rfl) ⟨36500, by rfl⟩ : syracuseStep 194669 = 73001) (by norm_num)
theorem B194693 : Blo 127788 194693 := bbase (se 4 (by rfl) ⟨18252, by rfl⟩ : syracuseStep 194693 = 36505) (by norm_num)
theorem B161929 : Blo 127788 161929 := bbase (se 2 (by rfl) ⟨60723, by rfl⟩ : syracuseStep 161929 = 121447) (by norm_num)
theorem B194717 : Blo 127788 194717 := bbase (se 3 (by rfl) ⟨36509, by rfl⟩ : syracuseStep 194717 = 73019) (by norm_num)
theorem B293021 : Blo 127788 293021 := bbase (se 3 (by rfl) ⟨54941, by rfl⟩ : syracuseStep 293021 = 109883) (by norm_num)
theorem B194741 : Blo 127788 194741 := bbase (se 5 (by rfl) ⟨9128, by rfl⟩ : syracuseStep 194741 = 18257) (by norm_num)
theorem B194765 : Blo 127788 194765 := bbase (se 3 (by rfl) ⟨36518, by rfl⟩ : syracuseStep 194765 = 73037) (by norm_num)
theorem B325853 : Blo 127788 325853 := bbase (se 3 (by rfl) ⟨61097, by rfl⟩ : syracuseStep 325853 = 122195) (by norm_num)
theorem B194789 : Blo 127788 194789 := bbase (se 4 (by rfl) ⟨18261, by rfl⟩ : syracuseStep 194789 = 36523) (by norm_num)
theorem B293093 : Blo 127788 293093 := bbase (se 4 (by rfl) ⟨27477, by rfl⟩ : syracuseStep 293093 = 54955) (by norm_num)
theorem B194813 : Blo 127788 194813 := bbase (se 3 (by rfl) ⟨36527, by rfl⟩ : syracuseStep 194813 = 73055) (by norm_num)
theorem B194837 : Blo 127788 194837 := bbase (se 6 (by rfl) ⟨4566, by rfl⟩ : syracuseStep 194837 = 9133) (by norm_num)
theorem B293165 : Blo 127788 293165 := bbase (se 3 (by rfl) ⟨54968, by rfl⟩ : syracuseStep 293165 = 109937) (by norm_num)
theorem B194861 : Blo 127788 194861 := bbase (se 3 (by rfl) ⟨36536, by rfl⟩ : syracuseStep 194861 = 73073) (by norm_num)
theorem B162101 : Blo 127788 162101 := bbase (se 5 (by rfl) ⟨7598, by rfl⟩ : syracuseStep 162101 = 15197) (by norm_num)
theorem B489797 : Blo 127788 489797 := bbase (se 4 (by rfl) ⟨45918, by rfl⟩ : syracuseStep 489797 = 91837) (by norm_num)
theorem B194885 : Blo 127788 194885 := bbase (se 4 (by rfl) ⟨18270, by rfl⟩ : syracuseStep 194885 = 36541) (by norm_num)
theorem B194909 : Blo 127788 194909 := bbase (se 3 (by rfl) ⟨36545, by rfl⟩ : syracuseStep 194909 = 73091) (by norm_num)
theorem B653669 : Blo 127788 653669 := bbase (se 4 (by rfl) ⟨61281, by rfl⟩ : syracuseStep 653669 = 122563) (by norm_num)
theorem B162157 : Blo 127788 162157 := bbase (se 3 (by rfl) ⟨30404, by rfl⟩ : syracuseStep 162157 = 60809) (by norm_num)
theorem B194933 : Blo 127788 194933 := bbase (se 5 (by rfl) ⟨9137, by rfl⟩ : syracuseStep 194933 = 18275) (by norm_num)
theorem B293237 : Blo 127788 293237 := bbase (se 5 (by rfl) ⟨13745, by rfl⟩ : syracuseStep 293237 = 27491) (by norm_num)
theorem B194957 : Blo 127788 194957 := bbase (se 3 (by rfl) ⟨36554, by rfl⟩ : syracuseStep 194957 = 73109) (by norm_num)
theorem B326045 : Blo 127788 326045 := bbase (se 3 (by rfl) ⟨61133, by rfl⟩ : syracuseStep 326045 = 122267) (by norm_num)
theorem B194981 : Blo 127788 194981 := bbase (se 4 (by rfl) ⟨18279, by rfl⟩ : syracuseStep 194981 = 36559) (by norm_num)
theorem B195005 : Blo 127788 195005 := bbase (se 3 (by rfl) ⟨36563, by rfl⟩ : syracuseStep 195005 = 73127) (by norm_num)
theorem B293309 : Blo 127788 293309 := bbase (se 3 (by rfl) ⟨54995, by rfl⟩ : syracuseStep 293309 = 109991) (by norm_num)
theorem B162253 : Blo 127788 162253 := bbase (se 3 (by rfl) ⟨30422, by rfl⟩ : syracuseStep 162253 = 60845) (by norm_num)
theorem B195029 : Blo 127788 195029 := bbase (se 7 (by rfl) ⟨2285, by rfl⟩ : syracuseStep 195029 = 4571) (by norm_num)
theorem B195053 : Blo 127788 195053 := bbase (se 3 (by rfl) ⟨36572, by rfl⟩ : syracuseStep 195053 = 73145) (by norm_num)
theorem B260597 : Blo 127788 260597 := bbase (se 5 (by rfl) ⟨12215, by rfl⟩ : syracuseStep 260597 = 24431) (by norm_num)
theorem B195077 : Blo 127788 195077 := bbase (se 4 (by rfl) ⟨18288, by rfl⟩ : syracuseStep 195077 = 36577) (by norm_num)
theorem B293381 : Blo 127788 293381 := bbase (se 4 (by rfl) ⟨27504, by rfl⟩ : syracuseStep 293381 = 55009) (by norm_num)
theorem B195101 : Blo 127788 195101 := bbase (se 3 (by rfl) ⟨36581, by rfl⟩ : syracuseStep 195101 = 73163) (by norm_num)
theorem B195125 : Blo 127788 195125 := bbase (se 5 (by rfl) ⟨9146, by rfl⟩ : syracuseStep 195125 = 18293) (by norm_num)
theorem B195149 : Blo 127788 195149 := bbase (se 3 (by rfl) ⟨36590, by rfl⟩ : syracuseStep 195149 = 73181) (by norm_num)
theorem B293453 : Blo 127788 293453 := bbase (se 3 (by rfl) ⟨55022, by rfl⟩ : syracuseStep 293453 = 110045) (by norm_num)
theorem B195173 : Blo 127788 195173 := bbase (se 4 (by rfl) ⟨18297, by rfl⟩ : syracuseStep 195173 = 36595) (by norm_num)
theorem B162425 : Blo 127788 162425 := bbase (se 2 (by rfl) ⟨60909, by rfl⟩ : syracuseStep 162425 = 121819) (by norm_num)
theorem B195197 : Blo 127788 195197 := bbase (se 3 (by rfl) ⟨36599, by rfl⟩ : syracuseStep 195197 = 73199) (by norm_num)
theorem B195205 : Blo 127788 195205 := bbase (se 4 (by rfl) ⟨18300, by rfl⟩ : syracuseStep 195205 = 36601) (by norm_num)
theorem B195221 : Blo 127788 195221 := bbase (se 6 (by rfl) ⟨4575, by rfl⟩ : syracuseStep 195221 = 9151) (by norm_num)
theorem B293525 : Blo 127788 293525 := bbase (se 6 (by rfl) ⟨6879, by rfl⟩ : syracuseStep 293525 = 13759) (by norm_num)
theorem B424597 : Blo 127788 424597 := bbase (se 6 (by rfl) ⟨9951, by rfl⟩ : syracuseStep 424597 = 19903) (by norm_num)
theorem B195245 : Blo 127788 195245 := bbase (se 3 (by rfl) ⟨36608, by rfl⟩ : syracuseStep 195245 = 73217) (by norm_num)
theorem B162481 : Blo 127788 162481 := bbase (se 2 (by rfl) ⟨60930, by rfl⟩ : syracuseStep 162481 = 121861) (by norm_num)
theorem B195269 : Blo 127788 195269 := bbase (se 4 (by rfl) ⟨18306, by rfl⟩ : syracuseStep 195269 = 36613) (by norm_num)
theorem B195293 : Blo 127788 195293 := bbase (se 3 (by rfl) ⟨36617, by rfl⟩ : syracuseStep 195293 = 73235) (by norm_num)
theorem B293597 : Blo 127788 293597 := bbase (se 3 (by rfl) ⟨55049, by rfl⟩ : syracuseStep 293597 = 110099) (by norm_num)
theorem B326389 : Blo 127788 326389 := bbase (se 5 (by rfl) ⟨15299, by rfl⟩ : syracuseStep 326389 = 30599) (by norm_num)
theorem B195317 : Blo 127788 195317 := bbase (se 5 (by rfl) ⟨9155, by rfl⟩ : syracuseStep 195317 = 18311) (by norm_num)
theorem B195341 : Blo 127788 195341 := bbase (se 3 (by rfl) ⟨36626, by rfl⟩ : syracuseStep 195341 = 73253) (by norm_num)
theorem B162577 : Blo 127788 162577 := bbase (se 2 (by rfl) ⟨60966, by rfl⟩ : syracuseStep 162577 = 121933) (by norm_num)
theorem B195365 : Blo 127788 195365 := bbase (se 4 (by rfl) ⟨18315, by rfl⟩ : syracuseStep 195365 = 36631) (by norm_num)
theorem B293669 : Blo 127788 293669 := bbase (se 4 (by rfl) ⟨27531, by rfl⟩ : syracuseStep 293669 = 55063) (by norm_num)
theorem B195389 : Blo 127788 195389 := bbase (se 3 (by rfl) ⟨36635, by rfl⟩ : syracuseStep 195389 = 73271) (by norm_num)
theorem B195413 : Blo 127788 195413 := bbase (se 9 (by rfl) ⟨572, by rfl⟩ : syracuseStep 195413 = 1145) (by norm_num)
theorem B326501 : Blo 127788 326501 := bbase (se 4 (by rfl) ⟨30609, by rfl⟩ : syracuseStep 326501 = 61219) (by norm_num)
theorem B195437 : Blo 127788 195437 := bbase (se 3 (by rfl) ⟨36644, by rfl⟩ : syracuseStep 195437 = 73289) (by norm_num)
theorem B293741 : Blo 127788 293741 := bbase (se 3 (by rfl) ⟨55076, by rfl⟩ : syracuseStep 293741 = 110153) (by norm_num)
theorem B555893 : Blo 127788 555893 := bbase (se 5 (by rfl) ⟨26057, by rfl⟩ : syracuseStep 555893 = 52115) (by norm_num)
theorem B195461 : Blo 127788 195461 := bbase (se 4 (by rfl) ⟨18324, by rfl⟩ : syracuseStep 195461 = 36649) (by norm_num)
theorem B195485 : Blo 127788 195485 := bbase (se 3 (by rfl) ⟨36653, by rfl⟩ : syracuseStep 195485 = 73307) (by norm_num)
theorem B195509 : Blo 127788 195509 := bbase (se 5 (by rfl) ⟨9164, by rfl⟩ : syracuseStep 195509 = 18329) (by norm_num)
theorem B293813 : Blo 127788 293813 := bbase (se 5 (by rfl) ⟨13772, by rfl⟩ : syracuseStep 293813 = 27545) (by norm_num)
theorem B162749 : Blo 127788 162749 := bbase (se 3 (by rfl) ⟨30515, by rfl⟩ : syracuseStep 162749 = 61031) (by norm_num)
theorem B195533 : Blo 127788 195533 := bbase (se 3 (by rfl) ⟨36662, by rfl⟩ : syracuseStep 195533 = 73325) (by norm_num)
theorem B195557 : Blo 127788 195557 := bbase (se 4 (by rfl) ⟨18333, by rfl⟩ : syracuseStep 195557 = 36667) (by norm_num)
theorem B162805 : Blo 127788 162805 := bbase (se 5 (by rfl) ⟨7631, by rfl⟩ : syracuseStep 162805 = 15263) (by norm_num)
theorem B195581 : Blo 127788 195581 := bbase (se 3 (by rfl) ⟨36671, by rfl⟩ : syracuseStep 195581 = 73343) (by norm_num)
theorem B293885 : Blo 127788 293885 := bbase (se 3 (by rfl) ⟨55103, by rfl⟩ : syracuseStep 293885 = 110207) (by norm_num)
theorem B195605 : Blo 127788 195605 := bbase (se 6 (by rfl) ⟨4584, by rfl⟩ : syracuseStep 195605 = 9169) (by norm_num)
theorem B326693 : Blo 127788 326693 := bbase (se 4 (by rfl) ⟨30627, by rfl⟩ : syracuseStep 326693 = 61255) (by norm_num)
theorem B195629 : Blo 127788 195629 := bbase (se 3 (by rfl) ⟨36680, by rfl⟩ : syracuseStep 195629 = 73361) (by norm_num)
theorem B195653 : Blo 127788 195653 := bbase (se 4 (by rfl) ⟨18342, by rfl⟩ : syracuseStep 195653 = 36685) (by norm_num)
theorem B293957 : Blo 127788 293957 := bbase (se 4 (by rfl) ⟨27558, by rfl⟩ : syracuseStep 293957 = 55117) (by norm_num)
theorem B162901 : Blo 127788 162901 := bbase (se 8 (by rfl) ⟨954, by rfl⟩ : syracuseStep 162901 = 1909) (by norm_num)
theorem B195677 : Blo 127788 195677 := bbase (se 3 (by rfl) ⟨36689, by rfl⟩ : syracuseStep 195677 = 73379) (by norm_num)
theorem B195701 : Blo 127788 195701 := bbase (se 5 (by rfl) ⟨9173, by rfl⟩ : syracuseStep 195701 = 18347) (by norm_num)
theorem B195725 : Blo 127788 195725 := bbase (se 3 (by rfl) ⟨36698, by rfl⟩ : syracuseStep 195725 = 73397) (by norm_num)
theorem B294029 : Blo 127788 294029 := bbase (se 3 (by rfl) ⟨55130, by rfl⟩ : syracuseStep 294029 = 110261) (by norm_num)
theorem B195749 : Blo 127788 195749 := bbase (se 4 (by rfl) ⟨18351, by rfl⟩ : syracuseStep 195749 = 36703) (by norm_num)
theorem B195773 : Blo 127788 195773 := bbase (se 3 (by rfl) ⟨36707, by rfl⟩ : syracuseStep 195773 = 73415) (by norm_num)
theorem B195797 : Blo 127788 195797 := bbase (se 7 (by rfl) ⟨2294, by rfl⟩ : syracuseStep 195797 = 4589) (by norm_num)
theorem B294101 : Blo 127788 294101 := bbase (se 7 (by rfl) ⟨3446, by rfl⟩ : syracuseStep 294101 = 6893) (by norm_num)
theorem B195821 : Blo 127788 195821 := bbase (se 3 (by rfl) ⟨36716, by rfl⟩ : syracuseStep 195821 = 73433) (by norm_num)
theorem B163073 : Blo 127788 163073 := bbase (se 2 (by rfl) ⟨61152, by rfl⟩ : syracuseStep 163073 = 122305) (by norm_num)
theorem B195845 : Blo 127788 195845 := bbase (se 4 (by rfl) ⟨18360, by rfl⟩ : syracuseStep 195845 = 36721) (by norm_num)
theorem B195869 : Blo 127788 195869 := bbase (se 3 (by rfl) ⟨36725, by rfl⟩ : syracuseStep 195869 = 73451) (by norm_num)
theorem B294173 : Blo 127788 294173 := bbase (se 3 (by rfl) ⟨55157, by rfl⟩ : syracuseStep 294173 = 110315) (by norm_num)
theorem B195893 : Blo 127788 195893 := bbase (se 5 (by rfl) ⟨9182, by rfl⟩ : syracuseStep 195893 = 18365) (by norm_num)
theorem B163129 : Blo 127788 163129 := bbase (se 2 (by rfl) ⟨61173, by rfl⟩ : syracuseStep 163129 = 122347) (by norm_num)
theorem B195917 : Blo 127788 195917 := bbase (se 3 (by rfl) ⟨36734, by rfl⟩ : syracuseStep 195917 = 73469) (by norm_num)
theorem B195941 : Blo 127788 195941 := bbase (se 4 (by rfl) ⟨18369, by rfl⟩ : syracuseStep 195941 = 36739) (by norm_num)
theorem B294245 : Blo 127788 294245 := bbase (se 4 (by rfl) ⟨27585, by rfl⟩ : syracuseStep 294245 = 55171) (by norm_num)
theorem B327037 : Blo 127788 327037 := bbase (se 3 (by rfl) ⟨61319, by rfl⟩ : syracuseStep 327037 = 122639) (by norm_num)
theorem B195965 : Blo 127788 195965 := bbase (se 3 (by rfl) ⟨36743, by rfl⟩ : syracuseStep 195965 = 73487) (by norm_num)
theorem B195989 : Blo 127788 195989 := bbase (se 6 (by rfl) ⟨4593, by rfl⟩ : syracuseStep 195989 = 9187) (by norm_num)
theorem B163225 : Blo 127788 163225 := bbase (se 2 (by rfl) ⟨61209, by rfl⟩ : syracuseStep 163225 = 122419) (by norm_num)
theorem B196013 : Blo 127788 196013 := bbase (se 3 (by rfl) ⟨36752, by rfl⟩ : syracuseStep 196013 = 73505) (by norm_num)
theorem B294317 : Blo 127788 294317 := bbase (se 3 (by rfl) ⟨55184, by rfl⟩ : syracuseStep 294317 = 110369) (by norm_num)
theorem B196037 : Blo 127788 196037 := bbase (se 4 (by rfl) ⟨18378, by rfl⟩ : syracuseStep 196037 = 36757) (by norm_num)
theorem B196061 : Blo 127788 196061 := bbase (se 3 (by rfl) ⟨36761, by rfl⟩ : syracuseStep 196061 = 73523) (by norm_num)
theorem B490981 : Blo 127788 490981 := bbase (se 4 (by rfl) ⟨46029, by rfl⟩ : syracuseStep 490981 = 92059) (by norm_num)
theorem B327149 : Blo 127788 327149 := bbase (se 3 (by rfl) ⟨61340, by rfl⟩ : syracuseStep 327149 = 122681) (by norm_num)
theorem B294389 : Blo 127788 294389 := bbase (se 5 (by rfl) ⟨13799, by rfl⟩ : syracuseStep 294389 = 27599) (by norm_num)
theorem B196085 : Blo 127788 196085 := bbase (se 5 (by rfl) ⟨9191, by rfl⟩ : syracuseStep 196085 = 18383) (by norm_num)
theorem B196109 : Blo 127788 196109 := bbase (se 3 (by rfl) ⟨36770, by rfl⟩ : syracuseStep 196109 = 73541) (by norm_num)
theorem B196133 : Blo 127788 196133 := bbase (se 4 (by rfl) ⟨18387, by rfl⟩ : syracuseStep 196133 = 36775) (by norm_num)
theorem B294461 : Blo 127788 294461 := bbase (se 3 (by rfl) ⟨55211, by rfl⟩ : syracuseStep 294461 = 110423) (by norm_num)
theorem B196157 : Blo 127788 196157 := bbase (se 3 (by rfl) ⟨36779, by rfl⟩ : syracuseStep 196157 = 73559) (by norm_num)
theorem B163397 : Blo 127788 163397 := bbase (se 4 (by rfl) ⟨15318, by rfl⟩ : syracuseStep 163397 = 30637) (by norm_num)
theorem B196181 : Blo 127788 196181 := bbase (se 8 (by rfl) ⟨1149, by rfl⟩ : syracuseStep 196181 = 2299) (by norm_num)
theorem B196205 : Blo 127788 196205 := bbase (se 3 (by rfl) ⟨36788, by rfl⟩ : syracuseStep 196205 = 73577) (by norm_num)
theorem B654965 : Blo 127788 654965 := bbase (se 5 (by rfl) ⟨30701, by rfl⟩ : syracuseStep 654965 = 61403) (by norm_num)
theorem B163453 : Blo 127788 163453 := bbase (se 3 (by rfl) ⟨30647, by rfl⟩ : syracuseStep 163453 = 61295) (by norm_num)
theorem B196229 : Blo 127788 196229 := bbase (se 4 (by rfl) ⟨18396, by rfl⟩ : syracuseStep 196229 = 36793) (by norm_num)
theorem B294533 : Blo 127788 294533 := bbase (se 4 (by rfl) ⟨27612, by rfl⟩ : syracuseStep 294533 = 55225) (by norm_num)
theorem B196253 : Blo 127788 196253 := bbase (se 3 (by rfl) ⟨36797, by rfl⟩ : syracuseStep 196253 = 73595) (by norm_num)
theorem B327341 : Blo 127788 327341 := bbase (se 3 (by rfl) ⟨61376, by rfl⟩ : syracuseStep 327341 = 122753) (by norm_num)
theorem B196277 : Blo 127788 196277 := bbase (se 5 (by rfl) ⟨9200, by rfl⟩ : syracuseStep 196277 = 18401) (by norm_num)
theorem B261829 : Blo 127788 261829 := bbase (se 4 (by rfl) ⟨24546, by rfl⟩ : syracuseStep 261829 = 49093) (by norm_num)
theorem B196301 : Blo 127788 196301 := bbase (se 3 (by rfl) ⟨36806, by rfl⟩ : syracuseStep 196301 = 73613) (by norm_num)
theorem B294605 : Blo 127788 294605 := bbase (se 3 (by rfl) ⟨55238, by rfl⟩ : syracuseStep 294605 = 110477) (by norm_num)
theorem B163549 : Blo 127788 163549 := bbase (se 3 (by rfl) ⟨30665, by rfl⟩ : syracuseStep 163549 = 61331) (by norm_num)
theorem B196325 : Blo 127788 196325 := bbase (se 4 (by rfl) ⟨18405, by rfl⟩ : syracuseStep 196325 = 36811) (by norm_num)
theorem B196349 : Blo 127788 196349 := bbase (se 3 (by rfl) ⟨36815, by rfl⟩ : syracuseStep 196349 = 73631) (by norm_num)
theorem B491285 : Blo 127788 491285 := bbase (se 6 (by rfl) ⟨11514, by rfl⟩ : syracuseStep 491285 = 23029) (by norm_num)
theorem B196373 : Blo 127788 196373 := bbase (se 6 (by rfl) ⟨4602, by rfl⟩ : syracuseStep 196373 = 9205) (by norm_num)
theorem B294677 : Blo 127788 294677 := bbase (se 6 (by rfl) ⟨6906, by rfl⟩ : syracuseStep 294677 = 13813) (by norm_num)
theorem B196397 : Blo 127788 196397 := bbase (se 3 (by rfl) ⟨36824, by rfl⟩ : syracuseStep 196397 = 73649) (by norm_num)
theorem B196421 : Blo 127788 196421 := bbase (se 4 (by rfl) ⟨18414, by rfl⟩ : syracuseStep 196421 = 36829) (by norm_num)
theorem B3211093 : Blo 127788 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B196445 : Blo 127788 196445 := bbase (se 3 (by rfl) ⟨36833, by rfl⟩ : syracuseStep 196445 = 73667) (by norm_num)
theorem B294749 : Blo 127788 294749 := bbase (se 3 (by rfl) ⟨55265, by rfl⟩ : syracuseStep 294749 = 110531) (by norm_num)
theorem B556901 : Blo 127788 556901 := bbase (se 4 (by rfl) ⟨52209, by rfl⟩ : syracuseStep 556901 = 104419) (by norm_num)
theorem B196469 : Blo 127788 196469 := bbase (se 5 (by rfl) ⟨9209, by rfl⟩ : syracuseStep 196469 = 18419) (by norm_num)
theorem B163721 : Blo 127788 163721 := bbase (se 2 (by rfl) ⟨61395, by rfl⟩ : syracuseStep 163721 = 122791) (by norm_num)
theorem B196493 : Blo 127788 196493 := bbase (se 3 (by rfl) ⟨36842, by rfl⟩ : syracuseStep 196493 = 73685) (by norm_num)
theorem B196517 : Blo 127788 196517 := bbase (se 4 (by rfl) ⟨18423, by rfl⟩ : syracuseStep 196517 = 36847) (by norm_num)
theorem B294821 : Blo 127788 294821 := bbase (se 4 (by rfl) ⟨27639, by rfl⟩ : syracuseStep 294821 = 55279) (by norm_num)
theorem B196541 : Blo 127788 196541 := bbase (se 3 (by rfl) ⟨36851, by rfl⟩ : syracuseStep 196541 = 73703) (by norm_num)
theorem B163777 : Blo 127788 163777 := bbase (se 2 (by rfl) ⟨61416, by rfl⟩ : syracuseStep 163777 = 122833) (by norm_num)
theorem B688085 : Blo 127788 688085 := bbase (se 7 (by rfl) ⟨8063, by rfl⟩ : syracuseStep 688085 = 16127) (by norm_num)
theorem B196565 : Blo 127788 196565 := bbase (se 7 (by rfl) ⟨2303, by rfl⟩ : syracuseStep 196565 = 4607) (by norm_num)
theorem B131041 : Blo 127788 131041 := bbase (se 2 (by rfl) ⟨49140, by rfl⟩ : syracuseStep 131041 = 98281) (by norm_num)
theorem B196589 : Blo 127788 196589 := bbase (se 3 (by rfl) ⟨36860, by rfl⟩ : syracuseStep 196589 = 73721) (by norm_num)
theorem B294893 : Blo 127788 294893 := bbase (se 3 (by rfl) ⟨55292, by rfl⟩ : syracuseStep 294893 = 110585) (by norm_num)
theorem B131075 : Blo 127788 131075 := bstep (se 1 (by rfl) ⟨98306, by rfl⟩ : syracuseStep 131075 = 196613) B196613
theorem B294929 : Blo 127788 294929 := bstep (se 2 (by rfl) ⟨110598, by rfl⟩ : syracuseStep 294929 = 221197) B221197
theorem B196625 : Blo 127788 196625 := bstep (se 2 (by rfl) ⟨73734, by rfl⟩ : syracuseStep 196625 = 147469) B147469
theorem B131091 : Blo 127788 131091 := bstep (se 1 (by rfl) ⟨98318, by rfl⟩ : syracuseStep 131091 = 196637) B196637
theorem B294947 : Blo 127788 294947 := bstep (se 1 (by rfl) ⟨221210, by rfl⟩ : syracuseStep 294947 = 442421) B442421
theorem B196643 : Blo 127788 196643 := bstep (se 1 (by rfl) ⟨147482, by rfl⟩ : syracuseStep 196643 = 294965) B294965
theorem B131107 : Blo 127788 131107 := bstep (se 1 (by rfl) ⟨98330, by rfl⟩ : syracuseStep 131107 = 196661) B196661
theorem B131123 : Blo 127788 131123 := bstep (se 1 (by rfl) ⟨98342, by rfl⟩ : syracuseStep 131123 = 196685) B196685
theorem B196673 : Blo 127788 196673 := bstep (se 2 (by rfl) ⟨73752, by rfl⟩ : syracuseStep 196673 = 147505) B147505
theorem B131139 : Blo 127788 131139 := bstep (se 1 (by rfl) ⟨98354, by rfl⟩ : syracuseStep 131139 = 196709) B196709
theorem B196691 : Blo 127788 196691 := bstep (se 1 (by rfl) ⟨147518, by rfl⟩ : syracuseStep 196691 = 295037) B295037
theorem B131155 : Blo 127788 131155 := bstep (se 1 (by rfl) ⟨98366, by rfl⟩ : syracuseStep 131155 = 196733) B196733
theorem B163939 : Blo 127788 163939 := bstep (se 1 (by rfl) ⟨122954, by rfl⟩ : syracuseStep 163939 = 245909) B245909
theorem B131171 : Blo 127788 131171 := bstep (se 1 (by rfl) ⟨98378, by rfl⟩ : syracuseStep 131171 = 196757) B196757
theorem B196721 : Blo 127788 196721 := bstep (se 2 (by rfl) ⟨73770, by rfl⟩ : syracuseStep 196721 = 147541) B147541
theorem B131187 : Blo 127788 131187 := bstep (se 1 (by rfl) ⟨98390, by rfl⟩ : syracuseStep 131187 = 196781) B196781
theorem B131203 : Blo 127788 131203 := bstep (se 1 (by rfl) ⟨98402, by rfl⟩ : syracuseStep 131203 = 196805) B196805
theorem B196739 : Blo 127788 196739 := bstep (se 1 (by rfl) ⟨147554, by rfl⟩ : syracuseStep 196739 = 295109) B295109
theorem B131219 : Blo 127788 131219 := bstep (se 1 (by rfl) ⟨98414, by rfl⟩ : syracuseStep 131219 = 196829) B196829
theorem B196769 : Blo 127788 196769 := bstep (se 2 (by rfl) ⟨73788, by rfl⟩ : syracuseStep 196769 = 147577) B147577
theorem B131235 : Blo 127788 131235 := bstep (se 1 (by rfl) ⟨98426, by rfl⟩ : syracuseStep 131235 = 196853) B196853
theorem B196787 : Blo 127788 196787 := bstep (se 1 (by rfl) ⟨147590, by rfl⟩ : syracuseStep 196787 = 295181) B295181
theorem B131251 : Blo 127788 131251 := bstep (se 1 (by rfl) ⟨98438, by rfl⟩ : syracuseStep 131251 = 196877) B196877
theorem B164035 : Blo 127788 164035 := bstep (se 1 (by rfl) ⟨123026, by rfl⟩ : syracuseStep 164035 = 246053) B246053
theorem B131267 : Blo 127788 131267 := bstep (se 1 (by rfl) ⟨98450, by rfl⟩ : syracuseStep 131267 = 196901) B196901
theorem B196817 : Blo 127788 196817 := bstep (se 2 (by rfl) ⟨73806, by rfl⟩ : syracuseStep 196817 = 147613) B147613
theorem B131283 : Blo 127788 131283 := bstep (se 1 (by rfl) ⟨98462, by rfl⟩ : syracuseStep 131283 = 196925) B196925
theorem B196835 : Blo 127788 196835 := bstep (se 1 (by rfl) ⟨147626, by rfl⟩ : syracuseStep 196835 = 295253) B295253
theorem B131299 : Blo 127788 131299 := bstep (se 1 (by rfl) ⟨98474, by rfl⟩ : syracuseStep 131299 = 196949) B196949
theorem B131315 : Blo 127788 131315 := bstep (se 1 (by rfl) ⟨98486, by rfl⟩ : syracuseStep 131315 = 196973) B196973
theorem B196865 : Blo 127788 196865 := bstep (se 2 (by rfl) ⟨73824, by rfl⟩ : syracuseStep 196865 = 147649) B147649
theorem B131331 : Blo 127788 131331 := bstep (se 1 (by rfl) ⟨98498, by rfl⟩ : syracuseStep 131331 = 196997) B196997
theorem B196883 : Blo 127788 196883 := bstep (se 1 (by rfl) ⟨147662, by rfl⟩ : syracuseStep 196883 = 295325) B295325
theorem B131347 : Blo 127788 131347 := bstep (se 1 (by rfl) ⟨98510, by rfl⟩ : syracuseStep 131347 = 197021) B197021
theorem B131363 : Blo 127788 131363 := bstep (se 1 (by rfl) ⟨98522, by rfl⟩ : syracuseStep 131363 = 197045) B197045
theorem B295217 : Blo 127788 295217 := bstep (se 2 (by rfl) ⟨110706, by rfl⟩ : syracuseStep 295217 = 221413) B221413
theorem B196913 : Blo 127788 196913 := bstep (se 2 (by rfl) ⟨73842, by rfl⟩ : syracuseStep 196913 = 147685) B147685
theorem B131379 : Blo 127788 131379 := bstep (se 1 (by rfl) ⟨98534, by rfl⟩ : syracuseStep 131379 = 197069) B197069
theorem B295235 : Blo 127788 295235 := bstep (se 1 (by rfl) ⟨221426, by rfl⟩ : syracuseStep 295235 = 442853) B442853
theorem B196931 : Blo 127788 196931 := bstep (se 1 (by rfl) ⟨147698, by rfl⟩ : syracuseStep 196931 = 295397) B295397
theorem B131395 : Blo 127788 131395 := bstep (se 1 (by rfl) ⟨98546, by rfl⟩ : syracuseStep 131395 = 197093) B197093
theorem B131411 : Blo 127788 131411 := bstep (se 1 (by rfl) ⟨98558, by rfl⟩ : syracuseStep 131411 = 197117) B197117
theorem B196961 : Blo 127788 196961 := bstep (se 2 (by rfl) ⟨73860, by rfl⟩ : syracuseStep 196961 = 147721) B147721
theorem B131427 : Blo 127788 131427 := bstep (se 1 (by rfl) ⟨98570, by rfl⟩ : syracuseStep 131427 = 197141) B197141
theorem B196979 : Blo 127788 196979 := bstep (se 1 (by rfl) ⟨147734, by rfl⟩ : syracuseStep 196979 = 295469) B295469
theorem B131443 : Blo 127788 131443 := bstep (se 1 (by rfl) ⟨98582, by rfl⟩ : syracuseStep 131443 = 197165) B197165
theorem B131459 : Blo 127788 131459 := bstep (se 1 (by rfl) ⟨98594, by rfl⟩ : syracuseStep 131459 = 197189) B197189
theorem B197009 : Blo 127788 197009 := bstep (se 2 (by rfl) ⟨73878, by rfl⟩ : syracuseStep 197009 = 147757) B147757
theorem B131475 : Blo 127788 131475 := bstep (se 1 (by rfl) ⟨98606, by rfl⟩ : syracuseStep 131475 = 197213) B197213
theorem B491939 : Blo 127788 491939 := bstep (se 1 (by rfl) ⟨368954, by rfl⟩ : syracuseStep 491939 = 737909) B737909
theorem B197027 : Blo 127788 197027 := bstep (se 1 (by rfl) ⟨147770, by rfl⟩ : syracuseStep 197027 = 295541) B295541
theorem B131491 : Blo 127788 131491 := bstep (se 1 (by rfl) ⟨98618, by rfl⟩ : syracuseStep 131491 = 197237) B197237
theorem B491953 : Blo 127788 491953 := bstep (se 2 (by rfl) ⟨184482, by rfl⟩ : syracuseStep 491953 = 368965) B368965
theorem B131507 : Blo 127788 131507 := bstep (se 1 (by rfl) ⟨98630, by rfl⟩ : syracuseStep 131507 = 197261) B197261
theorem B197057 : Blo 127788 197057 := bstep (se 2 (by rfl) ⟨73896, by rfl⟩ : syracuseStep 197057 = 147793) B147793
theorem B131523 : Blo 127788 131523 := bstep (se 1 (by rfl) ⟨98642, by rfl⟩ : syracuseStep 131523 = 197285) B197285
theorem B197075 : Blo 127788 197075 := bstep (se 1 (by rfl) ⟨147806, by rfl⟩ : syracuseStep 197075 = 295613) B295613
theorem B131539 : Blo 127788 131539 := bstep (se 1 (by rfl) ⟨98654, by rfl⟩ : syracuseStep 131539 = 197309) B197309
theorem B131555 : Blo 127788 131555 := bstep (se 1 (by rfl) ⟨98666, by rfl⟩ : syracuseStep 131555 = 197333) B197333
theorem B197105 : Blo 127788 197105 := bstep (se 2 (by rfl) ⟨73914, by rfl⟩ : syracuseStep 197105 = 147829) B147829
theorem B131571 : Blo 127788 131571 := bstep (se 1 (by rfl) ⟨98678, by rfl⟩ : syracuseStep 131571 = 197357) B197357
theorem B197123 : Blo 127788 197123 := bstep (se 1 (by rfl) ⟨147842, by rfl⟩ : syracuseStep 197123 = 295685) B295685
theorem B131587 : Blo 127788 131587 := bstep (se 1 (by rfl) ⟨98690, by rfl⟩ : syracuseStep 131587 = 197381) B197381
theorem B131603 : Blo 127788 131603 := bstep (se 1 (by rfl) ⟨98702, by rfl⟩ : syracuseStep 131603 = 197405) B197405
theorem B197153 : Blo 127788 197153 := bstep (se 2 (by rfl) ⟨73932, by rfl⟩ : syracuseStep 197153 = 147865) B147865
theorem B131619 : Blo 127788 131619 := bstep (se 1 (by rfl) ⟨98714, by rfl⟩ : syracuseStep 131619 = 197429) B197429
theorem B557617 : Blo 127788 557617 := bstep (se 2 (by rfl) ⟨209106, by rfl⟩ : syracuseStep 557617 = 418213) B418213
theorem B197171 : Blo 127788 197171 := bstep (se 1 (by rfl) ⟨147878, by rfl⟩ : syracuseStep 197171 = 295757) B295757
theorem B131635 : Blo 127788 131635 := bstep (se 1 (by rfl) ⟨98726, by rfl⟩ : syracuseStep 131635 = 197453) B197453
theorem B131651 : Blo 127788 131651 := bstep (se 1 (by rfl) ⟨98738, by rfl⟩ : syracuseStep 131651 = 197477) B197477
theorem B295505 : Blo 127788 295505 := bstep (se 2 (by rfl) ⟨110814, by rfl⟩ : syracuseStep 295505 = 221629) B221629
theorem B197201 : Blo 127788 197201 := bstep (se 2 (by rfl) ⟨73950, by rfl⟩ : syracuseStep 197201 = 147901) B147901
theorem B131667 : Blo 127788 131667 := bstep (se 1 (by rfl) ⟨98750, by rfl⟩ : syracuseStep 131667 = 197501) B197501
theorem B295523 : Blo 127788 295523 := bstep (se 1 (by rfl) ⟨221642, by rfl⟩ : syracuseStep 295523 = 443285) B443285
theorem B197219 : Blo 127788 197219 := bstep (se 1 (by rfl) ⟨147914, by rfl⟩ : syracuseStep 197219 = 295829) B295829
theorem B131683 : Blo 127788 131683 := bstep (se 1 (by rfl) ⟨98762, by rfl⟩ : syracuseStep 131683 = 197525) B197525
theorem B131699 : Blo 127788 131699 := bstep (se 1 (by rfl) ⟨98774, by rfl⟩ : syracuseStep 131699 = 197549) B197549
theorem B197249 : Blo 127788 197249 := bstep (se 2 (by rfl) ⟨73968, by rfl⟩ : syracuseStep 197249 = 147937) B147937
theorem B131715 : Blo 127788 131715 := bstep (se 1 (by rfl) ⟨98786, by rfl⟩ : syracuseStep 131715 = 197573) B197573
theorem B197267 : Blo 127788 197267 := bstep (se 1 (by rfl) ⟨147950, by rfl⟩ : syracuseStep 197267 = 295901) B295901
theorem B131731 : Blo 127788 131731 := bstep (se 1 (by rfl) ⟨98798, by rfl⟩ : syracuseStep 131731 = 197597) B197597
theorem B131747 : Blo 127788 131747 := bstep (se 1 (by rfl) ⟨98810, by rfl⟩ : syracuseStep 131747 = 197621) B197621
theorem B197297 : Blo 127788 197297 := bstep (se 2 (by rfl) ⟨73986, by rfl⟩ : syracuseStep 197297 = 147973) B147973
theorem B164531 : Blo 127788 164531 := bstep (se 1 (by rfl) ⟨123398, by rfl⟩ : syracuseStep 164531 = 246797) B246797
theorem B131763 : Blo 127788 131763 := bstep (se 1 (by rfl) ⟨98822, by rfl⟩ : syracuseStep 131763 = 197645) B197645
theorem B197315 : Blo 127788 197315 := bstep (se 1 (by rfl) ⟨147986, by rfl⟩ : syracuseStep 197315 = 295973) B295973
theorem B131779 : Blo 127788 131779 := bstep (se 1 (by rfl) ⟨98834, by rfl⟩ : syracuseStep 131779 = 197669) B197669
theorem B197345 : Blo 127788 197345 := bstep (se 2 (by rfl) ⟨74004, by rfl⟩ : syracuseStep 197345 = 148009) B148009
theorem B656099 : Blo 127788 656099 := bstep (se 1 (by rfl) ⟨492074, by rfl⟩ : syracuseStep 656099 = 984149) B984149
theorem B197363 : Blo 127788 197363 := bstep (se 1 (by rfl) ⟨148022, by rfl⟩ : syracuseStep 197363 = 296045) B296045
theorem B197393 : Blo 127788 197393 := bstep (se 2 (by rfl) ⟨74022, by rfl⟩ : syracuseStep 197393 = 148045) B148045
theorem B197411 : Blo 127788 197411 := bstep (se 1 (by rfl) ⟨148058, by rfl⟩ : syracuseStep 197411 = 296117) B296117
theorem B197441 : Blo 127788 197441 := bstep (se 2 (by rfl) ⟨74040, by rfl⟩ : syracuseStep 197441 = 148081) B148081
theorem B197459 : Blo 127788 197459 := bstep (se 1 (by rfl) ⟨148094, by rfl⟩ : syracuseStep 197459 = 296189) B296189
theorem B1016675 : Blo 127788 1016675 := bstep (se 1 (by rfl) ⟨762506, by rfl⟩ : syracuseStep 1016675 = 1525013) B1525013
theorem B295793 : Blo 127788 295793 := bstep (se 2 (by rfl) ⟨110922, by rfl⟩ : syracuseStep 295793 = 221845) B221845
theorem B197489 : Blo 127788 197489 := bstep (se 2 (by rfl) ⟨74058, by rfl⟩ : syracuseStep 197489 = 148117) B148117
theorem B295811 : Blo 127788 295811 := bstep (se 1 (by rfl) ⟨221858, by rfl⟩ : syracuseStep 295811 = 443717) B443717
theorem B197507 : Blo 127788 197507 := bstep (se 1 (by rfl) ⟨148130, by rfl⟩ : syracuseStep 197507 = 296261) B296261
theorem B197537 : Blo 127788 197537 := bstep (se 2 (by rfl) ⟨74076, by rfl⟩ : syracuseStep 197537 = 148153) B148153
theorem B197555 : Blo 127788 197555 := bstep (se 1 (by rfl) ⟨148166, by rfl⟩ : syracuseStep 197555 = 296333) B296333
theorem B328657 : Blo 127788 328657 := bstep (se 2 (by rfl) ⟨123246, by rfl⟩ : syracuseStep 328657 = 246493) B246493
theorem B197585 : Blo 127788 197585 := bstep (se 2 (by rfl) ⟨74094, by rfl⟩ : syracuseStep 197585 = 148189) B148189
theorem B197603 : Blo 127788 197603 := bstep (se 1 (by rfl) ⟨148202, by rfl⟩ : syracuseStep 197603 = 296405) B296405
theorem B197633 : Blo 127788 197633 := bstep (se 2 (by rfl) ⟨74112, by rfl⟩ : syracuseStep 197633 = 148225) B148225
theorem B623629 : Blo 127788 623629 := bstep (se 3 (by rfl) ⟨116930, by rfl⟩ : syracuseStep 623629 = 233861) B233861
theorem B197651 : Blo 127788 197651 := bstep (se 1 (by rfl) ⟨148238, by rfl⟩ : syracuseStep 197651 = 296477) B296477
theorem B197681 : Blo 127788 197681 := bstep (se 2 (by rfl) ⟨74130, by rfl⟩ : syracuseStep 197681 = 148261) B148261
theorem B263299 : Blo 127788 263299 := bstep (se 1 (by rfl) ⟨197474, by rfl⟩ : syracuseStep 263299 = 394949) B394949
theorem B230545 : Blo 127788 230545 := bstep (se 2 (by rfl) ⟨86454, by rfl⟩ : syracuseStep 230545 = 172909) B172909
theorem B296081 : Blo 127788 296081 := bstep (se 2 (by rfl) ⟨111030, by rfl⟩ : syracuseStep 296081 = 222061) B222061
theorem B296099 : Blo 127788 296099 := bstep (se 1 (by rfl) ⟨222074, by rfl⟩ : syracuseStep 296099 = 444149) B444149
theorem B722117 : Blo 127788 722117 := bstep (se 4 (by rfl) ⟨67698, by rfl⟩ : syracuseStep 722117 = 135397) B135397
theorem B328931 : Blo 127788 328931 := bstep (se 1 (by rfl) ⟨246698, by rfl⟩ : syracuseStep 328931 = 493397) B493397
theorem B197905 : Blo 127788 197905 := bstep (se 2 (by rfl) ⟨74214, by rfl⟩ : syracuseStep 197905 = 148429) B148429
theorem B886085 : Blo 127788 886085 := bstep (se 4 (by rfl) ⟨83070, by rfl⟩ : syracuseStep 886085 = 166141) B166141
theorem B165235 : Blo 127788 165235 := bstep (se 1 (by rfl) ⟨123926, by rfl⟩ : syracuseStep 165235 = 247853) B247853
theorem B329123 : Blo 127788 329123 := bstep (se 1 (by rfl) ⟨246842, by rfl⟩ : syracuseStep 329123 = 493685) B493685
theorem B296369 : Blo 127788 296369 := bstep (se 2 (by rfl) ⟨111138, by rfl⟩ : syracuseStep 296369 = 222277) B222277
theorem B296387 : Blo 127788 296387 := bstep (se 1 (by rfl) ⟨222290, by rfl⟩ : syracuseStep 296387 = 444581) B444581
theorem B165331 : Blo 127788 165331 := bstep (se 1 (by rfl) ⟨123998, by rfl⟩ : syracuseStep 165331 = 247997) B247997
theorem B656909 : Blo 127788 656909 := bstep (se 3 (by rfl) ⟨123170, by rfl⟩ : syracuseStep 656909 = 246341) B246341
theorem B493411 : Blo 127788 493411 := bstep (se 1 (by rfl) ⟨370058, by rfl⟩ : syracuseStep 493411 = 740117) B740117
theorem B264035 : Blo 127788 264035 := bstep (se 1 (by rfl) ⟨198026, by rfl⟩ : syracuseStep 264035 = 396053) B396053
theorem B165827 : Blo 127788 165827 := bstep (se 1 (by rfl) ⟨124370, by rfl⟩ : syracuseStep 165827 = 248741) B248741
theorem B526513 : Blo 127788 526513 := bstep (se 2 (by rfl) ⟨197442, by rfl⟩ : syracuseStep 526513 = 394885) B394885
theorem B330065 : Blo 127788 330065 := bstep (se 2 (by rfl) ⟨123774, by rfl⟩ : syracuseStep 330065 = 247549) B247549
theorem B330115 : Blo 127788 330115 := bstep (se 1 (by rfl) ⟨247586, by rfl⟩ : syracuseStep 330115 = 495173) B495173
theorem B821765 : Blo 127788 821765 := bstep (se 4 (by rfl) ⟨77040, by rfl⟩ : syracuseStep 821765 = 154081) B154081
theorem B330257 : Blo 127788 330257 := bstep (se 2 (by rfl) ⟨123846, by rfl⟩ : syracuseStep 330257 = 247693) B247693
theorem B395857 : Blo 127788 395857 := bstep (se 2 (by rfl) ⟨148446, by rfl⟩ : syracuseStep 395857 = 296893) B296893
theorem B166531 : Blo 127788 166531 := bstep (se 1 (by rfl) ⟨124898, by rfl⟩ : syracuseStep 166531 = 249797) B249797
theorem B395981 : Blo 127788 395981 := bstep (se 3 (by rfl) ⟨74246, by rfl⟩ : syracuseStep 395981 = 148493) B148493
theorem B166627 : Blo 127788 166627 := bstep (se 1 (by rfl) ⟨124970, by rfl⟩ : syracuseStep 166627 = 249941) B249941
theorem B756869 : Blo 127788 756869 := bstep (se 4 (by rfl) ⟨70956, by rfl⟩ : syracuseStep 756869 = 141913) B141913
theorem B167203 : Blo 127788 167203 := bstep (se 1 (by rfl) ⟨125402, by rfl⟩ : syracuseStep 167203 = 250805) B250805
theorem B363953 : Blo 127788 363953 := bstep (se 2 (by rfl) ⟨136482, by rfl⟩ : syracuseStep 363953 = 272965) B272965
theorem B331249 : Blo 127788 331249 := bstep (se 2 (by rfl) ⟨124218, by rfl⟩ : syracuseStep 331249 = 248437) B248437
theorem B658979 : Blo 127788 658979 := bstep (se 1 (by rfl) ⟨494234, by rfl⟩ : syracuseStep 658979 = 988469) B988469
theorem B691811 : Blo 127788 691811 := bstep (se 1 (by rfl) ⟨518858, by rfl⟩ : syracuseStep 691811 = 1037717) B1037717
theorem B790157 : Blo 127788 790157 := bstep (se 3 (by rfl) ⟨148154, by rfl⟩ : syracuseStep 790157 = 296309) B296309
theorem B233155 : Blo 127788 233155 := bstep (se 1 (by rfl) ⟨174866, by rfl⟩ : syracuseStep 233155 = 349733) B349733
theorem B331523 : Blo 127788 331523 := bstep (se 1 (by rfl) ⟨248642, by rfl⟩ : syracuseStep 331523 = 497285) B497285
theorem B593677 : Blo 127788 593677 := bstep (se 3 (by rfl) ⟨111314, by rfl⟩ : syracuseStep 593677 = 222629) B222629
theorem B331715 : Blo 127788 331715 := bstep (se 1 (by rfl) ⟨248786, by rfl⟩ : syracuseStep 331715 = 497573) B497573
theorem B495629 : Blo 127788 495629 := bstep (se 3 (by rfl) ⟨92930, by rfl⟩ : syracuseStep 495629 = 185861) B185861
theorem B233617 : Blo 127788 233617 := bstep (se 2 (by rfl) ⟨87606, by rfl⟩ : syracuseStep 233617 = 175213) B175213
theorem B659825 : Blo 127788 659825 := bstep (se 2 (by rfl) ⟨247434, by rfl⟩ : syracuseStep 659825 = 494869) B494869
theorem B364945 : Blo 127788 364945 := bstep (se 2 (by rfl) ⟨136854, by rfl⟩ : syracuseStep 364945 = 273709) B273709
theorem B823715 : Blo 127788 823715 := bstep (se 1 (by rfl) ⟨617786, by rfl⟩ : syracuseStep 823715 = 1235573) B1235573
theorem B561649 : Blo 127788 561649 := bstep (se 2 (by rfl) ⟨210618, by rfl⟩ : syracuseStep 561649 = 421237) B421237
theorem B365219 : Blo 127788 365219 := bstep (se 1 (by rfl) ⟨273914, by rfl⟩ : syracuseStep 365219 = 547829) B547829
theorem B627533 : Blo 127788 627533 := bstep (se 3 (by rfl) ⟨117662, by rfl⟩ : syracuseStep 627533 = 235325) B235325
theorem B365411 : Blo 127788 365411 := bstep (se 1 (by rfl) ⟨274058, by rfl⟩ : syracuseStep 365411 = 548117) B548117
theorem B332657 : Blo 127788 332657 := bstep (se 2 (by rfl) ⟨124746, by rfl⟩ : syracuseStep 332657 = 249493) B249493
theorem B332707 : Blo 127788 332707 := bstep (se 1 (by rfl) ⟨249530, by rfl⟩ : syracuseStep 332707 = 499061) B499061
theorem B693197 : Blo 127788 693197 := bstep (se 3 (by rfl) ⟨129974, by rfl⟩ : syracuseStep 693197 = 259949) B259949
theorem B332849 : Blo 127788 332849 := bstep (se 2 (by rfl) ⟨124818, by rfl⟩ : syracuseStep 332849 = 249637) B249637
theorem B2823281 : Blo 127788 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B431405 : Blo 127788 431405 := bstep (se 3 (by rfl) ⟨80888, by rfl⟩ : syracuseStep 431405 = 161777) B161777
theorem B431459 : Blo 127788 431459 := bstep (se 1 (by rfl) ⟨323594, by rfl⟩ : syracuseStep 431459 = 647189) B647189
theorem B1578467 : Blo 127788 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B136739 : Blo 127788 136739 := bstep (se 1 (by rfl) ⟨102554, by rfl⟩ : syracuseStep 136739 = 205109) B205109
theorem B431729 : Blo 127788 431729 := bstep (se 2 (by rfl) ⟨161898, by rfl⟩ : syracuseStep 431729 = 323797) B323797
theorem B366221 : Blo 127788 366221 := bstep (se 3 (by rfl) ⟨68666, by rfl⟩ : syracuseStep 366221 = 137333) B137333
theorem B235217 : Blo 127788 235217 := bstep (se 2 (by rfl) ⟨88206, by rfl⟩ : syracuseStep 235217 = 176413) B176413
theorem B661283 : Blo 127788 661283 := bstep (se 1 (by rfl) ⟨495962, by rfl⟩ : syracuseStep 661283 = 991925) B991925
theorem B366403 : Blo 127788 366403 := bstep (se 1 (by rfl) ⟨274802, by rfl⟩ : syracuseStep 366403 = 549605) B549605
theorem B432269 : Blo 127788 432269 := bstep (se 3 (by rfl) ⟨81050, by rfl⟩ : syracuseStep 432269 = 162101) B162101
theorem B432323 : Blo 127788 432323 := bstep (se 1 (by rfl) ⟨324242, by rfl⟩ : syracuseStep 432323 = 648485) B648485
theorem B366893 : Blo 127788 366893 := bstep (se 3 (by rfl) ⟨68792, by rfl⟩ : syracuseStep 366893 = 137585) B137585
theorem B432593 : Blo 127788 432593 := bstep (se 2 (by rfl) ⟨162222, by rfl⟩ : syracuseStep 432593 = 324445) B324445
theorem B137747 : Blo 127788 137747 := bstep (se 1 (by rfl) ⟨103310, by rfl⟩ : syracuseStep 137747 = 206621) B206621
theorem B236081 : Blo 127788 236081 := bstep (se 2 (by rfl) ⟨88530, by rfl⟩ : syracuseStep 236081 = 177061) B177061
theorem B1120837 : Blo 127788 1120837 := bstep (se 4 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 1120837 = 210157) B210157
theorem B662093 : Blo 127788 662093 := bstep (se 3 (by rfl) ⟨124142, by rfl⟩ : syracuseStep 662093 = 248285) B248285
theorem B694925 : Blo 127788 694925 := bstep (se 3 (by rfl) ⟨130298, by rfl⟩ : syracuseStep 694925 = 260597) B260597
theorem B465763 : Blo 127788 465763 := bstep (se 1 (by rfl) ⟨349322, by rfl⟩ : syracuseStep 465763 = 698645) B698645
theorem B498545 : Blo 127788 498545 := bstep (se 2 (by rfl) ⟨186954, by rfl⟩ : syracuseStep 498545 = 373909) B373909
theorem B433133 : Blo 127788 433133 := bstep (se 3 (by rfl) ⟨81212, by rfl⟩ : syracuseStep 433133 = 162425) B162425
theorem B433187 : Blo 127788 433187 := bstep (se 1 (by rfl) ⟨324890, by rfl⟩ : syracuseStep 433187 = 649781) B649781
theorem B269443 : Blo 127788 269443 := bstep (se 1 (by rfl) ⟨202082, by rfl⟩ : syracuseStep 269443 = 404165) B404165
theorem B433457 : Blo 127788 433457 := bstep (se 2 (by rfl) ⟨162546, by rfl⟩ : syracuseStep 433457 = 325093) B325093
theorem B728453 : Blo 127788 728453 := bstep (se 4 (by rfl) ⟨68292, by rfl⟩ : syracuseStep 728453 = 136585) B136585
theorem B368077 : Blo 127788 368077 := bstep (se 3 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 368077 = 138029) B138029
theorem B302915 : Blo 127788 302915 := bstep (se 1 (by rfl) ⟨227186, by rfl⟩ : syracuseStep 302915 = 454373) B454373
theorem B728909 : Blo 127788 728909 := bstep (se 3 (by rfl) ⟨136670, by rfl⟩ : syracuseStep 728909 = 273341) B273341
theorem B433997 : Blo 127788 433997 := bstep (se 3 (by rfl) ⟨81374, by rfl⟩ : syracuseStep 433997 = 162749) B162749
theorem B434051 : Blo 127788 434051 := bstep (se 1 (by rfl) ⟨325538, by rfl⟩ : syracuseStep 434051 = 651077) B651077
theorem B827405 : Blo 127788 827405 := bstep (se 3 (by rfl) ⟨155138, by rfl⟩ : syracuseStep 827405 = 310277) B310277
theorem B139315 : Blo 127788 139315 := bstep (se 1 (by rfl) ⟨104486, by rfl⟩ : syracuseStep 139315 = 208973) B208973
theorem B1450037 : Blo 127788 1450037 := bstep (se 5 (by rfl) ⟨67970, by rfl⟩ : syracuseStep 1450037 = 135941) B135941
theorem B237667 : Blo 127788 237667 := bstep (se 1 (by rfl) ⟨178250, by rfl⟩ : syracuseStep 237667 = 356501) B356501
theorem B434321 : Blo 127788 434321 := bstep (se 2 (by rfl) ⟨162870, by rfl⟩ : syracuseStep 434321 = 325741) B325741
theorem B500003 : Blo 127788 500003 := bstep (se 1 (by rfl) ⟨375002, by rfl⟩ : syracuseStep 500003 = 750005) B750005
theorem B369137 : Blo 127788 369137 := bstep (se 2 (by rfl) ⟨138426, by rfl⟩ : syracuseStep 369137 = 276853) B276853
theorem B139763 : Blo 127788 139763 := bstep (se 1 (by rfl) ⟨104822, by rfl⟩ : syracuseStep 139763 = 209645) B209645
theorem B3875381 : Blo 127788 3875381 := bstep (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) B363317
theorem B434861 : Blo 127788 434861 := bstep (se 3 (by rfl) ⟨81536, by rfl⟩ : syracuseStep 434861 = 163073) B163073
theorem B434915 : Blo 127788 434915 := bstep (se 1 (by rfl) ⟨326186, by rfl⟩ : syracuseStep 434915 = 652373) B652373
theorem B566129 : Blo 127788 566129 := bstep (se 2 (by rfl) ⟨212298, by rfl⟩ : syracuseStep 566129 = 424597) B424597
theorem B435185 : Blo 127788 435185 := bstep (se 2 (by rfl) ⟨163194, by rfl⟩ : syracuseStep 435185 = 326389) B326389
theorem B304163 : Blo 127788 304163 := bstep (se 1 (by rfl) ⟨228122, by rfl⟩ : syracuseStep 304163 = 456245) B456245
theorem B369809 : Blo 127788 369809 := bstep (se 2 (by rfl) ⟨138678, by rfl⟩ : syracuseStep 369809 = 277357) B277357
theorem B369937 : Blo 127788 369937 := bstep (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) B277453
theorem B665009 : Blo 127788 665009 := bstep (se 2 (by rfl) ⟨249378, by rfl⟩ : syracuseStep 665009 = 498757) B498757
theorem B435725 : Blo 127788 435725 := bstep (se 3 (by rfl) ⟨81698, by rfl⟩ : syracuseStep 435725 = 163397) B163397
theorem B435779 : Blo 127788 435779 := bstep (se 1 (by rfl) ⟨326834, by rfl⟩ : syracuseStep 435779 = 653669) B653669
theorem B436049 : Blo 127788 436049 := bstep (se 2 (by rfl) ⟨163518, by rfl⟩ : syracuseStep 436049 = 327037) B327037
theorem B239473 : Blo 127788 239473 := bstep (se 2 (by rfl) ⟨89802, by rfl⟩ : syracuseStep 239473 = 179605) B179605
theorem B206723 : Blo 127788 206723 := bstep (se 1 (by rfl) ⟨155042, by rfl⟩ : syracuseStep 206723 = 310085) B310085
theorem B370595 : Blo 127788 370595 := bstep (se 1 (by rfl) ⟨277946, by rfl⟩ : syracuseStep 370595 = 555893) B555893
theorem B370925 : Blo 127788 370925 := bstep (se 3 (by rfl) ⟨69548, by rfl⟩ : syracuseStep 370925 = 139097) B139097
theorem B370993 : Blo 127788 370993 := bstep (se 2 (by rfl) ⟨139122, by rfl⟩ : syracuseStep 370993 = 278245) B278245
theorem B436589 : Blo 127788 436589 := bstep (se 3 (by rfl) ⟨81860, by rfl⟩ : syracuseStep 436589 = 163721) B163721
theorem B436643 : Blo 127788 436643 := bstep (se 1 (by rfl) ⟨327482, by rfl⟩ : syracuseStep 436643 = 654965) B654965
theorem B371267 : Blo 127788 371267 := bstep (se 1 (by rfl) ⟨278450, by rfl⟩ : syracuseStep 371267 = 556901) B556901
theorem B174721 : Blo 127788 174721 := bstep (se 2 (by rfl) ⟨65520, by rfl⟩ : syracuseStep 174721 = 131041) B131041
theorem B731825 : Blo 127788 731825 := bstep (se 2 (by rfl) ⟨274434, by rfl⟩ : syracuseStep 731825 = 548869) B548869
theorem B436913 : Blo 127788 436913 := bstep (se 2 (by rfl) ⟨163842, by rfl⟩ : syracuseStep 436913 = 327685) B327685
theorem B207569 : Blo 127788 207569 := bstep (se 2 (by rfl) ⟨77838, by rfl⟩ : syracuseStep 207569 = 155677) B155677
theorem B174899 : Blo 127788 174899 := bstep (se 1 (by rfl) ⟨131174, by rfl⟩ : syracuseStep 174899 = 262349) B262349
theorem B666467 : Blo 127788 666467 := bstep (se 1 (by rfl) ⟨499850, by rfl⟩ : syracuseStep 666467 = 999701) B999701
theorem B174961 : Blo 127788 174961 := bstep (se 2 (by rfl) ⟨65610, by rfl⟩ : syracuseStep 174961 = 131221) B131221
theorem B338897 : Blo 127788 338897 := bstep (se 2 (by rfl) ⟨127086, by rfl⟩ : syracuseStep 338897 = 254173) B254173
theorem B437453 : Blo 127788 437453 := bstep (se 3 (by rfl) ⟨82022, by rfl⟩ : syracuseStep 437453 = 164045) B164045
theorem B175331 : Blo 127788 175331 := bstep (se 1 (by rfl) ⟨131498, by rfl⟩ : syracuseStep 175331 = 262997) B262997
theorem B437507 : Blo 127788 437507 := bstep (se 1 (by rfl) ⟨328130, by rfl⟩ : syracuseStep 437507 = 656261) B656261
theorem B372109 : Blo 127788 372109 := bstep (se 3 (by rfl) ⟨69770, by rfl⟩ : syracuseStep 372109 = 139541) B139541
theorem B208307 : Blo 127788 208307 := bstep (se 1 (by rfl) ⟨156230, by rfl⟩ : syracuseStep 208307 = 312461) B312461
theorem B437777 : Blo 127788 437777 := bstep (se 2 (by rfl) ⟨164166, by rfl⟩ : syracuseStep 437777 = 328333) B328333
theorem B372269 : Blo 127788 372269 := bstep (se 3 (by rfl) ⟨69800, by rfl⟩ : syracuseStep 372269 = 139601) B139601
theorem B929393 : Blo 127788 929393 := bstep (se 2 (by rfl) ⟨348522, by rfl⟩ : syracuseStep 929393 = 697045) B697045
theorem B667277 : Blo 127788 667277 := bstep (se 3 (by rfl) ⟨125114, by rfl⟩ : syracuseStep 667277 = 250229) B250229
theorem B372451 : Blo 127788 372451 := bstep (se 1 (by rfl) ⟨279338, by rfl⟩ : syracuseStep 372451 = 558677) B558677
theorem B438317 : Blo 127788 438317 := bstep (se 3 (by rfl) ⟨82184, by rfl⟩ : syracuseStep 438317 = 164369) B164369
theorem B733283 : Blo 127788 733283 := bstep (se 1 (by rfl) ⟨549962, by rfl⟩ : syracuseStep 733283 = 1099925) B1099925
theorem B438371 : Blo 127788 438371 := bstep (se 1 (by rfl) ⟨328778, by rfl⟩ : syracuseStep 438371 = 657557) B657557
theorem B209123 : Blo 127788 209123 := bstep (se 1 (by rfl) ⟨156842, by rfl⟩ : syracuseStep 209123 = 313685) B313685
theorem B274691 : Blo 127788 274691 := bstep (se 1 (by rfl) ⟨206018, by rfl⟩ : syracuseStep 274691 = 412037) B412037
theorem B438641 : Blo 127788 438641 := bstep (se 2 (by rfl) ⟨164490, by rfl⟩ : syracuseStep 438641 = 328981) B328981
theorem B209299 : Blo 127788 209299 := bstep (se 1 (by rfl) ⟨156974, by rfl⟩ : syracuseStep 209299 = 313949) B313949
theorem B143779 : Blo 127788 143779 := bstep (se 1 (by rfl) ⟨107834, by rfl⟩ : syracuseStep 143779 = 215669) B215669
theorem B438691 : Blo 127788 438691 := bstep (se 1 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 438691 = 658037) B658037
theorem B143923 : Blo 127788 143923 := bstep (se 1 (by rfl) ⟨107942, by rfl⟩ : syracuseStep 143923 = 215885) B215885
theorem B209537 : Blo 127788 209537 := bstep (se 2 (by rfl) ⟨78576, by rfl⟩ : syracuseStep 209537 = 157153) B157153
theorem B144067 : Blo 127788 144067 := bstep (se 1 (by rfl) ⟨108050, by rfl⟩ : syracuseStep 144067 = 216101) B216101
theorem B1651427 : Blo 127788 1651427 := bstep (se 1 (by rfl) ⟨1238570, by rfl⟩ : syracuseStep 1651427 = 2477141) B2477141
theorem B144211 : Blo 127788 144211 := bstep (se 1 (by rfl) ⟨108158, by rfl⟩ : syracuseStep 144211 = 216317) B216317
theorem B209747 : Blo 127788 209747 := bstep (se 1 (by rfl) ⟨157310, by rfl⟩ : syracuseStep 209747 = 314621) B314621
theorem B897905 : Blo 127788 897905 := bstep (se 2 (by rfl) ⟨336714, by rfl⟩ : syracuseStep 897905 = 673429) B673429
theorem B439181 : Blo 127788 439181 := bstep (se 3 (by rfl) ⟨82346, by rfl⟩ : syracuseStep 439181 = 164693) B164693
theorem B439235 : Blo 127788 439235 := bstep (se 1 (by rfl) ⟨329426, by rfl⟩ : syracuseStep 439235 = 658853) B658853
theorem B144355 : Blo 127788 144355 := bstep (se 1 (by rfl) ⟨108266, by rfl⟩ : syracuseStep 144355 = 216533) B216533
theorem B734285 : Blo 127788 734285 := bstep (se 3 (by rfl) ⟨137678, by rfl⟩ : syracuseStep 734285 = 275357) B275357
theorem B373841 : Blo 127788 373841 := bstep (se 2 (by rfl) ⟨140190, by rfl⟩ : syracuseStep 373841 = 280381) B280381
theorem B275555 : Blo 127788 275555 := bstep (se 1 (by rfl) ⟨206666, by rfl⟩ : syracuseStep 275555 = 413333) B413333
theorem B144499 : Blo 127788 144499 := bstep (se 1 (by rfl) ⟨108374, by rfl⟩ : syracuseStep 144499 = 216749) B216749
theorem B439427 : Blo 127788 439427 := bstep (se 1 (by rfl) ⟨329570, by rfl⟩ : syracuseStep 439427 = 659141) B659141
theorem B701581 : Blo 127788 701581 := bstep (se 3 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 701581 = 263093) B263093
theorem B242833 : Blo 127788 242833 := bstep (se 2 (by rfl) ⟨91062, by rfl⟩ : syracuseStep 242833 = 182125) B182125
theorem B275665 : Blo 127788 275665 := bstep (se 2 (by rfl) ⟨103374, by rfl⟩ : syracuseStep 275665 = 206749) B206749
theorem B439505 : Blo 127788 439505 := bstep (se 2 (by rfl) ⟨164814, by rfl⟩ : syracuseStep 439505 = 329629) B329629
theorem B144643 : Blo 127788 144643 := bstep (se 1 (by rfl) ⟨108482, by rfl⟩ : syracuseStep 144643 = 216965) B216965
theorem B242993 : Blo 127788 242993 := bstep (se 2 (by rfl) ⟨91122, by rfl⟩ : syracuseStep 242993 = 182245) B182245
theorem B832837 : Blo 127788 832837 := bstep (se 4 (by rfl) ⟨78078, by rfl⟩ : syracuseStep 832837 = 156157) B156157
theorem B144787 : Blo 127788 144787 := bstep (se 1 (by rfl) ⟨108590, by rfl⟩ : syracuseStep 144787 = 217181) B217181
theorem B144931 : Blo 127788 144931 := bstep (se 1 (by rfl) ⟨108698, by rfl⟩ : syracuseStep 144931 = 217397) B217397
theorem B472625 : Blo 127788 472625 := bstep (se 2 (by rfl) ⟨177234, by rfl⟩ : syracuseStep 472625 = 354469) B354469
theorem B210529 : Blo 127788 210529 := bstep (se 2 (by rfl) ⟨78948, by rfl⟩ : syracuseStep 210529 = 157897) B157897
theorem B669325 : Blo 127788 669325 := bstep (se 3 (by rfl) ⟨125498, by rfl⟩ : syracuseStep 669325 = 250997) B250997
theorem B145075 : Blo 127788 145075 := bstep (se 1 (by rfl) ⟨108806, by rfl⟩ : syracuseStep 145075 = 217613) B217613
theorem B243395 : Blo 127788 243395 := bstep (se 1 (by rfl) ⟨182546, by rfl⟩ : syracuseStep 243395 = 365093) B365093
theorem B440045 : Blo 127788 440045 := bstep (se 3 (by rfl) ⟨82508, by rfl⟩ : syracuseStep 440045 = 165017) B165017
theorem B440099 : Blo 127788 440099 := bstep (se 1 (by rfl) ⟨330074, by rfl⟩ : syracuseStep 440099 = 660149) B660149
theorem B145219 : Blo 127788 145219 := bstep (se 1 (by rfl) ⟨108914, by rfl⟩ : syracuseStep 145219 = 217829) B217829
theorem B210785 : Blo 127788 210785 := bstep (se 2 (by rfl) ⟨79044, by rfl⟩ : syracuseStep 210785 = 158089) B158089
theorem B145363 : Blo 127788 145363 := bstep (se 1 (by rfl) ⟨109022, by rfl⟩ : syracuseStep 145363 = 218045) B218045
theorem B374797 : Blo 127788 374797 := bstep (se 3 (by rfl) ⟨70274, by rfl⟩ : syracuseStep 374797 = 140549) B140549
theorem B440369 : Blo 127788 440369 := bstep (se 2 (by rfl) ⟨165138, by rfl⟩ : syracuseStep 440369 = 330277) B330277
theorem B145507 : Blo 127788 145507 := bstep (se 1 (by rfl) ⟨109130, by rfl⟩ : syracuseStep 145507 = 218261) B218261
theorem B375025 : Blo 127788 375025 := bstep (se 2 (by rfl) ⟨140634, by rfl⟩ : syracuseStep 375025 = 281269) B281269
theorem B145651 : Blo 127788 145651 := bstep (se 1 (by rfl) ⟨109238, by rfl⟩ : syracuseStep 145651 = 218477) B218477
theorem B145795 : Blo 127788 145795 := bstep (se 1 (by rfl) ⟨109346, by rfl⟩ : syracuseStep 145795 = 218693) B218693
theorem B375185 : Blo 127788 375185 := bstep (se 2 (by rfl) ⟨140694, by rfl⟩ : syracuseStep 375185 = 281389) B281389
theorem B145939 : Blo 127788 145939 := bstep (se 1 (by rfl) ⟨109454, by rfl⟩ : syracuseStep 145939 = 218909) B218909
theorem B244291 : Blo 127788 244291 := bstep (se 1 (by rfl) ⟨183218, by rfl⟩ : syracuseStep 244291 = 366437) B366437
theorem B440909 : Blo 127788 440909 := bstep (se 3 (by rfl) ⟨82670, by rfl⟩ : syracuseStep 440909 = 165341) B165341
theorem B342641 : Blo 127788 342641 := bstep (se 2 (by rfl) ⟨128490, by rfl⟩ : syracuseStep 342641 = 256981) B256981
theorem B440963 : Blo 127788 440963 := bstep (se 1 (by rfl) ⟨330722, by rfl⟩ : syracuseStep 440963 = 661445) B661445
theorem B146083 : Blo 127788 146083 := bstep (se 1 (by rfl) ⟨109562, by rfl⟩ : syracuseStep 146083 = 219125) B219125
theorem B244451 : Blo 127788 244451 := bstep (se 1 (by rfl) ⟨183338, by rfl⟩ : syracuseStep 244451 = 366677) B366677
theorem B146227 : Blo 127788 146227 := bstep (se 1 (by rfl) ⟨109670, by rfl⟩ : syracuseStep 146227 = 219341) B219341
theorem B998243 : Blo 127788 998243 := bstep (se 1 (by rfl) ⟨748682, by rfl⟩ : syracuseStep 998243 = 1497365) B1497365
theorem B1063793 : Blo 127788 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B441233 : Blo 127788 441233 := bstep (se 2 (by rfl) ⟨165462, by rfl⟩ : syracuseStep 441233 = 330925) B330925
theorem B146371 : Blo 127788 146371 := bstep (se 1 (by rfl) ⟨109778, by rfl⟩ : syracuseStep 146371 = 219557) B219557
theorem B146515 : Blo 127788 146515 := bstep (se 1 (by rfl) ⟨109886, by rfl⟩ : syracuseStep 146515 = 219773) B219773
theorem B277681 : Blo 127788 277681 := bstep (se 2 (by rfl) ⟨104130, by rfl⟩ : syracuseStep 277681 = 208261) B208261
theorem B146659 : Blo 127788 146659 := bstep (se 1 (by rfl) ⟨109994, by rfl⟩ : syracuseStep 146659 = 219989) B219989
theorem B146803 : Blo 127788 146803 := bstep (se 1 (by rfl) ⟨110102, by rfl⟩ : syracuseStep 146803 = 220205) B220205
theorem B310691 : Blo 127788 310691 := bstep (se 1 (by rfl) ⟨233018, by rfl⟩ : syracuseStep 310691 = 466037) B466037
theorem B441773 : Blo 127788 441773 := bstep (se 3 (by rfl) ⟨82832, by rfl⟩ : syracuseStep 441773 = 165665) B165665
theorem B474545 : Blo 127788 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B441827 : Blo 127788 441827 := bstep (se 1 (by rfl) ⟨331370, by rfl⟩ : syracuseStep 441827 = 662741) B662741
theorem B146947 : Blo 127788 146947 := bstep (se 1 (by rfl) ⟨110210, by rfl⟩ : syracuseStep 146947 = 220421) B220421
theorem B278083 : Blo 127788 278083 := bstep (se 1 (by rfl) ⟨208562, by rfl⟩ : syracuseStep 278083 = 417125) B417125
theorem B147091 : Blo 127788 147091 := bstep (se 1 (by rfl) ⟨110318, by rfl⟩ : syracuseStep 147091 = 220637) B220637
theorem B442097 : Blo 127788 442097 := bstep (se 2 (by rfl) ⟨165786, by rfl⟩ : syracuseStep 442097 = 331573) B331573
theorem B376589 : Blo 127788 376589 := bstep (se 3 (by rfl) ⟨70610, by rfl⟩ : syracuseStep 376589 = 141221) B141221
theorem B245521 : Blo 127788 245521 := bstep (se 2 (by rfl) ⟨92070, by rfl⟩ : syracuseStep 245521 = 184141) B184141
theorem B147235 : Blo 127788 147235 := bstep (se 1 (by rfl) ⟨110426, by rfl⟩ : syracuseStep 147235 = 220853) B220853
theorem B409475 : Blo 127788 409475 := bstep (se 1 (by rfl) ⟨307106, by rfl⟩ : syracuseStep 409475 = 614213) B614213
theorem B212897 : Blo 127788 212897 := bstep (se 2 (by rfl) ⟨79836, by rfl⟩ : syracuseStep 212897 = 159673) B159673
theorem B737201 : Blo 127788 737201 := bstep (se 2 (by rfl) ⟨276450, by rfl⟩ : syracuseStep 737201 = 552901) B552901
theorem B147379 : Blo 127788 147379 := bstep (se 1 (by rfl) ⟨110534, by rfl⟩ : syracuseStep 147379 = 221069) B221069
theorem B835555 : Blo 127788 835555 := bstep (se 1 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 835555 = 1253333) B1253333
theorem B147523 : Blo 127788 147523 := bstep (se 1 (by rfl) ⟨110642, by rfl⟩ : syracuseStep 147523 = 221285) B221285
theorem B147667 : Blo 127788 147667 := bstep (se 1 (by rfl) ⟨110750, by rfl⟩ : syracuseStep 147667 = 221501) B221501
theorem B442637 : Blo 127788 442637 := bstep (se 3 (by rfl) ⟨82994, by rfl⟩ : syracuseStep 442637 = 165989) B165989
theorem B442691 : Blo 127788 442691 := bstep (se 1 (by rfl) ⟨332018, by rfl⟩ : syracuseStep 442691 = 664037) B664037
theorem B147811 : Blo 127788 147811 := bstep (se 1 (by rfl) ⟨110858, by rfl⟩ : syracuseStep 147811 = 221717) B221717
theorem B147955 : Blo 127788 147955 := bstep (se 1 (by rfl) ⟨110966, by rfl⟩ : syracuseStep 147955 = 221933) B221933
theorem B442961 : Blo 127788 442961 := bstep (se 2 (by rfl) ⟨166110, by rfl⟩ : syracuseStep 442961 = 332221) B332221
theorem B148099 : Blo 127788 148099 := bstep (se 1 (by rfl) ⟨111074, by rfl⟩ : syracuseStep 148099 = 222149) B222149
theorem B705293 : Blo 127788 705293 := bstep (se 3 (by rfl) ⟨132242, by rfl⟩ : syracuseStep 705293 = 264485) B264485
theorem B148243 : Blo 127788 148243 := bstep (se 1 (by rfl) ⟨111182, by rfl⟩ : syracuseStep 148243 = 222365) B222365
theorem B246577 : Blo 127788 246577 := bstep (se 2 (by rfl) ⟨92466, by rfl⟩ : syracuseStep 246577 = 184933) B184933
theorem B213857 : Blo 127788 213857 := bstep (se 2 (by rfl) ⟨80196, by rfl⟩ : syracuseStep 213857 = 160393) B160393
theorem B148483 : Blo 127788 148483 := bstep (se 1 (by rfl) ⟨111362, by rfl⟩ : syracuseStep 148483 = 222725) B222725
theorem B279587 : Blo 127788 279587 := bstep (se 1 (by rfl) ⟨209690, by rfl⟩ : syracuseStep 279587 = 419381) B419381
theorem B443501 : Blo 127788 443501 := bstep (se 3 (by rfl) ⟨83156, by rfl⟩ : syracuseStep 443501 = 166313) B166313
theorem B443555 : Blo 127788 443555 := bstep (se 1 (by rfl) ⟨332666, by rfl⟩ : syracuseStep 443555 = 665333) B665333
theorem B246979 : Blo 127788 246979 := bstep (se 1 (by rfl) ⟨185234, by rfl⟩ : syracuseStep 246979 = 370469) B370469
theorem B1262789 : Blo 127788 1262789 := bstep (se 4 (by rfl) ⟨118386, by rfl⟩ : syracuseStep 1262789 = 236773) B236773
theorem B247025 : Blo 127788 247025 := bstep (se 2 (by rfl) ⟨92634, by rfl⟩ : syracuseStep 247025 = 185269) B185269
theorem B279811 : Blo 127788 279811 := bstep (se 1 (by rfl) ⟨209858, by rfl⟩ : syracuseStep 279811 = 419717) B419717
theorem B738659 : Blo 127788 738659 := bstep (se 1 (by rfl) ⟨553994, by rfl⟩ : syracuseStep 738659 = 1107989) B1107989
theorem B443825 : Blo 127788 443825 := bstep (se 2 (by rfl) ⟨166434, by rfl⟩ : syracuseStep 443825 = 332869) B332869
theorem B2377187 : Blo 127788 2377187 := bstep (se 1 (by rfl) ⟨1782890, by rfl⟩ : syracuseStep 2377187 = 3565781) B3565781
theorem B247313 : Blo 127788 247313 := bstep (se 2 (by rfl) ⟨92742, by rfl⟩ : syracuseStep 247313 = 185485) B185485
theorem B182017 : Blo 127788 182017 := bstep (se 2 (by rfl) ⟨68256, by rfl⟩ : syracuseStep 182017 = 136513) B136513
theorem B837553 : Blo 127788 837553 := bstep (se 2 (by rfl) ⟨314082, by rfl⟩ : syracuseStep 837553 = 628165) B628165
theorem B444365 : Blo 127788 444365 := bstep (se 3 (by rfl) ⟨83318, by rfl⟩ : syracuseStep 444365 = 166637) B166637
theorem B411601 : Blo 127788 411601 := bstep (se 2 (by rfl) ⟨154350, by rfl⟩ : syracuseStep 411601 = 308701) B308701
theorem B444419 : Blo 127788 444419 := bstep (se 1 (by rfl) ⟨333314, by rfl⟩ : syracuseStep 444419 = 666629) B666629
theorem B182353 : Blo 127788 182353 := bstep (se 2 (by rfl) ⟨68382, by rfl⟩ : syracuseStep 182353 = 136765) B136765
theorem B280675 : Blo 127788 280675 := bstep (se 1 (by rfl) ⟨210506, by rfl⟩ : syracuseStep 280675 = 421013) B421013
theorem B248035 : Blo 127788 248035 := bstep (se 1 (by rfl) ⟨186026, by rfl⟩ : syracuseStep 248035 = 372053) B372053
theorem B280817 : Blo 127788 280817 := bstep (se 2 (by rfl) ⟨105306, by rfl⟩ : syracuseStep 280817 = 210613) B210613
theorem B444689 : Blo 127788 444689 := bstep (se 2 (by rfl) ⟨166758, by rfl⟩ : syracuseStep 444689 = 333517) B333517
theorem B215347 : Blo 127788 215347 := bstep (se 1 (by rfl) ⟨161510, by rfl⟩ : syracuseStep 215347 = 323021) B323021
theorem B149843 : Blo 127788 149843 := bstep (se 1 (by rfl) ⟨112382, by rfl⟩ : syracuseStep 149843 = 224765) B224765
theorem B215473 : Blo 127788 215473 := bstep (se 2 (by rfl) ⟨80802, by rfl⟩ : syracuseStep 215473 = 161605) B161605
theorem B477731 : Blo 127788 477731 := bstep (se 1 (by rfl) ⟨358298, by rfl⟩ : syracuseStep 477731 = 716597) B716597
theorem B248465 : Blo 127788 248465 := bstep (se 2 (by rfl) ⟨93174, by rfl⟩ : syracuseStep 248465 = 186349) B186349
theorem B182945 : Blo 127788 182945 := bstep (se 2 (by rfl) ⟨68604, by rfl⟩ : syracuseStep 182945 = 137209) B137209
theorem B248483 : Blo 127788 248483 := bstep (se 1 (by rfl) ⟨186362, by rfl⟩ : syracuseStep 248483 = 372725) B372725
theorem B445123 : Blo 127788 445123 := bstep (se 1 (by rfl) ⟨333842, by rfl⟩ : syracuseStep 445123 = 667685) B667685
theorem B215777 : Blo 127788 215777 := bstep (se 2 (by rfl) ⟨80916, by rfl⟩ : syracuseStep 215777 = 161833) B161833
theorem B215905 : Blo 127788 215905 := bstep (se 2 (by rfl) ⟨80964, by rfl⟩ : syracuseStep 215905 = 161929) B161929
theorem B215939 : Blo 127788 215939 := bstep (se 1 (by rfl) ⟨161954, by rfl⟩ : syracuseStep 215939 = 323909) B323909
theorem B314275 : Blo 127788 314275 := bstep (se 1 (by rfl) ⟨235706, by rfl⟩ : syracuseStep 314275 = 471413) B471413
theorem B281539 : Blo 127788 281539 := bstep (se 1 (by rfl) ⟨211154, by rfl⟩ : syracuseStep 281539 = 422309) B422309
theorem B248771 : Blo 127788 248771 := bstep (se 1 (by rfl) ⟨186578, by rfl⟩ : syracuseStep 248771 = 373157) B373157
theorem B216067 : Blo 127788 216067 := bstep (se 1 (by rfl) ⟨162050, by rfl⟩ : syracuseStep 216067 = 324101) B324101
theorem B216209 : Blo 127788 216209 := bstep (se 2 (by rfl) ⟨81078, by rfl⟩ : syracuseStep 216209 = 162157) B162157
theorem B183475 : Blo 127788 183475 := bstep (se 1 (by rfl) ⟨137606, by rfl⟩ : syracuseStep 183475 = 275213) B275213
theorem B216337 : Blo 127788 216337 := bstep (se 2 (by rfl) ⟨81126, by rfl⟩ : syracuseStep 216337 = 162253) B162253
theorem B216371 : Blo 127788 216371 := bstep (se 1 (by rfl) ⟨162278, by rfl⟩ : syracuseStep 216371 = 324557) B324557
theorem B511331 : Blo 127788 511331 := bstep (se 1 (by rfl) ⟨383498, by rfl⟩ : syracuseStep 511331 = 766997) B766997
theorem B216499 : Blo 127788 216499 := bstep (se 1 (by rfl) ⟨162374, by rfl⟩ : syracuseStep 216499 = 324749) B324749
theorem B183811 : Blo 127788 183811 := bstep (se 1 (by rfl) ⟨137858, by rfl⟩ : syracuseStep 183811 = 275717) B275717
theorem B216641 : Blo 127788 216641 := bstep (se 2 (by rfl) ⟨81240, by rfl⟩ : syracuseStep 216641 = 162481) B162481
theorem B216769 : Blo 127788 216769 := bstep (se 2 (by rfl) ⟨81288, by rfl⟩ : syracuseStep 216769 = 162577) B162577
theorem B216803 : Blo 127788 216803 := bstep (se 1 (by rfl) ⟨162602, by rfl⟩ : syracuseStep 216803 = 325205) B325205
theorem B347939 : Blo 127788 347939 := bstep (se 1 (by rfl) ⟨260954, by rfl⟩ : syracuseStep 347939 = 521909) B521909
theorem B216931 : Blo 127788 216931 := bstep (se 1 (by rfl) ⟨162698, by rfl⟩ : syracuseStep 216931 = 325397) B325397
theorem B413549 : Blo 127788 413549 := bstep (se 3 (by rfl) ⟨77540, by rfl⟩ : syracuseStep 413549 = 155081) B155081
theorem B249713 : Blo 127788 249713 := bstep (se 2 (by rfl) ⟨93642, by rfl⟩ : syracuseStep 249713 = 187285) B187285
theorem B446435 : Blo 127788 446435 := bstep (se 1 (by rfl) ⟨334826, by rfl⟩ : syracuseStep 446435 = 669653) B669653
theorem B413677 : Blo 127788 413677 := bstep (se 3 (by rfl) ⟨77564, by rfl⟩ : syracuseStep 413677 = 155129) B155129
theorem B217073 : Blo 127788 217073 := bstep (se 2 (by rfl) ⟨81402, by rfl⟩ : syracuseStep 217073 = 162805) B162805
theorem B184369 : Blo 127788 184369 := bstep (se 2 (by rfl) ⟨69138, by rfl⟩ : syracuseStep 184369 = 138277) B138277
theorem B184403 : Blo 127788 184403 := bstep (se 1 (by rfl) ⟨138302, by rfl⟩ : syracuseStep 184403 = 276605) B276605
theorem B217201 : Blo 127788 217201 := bstep (se 2 (by rfl) ⟨81450, by rfl⟩ : syracuseStep 217201 = 162901) B162901
theorem B315505 : Blo 127788 315505 := bstep (se 2 (by rfl) ⟨118314, by rfl⟩ : syracuseStep 315505 = 236629) B236629
theorem B217235 : Blo 127788 217235 := bstep (se 1 (by rfl) ⟨162926, by rfl⟩ : syracuseStep 217235 = 325853) B325853
theorem B217363 : Blo 127788 217363 := bstep (se 1 (by rfl) ⟨163022, by rfl⟩ : syracuseStep 217363 = 326045) B326045
theorem B217505 : Blo 127788 217505 := bstep (se 2 (by rfl) ⟨81564, by rfl⟩ : syracuseStep 217505 = 163129) B163129
theorem B1036741 : Blo 127788 1036741 := bstep (se 4 (by rfl) ⟨97194, by rfl⟩ : syracuseStep 1036741 = 194389) B194389
theorem B17125829 : Blo 127788 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B217633 : Blo 127788 217633 := bstep (se 2 (by rfl) ⟨81612, by rfl⟩ : syracuseStep 217633 = 163225) B163225
theorem B217667 : Blo 127788 217667 := bstep (se 1 (by rfl) ⟨163250, by rfl⟩ : syracuseStep 217667 = 326501) B326501
theorem B184961 : Blo 127788 184961 := bstep (se 2 (by rfl) ⟨69360, by rfl⟩ : syracuseStep 184961 = 138721) B138721
theorem B1168013 : Blo 127788 1168013 := bstep (se 3 (by rfl) ⟨219002, by rfl⟩ : syracuseStep 1168013 = 438005) B438005
theorem B217795 : Blo 127788 217795 := bstep (se 1 (by rfl) ⟨163346, by rfl⟩ : syracuseStep 217795 = 326693) B326693
theorem B185041 : Blo 127788 185041 := bstep (se 2 (by rfl) ⟨69390, by rfl⟩ : syracuseStep 185041 = 138781) B138781
theorem B217937 : Blo 127788 217937 := bstep (se 2 (by rfl) ⟨81726, by rfl⟩ : syracuseStep 217937 = 163453) B163453
theorem B1495907 : Blo 127788 1495907 := bstep (se 1 (by rfl) ⟨1121930, by rfl⟩ : syracuseStep 1495907 = 2243861) B2243861
theorem B349105 : Blo 127788 349105 := bstep (se 2 (by rfl) ⟨130914, by rfl⟩ : syracuseStep 349105 = 261829) B261829
theorem B218065 : Blo 127788 218065 := bstep (se 2 (by rfl) ⟨81774, by rfl⟩ : syracuseStep 218065 = 163549) B163549
theorem B218099 : Blo 127788 218099 := bstep (se 1 (by rfl) ⟨163574, by rfl⟩ : syracuseStep 218099 = 327149) B327149
theorem B218227 : Blo 127788 218227 := bstep (se 1 (by rfl) ⟨163670, by rfl⟩ : syracuseStep 218227 = 327341) B327341
theorem B218369 : Blo 127788 218369 := bstep (se 2 (by rfl) ⟨81888, by rfl⟩ : syracuseStep 218369 = 163777) B163777
theorem B218497 : Blo 127788 218497 := bstep (se 2 (by rfl) ⟨81936, by rfl⟩ : syracuseStep 218497 = 163873) B163873
theorem B218531 : Blo 127788 218531 := bstep (se 1 (by rfl) ⟨163898, by rfl⟩ : syracuseStep 218531 = 327797) B327797
theorem B185827 : Blo 127788 185827 := bstep (se 1 (by rfl) ⟨139370, by rfl⟩ : syracuseStep 185827 = 278741) B278741
theorem B218659 : Blo 127788 218659 := bstep (se 1 (by rfl) ⟨163994, by rfl⟩ : syracuseStep 218659 = 327989) B327989
theorem B284305 : Blo 127788 284305 := bstep (se 2 (by rfl) ⟨106614, by rfl⟩ : syracuseStep 284305 = 213229) B213229
theorem B218801 : Blo 127788 218801 := bstep (se 2 (by rfl) ⟨82050, by rfl⟩ : syracuseStep 218801 = 164101) B164101
theorem B972485 : Blo 127788 972485 := bstep (se 4 (by rfl) ⟨91170, by rfl⟩ : syracuseStep 972485 = 182341) B182341
theorem B415523 : Blo 127788 415523 := bstep (se 1 (by rfl) ⟨311642, by rfl⟩ : syracuseStep 415523 = 623285) B623285
theorem B907057 : Blo 127788 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B218929 : Blo 127788 218929 := bstep (se 2 (by rfl) ⟨82098, by rfl⟩ : syracuseStep 218929 = 164197) B164197
theorem B218963 : Blo 127788 218963 := bstep (se 1 (by rfl) ⟨164222, by rfl⟩ : syracuseStep 218963 = 328445) B328445
theorem B2119537 : Blo 127788 2119537 := bstep (se 2 (by rfl) ⟨794826, by rfl⟩ : syracuseStep 2119537 = 1589653) B1589653
theorem B415651 : Blo 127788 415651 := bstep (se 1 (by rfl) ⟨311738, by rfl⟩ : syracuseStep 415651 = 623477) B623477
theorem B186305 : Blo 127788 186305 := bstep (se 2 (by rfl) ⟨69864, by rfl⟩ : syracuseStep 186305 = 139729) B139729
theorem B219091 : Blo 127788 219091 := bstep (se 1 (by rfl) ⟨164318, by rfl⟩ : syracuseStep 219091 = 328637) B328637
theorem B219107 : Blo 127788 219107 := bstep (se 1 (by rfl) ⟨164330, by rfl⟩ : syracuseStep 219107 = 328661) B328661
theorem B415793 : Blo 127788 415793 := bstep (se 2 (by rfl) ⟨155922, by rfl⟩ : syracuseStep 415793 = 311845) B311845
theorem B186419 : Blo 127788 186419 := bstep (se 1 (by rfl) ⟨139814, by rfl⟩ : syracuseStep 186419 = 279629) B279629
theorem B1169477 : Blo 127788 1169477 := bstep (se 4 (by rfl) ⟨109638, by rfl⟩ : syracuseStep 1169477 = 219277) B219277
theorem B219233 : Blo 127788 219233 := bstep (se 2 (by rfl) ⟨82212, by rfl⟩ : syracuseStep 219233 = 164425) B164425
theorem B186499 : Blo 127788 186499 := bstep (se 1 (by rfl) ⟨139874, by rfl⟩ : syracuseStep 186499 = 279749) B279749
theorem B415907 : Blo 127788 415907 := bstep (se 1 (by rfl) ⟨311930, by rfl⟩ : syracuseStep 415907 = 623861) B623861
theorem B219361 : Blo 127788 219361 := bstep (se 2 (by rfl) ⟨82260, by rfl⟩ : syracuseStep 219361 = 164521) B164521
theorem B219395 : Blo 127788 219395 := bstep (se 1 (by rfl) ⟨164546, by rfl⟩ : syracuseStep 219395 = 329093) B329093
theorem B711011 : Blo 127788 711011 := bstep (se 1 (by rfl) ⟨533258, by rfl⟩ : syracuseStep 711011 = 1066517) B1066517
theorem B219523 : Blo 127788 219523 := bstep (se 1 (by rfl) ⟨164642, by rfl⟩ : syracuseStep 219523 = 329285) B329285
theorem B219665 : Blo 127788 219665 := bstep (se 2 (by rfl) ⟨82374, by rfl⟩ : syracuseStep 219665 = 164749) B164749
theorem B186931 : Blo 127788 186931 := bstep (se 1 (by rfl) ⟨140198, by rfl⟩ : syracuseStep 186931 = 280397) B280397
theorem B547469 : Blo 127788 547469 := bstep (se 3 (by rfl) ⟨102650, by rfl⟩ : syracuseStep 547469 = 205301) B205301
theorem B219793 : Blo 127788 219793 := bstep (se 2 (by rfl) ⟨82422, by rfl⟩ : syracuseStep 219793 = 164845) B164845
theorem B187057 : Blo 127788 187057 := bstep (se 2 (by rfl) ⟨70146, by rfl⟩ : syracuseStep 187057 = 140293) B140293
theorem B219827 : Blo 127788 219827 := bstep (se 1 (by rfl) ⟨164870, by rfl⟩ : syracuseStep 219827 = 329741) B329741
theorem B219955 : Blo 127788 219955 := bstep (se 1 (by rfl) ⟨164966, by rfl⟩ : syracuseStep 219955 = 329933) B329933
theorem B220097 : Blo 127788 220097 := bstep (se 2 (by rfl) ⟨82536, by rfl⟩ : syracuseStep 220097 = 165073) B165073
theorem B744497 : Blo 127788 744497 := bstep (se 2 (by rfl) ⟨279186, by rfl⟩ : syracuseStep 744497 = 558373) B558373
theorem B220225 : Blo 127788 220225 := bstep (se 2 (by rfl) ⟨82584, by rfl⟩ : syracuseStep 220225 = 165169) B165169
theorem B220259 : Blo 127788 220259 := bstep (se 1 (by rfl) ⟨165194, by rfl⟩ : syracuseStep 220259 = 330389) B330389
theorem B842885 : Blo 127788 842885 := bstep (se 4 (by rfl) ⟨79020, by rfl⟩ : syracuseStep 842885 = 158041) B158041
theorem B875717 : Blo 127788 875717 := bstep (se 4 (by rfl) ⟨82098, by rfl⟩ : syracuseStep 875717 = 164197) B164197
theorem B220387 : Blo 127788 220387 := bstep (se 1 (by rfl) ⟨165290, by rfl⟩ : syracuseStep 220387 = 330581) B330581
theorem B875789 : Blo 127788 875789 := bstep (se 3 (by rfl) ⟨164210, by rfl⟩ : syracuseStep 875789 = 328421) B328421
theorem B220529 : Blo 127788 220529 := bstep (se 2 (by rfl) ⟨82698, by rfl⟩ : syracuseStep 220529 = 165397) B165397
theorem B220657 : Blo 127788 220657 := bstep (se 2 (by rfl) ⟨82746, by rfl⟩ : syracuseStep 220657 = 165493) B165493
theorem B220691 : Blo 127788 220691 := bstep (se 1 (by rfl) ⟨165518, by rfl⟩ : syracuseStep 220691 = 331037) B331037
theorem B450157 : Blo 127788 450157 := bstep (se 3 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 450157 = 168809) B168809
theorem B220819 : Blo 127788 220819 := bstep (se 1 (by rfl) ⟨165614, by rfl⟩ : syracuseStep 220819 = 331229) B331229
theorem B220961 : Blo 127788 220961 := bstep (se 2 (by rfl) ⟨82860, by rfl⟩ : syracuseStep 220961 = 165721) B165721
theorem B417649 : Blo 127788 417649 := bstep (se 2 (by rfl) ⟨156618, by rfl⟩ : syracuseStep 417649 = 313237) B313237
theorem B221089 : Blo 127788 221089 := bstep (se 2 (by rfl) ⟨82908, by rfl⟩ : syracuseStep 221089 = 165817) B165817
theorem B221123 : Blo 127788 221123 := bstep (se 1 (by rfl) ⟨165842, by rfl⟩ : syracuseStep 221123 = 331685) B331685
theorem B221251 : Blo 127788 221251 := bstep (se 1 (by rfl) ⟨165938, by rfl⟩ : syracuseStep 221251 = 331877) B331877
theorem B221393 : Blo 127788 221393 := bstep (se 2 (by rfl) ⟨83022, by rfl⟩ : syracuseStep 221393 = 166045) B166045
theorem B221521 : Blo 127788 221521 := bstep (se 2 (by rfl) ⟨83070, by rfl⟩ : syracuseStep 221521 = 166141) B166141
theorem B221555 : Blo 127788 221555 := bstep (se 1 (by rfl) ⟨166166, by rfl⟩ : syracuseStep 221555 = 332333) B332333
theorem B221683 : Blo 127788 221683 := bstep (se 1 (by rfl) ⟨166262, by rfl⟩ : syracuseStep 221683 = 332525) B332525
theorem B221795 : Blo 127788 221795 := bstep (se 1 (by rfl) ⟨166346, by rfl⟩ : syracuseStep 221795 = 332693) B332693
theorem B221825 : Blo 127788 221825 := bstep (se 2 (by rfl) ⟨83184, by rfl⟩ : syracuseStep 221825 = 166369) B166369
theorem B221843 : Blo 127788 221843 := bstep (se 1 (by rfl) ⟨166382, by rfl⟩ : syracuseStep 221843 = 332765) B332765
theorem B221953 : Blo 127788 221953 := bstep (se 2 (by rfl) ⟨83232, by rfl⟩ : syracuseStep 221953 = 166465) B166465
theorem B221987 : Blo 127788 221987 := bstep (se 1 (by rfl) ⟨166490, by rfl⟩ : syracuseStep 221987 = 332981) B332981
theorem B222115 : Blo 127788 222115 := bstep (se 1 (by rfl) ⟨166586, by rfl⟩ : syracuseStep 222115 = 333173) B333173
theorem B418765 : Blo 127788 418765 := bstep (se 3 (by rfl) ⟨78518, by rfl⟩ : syracuseStep 418765 = 157037) B157037
theorem B287729 : Blo 127788 287729 := bstep (se 2 (by rfl) ⟨107898, by rfl⟩ : syracuseStep 287729 = 215797) B215797
theorem B287747 : Blo 127788 287747 := bstep (se 1 (by rfl) ⟨215810, by rfl⟩ : syracuseStep 287747 = 431621) B431621
theorem B156691 : Blo 127788 156691 := bstep (se 1 (by rfl) ⟨117518, by rfl⟩ : syracuseStep 156691 = 235037) B235037
theorem B222257 : Blo 127788 222257 := bstep (se 2 (by rfl) ⟨83346, by rfl⟩ : syracuseStep 222257 = 166693) B166693
theorem B222353 : Blo 127788 222353 := bstep (se 2 (by rfl) ⟨83382, by rfl⟩ : syracuseStep 222353 = 166765) B166765
theorem B222385 : Blo 127788 222385 := bstep (se 2 (by rfl) ⟨83394, by rfl⟩ : syracuseStep 222385 = 166789) B166789
theorem B288017 : Blo 127788 288017 := bstep (se 2 (by rfl) ⟨108006, by rfl⟩ : syracuseStep 288017 = 216013) B216013
theorem B288035 : Blo 127788 288035 := bstep (se 1 (by rfl) ⟨216026, by rfl⟩ : syracuseStep 288035 = 432053) B432053
theorem B2876725 : Blo 127788 2876725 := bstep (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) B269693
theorem B288305 : Blo 127788 288305 := bstep (se 2 (by rfl) ⟨108114, by rfl⟩ : syracuseStep 288305 = 216229) B216229
theorem B288323 : Blo 127788 288323 := bstep (se 1 (by rfl) ⟨216242, by rfl⟩ : syracuseStep 288323 = 432485) B432485
theorem B550577 : Blo 127788 550577 := bstep (se 2 (by rfl) ⟨206466, by rfl⟩ : syracuseStep 550577 = 412933) B412933
theorem B419597 : Blo 127788 419597 := bstep (se 3 (by rfl) ⟨78674, by rfl⟩ : syracuseStep 419597 = 157349) B157349
theorem B288593 : Blo 127788 288593 := bstep (se 2 (by rfl) ⟨108222, by rfl⟩ : syracuseStep 288593 = 216445) B216445
theorem B288611 : Blo 127788 288611 := bstep (se 1 (by rfl) ⟨216458, by rfl⟩ : syracuseStep 288611 = 432917) B432917
theorem B780209 : Blo 127788 780209 := bstep (se 2 (by rfl) ⟨292578, by rfl⟩ : syracuseStep 780209 = 585157) B585157
theorem B354253 : Blo 127788 354253 := bstep (se 3 (by rfl) ⟨66422, by rfl⟩ : syracuseStep 354253 = 132845) B132845
theorem B747589 : Blo 127788 747589 := bstep (se 4 (by rfl) ⟨70086, by rfl⟩ : syracuseStep 747589 = 140173) B140173
theorem B485453 : Blo 127788 485453 := bstep (se 3 (by rfl) ⟨91022, by rfl⟩ : syracuseStep 485453 = 182045) B182045
theorem B288881 : Blo 127788 288881 := bstep (se 2 (by rfl) ⟨108330, by rfl⟩ : syracuseStep 288881 = 216661) B216661
theorem B288899 : Blo 127788 288899 := bstep (se 1 (by rfl) ⟨216674, by rfl⟩ : syracuseStep 288899 = 433349) B433349
theorem B223411 : Blo 127788 223411 := bstep (se 1 (by rfl) ⟨167558, by rfl⟩ : syracuseStep 223411 = 335117) B335117
theorem B649457 : Blo 127788 649457 := bstep (se 2 (by rfl) ⟨243546, by rfl⟩ : syracuseStep 649457 = 487093) B487093
theorem B354545 : Blo 127788 354545 := bstep (se 2 (by rfl) ⟨132954, by rfl⟩ : syracuseStep 354545 = 265909) B265909
theorem B354577 : Blo 127788 354577 := bstep (se 2 (by rfl) ⟨132966, by rfl⟩ : syracuseStep 354577 = 265933) B265933
theorem B551245 : Blo 127788 551245 := bstep (se 3 (by rfl) ⟨103358, by rfl⟩ : syracuseStep 551245 = 206717) B206717
theorem B158051 : Blo 127788 158051 := bstep (se 1 (by rfl) ⟨118538, by rfl⟩ : syracuseStep 158051 = 237077) B237077
theorem B289169 : Blo 127788 289169 := bstep (se 2 (by rfl) ⟨108438, by rfl⟩ : syracuseStep 289169 = 216877) B216877
theorem B289187 : Blo 127788 289187 := bstep (se 1 (by rfl) ⟨216890, by rfl⟩ : syracuseStep 289187 = 433781) B433781
theorem B1993187 : Blo 127788 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B289457 : Blo 127788 289457 := bstep (se 2 (by rfl) ⟨108546, by rfl⟩ : syracuseStep 289457 = 217093) B217093
theorem B289475 : Blo 127788 289475 := bstep (se 1 (by rfl) ⟨217106, by rfl⟩ : syracuseStep 289475 = 434213) B434213
theorem B551843 : Blo 127788 551843 := bstep (se 1 (by rfl) ⟨413882, by rfl⟩ : syracuseStep 551843 = 827765) B827765
theorem B420785 : Blo 127788 420785 := bstep (se 2 (by rfl) ⟨157794, by rfl⟩ : syracuseStep 420785 = 315589) B315589
theorem B289745 : Blo 127788 289745 := bstep (se 2 (by rfl) ⟨108654, by rfl⟩ : syracuseStep 289745 = 217309) B217309
theorem B289763 : Blo 127788 289763 := bstep (se 1 (by rfl) ⟨217322, by rfl⟩ : syracuseStep 289763 = 434645) B434645
theorem B191699 : Blo 127788 191699 := bstep (se 1 (by rfl) ⟨143774, by rfl⟩ : syracuseStep 191699 = 287549) B287549
theorem B191729 : Blo 127788 191729 := bstep (se 2 (by rfl) ⟨71898, by rfl⟩ : syracuseStep 191729 = 143797) B143797
theorem B519409 : Blo 127788 519409 := bstep (se 2 (by rfl) ⟨194778, by rfl⟩ : syracuseStep 519409 = 389557) B389557
theorem B290033 : Blo 127788 290033 := bstep (se 2 (by rfl) ⟨108762, by rfl⟩ : syracuseStep 290033 = 217525) B217525
theorem B191747 : Blo 127788 191747 := bstep (se 1 (by rfl) ⟨143810, by rfl⟩ : syracuseStep 191747 = 287621) B287621
theorem B290051 : Blo 127788 290051 := bstep (se 1 (by rfl) ⟨217538, by rfl⟩ : syracuseStep 290051 = 435077) B435077
theorem B191777 : Blo 127788 191777 := bstep (se 2 (by rfl) ⟨71916, by rfl⟩ : syracuseStep 191777 = 143833) B143833
theorem B191795 : Blo 127788 191795 := bstep (se 1 (by rfl) ⟨143846, by rfl⟩ : syracuseStep 191795 = 287693) B287693
theorem B191825 : Blo 127788 191825 := bstep (se 2 (by rfl) ⟨71934, by rfl⟩ : syracuseStep 191825 = 143869) B143869
theorem B191843 : Blo 127788 191843 := bstep (se 1 (by rfl) ⟨143882, by rfl⟩ : syracuseStep 191843 = 287765) B287765
theorem B191873 : Blo 127788 191873 := bstep (se 2 (by rfl) ⟨71952, by rfl⟩ : syracuseStep 191873 = 143905) B143905
theorem B978317 : Blo 127788 978317 := bstep (se 3 (by rfl) ⟨183434, by rfl⟩ : syracuseStep 978317 = 366869) B366869
theorem B191891 : Blo 127788 191891 := bstep (se 1 (by rfl) ⟨143918, by rfl⟩ : syracuseStep 191891 = 287837) B287837
theorem B191921 : Blo 127788 191921 := bstep (se 2 (by rfl) ⟨71970, by rfl⟩ : syracuseStep 191921 = 143941) B143941
theorem B224689 : Blo 127788 224689 := bstep (se 2 (by rfl) ⟨84258, by rfl⟩ : syracuseStep 224689 = 168517) B168517
theorem B191939 : Blo 127788 191939 := bstep (se 1 (by rfl) ⟨143954, by rfl⟩ : syracuseStep 191939 = 287909) B287909
theorem B191969 : Blo 127788 191969 := bstep (se 2 (by rfl) ⟨71988, by rfl⟩ : syracuseStep 191969 = 143977) B143977
theorem B191987 : Blo 127788 191987 := bstep (se 1 (by rfl) ⟨143990, by rfl⟩ : syracuseStep 191987 = 287981) B287981
theorem B192017 : Blo 127788 192017 := bstep (se 2 (by rfl) ⟨72006, by rfl⟩ : syracuseStep 192017 = 144013) B144013
theorem B290321 : Blo 127788 290321 := bstep (se 2 (by rfl) ⟨108870, by rfl⟩ : syracuseStep 290321 = 217741) B217741
theorem B192035 : Blo 127788 192035 := bstep (se 1 (by rfl) ⟨144026, by rfl⟩ : syracuseStep 192035 = 288053) B288053
theorem B585251 : Blo 127788 585251 := bstep (se 1 (by rfl) ⟨438938, by rfl⟩ : syracuseStep 585251 = 877877) B877877
theorem B290339 : Blo 127788 290339 := bstep (se 1 (by rfl) ⟨217754, by rfl⟩ : syracuseStep 290339 = 435509) B435509
theorem B192065 : Blo 127788 192065 := bstep (se 2 (by rfl) ⟨72024, by rfl⟩ : syracuseStep 192065 = 144049) B144049
theorem B192083 : Blo 127788 192083 := bstep (se 1 (by rfl) ⟨144062, by rfl⟩ : syracuseStep 192083 = 288125) B288125
theorem B192113 : Blo 127788 192113 := bstep (se 2 (by rfl) ⟨72042, by rfl⟩ : syracuseStep 192113 = 144085) B144085
theorem B192131 : Blo 127788 192131 := bstep (se 1 (by rfl) ⟨144098, by rfl⟩ : syracuseStep 192131 = 288197) B288197
theorem B192161 : Blo 127788 192161 := bstep (se 2 (by rfl) ⟨72060, by rfl⟩ : syracuseStep 192161 = 144121) B144121
theorem B650915 : Blo 127788 650915 := bstep (se 1 (by rfl) ⟨488186, by rfl⟩ : syracuseStep 650915 = 976373) B976373
theorem B192179 : Blo 127788 192179 := bstep (se 1 (by rfl) ⟨144134, by rfl⟩ : syracuseStep 192179 = 288269) B288269
theorem B192209 : Blo 127788 192209 := bstep (se 2 (by rfl) ⟨72078, by rfl⟩ : syracuseStep 192209 = 144157) B144157
theorem B192227 : Blo 127788 192227 := bstep (se 1 (by rfl) ⟨144170, by rfl⟩ : syracuseStep 192227 = 288341) B288341
theorem B192257 : Blo 127788 192257 := bstep (se 2 (by rfl) ⟨72096, by rfl⟩ : syracuseStep 192257 = 144193) B144193
theorem B192275 : Blo 127788 192275 := bstep (se 1 (by rfl) ⟨144206, by rfl⟩ : syracuseStep 192275 = 288413) B288413
theorem B192305 : Blo 127788 192305 := bstep (se 2 (by rfl) ⟨72114, by rfl⟩ : syracuseStep 192305 = 144229) B144229
theorem B290609 : Blo 127788 290609 := bstep (se 2 (by rfl) ⟨108978, by rfl⟩ : syracuseStep 290609 = 217957) B217957
theorem B192323 : Blo 127788 192323 := bstep (se 1 (by rfl) ⟨144242, by rfl⟩ : syracuseStep 192323 = 288485) B288485
theorem B290627 : Blo 127788 290627 := bstep (se 1 (by rfl) ⟨217970, by rfl⟩ : syracuseStep 290627 = 435941) B435941
theorem B421699 : Blo 127788 421699 := bstep (se 1 (by rfl) ⟨316274, by rfl⟩ : syracuseStep 421699 = 632549) B632549
theorem B192353 : Blo 127788 192353 := bstep (se 2 (by rfl) ⟨72132, by rfl⟩ : syracuseStep 192353 = 144265) B144265
theorem B192371 : Blo 127788 192371 := bstep (se 1 (by rfl) ⟨144278, by rfl⟩ : syracuseStep 192371 = 288557) B288557
theorem B323473 : Blo 127788 323473 := bstep (se 2 (by rfl) ⟨121302, by rfl⟩ : syracuseStep 323473 = 242605) B242605
theorem B192401 : Blo 127788 192401 := bstep (se 2 (by rfl) ⟨72150, by rfl⟩ : syracuseStep 192401 = 144301) B144301
theorem B192419 : Blo 127788 192419 := bstep (se 1 (by rfl) ⟨144314, by rfl⟩ : syracuseStep 192419 = 288629) B288629
theorem B192449 : Blo 127788 192449 := bstep (se 2 (by rfl) ⟨72168, by rfl⟩ : syracuseStep 192449 = 144337) B144337
theorem B421841 : Blo 127788 421841 := bstep (se 2 (by rfl) ⟨158190, by rfl⟩ : syracuseStep 421841 = 316381) B316381
theorem B192467 : Blo 127788 192467 := bstep (se 1 (by rfl) ⟨144350, by rfl⟩ : syracuseStep 192467 = 288701) B288701
theorem B192497 : Blo 127788 192497 := bstep (se 2 (by rfl) ⟨72186, by rfl⟩ : syracuseStep 192497 = 144373) B144373
theorem B192515 : Blo 127788 192515 := bstep (se 1 (by rfl) ⟨144386, by rfl⟩ : syracuseStep 192515 = 288773) B288773
theorem B749573 : Blo 127788 749573 := bstep (se 4 (by rfl) ⟨70272, by rfl⟩ : syracuseStep 749573 = 140545) B140545
theorem B192545 : Blo 127788 192545 := bstep (se 2 (by rfl) ⟨72204, by rfl⟩ : syracuseStep 192545 = 144409) B144409
theorem B192563 : Blo 127788 192563 := bstep (se 1 (by rfl) ⟨144422, by rfl⟩ : syracuseStep 192563 = 288845) B288845
theorem B192593 : Blo 127788 192593 := bstep (se 2 (by rfl) ⟨72222, by rfl⟩ : syracuseStep 192593 = 144445) B144445
theorem B290897 : Blo 127788 290897 := bstep (se 2 (by rfl) ⟨109086, by rfl⟩ : syracuseStep 290897 = 218173) B218173
theorem B192611 : Blo 127788 192611 := bstep (se 1 (by rfl) ⟨144458, by rfl⟩ : syracuseStep 192611 = 288917) B288917
theorem B290915 : Blo 127788 290915 := bstep (se 1 (by rfl) ⟨218186, by rfl⟩ : syracuseStep 290915 = 436373) B436373
theorem B192641 : Blo 127788 192641 := bstep (se 2 (by rfl) ⟨72240, by rfl⟩ : syracuseStep 192641 = 144481) B144481
theorem B487565 : Blo 127788 487565 := bstep (se 3 (by rfl) ⟨91418, by rfl⟩ : syracuseStep 487565 = 182837) B182837
theorem B192659 : Blo 127788 192659 := bstep (se 1 (by rfl) ⟨144494, by rfl⟩ : syracuseStep 192659 = 288989) B288989
theorem B323747 : Blo 127788 323747 := bstep (se 1 (by rfl) ⟨242810, by rfl⟩ : syracuseStep 323747 = 485621) B485621
theorem B192689 : Blo 127788 192689 := bstep (se 2 (by rfl) ⟨72258, by rfl⟩ : syracuseStep 192689 = 144517) B144517
theorem B192707 : Blo 127788 192707 := bstep (se 1 (by rfl) ⟨144530, by rfl⟩ : syracuseStep 192707 = 289061) B289061
theorem B192737 : Blo 127788 192737 := bstep (se 2 (by rfl) ⟨72276, by rfl⟩ : syracuseStep 192737 = 144553) B144553
theorem B946403 : Blo 127788 946403 := bstep (se 1 (by rfl) ⟨709802, by rfl⟩ : syracuseStep 946403 = 1419605) B1419605
theorem B192755 : Blo 127788 192755 := bstep (se 1 (by rfl) ⟨144566, by rfl⟩ : syracuseStep 192755 = 289133) B289133
theorem B192785 : Blo 127788 192785 := bstep (se 2 (by rfl) ⟨72294, by rfl⟩ : syracuseStep 192785 = 144589) B144589
theorem B192803 : Blo 127788 192803 := bstep (se 1 (by rfl) ⟨144602, by rfl⟩ : syracuseStep 192803 = 289205) B289205
theorem B192833 : Blo 127788 192833 := bstep (se 2 (by rfl) ⟨72312, by rfl⟩ : syracuseStep 192833 = 144625) B144625
theorem B192851 : Blo 127788 192851 := bstep (se 1 (by rfl) ⟨144638, by rfl⟩ : syracuseStep 192851 = 289277) B289277
theorem B323939 : Blo 127788 323939 := bstep (se 1 (by rfl) ⟨242954, by rfl⟩ : syracuseStep 323939 = 485909) B485909
theorem B192881 : Blo 127788 192881 := bstep (se 2 (by rfl) ⟨72330, by rfl⟩ : syracuseStep 192881 = 144661) B144661
theorem B291185 : Blo 127788 291185 := bstep (se 2 (by rfl) ⟨109194, by rfl⟩ : syracuseStep 291185 = 218389) B218389
theorem B192899 : Blo 127788 192899 := bstep (se 1 (by rfl) ⟨144674, by rfl⟩ : syracuseStep 192899 = 289349) B289349
theorem B291203 : Blo 127788 291203 := bstep (se 1 (by rfl) ⟨218402, by rfl⟩ : syracuseStep 291203 = 436805) B436805
theorem B192929 : Blo 127788 192929 := bstep (se 2 (by rfl) ⟨72348, by rfl⟩ : syracuseStep 192929 = 144697) B144697
theorem B192947 : Blo 127788 192947 := bstep (se 1 (by rfl) ⟨144710, by rfl⟩ : syracuseStep 192947 = 289421) B289421
theorem B651725 : Blo 127788 651725 := bstep (se 3 (by rfl) ⟨122198, by rfl⟩ : syracuseStep 651725 = 244397) B244397
theorem B192977 : Blo 127788 192977 := bstep (se 2 (by rfl) ⟨72366, by rfl⟩ : syracuseStep 192977 = 144733) B144733
theorem B192995 : Blo 127788 192995 := bstep (se 1 (by rfl) ⟨144746, by rfl⟩ : syracuseStep 192995 = 289493) B289493
theorem B193025 : Blo 127788 193025 := bstep (se 2 (by rfl) ⟨72384, by rfl⟩ : syracuseStep 193025 = 144769) B144769
theorem B193043 : Blo 127788 193043 := bstep (se 1 (by rfl) ⟨144782, by rfl⟩ : syracuseStep 193043 = 289565) B289565
theorem B193073 : Blo 127788 193073 := bstep (se 2 (by rfl) ⟨72402, by rfl⟩ : syracuseStep 193073 = 144805) B144805
theorem B193091 : Blo 127788 193091 := bstep (se 1 (by rfl) ⟨144818, by rfl⟩ : syracuseStep 193091 = 289637) B289637
theorem B193121 : Blo 127788 193121 := bstep (se 2 (by rfl) ⟨72420, by rfl⟩ : syracuseStep 193121 = 144841) B144841
theorem B193139 : Blo 127788 193139 := bstep (se 1 (by rfl) ⟨144854, by rfl⟩ : syracuseStep 193139 = 289709) B289709
theorem B193169 : Blo 127788 193169 := bstep (se 2 (by rfl) ⟨72438, by rfl⟩ : syracuseStep 193169 = 144877) B144877
theorem B291473 : Blo 127788 291473 := bstep (se 2 (by rfl) ⟨109302, by rfl⟩ : syracuseStep 291473 = 218605) B218605
theorem B193187 : Blo 127788 193187 := bstep (se 1 (by rfl) ⟨144890, by rfl⟩ : syracuseStep 193187 = 289781) B289781
theorem B291491 : Blo 127788 291491 := bstep (se 1 (by rfl) ⟨218618, by rfl⟩ : syracuseStep 291491 = 437237) B437237
theorem B193217 : Blo 127788 193217 := bstep (se 2 (by rfl) ⟨72456, by rfl⟩ : syracuseStep 193217 = 144913) B144913
theorem B193235 : Blo 127788 193235 := bstep (se 1 (by rfl) ⟨144926, by rfl⟩ : syracuseStep 193235 = 289853) B289853
theorem B193265 : Blo 127788 193265 := bstep (se 2 (by rfl) ⟨72474, by rfl⟩ : syracuseStep 193265 = 144949) B144949
theorem B193283 : Blo 127788 193283 := bstep (se 1 (by rfl) ⟨144962, by rfl⟩ : syracuseStep 193283 = 289925) B289925
theorem B193313 : Blo 127788 193313 := bstep (se 2 (by rfl) ⟨72492, by rfl⟩ : syracuseStep 193313 = 144985) B144985
theorem B127795 : Blo 127788 127795 := bstep (se 1 (by rfl) ⟨95846, by rfl⟩ : syracuseStep 127795 = 191693) B191693
theorem B193331 : Blo 127788 193331 := bstep (se 1 (by rfl) ⟨144998, by rfl⟩ : syracuseStep 193331 = 289997) B289997
theorem B127811 : Blo 127788 127811 := bstep (se 1 (by rfl) ⟨95858, by rfl⟩ : syracuseStep 127811 = 191717) B191717
theorem B193361 : Blo 127788 193361 := bstep (se 2 (by rfl) ⟨72510, by rfl⟩ : syracuseStep 193361 = 145021) B145021
theorem B127827 : Blo 127788 127827 := bstep (se 1 (by rfl) ⟨95870, by rfl⟩ : syracuseStep 127827 = 191741) B191741
theorem B127843 : Blo 127788 127843 := bstep (se 1 (by rfl) ⟨95882, by rfl⟩ : syracuseStep 127843 = 191765) B191765
theorem B193379 : Blo 127788 193379 := bstep (se 1 (by rfl) ⟨145034, by rfl⟩ : syracuseStep 193379 = 290069) B290069
theorem B127859 : Blo 127788 127859 := bstep (se 1 (by rfl) ⟨95894, by rfl⟩ : syracuseStep 127859 = 191789) B191789
theorem B193409 : Blo 127788 193409 := bstep (se 2 (by rfl) ⟨72528, by rfl⟩ : syracuseStep 193409 = 145057) B145057
theorem B127875 : Blo 127788 127875 := bstep (se 1 (by rfl) ⟨95906, by rfl⟩ : syracuseStep 127875 = 191813) B191813
theorem B127891 : Blo 127788 127891 := bstep (se 1 (by rfl) ⟨95918, by rfl⟩ : syracuseStep 127891 = 191837) B191837
theorem B193427 : Blo 127788 193427 := bstep (se 1 (by rfl) ⟨145070, by rfl⟩ : syracuseStep 193427 = 290141) B290141
theorem B127907 : Blo 127788 127907 := bstep (se 1 (by rfl) ⟨95930, by rfl⟩ : syracuseStep 127907 = 191861) B191861
theorem B488369 : Blo 127788 488369 := bstep (se 2 (by rfl) ⟨183138, by rfl⟩ : syracuseStep 488369 = 366277) B366277
theorem B193457 : Blo 127788 193457 := bstep (se 2 (by rfl) ⟨72546, by rfl⟩ : syracuseStep 193457 = 145093) B145093
theorem B127923 : Blo 127788 127923 := bstep (se 1 (by rfl) ⟨95942, by rfl⟩ : syracuseStep 127923 = 191885) B191885
theorem B291761 : Blo 127788 291761 := bstep (se 2 (by rfl) ⟨109410, by rfl⟩ : syracuseStep 291761 = 218821) B218821
theorem B127939 : Blo 127788 127939 := bstep (se 1 (by rfl) ⟨95954, by rfl⟩ : syracuseStep 127939 = 191909) B191909
theorem B193475 : Blo 127788 193475 := bstep (se 1 (by rfl) ⟨145106, by rfl⟩ : syracuseStep 193475 = 290213) B290213
theorem B291779 : Blo 127788 291779 := bstep (se 1 (by rfl) ⟨218834, by rfl⟩ : syracuseStep 291779 = 437669) B437669
theorem B127955 : Blo 127788 127955 := bstep (se 1 (by rfl) ⟨95966, by rfl⟩ : syracuseStep 127955 = 191933) B191933
theorem B193505 : Blo 127788 193505 := bstep (se 2 (by rfl) ⟨72564, by rfl⟩ : syracuseStep 193505 = 145129) B145129
theorem B127971 : Blo 127788 127971 := bstep (se 1 (by rfl) ⟨95978, by rfl⟩ : syracuseStep 127971 = 191957) B191957
theorem B127987 : Blo 127788 127987 := bstep (se 1 (by rfl) ⟨95990, by rfl⟩ : syracuseStep 127987 = 191981) B191981
theorem B193523 : Blo 127788 193523 := bstep (se 1 (by rfl) ⟨145142, by rfl⟩ : syracuseStep 193523 = 290285) B290285
theorem B128003 : Blo 127788 128003 := bstep (se 1 (by rfl) ⟨96002, by rfl⟩ : syracuseStep 128003 = 192005) B192005
theorem B193553 : Blo 127788 193553 := bstep (se 2 (by rfl) ⟨72582, by rfl⟩ : syracuseStep 193553 = 145165) B145165
theorem B128019 : Blo 127788 128019 := bstep (se 1 (by rfl) ⟨96014, by rfl⟩ : syracuseStep 128019 = 192029) B192029
theorem B128035 : Blo 127788 128035 := bstep (se 1 (by rfl) ⟨96026, by rfl⟩ : syracuseStep 128035 = 192053) B192053
theorem B193571 : Blo 127788 193571 := bstep (se 1 (by rfl) ⟨145178, by rfl⟩ : syracuseStep 193571 = 290357) B290357
theorem B128051 : Blo 127788 128051 := bstep (se 1 (by rfl) ⟨96038, by rfl⟩ : syracuseStep 128051 = 192077) B192077
theorem B193601 : Blo 127788 193601 := bstep (se 2 (by rfl) ⟨72600, by rfl⟩ : syracuseStep 193601 = 145201) B145201
theorem B128067 : Blo 127788 128067 := bstep (se 1 (by rfl) ⟨96050, by rfl⟩ : syracuseStep 128067 = 192101) B192101
theorem B128083 : Blo 127788 128083 := bstep (se 1 (by rfl) ⟨96062, by rfl⟩ : syracuseStep 128083 = 192125) B192125
theorem B193619 : Blo 127788 193619 := bstep (se 1 (by rfl) ⟨145214, by rfl⟩ : syracuseStep 193619 = 290429) B290429
theorem B128099 : Blo 127788 128099 := bstep (se 1 (by rfl) ⟨96074, by rfl⟩ : syracuseStep 128099 = 192149) B192149
theorem B193649 : Blo 127788 193649 := bstep (se 2 (by rfl) ⟨72618, by rfl⟩ : syracuseStep 193649 = 145237) B145237
theorem B128115 : Blo 127788 128115 := bstep (se 1 (by rfl) ⟨96086, by rfl⟩ : syracuseStep 128115 = 192173) B192173
theorem B128131 : Blo 127788 128131 := bstep (se 1 (by rfl) ⟨96098, by rfl⟩ : syracuseStep 128131 = 192197) B192197
theorem B193667 : Blo 127788 193667 := bstep (se 1 (by rfl) ⟨145250, by rfl⟩ : syracuseStep 193667 = 290501) B290501
theorem B128147 : Blo 127788 128147 := bstep (se 1 (by rfl) ⟨96110, by rfl⟩ : syracuseStep 128147 = 192221) B192221
theorem B193697 : Blo 127788 193697 := bstep (se 2 (by rfl) ⟨72636, by rfl⟩ : syracuseStep 193697 = 145273) B145273
theorem B128163 : Blo 127788 128163 := bstep (se 1 (by rfl) ⟨96122, by rfl⟩ : syracuseStep 128163 = 192245) B192245
theorem B128179 : Blo 127788 128179 := bstep (se 1 (by rfl) ⟨96134, by rfl⟩ : syracuseStep 128179 = 192269) B192269
theorem B193715 : Blo 127788 193715 := bstep (se 1 (by rfl) ⟨145286, by rfl⟩ : syracuseStep 193715 = 290573) B290573
theorem B128195 : Blo 127788 128195 := bstep (se 1 (by rfl) ⟨96146, by rfl⟩ : syracuseStep 128195 = 192293) B192293
theorem B193745 : Blo 127788 193745 := bstep (se 2 (by rfl) ⟨72654, by rfl⟩ : syracuseStep 193745 = 145309) B145309
theorem B292049 : Blo 127788 292049 := bstep (se 2 (by rfl) ⟨109518, by rfl⟩ : syracuseStep 292049 = 219037) B219037
theorem B128211 : Blo 127788 128211 := bstep (se 1 (by rfl) ⟨96158, by rfl⟩ : syracuseStep 128211 = 192317) B192317
theorem B128227 : Blo 127788 128227 := bstep (se 1 (by rfl) ⟨96170, by rfl⟩ : syracuseStep 128227 = 192341) B192341
theorem B193763 : Blo 127788 193763 := bstep (se 1 (by rfl) ⟨145322, by rfl⟩ : syracuseStep 193763 = 290645) B290645
theorem B292067 : Blo 127788 292067 := bstep (se 1 (by rfl) ⟨219050, by rfl⟩ : syracuseStep 292067 = 438101) B438101
theorem B128243 : Blo 127788 128243 := bstep (se 1 (by rfl) ⟨96182, by rfl⟩ : syracuseStep 128243 = 192365) B192365
theorem B193793 : Blo 127788 193793 := bstep (se 2 (by rfl) ⟨72672, by rfl⟩ : syracuseStep 193793 = 145345) B145345
theorem B128259 : Blo 127788 128259 := bstep (se 1 (by rfl) ⟨96194, by rfl⟩ : syracuseStep 128259 = 192389) B192389
theorem B324881 : Blo 127788 324881 := bstep (se 2 (by rfl) ⟨121830, by rfl⟩ : syracuseStep 324881 = 243661) B243661
theorem B128275 : Blo 127788 128275 := bstep (se 1 (by rfl) ⟨96206, by rfl⟩ : syracuseStep 128275 = 192413) B192413
theorem B193811 : Blo 127788 193811 := bstep (se 1 (by rfl) ⟨145358, by rfl⟩ : syracuseStep 193811 = 290717) B290717
theorem B128291 : Blo 127788 128291 := bstep (se 1 (by rfl) ⟨96218, by rfl⟩ : syracuseStep 128291 = 192437) B192437
theorem B193841 : Blo 127788 193841 := bstep (se 2 (by rfl) ⟨72690, by rfl⟩ : syracuseStep 193841 = 145381) B145381
theorem B128307 : Blo 127788 128307 := bstep (se 1 (by rfl) ⟨96230, by rfl⟩ : syracuseStep 128307 = 192461) B192461
theorem B128323 : Blo 127788 128323 := bstep (se 1 (by rfl) ⟨96242, by rfl⟩ : syracuseStep 128323 = 192485) B192485
theorem B324931 : Blo 127788 324931 := bstep (se 1 (by rfl) ⟨243698, by rfl⟩ : syracuseStep 324931 = 487397) B487397
theorem B193859 : Blo 127788 193859 := bstep (se 1 (by rfl) ⟨145394, by rfl⟩ : syracuseStep 193859 = 290789) B290789
theorem B128339 : Blo 127788 128339 := bstep (se 1 (by rfl) ⟨96254, by rfl⟩ : syracuseStep 128339 = 192509) B192509
theorem B193889 : Blo 127788 193889 := bstep (se 2 (by rfl) ⟨72708, by rfl⟩ : syracuseStep 193889 = 145417) B145417
theorem B128355 : Blo 127788 128355 := bstep (se 1 (by rfl) ⟨96266, by rfl⟩ : syracuseStep 128355 = 192533) B192533
theorem B750961 : Blo 127788 750961 := bstep (se 2 (by rfl) ⟨281610, by rfl⟩ : syracuseStep 750961 = 563221) B563221
theorem B128371 : Blo 127788 128371 := bstep (se 1 (by rfl) ⟨96278, by rfl⟩ : syracuseStep 128371 = 192557) B192557
theorem B193907 : Blo 127788 193907 := bstep (se 1 (by rfl) ⟨145430, by rfl⟩ : syracuseStep 193907 = 290861) B290861
theorem B128387 : Blo 127788 128387 := bstep (se 1 (by rfl) ⟨96290, by rfl⟩ : syracuseStep 128387 = 192581) B192581
theorem B423299 : Blo 127788 423299 := bstep (se 1 (by rfl) ⟨317474, by rfl⟩ : syracuseStep 423299 = 634949) B634949
theorem B193937 : Blo 127788 193937 := bstep (se 2 (by rfl) ⟨72726, by rfl⟩ : syracuseStep 193937 = 145453) B145453
theorem B128403 : Blo 127788 128403 := bstep (se 1 (by rfl) ⟨96302, by rfl⟩ : syracuseStep 128403 = 192605) B192605
theorem B128419 : Blo 127788 128419 := bstep (se 1 (by rfl) ⟨96314, by rfl⟩ : syracuseStep 128419 = 192629) B192629
theorem B193955 : Blo 127788 193955 := bstep (se 1 (by rfl) ⟨145466, by rfl⟩ : syracuseStep 193955 = 290933) B290933
theorem B128435 : Blo 127788 128435 := bstep (se 1 (by rfl) ⟨96326, by rfl⟩ : syracuseStep 128435 = 192653) B192653
theorem B193985 : Blo 127788 193985 := bstep (se 2 (by rfl) ⟨72744, by rfl⟩ : syracuseStep 193985 = 145489) B145489
theorem B128451 : Blo 127788 128451 := bstep (se 1 (by rfl) ⟨96338, by rfl⟩ : syracuseStep 128451 = 192677) B192677
theorem B325073 : Blo 127788 325073 := bstep (se 2 (by rfl) ⟨121902, by rfl⟩ : syracuseStep 325073 = 243805) B243805
theorem B128467 : Blo 127788 128467 := bstep (se 1 (by rfl) ⟨96350, by rfl⟩ : syracuseStep 128467 = 192701) B192701
theorem B194003 : Blo 127788 194003 := bstep (se 1 (by rfl) ⟨145502, by rfl⟩ : syracuseStep 194003 = 291005) B291005
theorem B128483 : Blo 127788 128483 := bstep (se 1 (by rfl) ⟨96362, by rfl⟩ : syracuseStep 128483 = 192725) B192725
theorem B194033 : Blo 127788 194033 := bstep (se 2 (by rfl) ⟨72762, by rfl⟩ : syracuseStep 194033 = 145525) B145525
theorem B292337 : Blo 127788 292337 := bstep (se 2 (by rfl) ⟨109626, by rfl⟩ : syracuseStep 292337 = 219253) B219253
theorem B128499 : Blo 127788 128499 := bstep (se 1 (by rfl) ⟨96374, by rfl⟩ : syracuseStep 128499 = 192749) B192749
theorem B128515 : Blo 127788 128515 := bstep (se 1 (by rfl) ⟨96386, by rfl⟩ : syracuseStep 128515 = 192773) B192773
theorem B194051 : Blo 127788 194051 := bstep (se 1 (by rfl) ⟨145538, by rfl⟩ : syracuseStep 194051 = 291077) B291077
theorem B292355 : Blo 127788 292355 := bstep (se 1 (by rfl) ⟨219266, by rfl⟩ : syracuseStep 292355 = 438533) B438533
theorem B128531 : Blo 127788 128531 := bstep (se 1 (by rfl) ⟨96398, by rfl⟩ : syracuseStep 128531 = 192797) B192797
theorem B194081 : Blo 127788 194081 := bstep (se 2 (by rfl) ⟨72780, by rfl⟩ : syracuseStep 194081 = 145561) B145561
theorem B128547 : Blo 127788 128547 := bstep (se 1 (by rfl) ⟨96410, by rfl⟩ : syracuseStep 128547 = 192821) B192821
theorem B128563 : Blo 127788 128563 := bstep (se 1 (by rfl) ⟨96422, by rfl⟩ : syracuseStep 128563 = 192845) B192845
theorem B194099 : Blo 127788 194099 := bstep (se 1 (by rfl) ⟨145574, by rfl⟩ : syracuseStep 194099 = 291149) B291149
theorem B128579 : Blo 127788 128579 := bstep (se 1 (by rfl) ⟨96434, by rfl⟩ : syracuseStep 128579 = 192869) B192869
theorem B489037 : Blo 127788 489037 := bstep (se 3 (by rfl) ⟨91694, by rfl⟩ : syracuseStep 489037 = 183389) B183389
theorem B194129 : Blo 127788 194129 := bstep (se 2 (by rfl) ⟨72798, by rfl⟩ : syracuseStep 194129 = 145597) B145597
theorem B128595 : Blo 127788 128595 := bstep (se 1 (by rfl) ⟨96446, by rfl⟩ : syracuseStep 128595 = 192893) B192893
theorem B128611 : Blo 127788 128611 := bstep (se 1 (by rfl) ⟨96458, by rfl⟩ : syracuseStep 128611 = 192917) B192917
theorem B194147 : Blo 127788 194147 := bstep (se 1 (by rfl) ⟨145610, by rfl⟩ : syracuseStep 194147 = 291221) B291221
theorem B128627 : Blo 127788 128627 := bstep (se 1 (by rfl) ⟨96470, by rfl⟩ : syracuseStep 128627 = 192941) B192941
theorem B194177 : Blo 127788 194177 := bstep (se 2 (by rfl) ⟨72816, by rfl⟩ : syracuseStep 194177 = 145633) B145633
theorem B128643 : Blo 127788 128643 := bstep (se 1 (by rfl) ⟨96482, by rfl⟩ : syracuseStep 128643 = 192965) B192965
theorem B128659 : Blo 127788 128659 := bstep (se 1 (by rfl) ⟨96494, by rfl⟩ : syracuseStep 128659 = 192989) B192989
theorem B194195 : Blo 127788 194195 := bstep (se 1 (by rfl) ⟨145646, by rfl⟩ : syracuseStep 194195 = 291293) B291293
theorem B128675 : Blo 127788 128675 := bstep (se 1 (by rfl) ⟨96506, by rfl⟩ : syracuseStep 128675 = 193013) B193013
theorem B194225 : Blo 127788 194225 := bstep (se 2 (by rfl) ⟨72834, by rfl⟩ : syracuseStep 194225 = 145669) B145669
theorem B128691 : Blo 127788 128691 := bstep (se 1 (by rfl) ⟨96518, by rfl⟩ : syracuseStep 128691 = 193037) B193037
theorem B128707 : Blo 127788 128707 := bstep (se 1 (by rfl) ⟨96530, by rfl⟩ : syracuseStep 128707 = 193061) B193061
theorem B194243 : Blo 127788 194243 := bstep (se 1 (by rfl) ⟨145682, by rfl⟩ : syracuseStep 194243 = 291365) B291365
theorem B554701 : Blo 127788 554701 := bstep (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) B208013
theorem B128723 : Blo 127788 128723 := bstep (se 1 (by rfl) ⟨96542, by rfl⟩ : syracuseStep 128723 = 193085) B193085
theorem B194273 : Blo 127788 194273 := bstep (se 2 (by rfl) ⟨72852, by rfl⟩ : syracuseStep 194273 = 145705) B145705
theorem B128739 : Blo 127788 128739 := bstep (se 1 (by rfl) ⟨96554, by rfl⟩ : syracuseStep 128739 = 193109) B193109
theorem B128755 : Blo 127788 128755 := bstep (se 1 (by rfl) ⟨96566, by rfl⟩ : syracuseStep 128755 = 193133) B193133
theorem B194291 : Blo 127788 194291 := bstep (se 1 (by rfl) ⟨145718, by rfl⟩ : syracuseStep 194291 = 291437) B291437
theorem B128771 : Blo 127788 128771 := bstep (se 1 (by rfl) ⟨96578, by rfl⟩ : syracuseStep 128771 = 193157) B193157
theorem B194321 : Blo 127788 194321 := bstep (se 2 (by rfl) ⟨72870, by rfl⟩ : syracuseStep 194321 = 145741) B145741
theorem B292625 : Blo 127788 292625 := bstep (se 2 (by rfl) ⟨109734, by rfl⟩ : syracuseStep 292625 = 219469) B219469
theorem B128787 : Blo 127788 128787 := bstep (se 1 (by rfl) ⟨96590, by rfl⟩ : syracuseStep 128787 = 193181) B193181
theorem B128803 : Blo 127788 128803 := bstep (se 1 (by rfl) ⟨96602, by rfl⟩ : syracuseStep 128803 = 193205) B193205
theorem B194339 : Blo 127788 194339 := bstep (se 1 (by rfl) ⟨145754, by rfl⟩ : syracuseStep 194339 = 291509) B291509
theorem B292643 : Blo 127788 292643 := bstep (se 1 (by rfl) ⟨219482, by rfl⟩ : syracuseStep 292643 = 438965) B438965
theorem B128819 : Blo 127788 128819 := bstep (se 1 (by rfl) ⟨96614, by rfl⟩ : syracuseStep 128819 = 193229) B193229
theorem B194369 : Blo 127788 194369 := bstep (se 2 (by rfl) ⟨72888, by rfl⟩ : syracuseStep 194369 = 145777) B145777
theorem B128835 : Blo 127788 128835 := bstep (se 1 (by rfl) ⟨96626, by rfl⟩ : syracuseStep 128835 = 193253) B193253
theorem B128851 : Blo 127788 128851 := bstep (se 1 (by rfl) ⟨96638, by rfl⟩ : syracuseStep 128851 = 193277) B193277
theorem B194387 : Blo 127788 194387 := bstep (se 1 (by rfl) ⟨145790, by rfl⟩ : syracuseStep 194387 = 291581) B291581
theorem B128867 : Blo 127788 128867 := bstep (se 1 (by rfl) ⟨96650, by rfl⟩ : syracuseStep 128867 = 193301) B193301
theorem B194417 : Blo 127788 194417 := bstep (se 2 (by rfl) ⟨72906, by rfl⟩ : syracuseStep 194417 = 145813) B145813
theorem B128883 : Blo 127788 128883 := bstep (se 1 (by rfl) ⟨96662, by rfl⟩ : syracuseStep 128883 = 193325) B193325
theorem B128899 : Blo 127788 128899 := bstep (se 1 (by rfl) ⟨96674, by rfl⟩ : syracuseStep 128899 = 193349) B193349
theorem B194435 : Blo 127788 194435 := bstep (se 1 (by rfl) ⟨145826, by rfl⟩ : syracuseStep 194435 = 291653) B291653
theorem B128915 : Blo 127788 128915 := bstep (se 1 (by rfl) ⟨96686, by rfl⟩ : syracuseStep 128915 = 193373) B193373
theorem B194465 : Blo 127788 194465 := bstep (se 2 (by rfl) ⟨72924, by rfl⟩ : syracuseStep 194465 = 145849) B145849
theorem B128931 : Blo 127788 128931 := bstep (se 1 (by rfl) ⟨96698, by rfl⟩ : syracuseStep 128931 = 193397) B193397
theorem B128947 : Blo 127788 128947 := bstep (se 1 (by rfl) ⟨96710, by rfl⟩ : syracuseStep 128947 = 193421) B193421
theorem B194483 : Blo 127788 194483 := bstep (se 1 (by rfl) ⟨145862, by rfl⟩ : syracuseStep 194483 = 291725) B291725
theorem B128963 : Blo 127788 128963 := bstep (se 1 (by rfl) ⟨96722, by rfl⟩ : syracuseStep 128963 = 193445) B193445
theorem B194513 : Blo 127788 194513 := bstep (se 2 (by rfl) ⟨72942, by rfl⟩ : syracuseStep 194513 = 145885) B145885
theorem B128979 : Blo 127788 128979 := bstep (se 1 (by rfl) ⟨96734, by rfl⟩ : syracuseStep 128979 = 193469) B193469
theorem B128995 : Blo 127788 128995 := bstep (se 1 (by rfl) ⟨96746, by rfl⟩ : syracuseStep 128995 = 193493) B193493
theorem B194531 : Blo 127788 194531 := bstep (se 1 (by rfl) ⟨145898, by rfl⟩ : syracuseStep 194531 = 291797) B291797
theorem B129011 : Blo 127788 129011 := bstep (se 1 (by rfl) ⟨96758, by rfl⟩ : syracuseStep 129011 = 193517) B193517
theorem B194561 : Blo 127788 194561 := bstep (se 2 (by rfl) ⟨72960, by rfl⟩ : syracuseStep 194561 = 145921) B145921
theorem B129027 : Blo 127788 129027 := bstep (se 1 (by rfl) ⟨96770, by rfl⟩ : syracuseStep 129027 = 193541) B193541
theorem B129043 : Blo 127788 129043 := bstep (se 1 (by rfl) ⟨96782, by rfl⟩ : syracuseStep 129043 = 193565) B193565
theorem B194579 : Blo 127788 194579 := bstep (se 1 (by rfl) ⟨145934, by rfl⟩ : syracuseStep 194579 = 291869) B291869
theorem B129059 : Blo 127788 129059 := bstep (se 1 (by rfl) ⟨96794, by rfl⟩ : syracuseStep 129059 = 193589) B193589
theorem B194609 : Blo 127788 194609 := bstep (se 2 (by rfl) ⟨72978, by rfl⟩ : syracuseStep 194609 = 145957) B145957
theorem B292913 : Blo 127788 292913 := bstep (se 2 (by rfl) ⟨109842, by rfl⟩ : syracuseStep 292913 = 219685) B219685
theorem B129075 : Blo 127788 129075 := bstep (se 1 (by rfl) ⟨96806, by rfl⟩ : syracuseStep 129075 = 193613) B193613
theorem B129091 : Blo 127788 129091 := bstep (se 1 (by rfl) ⟨96818, by rfl⟩ : syracuseStep 129091 = 193637) B193637
theorem B194627 : Blo 127788 194627 := bstep (se 1 (by rfl) ⟨145970, by rfl⟩ : syracuseStep 194627 = 291941) B291941
theorem B292931 : Blo 127788 292931 := bstep (se 1 (by rfl) ⟨219698, by rfl⟩ : syracuseStep 292931 = 439397) B439397
theorem B129107 : Blo 127788 129107 := bstep (se 1 (by rfl) ⟨96830, by rfl⟩ : syracuseStep 129107 = 193661) B193661
theorem B194657 : Blo 127788 194657 := bstep (se 2 (by rfl) ⟨72996, by rfl⟩ : syracuseStep 194657 = 145993) B145993
theorem B129123 : Blo 127788 129123 := bstep (se 1 (by rfl) ⟨96842, by rfl⟩ : syracuseStep 129123 = 193685) B193685
theorem B129139 : Blo 127788 129139 := bstep (se 1 (by rfl) ⟨96854, by rfl⟩ : syracuseStep 129139 = 193709) B193709
theorem B194675 : Blo 127788 194675 := bstep (se 1 (by rfl) ⟨146006, by rfl⟩ : syracuseStep 194675 = 292013) B292013
theorem B129155 : Blo 127788 129155 := bstep (se 1 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 129155 = 193733) B193733
theorem B194705 : Blo 127788 194705 := bstep (se 2 (by rfl) ⟨73014, by rfl⟩ : syracuseStep 194705 = 146029) B146029
theorem B161939 : Blo 127788 161939 := bstep (se 1 (by rfl) ⟨121454, by rfl⟩ : syracuseStep 161939 = 242909) B242909
theorem B129171 : Blo 127788 129171 := bstep (se 1 (by rfl) ⟨96878, by rfl⟩ : syracuseStep 129171 = 193757) B193757
theorem B129187 : Blo 127788 129187 := bstep (se 1 (by rfl) ⟨96890, by rfl⟩ : syracuseStep 129187 = 193781) B193781
theorem B194723 : Blo 127788 194723 := bstep (se 1 (by rfl) ⟨146042, by rfl⟩ : syracuseStep 194723 = 292085) B292085
theorem B260273 : Blo 127788 260273 := bstep (se 2 (by rfl) ⟨97602, by rfl⟩ : syracuseStep 260273 = 195205) B195205
theorem B129203 : Blo 127788 129203 := bstep (se 1 (by rfl) ⟨96902, by rfl⟩ : syracuseStep 129203 = 193805) B193805
theorem B194753 : Blo 127788 194753 := bstep (se 2 (by rfl) ⟨73032, by rfl⟩ : syracuseStep 194753 = 146065) B146065
theorem B129219 : Blo 127788 129219 := bstep (se 1 (by rfl) ⟨96914, by rfl⟩ : syracuseStep 129219 = 193829) B193829
theorem B129235 : Blo 127788 129235 := bstep (se 1 (by rfl) ⟨96926, by rfl⟩ : syracuseStep 129235 = 193853) B193853
theorem B194771 : Blo 127788 194771 := bstep (se 1 (by rfl) ⟨146078, by rfl⟩ : syracuseStep 194771 = 292157) B292157
theorem B129251 : Blo 127788 129251 := bstep (se 1 (by rfl) ⟨96938, by rfl⟩ : syracuseStep 129251 = 193877) B193877
theorem B981233 : Blo 127788 981233 := bstep (se 2 (by rfl) ⟨367962, by rfl⟩ : syracuseStep 981233 = 735925) B735925
theorem B194801 : Blo 127788 194801 := bstep (se 2 (by rfl) ⟨73050, by rfl⟩ : syracuseStep 194801 = 146101) B146101
theorem B129267 : Blo 127788 129267 := bstep (se 1 (by rfl) ⟨96950, by rfl⟩ : syracuseStep 129267 = 193901) B193901
theorem B129283 : Blo 127788 129283 := bstep (se 1 (by rfl) ⟨96962, by rfl⟩ : syracuseStep 129283 = 193925) B193925
theorem B194819 : Blo 127788 194819 := bstep (se 1 (by rfl) ⟨146114, by rfl⟩ : syracuseStep 194819 = 292229) B292229
theorem B129299 : Blo 127788 129299 := bstep (se 1 (by rfl) ⟨96974, by rfl⟩ : syracuseStep 129299 = 193949) B193949
theorem B194849 : Blo 127788 194849 := bstep (se 2 (by rfl) ⟨73068, by rfl⟩ : syracuseStep 194849 = 146137) B146137
theorem B129315 : Blo 127788 129315 := bstep (se 1 (by rfl) ⟨96986, by rfl⟩ : syracuseStep 129315 = 193973) B193973
theorem B129331 : Blo 127788 129331 := bstep (se 1 (by rfl) ⟨96998, by rfl⟩ : syracuseStep 129331 = 193997) B193997
theorem B194867 : Blo 127788 194867 := bstep (se 1 (by rfl) ⟨146150, by rfl⟩ : syracuseStep 194867 = 292301) B292301
theorem B129347 : Blo 127788 129347 := bstep (se 1 (by rfl) ⟨97010, by rfl⟩ : syracuseStep 129347 = 194021) B194021
theorem B194897 : Blo 127788 194897 := bstep (se 2 (by rfl) ⟨73086, by rfl⟩ : syracuseStep 194897 = 146173) B146173
theorem B293201 : Blo 127788 293201 := bstep (se 2 (by rfl) ⟨109950, by rfl⟩ : syracuseStep 293201 = 219901) B219901
theorem B129363 : Blo 127788 129363 := bstep (se 1 (by rfl) ⟨97022, by rfl⟩ : syracuseStep 129363 = 194045) B194045
theorem B489827 : Blo 127788 489827 := bstep (se 1 (by rfl) ⟨367370, by rfl⟩ : syracuseStep 489827 = 734741) B734741
theorem B129379 : Blo 127788 129379 := bstep (se 1 (by rfl) ⟨97034, by rfl⟩ : syracuseStep 129379 = 194069) B194069
theorem B194915 : Blo 127788 194915 := bstep (se 1 (by rfl) ⟨146186, by rfl⟩ : syracuseStep 194915 = 292373) B292373
theorem B293219 : Blo 127788 293219 := bstep (se 1 (by rfl) ⟨219914, by rfl⟩ : syracuseStep 293219 = 439829) B439829
theorem B129395 : Blo 127788 129395 := bstep (se 1 (by rfl) ⟨97046, by rfl⟩ : syracuseStep 129395 = 194093) B194093
theorem B194945 : Blo 127788 194945 := bstep (se 2 (by rfl) ⟨73104, by rfl⟩ : syracuseStep 194945 = 146209) B146209
theorem B129411 : Blo 127788 129411 := bstep (se 1 (by rfl) ⟨97058, by rfl⟩ : syracuseStep 129411 = 194117) B194117
theorem B129427 : Blo 127788 129427 := bstep (se 1 (by rfl) ⟨97070, by rfl⟩ : syracuseStep 129427 = 194141) B194141
theorem B194963 : Blo 127788 194963 := bstep (se 1 (by rfl) ⟨146222, by rfl⟩ : syracuseStep 194963 = 292445) B292445
theorem B129443 : Blo 127788 129443 := bstep (se 1 (by rfl) ⟨97082, by rfl⟩ : syracuseStep 129443 = 194165) B194165
theorem B326065 : Blo 127788 326065 := bstep (se 2 (by rfl) ⟨122274, by rfl⟩ : syracuseStep 326065 = 244549) B244549
theorem B194993 : Blo 127788 194993 := bstep (se 2 (by rfl) ⟨73122, by rfl⟩ : syracuseStep 194993 = 146245) B146245
theorem B129459 : Blo 127788 129459 := bstep (se 1 (by rfl) ⟨97094, by rfl⟩ : syracuseStep 129459 = 194189) B194189
theorem B129475 : Blo 127788 129475 := bstep (se 1 (by rfl) ⟨97106, by rfl⟩ : syracuseStep 129475 = 194213) B194213
theorem B195011 : Blo 127788 195011 := bstep (se 1 (by rfl) ⟨146258, by rfl⟩ : syracuseStep 195011 = 292517) B292517
theorem B129491 : Blo 127788 129491 := bstep (se 1 (by rfl) ⟨97118, by rfl⟩ : syracuseStep 129491 = 194237) B194237
theorem B195041 : Blo 127788 195041 := bstep (se 2 (by rfl) ⟨73140, by rfl⟩ : syracuseStep 195041 = 146281) B146281
theorem B129507 : Blo 127788 129507 := bstep (se 1 (by rfl) ⟨97130, by rfl⟩ : syracuseStep 129507 = 194261) B194261
theorem B129523 : Blo 127788 129523 := bstep (se 1 (by rfl) ⟨97142, by rfl⟩ : syracuseStep 129523 = 194285) B194285
theorem B195059 : Blo 127788 195059 := bstep (se 1 (by rfl) ⟨146294, by rfl⟩ : syracuseStep 195059 = 292589) B292589
theorem B129539 : Blo 127788 129539 := bstep (se 1 (by rfl) ⟨97154, by rfl⟩ : syracuseStep 129539 = 194309) B194309
theorem B195089 : Blo 127788 195089 := bstep (se 2 (by rfl) ⟨73158, by rfl⟩ : syracuseStep 195089 = 146317) B146317
theorem B129555 : Blo 127788 129555 := bstep (se 1 (by rfl) ⟨97166, by rfl⟩ : syracuseStep 129555 = 194333) B194333
theorem B3176981 : Blo 127788 3176981 := bstep (se 6 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 3176981 = 148921) B148921
theorem B129571 : Blo 127788 129571 := bstep (se 1 (by rfl) ⟨97178, by rfl⟩ : syracuseStep 129571 = 194357) B194357
theorem B195107 : Blo 127788 195107 := bstep (se 1 (by rfl) ⟨146330, by rfl⟩ : syracuseStep 195107 = 292661) B292661
theorem B129587 : Blo 127788 129587 := bstep (se 1 (by rfl) ⟨97190, by rfl⟩ : syracuseStep 129587 = 194381) B194381
theorem B195137 : Blo 127788 195137 := bstep (se 2 (by rfl) ⟨73176, by rfl⟩ : syracuseStep 195137 = 146353) B146353
theorem B129603 : Blo 127788 129603 := bstep (se 1 (by rfl) ⟨97202, by rfl⟩ : syracuseStep 129603 = 194405) B194405
theorem B129619 : Blo 127788 129619 := bstep (se 1 (by rfl) ⟨97214, by rfl⟩ : syracuseStep 129619 = 194429) B194429
theorem B195155 : Blo 127788 195155 := bstep (se 1 (by rfl) ⟨146366, by rfl⟩ : syracuseStep 195155 = 292733) B292733
theorem B129635 : Blo 127788 129635 := bstep (se 1 (by rfl) ⟨97226, by rfl⟩ : syracuseStep 129635 = 194453) B194453
theorem B555619 : Blo 127788 555619 := bstep (se 1 (by rfl) ⟨416714, by rfl⟩ : syracuseStep 555619 = 833429) B833429
theorem B293489 : Blo 127788 293489 := bstep (se 2 (by rfl) ⟨110058, by rfl⟩ : syracuseStep 293489 = 220117) B220117
theorem B195185 : Blo 127788 195185 := bstep (se 2 (by rfl) ⟨73194, by rfl⟩ : syracuseStep 195185 = 146389) B146389
theorem B129651 : Blo 127788 129651 := bstep (se 1 (by rfl) ⟨97238, by rfl⟩ : syracuseStep 129651 = 194477) B194477
theorem B129667 : Blo 127788 129667 := bstep (se 1 (by rfl) ⟨97250, by rfl⟩ : syracuseStep 129667 = 194501) B194501
theorem B195203 : Blo 127788 195203 := bstep (se 1 (by rfl) ⟨146402, by rfl⟩ : syracuseStep 195203 = 292805) B292805
theorem B293507 : Blo 127788 293507 := bstep (se 1 (by rfl) ⟨220130, by rfl⟩ : syracuseStep 293507 = 440261) B440261
theorem B129683 : Blo 127788 129683 := bstep (se 1 (by rfl) ⟨97262, by rfl⟩ : syracuseStep 129683 = 194525) B194525
theorem B195233 : Blo 127788 195233 := bstep (se 2 (by rfl) ⟨73212, by rfl⟩ : syracuseStep 195233 = 146425) B146425
theorem B129699 : Blo 127788 129699 := bstep (se 1 (by rfl) ⟨97274, by rfl⟩ : syracuseStep 129699 = 194549) B194549
theorem B129715 : Blo 127788 129715 := bstep (se 1 (by rfl) ⟨97286, by rfl⟩ : syracuseStep 129715 = 194573) B194573
theorem B195251 : Blo 127788 195251 := bstep (se 1 (by rfl) ⟨146438, by rfl⟩ : syracuseStep 195251 = 292877) B292877
theorem B326339 : Blo 127788 326339 := bstep (se 1 (by rfl) ⟨244754, by rfl⟩ : syracuseStep 326339 = 489509) B489509
theorem B129731 : Blo 127788 129731 := bstep (se 1 (by rfl) ⟨97298, by rfl⟩ : syracuseStep 129731 = 194597) B194597
theorem B195281 : Blo 127788 195281 := bstep (se 2 (by rfl) ⟨73230, by rfl⟩ : syracuseStep 195281 = 146461) B146461
theorem B129747 : Blo 127788 129747 := bstep (se 1 (by rfl) ⟨97310, by rfl⟩ : syracuseStep 129747 = 194621) B194621
theorem B129763 : Blo 127788 129763 := bstep (se 1 (by rfl) ⟨97322, by rfl⟩ : syracuseStep 129763 = 194645) B194645
theorem B195299 : Blo 127788 195299 := bstep (se 1 (by rfl) ⟨146474, by rfl⟩ : syracuseStep 195299 = 292949) B292949
theorem B129779 : Blo 127788 129779 := bstep (se 1 (by rfl) ⟨97334, by rfl⟩ : syracuseStep 129779 = 194669) B194669
theorem B195329 : Blo 127788 195329 := bstep (se 2 (by rfl) ⟨73248, by rfl⟩ : syracuseStep 195329 = 146497) B146497
theorem B129795 : Blo 127788 129795 := bstep (se 1 (by rfl) ⟨97346, by rfl⟩ : syracuseStep 129795 = 194693) B194693
theorem B129811 : Blo 127788 129811 := bstep (se 1 (by rfl) ⟨97358, by rfl⟩ : syracuseStep 129811 = 194717) B194717
theorem B195347 : Blo 127788 195347 := bstep (se 1 (by rfl) ⟨146510, by rfl⟩ : syracuseStep 195347 = 293021) B293021
theorem B129827 : Blo 127788 129827 := bstep (se 1 (by rfl) ⟨97370, by rfl⟩ : syracuseStep 129827 = 194741) B194741
theorem B195377 : Blo 127788 195377 := bstep (se 2 (by rfl) ⟨73266, by rfl⟩ : syracuseStep 195377 = 146533) B146533
theorem B129843 : Blo 127788 129843 := bstep (se 1 (by rfl) ⟨97382, by rfl⟩ : syracuseStep 129843 = 194765) B194765
theorem B129859 : Blo 127788 129859 := bstep (se 1 (by rfl) ⟨97394, by rfl⟩ : syracuseStep 129859 = 194789) B194789
theorem B195395 : Blo 127788 195395 := bstep (se 1 (by rfl) ⟨146546, by rfl⟩ : syracuseStep 195395 = 293093) B293093
theorem B162643 : Blo 127788 162643 := bstep (se 1 (by rfl) ⟨121982, by rfl⟩ : syracuseStep 162643 = 243965) B243965
theorem B129875 : Blo 127788 129875 := bstep (se 1 (by rfl) ⟨97406, by rfl⟩ : syracuseStep 129875 = 194813) B194813
theorem B195425 : Blo 127788 195425 := bstep (se 2 (by rfl) ⟨73284, by rfl⟩ : syracuseStep 195425 = 146569) B146569
theorem B129891 : Blo 127788 129891 := bstep (se 1 (by rfl) ⟨97418, by rfl⟩ : syracuseStep 129891 = 194837) B194837
theorem B195443 : Blo 127788 195443 := bstep (se 1 (by rfl) ⟨146582, by rfl⟩ : syracuseStep 195443 = 293165) B293165
theorem B129907 : Blo 127788 129907 := bstep (se 1 (by rfl) ⟨97430, by rfl⟩ : syracuseStep 129907 = 194861) B194861
theorem B326531 : Blo 127788 326531 := bstep (se 1 (by rfl) ⟨244898, by rfl⟩ : syracuseStep 326531 = 489797) B489797
theorem B129923 : Blo 127788 129923 := bstep (se 1 (by rfl) ⟨97442, by rfl⟩ : syracuseStep 129923 = 194885) B194885
theorem B195473 : Blo 127788 195473 := bstep (se 2 (by rfl) ⟨73302, by rfl⟩ : syracuseStep 195473 = 146605) B146605
theorem B293777 : Blo 127788 293777 := bstep (se 2 (by rfl) ⟨110166, by rfl⟩ : syracuseStep 293777 = 220333) B220333
theorem B129939 : Blo 127788 129939 := bstep (se 1 (by rfl) ⟨97454, by rfl⟩ : syracuseStep 129939 = 194909) B194909
theorem B129955 : Blo 127788 129955 := bstep (se 1 (by rfl) ⟨97466, by rfl⟩ : syracuseStep 129955 = 194933) B194933
theorem B195491 : Blo 127788 195491 := bstep (se 1 (by rfl) ⟨146618, by rfl⟩ : syracuseStep 195491 = 293237) B293237
theorem B293795 : Blo 127788 293795 := bstep (se 1 (by rfl) ⟨220346, by rfl⟩ : syracuseStep 293795 = 440693) B440693
theorem B162739 : Blo 127788 162739 := bstep (se 1 (by rfl) ⟨122054, by rfl⟩ : syracuseStep 162739 = 244109) B244109
theorem B129971 : Blo 127788 129971 := bstep (se 1 (by rfl) ⟨97478, by rfl⟩ : syracuseStep 129971 = 194957) B194957
theorem B195521 : Blo 127788 195521 := bstep (se 2 (by rfl) ⟨73320, by rfl⟩ : syracuseStep 195521 = 146641) B146641
theorem B129987 : Blo 127788 129987 := bstep (se 1 (by rfl) ⟨97490, by rfl⟩ : syracuseStep 129987 = 194981) B194981
theorem B130003 : Blo 127788 130003 := bstep (se 1 (by rfl) ⟨97502, by rfl⟩ : syracuseStep 130003 = 195005) B195005
theorem B195539 : Blo 127788 195539 := bstep (se 1 (by rfl) ⟨146654, by rfl⟩ : syracuseStep 195539 = 293309) B293309
theorem B130019 : Blo 127788 130019 := bstep (se 1 (by rfl) ⟨97514, by rfl⟩ : syracuseStep 130019 = 195029) B195029
theorem B490481 : Blo 127788 490481 := bstep (se 2 (by rfl) ⟨183930, by rfl⟩ : syracuseStep 490481 = 367861) B367861
theorem B621553 : Blo 127788 621553 := bstep (se 2 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 621553 = 466165) B466165
theorem B130035 : Blo 127788 130035 := bstep (se 1 (by rfl) ⟨97526, by rfl⟩ : syracuseStep 130035 = 195053) B195053
theorem B195569 : Blo 127788 195569 := bstep (se 2 (by rfl) ⟨73338, by rfl⟩ : syracuseStep 195569 = 146677) B146677
theorem B130051 : Blo 127788 130051 := bstep (se 1 (by rfl) ⟨97538, by rfl⟩ : syracuseStep 130051 = 195077) B195077
theorem B195587 : Blo 127788 195587 := bstep (se 1 (by rfl) ⟨146690, by rfl⟩ : syracuseStep 195587 = 293381) B293381
theorem B130067 : Blo 127788 130067 := bstep (se 1 (by rfl) ⟨97550, by rfl⟩ : syracuseStep 130067 = 195101) B195101
theorem B195617 : Blo 127788 195617 := bstep (se 2 (by rfl) ⟨73356, by rfl⟩ : syracuseStep 195617 = 146713) B146713
theorem B130083 : Blo 127788 130083 := bstep (se 1 (by rfl) ⟨97562, by rfl⟩ : syracuseStep 130083 = 195125) B195125
theorem B130099 : Blo 127788 130099 := bstep (se 1 (by rfl) ⟨97574, by rfl⟩ : syracuseStep 130099 = 195149) B195149
theorem B195635 : Blo 127788 195635 := bstep (se 1 (by rfl) ⟨146726, by rfl⟩ : syracuseStep 195635 = 293453) B293453
theorem B130115 : Blo 127788 130115 := bstep (se 1 (by rfl) ⟨97586, by rfl⟩ : syracuseStep 130115 = 195173) B195173
theorem B195665 : Blo 127788 195665 := bstep (se 2 (by rfl) ⟨73374, by rfl⟩ : syracuseStep 195665 = 146749) B146749
theorem B130131 : Blo 127788 130131 := bstep (se 1 (by rfl) ⟨97598, by rfl⟩ : syracuseStep 130131 = 195197) B195197
theorem B130147 : Blo 127788 130147 := bstep (se 1 (by rfl) ⟨97610, by rfl⟩ : syracuseStep 130147 = 195221) B195221
theorem B195683 : Blo 127788 195683 := bstep (se 1 (by rfl) ⟨146762, by rfl⟩ : syracuseStep 195683 = 293525) B293525
theorem B130163 : Blo 127788 130163 := bstep (se 1 (by rfl) ⟨97622, by rfl⟩ : syracuseStep 130163 = 195245) B195245
theorem B195713 : Blo 127788 195713 := bstep (se 2 (by rfl) ⟨73392, by rfl⟩ : syracuseStep 195713 = 146785) B146785
theorem B130179 : Blo 127788 130179 := bstep (se 1 (by rfl) ⟨97634, by rfl⟩ : syracuseStep 130179 = 195269) B195269
theorem B130195 : Blo 127788 130195 := bstep (se 1 (by rfl) ⟨97646, by rfl⟩ : syracuseStep 130195 = 195293) B195293
theorem B195731 : Blo 127788 195731 := bstep (se 1 (by rfl) ⟨146798, by rfl⟩ : syracuseStep 195731 = 293597) B293597
theorem B130211 : Blo 127788 130211 := bstep (se 1 (by rfl) ⟨97658, by rfl⟩ : syracuseStep 130211 = 195317) B195317
theorem B195761 : Blo 127788 195761 := bstep (se 2 (by rfl) ⟨73410, by rfl⟩ : syracuseStep 195761 = 146821) B146821
theorem B294065 : Blo 127788 294065 := bstep (se 2 (by rfl) ⟨110274, by rfl⟩ : syracuseStep 294065 = 220549) B220549
theorem B130227 : Blo 127788 130227 := bstep (se 1 (by rfl) ⟨97670, by rfl⟩ : syracuseStep 130227 = 195341) B195341
theorem B294083 : Blo 127788 294083 := bstep (se 1 (by rfl) ⟨220562, by rfl⟩ : syracuseStep 294083 = 441125) B441125
theorem B130243 : Blo 127788 130243 := bstep (se 1 (by rfl) ⟨97682, by rfl⟩ : syracuseStep 130243 = 195365) B195365
theorem B195779 : Blo 127788 195779 := bstep (se 1 (by rfl) ⟨146834, by rfl⟩ : syracuseStep 195779 = 293669) B293669
theorem B130259 : Blo 127788 130259 := bstep (se 1 (by rfl) ⟨97694, by rfl⟩ : syracuseStep 130259 = 195389) B195389
theorem B195809 : Blo 127788 195809 := bstep (se 2 (by rfl) ⟨73428, by rfl⟩ : syracuseStep 195809 = 146857) B146857
theorem B130275 : Blo 127788 130275 := bstep (se 1 (by rfl) ⟨97706, by rfl⟩ : syracuseStep 130275 = 195413) B195413
theorem B130291 : Blo 127788 130291 := bstep (se 1 (by rfl) ⟨97718, by rfl⟩ : syracuseStep 130291 = 195437) B195437
theorem B195827 : Blo 127788 195827 := bstep (se 1 (by rfl) ⟨146870, by rfl⟩ : syracuseStep 195827 = 293741) B293741
theorem B130307 : Blo 127788 130307 := bstep (se 1 (by rfl) ⟨97730, by rfl⟩ : syracuseStep 130307 = 195461) B195461
theorem B195857 : Blo 127788 195857 := bstep (se 2 (by rfl) ⟨73446, by rfl⟩ : syracuseStep 195857 = 146893) B146893
theorem B130323 : Blo 127788 130323 := bstep (se 1 (by rfl) ⟨97742, by rfl⟩ : syracuseStep 130323 = 195485) B195485
theorem B130339 : Blo 127788 130339 := bstep (se 1 (by rfl) ⟨97754, by rfl⟩ : syracuseStep 130339 = 195509) B195509
theorem B195875 : Blo 127788 195875 := bstep (se 1 (by rfl) ⟨146906, by rfl⟩ : syracuseStep 195875 = 293813) B293813
theorem B654641 : Blo 127788 654641 := bstep (se 2 (by rfl) ⟨245490, by rfl⟩ : syracuseStep 654641 = 490981) B490981
theorem B130355 : Blo 127788 130355 := bstep (se 1 (by rfl) ⟨97766, by rfl⟩ : syracuseStep 130355 = 195533) B195533
theorem B195905 : Blo 127788 195905 := bstep (se 2 (by rfl) ⟨73464, by rfl⟩ : syracuseStep 195905 = 146929) B146929
theorem B130371 : Blo 127788 130371 := bstep (se 1 (by rfl) ⟨97778, by rfl⟩ : syracuseStep 130371 = 195557) B195557
theorem B130387 : Blo 127788 130387 := bstep (se 1 (by rfl) ⟨97790, by rfl⟩ : syracuseStep 130387 = 195581) B195581
theorem B195923 : Blo 127788 195923 := bstep (se 1 (by rfl) ⟨146942, by rfl⟩ : syracuseStep 195923 = 293885) B293885
theorem B130403 : Blo 127788 130403 := bstep (se 1 (by rfl) ⟨97802, by rfl⟩ : syracuseStep 130403 = 195605) B195605
theorem B949603 : Blo 127788 949603 := bstep (se 1 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 949603 = 1424405) B1424405
theorem B195953 : Blo 127788 195953 := bstep (se 2 (by rfl) ⟨73482, by rfl⟩ : syracuseStep 195953 = 146965) B146965
theorem B130419 : Blo 127788 130419 := bstep (se 1 (by rfl) ⟨97814, by rfl⟩ : syracuseStep 130419 = 195629) B195629
theorem B130435 : Blo 127788 130435 := bstep (se 1 (by rfl) ⟨97826, by rfl⟩ : syracuseStep 130435 = 195653) B195653
theorem B195971 : Blo 127788 195971 := bstep (se 1 (by rfl) ⟨146978, by rfl⟩ : syracuseStep 195971 = 293957) B293957
theorem B130451 : Blo 127788 130451 := bstep (se 1 (by rfl) ⟨97838, by rfl⟩ : syracuseStep 130451 = 195677) B195677
theorem B196001 : Blo 127788 196001 := bstep (se 2 (by rfl) ⟨73500, by rfl⟩ : syracuseStep 196001 = 147001) B147001
theorem B163235 : Blo 127788 163235 := bstep (se 1 (by rfl) ⟨122426, by rfl⟩ : syracuseStep 163235 = 244853) B244853
theorem B130467 : Blo 127788 130467 := bstep (se 1 (by rfl) ⟨97850, by rfl⟩ : syracuseStep 130467 = 195701) B195701
theorem B130483 : Blo 127788 130483 := bstep (se 1 (by rfl) ⟨97862, by rfl⟩ : syracuseStep 130483 = 195725) B195725
theorem B196019 : Blo 127788 196019 := bstep (se 1 (by rfl) ⟨147014, by rfl⟩ : syracuseStep 196019 = 294029) B294029
theorem B130499 : Blo 127788 130499 := bstep (se 1 (by rfl) ⟨97874, by rfl⟩ : syracuseStep 130499 = 195749) B195749
theorem B196049 : Blo 127788 196049 := bstep (se 2 (by rfl) ⟨73518, by rfl⟩ : syracuseStep 196049 = 147037) B147037
theorem B294353 : Blo 127788 294353 := bstep (se 2 (by rfl) ⟨110382, by rfl⟩ : syracuseStep 294353 = 220765) B220765
theorem B130515 : Blo 127788 130515 := bstep (se 1 (by rfl) ⟨97886, by rfl⟩ : syracuseStep 130515 = 195773) B195773
theorem B130531 : Blo 127788 130531 := bstep (se 1 (by rfl) ⟨97898, by rfl⟩ : syracuseStep 130531 = 195797) B195797
theorem B196067 : Blo 127788 196067 := bstep (se 1 (by rfl) ⟨147050, by rfl⟩ : syracuseStep 196067 = 294101) B294101
theorem B294371 : Blo 127788 294371 := bstep (se 1 (by rfl) ⟨220778, by rfl⟩ : syracuseStep 294371 = 441557) B441557
theorem B130547 : Blo 127788 130547 := bstep (se 1 (by rfl) ⟨97910, by rfl⟩ : syracuseStep 130547 = 195821) B195821
theorem B196097 : Blo 127788 196097 := bstep (se 2 (by rfl) ⟨73536, by rfl⟩ : syracuseStep 196097 = 147073) B147073
theorem B130563 : Blo 127788 130563 := bstep (se 1 (by rfl) ⟨97922, by rfl⟩ : syracuseStep 130563 = 195845) B195845
theorem B130579 : Blo 127788 130579 := bstep (se 1 (by rfl) ⟨97934, by rfl⟩ : syracuseStep 130579 = 195869) B195869
theorem B196115 : Blo 127788 196115 := bstep (se 1 (by rfl) ⟨147086, by rfl⟩ : syracuseStep 196115 = 294173) B294173
theorem B130595 : Blo 127788 130595 := bstep (se 1 (by rfl) ⟨97946, by rfl⟩ : syracuseStep 130595 = 195893) B195893
theorem B196145 : Blo 127788 196145 := bstep (se 2 (by rfl) ⟨73554, by rfl⟩ : syracuseStep 196145 = 147109) B147109
theorem B130611 : Blo 127788 130611 := bstep (se 1 (by rfl) ⟨97958, by rfl⟩ : syracuseStep 130611 = 195917) B195917
theorem B130627 : Blo 127788 130627 := bstep (se 1 (by rfl) ⟨97970, by rfl⟩ : syracuseStep 130627 = 195941) B195941
theorem B196163 : Blo 127788 196163 := bstep (se 1 (by rfl) ⟨147122, by rfl⟩ : syracuseStep 196163 = 294245) B294245
theorem B130643 : Blo 127788 130643 := bstep (se 1 (by rfl) ⟨97982, by rfl⟩ : syracuseStep 130643 = 195965) B195965
theorem B196193 : Blo 127788 196193 := bstep (se 2 (by rfl) ⟨73572, by rfl⟩ : syracuseStep 196193 = 147145) B147145
theorem B130659 : Blo 127788 130659 := bstep (se 1 (by rfl) ⟨97994, by rfl⟩ : syracuseStep 130659 = 195989) B195989
theorem B130675 : Blo 127788 130675 := bstep (se 1 (by rfl) ⟨98006, by rfl⟩ : syracuseStep 130675 = 196013) B196013
theorem B196211 : Blo 127788 196211 := bstep (se 1 (by rfl) ⟨147158, by rfl⟩ : syracuseStep 196211 = 294317) B294317
theorem B130691 : Blo 127788 130691 := bstep (se 1 (by rfl) ⟨98018, by rfl⟩ : syracuseStep 130691 = 196037) B196037
theorem B196241 : Blo 127788 196241 := bstep (se 2 (by rfl) ⟨73590, by rfl⟩ : syracuseStep 196241 = 147181) B147181
theorem B130707 : Blo 127788 130707 := bstep (se 1 (by rfl) ⟨98030, by rfl⟩ : syracuseStep 130707 = 196061) B196061
theorem B130723 : Blo 127788 130723 := bstep (se 1 (by rfl) ⟨98042, by rfl⟩ : syracuseStep 130723 = 196085) B196085
theorem B196259 : Blo 127788 196259 := bstep (se 1 (by rfl) ⟨147194, by rfl⟩ : syracuseStep 196259 = 294389) B294389
theorem B130739 : Blo 127788 130739 := bstep (se 1 (by rfl) ⟨98054, by rfl⟩ : syracuseStep 130739 = 196109) B196109
theorem B196289 : Blo 127788 196289 := bstep (se 2 (by rfl) ⟨73608, by rfl⟩ : syracuseStep 196289 = 147217) B147217
theorem B130755 : Blo 127788 130755 := bstep (se 1 (by rfl) ⟨98066, by rfl⟩ : syracuseStep 130755 = 196133) B196133
theorem B130771 : Blo 127788 130771 := bstep (se 1 (by rfl) ⟨98078, by rfl⟩ : syracuseStep 130771 = 196157) B196157
theorem B196307 : Blo 127788 196307 := bstep (se 1 (by rfl) ⟨147230, by rfl⟩ : syracuseStep 196307 = 294461) B294461
theorem B130787 : Blo 127788 130787 := bstep (se 1 (by rfl) ⟨98090, by rfl⟩ : syracuseStep 130787 = 196181) B196181
theorem B196337 : Blo 127788 196337 := bstep (se 2 (by rfl) ⟨73626, by rfl⟩ : syracuseStep 196337 = 147253) B147253
theorem B294641 : Blo 127788 294641 := bstep (se 2 (by rfl) ⟨110490, by rfl⟩ : syracuseStep 294641 = 220981) B220981
theorem B130803 : Blo 127788 130803 := bstep (se 1 (by rfl) ⟨98102, by rfl⟩ : syracuseStep 130803 = 196205) B196205
theorem B130819 : Blo 127788 130819 := bstep (se 1 (by rfl) ⟨98114, by rfl⟩ : syracuseStep 130819 = 196229) B196229
theorem B196355 : Blo 127788 196355 := bstep (se 1 (by rfl) ⟨147266, by rfl⟩ : syracuseStep 196355 = 294533) B294533
theorem B294659 : Blo 127788 294659 := bstep (se 1 (by rfl) ⟨220994, by rfl⟩ : syracuseStep 294659 = 441989) B441989
theorem B130835 : Blo 127788 130835 := bstep (se 1 (by rfl) ⟨98126, by rfl⟩ : syracuseStep 130835 = 196253) B196253
theorem B196385 : Blo 127788 196385 := bstep (se 2 (by rfl) ⟨73644, by rfl⟩ : syracuseStep 196385 = 147289) B147289
theorem B130851 : Blo 127788 130851 := bstep (se 1 (by rfl) ⟨98138, by rfl⟩ : syracuseStep 130851 = 196277) B196277
theorem B327473 : Blo 127788 327473 := bstep (se 2 (by rfl) ⟨122802, by rfl⟩ : syracuseStep 327473 = 245605) B245605
theorem B130867 : Blo 127788 130867 := bstep (se 1 (by rfl) ⟨98150, by rfl⟩ : syracuseStep 130867 = 196301) B196301
theorem B196403 : Blo 127788 196403 := bstep (se 1 (by rfl) ⟨147302, by rfl⟩ : syracuseStep 196403 = 294605) B294605
theorem B130883 : Blo 127788 130883 := bstep (se 1 (by rfl) ⟨98162, by rfl⟩ : syracuseStep 130883 = 196325) B196325
theorem B196433 : Blo 127788 196433 := bstep (se 2 (by rfl) ⟨73662, by rfl⟩ : syracuseStep 196433 = 147325) B147325
theorem B130899 : Blo 127788 130899 := bstep (se 1 (by rfl) ⟨98174, by rfl⟩ : syracuseStep 130899 = 196349) B196349
theorem B327523 : Blo 127788 327523 := bstep (se 1 (by rfl) ⟨245642, by rfl⟩ : syracuseStep 327523 = 491285) B491285
theorem B130915 : Blo 127788 130915 := bstep (se 1 (by rfl) ⟨98186, by rfl⟩ : syracuseStep 130915 = 196373) B196373
theorem B196451 : Blo 127788 196451 := bstep (se 1 (by rfl) ⟨147338, by rfl⟩ : syracuseStep 196451 = 294677) B294677
theorem B130931 : Blo 127788 130931 := bstep (se 1 (by rfl) ⟨98198, by rfl⟩ : syracuseStep 130931 = 196397) B196397
theorem B196481 : Blo 127788 196481 := bstep (se 2 (by rfl) ⟨73680, by rfl⟩ : syracuseStep 196481 = 147361) B147361
theorem B130947 : Blo 127788 130947 := bstep (se 1 (by rfl) ⟨98210, by rfl⟩ : syracuseStep 130947 = 196421) B196421
theorem B425873 : Blo 127788 425873 := bstep (se 2 (by rfl) ⟨159702, by rfl⟩ : syracuseStep 425873 = 319405) B319405
theorem B130963 : Blo 127788 130963 := bstep (se 1 (by rfl) ⟨98222, by rfl⟩ : syracuseStep 130963 = 196445) B196445
theorem B196499 : Blo 127788 196499 := bstep (se 1 (by rfl) ⟨147374, by rfl⟩ : syracuseStep 196499 = 294749) B294749
theorem B130979 : Blo 127788 130979 := bstep (se 1 (by rfl) ⟨98234, by rfl⟩ : syracuseStep 130979 = 196469) B196469
theorem B393133 : Blo 127788 393133 := bstep (se 3 (by rfl) ⟨73712, by rfl⟩ : syracuseStep 393133 = 147425) B147425
theorem B196529 : Blo 127788 196529 := bstep (se 2 (by rfl) ⟨73698, by rfl⟩ : syracuseStep 196529 = 147397) B147397
theorem B130995 : Blo 127788 130995 := bstep (se 1 (by rfl) ⟨98246, by rfl⟩ : syracuseStep 130995 = 196493) B196493
theorem B131011 : Blo 127788 131011 := bstep (se 1 (by rfl) ⟨98258, by rfl⟩ : syracuseStep 131011 = 196517) B196517
theorem B196547 : Blo 127788 196547 := bstep (se 1 (by rfl) ⟨147410, by rfl⟩ : syracuseStep 196547 = 294821) B294821
theorem B131027 : Blo 127788 131027 := bstep (se 1 (by rfl) ⟨98270, by rfl⟩ : syracuseStep 131027 = 196541) B196541
theorem B196577 : Blo 127788 196577 := bstep (se 2 (by rfl) ⟨73716, by rfl⟩ : syracuseStep 196577 = 147433) B147433
theorem B458723 : Blo 127788 458723 := bstep (se 1 (by rfl) ⟨344042, by rfl⟩ : syracuseStep 458723 = 688085) B688085
theorem B131043 : Blo 127788 131043 := bstep (se 1 (by rfl) ⟨98282, by rfl⟩ : syracuseStep 131043 = 196565) B196565
theorem B327665 : Blo 127788 327665 := bstep (se 2 (by rfl) ⟨122874, by rfl⟩ : syracuseStep 327665 = 245749) B245749
theorem B131059 : Blo 127788 131059 := bstep (se 1 (by rfl) ⟨98294, by rfl⟩ : syracuseStep 131059 = 196589) B196589
theorem B196595 : Blo 127788 196595 := bstep (se 1 (by rfl) ⟨147446, by rfl⟩ : syracuseStep 196595 = 294893) B294893
theorem B196619 : Blo 127788 196619 := bstep (se 1 (by rfl) ⟨147464, by rfl⟩ : syracuseStep 196619 = 294929) B294929
theorem B131083 : Blo 127788 131083 := bstep (se 1 (by rfl) ⟨98312, by rfl⟩ : syracuseStep 131083 = 196625) B196625
theorem B196631 : Blo 127788 196631 := bstep (se 1 (by rfl) ⟨147473, by rfl⟩ : syracuseStep 196631 = 294947) B294947
theorem B131095 : Blo 127788 131095 := bstep (se 1 (by rfl) ⟨98321, by rfl⟩ : syracuseStep 131095 = 196643) B196643
theorem B131115 : Blo 127788 131115 := bstep (se 1 (by rfl) ⟨98336, by rfl⟩ : syracuseStep 131115 = 196673) B196673
theorem B131127 : Blo 127788 131127 := bstep (se 1 (by rfl) ⟨98345, by rfl⟩ : syracuseStep 131127 = 196691) B196691
theorem B131147 : Blo 127788 131147 := bstep (se 1 (by rfl) ⟨98360, by rfl⟩ : syracuseStep 131147 = 196721) B196721
theorem B131159 : Blo 127788 131159 := bstep (se 1 (by rfl) ⟨98369, by rfl⟩ : syracuseStep 131159 = 196739) B196739
theorem B295001 : Blo 127788 295001 := bstep (se 2 (by rfl) ⟨110625, by rfl⟩ : syracuseStep 295001 = 221251) B221251
theorem B196697 : Blo 127788 196697 := bstep (se 2 (by rfl) ⟨73761, by rfl⟩ : syracuseStep 196697 = 147523) B147523
theorem B131179 : Blo 127788 131179 := bstep (se 1 (by rfl) ⟨98384, by rfl⟩ : syracuseStep 131179 = 196769) B196769
theorem B131191 : Blo 127788 131191 := bstep (se 1 (by rfl) ⟨98393, by rfl⟩ : syracuseStep 131191 = 196787) B196787
theorem B131211 : Blo 127788 131211 := bstep (se 1 (by rfl) ⟨98408, by rfl⟩ : syracuseStep 131211 = 196817) B196817
theorem B131223 : Blo 127788 131223 := bstep (se 1 (by rfl) ⟨98417, by rfl⟩ : syracuseStep 131223 = 196835) B196835
theorem B131243 : Blo 127788 131243 := bstep (se 1 (by rfl) ⟨98432, by rfl⟩ : syracuseStep 131243 = 196865) B196865
theorem B295091 : Blo 127788 295091 := bstep (se 1 (by rfl) ⟨221318, by rfl⟩ : syracuseStep 295091 = 442637) B442637
theorem B131255 : Blo 127788 131255 := bstep (se 1 (by rfl) ⟨98441, by rfl⟩ : syracuseStep 131255 = 196883) B196883
theorem B196811 : Blo 127788 196811 := bstep (se 1 (by rfl) ⟨147608, by rfl⟩ : syracuseStep 196811 = 295217) B295217
theorem B131275 : Blo 127788 131275 := bstep (se 1 (by rfl) ⟨98456, by rfl⟩ : syracuseStep 131275 = 196913) B196913
theorem B295127 : Blo 127788 295127 := bstep (se 1 (by rfl) ⟨221345, by rfl⟩ : syracuseStep 295127 = 442691) B442691
theorem B196823 : Blo 127788 196823 := bstep (se 1 (by rfl) ⟨147617, by rfl⟩ : syracuseStep 196823 = 295235) B295235
theorem B131287 : Blo 127788 131287 := bstep (se 1 (by rfl) ⟨98465, by rfl⟩ : syracuseStep 131287 = 196931) B196931
theorem B491741 : Blo 127788 491741 := bstep (se 3 (by rfl) ⟨92201, by rfl⟩ : syracuseStep 491741 = 184403) B184403
theorem B131307 : Blo 127788 131307 := bstep (se 1 (by rfl) ⟨98480, by rfl⟩ : syracuseStep 131307 = 196961) B196961
theorem B131319 : Blo 127788 131319 := bstep (se 1 (by rfl) ⟨98489, by rfl⟩ : syracuseStep 131319 = 196979) B196979
theorem B131339 : Blo 127788 131339 := bstep (se 1 (by rfl) ⟨98504, by rfl⟩ : syracuseStep 131339 = 197009) B197009
theorem B327959 : Blo 127788 327959 := bstep (se 1 (by rfl) ⟨245969, by rfl⟩ : syracuseStep 327959 = 491939) B491939
theorem B131351 : Blo 127788 131351 := bstep (se 1 (by rfl) ⟨98513, by rfl⟩ : syracuseStep 131351 = 197027) B197027
theorem B196889 : Blo 127788 196889 := bstep (se 2 (by rfl) ⟨73833, by rfl⟩ : syracuseStep 196889 = 147667) B147667
theorem B131371 : Blo 127788 131371 := bstep (se 1 (by rfl) ⟨98528, by rfl⟩ : syracuseStep 131371 = 197057) B197057
theorem B131383 : Blo 127788 131383 := bstep (se 1 (by rfl) ⟨98537, by rfl⟩ : syracuseStep 131383 = 197075) B197075
theorem B131403 : Blo 127788 131403 := bstep (se 1 (by rfl) ⟨98552, by rfl⟩ : syracuseStep 131403 = 197105) B197105
theorem B131415 : Blo 127788 131415 := bstep (se 1 (by rfl) ⟨98561, by rfl⟩ : syracuseStep 131415 = 197123) B197123
theorem B131435 : Blo 127788 131435 := bstep (se 1 (by rfl) ⟨98576, by rfl⟩ : syracuseStep 131435 = 197153) B197153
theorem B131447 : Blo 127788 131447 := bstep (se 1 (by rfl) ⟨98585, by rfl⟩ : syracuseStep 131447 = 197171) B197171
theorem B295307 : Blo 127788 295307 := bstep (se 1 (by rfl) ⟨221480, by rfl⟩ : syracuseStep 295307 = 442961) B442961
theorem B197003 : Blo 127788 197003 := bstep (se 1 (by rfl) ⟨147752, by rfl⟩ : syracuseStep 197003 = 295505) B295505
theorem B131467 : Blo 127788 131467 := bstep (se 1 (by rfl) ⟨98600, by rfl⟩ : syracuseStep 131467 = 197201) B197201
theorem B197015 : Blo 127788 197015 := bstep (se 1 (by rfl) ⟨147761, by rfl⟩ : syracuseStep 197015 = 295523) B295523
theorem B131479 : Blo 127788 131479 := bstep (se 1 (by rfl) ⟨98609, by rfl⟩ : syracuseStep 131479 = 197219) B197219
theorem B131499 : Blo 127788 131499 := bstep (se 1 (by rfl) ⟨98624, by rfl⟩ : syracuseStep 131499 = 197249) B197249
theorem B131511 : Blo 127788 131511 := bstep (se 1 (by rfl) ⟨98633, by rfl⟩ : syracuseStep 131511 = 197267) B197267
theorem B295361 : Blo 127788 295361 := bstep (se 2 (by rfl) ⟨110760, by rfl⟩ : syracuseStep 295361 = 221521) B221521
theorem B131531 : Blo 127788 131531 := bstep (se 1 (by rfl) ⟨98648, by rfl⟩ : syracuseStep 131531 = 197297) B197297
theorem B131543 : Blo 127788 131543 := bstep (se 1 (by rfl) ⟨98657, by rfl⟩ : syracuseStep 131543 = 197315) B197315
theorem B197081 : Blo 127788 197081 := bstep (se 2 (by rfl) ⟨73905, by rfl⟩ : syracuseStep 197081 = 147811) B147811
theorem B131563 : Blo 127788 131563 := bstep (se 1 (by rfl) ⟨98672, by rfl⟩ : syracuseStep 131563 = 197345) B197345
theorem B131575 : Blo 127788 131575 := bstep (se 1 (by rfl) ⟨98681, by rfl⟩ : syracuseStep 131575 = 197363) B197363
theorem B131595 : Blo 127788 131595 := bstep (se 1 (by rfl) ⟨98696, by rfl⟩ : syracuseStep 131595 = 197393) B197393
theorem B131607 : Blo 127788 131607 := bstep (se 1 (by rfl) ⟨98705, by rfl⟩ : syracuseStep 131607 = 197411) B197411
theorem B131627 : Blo 127788 131627 := bstep (se 1 (by rfl) ⟨98720, by rfl⟩ : syracuseStep 131627 = 197441) B197441
theorem B131639 : Blo 127788 131639 := bstep (se 1 (by rfl) ⟨98729, by rfl⟩ : syracuseStep 131639 = 197459) B197459
theorem B655937 : Blo 127788 655937 := bstep (se 2 (by rfl) ⟨245976, by rfl⟩ : syracuseStep 655937 = 491953) B491953
theorem B197195 : Blo 127788 197195 := bstep (se 1 (by rfl) ⟨147896, by rfl⟩ : syracuseStep 197195 = 295793) B295793
theorem B131659 : Blo 127788 131659 := bstep (se 1 (by rfl) ⟨98744, by rfl⟩ : syracuseStep 131659 = 197489) B197489
theorem B197207 : Blo 127788 197207 := bstep (se 1 (by rfl) ⟨147905, by rfl⟩ : syracuseStep 197207 = 295811) B295811
theorem B131671 : Blo 127788 131671 := bstep (se 1 (by rfl) ⟨98753, by rfl⟩ : syracuseStep 131671 = 197507) B197507
theorem B131691 : Blo 127788 131691 := bstep (se 1 (by rfl) ⟨98768, by rfl⟩ : syracuseStep 131691 = 197537) B197537
theorem B131703 : Blo 127788 131703 := bstep (se 1 (by rfl) ⟨98777, by rfl⟩ : syracuseStep 131703 = 197555) B197555
theorem B131723 : Blo 127788 131723 := bstep (se 1 (by rfl) ⟨98792, by rfl⟩ : syracuseStep 131723 = 197585) B197585
theorem B131735 : Blo 127788 131735 := bstep (se 1 (by rfl) ⟨98801, by rfl⟩ : syracuseStep 131735 = 197603) B197603
theorem B295577 : Blo 127788 295577 := bstep (se 2 (by rfl) ⟨110841, by rfl⟩ : syracuseStep 295577 = 221683) B221683
theorem B197273 : Blo 127788 197273 := bstep (se 2 (by rfl) ⟨73977, by rfl⟩ : syracuseStep 197273 = 147955) B147955
theorem B131755 : Blo 127788 131755 := bstep (se 1 (by rfl) ⟨98816, by rfl⟩ : syracuseStep 131755 = 197633) B197633
theorem B131767 : Blo 127788 131767 := bstep (se 1 (by rfl) ⟨98825, by rfl⟩ : syracuseStep 131767 = 197651) B197651
theorem B131787 : Blo 127788 131787 := bstep (se 1 (by rfl) ⟨98840, by rfl⟩ : syracuseStep 131787 = 197681) B197681
theorem B295667 : Blo 127788 295667 := bstep (se 1 (by rfl) ⟨221750, by rfl⟩ : syracuseStep 295667 = 443501) B443501
theorem B197387 : Blo 127788 197387 := bstep (se 1 (by rfl) ⟨148040, by rfl⟩ : syracuseStep 197387 = 296081) B296081
theorem B295703 : Blo 127788 295703 := bstep (se 1 (by rfl) ⟨221777, by rfl⟩ : syracuseStep 295703 = 443555) B443555
theorem B197399 : Blo 127788 197399 := bstep (se 1 (by rfl) ⟨148049, by rfl⟩ : syracuseStep 197399 = 296099) B296099
theorem B164683 : Blo 127788 164683 := bstep (se 1 (by rfl) ⟨123512, by rfl⟩ : syracuseStep 164683 = 247025) B247025
theorem B197465 : Blo 127788 197465 := bstep (se 2 (by rfl) ⟨74049, by rfl⟩ : syracuseStep 197465 = 148099) B148099
theorem B590723 : Blo 127788 590723 := bstep (se 1 (by rfl) ⟨443042, by rfl⟩ : syracuseStep 590723 = 886085) B886085
theorem B492439 : Blo 127788 492439 := bstep (se 1 (by rfl) ⟨369329, by rfl⟩ : syracuseStep 492439 = 738659) B738659
theorem B295883 : Blo 127788 295883 := bstep (se 1 (by rfl) ⟨221912, by rfl⟩ : syracuseStep 295883 = 443825) B443825
theorem B197579 : Blo 127788 197579 := bstep (se 1 (by rfl) ⟨148184, by rfl⟩ : syracuseStep 197579 = 296369) B296369
theorem B197591 : Blo 127788 197591 := bstep (se 1 (by rfl) ⟨148193, by rfl⟩ : syracuseStep 197591 = 296387) B296387
theorem B295937 : Blo 127788 295937 := bstep (se 2 (by rfl) ⟨110976, by rfl⟩ : syracuseStep 295937 = 221953) B221953
theorem B197657 : Blo 127788 197657 := bstep (se 2 (by rfl) ⟨74121, by rfl⟩ : syracuseStep 197657 = 148243) B148243
theorem B328769 : Blo 127788 328769 := bstep (se 2 (by rfl) ⟨123288, by rfl⟩ : syracuseStep 328769 = 246577) B246577
theorem B296153 : Blo 127788 296153 := bstep (se 2 (by rfl) ⟨111057, by rfl⟩ : syracuseStep 296153 = 222115) B222115
theorem B558353 : Blo 127788 558353 := bstep (se 2 (by rfl) ⟨209382, by rfl⟩ : syracuseStep 558353 = 418765) B418765
theorem B296243 : Blo 127788 296243 := bstep (se 1 (by rfl) ⟨222182, by rfl⟩ : syracuseStep 296243 = 444365) B444365
theorem B296279 : Blo 127788 296279 := bstep (se 1 (by rfl) ⟨222209, by rfl⟩ : syracuseStep 296279 = 444419) B444419
theorem B296459 : Blo 127788 296459 := bstep (se 1 (by rfl) ⟨222344, by rfl⟩ : syracuseStep 296459 = 444689) B444689
theorem B296513 : Blo 127788 296513 := bstep (se 2 (by rfl) ⟨111192, by rfl⟩ : syracuseStep 296513 = 222385) B222385
theorem B329305 : Blo 127788 329305 := bstep (se 2 (by rfl) ⟨123489, by rfl⟩ : syracuseStep 329305 = 246979) B246979
theorem B493229 : Blo 127788 493229 := bstep (se 3 (by rfl) ⟨92480, by rfl⟩ : syracuseStep 493229 = 184961) B184961
theorem B493249 : Blo 127788 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B263873 : Blo 127788 263873 := bstep (se 2 (by rfl) ⟨98952, by rfl⟩ : syracuseStep 263873 = 197905) B197905
theorem B3835633 : Blo 127788 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B165655 : Blo 127788 165655 := bstep (se 1 (by rfl) ⟨124241, by rfl⟩ : syracuseStep 165655 = 248483) B248483
theorem B263987 : Blo 127788 263987 := bstep (se 1 (by rfl) ⟨197990, by rfl⟩ : syracuseStep 263987 = 395981) B395981
theorem B559325 : Blo 127788 559325 := bstep (se 3 (by rfl) ⟨104873, by rfl⟩ : syracuseStep 559325 = 209747) B209747
theorem B461207 : Blo 127788 461207 := bstep (se 1 (by rfl) ⟨345905, by rfl⟩ : syracuseStep 461207 = 691811) B691811
theorem B526771 : Blo 127788 526771 := bstep (se 1 (by rfl) ⟨395078, by rfl⟩ : syracuseStep 526771 = 790157) B790157
theorem B657881 : Blo 127788 657881 := bstep (se 2 (by rfl) ⟨246705, by rfl⟩ : syracuseStep 657881 = 493411) B493411
theorem B231959 : Blo 127788 231959 := bstep (se 1 (by rfl) ⟨173969, by rfl⟩ : syracuseStep 231959 = 347939) B347939
theorem B1116737 : Blo 127788 1116737 := bstep (se 2 (by rfl) ⟨418776, by rfl⟩ : syracuseStep 1116737 = 837553) B837553
theorem B166475 : Blo 127788 166475 := bstep (se 1 (by rfl) ⟨124856, by rfl⟩ : syracuseStep 166475 = 249713) B249713
theorem B297623 : Blo 127788 297623 := bstep (se 1 (by rfl) ⟨223217, by rfl⟩ : syracuseStep 297623 = 446435) B446435
theorem B330419 : Blo 127788 330419 := bstep (se 1 (by rfl) ⟨247814, by rfl⟩ : syracuseStep 330419 = 495629) B495629
theorem B297881 : Blo 127788 297881 := bstep (se 2 (by rfl) ⟨111705, by rfl⟩ : syracuseStep 297881 = 223411) B223411
theorem B330713 : Blo 127788 330713 := bstep (se 2 (by rfl) ⟨124017, by rfl⟩ : syracuseStep 330713 = 248035) B248035
theorem B494657 : Blo 127788 494657 := bstep (se 2 (by rfl) ⟨185496, by rfl⟩ : syracuseStep 494657 = 370993) B370993
theorem B462131 : Blo 127788 462131 := bstep (se 1 (by rfl) ⟨346598, by rfl⟩ : syracuseStep 462131 = 693197) B693197
theorem B527809 : Blo 127788 527809 := bstep (se 2 (by rfl) ⟨197928, by rfl⟩ : syracuseStep 527809 = 395857) B395857
theorem B232961 : Blo 127788 232961 := bstep (se 2 (by rfl) ⟨87360, by rfl⟩ : syracuseStep 232961 = 174721) B174721
theorem B593497 : Blo 127788 593497 := bstep (se 2 (by rfl) ⟨222561, by rfl⟩ : syracuseStep 593497 = 445123) B445123
theorem B659501 : Blo 127788 659501 := bstep (se 3 (by rfl) ⟨123656, by rfl⟩ : syracuseStep 659501 = 247313) B247313
theorem B364637 : Blo 127788 364637 := bstep (se 3 (by rfl) ⟨68369, by rfl⟩ : syracuseStep 364637 = 136739) B136739
theorem B692545 : Blo 127788 692545 := bstep (se 2 (by rfl) ⟨259704, by rfl⟩ : syracuseStep 692545 = 519409) B519409
theorem B364979 : Blo 127788 364979 := bstep (se 1 (by rfl) ⟨273734, by rfl⟩ : syracuseStep 364979 = 547469) B547469
theorem B463283 : Blo 127788 463283 := bstep (se 1 (by rfl) ⟨347462, by rfl⟩ : syracuseStep 463283 = 694925) B694925
theorem B496145 : Blo 127788 496145 := bstep (se 2 (by rfl) ⟨186054, by rfl⟩ : syracuseStep 496145 = 372109) B372109
theorem B299585 : Blo 127788 299585 := bstep (se 2 (by rfl) ⟨112344, by rfl⟩ : syracuseStep 299585 = 224689) B224689
theorem B332363 : Blo 127788 332363 := bstep (se 1 (by rfl) ⟨249272, by rfl⟩ : syracuseStep 332363 = 498545) B498545
theorem B496331 : Blo 127788 496331 := bstep (se 1 (by rfl) ⟨372248, by rfl⟩ : syracuseStep 496331 = 744497) B744497
theorem B561923 : Blo 127788 561923 := bstep (se 1 (by rfl) ⟨421442, by rfl⟩ : syracuseStep 561923 = 842885) B842885
theorem B496601 : Blo 127788 496601 := bstep (se 2 (by rfl) ⟨186225, by rfl⟩ : syracuseStep 496601 = 372451) B372451
theorem B791569 : Blo 127788 791569 := bstep (se 2 (by rfl) ⟨296838, by rfl⟩ : syracuseStep 791569 = 593677) B593677
theorem B562265 : Blo 127788 562265 := bstep (se 2 (by rfl) ⟨210849, by rfl⟩ : syracuseStep 562265 = 421699) B421699
theorem B496813 : Blo 127788 496813 := bstep (se 3 (by rfl) ⟨93152, by rfl⟩ : syracuseStep 496813 = 186305) B186305
theorem B431297 : Blo 127788 431297 := bstep (se 2 (by rfl) ⟨161736, by rfl⟩ : syracuseStep 431297 = 323473) B323473
theorem B201943 : Blo 127788 201943 := bstep (se 1 (by rfl) ⟨151457, by rfl⟩ : syracuseStep 201943 = 302915) B302915
theorem B791909 : Blo 127788 791909 := bstep (se 4 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 791909 = 148483) B148483
theorem B497117 : Blo 127788 497117 := bstep (se 3 (by rfl) ⟨93209, by rfl⟩ : syracuseStep 497117 = 186419) B186419
theorem B333335 : Blo 127788 333335 := bstep (se 1 (by rfl) ⟨250001, by rfl⟩ : syracuseStep 333335 = 500003) B500003
theorem B431837 : Blo 127788 431837 := bstep (se 3 (by rfl) ⟨80969, by rfl⟩ : syracuseStep 431837 = 161939) B161939
theorem B1382321 : Blo 127788 1382321 := bstep (se 2 (by rfl) ⟨518370, by rfl⟩ : syracuseStep 1382321 = 1036741) B1036741
theorem B202775 : Blo 127788 202775 := bstep (se 1 (by rfl) ⟨152081, by rfl⟩ : syracuseStep 202775 = 304163) B304163
theorem B399581 : Blo 127788 399581 := bstep (se 3 (by rfl) ⟨74921, by rfl⟩ : syracuseStep 399581 = 149843) B149843
theorem B465473 : Blo 127788 465473 := bstep (se 2 (by rfl) ⟨174552, by rfl⟩ : syracuseStep 465473 = 349105) B349105
theorem B367325 : Blo 127788 367325 := bstep (se 3 (by rfl) ⟨68873, by rfl⟩ : syracuseStep 367325 = 137747) B137747
theorem B629549 : Blo 127788 629549 := bstep (se 3 (by rfl) ⟨118040, by rfl⟩ : syracuseStep 629549 = 236081) B236081
theorem B432971 : Blo 127788 432971 := bstep (se 1 (by rfl) ⟨324728, by rfl⟩ : syracuseStep 432971 = 649457) B649457
theorem B236363 : Blo 127788 236363 := bstep (se 1 (by rfl) ⟨177272, by rfl⟩ : syracuseStep 236363 = 354545) B354545
theorem B891749 : Blo 127788 891749 := bstep (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) B167203
theorem B367553 : Blo 127788 367553 := bstep (se 2 (by rfl) ⟨137832, by rfl⟩ : syracuseStep 367553 = 275665) B275665
theorem B662573 : Blo 127788 662573 := bstep (se 3 (by rfl) ⟨124232, by rfl⟩ : syracuseStep 662573 = 248465) B248465
theorem B433241 : Blo 127788 433241 := bstep (se 2 (by rfl) ⟨162465, by rfl⟩ : syracuseStep 433241 = 324931) B324931
theorem B367895 : Blo 127788 367895 := bstep (se 1 (by rfl) ⟨275921, by rfl⟩ : syracuseStep 367895 = 551843) B551843
theorem B466397 : Blo 127788 466397 := bstep (se 3 (by rfl) ⟨87449, by rfl⟩ : syracuseStep 466397 = 174899) B174899
theorem B892433 : Blo 127788 892433 := bstep (se 2 (by rfl) ⟨334662, by rfl⟩ : syracuseStep 892433 = 669325) B669325
theorem B138871 : Blo 127788 138871 := bstep (se 1 (by rfl) ⟨104153, by rfl⟩ : syracuseStep 138871 = 208307) B208307
theorem B433943 : Blo 127788 433943 := bstep (se 1 (by rfl) ⟨325457, by rfl⟩ : syracuseStep 433943 = 650915) B650915
theorem B2826049 : Blo 127788 2826049 := bstep (se 2 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 2826049 = 2119537) B2119537
theorem B663389 : Blo 127788 663389 := bstep (se 3 (by rfl) ⟨124385, by rfl⟩ : syracuseStep 663389 = 248771) B248771
theorem B499715 : Blo 127788 499715 := bstep (se 1 (by rfl) ⟨374786, by rfl⟩ : syracuseStep 499715 = 749573) B749573
theorem B499729 : Blo 127788 499729 := bstep (se 2 (by rfl) ⟨187398, by rfl⟩ : syracuseStep 499729 = 374797) B374797
theorem B139415 : Blo 127788 139415 := bstep (se 1 (by rfl) ⟨104561, by rfl⟩ : syracuseStep 139415 = 209123) B209123
theorem B630935 : Blo 127788 630935 := bstep (se 1 (by rfl) ⟨473201, by rfl⟩ : syracuseStep 630935 = 946403) B946403
theorem B434483 : Blo 127788 434483 := bstep (se 1 (by rfl) ⟨325862, by rfl⟩ : syracuseStep 434483 = 651725) B651725
theorem B500033 : Blo 127788 500033 := bstep (se 2 (by rfl) ⟨187512, by rfl⟩ : syracuseStep 500033 = 375025) B375025
theorem B139691 : Blo 127788 139691 := bstep (se 1 (by rfl) ⟨104768, by rfl⟩ : syracuseStep 139691 = 209537) B209537
theorem B1122821 : Blo 127788 1122821 := bstep (se 4 (by rfl) ⟨105264, by rfl⟩ : syracuseStep 1122821 = 210529) B210529
theorem B434753 : Blo 127788 434753 := bstep (se 2 (by rfl) ⟨163032, by rfl⟩ : syracuseStep 434753 = 326065) B326065
theorem B598603 : Blo 127788 598603 := bstep (se 1 (by rfl) ⟨448952, by rfl⟩ : syracuseStep 598603 = 897905) B897905
theorem B467549 : Blo 127788 467549 := bstep (se 3 (by rfl) ⟨87665, by rfl⟩ : syracuseStep 467549 = 175331) B175331
theorem B435293 : Blo 127788 435293 := bstep (se 3 (by rfl) ⟨81617, by rfl⟩ : syracuseStep 435293 = 163235) B163235
theorem B828737 : Blo 127788 828737 := bstep (se 2 (by rfl) ⟨310776, by rfl⟩ : syracuseStep 828737 = 621553) B621553
theorem B173515 : Blo 127788 173515 := bstep (se 1 (by rfl) ⟨130136, by rfl⟩ : syracuseStep 173515 = 260273) B260273
theorem B370241 : Blo 127788 370241 := bstep (se 2 (by rfl) ⟨138840, by rfl⟩ : syracuseStep 370241 = 277681) B277681
theorem B665495 : Blo 127788 665495 := bstep (se 1 (by rfl) ⟨499121, by rfl⟩ : syracuseStep 665495 = 998243) B998243
theorem B370777 : Blo 127788 370777 := bstep (se 2 (by rfl) ⟨139041, by rfl⟩ : syracuseStep 370777 = 278083) B278083
theorem B600209 : Blo 127788 600209 := bstep (se 2 (by rfl) ⟨225078, by rfl⟩ : syracuseStep 600209 = 450157) B450157
theorem B436427 : Blo 127788 436427 := bstep (se 1 (by rfl) ⟨327320, by rfl⟩ : syracuseStep 436427 = 654641) B654641
theorem B207127 : Blo 127788 207127 := bstep (se 1 (by rfl) ⟨155345, by rfl⟩ : syracuseStep 207127 = 310691) B310691
theorem B436697 : Blo 127788 436697 := bstep (se 2 (by rfl) ⟨163761, by rfl⟩ : syracuseStep 436697 = 327523) B327523
theorem B272983 : Blo 127788 272983 := bstep (se 1 (by rfl) ⟨204737, by rfl⟩ : syracuseStep 272983 = 409475) B409475
theorem B1223261 : Blo 127788 1223261 := bstep (se 3 (by rfl) ⟨229361, by rfl⟩ : syracuseStep 1223261 = 458723) B458723
theorem B141931 : Blo 127788 141931 := bstep (se 1 (by rfl) ⟨106448, by rfl⟩ : syracuseStep 141931 = 212897) B212897
theorem B437399 : Blo 127788 437399 := bstep (se 1 (by rfl) ⟨328049, by rfl⟩ : syracuseStep 437399 = 656099) B656099
theorem B470195 : Blo 127788 470195 := bstep (se 1 (by rfl) ⟨352646, by rfl⟩ : syracuseStep 470195 = 705293) B705293
theorem B142571 : Blo 127788 142571 := bstep (se 1 (by rfl) ⟨106928, by rfl⟩ : syracuseStep 142571 = 213857) B213857
theorem B1682693 : Blo 127788 1682693 := bstep (se 4 (by rfl) ⟨157752, by rfl⟩ : syracuseStep 1682693 = 315505) B315505
theorem B732509 : Blo 127788 732509 := bstep (se 3 (by rfl) ⟨137345, by rfl⟩ : syracuseStep 732509 = 274691) B274691
theorem B699749 : Blo 127788 699749 := bstep (se 4 (by rfl) ⟨65601, by rfl⟩ : syracuseStep 699749 = 131203) B131203
theorem B1584791 : Blo 127788 1584791 := bstep (se 1 (by rfl) ⟨1188593, by rfl⟩ : syracuseStep 1584791 = 2377187) B2377187
theorem B437939 : Blo 127788 437939 := bstep (se 1 (by rfl) ⟨328454, by rfl⟩ : syracuseStep 437939 = 656909) B656909
theorem B176023 : Blo 127788 176023 := bstep (se 1 (by rfl) ⟨132017, by rfl⟩ : syracuseStep 176023 = 264035) B264035
theorem B438209 : Blo 127788 438209 := bstep (se 2 (by rfl) ⟨164328, by rfl⟩ : syracuseStep 438209 = 328657) B328657
theorem B372701 : Blo 127788 372701 := bstep (se 3 (by rfl) ⟨69881, by rfl⟩ : syracuseStep 372701 = 139763) B139763
theorem B831505 : Blo 127788 831505 := bstep (se 2 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 831505 = 623629) B623629
theorem B208921 : Blo 127788 208921 := bstep (se 2 (by rfl) ⟨78345, by rfl⟩ : syracuseStep 208921 = 156691) B156691
theorem B373081 : Blo 127788 373081 := bstep (se 2 (by rfl) ⟨139905, by rfl⟩ : syracuseStep 373081 = 279811) B279811
theorem B438749 : Blo 127788 438749 := bstep (se 3 (by rfl) ⟨82265, by rfl⟩ : syracuseStep 438749 = 164531) B164531
theorem B143851 : Blo 127788 143851 := bstep (se 1 (by rfl) ⟨107888, by rfl⟩ : syracuseStep 143851 = 215777) B215777
theorem B143959 : Blo 127788 143959 := bstep (se 1 (by rfl) ⟨107969, by rfl⟩ : syracuseStep 143959 = 215939) B215939
theorem B144139 : Blo 127788 144139 := bstep (se 1 (by rfl) ⟨108104, by rfl⟩ : syracuseStep 144139 = 216209) B216209
theorem B144247 : Blo 127788 144247 := bstep (se 1 (by rfl) ⟨108185, by rfl⟩ : syracuseStep 144247 = 216371) B216371
theorem B242689 : Blo 127788 242689 := bstep (se 2 (by rfl) ⟨91008, by rfl⟩ : syracuseStep 242689 = 182017) B182017
theorem B439319 : Blo 127788 439319 := bstep (se 1 (by rfl) ⟨329489, by rfl⟩ : syracuseStep 439319 = 658979) B658979
theorem B144427 : Blo 127788 144427 := bstep (se 1 (by rfl) ⟨108320, by rfl⟩ : syracuseStep 144427 = 216641) B216641
theorem B144535 : Blo 127788 144535 := bstep (se 1 (by rfl) ⟨108401, by rfl⟩ : syracuseStep 144535 = 216803) B216803
theorem B275699 : Blo 127788 275699 := bstep (se 1 (by rfl) ⟨206774, by rfl⟩ : syracuseStep 275699 = 413549) B413549
theorem B472337 : Blo 127788 472337 := bstep (se 2 (by rfl) ⟨177126, by rfl⟩ : syracuseStep 472337 = 354253) B354253
theorem B144715 : Blo 127788 144715 := bstep (se 1 (by rfl) ⟨108536, by rfl⟩ : syracuseStep 144715 = 217073) B217073
theorem B996785 : Blo 127788 996785 := bstep (se 2 (by rfl) ⟨373794, by rfl⟩ : syracuseStep 996785 = 747589) B747589
theorem B144823 : Blo 127788 144823 := bstep (se 1 (by rfl) ⟨108617, by rfl⟩ : syracuseStep 144823 = 217235) B217235
theorem B243137 : Blo 127788 243137 := bstep (se 2 (by rfl) ⟨91176, by rfl⟩ : syracuseStep 243137 = 182353) B182353
theorem B374233 : Blo 127788 374233 := bstep (se 2 (by rfl) ⟨140337, by rfl⟩ : syracuseStep 374233 = 280675) B280675
theorem B702017 : Blo 127788 702017 := bstep (se 2 (by rfl) ⟨263256, by rfl⟩ : syracuseStep 702017 = 526513) B526513
theorem B439883 : Blo 127788 439883 := bstep (se 1 (by rfl) ⟨329912, by rfl⟩ : syracuseStep 439883 = 659825) B659825
theorem B996965 : Blo 127788 996965 := bstep (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) B186931
theorem B145003 : Blo 127788 145003 := bstep (se 1 (by rfl) ⟨108752, by rfl⟩ : syracuseStep 145003 = 217505) B217505
theorem B11417219 : Blo 127788 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B472769 : Blo 127788 472769 := bstep (se 2 (by rfl) ⟨177288, by rfl⟩ : syracuseStep 472769 = 354577) B354577
theorem B145111 : Blo 127788 145111 := bstep (se 1 (by rfl) ⟨108833, by rfl⟩ : syracuseStep 145111 = 217667) B217667
theorem B734993 : Blo 127788 734993 := bstep (se 2 (by rfl) ⟨275622, by rfl⟩ : syracuseStep 734993 = 551245) B551245
theorem B243479 : Blo 127788 243479 := bstep (se 1 (by rfl) ⟨182609, by rfl⟩ : syracuseStep 243479 = 365219) B365219
theorem B440153 : Blo 127788 440153 := bstep (se 2 (by rfl) ⟨165057, by rfl⟩ : syracuseStep 440153 = 330115) B330115
theorem B145291 : Blo 127788 145291 := bstep (se 1 (by rfl) ⟨108968, by rfl⟩ : syracuseStep 145291 = 217937) B217937
theorem B997271 : Blo 127788 997271 := bstep (se 1 (by rfl) ⟨747953, by rfl⟩ : syracuseStep 997271 = 1495907) B1495907
theorem B145399 : Blo 127788 145399 := bstep (se 1 (by rfl) ⟨109049, by rfl⟩ : syracuseStep 145399 = 218099) B218099
theorem B1882187 : Blo 127788 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B145579 : Blo 127788 145579 := bstep (se 1 (by rfl) ⟨109184, by rfl⟩ : syracuseStep 145579 = 218369) B218369
theorem B145687 : Blo 127788 145687 := bstep (se 1 (by rfl) ⟨109265, by rfl⟩ : syracuseStep 145687 = 218531) B218531
theorem B244147 : Blo 127788 244147 := bstep (se 1 (by rfl) ⟨183110, by rfl⟩ : syracuseStep 244147 = 366221) B366221
theorem B145867 : Blo 127788 145867 := bstep (se 1 (by rfl) ⟨109400, by rfl⟩ : syracuseStep 145867 = 218801) B218801
theorem B277015 : Blo 127788 277015 := bstep (se 1 (by rfl) ⟨207761, by rfl⟩ : syracuseStep 277015 = 415523) B415523
theorem B440855 : Blo 127788 440855 := bstep (se 1 (by rfl) ⟨330641, by rfl⟩ : syracuseStep 440855 = 661283) B661283
theorem B145975 : Blo 127788 145975 := bstep (se 1 (by rfl) ⟨109481, by rfl⟩ : syracuseStep 145975 = 218963) B218963
theorem B375385 : Blo 127788 375385 := bstep (se 2 (by rfl) ⟨140769, by rfl⟩ : syracuseStep 375385 = 281539) B281539
theorem B4209245 : Blo 127788 4209245 := bstep (se 3 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 4209245 = 1578467) B1578467
theorem B146071 : Blo 127788 146071 := bstep (se 1 (by rfl) ⟨109553, by rfl⟩ : syracuseStep 146071 = 219107) B219107
theorem B277195 : Blo 127788 277195 := bstep (se 1 (by rfl) ⟨207896, by rfl⟩ : syracuseStep 277195 = 415793) B415793
theorem B146155 : Blo 127788 146155 := bstep (se 1 (by rfl) ⟨109616, by rfl⟩ : syracuseStep 146155 = 219233) B219233
theorem B277271 : Blo 127788 277271 := bstep (se 1 (by rfl) ⟨207953, by rfl⟩ : syracuseStep 277271 = 415907) B415907
theorem B146263 : Blo 127788 146263 := bstep (se 1 (by rfl) ⟨109697, by rfl⟩ : syracuseStep 146263 = 219395) B219395
theorem B244595 : Blo 127788 244595 := bstep (se 1 (by rfl) ⟨183446, by rfl⟩ : syracuseStep 244595 = 366893) B366893
theorem B474007 : Blo 127788 474007 := bstep (se 1 (by rfl) ⟨355505, by rfl⟩ : syracuseStep 474007 = 711011) B711011
theorem B244633 : Blo 127788 244633 := bstep (se 2 (by rfl) ⟨91737, by rfl⟩ : syracuseStep 244633 = 183475) B183475
theorem B146443 : Blo 127788 146443 := bstep (se 1 (by rfl) ⟨109832, by rfl⟩ : syracuseStep 146443 = 219665) B219665
theorem B441395 : Blo 127788 441395 := bstep (se 1 (by rfl) ⟨331046, by rfl⟩ : syracuseStep 441395 = 662093) B662093
theorem B146551 : Blo 127788 146551 := bstep (se 1 (by rfl) ⟨109913, by rfl⟩ : syracuseStep 146551 = 219827) B219827
theorem B933125 : Blo 127788 933125 := bstep (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) B174961
theorem B146731 : Blo 127788 146731 := bstep (se 1 (by rfl) ⟨110048, by rfl⟩ : syracuseStep 146731 = 220097) B220097
theorem B441665 : Blo 127788 441665 := bstep (se 2 (by rfl) ⟨165624, by rfl⟩ : syracuseStep 441665 = 331249) B331249
theorem B245081 : Blo 127788 245081 := bstep (se 2 (by rfl) ⟨91905, by rfl⟩ : syracuseStep 245081 = 183811) B183811
theorem B146839 : Blo 127788 146839 := bstep (se 1 (by rfl) ⟨110129, by rfl⟩ : syracuseStep 146839 = 220259) B220259
theorem B147019 : Blo 127788 147019 := bstep (se 1 (by rfl) ⟨110264, by rfl⟩ : syracuseStep 147019 = 220529) B220529
theorem B310873 : Blo 127788 310873 := bstep (se 2 (by rfl) ⟨116577, by rfl⟩ : syracuseStep 310873 = 233155) B233155
theorem B147127 : Blo 127788 147127 := bstep (se 1 (by rfl) ⟨110345, by rfl⟩ : syracuseStep 147127 = 220691) B220691
theorem B442205 : Blo 127788 442205 := bstep (se 3 (by rfl) ⟨82913, by rfl⟩ : syracuseStep 442205 = 165827) B165827
theorem B147307 : Blo 127788 147307 := bstep (se 1 (by rfl) ⟨110480, by rfl⟩ : syracuseStep 147307 = 220961) B220961
theorem B147415 : Blo 127788 147415 := bstep (se 1 (by rfl) ⟨110561, by rfl⟩ : syracuseStep 147415 = 221123) B221123
theorem B966691 : Blo 127788 966691 := bstep (se 1 (by rfl) ⟨725018, by rfl⟩ : syracuseStep 966691 = 1450037) B1450037
theorem B245825 : Blo 127788 245825 := bstep (se 2 (by rfl) ⟨92184, by rfl⟩ : syracuseStep 245825 = 184369) B184369
theorem B147595 : Blo 127788 147595 := bstep (se 1 (by rfl) ⟨110696, by rfl⟩ : syracuseStep 147595 = 221393) B221393
theorem B311489 : Blo 127788 311489 := bstep (se 2 (by rfl) ⟨116808, by rfl⟩ : syracuseStep 311489 = 233617) B233617
theorem B147703 : Blo 127788 147703 := bstep (se 1 (by rfl) ⟨110777, by rfl⟩ : syracuseStep 147703 = 221555) B221555
theorem B246091 : Blo 127788 246091 := bstep (se 1 (by rfl) ⟨184568, by rfl⟩ : syracuseStep 246091 = 369137) B369137
theorem B147863 : Blo 127788 147863 := bstep (se 1 (by rfl) ⟨110897, by rfl⟩ : syracuseStep 147863 = 221795) B221795
theorem B147883 : Blo 127788 147883 := bstep (se 1 (by rfl) ⟨110912, by rfl⟩ : syracuseStep 147883 = 221825) B221825
theorem B147895 : Blo 127788 147895 := bstep (se 1 (by rfl) ⟨110921, by rfl⟩ : syracuseStep 147895 = 221843) B221843
theorem B147991 : Blo 127788 147991 := bstep (se 1 (by rfl) ⟨110993, by rfl⟩ : syracuseStep 147991 = 221987) B221987
theorem B279065 : Blo 127788 279065 := bstep (se 2 (by rfl) ⟨104649, by rfl⟩ : syracuseStep 279065 = 209299) B209299
theorem B377419 : Blo 127788 377419 := bstep (se 1 (by rfl) ⟨283064, by rfl⟩ : syracuseStep 377419 = 566129) B566129
theorem B148171 : Blo 127788 148171 := bstep (se 1 (by rfl) ⟨111128, by rfl⟩ : syracuseStep 148171 = 222257) B222257
theorem B1229573 : Blo 127788 1229573 := bstep (se 4 (by rfl) ⟨115272, by rfl⟩ : syracuseStep 1229573 = 230545) B230545
theorem B148235 : Blo 127788 148235 := bstep (se 1 (by rfl) ⟨111176, by rfl⟩ : syracuseStep 148235 = 222353) B222353
theorem B246539 : Blo 127788 246539 := bstep (se 1 (by rfl) ⟨184904, by rfl⟩ : syracuseStep 246539 = 369809) B369809
theorem B246721 : Blo 127788 246721 := bstep (se 2 (by rfl) ⟨92520, by rfl⟩ : syracuseStep 246721 = 185041) B185041
theorem B443339 : Blo 127788 443339 := bstep (se 1 (by rfl) ⟨332504, by rfl⟩ : syracuseStep 443339 = 665009) B665009
theorem B279731 : Blo 127788 279731 := bstep (se 1 (by rfl) ⟨209798, by rfl⟩ : syracuseStep 279731 = 419597) B419597
theorem B443609 : Blo 127788 443609 := bstep (se 2 (by rfl) ⟨166353, by rfl⟩ : syracuseStep 443609 = 332707) B332707
theorem B247063 : Blo 127788 247063 := bstep (se 1 (by rfl) ⟨185297, by rfl⟩ : syracuseStep 247063 = 370595) B370595
theorem B247283 : Blo 127788 247283 := bstep (se 1 (by rfl) ⟨185462, by rfl⟩ : syracuseStep 247283 = 370925) B370925
theorem B935441 : Blo 127788 935441 := bstep (se 2 (by rfl) ⟨350790, by rfl⟩ : syracuseStep 935441 = 701581) B701581
theorem B1328791 : Blo 127788 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B247511 : Blo 127788 247511 := bstep (se 1 (by rfl) ⟨185633, by rfl⟩ : syracuseStep 247511 = 371267) B371267
theorem B1001281 : Blo 127788 1001281 := bstep (se 2 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 1001281 = 750961) B750961
theorem B444311 : Blo 127788 444311 := bstep (se 1 (by rfl) ⟨333233, by rfl⟩ : syracuseStep 444311 = 666467) B666467
theorem B280523 : Blo 127788 280523 := bstep (se 1 (by rfl) ⟨210392, by rfl⟩ : syracuseStep 280523 = 420785) B420785
theorem B247769 : Blo 127788 247769 := bstep (se 2 (by rfl) ⟨92913, by rfl⟩ : syracuseStep 247769 = 185827) B185827
theorem B379073 : Blo 127788 379073 := bstep (se 2 (by rfl) ⟨142152, by rfl⟩ : syracuseStep 379073 = 284305) B284305
theorem B739601 : Blo 127788 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B2836781 : Blo 127788 2836781 := bstep (se 3 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 2836781 = 1063793) B1063793
theorem B248179 : Blo 127788 248179 := bstep (se 1 (by rfl) ⟨186134, by rfl⟩ : syracuseStep 248179 = 372269) B372269
theorem B444851 : Blo 127788 444851 := bstep (se 1 (by rfl) ⟨333638, by rfl⟩ : syracuseStep 444851 = 667277) B667277
theorem B281227 : Blo 127788 281227 := bstep (se 1 (by rfl) ⟨210920, by rfl⟩ : syracuseStep 281227 = 421841) B421841
theorem B215831 : Blo 127788 215831 := bstep (se 1 (by rfl) ⟨161873, by rfl⟩ : syracuseStep 215831 = 323747) B323747
theorem B248665 : Blo 127788 248665 := bstep (se 2 (by rfl) ⟨93249, by rfl⟩ : syracuseStep 248665 = 186499) B186499
theorem B215959 : Blo 127788 215959 := bstep (se 1 (by rfl) ⟨161969, by rfl⟩ : syracuseStep 215959 = 323939) B323939
theorem B2018317 : Blo 127788 2018317 := bstep (se 3 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 2018317 = 756869) B756869
theorem B1100951 : Blo 127788 1100951 := bstep (se 1 (by rfl) ⟨825713, by rfl⟩ : syracuseStep 1100951 = 1651427) B1651427
theorem B249227 : Blo 127788 249227 := bstep (se 1 (by rfl) ⟨186920, by rfl⟩ : syracuseStep 249227 = 373841) B373841
theorem B183703 : Blo 127788 183703 := bstep (se 1 (by rfl) ⟨137777, by rfl⟩ : syracuseStep 183703 = 275555) B275555
theorem B1494449 : Blo 127788 1494449 := bstep (se 2 (by rfl) ⟨560418, by rfl⟩ : syracuseStep 1494449 = 1120837) B1120837
theorem B740825 : Blo 127788 740825 := bstep (se 2 (by rfl) ⟨277809, by rfl⟩ : syracuseStep 740825 = 555619) B555619
theorem B216587 : Blo 127788 216587 := bstep (se 1 (by rfl) ⟨162440, by rfl⟩ : syracuseStep 216587 = 324881) B324881
theorem B249409 : Blo 127788 249409 := bstep (se 2 (by rfl) ⟨93528, by rfl⟩ : syracuseStep 249409 = 187057) B187057
theorem B282199 : Blo 127788 282199 := bstep (se 1 (by rfl) ⟨211649, by rfl⟩ : syracuseStep 282199 = 423299) B423299
theorem B1363549 : Blo 127788 1363549 := bstep (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) B511331
theorem B216715 : Blo 127788 216715 := bstep (se 1 (by rfl) ⟨162536, by rfl⟩ : syracuseStep 216715 = 325073) B325073
theorem B2248373 : Blo 127788 2248373 := bstep (se 5 (by rfl) ⟨105392, by rfl⟩ : syracuseStep 2248373 = 210785) B210785
theorem B315083 : Blo 127788 315083 := bstep (se 1 (by rfl) ⟨236312, by rfl⟩ : syracuseStep 315083 = 472625) B472625
theorem B216857 : Blo 127788 216857 := bstep (se 2 (by rfl) ⟨81321, by rfl⟩ : syracuseStep 216857 = 162643) B162643
theorem B970541 : Blo 127788 970541 := bstep (se 3 (by rfl) ⟨181976, by rfl⟩ : syracuseStep 970541 = 363953) B363953
theorem B1265453 : Blo 127788 1265453 := bstep (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) B474545
theorem B216985 : Blo 127788 216985 := bstep (se 2 (by rfl) ⟨81369, by rfl⟩ : syracuseStep 216985 = 162739) B162739
theorem B4837637 : Blo 127788 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B250123 : Blo 127788 250123 := bstep (se 1 (by rfl) ⟨187592, by rfl⟩ : syracuseStep 250123 = 375185) B375185
theorem B2117987 : Blo 127788 2117987 := bstep (se 1 (by rfl) ⟨1588490, by rfl⟩ : syracuseStep 2117987 = 3176981) B3176981
theorem B217559 : Blo 127788 217559 := bstep (se 1 (by rfl) ⟨163169, by rfl⟩ : syracuseStep 217559 = 326339) B326339
theorem B1266137 : Blo 127788 1266137 := bstep (se 2 (by rfl) ⟨474801, by rfl⟩ : syracuseStep 1266137 = 949603) B949603
theorem B217687 : Blo 127788 217687 := bstep (se 1 (by rfl) ⟨163265, by rfl⟩ : syracuseStep 217687 = 326531) B326531
theorem B251059 : Blo 127788 251059 := bstep (se 1 (by rfl) ⟨188294, by rfl⟩ : syracuseStep 251059 = 376589) B376589
theorem B218315 : Blo 127788 218315 := bstep (se 1 (by rfl) ⟨163736, by rfl⟩ : syracuseStep 218315 = 327473) B327473
theorem B283915 : Blo 127788 283915 := bstep (se 1 (by rfl) ⟨212936, by rfl⟩ : syracuseStep 283915 = 425873) B425873
theorem B218443 : Blo 127788 218443 := bstep (se 1 (by rfl) ⟨163832, by rfl⟩ : syracuseStep 218443 = 327665) B327665
theorem B185753 : Blo 127788 185753 := bstep (se 2 (by rfl) ⟨69657, by rfl⟩ : syracuseStep 185753 = 139315) B139315
theorem B316889 : Blo 127788 316889 := bstep (se 2 (by rfl) ⟨118833, by rfl⟩ : syracuseStep 316889 = 237667) B237667
theorem B218585 : Blo 127788 218585 := bstep (se 2 (by rfl) ⟨81969, by rfl⟩ : syracuseStep 218585 = 163939) B163939
theorem B218713 : Blo 127788 218713 := bstep (se 2 (by rfl) ⟨82017, by rfl⟩ : syracuseStep 218713 = 164035) B164035
theorem B677783 : Blo 127788 677783 := bstep (se 1 (by rfl) ⟨508337, by rfl⟩ : syracuseStep 677783 = 1016675) B1016675
theorem B186391 : Blo 127788 186391 := bstep (se 1 (by rfl) ⟨139793, by rfl⟩ : syracuseStep 186391 = 279587) B279587
theorem B743489 : Blo 127788 743489 := bstep (se 2 (by rfl) ⟨278808, by rfl⟩ : syracuseStep 743489 = 557617) B557617
theorem B841859 : Blo 127788 841859 := bstep (se 1 (by rfl) ⟨631394, by rfl⟩ : syracuseStep 841859 = 1262789) B1262789
theorem B481411 : Blo 127788 481411 := bstep (se 1 (by rfl) ⟨361058, by rfl⟩ : syracuseStep 481411 = 722117) B722117
theorem B219287 : Blo 127788 219287 := bstep (se 1 (by rfl) ⟨164465, by rfl⟩ : syracuseStep 219287 = 328931) B328931
theorem B219415 : Blo 127788 219415 := bstep (se 1 (by rfl) ⟨164561, by rfl⟩ : syracuseStep 219415 = 329123) B329123
theorem B187211 : Blo 127788 187211 := bstep (se 1 (by rfl) ⟨140408, by rfl⟩ : syracuseStep 187211 = 280817) B280817
theorem B351065 : Blo 127788 351065 := bstep (se 2 (by rfl) ⟨131649, by rfl⟩ : syracuseStep 351065 = 263299) B263299
theorem B220043 : Blo 127788 220043 := bstep (se 1 (by rfl) ⟨165032, by rfl⟩ : syracuseStep 220043 = 330065) B330065
theorem B220171 : Blo 127788 220171 := bstep (se 1 (by rfl) ⟨165128, by rfl⟩ : syracuseStep 220171 = 330257) B330257
theorem B318487 : Blo 127788 318487 := bstep (se 1 (by rfl) ⟨238865, by rfl⟩ : syracuseStep 318487 = 477731) B477731
theorem B220313 : Blo 127788 220313 := bstep (se 2 (by rfl) ⟨82617, by rfl⟩ : syracuseStep 220313 = 165235) B165235
theorem B220441 : Blo 127788 220441 := bstep (se 2 (by rfl) ⟨82665, by rfl⟩ : syracuseStep 220441 = 165331) B165331
theorem B974429 : Blo 127788 974429 := bstep (se 3 (by rfl) ⟨182705, by rfl⟩ : syracuseStep 974429 = 365411) B365411
theorem B2088629 : Blo 127788 2088629 := bstep (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) B195809
theorem B319297 : Blo 127788 319297 := bstep (se 2 (by rfl) ⟨119736, by rfl⟩ : syracuseStep 319297 = 239473) B239473
theorem B221015 : Blo 127788 221015 := bstep (se 1 (by rfl) ⟨165761, by rfl⟩ : syracuseStep 221015 = 331523) B331523
theorem B548801 : Blo 127788 548801 := bstep (se 2 (by rfl) ⟨205800, by rfl⟩ : syracuseStep 548801 = 411601) B411601
theorem B221143 : Blo 127788 221143 := bstep (se 1 (by rfl) ⟨165857, by rfl⟩ : syracuseStep 221143 = 331715) B331715
theorem B549143 : Blo 127788 549143 := bstep (se 1 (by rfl) ⟨411857, by rfl⟩ : syracuseStep 549143 = 823715) B823715
theorem B1171805 : Blo 127788 1171805 := bstep (se 3 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 1171805 = 439427) B439427
theorem B287129 : Blo 127788 287129 := bstep (se 2 (by rfl) ⟨107673, by rfl⟩ : syracuseStep 287129 = 215347) B215347
theorem B778675 : Blo 127788 778675 := bstep (se 1 (by rfl) ⟨584006, by rfl⟩ : syracuseStep 778675 = 1168013) B1168013
theorem B418355 : Blo 127788 418355 := bstep (se 1 (by rfl) ⟨313766, by rfl⟩ : syracuseStep 418355 = 627533) B627533
theorem B287297 : Blo 127788 287297 := bstep (se 2 (by rfl) ⟨107736, by rfl⟩ : syracuseStep 287297 = 215473) B215473
theorem B221771 : Blo 127788 221771 := bstep (se 1 (by rfl) ⟨166328, by rfl⟩ : syracuseStep 221771 = 332657) B332657
theorem B221899 : Blo 127788 221899 := bstep (se 1 (by rfl) ⟨166424, by rfl⟩ : syracuseStep 221899 = 332849) B332849
theorem B222041 : Blo 127788 222041 := bstep (se 2 (by rfl) ⟨83265, by rfl⟩ : syracuseStep 222041 = 166531) B166531
theorem B287603 : Blo 127788 287603 := bstep (se 1 (by rfl) ⟨215702, by rfl⟩ : syracuseStep 287603 = 431405) B431405
theorem B287639 : Blo 127788 287639 := bstep (se 1 (by rfl) ⟨215729, by rfl⟩ : syracuseStep 287639 = 431459) B431459
theorem B222169 : Blo 127788 222169 := bstep (se 2 (by rfl) ⟨83313, by rfl⟩ : syracuseStep 222169 = 166627) B166627
theorem B287819 : Blo 127788 287819 := bstep (se 1 (by rfl) ⟨215864, by rfl⟩ : syracuseStep 287819 = 431729) B431729
theorem B287873 : Blo 127788 287873 := bstep (se 2 (by rfl) ⟨107952, by rfl⟩ : syracuseStep 287873 = 215905) B215905
theorem B648323 : Blo 127788 648323 := bstep (se 1 (by rfl) ⟨486242, by rfl⟩ : syracuseStep 648323 = 972485) B972485
theorem B156811 : Blo 127788 156811 := bstep (se 1 (by rfl) ⟨117608, by rfl⟩ : syracuseStep 156811 = 235217) B235217
theorem B419033 : Blo 127788 419033 := bstep (se 2 (by rfl) ⟨157137, by rfl⟩ : syracuseStep 419033 = 314275) B314275
theorem B288089 : Blo 127788 288089 := bstep (se 2 (by rfl) ⟨108033, by rfl⟩ : syracuseStep 288089 = 216067) B216067
theorem B779651 : Blo 127788 779651 := bstep (se 1 (by rfl) ⟨584738, by rfl⟩ : syracuseStep 779651 = 1169477) B1169477
theorem B288179 : Blo 127788 288179 := bstep (se 1 (by rfl) ⟨216134, by rfl⟩ : syracuseStep 288179 = 432269) B432269
theorem B288215 : Blo 127788 288215 := bstep (se 1 (by rfl) ⟨216161, by rfl⟩ : syracuseStep 288215 = 432323) B432323
theorem B288395 : Blo 127788 288395 := bstep (se 1 (by rfl) ⟨216296, by rfl⟩ : syracuseStep 288395 = 432593) B432593
theorem B288449 : Blo 127788 288449 := bstep (se 2 (by rfl) ⟨108168, by rfl⟩ : syracuseStep 288449 = 216337) B216337
theorem B1468205 : Blo 127788 1468205 := bstep (se 3 (by rfl) ⟨275288, by rfl⟩ : syracuseStep 1468205 = 550577) B550577
theorem B288665 : Blo 127788 288665 := bstep (se 2 (by rfl) ⟨108249, by rfl⟩ : syracuseStep 288665 = 216499) B216499
theorem B288755 : Blo 127788 288755 := bstep (se 1 (by rfl) ⟨216566, by rfl⟩ : syracuseStep 288755 = 433133) B433133
theorem B288791 : Blo 127788 288791 := bstep (se 1 (by rfl) ⟨216593, by rfl⟩ : syracuseStep 288791 = 433187) B433187
theorem B583811 : Blo 127788 583811 := bstep (se 1 (by rfl) ⟨437858, by rfl⟩ : syracuseStep 583811 = 875717) B875717
theorem B583859 : Blo 127788 583859 := bstep (se 1 (by rfl) ⟨437894, by rfl⟩ : syracuseStep 583859 = 875789) B875789
theorem B288971 : Blo 127788 288971 := bstep (se 1 (by rfl) ⟨216728, by rfl⟩ : syracuseStep 288971 = 433457) B433457
theorem B289025 : Blo 127788 289025 := bstep (se 2 (by rfl) ⟨108384, by rfl⟩ : syracuseStep 289025 = 216769) B216769
theorem B485635 : Blo 127788 485635 := bstep (se 1 (by rfl) ⟨364226, by rfl⟩ : syracuseStep 485635 = 728453) B728453
theorem B551261 : Blo 127788 551261 := bstep (se 3 (by rfl) ⟨103361, by rfl⟩ : syracuseStep 551261 = 206723) B206723
theorem B289241 : Blo 127788 289241 := bstep (se 2 (by rfl) ⟨108465, by rfl⟩ : syracuseStep 289241 = 216931) B216931
theorem B485939 : Blo 127788 485939 := bstep (se 1 (by rfl) ⟨364454, by rfl⟩ : syracuseStep 485939 = 728909) B728909
theorem B289331 : Blo 127788 289331 := bstep (se 1 (by rfl) ⟨216998, by rfl⟩ : syracuseStep 289331 = 433997) B433997
theorem B289367 : Blo 127788 289367 := bstep (se 1 (by rfl) ⟨217025, by rfl⟩ : syracuseStep 289367 = 434051) B434051
theorem B551569 : Blo 127788 551569 := bstep (se 2 (by rfl) ⟨206838, by rfl⟩ : syracuseStep 551569 = 413677) B413677
theorem B551603 : Blo 127788 551603 := bstep (se 1 (by rfl) ⟨413702, by rfl⟩ : syracuseStep 551603 = 827405) B827405
theorem B289547 : Blo 127788 289547 := bstep (se 1 (by rfl) ⟨217160, by rfl⟩ : syracuseStep 289547 = 434321) B434321
theorem B289601 : Blo 127788 289601 := bstep (se 2 (by rfl) ⟨108600, by rfl⟩ : syracuseStep 289601 = 217201) B217201
theorem B289817 : Blo 127788 289817 := bstep (se 2 (by rfl) ⟨108681, by rfl⟩ : syracuseStep 289817 = 217363) B217363
theorem B2583587 : Blo 127788 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B289907 : Blo 127788 289907 := bstep (se 1 (by rfl) ⟨217430, by rfl⟩ : syracuseStep 289907 = 434861) B434861
theorem B289943 : Blo 127788 289943 := bstep (se 1 (by rfl) ⟨217457, by rfl⟩ : syracuseStep 289943 = 434915) B434915
theorem B486593 : Blo 127788 486593 := bstep (se 2 (by rfl) ⟨182472, by rfl⟩ : syracuseStep 486593 = 364945) B364945
theorem B191705 : Blo 127788 191705 := bstep (se 2 (by rfl) ⟨71889, by rfl⟩ : syracuseStep 191705 = 143779) B143779
theorem B584921 : Blo 127788 584921 := bstep (se 2 (by rfl) ⟨219345, by rfl⟩ : syracuseStep 584921 = 438691) B438691
theorem B748865 : Blo 127788 748865 := bstep (se 2 (by rfl) ⟨280824, by rfl⟩ : syracuseStep 748865 = 561649) B561649
theorem B191819 : Blo 127788 191819 := bstep (se 1 (by rfl) ⟨143864, by rfl⟩ : syracuseStep 191819 = 287729) B287729
theorem B290123 : Blo 127788 290123 := bstep (se 1 (by rfl) ⟨217592, by rfl⟩ : syracuseStep 290123 = 435185) B435185
theorem B191831 : Blo 127788 191831 := bstep (se 1 (by rfl) ⟨143873, by rfl⟩ : syracuseStep 191831 = 287747) B287747
theorem B290177 : Blo 127788 290177 := bstep (se 2 (by rfl) ⟨108816, by rfl⟩ : syracuseStep 290177 = 217633) B217633
theorem B191897 : Blo 127788 191897 := bstep (se 2 (by rfl) ⟨71961, by rfl⟩ : syracuseStep 191897 = 143923) B143923
theorem B192011 : Blo 127788 192011 := bstep (se 1 (by rfl) ⟨144008, by rfl⟩ : syracuseStep 192011 = 288017) B288017
theorem B192023 : Blo 127788 192023 := bstep (se 1 (by rfl) ⟨144017, by rfl⟩ : syracuseStep 192023 = 288035) B288035
theorem B192089 : Blo 127788 192089 := bstep (se 2 (by rfl) ⟨72033, by rfl⟩ : syracuseStep 192089 = 144067) B144067
theorem B290393 : Blo 127788 290393 := bstep (se 2 (by rfl) ⟨108897, by rfl⟩ : syracuseStep 290393 = 217795) B217795
theorem B421469 : Blo 127788 421469 := bstep (se 3 (by rfl) ⟨79025, by rfl⟩ : syracuseStep 421469 = 158051) B158051
theorem B290483 : Blo 127788 290483 := bstep (se 1 (by rfl) ⟨217862, by rfl⟩ : syracuseStep 290483 = 435725) B435725
theorem B192203 : Blo 127788 192203 := bstep (se 1 (by rfl) ⟨144152, by rfl⟩ : syracuseStep 192203 = 288305) B288305
theorem B192215 : Blo 127788 192215 := bstep (se 1 (by rfl) ⟨144161, by rfl⟩ : syracuseStep 192215 = 288323) B288323
theorem B290519 : Blo 127788 290519 := bstep (se 1 (by rfl) ⟨217889, by rfl⟩ : syracuseStep 290519 = 435779) B435779
theorem B192281 : Blo 127788 192281 := bstep (se 2 (by rfl) ⟨72105, by rfl⟩ : syracuseStep 192281 = 144211) B144211
theorem B192395 : Blo 127788 192395 := bstep (se 1 (by rfl) ⟨144296, by rfl⟩ : syracuseStep 192395 = 288593) B288593
theorem B290699 : Blo 127788 290699 := bstep (se 1 (by rfl) ⟨218024, by rfl⟩ : syracuseStep 290699 = 436049) B436049
theorem B192407 : Blo 127788 192407 := bstep (se 1 (by rfl) ⟨144305, by rfl⟩ : syracuseStep 192407 = 288611) B288611
theorem B290753 : Blo 127788 290753 := bstep (se 2 (by rfl) ⟨109032, by rfl⟩ : syracuseStep 290753 = 218065) B218065
theorem B520139 : Blo 127788 520139 := bstep (se 1 (by rfl) ⟨390104, by rfl⟩ : syracuseStep 520139 = 780209) B780209
theorem B192473 : Blo 127788 192473 := bstep (se 2 (by rfl) ⟨72177, by rfl⟩ : syracuseStep 192473 = 144355) B144355
theorem B2191373 : Blo 127788 2191373 := bstep (se 3 (by rfl) ⟨410882, by rfl⟩ : syracuseStep 2191373 = 821765) B821765
theorem B323635 : Blo 127788 323635 := bstep (se 1 (by rfl) ⟨242726, by rfl⟩ : syracuseStep 323635 = 485453) B485453
theorem B192587 : Blo 127788 192587 := bstep (se 1 (by rfl) ⟨144440, by rfl⟩ : syracuseStep 192587 = 288881) B288881
theorem B192599 : Blo 127788 192599 := bstep (se 1 (by rfl) ⟨144449, by rfl⟩ : syracuseStep 192599 = 288899) B288899
theorem B192665 : Blo 127788 192665 := bstep (se 2 (by rfl) ⟨72249, by rfl⟩ : syracuseStep 192665 = 144499) B144499
theorem B290969 : Blo 127788 290969 := bstep (se 2 (by rfl) ⟨109113, by rfl⟩ : syracuseStep 290969 = 218227) B218227
theorem B323777 : Blo 127788 323777 := bstep (se 2 (by rfl) ⟨121416, by rfl⟩ : syracuseStep 323777 = 242833) B242833
theorem B291059 : Blo 127788 291059 := bstep (se 1 (by rfl) ⟨218294, by rfl⟩ : syracuseStep 291059 = 436589) B436589
theorem B192779 : Blo 127788 192779 := bstep (se 1 (by rfl) ⟨144584, by rfl⟩ : syracuseStep 192779 = 289169) B289169
theorem B192791 : Blo 127788 192791 := bstep (se 1 (by rfl) ⟨144593, by rfl⟩ : syracuseStep 192791 = 289187) B289187
theorem B291095 : Blo 127788 291095 := bstep (se 1 (by rfl) ⟨218321, by rfl⟩ : syracuseStep 291095 = 436643) B436643
theorem B192857 : Blo 127788 192857 := bstep (se 2 (by rfl) ⟨72321, by rfl⟩ : syracuseStep 192857 = 144643) B144643
theorem B487853 : Blo 127788 487853 := bstep (se 3 (by rfl) ⟨91472, by rfl⟩ : syracuseStep 487853 = 182945) B182945
theorem B1110449 : Blo 127788 1110449 := bstep (se 2 (by rfl) ⟨416418, by rfl⟩ : syracuseStep 1110449 = 832837) B832837
theorem B487883 : Blo 127788 487883 := bstep (se 1 (by rfl) ⟨365912, by rfl⟩ : syracuseStep 487883 = 731825) B731825
theorem B192971 : Blo 127788 192971 := bstep (se 1 (by rfl) ⟨144728, by rfl⟩ : syracuseStep 192971 = 289457) B289457
theorem B291275 : Blo 127788 291275 := bstep (se 1 (by rfl) ⟨218456, by rfl⟩ : syracuseStep 291275 = 436913) B436913
theorem B192983 : Blo 127788 192983 := bstep (se 1 (by rfl) ⟨144737, by rfl⟩ : syracuseStep 192983 = 289475) B289475
theorem B291329 : Blo 127788 291329 := bstep (se 2 (by rfl) ⟨109248, by rfl⟩ : syracuseStep 291329 = 218497) B218497
theorem B193049 : Blo 127788 193049 := bstep (se 2 (by rfl) ⟨72393, by rfl⟩ : syracuseStep 193049 = 144787) B144787
theorem B553517 : Blo 127788 553517 := bstep (se 3 (by rfl) ⟨103784, by rfl⟩ : syracuseStep 553517 = 207569) B207569
theorem B193163 : Blo 127788 193163 := bstep (se 1 (by rfl) ⟨144872, by rfl⟩ : syracuseStep 193163 = 289745) B289745
theorem B225931 : Blo 127788 225931 := bstep (se 1 (by rfl) ⟨169448, by rfl⟩ : syracuseStep 225931 = 338897) B338897
theorem B193175 : Blo 127788 193175 := bstep (se 1 (by rfl) ⟨144881, by rfl⟩ : syracuseStep 193175 = 289763) B289763
theorem B193241 : Blo 127788 193241 := bstep (se 2 (by rfl) ⟨72465, by rfl⟩ : syracuseStep 193241 = 144931) B144931
theorem B291545 : Blo 127788 291545 := bstep (se 2 (by rfl) ⟨109329, by rfl⟩ : syracuseStep 291545 = 218659) B218659
theorem B652049 : Blo 127788 652049 := bstep (se 2 (by rfl) ⟨244518, by rfl⟩ : syracuseStep 652049 = 489037) B489037
theorem B291635 : Blo 127788 291635 := bstep (se 1 (by rfl) ⟨218726, by rfl⟩ : syracuseStep 291635 = 437453) B437453
theorem B127799 : Blo 127788 127799 := bstep (se 1 (by rfl) ⟨95849, by rfl⟩ : syracuseStep 127799 = 191699) B191699
theorem B127819 : Blo 127788 127819 := bstep (se 1 (by rfl) ⟨95864, by rfl⟩ : syracuseStep 127819 = 191729) B191729
theorem B193355 : Blo 127788 193355 := bstep (se 1 (by rfl) ⟨145016, by rfl⟩ : syracuseStep 193355 = 290033) B290033
theorem B127831 : Blo 127788 127831 := bstep (se 1 (by rfl) ⟨95873, by rfl⟩ : syracuseStep 127831 = 191747) B191747
theorem B193367 : Blo 127788 193367 := bstep (se 1 (by rfl) ⟨145025, by rfl⟩ : syracuseStep 193367 = 290051) B290051
theorem B291671 : Blo 127788 291671 := bstep (se 1 (by rfl) ⟨218753, by rfl⟩ : syracuseStep 291671 = 437507) B437507
theorem B127851 : Blo 127788 127851 := bstep (se 1 (by rfl) ⟨95888, by rfl⟩ : syracuseStep 127851 = 191777) B191777
theorem B127863 : Blo 127788 127863 := bstep (se 1 (by rfl) ⟨95897, by rfl⟩ : syracuseStep 127863 = 191795) B191795
theorem B127883 : Blo 127788 127883 := bstep (se 1 (by rfl) ⟨95912, by rfl⟩ : syracuseStep 127883 = 191825) B191825
theorem B127895 : Blo 127788 127895 := bstep (se 1 (by rfl) ⟨95921, by rfl⟩ : syracuseStep 127895 = 191843) B191843
theorem B193433 : Blo 127788 193433 := bstep (se 2 (by rfl) ⟨72537, by rfl⟩ : syracuseStep 193433 = 145075) B145075
theorem B127915 : Blo 127788 127915 := bstep (se 1 (by rfl) ⟨95936, by rfl⟩ : syracuseStep 127915 = 191873) B191873
theorem B652211 : Blo 127788 652211 := bstep (se 1 (by rfl) ⟨489158, by rfl⟩ : syracuseStep 652211 = 978317) B978317
theorem B127927 : Blo 127788 127927 := bstep (se 1 (by rfl) ⟨95945, by rfl⟩ : syracuseStep 127927 = 191891) B191891
theorem B127947 : Blo 127788 127947 := bstep (se 1 (by rfl) ⟨95960, by rfl⟩ : syracuseStep 127947 = 191921) B191921
theorem B127959 : Blo 127788 127959 := bstep (se 1 (by rfl) ⟨95969, by rfl⟩ : syracuseStep 127959 = 191939) B191939
theorem B127979 : Blo 127788 127979 := bstep (se 1 (by rfl) ⟨95984, by rfl⟩ : syracuseStep 127979 = 191969) B191969
theorem B127991 : Blo 127788 127991 := bstep (se 1 (by rfl) ⟨95993, by rfl⟩ : syracuseStep 127991 = 191987) B191987
theorem B128011 : Blo 127788 128011 := bstep (se 1 (by rfl) ⟨96008, by rfl⟩ : syracuseStep 128011 = 192017) B192017
theorem B193547 : Blo 127788 193547 := bstep (se 1 (by rfl) ⟨145160, by rfl⟩ : syracuseStep 193547 = 290321) B290321
theorem B291851 : Blo 127788 291851 := bstep (se 1 (by rfl) ⟨218888, by rfl⟩ : syracuseStep 291851 = 437777) B437777
theorem B128023 : Blo 127788 128023 := bstep (se 1 (by rfl) ⟨96017, by rfl⟩ : syracuseStep 128023 = 192035) B192035
theorem B390167 : Blo 127788 390167 := bstep (se 1 (by rfl) ⟨292625, by rfl⟩ : syracuseStep 390167 = 585251) B585251
theorem B193559 : Blo 127788 193559 := bstep (se 1 (by rfl) ⟨145169, by rfl⟩ : syracuseStep 193559 = 290339) B290339
theorem B128043 : Blo 127788 128043 := bstep (se 1 (by rfl) ⟨96032, by rfl⟩ : syracuseStep 128043 = 192065) B192065
theorem B128055 : Blo 127788 128055 := bstep (se 1 (by rfl) ⟨96041, by rfl⟩ : syracuseStep 128055 = 192083) B192083
theorem B291905 : Blo 127788 291905 := bstep (se 2 (by rfl) ⟨109464, by rfl⟩ : syracuseStep 291905 = 218929) B218929
theorem B128075 : Blo 127788 128075 := bstep (se 1 (by rfl) ⟨96056, by rfl⟩ : syracuseStep 128075 = 192113) B192113
theorem B619595 : Blo 127788 619595 := bstep (se 1 (by rfl) ⟨464696, by rfl⟩ : syracuseStep 619595 = 929393) B929393
theorem B128087 : Blo 127788 128087 := bstep (se 1 (by rfl) ⟨96065, by rfl⟩ : syracuseStep 128087 = 192131) B192131
theorem B488537 : Blo 127788 488537 := bstep (se 2 (by rfl) ⟨183201, by rfl⟩ : syracuseStep 488537 = 366403) B366403
theorem B193625 : Blo 127788 193625 := bstep (se 2 (by rfl) ⟨72609, by rfl⟩ : syracuseStep 193625 = 145219) B145219
theorem B128107 : Blo 127788 128107 := bstep (se 1 (by rfl) ⟨96080, by rfl⟩ : syracuseStep 128107 = 192161) B192161
theorem B128119 : Blo 127788 128119 := bstep (se 1 (by rfl) ⟨96089, by rfl⟩ : syracuseStep 128119 = 192179) B192179
theorem B128139 : Blo 127788 128139 := bstep (se 1 (by rfl) ⟨96104, by rfl⟩ : syracuseStep 128139 = 192209) B192209
theorem B128151 : Blo 127788 128151 := bstep (se 1 (by rfl) ⟨96113, by rfl⟩ : syracuseStep 128151 = 192227) B192227
theorem B128171 : Blo 127788 128171 := bstep (se 1 (by rfl) ⟨96128, by rfl⟩ : syracuseStep 128171 = 192257) B192257
theorem B128183 : Blo 127788 128183 := bstep (se 1 (by rfl) ⟨96137, by rfl⟩ : syracuseStep 128183 = 192275) B192275
theorem B128203 : Blo 127788 128203 := bstep (se 1 (by rfl) ⟨96152, by rfl⟩ : syracuseStep 128203 = 192305) B192305
theorem B193739 : Blo 127788 193739 := bstep (se 1 (by rfl) ⟨145304, by rfl⟩ : syracuseStep 193739 = 290609) B290609
theorem B128215 : Blo 127788 128215 := bstep (se 1 (by rfl) ⟨96161, by rfl⟩ : syracuseStep 128215 = 192323) B192323
theorem B193751 : Blo 127788 193751 := bstep (se 1 (by rfl) ⟨145313, by rfl⟩ : syracuseStep 193751 = 290627) B290627
theorem B554201 : Blo 127788 554201 := bstep (se 2 (by rfl) ⟨207825, by rfl⟩ : syracuseStep 554201 = 415651) B415651
theorem B128235 : Blo 127788 128235 := bstep (se 1 (by rfl) ⟨96176, by rfl⟩ : syracuseStep 128235 = 192353) B192353
theorem B128247 : Blo 127788 128247 := bstep (se 1 (by rfl) ⟨96185, by rfl⟩ : syracuseStep 128247 = 192371) B192371
theorem B128267 : Blo 127788 128267 := bstep (se 1 (by rfl) ⟨96200, by rfl⟩ : syracuseStep 128267 = 192401) B192401
theorem B128279 : Blo 127788 128279 := bstep (se 1 (by rfl) ⟨96209, by rfl⟩ : syracuseStep 128279 = 192419) B192419
theorem B193817 : Blo 127788 193817 := bstep (se 2 (by rfl) ⟨72681, by rfl⟩ : syracuseStep 193817 = 145363) B145363
theorem B292121 : Blo 127788 292121 := bstep (se 2 (by rfl) ⟨109545, by rfl⟩ : syracuseStep 292121 = 219091) B219091
theorem B128299 : Blo 127788 128299 := bstep (se 1 (by rfl) ⟨96224, by rfl⟩ : syracuseStep 128299 = 192449) B192449
theorem B128311 : Blo 127788 128311 := bstep (se 1 (by rfl) ⟨96233, by rfl⟩ : syracuseStep 128311 = 192467) B192467
theorem B128331 : Blo 127788 128331 := bstep (se 1 (by rfl) ⟨96248, by rfl⟩ : syracuseStep 128331 = 192497) B192497
theorem B128343 : Blo 127788 128343 := bstep (se 1 (by rfl) ⟨96257, by rfl⟩ : syracuseStep 128343 = 192515) B192515
theorem B128363 : Blo 127788 128363 := bstep (se 1 (by rfl) ⟨96272, by rfl⟩ : syracuseStep 128363 = 192545) B192545
theorem B292211 : Blo 127788 292211 := bstep (se 1 (by rfl) ⟨219158, by rfl⟩ : syracuseStep 292211 = 438317) B438317
theorem B128375 : Blo 127788 128375 := bstep (se 1 (by rfl) ⟨96281, by rfl⟩ : syracuseStep 128375 = 192563) B192563
theorem B128395 : Blo 127788 128395 := bstep (se 1 (by rfl) ⟨96296, by rfl⟩ : syracuseStep 128395 = 192593) B192593
theorem B193931 : Blo 127788 193931 := bstep (se 1 (by rfl) ⟨145448, by rfl⟩ : syracuseStep 193931 = 290897) B290897
theorem B193943 : Blo 127788 193943 := bstep (se 1 (by rfl) ⟨145457, by rfl⟩ : syracuseStep 193943 = 290915) B290915
theorem B292247 : Blo 127788 292247 := bstep (se 1 (by rfl) ⟨219185, by rfl⟩ : syracuseStep 292247 = 438371) B438371
theorem B128407 : Blo 127788 128407 := bstep (se 1 (by rfl) ⟨96305, by rfl⟩ : syracuseStep 128407 = 192611) B192611
theorem B488855 : Blo 127788 488855 := bstep (se 1 (by rfl) ⟨366641, by rfl⟩ : syracuseStep 488855 = 733283) B733283
theorem B128427 : Blo 127788 128427 := bstep (se 1 (by rfl) ⟨96320, by rfl⟩ : syracuseStep 128427 = 192641) B192641
theorem B325043 : Blo 127788 325043 := bstep (se 1 (by rfl) ⟨243782, by rfl⟩ : syracuseStep 325043 = 487565) B487565
theorem B128439 : Blo 127788 128439 := bstep (se 1 (by rfl) ⟨96329, by rfl⟩ : syracuseStep 128439 = 192659) B192659
theorem B128459 : Blo 127788 128459 := bstep (se 1 (by rfl) ⟨96344, by rfl⟩ : syracuseStep 128459 = 192689) B192689
theorem B128471 : Blo 127788 128471 := bstep (se 1 (by rfl) ⟨96353, by rfl⟩ : syracuseStep 128471 = 192707) B192707
theorem B194009 : Blo 127788 194009 := bstep (se 2 (by rfl) ⟨72753, by rfl⟩ : syracuseStep 194009 = 145507) B145507
theorem B128491 : Blo 127788 128491 := bstep (se 1 (by rfl) ⟨96368, by rfl⟩ : syracuseStep 128491 = 192737) B192737
theorem B128503 : Blo 127788 128503 := bstep (se 1 (by rfl) ⟨96377, by rfl⟩ : syracuseStep 128503 = 192755) B192755
theorem B128523 : Blo 127788 128523 := bstep (se 1 (by rfl) ⟨96392, by rfl⟩ : syracuseStep 128523 = 192785) B192785
theorem B128535 : Blo 127788 128535 := bstep (se 1 (by rfl) ⟨96401, by rfl⟩ : syracuseStep 128535 = 192803) B192803
theorem B128555 : Blo 127788 128555 := bstep (se 1 (by rfl) ⟨96416, by rfl⟩ : syracuseStep 128555 = 192833) B192833
theorem B128567 : Blo 127788 128567 := bstep (se 1 (by rfl) ⟨96425, by rfl⟩ : syracuseStep 128567 = 192851) B192851
theorem B128587 : Blo 127788 128587 := bstep (se 1 (by rfl) ⟨96440, by rfl⟩ : syracuseStep 128587 = 192881) B192881
theorem B194123 : Blo 127788 194123 := bstep (se 1 (by rfl) ⟨145592, by rfl⟩ : syracuseStep 194123 = 291185) B291185
theorem B292427 : Blo 127788 292427 := bstep (se 1 (by rfl) ⟨219320, by rfl⟩ : syracuseStep 292427 = 438641) B438641
theorem B128599 : Blo 127788 128599 := bstep (se 1 (by rfl) ⟨96449, by rfl⟩ : syracuseStep 128599 = 192899) B192899
theorem B194135 : Blo 127788 194135 := bstep (se 1 (by rfl) ⟨145601, by rfl⟩ : syracuseStep 194135 = 291203) B291203
theorem B128619 : Blo 127788 128619 := bstep (se 1 (by rfl) ⟨96464, by rfl⟩ : syracuseStep 128619 = 192929) B192929
theorem B128631 : Blo 127788 128631 := bstep (se 1 (by rfl) ⟨96473, by rfl⟩ : syracuseStep 128631 = 192947) B192947
theorem B292481 : Blo 127788 292481 := bstep (se 2 (by rfl) ⟨109680, by rfl⟩ : syracuseStep 292481 = 219361) B219361
theorem B128651 : Blo 127788 128651 := bstep (se 1 (by rfl) ⟨96488, by rfl⟩ : syracuseStep 128651 = 192977) B192977
theorem B128663 : Blo 127788 128663 := bstep (se 1 (by rfl) ⟨96497, by rfl⟩ : syracuseStep 128663 = 192995) B192995
theorem B194201 : Blo 127788 194201 := bstep (se 2 (by rfl) ⟨72825, by rfl⟩ : syracuseStep 194201 = 145651) B145651
theorem B128683 : Blo 127788 128683 := bstep (se 1 (by rfl) ⟨96512, by rfl⟩ : syracuseStep 128683 = 193025) B193025
theorem B128695 : Blo 127788 128695 := bstep (se 1 (by rfl) ⟨96521, by rfl⟩ : syracuseStep 128695 = 193043) B193043
theorem B128715 : Blo 127788 128715 := bstep (se 1 (by rfl) ⟨96536, by rfl⟩ : syracuseStep 128715 = 193073) B193073
theorem B128727 : Blo 127788 128727 := bstep (se 1 (by rfl) ⟨96545, by rfl⟩ : syracuseStep 128727 = 193091) B193091
theorem B128747 : Blo 127788 128747 := bstep (se 1 (by rfl) ⟨96560, by rfl⟩ : syracuseStep 128747 = 193121) B193121
theorem B128759 : Blo 127788 128759 := bstep (se 1 (by rfl) ⟨96569, by rfl⟩ : syracuseStep 128759 = 193139) B193139
theorem B128779 : Blo 127788 128779 := bstep (se 1 (by rfl) ⟨96584, by rfl⟩ : syracuseStep 128779 = 193169) B193169
theorem B194315 : Blo 127788 194315 := bstep (se 1 (by rfl) ⟨145736, by rfl⟩ : syracuseStep 194315 = 291473) B291473
theorem B128791 : Blo 127788 128791 := bstep (se 1 (by rfl) ⟨96593, by rfl⟩ : syracuseStep 128791 = 193187) B193187
theorem B194327 : Blo 127788 194327 := bstep (se 1 (by rfl) ⟨145745, by rfl⟩ : syracuseStep 194327 = 291491) B291491
theorem B128811 : Blo 127788 128811 := bstep (se 1 (by rfl) ⟨96608, by rfl⟩ : syracuseStep 128811 = 193217) B193217
theorem B128823 : Blo 127788 128823 := bstep (se 1 (by rfl) ⟨96617, by rfl⟩ : syracuseStep 128823 = 193235) B193235
theorem B128843 : Blo 127788 128843 := bstep (se 1 (by rfl) ⟨96632, by rfl⟩ : syracuseStep 128843 = 193265) B193265
theorem B128855 : Blo 127788 128855 := bstep (se 1 (by rfl) ⟨96641, by rfl⟩ : syracuseStep 128855 = 193283) B193283
theorem B194393 : Blo 127788 194393 := bstep (se 2 (by rfl) ⟨72897, by rfl⟩ : syracuseStep 194393 = 145795) B145795
theorem B292697 : Blo 127788 292697 := bstep (se 2 (by rfl) ⟨109761, by rfl⟩ : syracuseStep 292697 = 219523) B219523
theorem B128875 : Blo 127788 128875 := bstep (se 1 (by rfl) ⟨96656, by rfl⟩ : syracuseStep 128875 = 193313) B193313
theorem B128887 : Blo 127788 128887 := bstep (se 1 (by rfl) ⟨96665, by rfl⟩ : syracuseStep 128887 = 193331) B193331
theorem B128907 : Blo 127788 128907 := bstep (se 1 (by rfl) ⟨96680, by rfl⟩ : syracuseStep 128907 = 193361) B193361
theorem B128919 : Blo 127788 128919 := bstep (se 1 (by rfl) ⟨96689, by rfl⟩ : syracuseStep 128919 = 193379) B193379
theorem B128939 : Blo 127788 128939 := bstep (se 1 (by rfl) ⟨96704, by rfl⟩ : syracuseStep 128939 = 193409) B193409
theorem B292787 : Blo 127788 292787 := bstep (se 1 (by rfl) ⟨219590, by rfl⟩ : syracuseStep 292787 = 439181) B439181
theorem B128951 : Blo 127788 128951 := bstep (se 1 (by rfl) ⟨96713, by rfl⟩ : syracuseStep 128951 = 193427) B193427
theorem B325579 : Blo 127788 325579 := bstep (se 1 (by rfl) ⟨244184, by rfl⟩ : syracuseStep 325579 = 488369) B488369
theorem B128971 : Blo 127788 128971 := bstep (se 1 (by rfl) ⟨96728, by rfl⟩ : syracuseStep 128971 = 193457) B193457
theorem B194507 : Blo 127788 194507 := bstep (se 1 (by rfl) ⟨145880, by rfl⟩ : syracuseStep 194507 = 291761) B291761
theorem B128983 : Blo 127788 128983 := bstep (se 1 (by rfl) ⟨96737, by rfl⟩ : syracuseStep 128983 = 193475) B193475
theorem B194519 : Blo 127788 194519 := bstep (se 1 (by rfl) ⟨145889, by rfl⟩ : syracuseStep 194519 = 291779) B291779
theorem B292823 : Blo 127788 292823 := bstep (se 1 (by rfl) ⟨219617, by rfl⟩ : syracuseStep 292823 = 439235) B439235
theorem B129003 : Blo 127788 129003 := bstep (se 1 (by rfl) ⟨96752, by rfl⟩ : syracuseStep 129003 = 193505) B193505
theorem B129015 : Blo 127788 129015 := bstep (se 1 (by rfl) ⟨96761, by rfl⟩ : syracuseStep 129015 = 193523) B193523
theorem B129035 : Blo 127788 129035 := bstep (se 1 (by rfl) ⟨96776, by rfl⟩ : syracuseStep 129035 = 193553) B193553
theorem B129047 : Blo 127788 129047 := bstep (se 1 (by rfl) ⟨96785, by rfl⟩ : syracuseStep 129047 = 193571) B193571
theorem B194585 : Blo 127788 194585 := bstep (se 2 (by rfl) ⟨72969, by rfl⟩ : syracuseStep 194585 = 145939) B145939
theorem B129067 : Blo 127788 129067 := bstep (se 1 (by rfl) ⟨96800, by rfl⟩ : syracuseStep 129067 = 193601) B193601
theorem B489523 : Blo 127788 489523 := bstep (se 1 (by rfl) ⟨367142, by rfl⟩ : syracuseStep 489523 = 734285) B734285
theorem B129079 : Blo 127788 129079 := bstep (se 1 (by rfl) ⟨96809, by rfl⟩ : syracuseStep 129079 = 193619) B193619
theorem B129099 : Blo 127788 129099 := bstep (se 1 (by rfl) ⟨96824, by rfl⟩ : syracuseStep 129099 = 193649) B193649
theorem B129111 : Blo 127788 129111 := bstep (se 1 (by rfl) ⟨96833, by rfl⟩ : syracuseStep 129111 = 193667) B193667
theorem B325721 : Blo 127788 325721 := bstep (se 2 (by rfl) ⟨122145, by rfl⟩ : syracuseStep 325721 = 244291) B244291
theorem B129131 : Blo 127788 129131 := bstep (se 1 (by rfl) ⟨96848, by rfl⟩ : syracuseStep 129131 = 193697) B193697
theorem B129143 : Blo 127788 129143 := bstep (se 1 (by rfl) ⟨96857, by rfl⟩ : syracuseStep 129143 = 193715) B193715
theorem B129163 : Blo 127788 129163 := bstep (se 1 (by rfl) ⟨96872, by rfl⟩ : syracuseStep 129163 = 193745) B193745
theorem B194699 : Blo 127788 194699 := bstep (se 1 (by rfl) ⟨146024, by rfl⟩ : syracuseStep 194699 = 292049) B292049
theorem B293003 : Blo 127788 293003 := bstep (se 1 (by rfl) ⟨219752, by rfl⟩ : syracuseStep 293003 = 439505) B439505
theorem B129175 : Blo 127788 129175 := bstep (se 1 (by rfl) ⟨96881, by rfl⟩ : syracuseStep 129175 = 193763) B193763
theorem B194711 : Blo 127788 194711 := bstep (se 1 (by rfl) ⟨146033, by rfl⟩ : syracuseStep 194711 = 292067) B292067
theorem B129195 : Blo 127788 129195 := bstep (se 1 (by rfl) ⟨96896, by rfl⟩ : syracuseStep 129195 = 193793) B193793
theorem B129207 : Blo 127788 129207 := bstep (se 1 (by rfl) ⟨96905, by rfl⟩ : syracuseStep 129207 = 193811) B193811
theorem B293057 : Blo 127788 293057 := bstep (se 2 (by rfl) ⟨109896, by rfl⟩ : syracuseStep 293057 = 219793) B219793
theorem B161995 : Blo 127788 161995 := bstep (se 1 (by rfl) ⟨121496, by rfl⟩ : syracuseStep 161995 = 242993) B242993
theorem B129227 : Blo 127788 129227 := bstep (se 1 (by rfl) ⟨96920, by rfl⟩ : syracuseStep 129227 = 193841) B193841
theorem B129239 : Blo 127788 129239 := bstep (se 1 (by rfl) ⟨96929, by rfl⟩ : syracuseStep 129239 = 193859) B193859
theorem B194777 : Blo 127788 194777 := bstep (se 2 (by rfl) ⟨73041, by rfl⟩ : syracuseStep 194777 = 146083) B146083
theorem B129259 : Blo 127788 129259 := bstep (se 1 (by rfl) ⟨96944, by rfl⟩ : syracuseStep 129259 = 193889) B193889
theorem B129271 : Blo 127788 129271 := bstep (se 1 (by rfl) ⟨96953, by rfl⟩ : syracuseStep 129271 = 193907) B193907
theorem B129291 : Blo 127788 129291 := bstep (se 1 (by rfl) ⟨96968, by rfl⟩ : syracuseStep 129291 = 193937) B193937
theorem B129303 : Blo 127788 129303 := bstep (se 1 (by rfl) ⟨96977, by rfl⟩ : syracuseStep 129303 = 193955) B193955
theorem B129323 : Blo 127788 129323 := bstep (se 1 (by rfl) ⟨96992, by rfl⟩ : syracuseStep 129323 = 193985) B193985
theorem B129335 : Blo 127788 129335 := bstep (se 1 (by rfl) ⟨97001, by rfl⟩ : syracuseStep 129335 = 194003) B194003
theorem B129355 : Blo 127788 129355 := bstep (se 1 (by rfl) ⟨97016, by rfl⟩ : syracuseStep 129355 = 194033) B194033
theorem B194891 : Blo 127788 194891 := bstep (se 1 (by rfl) ⟨146168, by rfl⟩ : syracuseStep 194891 = 292337) B292337
theorem B129367 : Blo 127788 129367 := bstep (se 1 (by rfl) ⟨97025, by rfl⟩ : syracuseStep 129367 = 194051) B194051
theorem B194903 : Blo 127788 194903 := bstep (se 1 (by rfl) ⟨146177, by rfl⟩ : syracuseStep 194903 = 292355) B292355
theorem B129387 : Blo 127788 129387 := bstep (se 1 (by rfl) ⟨97040, by rfl⟩ : syracuseStep 129387 = 194081) B194081
theorem B129399 : Blo 127788 129399 := bstep (se 1 (by rfl) ⟨97049, by rfl⟩ : syracuseStep 129399 = 194099) B194099
theorem B129419 : Blo 127788 129419 := bstep (se 1 (by rfl) ⟨97064, by rfl⟩ : syracuseStep 129419 = 194129) B194129
theorem B129431 : Blo 127788 129431 := bstep (se 1 (by rfl) ⟨97073, by rfl⟩ : syracuseStep 129431 = 194147) B194147
theorem B194969 : Blo 127788 194969 := bstep (se 2 (by rfl) ⟨73113, by rfl⟩ : syracuseStep 194969 = 146227) B146227
theorem B293273 : Blo 127788 293273 := bstep (se 2 (by rfl) ⟨109977, by rfl⟩ : syracuseStep 293273 = 219955) B219955
theorem B129451 : Blo 127788 129451 := bstep (se 1 (by rfl) ⟨97088, by rfl⟩ : syracuseStep 129451 = 194177) B194177
theorem B129463 : Blo 127788 129463 := bstep (se 1 (by rfl) ⟨97097, by rfl⟩ : syracuseStep 129463 = 194195) B194195
theorem B129483 : Blo 127788 129483 := bstep (se 1 (by rfl) ⟨97112, by rfl⟩ : syracuseStep 129483 = 194225) B194225
theorem B162263 : Blo 127788 162263 := bstep (se 1 (by rfl) ⟨121697, by rfl⟩ : syracuseStep 162263 = 243395) B243395
theorem B129495 : Blo 127788 129495 := bstep (se 1 (by rfl) ⟨97121, by rfl⟩ : syracuseStep 129495 = 194243) B194243
theorem B621017 : Blo 127788 621017 := bstep (se 2 (by rfl) ⟨232881, by rfl⟩ : syracuseStep 621017 = 465763) B465763
theorem B129515 : Blo 127788 129515 := bstep (se 1 (by rfl) ⟨97136, by rfl⟩ : syracuseStep 129515 = 194273) B194273
theorem B293363 : Blo 127788 293363 := bstep (se 1 (by rfl) ⟨220022, by rfl⟩ : syracuseStep 293363 = 440045) B440045
theorem B129527 : Blo 127788 129527 := bstep (se 1 (by rfl) ⟨97145, by rfl⟩ : syracuseStep 129527 = 194291) B194291
theorem B129547 : Blo 127788 129547 := bstep (se 1 (by rfl) ⟨97160, by rfl⟩ : syracuseStep 129547 = 194321) B194321
theorem B195083 : Blo 127788 195083 := bstep (se 1 (by rfl) ⟨146312, by rfl⟩ : syracuseStep 195083 = 292625) B292625
theorem B129559 : Blo 127788 129559 := bstep (se 1 (by rfl) ⟨97169, by rfl⟩ : syracuseStep 129559 = 194339) B194339
theorem B195095 : Blo 127788 195095 := bstep (se 1 (by rfl) ⟨146321, by rfl⟩ : syracuseStep 195095 = 292643) B292643
theorem B293399 : Blo 127788 293399 := bstep (se 1 (by rfl) ⟨220049, by rfl⟩ : syracuseStep 293399 = 440099) B440099
theorem B129579 : Blo 127788 129579 := bstep (se 1 (by rfl) ⟨97184, by rfl⟩ : syracuseStep 129579 = 194369) B194369
theorem B129591 : Blo 127788 129591 := bstep (se 1 (by rfl) ⟨97193, by rfl⟩ : syracuseStep 129591 = 194387) B194387
theorem B129611 : Blo 127788 129611 := bstep (se 1 (by rfl) ⟨97208, by rfl⟩ : syracuseStep 129611 = 194417) B194417
theorem B129623 : Blo 127788 129623 := bstep (se 1 (by rfl) ⟨97217, by rfl⟩ : syracuseStep 129623 = 194435) B194435
theorem B195161 : Blo 127788 195161 := bstep (se 2 (by rfl) ⟨73185, by rfl⟩ : syracuseStep 195161 = 146371) B146371
theorem B129643 : Blo 127788 129643 := bstep (se 1 (by rfl) ⟨97232, by rfl⟩ : syracuseStep 129643 = 194465) B194465
theorem B129655 : Blo 127788 129655 := bstep (se 1 (by rfl) ⟨97241, by rfl⟩ : syracuseStep 129655 = 194483) B194483
theorem B129675 : Blo 127788 129675 := bstep (se 1 (by rfl) ⟨97256, by rfl⟩ : syracuseStep 129675 = 194513) B194513
theorem B129687 : Blo 127788 129687 := bstep (se 1 (by rfl) ⟨97265, by rfl⟩ : syracuseStep 129687 = 194531) B194531
theorem B129707 : Blo 127788 129707 := bstep (se 1 (by rfl) ⟨97280, by rfl⟩ : syracuseStep 129707 = 194561) B194561
theorem B129719 : Blo 127788 129719 := bstep (se 1 (by rfl) ⟨97289, by rfl⟩ : syracuseStep 129719 = 194579) B194579
theorem B129739 : Blo 127788 129739 := bstep (se 1 (by rfl) ⟨97304, by rfl⟩ : syracuseStep 129739 = 194609) B194609
theorem B195275 : Blo 127788 195275 := bstep (se 1 (by rfl) ⟨146456, by rfl⟩ : syracuseStep 195275 = 292913) B292913
theorem B293579 : Blo 127788 293579 := bstep (se 1 (by rfl) ⟨220184, by rfl⟩ : syracuseStep 293579 = 440369) B440369
theorem B129751 : Blo 127788 129751 := bstep (se 1 (by rfl) ⟨97313, by rfl⟩ : syracuseStep 129751 = 194627) B194627
theorem B195287 : Blo 127788 195287 := bstep (se 1 (by rfl) ⟨146465, by rfl⟩ : syracuseStep 195287 = 292931) B292931
theorem B129771 : Blo 127788 129771 := bstep (se 1 (by rfl) ⟨97328, by rfl⟩ : syracuseStep 129771 = 194657) B194657
theorem B129783 : Blo 127788 129783 := bstep (se 1 (by rfl) ⟨97337, by rfl⟩ : syracuseStep 129783 = 194675) B194675
theorem B293633 : Blo 127788 293633 := bstep (se 2 (by rfl) ⟨110112, by rfl⟩ : syracuseStep 293633 = 220225) B220225
theorem B129803 : Blo 127788 129803 := bstep (se 1 (by rfl) ⟨97352, by rfl⟩ : syracuseStep 129803 = 194705) B194705
theorem B129815 : Blo 127788 129815 := bstep (se 1 (by rfl) ⟨97361, by rfl⟩ : syracuseStep 129815 = 194723) B194723
theorem B195353 : Blo 127788 195353 := bstep (se 2 (by rfl) ⟨73257, by rfl⟩ : syracuseStep 195353 = 146515) B146515
theorem B129835 : Blo 127788 129835 := bstep (se 1 (by rfl) ⟨97376, by rfl⟩ : syracuseStep 129835 = 194753) B194753
theorem B129847 : Blo 127788 129847 := bstep (se 1 (by rfl) ⟨97385, by rfl⟩ : syracuseStep 129847 = 194771) B194771
theorem B654155 : Blo 127788 654155 := bstep (se 1 (by rfl) ⟨490616, by rfl⟩ : syracuseStep 654155 = 981233) B981233
theorem B129867 : Blo 127788 129867 := bstep (se 1 (by rfl) ⟨97400, by rfl⟩ : syracuseStep 129867 = 194801) B194801
theorem B129879 : Blo 127788 129879 := bstep (se 1 (by rfl) ⟨97409, by rfl⟩ : syracuseStep 129879 = 194819) B194819
theorem B359257 : Blo 127788 359257 := bstep (se 2 (by rfl) ⟨134721, by rfl⟩ : syracuseStep 359257 = 269443) B269443
theorem B129899 : Blo 127788 129899 := bstep (se 1 (by rfl) ⟨97424, by rfl⟩ : syracuseStep 129899 = 194849) B194849
theorem B129911 : Blo 127788 129911 := bstep (se 1 (by rfl) ⟨97433, by rfl⟩ : syracuseStep 129911 = 194867) B194867
theorem B129931 : Blo 127788 129931 := bstep (se 1 (by rfl) ⟨97448, by rfl⟩ : syracuseStep 129931 = 194897) B194897
theorem B195467 : Blo 127788 195467 := bstep (se 1 (by rfl) ⟨146600, by rfl⟩ : syracuseStep 195467 = 293201) B293201
theorem B326551 : Blo 127788 326551 := bstep (se 1 (by rfl) ⟨244913, by rfl⟩ : syracuseStep 326551 = 489827) B489827
theorem B129943 : Blo 127788 129943 := bstep (se 1 (by rfl) ⟨97457, by rfl⟩ : syracuseStep 129943 = 194915) B194915
theorem B195479 : Blo 127788 195479 := bstep (se 1 (by rfl) ⟨146609, by rfl⟩ : syracuseStep 195479 = 293219) B293219
theorem B129963 : Blo 127788 129963 := bstep (se 1 (by rfl) ⟨97472, by rfl⟩ : syracuseStep 129963 = 194945) B194945
theorem B129975 : Blo 127788 129975 := bstep (se 1 (by rfl) ⟨97481, by rfl⟩ : syracuseStep 129975 = 194963) B194963
theorem B129995 : Blo 127788 129995 := bstep (se 1 (by rfl) ⟨97496, by rfl⟩ : syracuseStep 129995 = 194993) B194993
theorem B130007 : Blo 127788 130007 := bstep (se 1 (by rfl) ⟨97505, by rfl⟩ : syracuseStep 130007 = 195011) B195011
theorem B195545 : Blo 127788 195545 := bstep (se 2 (by rfl) ⟨73329, by rfl⟩ : syracuseStep 195545 = 146659) B146659
theorem B293849 : Blo 127788 293849 := bstep (se 2 (by rfl) ⟨110193, by rfl⟩ : syracuseStep 293849 = 220387) B220387
theorem B130027 : Blo 127788 130027 := bstep (se 1 (by rfl) ⟨97520, by rfl⟩ : syracuseStep 130027 = 195041) B195041
theorem B130039 : Blo 127788 130039 := bstep (se 1 (by rfl) ⟨97529, by rfl⟩ : syracuseStep 130039 = 195059) B195059
theorem B130059 : Blo 127788 130059 := bstep (se 1 (by rfl) ⟨97544, by rfl⟩ : syracuseStep 130059 = 195089) B195089
theorem B130071 : Blo 127788 130071 := bstep (se 1 (by rfl) ⟨97553, by rfl⟩ : syracuseStep 130071 = 195107) B195107
theorem B130091 : Blo 127788 130091 := bstep (se 1 (by rfl) ⟨97568, by rfl⟩ : syracuseStep 130091 = 195137) B195137
theorem B293939 : Blo 127788 293939 := bstep (se 1 (by rfl) ⟨220454, by rfl⟩ : syracuseStep 293939 = 440909) B440909
theorem B130103 : Blo 127788 130103 := bstep (se 1 (by rfl) ⟨97577, by rfl⟩ : syracuseStep 130103 = 195155) B195155
theorem B130123 : Blo 127788 130123 := bstep (se 1 (by rfl) ⟨97592, by rfl⟩ : syracuseStep 130123 = 195185) B195185
theorem B195659 : Blo 127788 195659 := bstep (se 1 (by rfl) ⟨146744, by rfl⟩ : syracuseStep 195659 = 293489) B293489
theorem B228427 : Blo 127788 228427 := bstep (se 1 (by rfl) ⟨171320, by rfl⟩ : syracuseStep 228427 = 342641) B342641
theorem B130135 : Blo 127788 130135 := bstep (se 1 (by rfl) ⟨97601, by rfl⟩ : syracuseStep 130135 = 195203) B195203
theorem B195671 : Blo 127788 195671 := bstep (se 1 (by rfl) ⟨146753, by rfl⟩ : syracuseStep 195671 = 293507) B293507
theorem B293975 : Blo 127788 293975 := bstep (se 1 (by rfl) ⟨220481, by rfl⟩ : syracuseStep 293975 = 440963) B440963
theorem B130155 : Blo 127788 130155 := bstep (se 1 (by rfl) ⟨97616, by rfl⟩ : syracuseStep 130155 = 195233) B195233
theorem B130167 : Blo 127788 130167 := bstep (se 1 (by rfl) ⟨97625, by rfl⟩ : syracuseStep 130167 = 195251) B195251
theorem B130187 : Blo 127788 130187 := bstep (se 1 (by rfl) ⟨97640, by rfl⟩ : syracuseStep 130187 = 195281) B195281
theorem B162967 : Blo 127788 162967 := bstep (se 1 (by rfl) ⟨122225, by rfl⟩ : syracuseStep 162967 = 244451) B244451
theorem B130199 : Blo 127788 130199 := bstep (se 1 (by rfl) ⟨97649, by rfl⟩ : syracuseStep 130199 = 195299) B195299
theorem B195737 : Blo 127788 195737 := bstep (se 2 (by rfl) ⟨73401, by rfl⟩ : syracuseStep 195737 = 146803) B146803
theorem B130219 : Blo 127788 130219 := bstep (se 1 (by rfl) ⟨97664, by rfl⟩ : syracuseStep 130219 = 195329) B195329
theorem B130231 : Blo 127788 130231 := bstep (se 1 (by rfl) ⟨97673, by rfl⟩ : syracuseStep 130231 = 195347) B195347
theorem B130251 : Blo 127788 130251 := bstep (se 1 (by rfl) ⟨97688, by rfl⟩ : syracuseStep 130251 = 195377) B195377
theorem B130263 : Blo 127788 130263 := bstep (se 1 (by rfl) ⟨97697, by rfl⟩ : syracuseStep 130263 = 195395) B195395
theorem B130283 : Blo 127788 130283 := bstep (se 1 (by rfl) ⟨97712, by rfl⟩ : syracuseStep 130283 = 195425) B195425
theorem B130295 : Blo 127788 130295 := bstep (se 1 (by rfl) ⟨97721, by rfl⟩ : syracuseStep 130295 = 195443) B195443
theorem B294155 : Blo 127788 294155 := bstep (se 1 (by rfl) ⟨220616, by rfl⟩ : syracuseStep 294155 = 441233) B441233
theorem B130315 : Blo 127788 130315 := bstep (se 1 (by rfl) ⟨97736, by rfl⟩ : syracuseStep 130315 = 195473) B195473
theorem B195851 : Blo 127788 195851 := bstep (se 1 (by rfl) ⟨146888, by rfl⟩ : syracuseStep 195851 = 293777) B293777
theorem B490769 : Blo 127788 490769 := bstep (se 2 (by rfl) ⟨184038, by rfl⟩ : syracuseStep 490769 = 368077) B368077
theorem B130327 : Blo 127788 130327 := bstep (se 1 (by rfl) ⟨97745, by rfl⟩ : syracuseStep 130327 = 195491) B195491
theorem B195863 : Blo 127788 195863 := bstep (se 1 (by rfl) ⟨146897, by rfl⟩ : syracuseStep 195863 = 293795) B293795
theorem B130347 : Blo 127788 130347 := bstep (se 1 (by rfl) ⟨97760, by rfl⟩ : syracuseStep 130347 = 195521) B195521
theorem B130359 : Blo 127788 130359 := bstep (se 1 (by rfl) ⟨97769, by rfl⟩ : syracuseStep 130359 = 195539) B195539
theorem B294209 : Blo 127788 294209 := bstep (se 2 (by rfl) ⟨110328, by rfl⟩ : syracuseStep 294209 = 220657) B220657
theorem B326987 : Blo 127788 326987 := bstep (se 1 (by rfl) ⟨245240, by rfl⟩ : syracuseStep 326987 = 490481) B490481
theorem B130379 : Blo 127788 130379 := bstep (se 1 (by rfl) ⟨97784, by rfl⟩ : syracuseStep 130379 = 195569) B195569
theorem B130391 : Blo 127788 130391 := bstep (se 1 (by rfl) ⟨97793, by rfl⟩ : syracuseStep 130391 = 195587) B195587
theorem B195929 : Blo 127788 195929 := bstep (se 2 (by rfl) ⟨73473, by rfl⟩ : syracuseStep 195929 = 146947) B146947
theorem B130411 : Blo 127788 130411 := bstep (se 1 (by rfl) ⟨97808, by rfl⟩ : syracuseStep 130411 = 195617) B195617
theorem B130423 : Blo 127788 130423 := bstep (se 1 (by rfl) ⟨97817, by rfl⟩ : syracuseStep 130423 = 195635) B195635
theorem B130443 : Blo 127788 130443 := bstep (se 1 (by rfl) ⟨97832, by rfl⟩ : syracuseStep 130443 = 195665) B195665
theorem B130455 : Blo 127788 130455 := bstep (se 1 (by rfl) ⟨97841, by rfl⟩ : syracuseStep 130455 = 195683) B195683
theorem B130475 : Blo 127788 130475 := bstep (se 1 (by rfl) ⟨97856, by rfl⟩ : syracuseStep 130475 = 195713) B195713
theorem B130487 : Blo 127788 130487 := bstep (se 1 (by rfl) ⟨97865, by rfl⟩ : syracuseStep 130487 = 195731) B195731
theorem B130507 : Blo 127788 130507 := bstep (se 1 (by rfl) ⟨97880, by rfl⟩ : syracuseStep 130507 = 195761) B195761
theorem B196043 : Blo 127788 196043 := bstep (se 1 (by rfl) ⟨147032, by rfl⟩ : syracuseStep 196043 = 294065) B294065
theorem B130519 : Blo 127788 130519 := bstep (se 1 (by rfl) ⟨97889, by rfl⟩ : syracuseStep 130519 = 195779) B195779
theorem B196055 : Blo 127788 196055 := bstep (se 1 (by rfl) ⟨147041, by rfl⟩ : syracuseStep 196055 = 294083) B294083
theorem B130539 : Blo 127788 130539 := bstep (se 1 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 130539 = 195809) B195809
theorem B130551 : Blo 127788 130551 := bstep (se 1 (by rfl) ⟨97913, by rfl⟩ : syracuseStep 130551 = 195827) B195827
theorem B130571 : Blo 127788 130571 := bstep (se 1 (by rfl) ⟨97928, by rfl⟩ : syracuseStep 130571 = 195857) B195857
theorem B130583 : Blo 127788 130583 := bstep (se 1 (by rfl) ⟨97937, by rfl⟩ : syracuseStep 130583 = 195875) B195875
theorem B196121 : Blo 127788 196121 := bstep (se 2 (by rfl) ⟨73545, by rfl⟩ : syracuseStep 196121 = 147091) B147091
theorem B294425 : Blo 127788 294425 := bstep (se 2 (by rfl) ⟨110409, by rfl⟩ : syracuseStep 294425 = 220819) B220819
theorem B130603 : Blo 127788 130603 := bstep (se 1 (by rfl) ⟨97952, by rfl⟩ : syracuseStep 130603 = 195905) B195905
theorem B130615 : Blo 127788 130615 := bstep (se 1 (by rfl) ⟨97961, by rfl⟩ : syracuseStep 130615 = 195923) B195923
theorem B130635 : Blo 127788 130635 := bstep (se 1 (by rfl) ⟨97976, by rfl⟩ : syracuseStep 130635 = 195953) B195953
theorem B130647 : Blo 127788 130647 := bstep (se 1 (by rfl) ⟨97985, by rfl⟩ : syracuseStep 130647 = 195971) B195971
theorem B130667 : Blo 127788 130667 := bstep (se 1 (by rfl) ⟨98000, by rfl⟩ : syracuseStep 130667 = 196001) B196001
theorem B294515 : Blo 127788 294515 := bstep (se 1 (by rfl) ⟨220886, by rfl⟩ : syracuseStep 294515 = 441773) B441773
theorem B130679 : Blo 127788 130679 := bstep (se 1 (by rfl) ⟨98009, by rfl⟩ : syracuseStep 130679 = 196019) B196019
theorem B130699 : Blo 127788 130699 := bstep (se 1 (by rfl) ⟨98024, by rfl⟩ : syracuseStep 130699 = 196049) B196049
theorem B196235 : Blo 127788 196235 := bstep (se 1 (by rfl) ⟨147176, by rfl⟩ : syracuseStep 196235 = 294353) B294353
theorem B130711 : Blo 127788 130711 := bstep (se 1 (by rfl) ⟨98033, by rfl⟩ : syracuseStep 130711 = 196067) B196067
theorem B196247 : Blo 127788 196247 := bstep (se 1 (by rfl) ⟨147185, by rfl⟩ : syracuseStep 196247 = 294371) B294371
theorem B294551 : Blo 127788 294551 := bstep (se 1 (by rfl) ⟨220913, by rfl⟩ : syracuseStep 294551 = 441827) B441827
theorem B130731 : Blo 127788 130731 := bstep (se 1 (by rfl) ⟨98048, by rfl⟩ : syracuseStep 130731 = 196097) B196097
theorem B130743 : Blo 127788 130743 := bstep (se 1 (by rfl) ⟨98057, by rfl⟩ : syracuseStep 130743 = 196115) B196115
theorem B327361 : Blo 127788 327361 := bstep (se 2 (by rfl) ⟨122760, by rfl⟩ : syracuseStep 327361 = 245521) B245521
theorem B130763 : Blo 127788 130763 := bstep (se 1 (by rfl) ⟨98072, by rfl⟩ : syracuseStep 130763 = 196145) B196145
theorem B130775 : Blo 127788 130775 := bstep (se 1 (by rfl) ⟨98081, by rfl⟩ : syracuseStep 130775 = 196163) B196163
theorem B196313 : Blo 127788 196313 := bstep (se 2 (by rfl) ⟨73617, by rfl⟩ : syracuseStep 196313 = 147235) B147235
theorem B130795 : Blo 127788 130795 := bstep (se 1 (by rfl) ⟨98096, by rfl⟩ : syracuseStep 130795 = 196193) B196193
theorem B130807 : Blo 127788 130807 := bstep (se 1 (by rfl) ⟨98105, by rfl⟩ : syracuseStep 130807 = 196211) B196211
theorem B130827 : Blo 127788 130827 := bstep (se 1 (by rfl) ⟨98120, by rfl⟩ : syracuseStep 130827 = 196241) B196241
theorem B130839 : Blo 127788 130839 := bstep (se 1 (by rfl) ⟨98129, by rfl⟩ : syracuseStep 130839 = 196259) B196259
theorem B130859 : Blo 127788 130859 := bstep (se 1 (by rfl) ⟨98144, by rfl⟩ : syracuseStep 130859 = 196289) B196289
theorem B130871 : Blo 127788 130871 := bstep (se 1 (by rfl) ⟨98153, by rfl⟩ : syracuseStep 130871 = 196307) B196307
theorem B556865 : Blo 127788 556865 := bstep (se 2 (by rfl) ⟨208824, by rfl⟩ : syracuseStep 556865 = 417649) B417649
theorem B294731 : Blo 127788 294731 := bstep (se 1 (by rfl) ⟨221048, by rfl⟩ : syracuseStep 294731 = 442097) B442097
theorem B130891 : Blo 127788 130891 := bstep (se 1 (by rfl) ⟨98168, by rfl⟩ : syracuseStep 130891 = 196337) B196337
theorem B196427 : Blo 127788 196427 := bstep (se 1 (by rfl) ⟨147320, by rfl⟩ : syracuseStep 196427 = 294641) B294641
theorem B130903 : Blo 127788 130903 := bstep (se 1 (by rfl) ⟨98177, by rfl⟩ : syracuseStep 130903 = 196355) B196355
theorem B196439 : Blo 127788 196439 := bstep (se 1 (by rfl) ⟨147329, by rfl⟩ : syracuseStep 196439 = 294659) B294659
theorem B130923 : Blo 127788 130923 := bstep (se 1 (by rfl) ⟨98192, by rfl⟩ : syracuseStep 130923 = 196385) B196385
theorem B130935 : Blo 127788 130935 := bstep (se 1 (by rfl) ⟨98201, by rfl⟩ : syracuseStep 130935 = 196403) B196403
theorem B294785 : Blo 127788 294785 := bstep (se 2 (by rfl) ⟨110544, by rfl⟩ : syracuseStep 294785 = 221089) B221089
theorem B130955 : Blo 127788 130955 := bstep (se 1 (by rfl) ⟨98216, by rfl⟩ : syracuseStep 130955 = 196433) B196433
theorem B524177 : Blo 127788 524177 := bstep (se 2 (by rfl) ⟨196566, by rfl⟩ : syracuseStep 524177 = 393133) B393133
theorem B130967 : Blo 127788 130967 := bstep (se 1 (by rfl) ⟨98225, by rfl⟩ : syracuseStep 130967 = 196451) B196451
theorem B196505 : Blo 127788 196505 := bstep (se 2 (by rfl) ⟨73689, by rfl⟩ : syracuseStep 196505 = 147379) B147379
theorem B130987 : Blo 127788 130987 := bstep (se 1 (by rfl) ⟨98240, by rfl⟩ : syracuseStep 130987 = 196481) B196481
theorem B130999 : Blo 127788 130999 := bstep (se 1 (by rfl) ⟨98249, by rfl⟩ : syracuseStep 130999 = 196499) B196499
theorem B491467 : Blo 127788 491467 := bstep (se 1 (by rfl) ⟨368600, by rfl⟩ : syracuseStep 491467 = 737201) B737201
theorem B131019 : Blo 127788 131019 := bstep (se 1 (by rfl) ⟨98264, by rfl⟩ : syracuseStep 131019 = 196529) B196529
theorem B131031 : Blo 127788 131031 := bstep (se 1 (by rfl) ⟨98273, by rfl⟩ : syracuseStep 131031 = 196547) B196547
theorem B1114073 : Blo 127788 1114073 := bstep (se 2 (by rfl) ⟨417777, by rfl⟩ : syracuseStep 1114073 = 835555) B835555
theorem B131051 : Blo 127788 131051 := bstep (se 1 (by rfl) ⟨98288, by rfl⟩ : syracuseStep 131051 = 196577) B196577
theorem B131063 : Blo 127788 131063 := bstep (se 1 (by rfl) ⟨98297, by rfl⟩ : syracuseStep 131063 = 196595) B196595
theorem B131079 : Blo 127788 131079 := bstep (se 1 (by rfl) ⟨98309, by rfl⟩ : syracuseStep 131079 = 196619) B196619
theorem B131087 : Blo 127788 131087 := bstep (se 1 (by rfl) ⟨98315, by rfl⟩ : syracuseStep 131087 = 196631) B196631
theorem B163883 : Blo 127788 163883 := bstep (se 1 (by rfl) ⟨122912, by rfl⟩ : syracuseStep 163883 = 245825) B245825
theorem B196667 : Blo 127788 196667 := bstep (se 1 (by rfl) ⟨147500, by rfl⟩ : syracuseStep 196667 = 295001) B295001
theorem B131131 : Blo 127788 131131 := bstep (se 1 (by rfl) ⟨98348, by rfl⟩ : syracuseStep 131131 = 196697) B196697
theorem B196727 : Blo 127788 196727 := bstep (se 1 (by rfl) ⟨147545, by rfl⟩ : syracuseStep 196727 = 295091) B295091
theorem B131207 : Blo 127788 131207 := bstep (se 1 (by rfl) ⟨98405, by rfl⟩ : syracuseStep 131207 = 196811) B196811
theorem B196751 : Blo 127788 196751 := bstep (se 1 (by rfl) ⟨147563, by rfl⟩ : syracuseStep 196751 = 295127) B295127
theorem B131215 : Blo 127788 131215 := bstep (se 1 (by rfl) ⟨98411, by rfl⟩ : syracuseStep 131215 = 196823) B196823
theorem B327827 : Blo 127788 327827 := bstep (se 1 (by rfl) ⟨245870, by rfl⟩ : syracuseStep 327827 = 491741) B491741
theorem B196793 : Blo 127788 196793 := bstep (se 2 (by rfl) ⟨73797, by rfl⟩ : syracuseStep 196793 = 147595) B147595
theorem B131259 : Blo 127788 131259 := bstep (se 1 (by rfl) ⟨98444, by rfl⟩ : syracuseStep 131259 = 196889) B196889
theorem B2162933 : Blo 127788 2162933 := bstep (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) B202775
theorem B196871 : Blo 127788 196871 := bstep (se 1 (by rfl) ⟨147653, by rfl⟩ : syracuseStep 196871 = 295307) B295307
theorem B131335 : Blo 127788 131335 := bstep (se 1 (by rfl) ⟨98501, by rfl⟩ : syracuseStep 131335 = 197003) B197003
theorem B131343 : Blo 127788 131343 := bstep (se 1 (by rfl) ⟨98507, by rfl⟩ : syracuseStep 131343 = 197015) B197015
theorem B196907 : Blo 127788 196907 := bstep (se 1 (by rfl) ⟨147680, by rfl⟩ : syracuseStep 196907 = 295361) B295361
theorem B131387 : Blo 127788 131387 := bstep (se 1 (by rfl) ⟨98540, by rfl⟩ : syracuseStep 131387 = 197081) B197081
theorem B196937 : Blo 127788 196937 := bstep (se 2 (by rfl) ⟨73851, by rfl⟩ : syracuseStep 196937 = 147703) B147703
theorem B131463 : Blo 127788 131463 := bstep (se 1 (by rfl) ⟨98597, by rfl⟩ : syracuseStep 131463 = 197195) B197195
theorem B131471 : Blo 127788 131471 := bstep (se 1 (by rfl) ⟨98603, by rfl⟩ : syracuseStep 131471 = 197207) B197207
theorem B328121 : Blo 127788 328121 := bstep (se 2 (by rfl) ⟨123045, by rfl⟩ : syracuseStep 328121 = 246091) B246091
theorem B197051 : Blo 127788 197051 := bstep (se 1 (by rfl) ⟨147788, by rfl⟩ : syracuseStep 197051 = 295577) B295577
theorem B131515 : Blo 127788 131515 := bstep (se 1 (by rfl) ⟨98636, by rfl⟩ : syracuseStep 131515 = 197273) B197273
theorem B197111 : Blo 127788 197111 := bstep (se 1 (by rfl) ⟨147833, by rfl⟩ : syracuseStep 197111 = 295667) B295667
theorem B819715 : Blo 127788 819715 := bstep (se 1 (by rfl) ⟨614786, by rfl⟩ : syracuseStep 819715 = 1229573) B1229573
theorem B164359 : Blo 127788 164359 := bstep (se 1 (by rfl) ⟨123269, by rfl⟩ : syracuseStep 164359 = 246539) B246539
theorem B131591 : Blo 127788 131591 := bstep (se 1 (by rfl) ⟨98693, by rfl⟩ : syracuseStep 131591 = 197387) B197387
theorem B197135 : Blo 127788 197135 := bstep (se 1 (by rfl) ⟨147851, by rfl⟩ : syracuseStep 197135 = 295703) B295703
theorem B131599 : Blo 127788 131599 := bstep (se 1 (by rfl) ⟨98699, by rfl⟩ : syracuseStep 131599 = 197399) B197399
theorem B197177 : Blo 127788 197177 := bstep (se 2 (by rfl) ⟨73941, by rfl⟩ : syracuseStep 197177 = 147883) B147883
theorem B131643 : Blo 127788 131643 := bstep (se 1 (by rfl) ⟨98732, by rfl⟩ : syracuseStep 131643 = 197465) B197465
theorem B393815 : Blo 127788 393815 := bstep (se 1 (by rfl) ⟨295361, by rfl⟩ : syracuseStep 393815 = 590723) B590723
theorem B295559 : Blo 127788 295559 := bstep (se 1 (by rfl) ⟨221669, by rfl⟩ : syracuseStep 295559 = 443339) B443339
theorem B197255 : Blo 127788 197255 := bstep (se 1 (by rfl) ⟨147941, by rfl⟩ : syracuseStep 197255 = 295883) B295883
theorem B131719 : Blo 127788 131719 := bstep (se 1 (by rfl) ⟨98789, by rfl⟩ : syracuseStep 131719 = 197579) B197579
theorem B131727 : Blo 127788 131727 := bstep (se 1 (by rfl) ⟨98795, by rfl⟩ : syracuseStep 131727 = 197591) B197591
theorem B197291 : Blo 127788 197291 := bstep (se 1 (by rfl) ⟨147968, by rfl⟩ : syracuseStep 197291 = 295937) B295937
theorem B131771 : Blo 127788 131771 := bstep (se 1 (by rfl) ⟨98828, by rfl⟩ : syracuseStep 131771 = 197657) B197657
theorem B197321 : Blo 127788 197321 := bstep (se 2 (by rfl) ⟨73995, by rfl⟩ : syracuseStep 197321 = 147991) B147991
theorem B295739 : Blo 127788 295739 := bstep (se 1 (by rfl) ⟨221804, by rfl⟩ : syracuseStep 295739 = 443609) B443609
theorem B197435 : Blo 127788 197435 := bstep (se 1 (by rfl) ⟨148076, by rfl⟩ : syracuseStep 197435 = 296153) B296153
theorem B197495 : Blo 127788 197495 := bstep (se 1 (by rfl) ⟨148121, by rfl⟩ : syracuseStep 197495 = 296243) B296243
theorem B197519 : Blo 127788 197519 := bstep (se 1 (by rfl) ⟨148139, by rfl⟩ : syracuseStep 197519 = 296279) B296279
theorem B295865 : Blo 127788 295865 := bstep (se 2 (by rfl) ⟨110949, by rfl⟩ : syracuseStep 295865 = 221899) B221899
theorem B197561 : Blo 127788 197561 := bstep (se 2 (by rfl) ⟨74085, by rfl⟩ : syracuseStep 197561 = 148171) B148171
theorem B164855 : Blo 127788 164855 := bstep (se 1 (by rfl) ⟨123641, by rfl⟩ : syracuseStep 164855 = 247283) B247283
theorem B197639 : Blo 127788 197639 := bstep (se 1 (by rfl) ⟨148229, by rfl⟩ : syracuseStep 197639 = 296459) B296459
theorem B623627 : Blo 127788 623627 := bstep (se 1 (by rfl) ⟨467720, by rfl⟩ : syracuseStep 623627 = 935441) B935441
theorem B197675 : Blo 127788 197675 := bstep (se 1 (by rfl) ⟨148256, by rfl⟩ : syracuseStep 197675 = 296513) B296513
theorem B394301 : Blo 127788 394301 := bstep (se 3 (by rfl) ⟨73931, by rfl⟩ : syracuseStep 394301 = 147863) B147863
theorem B328819 : Blo 127788 328819 := bstep (se 1 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 328819 = 493229) B493229
theorem B165007 : Blo 127788 165007 := bstep (se 1 (by rfl) ⟨123755, by rfl⟩ : syracuseStep 165007 = 247511) B247511
theorem B656585 : Blo 127788 656585 := bstep (se 2 (by rfl) ⟨246219, by rfl⟩ : syracuseStep 656585 = 492439) B492439
theorem B328961 : Blo 127788 328961 := bstep (se 2 (by rfl) ⟨123360, by rfl⟩ : syracuseStep 328961 = 246721) B246721
theorem B296207 : Blo 127788 296207 := bstep (se 1 (by rfl) ⟨222155, by rfl⟩ : syracuseStep 296207 = 444311) B444311
theorem B296225 : Blo 127788 296225 := bstep (se 2 (by rfl) ⟨111084, by rfl⟩ : syracuseStep 296225 = 222169) B222169
theorem B165179 : Blo 127788 165179 := bstep (se 1 (by rfl) ⟨123884, by rfl⟩ : syracuseStep 165179 = 247769) B247769
theorem B493067 : Blo 127788 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B296567 : Blo 127788 296567 := bstep (se 1 (by rfl) ⟨222425, by rfl⟩ : syracuseStep 296567 = 444851) B444851
theorem B329417 : Blo 127788 329417 := bstep (se 2 (by rfl) ⟨123531, by rfl⟩ : syracuseStep 329417 = 247063) B247063
theorem B198415 : Blo 127788 198415 := bstep (se 1 (by rfl) ⟨148811, by rfl⟩ : syracuseStep 198415 = 297623) B297623
theorem B231353 : Blo 127788 231353 := bstep (se 2 (by rfl) ⟨86757, by rfl⟩ : syracuseStep 231353 = 173515) B173515
theorem B198587 : Blo 127788 198587 := bstep (se 1 (by rfl) ⟨148940, by rfl⟩ : syracuseStep 198587 = 297881) B297881
theorem B395293 : Blo 127788 395293 := bstep (se 3 (by rfl) ⟨74117, by rfl⟩ : syracuseStep 395293 = 148235) B148235
theorem B329771 : Blo 127788 329771 := bstep (se 1 (by rfl) ⟨247328, by rfl⟩ : syracuseStep 329771 = 494657) B494657
theorem B1771721 : Blo 127788 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B657665 : Blo 127788 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B166151 : Blo 127788 166151 := bstep (se 1 (by rfl) ⟨124613, by rfl⟩ : syracuseStep 166151 = 249227) B249227
theorem B788773 : Blo 127788 788773 := bstep (se 4 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 788773 = 147895) B147895
theorem B493883 : Blo 127788 493883 := bstep (se 1 (by rfl) ⟨370412, by rfl⟩ : syracuseStep 493883 = 740825) B740825
theorem B5114177 : Blo 127788 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B494369 : Blo 127788 494369 := bstep (se 2 (by rfl) ⟨185388, by rfl⟩ : syracuseStep 494369 = 370777) B370777
theorem B1411991 : Blo 127788 1411991 := bstep (se 1 (by rfl) ⟨1058993, by rfl⟩ : syracuseStep 1411991 = 2117987) B2117987
theorem B330763 : Blo 127788 330763 := bstep (se 1 (by rfl) ⟨248072, by rfl⟩ : syracuseStep 330763 = 496145) B496145
theorem B330887 : Blo 127788 330887 := bstep (se 1 (by rfl) ⟨248165, by rfl⟩ : syracuseStep 330887 = 496331) B496331
theorem B330905 : Blo 127788 330905 := bstep (se 2 (by rfl) ⟨124089, by rfl⟩ : syracuseStep 330905 = 248179) B248179
theorem B756965 : Blo 127788 756965 := bstep (se 4 (by rfl) ⟨70965, by rfl⟩ : syracuseStep 756965 = 141931) B141931
theorem B1117421 : Blo 127788 1117421 := bstep (se 3 (by rfl) ⟨209516, by rfl⟩ : syracuseStep 1117421 = 419033) B419033
theorem B331067 : Blo 127788 331067 := bstep (se 1 (by rfl) ⟨248300, by rfl⟩ : syracuseStep 331067 = 496601) B496601
theorem B363977 : Blo 127788 363977 := bstep (se 2 (by rfl) ⟨136491, by rfl⟩ : syracuseStep 363977 = 272983) B272983
theorem B527939 : Blo 127788 527939 := bstep (se 1 (by rfl) ⟨395954, by rfl⟩ : syracuseStep 527939 = 791909) B791909
theorem B331411 : Blo 127788 331411 := bstep (se 1 (by rfl) ⟨248558, by rfl⟩ : syracuseStep 331411 = 497117) B497117
theorem B495341 : Blo 127788 495341 := bstep (se 3 (by rfl) ⟨92876, by rfl⟩ : syracuseStep 495341 = 185753) B185753
theorem B331553 : Blo 127788 331553 := bstep (se 2 (by rfl) ⟨124332, by rfl⟩ : syracuseStep 331553 = 248665) B248665
theorem B921547 : Blo 127788 921547 := bstep (se 1 (by rfl) ⟨691160, by rfl⟩ : syracuseStep 921547 = 1382321) B1382321
theorem B2691089 : Blo 127788 2691089 := bstep (se 2 (by rfl) ⟨1009158, by rfl⟩ : syracuseStep 2691089 = 2018317) B2018317
theorem B495659 : Blo 127788 495659 := bstep (se 1 (by rfl) ⟨371744, by rfl⟩ : syracuseStep 495659 = 743489) B743489
theorem B561239 : Blo 127788 561239 := bstep (se 1 (by rfl) ⟨420929, by rfl⟩ : syracuseStep 561239 = 841859) B841859
theorem B266387 : Blo 127788 266387 := bstep (se 1 (by rfl) ⟨199790, by rfl⟩ : syracuseStep 266387 = 399581) B399581
theorem B332545 : Blo 127788 332545 := bstep (se 2 (by rfl) ⟨124704, by rfl⟩ : syracuseStep 332545 = 249409) B249409
theorem B791329 : Blo 127788 791329 := bstep (se 2 (by rfl) ⟨296748, by rfl⟩ : syracuseStep 791329 = 593497) B593497
theorem B594955 : Blo 127788 594955 := bstep (se 1 (by rfl) ⟨446216, by rfl⟩ : syracuseStep 594955 = 892433) B892433
theorem B365867 : Blo 127788 365867 := bstep (se 1 (by rfl) ⟨274400, by rfl⟩ : syracuseStep 365867 = 548801) B548801
theorem B333143 : Blo 127788 333143 := bstep (se 1 (by rfl) ⟨249857, by rfl⟩ : syracuseStep 333143 = 499715) B499715
theorem B431513 : Blo 127788 431513 := bstep (se 2 (by rfl) ⟨161817, by rfl⟩ : syracuseStep 431513 = 323635) B323635
theorem B366095 : Blo 127788 366095 := bstep (se 1 (by rfl) ⟨274571, by rfl⟩ : syracuseStep 366095 = 549143) B549143
theorem B333355 : Blo 127788 333355 := bstep (se 1 (by rfl) ⟨250016, by rfl⟩ : syracuseStep 333355 = 500033) B500033
theorem B333497 : Blo 127788 333497 := bstep (se 2 (by rfl) ⟨125061, by rfl⟩ : syracuseStep 333497 = 250123) B250123
theorem B1218277 : Blo 127788 1218277 := bstep (se 4 (by rfl) ⟨114213, by rfl⟩ : syracuseStep 1218277 = 228427) B228427
theorem B923393 : Blo 127788 923393 := bstep (se 2 (by rfl) ⟨346272, by rfl⟩ : syracuseStep 923393 = 692545) B692545
theorem B497441 : Blo 127788 497441 := bstep (se 2 (by rfl) ⟨186540, by rfl⟩ : syracuseStep 497441 = 373081) B373081
theorem B432215 : Blo 127788 432215 := bstep (se 1 (by rfl) ⟨324161, by rfl⟩ : syracuseStep 432215 = 648323) B648323
theorem B301241 : Blo 127788 301241 := bstep (se 2 (by rfl) ⟨112965, by rfl⟩ : syracuseStep 301241 = 225931) B225931
theorem B432701 : Blo 127788 432701 := bstep (se 3 (by rfl) ⟨81131, by rfl⟩ : syracuseStep 432701 = 162263) B162263
theorem B1055425 : Blo 127788 1055425 := bstep (se 2 (by rfl) ⟨395784, by rfl⟩ : syracuseStep 1055425 = 791569) B791569
theorem B400139 : Blo 127788 400139 := bstep (se 1 (by rfl) ⟨300104, by rfl⟩ : syracuseStep 400139 = 600209) B600209
theorem B662417 : Blo 127788 662417 := bstep (se 2 (by rfl) ⟨248406, by rfl⟩ : syracuseStep 662417 = 496813) B496813
theorem B367507 : Blo 127788 367507 := bstep (se 1 (by rfl) ⟨275630, by rfl⟩ : syracuseStep 367507 = 551261) B551261
theorem B334745 : Blo 127788 334745 := bstep (se 2 (by rfl) ⟨125529, by rfl⟩ : syracuseStep 334745 = 251059) B251059
theorem B269257 : Blo 127788 269257 := bstep (se 2 (by rfl) ⟨100971, by rfl⟩ : syracuseStep 269257 = 201943) B201943
theorem B367735 : Blo 127788 367735 := bstep (se 1 (by rfl) ⟨275801, by rfl⟩ : syracuseStep 367735 = 551603) B551603
theorem B498977 : Blo 127788 498977 := bstep (se 2 (by rfl) ⟨187116, by rfl⟩ : syracuseStep 498977 = 374233) B374233
theorem B1121795 : Blo 127788 1121795 := bstep (se 1 (by rfl) ⟨841346, by rfl⟩ : syracuseStep 1121795 = 1682693) B1682693
theorem B630301 : Blo 127788 630301 := bstep (se 3 (by rfl) ⟨118181, by rfl⟩ : syracuseStep 630301 = 236363) B236363
theorem B499229 : Blo 127788 499229 := bstep (se 3 (by rfl) ⟨93605, by rfl⟩ : syracuseStep 499229 = 187211) B187211
theorem B499243 : Blo 127788 499243 := bstep (se 1 (by rfl) ⟨374432, by rfl⟩ : syracuseStep 499243 = 748865) B748865
theorem B466499 : Blo 127788 466499 := bstep (se 1 (by rfl) ⟨349874, by rfl⟩ : syracuseStep 466499 = 699749) B699749
theorem B1056527 : Blo 127788 1056527 := bstep (se 1 (by rfl) ⟨792395, by rfl⟩ : syracuseStep 1056527 = 1584791) B1584791
theorem B434105 : Blo 127788 434105 := bstep (se 2 (by rfl) ⟨162789, by rfl⟩ : syracuseStep 434105 = 325579) B325579
theorem B369011 : Blo 127788 369011 := bstep (se 1 (by rfl) ⟨276758, by rfl⟩ : syracuseStep 369011 = 553517) B553517
theorem B434699 : Blo 127788 434699 := bstep (se 1 (by rfl) ⟨326024, by rfl⟩ : syracuseStep 434699 = 652049) B652049
theorem B434807 : Blo 127788 434807 := bstep (se 1 (by rfl) ⟨326105, by rfl⟩ : syracuseStep 434807 = 652211) B652211
theorem B369353 : Blo 127788 369353 := bstep (se 2 (by rfl) ⟨138507, by rfl⟩ : syracuseStep 369353 = 277015) B277015
theorem B500513 : Blo 127788 500513 := bstep (se 2 (by rfl) ⟨187692, by rfl⟩ : syracuseStep 500513 = 375385) B375385
theorem B369467 : Blo 127788 369467 := bstep (se 1 (by rfl) ⟨277100, by rfl⟩ : syracuseStep 369467 = 554201) B554201
theorem B369593 : Blo 127788 369593 := bstep (se 2 (by rfl) ⟨138597, by rfl⟩ : syracuseStep 369593 = 277195) B277195
theorem B664523 : Blo 127788 664523 := bstep (se 1 (by rfl) ⟨498392, by rfl⟩ : syracuseStep 664523 = 996785) B996785
theorem B468011 : Blo 127788 468011 := bstep (se 1 (by rfl) ⟨351008, by rfl⟩ : syracuseStep 468011 = 702017) B702017
theorem B664643 : Blo 127788 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B7611479 : Blo 127788 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B435401 : Blo 127788 435401 := bstep (se 2 (by rfl) ⟨163275, by rfl⟩ : syracuseStep 435401 = 326551) B326551
theorem B632009 : Blo 127788 632009 := bstep (se 2 (by rfl) ⟨237003, by rfl⟩ : syracuseStep 632009 = 474007) B474007
theorem B664847 : Blo 127788 664847 := bstep (se 1 (by rfl) ⟨498635, by rfl⟩ : syracuseStep 664847 = 997271) B997271
theorem B1254791 : Blo 127788 1254791 := bstep (se 1 (by rfl) ⟨941093, by rfl⟩ : syracuseStep 1254791 = 1882187) B1882187
theorem B436103 : Blo 127788 436103 := bstep (se 1 (by rfl) ⟨327077, by rfl⟩ : syracuseStep 436103 = 654155) B654155
theorem B436481 : Blo 127788 436481 := bstep (se 2 (by rfl) ⟨163680, by rfl⟩ : syracuseStep 436481 = 327361) B327361
theorem B1387037 : Blo 127788 1387037 := bstep (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) B520139
theorem B371243 : Blo 127788 371243 := bstep (se 1 (by rfl) ⟨278432, by rfl⟩ : syracuseStep 371243 = 556865) B556865
theorem B993869 : Blo 127788 993869 := bstep (se 3 (by rfl) ⟨186350, by rfl⟩ : syracuseStep 993869 = 372701) B372701
theorem B666305 : Blo 127788 666305 := bstep (se 2 (by rfl) ⟨249864, by rfl⟩ : syracuseStep 666305 = 499729) B499729
theorem B1288921 : Blo 127788 1288921 := bstep (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) B966691
theorem B207659 : Blo 127788 207659 := bstep (se 1 (by rfl) ⟨155744, by rfl⟩ : syracuseStep 207659 = 311489) B311489
theorem B437291 : Blo 127788 437291 := bstep (se 1 (by rfl) ⟨327968, by rfl⟩ : syracuseStep 437291 = 655937) B655937
theorem B371773 : Blo 127788 371773 := bstep (se 3 (by rfl) ⟨69707, by rfl⟩ : syracuseStep 371773 = 139415) B139415
theorem B503225 : Blo 127788 503225 := bstep (se 2 (by rfl) ⟨188709, by rfl⟩ : syracuseStep 503225 = 377419) B377419
theorem B798137 : Blo 127788 798137 := bstep (se 2 (by rfl) ⟨299301, by rfl⟩ : syracuseStep 798137 = 598603) B598603
theorem B372235 : Blo 127788 372235 := bstep (se 1 (by rfl) ⟨279176, by rfl⟩ : syracuseStep 372235 = 558353) B558353
theorem B3124813 : Blo 127788 3124813 := bstep (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) B1171805
theorem B765677 : Blo 127788 765677 := bstep (se 3 (by rfl) ⟨143564, by rfl⟩ : syracuseStep 765677 = 287129) B287129
theorem B372509 : Blo 127788 372509 := bstep (se 3 (by rfl) ⟨69845, by rfl⟩ : syracuseStep 372509 = 139691) B139691
theorem B175915 : Blo 127788 175915 := bstep (se 1 (by rfl) ⟨131936, by rfl⟩ : syracuseStep 175915 = 263873) B263873
theorem B175991 : Blo 127788 175991 := bstep (se 1 (by rfl) ⟨131993, by rfl⟩ : syracuseStep 175991 = 263987) B263987
theorem B798893 : Blo 127788 798893 := bstep (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) B299585
theorem B209081 : Blo 127788 209081 := bstep (se 2 (by rfl) ⟨78405, by rfl⟩ : syracuseStep 209081 = 156811) B156811
theorem B307471 : Blo 127788 307471 := bstep (se 1 (by rfl) ⟨230603, by rfl⟩ : syracuseStep 307471 = 461207) B461207
theorem B438587 : Blo 127788 438587 := bstep (se 1 (by rfl) ⟨328940, by rfl⟩ : syracuseStep 438587 = 657881) B657881
theorem B143887 : Blo 127788 143887 := bstep (se 1 (by rfl) ⟨107915, by rfl⟩ : syracuseStep 143887 = 215831) B215831
theorem B733967 : Blo 127788 733967 := bstep (se 1 (by rfl) ⟨550475, by rfl⟩ : syracuseStep 733967 = 1100951) B1100951
theorem B439073 : Blo 127788 439073 := bstep (se 2 (by rfl) ⟨164652, by rfl⟩ : syracuseStep 439073 = 329305) B329305
theorem B308087 : Blo 127788 308087 := bstep (se 1 (by rfl) ⟨231065, by rfl⟩ : syracuseStep 308087 = 462131) B462131
theorem B996299 : Blo 127788 996299 := bstep (se 1 (by rfl) ⟨747224, by rfl⟩ : syracuseStep 996299 = 1494449) B1494449
theorem B144391 : Blo 127788 144391 := bstep (se 1 (by rfl) ⟨108293, by rfl⟩ : syracuseStep 144391 = 216587) B216587
theorem B210055 : Blo 127788 210055 := bstep (se 1 (by rfl) ⟨157541, by rfl⟩ : syracuseStep 210055 = 315083) B315083
theorem B144571 : Blo 127788 144571 := bstep (se 1 (by rfl) ⟨108428, by rfl⟩ : syracuseStep 144571 = 216857) B216857
theorem B701669 : Blo 127788 701669 := bstep (se 4 (by rfl) ⟨65781, by rfl⟩ : syracuseStep 701669 = 131563) B131563
theorem B439667 : Blo 127788 439667 := bstep (se 1 (by rfl) ⟨329750, by rfl⟩ : syracuseStep 439667 = 659501) B659501
theorem B243091 : Blo 127788 243091 := bstep (se 1 (by rfl) ⟨182318, by rfl⟩ : syracuseStep 243091 = 364637) B364637
theorem B3225091 : Blo 127788 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B243319 : Blo 127788 243319 := bstep (se 1 (by rfl) ⟨182489, by rfl⟩ : syracuseStep 243319 = 364979) B364979
theorem B308855 : Blo 127788 308855 := bstep (se 1 (by rfl) ⟨231641, by rfl⟩ : syracuseStep 308855 = 463283) B463283
theorem B145039 : Blo 127788 145039 := bstep (se 1 (by rfl) ⟨108779, by rfl⟩ : syracuseStep 145039 = 217559) B217559
theorem B374615 : Blo 127788 374615 := bstep (se 1 (by rfl) ⟨280961, by rfl⟩ : syracuseStep 374615 = 561923) B561923
theorem B702361 : Blo 127788 702361 := bstep (se 2 (by rfl) ⟨263385, by rfl⟩ : syracuseStep 702361 = 526771) B526771
theorem B374843 : Blo 127788 374843 := bstep (se 1 (by rfl) ⟨281132, by rfl⟩ : syracuseStep 374843 = 562265) B562265
theorem B145543 : Blo 127788 145543 := bstep (se 1 (by rfl) ⟨109157, by rfl⟩ : syracuseStep 145543 = 218315) B218315
theorem B374969 : Blo 127788 374969 := bstep (se 2 (by rfl) ⟨140613, by rfl⟩ : syracuseStep 374969 = 281227) B281227
theorem B735425 : Blo 127788 735425 := bstep (se 2 (by rfl) ⟨275784, by rfl⟩ : syracuseStep 735425 = 551569) B551569
theorem B211259 : Blo 127788 211259 := bstep (se 1 (by rfl) ⟨158444, by rfl⟩ : syracuseStep 211259 = 316889) B316889
theorem B145723 : Blo 127788 145723 := bstep (se 1 (by rfl) ⟨109292, by rfl⟩ : syracuseStep 145723 = 218585) B218585
theorem B146191 : Blo 127788 146191 := bstep (se 1 (by rfl) ⟨109643, by rfl⟩ : syracuseStep 146191 = 219287) B219287
theorem B310315 : Blo 127788 310315 := bstep (se 1 (by rfl) ⟨232736, by rfl⟩ : syracuseStep 310315 = 465473) B465473
theorem B244883 : Blo 127788 244883 := bstep (se 1 (by rfl) ⟨183662, by rfl⟩ : syracuseStep 244883 = 367325) B367325
theorem B244937 : Blo 127788 244937 := bstep (se 2 (by rfl) ⟨91851, by rfl⟩ : syracuseStep 244937 = 183703) B183703
theorem B703745 : Blo 127788 703745 := bstep (se 2 (by rfl) ⟨263904, by rfl⟩ : syracuseStep 703745 = 527809) B527809
theorem B146695 : Blo 127788 146695 := bstep (se 1 (by rfl) ⟨110021, by rfl⟩ : syracuseStep 146695 = 220043) B220043
theorem B245035 : Blo 127788 245035 := bstep (se 1 (by rfl) ⟨183776, by rfl⟩ : syracuseStep 245035 = 367553) B367553
theorem B441715 : Blo 127788 441715 := bstep (se 1 (by rfl) ⟨331286, by rfl⟩ : syracuseStep 441715 = 662573) B662573
theorem B146875 : Blo 127788 146875 := bstep (se 1 (by rfl) ⟨110156, by rfl⟩ : syracuseStep 146875 = 220313) B220313
theorem B376265 : Blo 127788 376265 := bstep (se 2 (by rfl) ⟨141099, by rfl⟩ : syracuseStep 376265 = 282199) B282199
theorem B1818065 : Blo 127788 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B245263 : Blo 127788 245263 := bstep (se 1 (by rfl) ⟨183947, by rfl⟩ : syracuseStep 245263 = 367895) B367895
theorem B310931 : Blo 127788 310931 := bstep (se 1 (by rfl) ⟨233198, by rfl⟩ : syracuseStep 310931 = 466397) B466397
theorem B1392419 : Blo 127788 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B147343 : Blo 127788 147343 := bstep (se 1 (by rfl) ⟨110507, by rfl⟩ : syracuseStep 147343 = 221015) B221015
theorem B442259 : Blo 127788 442259 := bstep (se 1 (by rfl) ⟨331694, by rfl⟩ : syracuseStep 442259 = 663389) B663389
theorem B278561 : Blo 127788 278561 := bstep (se 2 (by rfl) ⟨104460, by rfl⟩ : syracuseStep 278561 = 208921) B208921
theorem B278903 : Blo 127788 278903 := bstep (se 1 (by rfl) ⟨209177, by rfl⟩ : syracuseStep 278903 = 418355) B418355
theorem B147847 : Blo 127788 147847 := bstep (se 1 (by rfl) ⟨110885, by rfl⟩ : syracuseStep 147847 = 221771) B221771
theorem B311699 : Blo 127788 311699 := bstep (se 1 (by rfl) ⟨233774, by rfl⟩ : syracuseStep 311699 = 467549) B467549
theorem B1556957 : Blo 127788 1556957 := bstep (se 3 (by rfl) ⟨291929, by rfl⟩ : syracuseStep 1556957 = 583859) B583859
theorem B148027 : Blo 127788 148027 := bstep (se 1 (by rfl) ⟨111020, by rfl⟩ : syracuseStep 148027 = 222041) B222041
theorem B1491533 : Blo 127788 1491533 := bstep (se 3 (by rfl) ⟨279662, by rfl⟩ : syracuseStep 1491533 = 559325) B559325
theorem B246827 : Blo 127788 246827 := bstep (se 1 (by rfl) ⟨185120, by rfl⟩ : syracuseStep 246827 = 370241) B370241
theorem B443663 : Blo 127788 443663 := bstep (se 1 (by rfl) ⟨332747, by rfl⟩ : syracuseStep 443663 = 665495) B665495
theorem B443933 : Blo 127788 443933 := bstep (se 3 (by rfl) ⟨83237, by rfl⟩ : syracuseStep 443933 = 166475) B166475
theorem B378553 : Blo 127788 378553 := bstep (se 2 (by rfl) ⟨141957, by rfl⟩ : syracuseStep 378553 = 283915) B283915
theorem B1722391 : Blo 127788 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B313463 : Blo 127788 313463 := bstep (se 1 (by rfl) ⟨235097, by rfl⟩ : syracuseStep 313463 = 470195) B470195
theorem B936173 : Blo 127788 936173 := bstep (se 3 (by rfl) ⟨175532, by rfl⟩ : syracuseStep 936173 = 351065) B351065
theorem B2377997 : Blo 127788 2377997 := bstep (se 3 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 2377997 = 891749) B891749
theorem B280979 : Blo 127788 280979 := bstep (se 1 (by rfl) ⟨210734, by rfl⟩ : syracuseStep 280979 = 421469) B421469
theorem B1460915 : Blo 127788 1460915 := bstep (se 1 (by rfl) ⟨1095686, by rfl⟩ : syracuseStep 1460915 = 2191373) B2191373
theorem B248521 : Blo 127788 248521 := bstep (se 2 (by rfl) ⟨93195, by rfl⟩ : syracuseStep 248521 = 186391) B186391
theorem B215851 : Blo 127788 215851 := bstep (se 1 (by rfl) ⟨161888, by rfl⟩ : syracuseStep 215851 = 323777) B323777
theorem B641881 : Blo 127788 641881 := bstep (se 2 (by rfl) ⟨240705, by rfl⟩ : syracuseStep 641881 = 481411) B481411
theorem B215993 : Blo 127788 215993 := bstep (se 2 (by rfl) ⟨80997, by rfl⟩ : syracuseStep 215993 = 161995) B161995
theorem B740299 : Blo 127788 740299 := bstep (se 1 (by rfl) ⟨555224, by rfl⟩ : syracuseStep 740299 = 1110449) B1110449
theorem B380189 : Blo 127788 380189 := bstep (se 3 (by rfl) ⟨71285, by rfl⟩ : syracuseStep 380189 = 142571) B142571
theorem B347453 : Blo 127788 347453 := bstep (se 3 (by rfl) ⟨65147, by rfl⟩ : syracuseStep 347453 = 130295) B130295
theorem B413063 : Blo 127788 413063 := bstep (se 1 (by rfl) ⟨309797, by rfl⟩ : syracuseStep 413063 = 619595) B619595
theorem B183799 : Blo 127788 183799 := bstep (se 1 (by rfl) ⟨137849, by rfl⟩ : syracuseStep 183799 = 275699) B275699
theorem B314891 : Blo 127788 314891 := bstep (se 1 (by rfl) ⟨236168, by rfl⟩ : syracuseStep 314891 = 472337) B472337
theorem B216695 : Blo 127788 216695 := bstep (se 1 (by rfl) ⟨162521, by rfl⟩ : syracuseStep 216695 = 325043) B325043
theorem B479009 : Blo 127788 479009 := bstep (se 2 (by rfl) ⟨179628, by rfl⟩ : syracuseStep 479009 = 359257) B359257
theorem B315179 : Blo 127788 315179 := bstep (se 1 (by rfl) ⟨236384, by rfl⟩ : syracuseStep 315179 = 472769) B472769
theorem B217147 : Blo 127788 217147 := bstep (se 1 (by rfl) ⟨162860, by rfl⟩ : syracuseStep 217147 = 325721) B325721
theorem B217289 : Blo 127788 217289 := bstep (se 2 (by rfl) ⟨81483, by rfl⟩ : syracuseStep 217289 = 162967) B162967
theorem B414011 : Blo 127788 414011 := bstep (se 1 (by rfl) ⟨310508, by rfl⟩ : syracuseStep 414011 = 621017) B621017
theorem B2806163 : Blo 127788 2806163 := bstep (se 1 (by rfl) ⟨2104622, by rfl⟩ : syracuseStep 2806163 = 4209245) B4209245
theorem B184847 : Blo 127788 184847 := bstep (se 1 (by rfl) ⟨138635, by rfl⟩ : syracuseStep 184847 = 277271) B277271
theorem B414497 : Blo 127788 414497 := bstep (se 2 (by rfl) ⟨155436, by rfl⟩ : syracuseStep 414497 = 310873) B310873
theorem B938789 : Blo 127788 938789 := bstep (se 4 (by rfl) ⟨88011, by rfl⟩ : syracuseStep 938789 = 176023) B176023
theorem B185161 : Blo 127788 185161 := bstep (se 2 (by rfl) ⟨69435, by rfl⟩ : syracuseStep 185161 = 138871) B138871
theorem B217991 : Blo 127788 217991 := bstep (se 1 (by rfl) ⟨163493, by rfl⟩ : syracuseStep 217991 = 326987) B326987
theorem B349451 : Blo 127788 349451 := bstep (se 1 (by rfl) ⟨262088, by rfl⟩ : syracuseStep 349451 = 524177) B524177
theorem B742715 : Blo 127788 742715 := bstep (se 1 (by rfl) ⟨557036, by rfl⟩ : syracuseStep 742715 = 1114073) B1114073
theorem B218639 : Blo 127788 218639 := bstep (se 1 (by rfl) ⟨163979, by rfl⟩ : syracuseStep 218639 = 327959) B327959
theorem B1038233 : Blo 127788 1038233 := bstep (se 2 (by rfl) ⟨389337, by rfl⟩ : syracuseStep 1038233 = 778675) B778675
theorem B219179 : Blo 127788 219179 := bstep (se 1 (by rfl) ⟨164384, by rfl⟩ : syracuseStep 219179 = 328769) B328769
theorem B219577 : Blo 127788 219577 := bstep (se 2 (by rfl) ⟨82341, by rfl⟩ : syracuseStep 219577 = 164683) B164683
theorem B744173 : Blo 127788 744173 := bstep (se 3 (by rfl) ⟨139532, by rfl⟩ : syracuseStep 744173 = 279065) B279065
theorem B1104677 : Blo 127788 1104677 := bstep (se 4 (by rfl) ⟨103563, by rfl⟩ : syracuseStep 1104677 = 207127) B207127
theorem B252715 : Blo 127788 252715 := bstep (se 1 (by rfl) ⟨189536, by rfl⟩ : syracuseStep 252715 = 379073) B379073
theorem B1891187 : Blo 127788 1891187 := bstep (se 1 (by rfl) ⟨1418390, by rfl⟩ : syracuseStep 1891187 = 2836781) B2836781
theorem B154639 : Blo 127788 154639 := bstep (se 1 (by rfl) ⟨115979, by rfl⟩ : syracuseStep 154639 = 231959) B231959
theorem B744491 : Blo 127788 744491 := bstep (se 1 (by rfl) ⟨558368, by rfl⟩ : syracuseStep 744491 = 1116737) B1116737
theorem B220279 : Blo 127788 220279 := bstep (se 1 (by rfl) ⟨165209, by rfl⟩ : syracuseStep 220279 = 330419) B330419
theorem B220475 : Blo 127788 220475 := bstep (se 1 (by rfl) ⟨165356, by rfl⟩ : syracuseStep 220475 = 330713) B330713
theorem B220873 : Blo 127788 220873 := bstep (se 2 (by rfl) ⟨82827, by rfl⟩ : syracuseStep 220873 = 165655) B165655
theorem B1335041 : Blo 127788 1335041 := bstep (se 2 (by rfl) ⟨500640, by rfl⟩ : syracuseStep 1335041 = 1001281) B1001281
theorem B1498915 : Blo 127788 1498915 := bstep (se 1 (by rfl) ⟨1124186, by rfl⟩ : syracuseStep 1498915 = 2248373) B2248373
theorem B647027 : Blo 127788 647027 := bstep (se 1 (by rfl) ⟨485270, by rfl⟩ : syracuseStep 647027 = 970541) B970541
theorem B843635 : Blo 127788 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B844091 : Blo 127788 844091 := bstep (se 1 (by rfl) ⟨633068, by rfl⟩ : syracuseStep 844091 = 1266137) B1266137
theorem B647513 : Blo 127788 647513 := bstep (se 2 (by rfl) ⟨242817, by rfl⟩ : syracuseStep 647513 = 485635) B485635
theorem B221575 : Blo 127788 221575 := bstep (se 1 (by rfl) ⟨166181, by rfl⟩ : syracuseStep 221575 = 332363) B332363
theorem B745949 : Blo 127788 745949 := bstep (se 3 (by rfl) ⟨139865, by rfl⟩ : syracuseStep 745949 = 279731) B279731
theorem B287531 : Blo 127788 287531 := bstep (se 1 (by rfl) ⟨215648, by rfl⟩ : syracuseStep 287531 = 431297) B431297
theorem B222223 : Blo 127788 222223 := bstep (se 1 (by rfl) ⟨166667, by rfl⟩ : syracuseStep 222223 = 333335) B333335
theorem B287891 : Blo 127788 287891 := bstep (se 1 (by rfl) ⟨215918, by rfl⟩ : syracuseStep 287891 = 431837) B431837
theorem B287945 : Blo 127788 287945 := bstep (se 2 (by rfl) ⟨107979, by rfl⟩ : syracuseStep 287945 = 215959) B215959
theorem B451855 : Blo 127788 451855 := bstep (se 1 (by rfl) ⟨338891, by rfl⟩ : syracuseStep 451855 = 677783) B677783
theorem B419699 : Blo 127788 419699 := bstep (se 1 (by rfl) ⟨314774, by rfl⟩ : syracuseStep 419699 = 629549) B629549
theorem B288647 : Blo 127788 288647 := bstep (se 1 (by rfl) ⟨216485, by rfl⟩ : syracuseStep 288647 = 432971) B432971
theorem B288827 : Blo 127788 288827 := bstep (se 1 (by rfl) ⟨216620, by rfl⟩ : syracuseStep 288827 = 433241) B433241
theorem B288953 : Blo 127788 288953 := bstep (se 2 (by rfl) ⟨108357, by rfl⟩ : syracuseStep 288953 = 216715) B216715
theorem B649619 : Blo 127788 649619 := bstep (se 1 (by rfl) ⟨487214, by rfl⟩ : syracuseStep 649619 = 974429) B974429
theorem B289295 : Blo 127788 289295 := bstep (se 1 (by rfl) ⟨216971, by rfl⟩ : syracuseStep 289295 = 433943) B433943
theorem B748061 : Blo 127788 748061 := bstep (se 3 (by rfl) ⟨140261, by rfl⟩ : syracuseStep 748061 = 280523) B280523
theorem B289313 : Blo 127788 289313 := bstep (se 2 (by rfl) ⟨108492, by rfl⟩ : syracuseStep 289313 = 216985) B216985
theorem B1108673 : Blo 127788 1108673 := bstep (se 2 (by rfl) ⟨415752, by rfl⟩ : syracuseStep 1108673 = 831505) B831505
theorem B420623 : Blo 127788 420623 := bstep (se 1 (by rfl) ⟨315467, by rfl⟩ : syracuseStep 420623 = 630935) B630935
theorem B289655 : Blo 127788 289655 := bstep (se 1 (by rfl) ⟨217241, by rfl⟩ : syracuseStep 289655 = 434483) B434483
theorem B748547 : Blo 127788 748547 := bstep (se 1 (by rfl) ⟨561410, by rfl⟩ : syracuseStep 748547 = 1122821) B1122821
theorem B289835 : Blo 127788 289835 := bstep (se 1 (by rfl) ⟨217376, by rfl⟩ : syracuseStep 289835 = 434753) B434753
theorem B191531 : Blo 127788 191531 := bstep (se 1 (by rfl) ⟨143648, by rfl⟩ : syracuseStep 191531 = 287297) B287297
theorem B191735 : Blo 127788 191735 := bstep (se 1 (by rfl) ⟨143801, by rfl⟩ : syracuseStep 191735 = 287603) B287603
theorem B191759 : Blo 127788 191759 := bstep (se 1 (by rfl) ⟨143819, by rfl⟩ : syracuseStep 191759 = 287639) B287639
theorem B191801 : Blo 127788 191801 := bstep (se 2 (by rfl) ⟨71925, by rfl⟩ : syracuseStep 191801 = 143851) B143851
theorem B191879 : Blo 127788 191879 := bstep (se 1 (by rfl) ⟨143909, by rfl⟩ : syracuseStep 191879 = 287819) B287819
theorem B290195 : Blo 127788 290195 := bstep (se 1 (by rfl) ⟨217646, by rfl⟩ : syracuseStep 290195 = 435293) B435293
theorem B191915 : Blo 127788 191915 := bstep (se 1 (by rfl) ⟨143936, by rfl⟩ : syracuseStep 191915 = 287873) B287873
theorem B191945 : Blo 127788 191945 := bstep (se 2 (by rfl) ⟨71979, by rfl⟩ : syracuseStep 191945 = 143959) B143959
theorem B290249 : Blo 127788 290249 := bstep (se 2 (by rfl) ⟨108843, by rfl⟩ : syracuseStep 290249 = 217687) B217687
theorem B552491 : Blo 127788 552491 := bstep (se 1 (by rfl) ⟨414368, by rfl⟩ : syracuseStep 552491 = 828737) B828737
theorem B192059 : Blo 127788 192059 := bstep (se 1 (by rfl) ⟨144044, by rfl⟩ : syracuseStep 192059 = 288089) B288089
theorem B519767 : Blo 127788 519767 := bstep (se 1 (by rfl) ⟨389825, by rfl⟩ : syracuseStep 519767 = 779651) B779651
theorem B192119 : Blo 127788 192119 := bstep (se 1 (by rfl) ⟨144089, by rfl⟩ : syracuseStep 192119 = 288179) B288179
theorem B192143 : Blo 127788 192143 := bstep (se 1 (by rfl) ⟨144107, by rfl⟩ : syracuseStep 192143 = 288215) B288215
theorem B192185 : Blo 127788 192185 := bstep (se 2 (by rfl) ⟨72069, by rfl⟩ : syracuseStep 192185 = 144139) B144139
theorem B192263 : Blo 127788 192263 := bstep (se 1 (by rfl) ⟨144197, by rfl⟩ : syracuseStep 192263 = 288395) B288395
theorem B192299 : Blo 127788 192299 := bstep (se 1 (by rfl) ⟨144224, by rfl⟩ : syracuseStep 192299 = 288449) B288449
theorem B192329 : Blo 127788 192329 := bstep (se 2 (by rfl) ⟨72123, by rfl⟩ : syracuseStep 192329 = 144247) B144247
theorem B978803 : Blo 127788 978803 := bstep (se 1 (by rfl) ⟨734102, by rfl⟩ : syracuseStep 978803 = 1468205) B1468205
theorem B192443 : Blo 127788 192443 := bstep (se 1 (by rfl) ⟨144332, by rfl⟩ : syracuseStep 192443 = 288665) B288665
theorem B192503 : Blo 127788 192503 := bstep (se 1 (by rfl) ⟨144377, by rfl⟩ : syracuseStep 192503 = 288755) B288755
theorem B323585 : Blo 127788 323585 := bstep (se 2 (by rfl) ⟨121344, by rfl⟩ : syracuseStep 323585 = 242689) B242689
theorem B192527 : Blo 127788 192527 := bstep (se 1 (by rfl) ⟨144395, by rfl⟩ : syracuseStep 192527 = 288791) B288791
theorem B192569 : Blo 127788 192569 := bstep (se 2 (by rfl) ⟨72213, by rfl⟩ : syracuseStep 192569 = 144427) B144427
theorem B389207 : Blo 127788 389207 := bstep (se 1 (by rfl) ⟨291905, by rfl⟩ : syracuseStep 389207 = 583811) B583811
theorem B192647 : Blo 127788 192647 := bstep (se 1 (by rfl) ⟨144485, by rfl⟩ : syracuseStep 192647 = 288971) B288971
theorem B290951 : Blo 127788 290951 := bstep (se 1 (by rfl) ⟨218213, by rfl⟩ : syracuseStep 290951 = 436427) B436427
theorem B192683 : Blo 127788 192683 := bstep (se 1 (by rfl) ⟨144512, by rfl⟩ : syracuseStep 192683 = 289025) B289025
theorem B192713 : Blo 127788 192713 := bstep (se 2 (by rfl) ⟨72267, by rfl⟩ : syracuseStep 192713 = 144535) B144535
theorem B192827 : Blo 127788 192827 := bstep (se 1 (by rfl) ⟨144620, by rfl⟩ : syracuseStep 192827 = 289241) B289241
theorem B291131 : Blo 127788 291131 := bstep (se 1 (by rfl) ⟨218348, by rfl⟩ : syracuseStep 291131 = 436697) B436697
theorem B323959 : Blo 127788 323959 := bstep (se 1 (by rfl) ⟨242969, by rfl⟩ : syracuseStep 323959 = 485939) B485939
theorem B192887 : Blo 127788 192887 := bstep (se 1 (by rfl) ⟨144665, by rfl⟩ : syracuseStep 192887 = 289331) B289331
theorem B192911 : Blo 127788 192911 := bstep (se 1 (by rfl) ⟨144683, by rfl⟩ : syracuseStep 192911 = 289367) B289367
theorem B815507 : Blo 127788 815507 := bstep (se 1 (by rfl) ⟨611630, by rfl⟩ : syracuseStep 815507 = 1223261) B1223261
theorem B192953 : Blo 127788 192953 := bstep (se 2 (by rfl) ⟨72357, by rfl⟩ : syracuseStep 192953 = 144715) B144715
theorem B291257 : Blo 127788 291257 := bstep (se 2 (by rfl) ⟨109221, by rfl⟩ : syracuseStep 291257 = 218443) B218443
theorem B193031 : Blo 127788 193031 := bstep (se 1 (by rfl) ⟨144773, by rfl⟩ : syracuseStep 193031 = 289547) B289547
theorem B193067 : Blo 127788 193067 := bstep (se 1 (by rfl) ⟨144800, by rfl⟩ : syracuseStep 193067 = 289601) B289601
theorem B193097 : Blo 127788 193097 := bstep (se 2 (by rfl) ⟨72411, by rfl⟩ : syracuseStep 193097 = 144823) B144823
theorem B193211 : Blo 127788 193211 := bstep (se 1 (by rfl) ⟨144908, by rfl⟩ : syracuseStep 193211 = 289817) B289817
theorem B193271 : Blo 127788 193271 := bstep (se 1 (by rfl) ⟨144953, by rfl⟩ : syracuseStep 193271 = 289907) B289907
theorem B193295 : Blo 127788 193295 := bstep (se 1 (by rfl) ⟨144971, by rfl⟩ : syracuseStep 193295 = 289943) B289943
theorem B291599 : Blo 127788 291599 := bstep (se 1 (by rfl) ⟨218699, by rfl⟩ : syracuseStep 291599 = 437399) B437399
theorem B291617 : Blo 127788 291617 := bstep (se 2 (by rfl) ⟨109356, by rfl⟩ : syracuseStep 291617 = 218713) B218713
theorem B324395 : Blo 127788 324395 := bstep (se 1 (by rfl) ⟨243296, by rfl⟩ : syracuseStep 324395 = 486593) B486593
theorem B193337 : Blo 127788 193337 := bstep (se 2 (by rfl) ⟨72501, by rfl⟩ : syracuseStep 193337 = 145003) B145003
theorem B127803 : Blo 127788 127803 := bstep (se 1 (by rfl) ⟨95852, by rfl⟩ : syracuseStep 127803 = 191705) B191705
theorem B389947 : Blo 127788 389947 := bstep (se 1 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 389947 = 584921) B584921
theorem B127879 : Blo 127788 127879 := bstep (se 1 (by rfl) ⟨95909, by rfl⟩ : syracuseStep 127879 = 191819) B191819
theorem B193415 : Blo 127788 193415 := bstep (se 1 (by rfl) ⟨145061, by rfl⟩ : syracuseStep 193415 = 290123) B290123
theorem B127887 : Blo 127788 127887 := bstep (se 1 (by rfl) ⟨95915, by rfl⟩ : syracuseStep 127887 = 191831) B191831
theorem B488339 : Blo 127788 488339 := bstep (se 1 (by rfl) ⟨366254, by rfl⟩ : syracuseStep 488339 = 732509) B732509
theorem B193451 : Blo 127788 193451 := bstep (se 1 (by rfl) ⟨145088, by rfl⟩ : syracuseStep 193451 = 290177) B290177
theorem B127931 : Blo 127788 127931 := bstep (se 1 (by rfl) ⟨95948, by rfl⟩ : syracuseStep 127931 = 191897) B191897
theorem B193481 : Blo 127788 193481 := bstep (se 2 (by rfl) ⟨72555, by rfl⟩ : syracuseStep 193481 = 145111) B145111
theorem B128007 : Blo 127788 128007 := bstep (se 1 (by rfl) ⟨96005, by rfl⟩ : syracuseStep 128007 = 192011) B192011
theorem B128015 : Blo 127788 128015 := bstep (se 1 (by rfl) ⟨96011, by rfl⟩ : syracuseStep 128015 = 192023) B192023
theorem B128059 : Blo 127788 128059 := bstep (se 1 (by rfl) ⟨96044, by rfl⟩ : syracuseStep 128059 = 192089) B192089
theorem B193595 : Blo 127788 193595 := bstep (se 1 (by rfl) ⟨145196, by rfl⟩ : syracuseStep 193595 = 290393) B290393
theorem B193655 : Blo 127788 193655 := bstep (se 1 (by rfl) ⟨145241, by rfl⟩ : syracuseStep 193655 = 290483) B290483
theorem B291959 : Blo 127788 291959 := bstep (se 1 (by rfl) ⟨218969, by rfl⟩ : syracuseStep 291959 = 437939) B437939
theorem B128135 : Blo 127788 128135 := bstep (se 1 (by rfl) ⟨96101, by rfl⟩ : syracuseStep 128135 = 192203) B192203
theorem B128143 : Blo 127788 128143 := bstep (se 1 (by rfl) ⟨96107, by rfl⟩ : syracuseStep 128143 = 192215) B192215
theorem B193679 : Blo 127788 193679 := bstep (se 1 (by rfl) ⟨145259, by rfl⟩ : syracuseStep 193679 = 290519) B290519
theorem B193721 : Blo 127788 193721 := bstep (se 2 (by rfl) ⟨72645, by rfl⟩ : syracuseStep 193721 = 145291) B145291
theorem B128187 : Blo 127788 128187 := bstep (se 1 (by rfl) ⟨96140, by rfl⟩ : syracuseStep 128187 = 192281) B192281
theorem B128263 : Blo 127788 128263 := bstep (se 1 (by rfl) ⟨96197, by rfl⟩ : syracuseStep 128263 = 192395) B192395
theorem B193799 : Blo 127788 193799 := bstep (se 1 (by rfl) ⟨145349, by rfl⟩ : syracuseStep 193799 = 290699) B290699
theorem B128271 : Blo 127788 128271 := bstep (se 1 (by rfl) ⟨96203, by rfl⟩ : syracuseStep 128271 = 192407) B192407
theorem B292139 : Blo 127788 292139 := bstep (se 1 (by rfl) ⟨219104, by rfl⟩ : syracuseStep 292139 = 438209) B438209
theorem B193835 : Blo 127788 193835 := bstep (se 1 (by rfl) ⟨145376, by rfl⟩ : syracuseStep 193835 = 290753) B290753
theorem B128315 : Blo 127788 128315 := bstep (se 1 (by rfl) ⟨96236, by rfl⟩ : syracuseStep 128315 = 192473) B192473
theorem B193865 : Blo 127788 193865 := bstep (se 2 (by rfl) ⟨72699, by rfl⟩ : syracuseStep 193865 = 145399) B145399
theorem B128391 : Blo 127788 128391 := bstep (se 1 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 128391 = 192587) B192587
theorem B128399 : Blo 127788 128399 := bstep (se 1 (by rfl) ⟨96299, by rfl⟩ : syracuseStep 128399 = 192599) B192599
theorem B652697 : Blo 127788 652697 := bstep (se 2 (by rfl) ⟨244761, by rfl⟩ : syracuseStep 652697 = 489523) B489523
theorem B128443 : Blo 127788 128443 := bstep (se 1 (by rfl) ⟨96332, by rfl⟩ : syracuseStep 128443 = 192665) B192665
theorem B193979 : Blo 127788 193979 := bstep (se 1 (by rfl) ⟨145484, by rfl⟩ : syracuseStep 193979 = 290969) B290969
theorem B194039 : Blo 127788 194039 := bstep (se 1 (by rfl) ⟨145529, by rfl⟩ : syracuseStep 194039 = 291059) B291059
theorem B128519 : Blo 127788 128519 := bstep (se 1 (by rfl) ⟨96389, by rfl⟩ : syracuseStep 128519 = 192779) B192779
theorem B128527 : Blo 127788 128527 := bstep (se 1 (by rfl) ⟨96395, by rfl⟩ : syracuseStep 128527 = 192791) B192791
theorem B194063 : Blo 127788 194063 := bstep (se 1 (by rfl) ⟨145547, by rfl⟩ : syracuseStep 194063 = 291095) B291095
theorem B194105 : Blo 127788 194105 := bstep (se 2 (by rfl) ⟨72789, by rfl⟩ : syracuseStep 194105 = 145579) B145579
theorem B128571 : Blo 127788 128571 := bstep (se 1 (by rfl) ⟨96428, by rfl⟩ : syracuseStep 128571 = 192857) B192857
theorem B325235 : Blo 127788 325235 := bstep (se 1 (by rfl) ⟨243926, by rfl⟩ : syracuseStep 325235 = 487853) B487853
theorem B325255 : Blo 127788 325255 := bstep (se 1 (by rfl) ⟨243941, by rfl⟩ : syracuseStep 325255 = 487883) B487883
theorem B128647 : Blo 127788 128647 := bstep (se 1 (by rfl) ⟨96485, by rfl⟩ : syracuseStep 128647 = 192971) B192971
theorem B194183 : Blo 127788 194183 := bstep (se 1 (by rfl) ⟨145637, by rfl⟩ : syracuseStep 194183 = 291275) B291275
theorem B128655 : Blo 127788 128655 := bstep (se 1 (by rfl) ⟨96491, by rfl⟩ : syracuseStep 128655 = 192983) B192983
theorem B292499 : Blo 127788 292499 := bstep (se 1 (by rfl) ⟨219374, by rfl⟩ : syracuseStep 292499 = 438749) B438749
theorem B194219 : Blo 127788 194219 := bstep (se 1 (by rfl) ⟨145664, by rfl⟩ : syracuseStep 194219 = 291329) B291329
theorem B128699 : Blo 127788 128699 := bstep (se 1 (by rfl) ⟨96524, by rfl⟩ : syracuseStep 128699 = 193049) B193049
theorem B194249 : Blo 127788 194249 := bstep (se 2 (by rfl) ⟨72843, by rfl⟩ : syracuseStep 194249 = 145687) B145687
theorem B292553 : Blo 127788 292553 := bstep (se 2 (by rfl) ⟨109707, by rfl⟩ : syracuseStep 292553 = 219415) B219415
theorem B128775 : Blo 127788 128775 := bstep (se 1 (by rfl) ⟨96581, by rfl⟩ : syracuseStep 128775 = 193163) B193163
theorem B128783 : Blo 127788 128783 := bstep (se 1 (by rfl) ⟨96587, by rfl⟩ : syracuseStep 128783 = 193175) B193175
theorem B128827 : Blo 127788 128827 := bstep (se 1 (by rfl) ⟨96620, by rfl⟩ : syracuseStep 128827 = 193241) B193241
theorem B194363 : Blo 127788 194363 := bstep (se 1 (by rfl) ⟨145772, by rfl⟩ : syracuseStep 194363 = 291545) B291545
theorem B194423 : Blo 127788 194423 := bstep (se 1 (by rfl) ⟨145817, by rfl⟩ : syracuseStep 194423 = 291635) B291635
theorem B128903 : Blo 127788 128903 := bstep (se 1 (by rfl) ⟨96677, by rfl⟩ : syracuseStep 128903 = 193355) B193355
theorem B128911 : Blo 127788 128911 := bstep (se 1 (by rfl) ⟨96683, by rfl⟩ : syracuseStep 128911 = 193367) B193367
theorem B194447 : Blo 127788 194447 := bstep (se 1 (by rfl) ⟨145835, by rfl⟩ : syracuseStep 194447 = 291671) B291671
theorem B325529 : Blo 127788 325529 := bstep (se 2 (by rfl) ⟨122073, by rfl⟩ : syracuseStep 325529 = 244147) B244147
theorem B194489 : Blo 127788 194489 := bstep (se 2 (by rfl) ⟨72933, by rfl⟩ : syracuseStep 194489 = 145867) B145867
theorem B128955 : Blo 127788 128955 := bstep (se 1 (by rfl) ⟨96716, by rfl⟩ : syracuseStep 128955 = 193433) B193433
theorem B129031 : Blo 127788 129031 := bstep (se 1 (by rfl) ⟨96773, by rfl⟩ : syracuseStep 129031 = 193547) B193547
theorem B194567 : Blo 127788 194567 := bstep (se 1 (by rfl) ⟨145925, by rfl⟩ : syracuseStep 194567 = 291851) B291851
theorem B2488333 : Blo 127788 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B260111 : Blo 127788 260111 := bstep (se 1 (by rfl) ⟨195083, by rfl⟩ : syracuseStep 260111 = 390167) B390167
theorem B292879 : Blo 127788 292879 := bstep (se 1 (by rfl) ⟨219659, by rfl⟩ : syracuseStep 292879 = 439319) B439319
theorem B129039 : Blo 127788 129039 := bstep (se 1 (by rfl) ⟨96779, by rfl⟩ : syracuseStep 129039 = 193559) B193559
theorem B194603 : Blo 127788 194603 := bstep (se 1 (by rfl) ⟨145952, by rfl⟩ : syracuseStep 194603 = 291905) B291905
theorem B325691 : Blo 127788 325691 := bstep (se 1 (by rfl) ⟨244268, by rfl⟩ : syracuseStep 325691 = 488537) B488537
theorem B129083 : Blo 127788 129083 := bstep (se 1 (by rfl) ⟨96812, by rfl⟩ : syracuseStep 129083 = 193625) B193625
theorem B194633 : Blo 127788 194633 := bstep (se 2 (by rfl) ⟨72987, by rfl⟩ : syracuseStep 194633 = 145975) B145975
theorem B129159 : Blo 127788 129159 := bstep (se 1 (by rfl) ⟨96869, by rfl⟩ : syracuseStep 129159 = 193739) B193739
theorem B129167 : Blo 127788 129167 := bstep (se 1 (by rfl) ⟨96875, by rfl⟩ : syracuseStep 129167 = 193751) B193751
theorem B129211 : Blo 127788 129211 := bstep (se 1 (by rfl) ⟨96908, by rfl⟩ : syracuseStep 129211 = 193817) B193817
theorem B194747 : Blo 127788 194747 := bstep (se 1 (by rfl) ⟨146060, by rfl⟩ : syracuseStep 194747 = 292121) B292121
theorem B194761 : Blo 127788 194761 := bstep (se 2 (by rfl) ⟨73035, by rfl⟩ : syracuseStep 194761 = 146071) B146071
theorem B194807 : Blo 127788 194807 := bstep (se 1 (by rfl) ⟨146105, by rfl⟩ : syracuseStep 194807 = 292211) B292211
theorem B129287 : Blo 127788 129287 := bstep (se 1 (by rfl) ⟨96965, by rfl⟩ : syracuseStep 129287 = 193931) B193931
theorem B325903 : Blo 127788 325903 := bstep (se 1 (by rfl) ⟨244427, by rfl⟩ : syracuseStep 325903 = 488855) B488855
theorem B129295 : Blo 127788 129295 := bstep (se 1 (by rfl) ⟨96971, by rfl⟩ : syracuseStep 129295 = 193943) B193943
theorem B194831 : Blo 127788 194831 := bstep (se 1 (by rfl) ⟨146123, by rfl⟩ : syracuseStep 194831 = 292247) B292247
theorem B162091 : Blo 127788 162091 := bstep (se 1 (by rfl) ⟨121568, by rfl⟩ : syracuseStep 162091 = 243137) B243137
theorem B194873 : Blo 127788 194873 := bstep (se 2 (by rfl) ⟨73077, by rfl⟩ : syracuseStep 194873 = 146155) B146155
theorem B129339 : Blo 127788 129339 := bstep (se 1 (by rfl) ⟨97004, by rfl⟩ : syracuseStep 129339 = 194009) B194009
theorem B129415 : Blo 127788 129415 := bstep (se 1 (by rfl) ⟨97061, by rfl⟩ : syracuseStep 129415 = 194123) B194123
theorem B194951 : Blo 127788 194951 := bstep (se 1 (by rfl) ⟨146213, by rfl⟩ : syracuseStep 194951 = 292427) B292427
theorem B293255 : Blo 127788 293255 := bstep (se 1 (by rfl) ⟨219941, by rfl⟩ : syracuseStep 293255 = 439883) B439883
theorem B129423 : Blo 127788 129423 := bstep (se 1 (by rfl) ⟨97067, by rfl⟩ : syracuseStep 129423 = 194135) B194135
theorem B194987 : Blo 127788 194987 := bstep (se 1 (by rfl) ⟨146240, by rfl⟩ : syracuseStep 194987 = 292481) B292481
theorem B129467 : Blo 127788 129467 := bstep (se 1 (by rfl) ⟨97100, by rfl⟩ : syracuseStep 129467 = 194201) B194201
theorem B195017 : Blo 127788 195017 := bstep (se 2 (by rfl) ⟨73131, by rfl⟩ : syracuseStep 195017 = 146263) B146263
theorem B129543 : Blo 127788 129543 := bstep (se 1 (by rfl) ⟨97157, by rfl⟩ : syracuseStep 129543 = 194315) B194315
theorem B489995 : Blo 127788 489995 := bstep (se 1 (by rfl) ⟨367496, by rfl⟩ : syracuseStep 489995 = 734993) B734993
theorem B162319 : Blo 127788 162319 := bstep (se 1 (by rfl) ⟨121739, by rfl⟩ : syracuseStep 162319 = 243479) B243479
theorem B129551 : Blo 127788 129551 := bstep (se 1 (by rfl) ⟨97163, by rfl⟩ : syracuseStep 129551 = 194327) B194327
theorem B326177 : Blo 127788 326177 := bstep (se 2 (by rfl) ⟨122316, by rfl⟩ : syracuseStep 326177 = 244633) B244633
theorem B129595 : Blo 127788 129595 := bstep (se 1 (by rfl) ⟨97196, by rfl⟩ : syracuseStep 129595 = 194393) B194393
theorem B195131 : Blo 127788 195131 := bstep (se 1 (by rfl) ⟨146348, by rfl⟩ : syracuseStep 195131 = 292697) B292697
theorem B293435 : Blo 127788 293435 := bstep (se 1 (by rfl) ⟨220076, by rfl⟩ : syracuseStep 293435 = 440153) B440153
theorem B195191 : Blo 127788 195191 := bstep (se 1 (by rfl) ⟨146393, by rfl⟩ : syracuseStep 195191 = 292787) B292787
theorem B129671 : Blo 127788 129671 := bstep (se 1 (by rfl) ⟨97253, by rfl⟩ : syracuseStep 129671 = 194507) B194507
theorem B129679 : Blo 127788 129679 := bstep (se 1 (by rfl) ⟨97259, by rfl⟩ : syracuseStep 129679 = 194519) B194519
theorem B195215 : Blo 127788 195215 := bstep (se 1 (by rfl) ⟨146411, by rfl⟩ : syracuseStep 195215 = 292823) B292823
theorem B621229 : Blo 127788 621229 := bstep (se 3 (by rfl) ⟨116480, by rfl⟩ : syracuseStep 621229 = 232961) B232961
theorem B195257 : Blo 127788 195257 := bstep (se 2 (by rfl) ⟨73221, by rfl⟩ : syracuseStep 195257 = 146443) B146443
theorem B293561 : Blo 127788 293561 := bstep (se 2 (by rfl) ⟨110085, by rfl⟩ : syracuseStep 293561 = 220171) B220171
theorem B129723 : Blo 127788 129723 := bstep (se 1 (by rfl) ⟨97292, by rfl⟩ : syracuseStep 129723 = 194585) B194585
theorem B424649 : Blo 127788 424649 := bstep (se 2 (by rfl) ⟨159243, by rfl⟩ : syracuseStep 424649 = 318487) B318487
theorem B129799 : Blo 127788 129799 := bstep (se 1 (by rfl) ⟨97349, by rfl⟩ : syracuseStep 129799 = 194699) B194699
theorem B195335 : Blo 127788 195335 := bstep (se 1 (by rfl) ⟨146501, by rfl⟩ : syracuseStep 195335 = 293003) B293003
theorem B129807 : Blo 127788 129807 := bstep (se 1 (by rfl) ⟨97355, by rfl⟩ : syracuseStep 129807 = 194711) B194711
theorem B195371 : Blo 127788 195371 := bstep (se 1 (by rfl) ⟨146528, by rfl⟩ : syracuseStep 195371 = 293057) B293057
theorem B129851 : Blo 127788 129851 := bstep (se 1 (by rfl) ⟨97388, by rfl⟩ : syracuseStep 129851 = 194777) B194777
theorem B195401 : Blo 127788 195401 := bstep (se 2 (by rfl) ⟨73275, by rfl⟩ : syracuseStep 195401 = 146551) B146551
theorem B129927 : Blo 127788 129927 := bstep (se 1 (by rfl) ⟨97445, by rfl⟩ : syracuseStep 129927 = 194891) B194891
theorem B129935 : Blo 127788 129935 := bstep (se 1 (by rfl) ⟨97451, by rfl⟩ : syracuseStep 129935 = 194903) B194903
theorem B129979 : Blo 127788 129979 := bstep (se 1 (by rfl) ⟨97484, by rfl⟩ : syracuseStep 129979 = 194969) B194969
theorem B195515 : Blo 127788 195515 := bstep (se 1 (by rfl) ⟨146636, by rfl⟩ : syracuseStep 195515 = 293273) B293273
theorem B195575 : Blo 127788 195575 := bstep (se 1 (by rfl) ⟨146681, by rfl⟩ : syracuseStep 195575 = 293363) B293363
theorem B130055 : Blo 127788 130055 := bstep (se 1 (by rfl) ⟨97541, by rfl⟩ : syracuseStep 130055 = 195083) B195083
theorem B130063 : Blo 127788 130063 := bstep (se 1 (by rfl) ⟨97547, by rfl⟩ : syracuseStep 130063 = 195095) B195095
theorem B195599 : Blo 127788 195599 := bstep (se 1 (by rfl) ⟨146699, by rfl⟩ : syracuseStep 195599 = 293399) B293399
theorem B293903 : Blo 127788 293903 := bstep (se 1 (by rfl) ⟨220427, by rfl⟩ : syracuseStep 293903 = 440855) B440855
theorem B293921 : Blo 127788 293921 := bstep (se 2 (by rfl) ⟨110220, by rfl⟩ : syracuseStep 293921 = 220441) B220441
theorem B195641 : Blo 127788 195641 := bstep (se 2 (by rfl) ⟨73365, by rfl⟩ : syracuseStep 195641 = 146731) B146731
theorem B130107 : Blo 127788 130107 := bstep (se 1 (by rfl) ⟨97580, by rfl⟩ : syracuseStep 130107 = 195161) B195161
theorem B130183 : Blo 127788 130183 := bstep (se 1 (by rfl) ⟨97637, by rfl⟩ : syracuseStep 130183 = 195275) B195275
theorem B195719 : Blo 127788 195719 := bstep (se 1 (by rfl) ⟨146789, by rfl⟩ : syracuseStep 195719 = 293579) B293579
theorem B130191 : Blo 127788 130191 := bstep (se 1 (by rfl) ⟨97643, by rfl⟩ : syracuseStep 130191 = 195287) B195287
theorem B195755 : Blo 127788 195755 := bstep (se 1 (by rfl) ⟨146816, by rfl⟩ : syracuseStep 195755 = 293633) B293633
theorem B130235 : Blo 127788 130235 := bstep (se 1 (by rfl) ⟨97676, by rfl⟩ : syracuseStep 130235 = 195353) B195353
theorem B195785 : Blo 127788 195785 := bstep (se 2 (by rfl) ⟨73419, by rfl⟩ : syracuseStep 195785 = 146839) B146839
theorem B163063 : Blo 127788 163063 := bstep (se 1 (by rfl) ⟨122297, by rfl⟩ : syracuseStep 163063 = 244595) B244595
theorem B130311 : Blo 127788 130311 := bstep (se 1 (by rfl) ⟨97733, by rfl⟩ : syracuseStep 130311 = 195467) B195467
theorem B130319 : Blo 127788 130319 := bstep (se 1 (by rfl) ⟨97739, by rfl⟩ : syracuseStep 130319 = 195479) B195479
theorem B130363 : Blo 127788 130363 := bstep (se 1 (by rfl) ⟨97772, by rfl⟩ : syracuseStep 130363 = 195545) B195545
theorem B195899 : Blo 127788 195899 := bstep (se 1 (by rfl) ⟨146924, by rfl⟩ : syracuseStep 195899 = 293849) B293849
theorem B195959 : Blo 127788 195959 := bstep (se 1 (by rfl) ⟨146969, by rfl⟩ : syracuseStep 195959 = 293939) B293939
theorem B294263 : Blo 127788 294263 := bstep (se 1 (by rfl) ⟨220697, by rfl⟩ : syracuseStep 294263 = 441395) B441395
theorem B130439 : Blo 127788 130439 := bstep (se 1 (by rfl) ⟨97829, by rfl⟩ : syracuseStep 130439 = 195659) B195659
theorem B130447 : Blo 127788 130447 := bstep (se 1 (by rfl) ⟨97835, by rfl⟩ : syracuseStep 130447 = 195671) B195671
theorem B195983 : Blo 127788 195983 := bstep (se 1 (by rfl) ⟨146987, by rfl⟩ : syracuseStep 195983 = 293975) B293975
theorem B196025 : Blo 127788 196025 := bstep (se 2 (by rfl) ⟨73509, by rfl⟩ : syracuseStep 196025 = 147019) B147019
theorem B130491 : Blo 127788 130491 := bstep (se 1 (by rfl) ⟨97868, by rfl⟩ : syracuseStep 130491 = 195737) B195737
theorem B130567 : Blo 127788 130567 := bstep (se 1 (by rfl) ⟨97925, by rfl⟩ : syracuseStep 130567 = 195851) B195851
theorem B196103 : Blo 127788 196103 := bstep (se 1 (by rfl) ⟨147077, by rfl⟩ : syracuseStep 196103 = 294155) B294155
theorem B327179 : Blo 127788 327179 := bstep (se 1 (by rfl) ⟨245384, by rfl⟩ : syracuseStep 327179 = 490769) B490769
theorem B130575 : Blo 127788 130575 := bstep (se 1 (by rfl) ⟨97931, by rfl⟩ : syracuseStep 130575 = 195863) B195863
theorem B196139 : Blo 127788 196139 := bstep (se 1 (by rfl) ⟨147104, by rfl⟩ : syracuseStep 196139 = 294209) B294209
theorem B294443 : Blo 127788 294443 := bstep (se 1 (by rfl) ⟨220832, by rfl⟩ : syracuseStep 294443 = 441665) B441665
theorem B163387 : Blo 127788 163387 := bstep (se 1 (by rfl) ⟨122540, by rfl⟩ : syracuseStep 163387 = 245081) B245081
theorem B130619 : Blo 127788 130619 := bstep (se 1 (by rfl) ⟨97964, by rfl⟩ : syracuseStep 130619 = 195929) B195929
theorem B196169 : Blo 127788 196169 := bstep (se 2 (by rfl) ⟨73563, by rfl⟩ : syracuseStep 196169 = 147127) B147127
theorem B130695 : Blo 127788 130695 := bstep (se 1 (by rfl) ⟨98021, by rfl⟩ : syracuseStep 130695 = 196043) B196043
theorem B130703 : Blo 127788 130703 := bstep (se 1 (by rfl) ⟨98027, by rfl⟩ : syracuseStep 130703 = 196055) B196055
theorem B130747 : Blo 127788 130747 := bstep (se 1 (by rfl) ⟨98060, by rfl⟩ : syracuseStep 130747 = 196121) B196121
theorem B196283 : Blo 127788 196283 := bstep (se 1 (by rfl) ⟨147212, by rfl⟩ : syracuseStep 196283 = 294425) B294425
theorem B196343 : Blo 127788 196343 := bstep (se 1 (by rfl) ⟨147257, by rfl⟩ : syracuseStep 196343 = 294515) B294515
theorem B3768065 : Blo 127788 3768065 := bstep (se 2 (by rfl) ⟨1413024, by rfl⟩ : syracuseStep 3768065 = 2826049) B2826049
theorem B425729 : Blo 127788 425729 := bstep (se 2 (by rfl) ⟨159648, by rfl⟩ : syracuseStep 425729 = 319297) B319297
theorem B130823 : Blo 127788 130823 := bstep (se 1 (by rfl) ⟨98117, by rfl⟩ : syracuseStep 130823 = 196235) B196235
theorem B130831 : Blo 127788 130831 := bstep (se 1 (by rfl) ⟨98123, by rfl⟩ : syracuseStep 130831 = 196247) B196247
theorem B196367 : Blo 127788 196367 := bstep (se 1 (by rfl) ⟨147275, by rfl⟩ : syracuseStep 196367 = 294551) B294551
theorem B196409 : Blo 127788 196409 := bstep (se 2 (by rfl) ⟨73653, by rfl⟩ : syracuseStep 196409 = 147307) B147307
theorem B130875 : Blo 127788 130875 := bstep (se 1 (by rfl) ⟨98156, by rfl⟩ : syracuseStep 130875 = 196313) B196313
theorem B130951 : Blo 127788 130951 := bstep (se 1 (by rfl) ⟨98213, by rfl⟩ : syracuseStep 130951 = 196427) B196427
theorem B196487 : Blo 127788 196487 := bstep (se 1 (by rfl) ⟨147365, by rfl⟩ : syracuseStep 196487 = 294731) B294731
theorem B130959 : Blo 127788 130959 := bstep (se 1 (by rfl) ⟨98219, by rfl⟩ : syracuseStep 130959 = 196439) B196439
theorem B294803 : Blo 127788 294803 := bstep (se 1 (by rfl) ⟨221102, by rfl⟩ : syracuseStep 294803 = 442205) B442205
theorem B196523 : Blo 127788 196523 := bstep (se 1 (by rfl) ⟨147392, by rfl⟩ : syracuseStep 196523 = 294785) B294785
theorem B655289 : Blo 127788 655289 := bstep (se 2 (by rfl) ⟨245733, by rfl⟩ : syracuseStep 655289 = 491467) B491467
theorem B131003 : Blo 127788 131003 := bstep (se 1 (by rfl) ⟨98252, by rfl⟩ : syracuseStep 131003 = 196505) B196505
theorem B196553 : Blo 127788 196553 := bstep (se 2 (by rfl) ⟨73707, by rfl⟩ : syracuseStep 196553 = 147415) B147415
theorem B294857 : Blo 127788 294857 := bstep (se 2 (by rfl) ⟨110571, by rfl⟩ : syracuseStep 294857 = 221143) B221143
theorem B131111 : Blo 127788 131111 := bstep (se 1 (by rfl) ⟨98333, by rfl⟩ : syracuseStep 131111 = 196667) B196667
theorem B131151 : Blo 127788 131151 := bstep (se 1 (by rfl) ⟨98363, by rfl⟩ : syracuseStep 131151 = 196727) B196727
theorem B131167 : Blo 127788 131167 := bstep (se 1 (by rfl) ⟨98375, by rfl⟩ : syracuseStep 131167 = 196751) B196751
theorem B131195 : Blo 127788 131195 := bstep (se 1 (by rfl) ⟨98396, by rfl⟩ : syracuseStep 131195 = 196793) B196793
theorem B1441955 : Blo 127788 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B131247 : Blo 127788 131247 := bstep (se 1 (by rfl) ⟨98435, by rfl⟩ : syracuseStep 131247 = 196871) B196871
theorem B131271 : Blo 127788 131271 := bstep (se 1 (by rfl) ⟨98453, by rfl⟩ : syracuseStep 131271 = 196907) B196907
theorem B131291 : Blo 127788 131291 := bstep (se 1 (by rfl) ⟨98468, by rfl⟩ : syracuseStep 131291 = 196937) B196937
theorem B131367 : Blo 127788 131367 := bstep (se 1 (by rfl) ⟨98525, by rfl⟩ : syracuseStep 131367 = 197051) B197051
theorem B131407 : Blo 127788 131407 := bstep (se 1 (by rfl) ⟨98555, by rfl⟩ : syracuseStep 131407 = 197111) B197111
theorem B131423 : Blo 127788 131423 := bstep (se 1 (by rfl) ⟨98567, by rfl⟩ : syracuseStep 131423 = 197135) B197135
theorem B131451 : Blo 127788 131451 := bstep (se 1 (by rfl) ⟨98588, by rfl⟩ : syracuseStep 131451 = 197177) B197177
theorem B262543 : Blo 127788 262543 := bstep (se 1 (by rfl) ⟨196907, by rfl⟩ : syracuseStep 262543 = 393815) B393815
theorem B197039 : Blo 127788 197039 := bstep (se 1 (by rfl) ⟨147779, by rfl⟩ : syracuseStep 197039 = 295559) B295559
theorem B131503 : Blo 127788 131503 := bstep (se 1 (by rfl) ⟨98627, by rfl⟩ : syracuseStep 131503 = 197255) B197255
theorem B131527 : Blo 127788 131527 := bstep (se 1 (by rfl) ⟨98645, by rfl⟩ : syracuseStep 131527 = 197291) B197291
theorem B131547 : Blo 127788 131547 := bstep (se 1 (by rfl) ⟨98660, by rfl⟩ : syracuseStep 131547 = 197321) B197321
theorem B557549 : Blo 127788 557549 := bstep (se 3 (by rfl) ⟨104540, by rfl⟩ : syracuseStep 557549 = 209081) B209081
theorem B295433 : Blo 127788 295433 := bstep (se 2 (by rfl) ⟨110787, by rfl⟩ : syracuseStep 295433 = 221575) B221575
theorem B197129 : Blo 127788 197129 := bstep (se 2 (by rfl) ⟨73923, by rfl⟩ : syracuseStep 197129 = 147847) B147847
theorem B197159 : Blo 127788 197159 := bstep (se 1 (by rfl) ⟨147869, by rfl⟩ : syracuseStep 197159 = 295739) B295739
theorem B131623 : Blo 127788 131623 := bstep (se 1 (by rfl) ⟨98717, by rfl⟩ : syracuseStep 131623 = 197435) B197435
theorem B131663 : Blo 127788 131663 := bstep (se 1 (by rfl) ⟨98747, by rfl⟩ : syracuseStep 131663 = 197495) B197495
theorem B131679 : Blo 127788 131679 := bstep (se 1 (by rfl) ⟨98759, by rfl⟩ : syracuseStep 131679 = 197519) B197519
theorem B197243 : Blo 127788 197243 := bstep (se 1 (by rfl) ⟨147932, by rfl⟩ : syracuseStep 197243 = 295865) B295865
theorem B131707 : Blo 127788 131707 := bstep (se 1 (by rfl) ⟨98780, by rfl⟩ : syracuseStep 131707 = 197561) B197561
theorem B131759 : Blo 127788 131759 := bstep (se 1 (by rfl) ⟨98819, by rfl⟩ : syracuseStep 131759 = 197639) B197639
theorem B131783 : Blo 127788 131783 := bstep (se 1 (by rfl) ⟨98837, by rfl⟩ : syracuseStep 131783 = 197675) B197675
theorem B262867 : Blo 127788 262867 := bstep (se 1 (by rfl) ⟨197150, by rfl⟩ : syracuseStep 262867 = 394301) B394301
theorem B197369 : Blo 127788 197369 := bstep (se 2 (by rfl) ⟨74013, by rfl⟩ : syracuseStep 197369 = 148027) B148027
theorem B295775 : Blo 127788 295775 := bstep (se 1 (by rfl) ⟨221831, by rfl⟩ : syracuseStep 295775 = 443663) B443663
theorem B197471 : Blo 127788 197471 := bstep (se 1 (by rfl) ⟨148103, by rfl⟩ : syracuseStep 197471 = 296207) B296207
theorem B197483 : Blo 127788 197483 := bstep (se 1 (by rfl) ⟨148112, by rfl⟩ : syracuseStep 197483 = 296225) B296225
theorem B328711 : Blo 127788 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B295955 : Blo 127788 295955 := bstep (se 1 (by rfl) ⟨221966, by rfl⟩ : syracuseStep 295955 = 443933) B443933
theorem B197711 : Blo 127788 197711 := bstep (se 1 (by rfl) ⟨148283, by rfl⟩ : syracuseStep 197711 = 296567) B296567
theorem B132391 : Blo 127788 132391 := bstep (se 1 (by rfl) ⟨99293, by rfl⟩ : syracuseStep 132391 = 198587) B198587
theorem B296297 : Blo 127788 296297 := bstep (se 2 (by rfl) ⟨111111, by rfl⟩ : syracuseStep 296297 = 222223) B222223
theorem B492925 : Blo 127788 492925 := bstep (se 3 (by rfl) ⟨92423, by rfl⟩ : syracuseStep 492925 = 184847) B184847
theorem B1181147 : Blo 127788 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B624115 : Blo 127788 624115 := bstep (se 1 (by rfl) ⟨468086, by rfl⟩ : syracuseStep 624115 = 936173) B936173
theorem B329255 : Blo 127788 329255 := bstep (se 1 (by rfl) ⟨246941, by rfl⟩ : syracuseStep 329255 = 493883) B493883
theorem B3409451 : Blo 127788 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B329579 : Blo 127788 329579 := bstep (se 1 (by rfl) ⟨247184, by rfl⟩ : syracuseStep 329579 = 494369) B494369
theorem B231635 : Blo 127788 231635 := bstep (se 1 (by rfl) ⟨173726, by rfl⟩ : syracuseStep 231635 = 347453) B347453
theorem B264553 : Blo 127788 264553 := bstep (se 2 (by rfl) ⟨99207, by rfl⟩ : syracuseStep 264553 = 198415) B198415
theorem B330227 : Blo 127788 330227 := bstep (se 1 (by rfl) ⟨247670, by rfl⟩ : syracuseStep 330227 = 495341) B495341
theorem B330439 : Blo 127788 330439 := bstep (se 1 (by rfl) ⟨247829, by rfl⟩ : syracuseStep 330439 = 495659) B495659
theorem B527057 : Blo 127788 527057 := bstep (se 2 (by rfl) ⟨197646, by rfl⟩ : syracuseStep 527057 = 395293) B395293
theorem B658205 : Blo 127788 658205 := bstep (se 3 (by rfl) ⟨123413, by rfl⟩ : syracuseStep 658205 = 246827) B246827
theorem B1772381 : Blo 127788 1772381 := bstep (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) B664643
theorem B1870775 : Blo 127788 1870775 := bstep (se 1 (by rfl) ⟨1403081, by rfl⟩ : syracuseStep 1870775 = 2806163) B2806163
theorem B1051697 : Blo 127788 1051697 := bstep (se 2 (by rfl) ⟨394386, by rfl⟩ : syracuseStep 1051697 = 788773) B788773
theorem B625859 : Blo 127788 625859 := bstep (se 1 (by rfl) ⟨469394, by rfl⟩ : syracuseStep 625859 = 938789) B938789
theorem B232967 : Blo 127788 232967 := bstep (se 1 (by rfl) ⟨174725, by rfl⟩ : syracuseStep 232967 = 349451) B349451
theorem B495143 : Blo 127788 495143 := bstep (se 1 (by rfl) ⟨371357, by rfl⟩ : syracuseStep 495143 = 742715) B742715
theorem B331361 : Blo 127788 331361 := bstep (se 2 (by rfl) ⟨124260, by rfl⟩ : syracuseStep 331361 = 248521) B248521
theorem B3346109 : Blo 127788 3346109 := bstep (se 3 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 3346109 = 1254791) B1254791
theorem B855841 : Blo 127788 855841 := bstep (se 2 (by rfl) ⟨320940, by rfl⟩ : syracuseStep 855841 = 641881) B641881
theorem B331627 : Blo 127788 331627 := bstep (se 1 (by rfl) ⟨248720, by rfl⟩ : syracuseStep 331627 = 497441) B497441
theorem B987065 : Blo 127788 987065 := bstep (se 2 (by rfl) ⟨370149, by rfl⟩ : syracuseStep 987065 = 740299) B740299
theorem B692155 : Blo 127788 692155 := bstep (se 1 (by rfl) ⟨519116, by rfl⟩ : syracuseStep 692155 = 1038233) B1038233
theorem B200827 : Blo 127788 200827 := bstep (se 1 (by rfl) ⟨150620, by rfl⟩ : syracuseStep 200827 = 301241) B301241
theorem B496115 : Blo 127788 496115 := bstep (se 1 (by rfl) ⟨372086, by rfl⟩ : syracuseStep 496115 = 744173) B744173
theorem B266759 : Blo 127788 266759 := bstep (se 1 (by rfl) ⟨200069, by rfl⟩ : syracuseStep 266759 = 400139) B400139
theorem B496313 : Blo 127788 496313 := bstep (se 2 (by rfl) ⟨186117, by rfl⟩ : syracuseStep 496313 = 372235) B372235
theorem B496327 : Blo 127788 496327 := bstep (se 1 (by rfl) ⟨372245, by rfl⟩ : syracuseStep 496327 = 744491) B744491
theorem B4166417 : Blo 127788 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B332651 : Blo 127788 332651 := bstep (se 1 (by rfl) ⟨249488, by rfl⟩ : syracuseStep 332651 = 498977) B498977
theorem B1119197 : Blo 127788 1119197 := bstep (se 3 (by rfl) ⟨209849, by rfl⟩ : syracuseStep 1119197 = 419699) B419699
theorem B332819 : Blo 127788 332819 := bstep (se 1 (by rfl) ⟨249614, by rfl⟩ : syracuseStep 332819 = 499229) B499229
theorem B890027 : Blo 127788 890027 := bstep (se 1 (by rfl) ⟨667520, by rfl⟩ : syracuseStep 890027 = 1335041) B1335041
theorem B431351 : Blo 127788 431351 := bstep (se 1 (by rfl) ⟨323513, by rfl⟩ : syracuseStep 431351 = 647027) B647027
theorem B693629 : Blo 127788 693629 := bstep (se 3 (by rfl) ⟨130055, by rfl⟩ : syracuseStep 693629 = 260111) B260111
theorem B824741 : Blo 127788 824741 := bstep (se 4 (by rfl) ⟨77319, by rfl⟩ : syracuseStep 824741 = 154639) B154639
theorem B562727 : Blo 127788 562727 := bstep (se 1 (by rfl) ⟨422045, by rfl⟩ : syracuseStep 562727 = 844091) B844091
theorem B431675 : Blo 127788 431675 := bstep (se 1 (by rfl) ⟨323756, by rfl⟩ : syracuseStep 431675 = 647513) B647513
theorem B497299 : Blo 127788 497299 := bstep (se 1 (by rfl) ⟨372974, by rfl⟩ : syracuseStep 497299 = 745949) B745949
theorem B431945 : Blo 127788 431945 := bstep (se 2 (by rfl) ⟨161979, by rfl⟩ : syracuseStep 431945 = 323959) B323959
theorem B1055105 : Blo 127788 1055105 := bstep (se 2 (by rfl) ⟨395664, by rfl⟩ : syracuseStep 1055105 = 791329) B791329
theorem B793273 : Blo 127788 793273 := bstep (se 2 (by rfl) ⟨297477, by rfl⟩ : syracuseStep 793273 = 594955) B594955
theorem B989981 : Blo 127788 989981 := bstep (se 3 (by rfl) ⟨185621, by rfl⟩ : syracuseStep 989981 = 371243) B371243
theorem B433079 : Blo 127788 433079 := bstep (se 1 (by rfl) ⟨324809, by rfl⟩ : syracuseStep 433079 = 649619) B649619
theorem B924691 : Blo 127788 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B498707 : Blo 127788 498707 := bstep (se 1 (by rfl) ⟨374030, by rfl⟩ : syracuseStep 498707 = 748061) B748061
theorem B662579 : Blo 127788 662579 := bstep (se 1 (by rfl) ⟨496934, by rfl⟩ : syracuseStep 662579 = 993869) B993869
theorem B138439 : Blo 127788 138439 := bstep (se 1 (by rfl) ⟨103829, by rfl⟩ : syracuseStep 138439 = 207659) B207659
theorem B499031 : Blo 127788 499031 := bstep (se 1 (by rfl) ⟨374273, by rfl⟩ : syracuseStep 499031 = 748547) B748547
theorem B4300121 : Blo 127788 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B433673 : Blo 127788 433673 := bstep (se 2 (by rfl) ⟨162627, by rfl⟩ : syracuseStep 433673 = 325255) B325255
theorem B335483 : Blo 127788 335483 := bstep (se 1 (by rfl) ⟨251612, by rfl⟩ : syracuseStep 335483 = 503225) B503225
theorem B532091 : Blo 127788 532091 := bstep (se 1 (by rfl) ⟨399068, by rfl⟩ : syracuseStep 532091 = 798137) B798137
theorem B368327 : Blo 127788 368327 := bstep (se 1 (by rfl) ⟨276245, by rfl⟩ : syracuseStep 368327 = 552491) B552491
theorem B3317777 : Blo 127788 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B532595 : Blo 127788 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B434537 : Blo 127788 434537 := bstep (se 2 (by rfl) ⟨162951, by rfl⟩ : syracuseStep 434537 = 325903) B325903
theorem B205391 : Blo 127788 205391 := bstep (se 1 (by rfl) ⟨154043, by rfl⟩ : syracuseStep 205391 = 308087) B308087
theorem B664199 : Blo 127788 664199 := bstep (se 1 (by rfl) ⟨498149, by rfl⟩ : syracuseStep 664199 = 996299) B996299
theorem B467779 : Blo 127788 467779 := bstep (se 1 (by rfl) ⟨350834, by rfl⟩ : syracuseStep 467779 = 701669) B701669
theorem B828305 : Blo 127788 828305 := bstep (se 2 (by rfl) ⟨310614, by rfl⟩ : syracuseStep 828305 = 621229) B621229
theorem B435131 : Blo 127788 435131 := bstep (se 1 (by rfl) ⟨326348, by rfl⟩ : syracuseStep 435131 = 652697) B652697
theorem B336953 : Blo 127788 336953 := bstep (se 2 (by rfl) ⟨126357, by rfl⟩ : syracuseStep 336953 = 252715) B252715
theorem B205903 : Blo 127788 205903 := bstep (se 1 (by rfl) ⟨154427, by rfl⟩ : syracuseStep 205903 = 308855) B308855
theorem B140839 : Blo 127788 140839 := bstep (se 1 (by rfl) ⟨105629, by rfl⟩ : syracuseStep 140839 = 211259) B211259
theorem B665657 : Blo 127788 665657 := bstep (se 2 (by rfl) ⟨249621, by rfl⟩ : syracuseStep 665657 = 499243) B499243
theorem B469163 : Blo 127788 469163 := bstep (se 1 (by rfl) ⟨351872, by rfl⟩ : syracuseStep 469163 = 703745) B703745
theorem B469309 : Blo 127788 469309 := bstep (se 3 (by rfl) ⟨87995, by rfl⟩ : syracuseStep 469309 = 175991) B175991
theorem B207287 : Blo 127788 207287 := bstep (se 1 (by rfl) ⟨155465, by rfl⟩ : syracuseStep 207287 = 310931) B310931
theorem B928279 : Blo 127788 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B436859 : Blo 127788 436859 := bstep (se 1 (by rfl) ⟨327644, by rfl⟩ : syracuseStep 436859 = 655289) B655289
theorem B437021 : Blo 127788 437021 := bstep (se 3 (by rfl) ⟨81941, by rfl⟩ : syracuseStep 437021 = 163883) B163883
theorem B9186085 : Blo 127788 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B994355 : Blo 127788 994355 := bstep (se 1 (by rfl) ⟨745766, by rfl⟩ : syracuseStep 994355 = 1491533) B1491533
theorem B1092953 : Blo 127788 1092953 := bstep (se 2 (by rfl) ⟨409857, by rfl⟩ : syracuseStep 1092953 = 819715) B819715
theorem B437723 : Blo 127788 437723 := bstep (se 1 (by rfl) ⟨328292, by rfl⟩ : syracuseStep 437723 = 656585) B656585
theorem B831197 : Blo 127788 831197 := bstep (se 3 (by rfl) ⟨155849, by rfl⟩ : syracuseStep 831197 = 311699) B311699
theorem B208975 : Blo 127788 208975 := bstep (se 1 (by rfl) ⟨156731, by rfl⟩ : syracuseStep 208975 = 313463) B313463
theorem B438425 : Blo 127788 438425 := bstep (se 2 (by rfl) ⟨164409, by rfl⟩ : syracuseStep 438425 = 328819) B328819
theorem B438443 : Blo 127788 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B1585331 : Blo 127788 1585331 := bstep (se 1 (by rfl) ⟨1188998, by rfl⟩ : syracuseStep 1585331 = 2377997) B2377997
theorem B602473 : Blo 127788 602473 := bstep (se 2 (by rfl) ⟨225927, by rfl⟩ : syracuseStep 602473 = 451855) B451855
theorem B143995 : Blo 127788 143995 := bstep (se 1 (by rfl) ⟨107996, by rfl⟩ : syracuseStep 143995 = 215993) B215993
theorem B504643 : Blo 127788 504643 := bstep (se 1 (by rfl) ⟨378482, by rfl⟩ : syracuseStep 504643 = 756965) B756965
theorem B504737 : Blo 127788 504737 := bstep (se 2 (by rfl) ⟨189276, by rfl⟩ : syracuseStep 504737 = 378553) B378553
theorem B275375 : Blo 127788 275375 := bstep (se 1 (by rfl) ⟨206531, by rfl⟩ : syracuseStep 275375 = 413063) B413063
theorem B242651 : Blo 127788 242651 := bstep (se 1 (by rfl) ⟨181988, by rfl⟩ : syracuseStep 242651 = 363977) B363977
theorem B209927 : Blo 127788 209927 := bstep (se 1 (by rfl) ⟨157445, by rfl⟩ : syracuseStep 209927 = 314891) B314891
theorem B144463 : Blo 127788 144463 := bstep (se 1 (by rfl) ⟨108347, by rfl⟩ : syracuseStep 144463 = 216695) B216695
theorem B210119 : Blo 127788 210119 := bstep (se 1 (by rfl) ⟨157589, by rfl⟩ : syracuseStep 210119 = 315179) B315179
theorem B439613 : Blo 127788 439613 := bstep (se 3 (by rfl) ⟨82427, by rfl⟩ : syracuseStep 439613 = 164855) B164855
theorem B374159 : Blo 127788 374159 := bstep (se 1 (by rfl) ⟨280619, by rfl⟩ : syracuseStep 374159 = 561239) B561239
theorem B144859 : Blo 127788 144859 := bstep (se 1 (by rfl) ⟨108644, by rfl⟩ : syracuseStep 144859 = 217289) B217289
theorem B276007 : Blo 127788 276007 := bstep (se 1 (by rfl) ⟨207005, by rfl⟩ : syracuseStep 276007 = 414011) B414011
theorem B1685357 : Blo 127788 1685357 := bstep (se 3 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 1685357 = 632009) B632009
theorem B145327 : Blo 127788 145327 := bstep (se 1 (by rfl) ⟨108995, by rfl⟩ : syracuseStep 145327 = 217991) B217991
theorem B440477 : Blo 127788 440477 := bstep (se 3 (by rfl) ⟨82589, by rfl⟩ : syracuseStep 440477 = 165179) B165179
theorem B243911 : Blo 127788 243911 := bstep (se 1 (by rfl) ⟨182933, by rfl⟩ : syracuseStep 243911 = 365867) B365867
theorem B1718561 : Blo 127788 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B244063 : Blo 127788 244063 := bstep (se 1 (by rfl) ⟨183047, by rfl⟩ : syracuseStep 244063 = 366095) B366095
theorem B145759 : Blo 127788 145759 := bstep (se 1 (by rfl) ⟨109319, by rfl⟩ : syracuseStep 145759 = 218639) B218639
theorem B441017 : Blo 127788 441017 := bstep (se 2 (by rfl) ⟨165381, by rfl⟩ : syracuseStep 441017 = 330763) B330763
theorem B146119 : Blo 127788 146119 := bstep (se 1 (by rfl) ⟨109589, by rfl⟩ : syracuseStep 146119 = 219179) B219179
theorem B736451 : Blo 127788 736451 := bstep (se 1 (by rfl) ⟨552338, by rfl⟩ : syracuseStep 736451 = 1104677) B1104677
theorem B1260791 : Blo 127788 1260791 := bstep (se 1 (by rfl) ⟨945593, by rfl⟩ : syracuseStep 1260791 = 1891187) B1891187
theorem B441611 : Blo 127788 441611 := bstep (se 1 (by rfl) ⟨331208, by rfl⟩ : syracuseStep 441611 = 662417) B662417
theorem B441881 : Blo 127788 441881 := bstep (se 2 (by rfl) ⟨165705, by rfl⟩ : syracuseStep 441881 = 331411) B331411
theorem B146983 : Blo 127788 146983 := bstep (se 1 (by rfl) ⟨110237, by rfl⟩ : syracuseStep 146983 = 220475) B220475
theorem B310999 : Blo 127788 310999 := bstep (se 1 (by rfl) ⟨233249, by rfl⟩ : syracuseStep 310999 = 466499) B466499
theorem B704351 : Blo 127788 704351 := bstep (se 1 (by rfl) ⟨528263, by rfl⟩ : syracuseStep 704351 = 1056527) B1056527
theorem B1228729 : Blo 127788 1228729 := bstep (se 2 (by rfl) ⟨460773, by rfl⟩ : syracuseStep 1228729 = 921547) B921547
theorem B246007 : Blo 127788 246007 := bstep (se 1 (by rfl) ⟨184505, by rfl⟩ : syracuseStep 246007 = 369011) B369011
theorem B1982789 : Blo 127788 1982789 := bstep (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) B371773
theorem B409961 : Blo 127788 409961 := bstep (se 2 (by rfl) ⟨153735, by rfl⟩ : syracuseStep 409961 = 307471) B307471
theorem B246235 : Blo 127788 246235 := bstep (se 1 (by rfl) ⟨184676, by rfl⟩ : syracuseStep 246235 = 369353) B369353
theorem B246311 : Blo 127788 246311 := bstep (se 1 (by rfl) ⟨184733, by rfl⟩ : syracuseStep 246311 = 369467) B369467
theorem B246395 : Blo 127788 246395 := bstep (se 1 (by rfl) ⟨184796, by rfl⟩ : syracuseStep 246395 = 369593) B369593
theorem B443015 : Blo 127788 443015 := bstep (se 1 (by rfl) ⟨332261, by rfl⟩ : syracuseStep 443015 = 664523) B664523
theorem B443069 : Blo 127788 443069 := bstep (se 3 (by rfl) ⟨83075, by rfl⟩ : syracuseStep 443069 = 166151) B166151
theorem B312007 : Blo 127788 312007 := bstep (se 1 (by rfl) ⟨234005, by rfl⟩ : syracuseStep 312007 = 468011) B468011
theorem B443231 : Blo 127788 443231 := bstep (se 1 (by rfl) ⟨332423, by rfl⟩ : syracuseStep 443231 = 664847) B664847
theorem B443393 : Blo 127788 443393 := bstep (se 2 (by rfl) ⟨166272, by rfl⟩ : syracuseStep 443393 = 332545) B332545
theorem B246881 : Blo 127788 246881 := bstep (se 2 (by rfl) ⟨92580, by rfl⟩ : syracuseStep 246881 = 185161) B185161
theorem B280073 : Blo 127788 280073 := bstep (se 2 (by rfl) ⟨105027, by rfl⟩ : syracuseStep 280073 = 210055) B210055
theorem B739115 : Blo 127788 739115 := bstep (se 1 (by rfl) ⟨554336, by rfl⟩ : syracuseStep 739115 = 1108673) B1108673
theorem B444203 : Blo 127788 444203 := bstep (se 1 (by rfl) ⟨333152, by rfl⟩ : syracuseStep 444203 = 666305) B666305
theorem B280415 : Blo 127788 280415 := bstep (se 1 (by rfl) ⟨210311, by rfl⟩ : syracuseStep 280415 = 420623) B420623
theorem B444473 : Blo 127788 444473 := bstep (se 2 (by rfl) ⟨166677, by rfl⟩ : syracuseStep 444473 = 333355) B333355
theorem B1624369 : Blo 127788 1624369 := bstep (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) B1218277
theorem B346511 : Blo 127788 346511 := bstep (se 1 (by rfl) ⟨259883, by rfl⟩ : syracuseStep 346511 = 519767) B519767
theorem B510451 : Blo 127788 510451 := bstep (se 1 (by rfl) ⟨382838, by rfl⟩ : syracuseStep 510451 = 765677) B765677
theorem B248339 : Blo 127788 248339 := bstep (se 1 (by rfl) ⟨186254, by rfl⟩ : syracuseStep 248339 = 372509) B372509
theorem B936481 : Blo 127788 936481 := bstep (se 2 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 936481 = 702361) B702361
theorem B215723 : Blo 127788 215723 := bstep (se 1 (by rfl) ⟨161792, by rfl⟩ : syracuseStep 215723 = 323585) B323585
theorem B510749 : Blo 127788 510749 := bstep (se 3 (by rfl) ⟨95765, by rfl⟩ : syracuseStep 510749 = 191531) B191531
theorem B543671 : Blo 127788 543671 := bstep (se 1 (by rfl) ⟨407753, by rfl⟩ : syracuseStep 543671 = 815507) B815507
theorem B216121 : Blo 127788 216121 := bstep (se 2 (by rfl) ⟨81045, by rfl⟩ : syracuseStep 216121 = 162091) B162091
theorem B216263 : Blo 127788 216263 := bstep (se 1 (by rfl) ⟨162197, by rfl⟩ : syracuseStep 216263 = 324395) B324395
theorem B216425 : Blo 127788 216425 := bstep (se 2 (by rfl) ⟨81159, by rfl⟩ : syracuseStep 216425 = 162319) B162319
theorem B216823 : Blo 127788 216823 := bstep (se 1 (by rfl) ⟨162617, by rfl⟩ : syracuseStep 216823 = 325235) B325235
theorem B1003373 : Blo 127788 1003373 := bstep (se 3 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 1003373 = 376265) B376265
theorem B249743 : Blo 127788 249743 := bstep (se 1 (by rfl) ⟨187307, by rfl⟩ : syracuseStep 249743 = 374615) B374615
theorem B217019 : Blo 127788 217019 := bstep (se 1 (by rfl) ⟨162764, by rfl⟩ : syracuseStep 217019 = 325529) B325529
theorem B217127 : Blo 127788 217127 := bstep (se 1 (by rfl) ⟨162845, by rfl⟩ : syracuseStep 217127 = 325691) B325691
theorem B249895 : Blo 127788 249895 := bstep (se 1 (by rfl) ⟨187421, by rfl⟩ : syracuseStep 249895 = 374843) B374843
theorem B413753 : Blo 127788 413753 := bstep (se 2 (by rfl) ⟨155157, by rfl⟩ : syracuseStep 413753 = 310315) B310315
theorem B249979 : Blo 127788 249979 := bstep (se 1 (by rfl) ⟨187484, by rfl⟩ : syracuseStep 249979 = 374969) B374969
theorem B938213 : Blo 127788 938213 := bstep (se 4 (by rfl) ⟨87957, by rfl⟩ : syracuseStep 938213 = 175915) B175915
theorem B217417 : Blo 127788 217417 := bstep (se 2 (by rfl) ⟨81531, by rfl⟩ : syracuseStep 217417 = 163063) B163063
theorem B217451 : Blo 127788 217451 := bstep (se 1 (by rfl) ⟨163088, by rfl⟩ : syracuseStep 217451 = 326177) B326177
theorem B283099 : Blo 127788 283099 := bstep (se 1 (by rfl) ⟨212324, by rfl⟩ : syracuseStep 283099 = 424649) B424649
theorem B840401 : Blo 127788 840401 := bstep (se 2 (by rfl) ⟨315150, by rfl⟩ : syracuseStep 840401 = 630301) B630301
theorem B217849 : Blo 127788 217849 := bstep (se 2 (by rfl) ⟨81693, by rfl⟩ : syracuseStep 217849 = 163387) B163387
theorem B2249693 : Blo 127788 2249693 := bstep (se 3 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 2249693 = 843635) B843635
theorem B218119 : Blo 127788 218119 := bstep (se 1 (by rfl) ⟨163589, by rfl⟩ : syracuseStep 218119 = 327179) B327179
theorem B2512043 : Blo 127788 2512043 := bstep (se 1 (by rfl) ⟨1884032, by rfl⟩ : syracuseStep 2512043 = 3768065) B3768065
theorem B283819 : Blo 127788 283819 := bstep (se 1 (by rfl) ⟨212864, by rfl⟩ : syracuseStep 283819 = 425729) B425729
theorem B185707 : Blo 127788 185707 := bstep (se 1 (by rfl) ⟨139280, by rfl⟩ : syracuseStep 185707 = 278561) B278561
theorem B218551 : Blo 127788 218551 := bstep (se 1 (by rfl) ⟨163913, by rfl⟩ : syracuseStep 218551 = 327827) B327827
theorem B218747 : Blo 127788 218747 := bstep (se 1 (by rfl) ⟨164060, by rfl⟩ : syracuseStep 218747 = 328121) B328121
theorem B1037971 : Blo 127788 1037971 := bstep (se 1 (by rfl) ⟨778478, by rfl⟩ : syracuseStep 1037971 = 1556957) B1556957
theorem B710365 : Blo 127788 710365 := bstep (se 3 (by rfl) ⟨133193, by rfl⟩ : syracuseStep 710365 = 266387) B266387
theorem B415751 : Blo 127788 415751 := bstep (se 1 (by rfl) ⟨311813, by rfl⟩ : syracuseStep 415751 = 623627) B623627
theorem B219145 : Blo 127788 219145 := bstep (se 2 (by rfl) ⟨82179, by rfl⟩ : syracuseStep 219145 = 164359) B164359
theorem B350365 : Blo 127788 350365 := bstep (se 3 (by rfl) ⟨65693, by rfl⟩ : syracuseStep 350365 = 131387) B131387
theorem B219307 : Blo 127788 219307 := bstep (se 1 (by rfl) ⟨164480, by rfl⟩ : syracuseStep 219307 = 328961) B328961
theorem B743741 : Blo 127788 743741 := bstep (se 3 (by rfl) ⟨139451, by rfl⟩ : syracuseStep 743741 = 278903) B278903
theorem B219611 : Blo 127788 219611 := bstep (se 1 (by rfl) ⟨164708, by rfl⟩ : syracuseStep 219611 = 329417) B329417
theorem B154235 : Blo 127788 154235 := bstep (se 1 (by rfl) ⟨115676, by rfl⟩ : syracuseStep 154235 = 231353) B231353
theorem B219847 : Blo 127788 219847 := bstep (se 1 (by rfl) ⟨164885, by rfl⟩ : syracuseStep 219847 = 329771) B329771
theorem B220009 : Blo 127788 220009 := bstep (se 2 (by rfl) ⟨82503, by rfl⟩ : syracuseStep 220009 = 165007) B165007
theorem B187319 : Blo 127788 187319 := bstep (se 1 (by rfl) ⟨140489, by rfl⟩ : syracuseStep 187319 = 280979) B280979
theorem B973943 : Blo 127788 973943 := bstep (se 1 (by rfl) ⟨730457, by rfl⟩ : syracuseStep 973943 = 1460915) B1460915
theorem B941327 : Blo 127788 941327 := bstep (se 1 (by rfl) ⟨705995, by rfl⟩ : syracuseStep 941327 = 1411991) B1411991
theorem B1105325 : Blo 127788 1105325 := bstep (se 3 (by rfl) ⟨207248, by rfl⟩ : syracuseStep 1105325 = 414497) B414497
theorem B1334701 : Blo 127788 1334701 := bstep (se 3 (by rfl) ⟨250256, by rfl⟩ : syracuseStep 1334701 = 500513) B500513
theorem B220591 : Blo 127788 220591 := bstep (se 1 (by rfl) ⟨165443, by rfl⟩ : syracuseStep 220591 = 330887) B330887
theorem B220603 : Blo 127788 220603 := bstep (se 1 (by rfl) ⟨165452, by rfl⟩ : syracuseStep 220603 = 330905) B330905
theorem B744947 : Blo 127788 744947 := bstep (se 1 (by rfl) ⟨558710, by rfl⟩ : syracuseStep 744947 = 1117421) B1117421
theorem B253459 : Blo 127788 253459 := bstep (se 1 (by rfl) ⟨190094, by rfl⟩ : syracuseStep 253459 = 380189) B380189
theorem B220711 : Blo 127788 220711 := bstep (se 1 (by rfl) ⟨165533, by rfl⟩ : syracuseStep 220711 = 331067) B331067
theorem B351959 : Blo 127788 351959 := bstep (se 1 (by rfl) ⟨263969, by rfl⟩ : syracuseStep 351959 = 527939) B527939
theorem B319339 : Blo 127788 319339 := bstep (se 1 (by rfl) ⟨239504, by rfl⟩ : syracuseStep 319339 = 479009) B479009
theorem B221035 : Blo 127788 221035 := bstep (se 1 (by rfl) ⟨165776, by rfl⟩ : syracuseStep 221035 = 331553) B331553
theorem B1794059 : Blo 127788 1794059 := bstep (se 1 (by rfl) ⟨1345544, by rfl⟩ : syracuseStep 1794059 = 2691089) B2691089
theorem B222095 : Blo 127788 222095 := bstep (se 1 (by rfl) ⟨166571, by rfl⟩ : syracuseStep 222095 = 333143) B333143
theorem B287675 : Blo 127788 287675 := bstep (se 1 (by rfl) ⟨215756, by rfl⟩ : syracuseStep 287675 = 431513) B431513
theorem B287801 : Blo 127788 287801 := bstep (se 2 (by rfl) ⟨107925, by rfl⟩ : syracuseStep 287801 = 215851) B215851
theorem B222331 : Blo 127788 222331 := bstep (se 1 (by rfl) ⟨166748, by rfl⟩ : syracuseStep 222331 = 333497) B333497
theorem B615595 : Blo 127788 615595 := bstep (se 1 (by rfl) ⟨461696, by rfl⟩ : syracuseStep 615595 = 923393) B923393
theorem B288143 : Blo 127788 288143 := bstep (se 1 (by rfl) ⟨216107, by rfl⟩ : syracuseStep 288143 = 432215) B432215
theorem B288467 : Blo 127788 288467 := bstep (se 1 (by rfl) ⟨216350, by rfl⟩ : syracuseStep 288467 = 432701) B432701
theorem B223163 : Blo 127788 223163 := bstep (se 1 (by rfl) ⟨167372, by rfl⟩ : syracuseStep 223163 = 334745) B334745
theorem B747863 : Blo 127788 747863 := bstep (se 1 (by rfl) ⟨560897, by rfl⟩ : syracuseStep 747863 = 1121795) B1121795
theorem B289403 : Blo 127788 289403 := bstep (se 1 (by rfl) ⟨217052, by rfl⟩ : syracuseStep 289403 = 434105) B434105
theorem B289529 : Blo 127788 289529 := bstep (se 2 (by rfl) ⟨108573, by rfl⟩ : syracuseStep 289529 = 217147) B217147
theorem B289799 : Blo 127788 289799 := bstep (se 1 (by rfl) ⟨217349, by rfl⟩ : syracuseStep 289799 = 434699) B434699
theorem B289871 : Blo 127788 289871 := bstep (se 1 (by rfl) ⟨217403, by rfl⟩ : syracuseStep 289871 = 434807) B434807
theorem B191687 : Blo 127788 191687 := bstep (se 1 (by rfl) ⟨143765, by rfl⟩ : syracuseStep 191687 = 287531) B287531
theorem B191849 : Blo 127788 191849 := bstep (se 2 (by rfl) ⟨71943, by rfl⟩ : syracuseStep 191849 = 143887) B143887
theorem B5074319 : Blo 127788 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B191927 : Blo 127788 191927 := bstep (se 1 (by rfl) ⟨143945, by rfl⟩ : syracuseStep 191927 = 287891) B287891
theorem B191963 : Blo 127788 191963 := bstep (se 1 (by rfl) ⟨143972, by rfl⟩ : syracuseStep 191963 = 287945) B287945
theorem B290267 : Blo 127788 290267 := bstep (se 1 (by rfl) ⟨217700, by rfl⟩ : syracuseStep 290267 = 435401) B435401
theorem B519929 : Blo 127788 519929 := bstep (se 2 (by rfl) ⟨194973, by rfl⟩ : syracuseStep 519929 = 389947) B389947
theorem B192431 : Blo 127788 192431 := bstep (se 1 (by rfl) ⟨144323, by rfl⟩ : syracuseStep 192431 = 288647) B288647
theorem B290735 : Blo 127788 290735 := bstep (se 1 (by rfl) ⟨218051, by rfl⟩ : syracuseStep 290735 = 436103) B436103
theorem B192521 : Blo 127788 192521 := bstep (se 2 (by rfl) ⟨72195, by rfl⟩ : syracuseStep 192521 = 144391) B144391
theorem B192551 : Blo 127788 192551 := bstep (se 1 (by rfl) ⟨144413, by rfl⟩ : syracuseStep 192551 = 288827) B288827
theorem B192635 : Blo 127788 192635 := bstep (se 1 (by rfl) ⟨144476, by rfl⟩ : syracuseStep 192635 = 288953) B288953
theorem B290987 : Blo 127788 290987 := bstep (se 1 (by rfl) ⟨218240, by rfl⟩ : syracuseStep 290987 = 436481) B436481
theorem B192761 : Blo 127788 192761 := bstep (se 2 (by rfl) ⟨72285, by rfl⟩ : syracuseStep 192761 = 144571) B144571
theorem B192863 : Blo 127788 192863 := bstep (se 1 (by rfl) ⟨144647, by rfl⟩ : syracuseStep 192863 = 289295) B289295
theorem B192875 : Blo 127788 192875 := bstep (se 1 (by rfl) ⟨144656, by rfl⟩ : syracuseStep 192875 = 289313) B289313
theorem B324121 : Blo 127788 324121 := bstep (se 2 (by rfl) ⟨121545, by rfl⟩ : syracuseStep 324121 = 243091) B243091
theorem B193103 : Blo 127788 193103 := bstep (se 1 (by rfl) ⟨144827, by rfl⟩ : syracuseStep 193103 = 289655) B289655
theorem B193223 : Blo 127788 193223 := bstep (se 1 (by rfl) ⟨144917, by rfl⟩ : syracuseStep 193223 = 289835) B289835
theorem B291527 : Blo 127788 291527 := bstep (se 1 (by rfl) ⟨218645, by rfl⟩ : syracuseStep 291527 = 437291) B437291
theorem B324425 : Blo 127788 324425 := bstep (se 2 (by rfl) ⟨121659, by rfl⟩ : syracuseStep 324425 = 243319) B243319
theorem B127823 : Blo 127788 127823 := bstep (se 1 (by rfl) ⟨95867, by rfl⟩ : syracuseStep 127823 = 191735) B191735
theorem B127839 : Blo 127788 127839 := bstep (se 1 (by rfl) ⟨95879, by rfl⟩ : syracuseStep 127839 = 191759) B191759
theorem B193385 : Blo 127788 193385 := bstep (se 2 (by rfl) ⟨72519, by rfl⟩ : syracuseStep 193385 = 145039) B145039
theorem B127867 : Blo 127788 127867 := bstep (se 1 (by rfl) ⟨95900, by rfl⟩ : syracuseStep 127867 = 191801) B191801
theorem B127919 : Blo 127788 127919 := bstep (se 1 (by rfl) ⟨95939, by rfl⟩ : syracuseStep 127919 = 191879) B191879
theorem B193463 : Blo 127788 193463 := bstep (se 1 (by rfl) ⟨145097, by rfl⟩ : syracuseStep 193463 = 290195) B290195
theorem B127943 : Blo 127788 127943 := bstep (se 1 (by rfl) ⟨95957, by rfl⟩ : syracuseStep 127943 = 191915) B191915
theorem B127963 : Blo 127788 127963 := bstep (se 1 (by rfl) ⟨95972, by rfl⟩ : syracuseStep 127963 = 191945) B191945
theorem B193499 : Blo 127788 193499 := bstep (se 1 (by rfl) ⟨145124, by rfl⟩ : syracuseStep 193499 = 290249) B290249
theorem B128039 : Blo 127788 128039 := bstep (se 1 (by rfl) ⟨96029, by rfl⟩ : syracuseStep 128039 = 192059) B192059
theorem B128079 : Blo 127788 128079 := bstep (se 1 (by rfl) ⟨96059, by rfl⟩ : syracuseStep 128079 = 192119) B192119
theorem B128095 : Blo 127788 128095 := bstep (se 1 (by rfl) ⟨96071, by rfl⟩ : syracuseStep 128095 = 192143) B192143
theorem B128123 : Blo 127788 128123 := bstep (se 1 (by rfl) ⟨96092, by rfl⟩ : syracuseStep 128123 = 192185) B192185
theorem B128175 : Blo 127788 128175 := bstep (se 1 (by rfl) ⟨96131, by rfl⟩ : syracuseStep 128175 = 192263) B192263
theorem B128199 : Blo 127788 128199 := bstep (se 1 (by rfl) ⟨96149, by rfl⟩ : syracuseStep 128199 = 192299) B192299
theorem B128219 : Blo 127788 128219 := bstep (se 1 (by rfl) ⟨96164, by rfl⟩ : syracuseStep 128219 = 192329) B192329
theorem B652535 : Blo 127788 652535 := bstep (se 1 (by rfl) ⟨489401, by rfl⟩ : syracuseStep 652535 = 978803) B978803
theorem B980261 : Blo 127788 980261 := bstep (se 4 (by rfl) ⟨91899, by rfl⟩ : syracuseStep 980261 = 183799) B183799
theorem B128295 : Blo 127788 128295 := bstep (se 1 (by rfl) ⟨96221, by rfl⟩ : syracuseStep 128295 = 192443) B192443
theorem B128335 : Blo 127788 128335 := bstep (se 1 (by rfl) ⟨96251, by rfl⟩ : syracuseStep 128335 = 192503) B192503
theorem B128351 : Blo 127788 128351 := bstep (se 1 (by rfl) ⟨96263, by rfl⟩ : syracuseStep 128351 = 192527) B192527
theorem B390505 : Blo 127788 390505 := bstep (se 2 (by rfl) ⟨146439, by rfl⟩ : syracuseStep 390505 = 292879) B292879
theorem B128379 : Blo 127788 128379 := bstep (se 1 (by rfl) ⟨96284, by rfl⟩ : syracuseStep 128379 = 192569) B192569
theorem B259471 : Blo 127788 259471 := bstep (se 1 (by rfl) ⟨194603, by rfl⟩ : syracuseStep 259471 = 389207) B389207
theorem B128431 : Blo 127788 128431 := bstep (se 1 (by rfl) ⟨96323, by rfl⟩ : syracuseStep 128431 = 192647) B192647
theorem B193967 : Blo 127788 193967 := bstep (se 1 (by rfl) ⟨145475, by rfl⟩ : syracuseStep 193967 = 290951) B290951
theorem B128455 : Blo 127788 128455 := bstep (se 1 (by rfl) ⟨96341, by rfl⟩ : syracuseStep 128455 = 192683) B192683
theorem B128475 : Blo 127788 128475 := bstep (se 1 (by rfl) ⟨96356, by rfl⟩ : syracuseStep 128475 = 192713) B192713
theorem B194057 : Blo 127788 194057 := bstep (se 2 (by rfl) ⟨72771, by rfl⟩ : syracuseStep 194057 = 145543) B145543
theorem B128551 : Blo 127788 128551 := bstep (se 1 (by rfl) ⟨96413, by rfl⟩ : syracuseStep 128551 = 192827) B192827
theorem B194087 : Blo 127788 194087 := bstep (se 1 (by rfl) ⟨145565, by rfl⟩ : syracuseStep 194087 = 291131) B291131
theorem B292391 : Blo 127788 292391 := bstep (se 1 (by rfl) ⟨219293, by rfl⟩ : syracuseStep 292391 = 438587) B438587
theorem B128591 : Blo 127788 128591 := bstep (se 1 (by rfl) ⟨96443, by rfl⟩ : syracuseStep 128591 = 192887) B192887
theorem B128607 : Blo 127788 128607 := bstep (se 1 (by rfl) ⟨96455, by rfl⟩ : syracuseStep 128607 = 192911) B192911
theorem B259681 : Blo 127788 259681 := bstep (se 2 (by rfl) ⟨97380, by rfl⟩ : syracuseStep 259681 = 194761) B194761
theorem B128635 : Blo 127788 128635 := bstep (se 1 (by rfl) ⟨96476, by rfl⟩ : syracuseStep 128635 = 192953) B192953
theorem B194171 : Blo 127788 194171 := bstep (se 1 (by rfl) ⟨145628, by rfl⟩ : syracuseStep 194171 = 291257) B291257
theorem B128687 : Blo 127788 128687 := bstep (se 1 (by rfl) ⟨96515, by rfl⟩ : syracuseStep 128687 = 193031) B193031
theorem B128711 : Blo 127788 128711 := bstep (se 1 (by rfl) ⟨96533, by rfl⟩ : syracuseStep 128711 = 193067) B193067
theorem B128731 : Blo 127788 128731 := bstep (se 1 (by rfl) ⟨96548, by rfl⟩ : syracuseStep 128731 = 193097) B193097
theorem B653021 : Blo 127788 653021 := bstep (se 3 (by rfl) ⟨122441, by rfl⟩ : syracuseStep 653021 = 244883) B244883
theorem B194297 : Blo 127788 194297 := bstep (se 2 (by rfl) ⟨72861, by rfl⟩ : syracuseStep 194297 = 145723) B145723
theorem B128807 : Blo 127788 128807 := bstep (se 1 (by rfl) ⟨96605, by rfl⟩ : syracuseStep 128807 = 193211) B193211
theorem B128847 : Blo 127788 128847 := bstep (se 1 (by rfl) ⟨96635, by rfl⟩ : syracuseStep 128847 = 193271) B193271
theorem B128863 : Blo 127788 128863 := bstep (se 1 (by rfl) ⟨96647, by rfl⟩ : syracuseStep 128863 = 193295) B193295
theorem B489311 : Blo 127788 489311 := bstep (se 1 (by rfl) ⟨366983, by rfl⟩ : syracuseStep 489311 = 733967) B733967
theorem B194399 : Blo 127788 194399 := bstep (se 1 (by rfl) ⟨145799, by rfl⟩ : syracuseStep 194399 = 291599) B291599
theorem B194411 : Blo 127788 194411 := bstep (se 1 (by rfl) ⟨145808, by rfl⟩ : syracuseStep 194411 = 291617) B291617
theorem B292715 : Blo 127788 292715 := bstep (se 1 (by rfl) ⟨219536, by rfl⟩ : syracuseStep 292715 = 439073) B439073
theorem B128891 : Blo 127788 128891 := bstep (se 1 (by rfl) ⟨96668, by rfl⟩ : syracuseStep 128891 = 193337) B193337
theorem B292769 : Blo 127788 292769 := bstep (se 2 (by rfl) ⟨109788, by rfl⟩ : syracuseStep 292769 = 219577) B219577
theorem B128943 : Blo 127788 128943 := bstep (se 1 (by rfl) ⟨96707, by rfl⟩ : syracuseStep 128943 = 193415) B193415
theorem B325559 : Blo 127788 325559 := bstep (se 1 (by rfl) ⟨244169, by rfl⟩ : syracuseStep 325559 = 488339) B488339
theorem B128967 : Blo 127788 128967 := bstep (se 1 (by rfl) ⟨96725, by rfl⟩ : syracuseStep 128967 = 193451) B193451
theorem B128987 : Blo 127788 128987 := bstep (se 1 (by rfl) ⟨96740, by rfl⟩ : syracuseStep 128987 = 193481) B193481
theorem B129063 : Blo 127788 129063 := bstep (se 1 (by rfl) ⟨96797, by rfl⟩ : syracuseStep 129063 = 193595) B193595
theorem B129103 : Blo 127788 129103 := bstep (se 1 (by rfl) ⟨96827, by rfl⟩ : syracuseStep 129103 = 193655) B193655
theorem B194639 : Blo 127788 194639 := bstep (se 1 (by rfl) ⟨145979, by rfl⟩ : syracuseStep 194639 = 291959) B291959
theorem B129119 : Blo 127788 129119 := bstep (se 1 (by rfl) ⟨96839, by rfl⟩ : syracuseStep 129119 = 193679) B193679
theorem B129147 : Blo 127788 129147 := bstep (se 1 (by rfl) ⟨96860, by rfl⟩ : syracuseStep 129147 = 193721) B193721
theorem B129199 : Blo 127788 129199 := bstep (se 1 (by rfl) ⟨96899, by rfl⟩ : syracuseStep 129199 = 193799) B193799
theorem B129223 : Blo 127788 129223 := bstep (se 1 (by rfl) ⟨96917, by rfl⟩ : syracuseStep 129223 = 193835) B193835
theorem B194759 : Blo 127788 194759 := bstep (se 1 (by rfl) ⟨146069, by rfl⟩ : syracuseStep 194759 = 292139) B292139
theorem B129243 : Blo 127788 129243 := bstep (se 1 (by rfl) ⟨96932, by rfl⟩ : syracuseStep 129243 = 193865) B193865
theorem B293111 : Blo 127788 293111 := bstep (se 1 (by rfl) ⟨219833, by rfl⟩ : syracuseStep 293111 = 439667) B439667
theorem B1407233 : Blo 127788 1407233 := bstep (se 2 (by rfl) ⟨527712, by rfl⟩ : syracuseStep 1407233 = 1055425) B1055425
theorem B129319 : Blo 127788 129319 := bstep (se 1 (by rfl) ⟨96989, by rfl⟩ : syracuseStep 129319 = 193979) B193979
theorem B522557 : Blo 127788 522557 := bstep (se 3 (by rfl) ⟨97979, by rfl⟩ : syracuseStep 522557 = 195959) B195959
theorem B129359 : Blo 127788 129359 := bstep (se 1 (by rfl) ⟨97019, by rfl⟩ : syracuseStep 129359 = 194039) B194039
theorem B129375 : Blo 127788 129375 := bstep (se 1 (by rfl) ⟨97031, by rfl⟩ : syracuseStep 129375 = 194063) B194063
theorem B194921 : Blo 127788 194921 := bstep (se 2 (by rfl) ⟨73095, by rfl⟩ : syracuseStep 194921 = 146191) B146191
theorem B129403 : Blo 127788 129403 := bstep (se 1 (by rfl) ⟨97052, by rfl⟩ : syracuseStep 129403 = 194105) B194105
theorem B129455 : Blo 127788 129455 := bstep (se 1 (by rfl) ⟨97091, by rfl⟩ : syracuseStep 129455 = 194183) B194183
theorem B194999 : Blo 127788 194999 := bstep (se 1 (by rfl) ⟨146249, by rfl⟩ : syracuseStep 194999 = 292499) B292499
theorem B129479 : Blo 127788 129479 := bstep (se 1 (by rfl) ⟨97109, by rfl⟩ : syracuseStep 129479 = 194219) B194219
theorem B129499 : Blo 127788 129499 := bstep (se 1 (by rfl) ⟨97124, by rfl⟩ : syracuseStep 129499 = 194249) B194249
theorem B195035 : Blo 127788 195035 := bstep (se 1 (by rfl) ⟨146276, by rfl⟩ : syracuseStep 195035 = 292553) B292553
theorem B490009 : Blo 127788 490009 := bstep (se 2 (by rfl) ⟨183753, by rfl⟩ : syracuseStep 490009 = 367507) B367507
theorem B129575 : Blo 127788 129575 := bstep (se 1 (by rfl) ⟨97181, by rfl⟩ : syracuseStep 129575 = 194363) B194363
theorem B129615 : Blo 127788 129615 := bstep (se 1 (by rfl) ⟨97211, by rfl⟩ : syracuseStep 129615 = 194423) B194423
theorem B129631 : Blo 127788 129631 := bstep (se 1 (by rfl) ⟨97223, by rfl⟩ : syracuseStep 129631 = 194447) B194447
theorem B359009 : Blo 127788 359009 := bstep (se 2 (by rfl) ⟨134628, by rfl⟩ : syracuseStep 359009 = 269257) B269257
theorem B129659 : Blo 127788 129659 := bstep (se 1 (by rfl) ⟨97244, by rfl⟩ : syracuseStep 129659 = 194489) B194489
theorem B129711 : Blo 127788 129711 := bstep (se 1 (by rfl) ⟨97283, by rfl⟩ : syracuseStep 129711 = 194567) B194567
theorem B129735 : Blo 127788 129735 := bstep (se 1 (by rfl) ⟨97301, by rfl⟩ : syracuseStep 129735 = 194603) B194603
theorem B129755 : Blo 127788 129755 := bstep (se 1 (by rfl) ⟨97316, by rfl⟩ : syracuseStep 129755 = 194633) B194633
theorem B129831 : Blo 127788 129831 := bstep (se 1 (by rfl) ⟨97373, by rfl⟩ : syracuseStep 129831 = 194747) B194747
theorem B490283 : Blo 127788 490283 := bstep (se 1 (by rfl) ⟨367712, by rfl⟩ : syracuseStep 490283 = 735425) B735425
theorem B490313 : Blo 127788 490313 := bstep (se 2 (by rfl) ⟨183867, by rfl⟩ : syracuseStep 490313 = 367735) B367735
theorem B293705 : Blo 127788 293705 := bstep (se 2 (by rfl) ⟨110139, by rfl⟩ : syracuseStep 293705 = 220279) B220279
theorem B129871 : Blo 127788 129871 := bstep (se 1 (by rfl) ⟨97403, by rfl⟩ : syracuseStep 129871 = 194807) B194807
theorem B129887 : Blo 127788 129887 := bstep (se 1 (by rfl) ⟨97415, by rfl⟩ : syracuseStep 129887 = 194831) B194831
theorem B129915 : Blo 127788 129915 := bstep (se 1 (by rfl) ⟨97436, by rfl⟩ : syracuseStep 129915 = 194873) B194873
theorem B129967 : Blo 127788 129967 := bstep (se 1 (by rfl) ⟨97475, by rfl⟩ : syracuseStep 129967 = 194951) B194951
theorem B195503 : Blo 127788 195503 := bstep (se 1 (by rfl) ⟨146627, by rfl⟩ : syracuseStep 195503 = 293255) B293255
theorem B129991 : Blo 127788 129991 := bstep (se 1 (by rfl) ⟨97493, by rfl⟩ : syracuseStep 129991 = 194987) B194987
theorem B130011 : Blo 127788 130011 := bstep (se 1 (by rfl) ⟨97508, by rfl⟩ : syracuseStep 130011 = 195017) B195017
theorem B326663 : Blo 127788 326663 := bstep (se 1 (by rfl) ⟨244997, by rfl⟩ : syracuseStep 326663 = 489995) B489995
theorem B195593 : Blo 127788 195593 := bstep (se 2 (by rfl) ⟨73347, by rfl⟩ : syracuseStep 195593 = 146695) B146695
theorem B130087 : Blo 127788 130087 := bstep (se 1 (by rfl) ⟨97565, by rfl⟩ : syracuseStep 130087 = 195131) B195131
theorem B195623 : Blo 127788 195623 := bstep (se 1 (by rfl) ⟨146717, by rfl⟩ : syracuseStep 195623 = 293435) B293435
theorem B326713 : Blo 127788 326713 := bstep (se 2 (by rfl) ⟨122517, by rfl⟩ : syracuseStep 326713 = 245035) B245035
theorem B130127 : Blo 127788 130127 := bstep (se 1 (by rfl) ⟨97595, by rfl⟩ : syracuseStep 130127 = 195191) B195191
theorem B130143 : Blo 127788 130143 := bstep (se 1 (by rfl) ⟨97607, by rfl⟩ : syracuseStep 130143 = 195215) B195215
theorem B130171 : Blo 127788 130171 := bstep (se 1 (by rfl) ⟨97628, by rfl⟩ : syracuseStep 130171 = 195257) B195257
theorem B195707 : Blo 127788 195707 := bstep (se 1 (by rfl) ⟨146780, by rfl⟩ : syracuseStep 195707 = 293561) B293561
theorem B588953 : Blo 127788 588953 := bstep (se 2 (by rfl) ⟨220857, by rfl⟩ : syracuseStep 588953 = 441715) B441715
theorem B130223 : Blo 127788 130223 := bstep (se 1 (by rfl) ⟨97667, by rfl⟩ : syracuseStep 130223 = 195335) B195335
theorem B130247 : Blo 127788 130247 := bstep (se 1 (by rfl) ⟨97685, by rfl⟩ : syracuseStep 130247 = 195371) B195371
theorem B130267 : Blo 127788 130267 := bstep (se 1 (by rfl) ⟨97700, by rfl⟩ : syracuseStep 130267 = 195401) B195401
theorem B195833 : Blo 127788 195833 := bstep (se 2 (by rfl) ⟨73437, by rfl⟩ : syracuseStep 195833 = 146875) B146875
theorem B130343 : Blo 127788 130343 := bstep (se 1 (by rfl) ⟨97757, by rfl⟩ : syracuseStep 130343 = 195515) B195515
theorem B130383 : Blo 127788 130383 := bstep (se 1 (by rfl) ⟨97787, by rfl⟩ : syracuseStep 130383 = 195575) B195575
theorem B130399 : Blo 127788 130399 := bstep (se 1 (by rfl) ⟨97799, by rfl⟩ : syracuseStep 130399 = 195599) B195599
theorem B195935 : Blo 127788 195935 := bstep (se 1 (by rfl) ⟨146951, by rfl⟩ : syracuseStep 195935 = 293903) B293903
theorem B327017 : Blo 127788 327017 := bstep (se 2 (by rfl) ⟨122631, by rfl⟩ : syracuseStep 327017 = 245263) B245263
theorem B195947 : Blo 127788 195947 := bstep (se 1 (by rfl) ⟨146960, by rfl⟩ : syracuseStep 195947 = 293921) B293921
theorem B130427 : Blo 127788 130427 := bstep (se 1 (by rfl) ⟨97820, by rfl⟩ : syracuseStep 130427 = 195641) B195641
theorem B130479 : Blo 127788 130479 := bstep (se 1 (by rfl) ⟨97859, by rfl⟩ : syracuseStep 130479 = 195719) B195719
theorem B130503 : Blo 127788 130503 := bstep (se 1 (by rfl) ⟨97877, by rfl⟩ : syracuseStep 130503 = 195755) B195755
theorem B163291 : Blo 127788 163291 := bstep (se 1 (by rfl) ⟨122468, by rfl⟩ : syracuseStep 163291 = 244937) B244937
theorem B130523 : Blo 127788 130523 := bstep (se 1 (by rfl) ⟨97892, by rfl⟩ : syracuseStep 130523 = 195785) B195785
theorem B130599 : Blo 127788 130599 := bstep (se 1 (by rfl) ⟨97949, by rfl⟩ : syracuseStep 130599 = 195899) B195899
theorem B130639 : Blo 127788 130639 := bstep (se 1 (by rfl) ⟨97979, by rfl⟩ : syracuseStep 130639 = 195959) B195959
theorem B196175 : Blo 127788 196175 := bstep (se 1 (by rfl) ⟨147131, by rfl⟩ : syracuseStep 196175 = 294263) B294263
theorem B130655 : Blo 127788 130655 := bstep (se 1 (by rfl) ⟨97991, by rfl⟩ : syracuseStep 130655 = 195983) B195983
theorem B294497 : Blo 127788 294497 := bstep (se 2 (by rfl) ⟨110436, by rfl⟩ : syracuseStep 294497 = 220873) B220873
theorem B130683 : Blo 127788 130683 := bstep (se 1 (by rfl) ⟨98012, by rfl⟩ : syracuseStep 130683 = 196025) B196025
theorem B1212043 : Blo 127788 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B130735 : Blo 127788 130735 := bstep (se 1 (by rfl) ⟨98051, by rfl⟩ : syracuseStep 130735 = 196103) B196103
theorem B130759 : Blo 127788 130759 := bstep (se 1 (by rfl) ⟨98069, by rfl⟩ : syracuseStep 130759 = 196139) B196139
theorem B196295 : Blo 127788 196295 := bstep (se 1 (by rfl) ⟨147221, by rfl⟩ : syracuseStep 196295 = 294443) B294443
theorem B1998553 : Blo 127788 1998553 := bstep (se 2 (by rfl) ⟨749457, by rfl⟩ : syracuseStep 1998553 = 1498915) B1498915
theorem B130779 : Blo 127788 130779 := bstep (se 1 (by rfl) ⟨98084, by rfl⟩ : syracuseStep 130779 = 196169) B196169
theorem B130855 : Blo 127788 130855 := bstep (se 1 (by rfl) ⟨98141, by rfl⟩ : syracuseStep 130855 = 196283) B196283
theorem B130895 : Blo 127788 130895 := bstep (se 1 (by rfl) ⟨98171, by rfl⟩ : syracuseStep 130895 = 196343) B196343
theorem B130911 : Blo 127788 130911 := bstep (se 1 (by rfl) ⟨98183, by rfl⟩ : syracuseStep 130911 = 196367) B196367
theorem B196457 : Blo 127788 196457 := bstep (se 2 (by rfl) ⟨73671, by rfl⟩ : syracuseStep 196457 = 147343) B147343
theorem B130939 : Blo 127788 130939 := bstep (se 1 (by rfl) ⟨98204, by rfl⟩ : syracuseStep 130939 = 196409) B196409
theorem B130991 : Blo 127788 130991 := bstep (se 1 (by rfl) ⟨98243, by rfl⟩ : syracuseStep 130991 = 196487) B196487
theorem B196535 : Blo 127788 196535 := bstep (se 1 (by rfl) ⟨147401, by rfl⟩ : syracuseStep 196535 = 294803) B294803
theorem B294839 : Blo 127788 294839 := bstep (se 1 (by rfl) ⟨221129, by rfl⟩ : syracuseStep 294839 = 442259) B442259
theorem B131015 : Blo 127788 131015 := bstep (se 1 (by rfl) ⟨98261, by rfl⟩ : syracuseStep 131015 = 196523) B196523
theorem B131035 : Blo 127788 131035 := bstep (se 1 (by rfl) ⟨98276, by rfl⟩ : syracuseStep 131035 = 196553) B196553
theorem B196571 : Blo 127788 196571 := bstep (se 1 (by rfl) ⟨147428, by rfl⟩ : syracuseStep 196571 = 294857) B294857
theorem B131359 : Blo 127788 131359 := bstep (se 1 (by rfl) ⟨98519, by rfl⟩ : syracuseStep 131359 = 197039) B197039
theorem B328009 : Blo 127788 328009 := bstep (se 2 (by rfl) ⟨123003, by rfl⟩ : syracuseStep 328009 = 246007) B246007
theorem B196955 : Blo 127788 196955 := bstep (se 1 (by rfl) ⟨147716, by rfl⟩ : syracuseStep 196955 = 295433) B295433
theorem B131419 : Blo 127788 131419 := bstep (se 1 (by rfl) ⟨98564, by rfl⟩ : syracuseStep 131419 = 197129) B197129
theorem B164207 : Blo 127788 164207 := bstep (se 1 (by rfl) ⟨123155, by rfl⟩ : syracuseStep 164207 = 246311) B246311
theorem B131439 : Blo 127788 131439 := bstep (se 1 (by rfl) ⟨98579, by rfl⟩ : syracuseStep 131439 = 197159) B197159
theorem B164263 : Blo 127788 164263 := bstep (se 1 (by rfl) ⟨123197, by rfl⟩ : syracuseStep 164263 = 246395) B246395
theorem B131495 : Blo 127788 131495 := bstep (se 1 (by rfl) ⟨98621, by rfl⟩ : syracuseStep 131495 = 197243) B197243
theorem B295343 : Blo 127788 295343 := bstep (se 1 (by rfl) ⟨221507, by rfl⟩ : syracuseStep 295343 = 443015) B443015
theorem B295379 : Blo 127788 295379 := bstep (se 1 (by rfl) ⟨221534, by rfl⟩ : syracuseStep 295379 = 443069) B443069
theorem B131579 : Blo 127788 131579 := bstep (se 1 (by rfl) ⟨98684, by rfl⟩ : syracuseStep 131579 = 197369) B197369
theorem B295487 : Blo 127788 295487 := bstep (se 1 (by rfl) ⟨221615, by rfl⟩ : syracuseStep 295487 = 443231) B443231
theorem B197183 : Blo 127788 197183 := bstep (se 1 (by rfl) ⟨147887, by rfl⟩ : syracuseStep 197183 = 295775) B295775
theorem B131647 : Blo 127788 131647 := bstep (se 1 (by rfl) ⟨98735, by rfl⟩ : syracuseStep 131647 = 197471) B197471
theorem B131655 : Blo 127788 131655 := bstep (se 1 (by rfl) ⟨98741, by rfl⟩ : syracuseStep 131655 = 197483) B197483
theorem B328313 : Blo 127788 328313 := bstep (se 2 (by rfl) ⟨123117, by rfl⟩ : syracuseStep 328313 = 246235) B246235
theorem B295595 : Blo 127788 295595 := bstep (se 1 (by rfl) ⟨221696, by rfl⟩ : syracuseStep 295595 = 443393) B443393
theorem B197303 : Blo 127788 197303 := bstep (se 1 (by rfl) ⟨147977, by rfl⟩ : syracuseStep 197303 = 295955) B295955
theorem B131807 : Blo 127788 131807 := bstep (se 1 (by rfl) ⟨98855, by rfl⟩ : syracuseStep 131807 = 197711) B197711
theorem B164587 : Blo 127788 164587 := bstep (se 1 (by rfl) ⟨123440, by rfl⟩ : syracuseStep 164587 = 246881) B246881
theorem B197531 : Blo 127788 197531 := bstep (se 1 (by rfl) ⟨148148, by rfl⟩ : syracuseStep 197531 = 296297) B296297
theorem B623705 : Blo 127788 623705 := bstep (se 2 (by rfl) ⟨233889, by rfl⟩ : syracuseStep 623705 = 467779) B467779
theorem B492743 : Blo 127788 492743 := bstep (se 1 (by rfl) ⟨369557, by rfl⟩ : syracuseStep 492743 = 739115) B739115
theorem B296135 : Blo 127788 296135 := bstep (se 1 (by rfl) ⟨222101, by rfl⟩ : syracuseStep 296135 = 444203) B444203
theorem B296315 : Blo 127788 296315 := bstep (se 1 (by rfl) ⟨222236, by rfl⟩ : syracuseStep 296315 = 444473) B444473
theorem B296441 : Blo 127788 296441 := bstep (se 2 (by rfl) ⟨111165, by rfl⟩ : syracuseStep 296441 = 222331) B222331
theorem B820793 : Blo 127788 820793 := bstep (se 2 (by rfl) ⟨307797, by rfl⟩ : syracuseStep 820793 = 615595) B615595
theorem B231007 : Blo 127788 231007 := bstep (se 1 (by rfl) ⟨173255, by rfl⟩ : syracuseStep 231007 = 346511) B346511
theorem B165559 : Blo 127788 165559 := bstep (se 1 (by rfl) ⟨124169, by rfl⟩ : syracuseStep 165559 = 248339) B248339
theorem B657233 : Blo 127788 657233 := bstep (se 2 (by rfl) ⟨246462, by rfl⟩ : syracuseStep 657233 = 492925) B492925
theorem B1410949 : Blo 127788 1410949 := bstep (se 4 (by rfl) ⟨132276, by rfl⟩ : syracuseStep 1410949 = 264553) B264553
theorem B362447 : Blo 127788 362447 := bstep (se 1 (by rfl) ⟨271835, by rfl⟩ : syracuseStep 362447 = 543671) B543671
theorem B1247183 : Blo 127788 1247183 := bstep (se 1 (by rfl) ⟨935387, by rfl⟩ : syracuseStep 1247183 = 1870775) B1870775
theorem B330095 : Blo 127788 330095 := bstep (se 1 (by rfl) ⟨247571, by rfl⟩ : syracuseStep 330095 = 495143) B495143
theorem B2230739 : Blo 127788 2230739 := bstep (se 1 (by rfl) ⟨1673054, by rfl⟩ : syracuseStep 2230739 = 3346109) B3346109
theorem B2722405 : Blo 127788 2722405 := bstep (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) B510451
theorem B658043 : Blo 127788 658043 := bstep (se 1 (by rfl) ⟨493532, by rfl⟩ : syracuseStep 658043 = 987065) B987065
theorem B4950821 : Blo 127788 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B625475 : Blo 127788 625475 := bstep (se 1 (by rfl) ⟨469106, by rfl⟩ : syracuseStep 625475 = 938213) B938213
theorem B330743 : Blo 127788 330743 := bstep (se 1 (by rfl) ⟨248057, by rfl⟩ : syracuseStep 330743 = 496115) B496115
theorem B2165825 : Blo 127788 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B625745 : Blo 127788 625745 := bstep (se 2 (by rfl) ⟨234654, by rfl⟩ : syracuseStep 625745 = 469309) B469309
theorem B330875 : Blo 127788 330875 := bstep (se 1 (by rfl) ⟨248156, by rfl⟩ : syracuseStep 330875 = 496313) B496313
theorem B560267 : Blo 127788 560267 := bstep (se 1 (by rfl) ⟨420200, by rfl⟩ : syracuseStep 560267 = 840401) B840401
theorem B560317 : Blo 127788 560317 := bstep (se 3 (by rfl) ⟨105059, by rfl⟩ : syracuseStep 560317 = 210119) B210119
theorem B1248641 : Blo 127788 1248641 := bstep (se 2 (by rfl) ⟨468240, by rfl⟩ : syracuseStep 1248641 = 936481) B936481
theorem B593351 : Blo 127788 593351 := bstep (se 1 (by rfl) ⟨445013, by rfl⟩ : syracuseStep 593351 = 890027) B890027
theorem B1674695 : Blo 127788 1674695 := bstep (se 1 (by rfl) ⟨1256021, by rfl⟩ : syracuseStep 1674695 = 2512043) B2512043
theorem B462419 : Blo 127788 462419 := bstep (se 1 (by rfl) ⟨346814, by rfl⟩ : syracuseStep 462419 = 693629) B693629
theorem B3149725 : Blo 127788 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B495827 : Blo 127788 495827 := bstep (se 1 (by rfl) ⟨371870, by rfl⟩ : syracuseStep 495827 = 743741) B743741
theorem B659987 : Blo 127788 659987 := bstep (se 1 (by rfl) ⟨494990, by rfl⟩ : syracuseStep 659987 = 989981) B989981
theorem B332471 : Blo 127788 332471 := bstep (se 1 (by rfl) ⟨249353, by rfl⟩ : syracuseStep 332471 = 498707) B498707
theorem B627551 : Blo 127788 627551 := bstep (se 1 (by rfl) ⟨470663, by rfl⟩ : syracuseStep 627551 = 941327) B941327
theorem B332687 : Blo 127788 332687 := bstep (se 1 (by rfl) ⟨249515, by rfl⟩ : syracuseStep 332687 = 499031) B499031
theorem B496631 : Blo 127788 496631 := bstep (se 1 (by rfl) ⟨372473, by rfl⟩ : syracuseStep 496631 = 744947) B744947
theorem B922873 : Blo 127788 922873 := bstep (se 2 (by rfl) ⟨346077, by rfl⟩ : syracuseStep 922873 = 692155) B692155
theorem B333193 : Blo 127788 333193 := bstep (se 2 (by rfl) ⟨124947, by rfl⟩ : syracuseStep 333193 = 249895) B249895
theorem B267769 : Blo 127788 267769 := bstep (se 2 (by rfl) ⟨100413, by rfl⟩ : syracuseStep 267769 = 200827) B200827
theorem B333305 : Blo 127788 333305 := bstep (se 2 (by rfl) ⟨124989, by rfl⟩ : syracuseStep 333305 = 249979) B249979
theorem B136927 : Blo 127788 136927 := bstep (se 1 (by rfl) ⟨102695, by rfl⟩ : syracuseStep 136927 = 205391) B205391
theorem B1251101 : Blo 127788 1251101 := bstep (se 3 (by rfl) ⟨234581, by rfl⟩ : syracuseStep 1251101 = 469163) B469163
theorem B432161 : Blo 127788 432161 := bstep (se 2 (by rfl) ⟨162060, by rfl⟩ : syracuseStep 432161 = 324121) B324121
theorem B661769 : Blo 127788 661769 := bstep (se 2 (by rfl) ⟨248163, by rfl⟩ : syracuseStep 661769 = 496327) B496327
theorem B498575 : Blo 127788 498575 := bstep (se 1 (by rfl) ⟨373931, by rfl⟩ : syracuseStep 498575 = 747863) B747863
theorem B138191 : Blo 127788 138191 := bstep (se 1 (by rfl) ⟨103643, by rfl⟩ : syracuseStep 138191 = 207287) B207287
theorem B662903 : Blo 127788 662903 := bstep (se 1 (by rfl) ⟨497177, by rfl⟩ : syracuseStep 662903 = 994355) B994355
theorem B368009 : Blo 127788 368009 := bstep (se 2 (by rfl) ⟨138003, by rfl⟩ : syracuseStep 368009 = 276007) B276007
theorem B663065 : Blo 127788 663065 := bstep (se 2 (by rfl) ⟨248649, by rfl⟩ : syracuseStep 663065 = 497299) B497299
theorem B1383961 : Blo 127788 1383961 := bstep (se 2 (by rfl) ⟨518985, by rfl⟩ : syracuseStep 1383961 = 1037971) B1037971
theorem B728635 : Blo 127788 728635 := bstep (se 1 (by rfl) ⟨546476, by rfl⟩ : syracuseStep 728635 = 1092953) B1092953
theorem B7118405 : Blo 127788 7118405 := bstep (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) B1334701
theorem B4726349 : Blo 127788 4726349 := bstep (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) B1772381
theorem B3382879 : Blo 127788 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B499517 : Blo 127788 499517 := bstep (se 3 (by rfl) ⟨93659, by rfl⟩ : syracuseStep 499517 = 187319) B187319
theorem B1351781 : Blo 127788 1351781 := bstep (se 4 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 1351781 = 253459) B253459
theorem B1056887 : Blo 127788 1056887 := bstep (se 1 (by rfl) ⟨792665, by rfl⟩ : syracuseStep 1056887 = 1585331) B1585331
theorem B467153 : Blo 127788 467153 := bstep (se 2 (by rfl) ⟨175182, by rfl⟩ : syracuseStep 467153 = 350365) B350365
theorem B336491 : Blo 127788 336491 := bstep (se 1 (by rfl) ⟨252368, by rfl⟩ : syracuseStep 336491 = 504737) B504737
theorem B139951 : Blo 127788 139951 := bstep (se 1 (by rfl) ⟨104963, by rfl⟩ : syracuseStep 139951 = 209927) B209927
theorem B435023 : Blo 127788 435023 := bstep (se 1 (by rfl) ⟨326267, by rfl⟩ : syracuseStep 435023 = 652535) B652535
theorem B1057697 : Blo 127788 1057697 := bstep (se 2 (by rfl) ⟨396636, by rfl⟩ : syracuseStep 1057697 = 793273) B793273
theorem B435347 : Blo 127788 435347 := bstep (se 1 (by rfl) ⟨326510, by rfl⟩ : syracuseStep 435347 = 653021) B653021
theorem B1123571 : Blo 127788 1123571 := bstep (se 1 (by rfl) ⟨842678, by rfl⟩ : syracuseStep 1123571 = 1685357) B1685357
theorem B435617 : Blo 127788 435617 := bstep (se 2 (by rfl) ⟨163356, by rfl⟩ : syracuseStep 435617 = 326713) B326713
theorem B239339 : Blo 127788 239339 := bstep (se 1 (by rfl) ⟨179504, by rfl⟩ : syracuseStep 239339 = 359009) B359009
theorem B1616057 : Blo 127788 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B2664737 : Blo 127788 2664737 := bstep (se 2 (by rfl) ⟨999276, by rfl⟩ : syracuseStep 2664737 = 1998553) B1998553
theorem B665981 : Blo 127788 665981 := bstep (se 3 (by rfl) ⟨124871, by rfl⟩ : syracuseStep 665981 = 249743) B249743
theorem B469567 : Blo 127788 469567 := bstep (se 1 (by rfl) ⟨352175, by rfl⟩ : syracuseStep 469567 = 704351) B704351
theorem B961303 : Blo 127788 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B1321859 : Blo 127788 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B273307 : Blo 127788 273307 := bstep (se 1 (by rfl) ⟨204980, by rfl⟩ : syracuseStep 273307 = 409961) B409961
theorem B1420253 : Blo 127788 1420253 := bstep (se 3 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 1420253 = 532595) B532595
theorem B371699 : Blo 127788 371699 := bstep (se 1 (by rfl) ⟨278774, by rfl⟩ : syracuseStep 371699 = 557549) B557549
theorem B2272967 : Blo 127788 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B438281 : Blo 127788 438281 := bstep (se 2 (by rfl) ⟨164355, by rfl⟩ : syracuseStep 438281 = 328711) B328711
theorem B274537 : Blo 127788 274537 := bstep (se 2 (by rfl) ⟨102951, by rfl⟩ : syracuseStep 274537 = 205903) B205903
theorem B176521 : Blo 127788 176521 := bstep (se 2 (by rfl) ⟨66195, by rfl⟩ : syracuseStep 176521 = 132391) B132391
theorem B143815 : Blo 127788 143815 := bstep (se 1 (by rfl) ⟨107861, by rfl⟩ : syracuseStep 143815 = 215723) B215723
theorem B438803 : Blo 127788 438803 := bstep (se 1 (by rfl) ⟨329102, by rfl⟩ : syracuseStep 438803 = 658205) B658205
theorem B340499 : Blo 127788 340499 := bstep (se 1 (by rfl) ⟨255374, by rfl⟩ : syracuseStep 340499 = 510749) B510749
theorem B701131 : Blo 127788 701131 := bstep (se 1 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 701131 = 1051697) B1051697
theorem B144175 : Blo 127788 144175 := bstep (se 1 (by rfl) ⟨108131, by rfl⟩ : syracuseStep 144175 = 216263) B216263
theorem B144283 : Blo 127788 144283 := bstep (se 1 (by rfl) ⟨108212, by rfl⟩ : syracuseStep 144283 = 216425) B216425
theorem B668915 : Blo 127788 668915 := bstep (se 1 (by rfl) ⟨501686, by rfl⟩ : syracuseStep 668915 = 1003373) B1003373
theorem B144679 : Blo 127788 144679 := bstep (se 1 (by rfl) ⟨108509, by rfl⟩ : syracuseStep 144679 = 217019) B217019
theorem B144751 : Blo 127788 144751 := bstep (se 1 (by rfl) ⟨108563, by rfl⟩ : syracuseStep 144751 = 217127) B217127
theorem B144967 : Blo 127788 144967 := bstep (se 1 (by rfl) ⟨108725, by rfl⟩ : syracuseStep 144967 = 217451) B217451
theorem B177839 : Blo 127788 177839 := bstep (se 1 (by rfl) ⟨133379, by rfl⟩ : syracuseStep 177839 = 266759) B266759
theorem B440585 : Blo 127788 440585 := bstep (se 2 (by rfl) ⟨165219, by rfl⟩ : syracuseStep 440585 = 330439) B330439
theorem B375151 : Blo 127788 375151 := bstep (se 1 (by rfl) ⟨281363, by rfl⟩ : syracuseStep 375151 = 562727) B562727
theorem B997757 : Blo 127788 997757 := bstep (se 3 (by rfl) ⟨187079, by rfl⟩ : syracuseStep 997757 = 374159) B374159
theorem B145831 : Blo 127788 145831 := bstep (se 1 (by rfl) ⟨109373, by rfl⟩ : syracuseStep 145831 = 218747) B218747
theorem B703403 : Blo 127788 703403 := bstep (se 1 (by rfl) ⟨527552, by rfl⟩ : syracuseStep 703403 = 1055105) B1055105
theorem B146407 : Blo 127788 146407 := bstep (se 1 (by rfl) ⟨109805, by rfl⟩ : syracuseStep 146407 = 219611) B219611
theorem B441719 : Blo 127788 441719 := bstep (se 1 (by rfl) ⟨331289, by rfl⟩ : syracuseStep 441719 = 662579) B662579
theorem B2866747 : Blo 127788 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B736883 : Blo 127788 736883 := bstep (se 1 (by rfl) ⟨552662, by rfl⟩ : syracuseStep 736883 = 1105325) B1105325
theorem B442169 : Blo 127788 442169 := bstep (se 2 (by rfl) ⟨165813, by rfl⟩ : syracuseStep 442169 = 331627) B331627
theorem B1196039 : Blo 127788 1196039 := bstep (se 1 (by rfl) ⟨897029, by rfl⟩ : syracuseStep 1196039 = 1794059) B1794059
theorem B2211851 : Blo 127788 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B278633 : Blo 127788 278633 := bstep (se 2 (by rfl) ⟨104487, by rfl⟩ : syracuseStep 278633 = 208975) B208975
theorem B442799 : Blo 127788 442799 := bstep (se 1 (by rfl) ⟨332099, by rfl⟩ : syracuseStep 442799 = 664199) B664199
theorem B803297 : Blo 127788 803297 := bstep (se 2 (by rfl) ⟨301236, by rfl⟩ : syracuseStep 803297 = 602473) B602473
theorem B148063 : Blo 127788 148063 := bstep (se 1 (by rfl) ⟨111047, by rfl⟩ : syracuseStep 148063 = 222095) B222095
theorem B377465 : Blo 127788 377465 := bstep (se 2 (by rfl) ⟨141549, by rfl⟩ : syracuseStep 377465 = 283099) B283099
theorem B738341 : Blo 127788 738341 := bstep (se 4 (by rfl) ⟨69219, by rfl⟩ : syracuseStep 738341 = 138439) B138439
theorem B672857 : Blo 127788 672857 := bstep (se 2 (by rfl) ⟨252321, by rfl⟩ : syracuseStep 672857 = 504643) B504643
theorem B148775 : Blo 127788 148775 := bstep (se 1 (by rfl) ⟨111581, by rfl⟩ : syracuseStep 148775 = 223163) B223163
theorem B443771 : Blo 127788 443771 := bstep (se 1 (by rfl) ⟨332828, by rfl⟩ : syracuseStep 443771 = 665657) B665657
theorem B378425 : Blo 127788 378425 := bstep (se 2 (by rfl) ⟨141909, by rfl⟩ : syracuseStep 378425 = 283819) B283819
theorem B411293 : Blo 127788 411293 := bstep (se 3 (by rfl) ⟨77117, by rfl⟩ : syracuseStep 411293 = 154235) B154235
theorem B247609 : Blo 127788 247609 := bstep (se 2 (by rfl) ⟨92853, by rfl⟩ : syracuseStep 247609 = 185707) B185707
theorem B345961 : Blo 127788 345961 := bstep (se 2 (by rfl) ⟨129735, by rfl⟩ : syracuseStep 345961 = 259471) B259471
theorem B346241 : Blo 127788 346241 := bstep (se 2 (by rfl) ⟨129840, by rfl⟩ : syracuseStep 346241 = 259681) B259681
theorem B346619 : Blo 127788 346619 := bstep (se 1 (by rfl) ⟨259964, by rfl⟩ : syracuseStep 346619 = 519929) B519929
theorem B3328613 : Blo 127788 3328613 := bstep (se 4 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 3328613 = 624115) B624115
theorem B216283 : Blo 127788 216283 := bstep (se 1 (by rfl) ⟨162212, by rfl⟩ : syracuseStep 216283 = 324425) B324425
theorem B183583 : Blo 127788 183583 := bstep (se 1 (by rfl) ⟨137687, by rfl⟩ : syracuseStep 183583 = 275375) B275375
theorem B217039 : Blo 127788 217039 := bstep (se 1 (by rfl) ⟨162779, by rfl⟩ : syracuseStep 217039 = 325559) B325559
theorem B1232921 : Blo 127788 1232921 := bstep (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) B924691
theorem B938155 : Blo 127788 938155 := bstep (se 1 (by rfl) ⟨703616, by rfl⟩ : syracuseStep 938155 = 1407233) B1407233
theorem B348371 : Blo 127788 348371 := bstep (se 1 (by rfl) ⟨261278, by rfl⟩ : syracuseStep 348371 = 522557) B522557
theorem B938557 : Blo 127788 938557 := bstep (se 3 (by rfl) ⟨175979, by rfl⟩ : syracuseStep 938557 = 351959) B351959
theorem B217721 : Blo 127788 217721 := bstep (se 2 (by rfl) ⟨81645, by rfl⟩ : syracuseStep 217721 = 163291) B163291
theorem B217775 : Blo 127788 217775 := bstep (se 1 (by rfl) ⟨163331, by rfl⟩ : syracuseStep 217775 = 326663) B326663
theorem B840527 : Blo 127788 840527 := bstep (se 1 (by rfl) ⟨630395, by rfl⟩ : syracuseStep 840527 = 1260791) B1260791
theorem B218011 : Blo 127788 218011 := bstep (se 1 (by rfl) ⟨163508, by rfl⟩ : syracuseStep 218011 = 327017) B327017
theorem B414665 : Blo 127788 414665 := bstep (se 2 (by rfl) ⟨155499, by rfl⟩ : syracuseStep 414665 = 310999) B310999
theorem B1103341 : Blo 127788 1103341 := bstep (se 3 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 1103341 = 413753) B413753
theorem B350057 : Blo 127788 350057 := bstep (se 2 (by rfl) ⟨131271, by rfl⟩ : syracuseStep 350057 = 262543) B262543
theorem B416009 : Blo 127788 416009 := bstep (se 2 (by rfl) ⟨156003, by rfl⟩ : syracuseStep 416009 = 312007) B312007
theorem B350489 : Blo 127788 350489 := bstep (se 2 (by rfl) ⟨131433, by rfl⟩ : syracuseStep 350489 = 262867) B262867
theorem B186715 : Blo 127788 186715 := bstep (se 1 (by rfl) ⟨140036, by rfl⟩ : syracuseStep 186715 = 280073) B280073
theorem B219503 : Blo 127788 219503 := bstep (se 1 (by rfl) ⟨164627, by rfl⟩ : syracuseStep 219503 = 329255) B329255
theorem B186943 : Blo 127788 186943 := bstep (se 1 (by rfl) ⟨140207, by rfl⟩ : syracuseStep 186943 = 280415) B280415
theorem B219719 : Blo 127788 219719 := bstep (se 1 (by rfl) ⟨164789, by rfl⟩ : syracuseStep 219719 = 329579) B329579
theorem B154423 : Blo 127788 154423 := bstep (se 1 (by rfl) ⟨115817, by rfl⟩ : syracuseStep 154423 = 231635) B231635
theorem B220151 : Blo 127788 220151 := bstep (se 1 (by rfl) ⟨165113, by rfl⟩ : syracuseStep 220151 = 330227) B330227
theorem B351371 : Blo 127788 351371 := bstep (se 1 (by rfl) ⟨263528, by rfl⟩ : syracuseStep 351371 = 527057) B527057
theorem B417239 : Blo 127788 417239 := bstep (se 1 (by rfl) ⟨312929, by rfl⟩ : syracuseStep 417239 = 625859) B625859
theorem B220907 : Blo 127788 220907 := bstep (se 1 (by rfl) ⟨165680, by rfl⟩ : syracuseStep 220907 = 331361) B331361
theorem B2777611 : Blo 127788 2777611 := bstep (se 1 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 2777611 = 4166417) B4166417
theorem B221767 : Blo 127788 221767 := bstep (se 1 (by rfl) ⟨166325, by rfl⟩ : syracuseStep 221767 = 332651) B332651
theorem B1499795 : Blo 127788 1499795 := bstep (se 1 (by rfl) ⟨1124846, by rfl⟩ : syracuseStep 1499795 = 2249693) B2249693
theorem B746131 : Blo 127788 746131 := bstep (se 1 (by rfl) ⟨559598, by rfl⟩ : syracuseStep 746131 = 1119197) B1119197
theorem B221879 : Blo 127788 221879 := bstep (se 1 (by rfl) ⟨166409, by rfl⟩ : syracuseStep 221879 = 332819) B332819
theorem B287567 : Blo 127788 287567 := bstep (se 1 (by rfl) ⟨215675, by rfl⟩ : syracuseStep 287567 = 431351) B431351
theorem B549827 : Blo 127788 549827 := bstep (se 1 (by rfl) ⟨412370, by rfl⟩ : syracuseStep 549827 = 824741) B824741
theorem B287783 : Blo 127788 287783 := bstep (se 1 (by rfl) ⟨215837, by rfl⟩ : syracuseStep 287783 = 431675) B431675
theorem B12248113 : Blo 127788 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B287963 : Blo 127788 287963 := bstep (se 1 (by rfl) ⟨215972, by rfl⟩ : syracuseStep 287963 = 431945) B431945
theorem B288161 : Blo 127788 288161 := bstep (se 2 (by rfl) ⟨108060, by rfl⟩ : syracuseStep 288161 = 216121) B216121
theorem B288719 : Blo 127788 288719 := bstep (se 1 (by rfl) ⟨216539, by rfl⟩ : syracuseStep 288719 = 433079) B433079
theorem B649295 : Blo 127788 649295 := bstep (se 1 (by rfl) ⟨486971, by rfl⟩ : syracuseStep 649295 = 973943) B973943
theorem B289097 : Blo 127788 289097 := bstep (se 2 (by rfl) ⟨108411, by rfl⟩ : syracuseStep 289097 = 216823) B216823
theorem B289115 : Blo 127788 289115 := bstep (se 1 (by rfl) ⟨216836, by rfl⟩ : syracuseStep 289115 = 433673) B433673
theorem B1141121 : Blo 127788 1141121 := bstep (se 2 (by rfl) ⟨427920, by rfl⟩ : syracuseStep 1141121 = 855841) B855841
theorem B223655 : Blo 127788 223655 := bstep (se 1 (by rfl) ⟨167741, by rfl⟩ : syracuseStep 223655 = 335483) B335483
theorem B354727 : Blo 127788 354727 := bstep (se 1 (by rfl) ⟨266045, by rfl⟩ : syracuseStep 354727 = 532091) B532091
theorem B1108669 : Blo 127788 1108669 := bstep (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) B415751
theorem B289691 : Blo 127788 289691 := bstep (se 1 (by rfl) ⟨217268, by rfl⟩ : syracuseStep 289691 = 434537) B434537
theorem B289889 : Blo 127788 289889 := bstep (se 2 (by rfl) ⟨108708, by rfl⟩ : syracuseStep 289889 = 217417) B217417
theorem B650429 : Blo 127788 650429 := bstep (se 3 (by rfl) ⟨121955, by rfl⟩ : syracuseStep 650429 = 243911) B243911
theorem B552203 : Blo 127788 552203 := bstep (se 1 (by rfl) ⟨414152, by rfl⟩ : syracuseStep 552203 = 828305) B828305
theorem B191783 : Blo 127788 191783 := bstep (se 1 (by rfl) ⟨143837, by rfl⟩ : syracuseStep 191783 = 287675) B287675
theorem B290087 : Blo 127788 290087 := bstep (se 1 (by rfl) ⟨217565, by rfl⟩ : syracuseStep 290087 = 435131) B435131
theorem B191867 : Blo 127788 191867 := bstep (se 1 (by rfl) ⟨143900, by rfl⟩ : syracuseStep 191867 = 287801) B287801
theorem B224635 : Blo 127788 224635 := bstep (se 1 (by rfl) ⟨168476, by rfl⟩ : syracuseStep 224635 = 336953) B336953
theorem B191993 : Blo 127788 191993 := bstep (se 2 (by rfl) ⟨71997, by rfl⟩ : syracuseStep 191993 = 143995) B143995
theorem B192095 : Blo 127788 192095 := bstep (se 1 (by rfl) ⟨144071, by rfl⟩ : syracuseStep 192095 = 288143) B288143
theorem B290465 : Blo 127788 290465 := bstep (se 2 (by rfl) ⟨108924, by rfl⟩ : syracuseStep 290465 = 217849) B217849
theorem B192311 : Blo 127788 192311 := bstep (se 1 (by rfl) ⟨144233, by rfl⟩ : syracuseStep 192311 = 288467) B288467
theorem B290825 : Blo 127788 290825 := bstep (se 2 (by rfl) ⟨109059, by rfl⟩ : syracuseStep 290825 = 218119) B218119
theorem B192617 : Blo 127788 192617 := bstep (se 2 (by rfl) ⟨72231, by rfl⟩ : syracuseStep 192617 = 144463) B144463
theorem B192935 : Blo 127788 192935 := bstep (se 1 (by rfl) ⟨144701, by rfl⟩ : syracuseStep 192935 = 289403) B289403
theorem B291239 : Blo 127788 291239 := bstep (se 1 (by rfl) ⟨218429, by rfl⟩ : syracuseStep 291239 = 436859) B436859
theorem B520673 : Blo 127788 520673 := bstep (se 2 (by rfl) ⟨195252, by rfl⟩ : syracuseStep 520673 = 390505) B390505
theorem B193019 : Blo 127788 193019 := bstep (se 1 (by rfl) ⟨144764, by rfl⟩ : syracuseStep 193019 = 289529) B289529
theorem B291347 : Blo 127788 291347 := bstep (se 1 (by rfl) ⟨218510, by rfl⟩ : syracuseStep 291347 = 437021) B437021
theorem B291401 : Blo 127788 291401 := bstep (se 2 (by rfl) ⟨109275, by rfl⟩ : syracuseStep 291401 = 218551) B218551
theorem B193145 : Blo 127788 193145 := bstep (se 2 (by rfl) ⟨72429, by rfl⟩ : syracuseStep 193145 = 144859) B144859
theorem B193199 : Blo 127788 193199 := bstep (se 1 (by rfl) ⟨144899, by rfl⟩ : syracuseStep 193199 = 289799) B289799
theorem B193247 : Blo 127788 193247 := bstep (se 1 (by rfl) ⟨144935, by rfl⟩ : syracuseStep 193247 = 289871) B289871
theorem B127791 : Blo 127788 127791 := bstep (se 1 (by rfl) ⟨95843, by rfl⟩ : syracuseStep 127791 = 191687) B191687
theorem B127899 : Blo 127788 127899 := bstep (se 1 (by rfl) ⟨95924, by rfl⟩ : syracuseStep 127899 = 191849) B191849
theorem B127951 : Blo 127788 127951 := bstep (se 1 (by rfl) ⟨95963, by rfl⟩ : syracuseStep 127951 = 191927) B191927
theorem B947153 : Blo 127788 947153 := bstep (se 2 (by rfl) ⟨355182, by rfl⟩ : syracuseStep 947153 = 710365) B710365
theorem B127975 : Blo 127788 127975 := bstep (se 1 (by rfl) ⟨95981, by rfl⟩ : syracuseStep 127975 = 191963) B191963
theorem B193511 : Blo 127788 193511 := bstep (se 1 (by rfl) ⟨145133, by rfl⟩ : syracuseStep 193511 = 290267) B290267
theorem B291815 : Blo 127788 291815 := bstep (se 1 (by rfl) ⟨218861, by rfl⟩ : syracuseStep 291815 = 437723) B437723
theorem B554131 : Blo 127788 554131 := bstep (se 1 (by rfl) ⟨415598, by rfl⟩ : syracuseStep 554131 = 831197) B831197
theorem B193769 : Blo 127788 193769 := bstep (se 2 (by rfl) ⟨72663, by rfl⟩ : syracuseStep 193769 = 145327) B145327
theorem B128287 : Blo 127788 128287 := bstep (se 1 (by rfl) ⟨96215, by rfl⟩ : syracuseStep 128287 = 192431) B192431
theorem B193823 : Blo 127788 193823 := bstep (se 1 (by rfl) ⟨145367, by rfl⟩ : syracuseStep 193823 = 290735) B290735
theorem B128347 : Blo 127788 128347 := bstep (se 1 (by rfl) ⟨96260, by rfl⟩ : syracuseStep 128347 = 192521) B192521
theorem B292193 : Blo 127788 292193 := bstep (se 2 (by rfl) ⟨109572, by rfl⟩ : syracuseStep 292193 = 219145) B219145
theorem B521581 : Blo 127788 521581 := bstep (se 3 (by rfl) ⟨97796, by rfl⟩ : syracuseStep 521581 = 195593) B195593
theorem B128367 : Blo 127788 128367 := bstep (se 1 (by rfl) ⟨96275, by rfl⟩ : syracuseStep 128367 = 192551) B192551
theorem B128423 : Blo 127788 128423 := bstep (se 1 (by rfl) ⟨96317, by rfl⟩ : syracuseStep 128423 = 192635) B192635
theorem B292283 : Blo 127788 292283 := bstep (se 1 (by rfl) ⟨219212, by rfl⟩ : syracuseStep 292283 = 438425) B438425
theorem B292295 : Blo 127788 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B193991 : Blo 127788 193991 := bstep (se 1 (by rfl) ⟨145493, by rfl⟩ : syracuseStep 193991 = 290987) B290987
theorem B128507 : Blo 127788 128507 := bstep (se 1 (by rfl) ⟨96380, by rfl⟩ : syracuseStep 128507 = 192761) B192761
theorem B751141 : Blo 127788 751141 := bstep (se 4 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 751141 = 140839) B140839
theorem B292409 : Blo 127788 292409 := bstep (se 2 (by rfl) ⟨109653, by rfl⟩ : syracuseStep 292409 = 219307) B219307
theorem B128575 : Blo 127788 128575 := bstep (se 1 (by rfl) ⟨96431, by rfl⟩ : syracuseStep 128575 = 192863) B192863
theorem B128583 : Blo 127788 128583 := bstep (se 1 (by rfl) ⟨96437, by rfl⟩ : syracuseStep 128583 = 192875) B192875
theorem B128735 : Blo 127788 128735 := bstep (se 1 (by rfl) ⟨96551, by rfl⟩ : syracuseStep 128735 = 193103) B193103
theorem B325417 : Blo 127788 325417 := bstep (se 2 (by rfl) ⟨122031, by rfl⟩ : syracuseStep 325417 = 244063) B244063
theorem B194345 : Blo 127788 194345 := bstep (se 2 (by rfl) ⟨72879, by rfl⟩ : syracuseStep 194345 = 145759) B145759
theorem B128815 : Blo 127788 128815 := bstep (se 1 (by rfl) ⟨96611, by rfl⟩ : syracuseStep 128815 = 193223) B193223
theorem B194351 : Blo 127788 194351 := bstep (se 1 (by rfl) ⟨145763, by rfl⟩ : syracuseStep 194351 = 291527) B291527
theorem B128923 : Blo 127788 128923 := bstep (se 1 (by rfl) ⟨96692, by rfl⟩ : syracuseStep 128923 = 193385) B193385
theorem B128975 : Blo 127788 128975 := bstep (se 1 (by rfl) ⟨96731, by rfl⟩ : syracuseStep 128975 = 193463) B193463
theorem B161767 : Blo 127788 161767 := bstep (se 1 (by rfl) ⟨121325, by rfl⟩ : syracuseStep 161767 = 242651) B242651
theorem B128999 : Blo 127788 128999 := bstep (se 1 (by rfl) ⟨96749, by rfl⟩ : syracuseStep 128999 = 193499) B193499
theorem B653345 : Blo 127788 653345 := bstep (se 2 (by rfl) ⟨245004, by rfl⟩ : syracuseStep 653345 = 490009) B490009
theorem B653507 : Blo 127788 653507 := bstep (se 1 (by rfl) ⟨490130, by rfl⟩ : syracuseStep 653507 = 980261) B980261
theorem B293075 : Blo 127788 293075 := bstep (se 1 (by rfl) ⟨219806, by rfl⟩ : syracuseStep 293075 = 439613) B439613
theorem B194825 : Blo 127788 194825 := bstep (se 2 (by rfl) ⟨73059, by rfl⟩ : syracuseStep 194825 = 146119) B146119
theorem B293129 : Blo 127788 293129 := bstep (se 2 (by rfl) ⟨109923, by rfl⟩ : syracuseStep 293129 = 219847) B219847
theorem B129311 : Blo 127788 129311 := bstep (se 1 (by rfl) ⟨96983, by rfl⟩ : syracuseStep 129311 = 193967) B193967
theorem B129371 : Blo 127788 129371 := bstep (se 1 (by rfl) ⟨97028, by rfl⟩ : syracuseStep 129371 = 194057) B194057
theorem B129391 : Blo 127788 129391 := bstep (se 1 (by rfl) ⟨97043, by rfl⟩ : syracuseStep 129391 = 194087) B194087
theorem B194927 : Blo 127788 194927 := bstep (se 1 (by rfl) ⟨146195, by rfl⟩ : syracuseStep 194927 = 292391) B292391
theorem B129447 : Blo 127788 129447 := bstep (se 1 (by rfl) ⟨97085, by rfl⟩ : syracuseStep 129447 = 194171) B194171
theorem B293345 : Blo 127788 293345 := bstep (se 2 (by rfl) ⟨110004, by rfl⟩ : syracuseStep 293345 = 220009) B220009
theorem B129531 : Blo 127788 129531 := bstep (se 1 (by rfl) ⟨97148, by rfl⟩ : syracuseStep 129531 = 194297) B194297
theorem B326207 : Blo 127788 326207 := bstep (se 1 (by rfl) ⟨244655, by rfl⟩ : syracuseStep 326207 = 489311) B489311
theorem B129599 : Blo 127788 129599 := bstep (se 1 (by rfl) ⟨97199, by rfl⟩ : syracuseStep 129599 = 194399) B194399
theorem B129607 : Blo 127788 129607 := bstep (se 1 (by rfl) ⟨97205, by rfl⟩ : syracuseStep 129607 = 194411) B194411
theorem B195143 : Blo 127788 195143 := bstep (se 1 (by rfl) ⟨146357, by rfl⟩ : syracuseStep 195143 = 292715) B292715
theorem B195179 : Blo 127788 195179 := bstep (se 1 (by rfl) ⟨146384, by rfl⟩ : syracuseStep 195179 = 292769) B292769
theorem B621245 : Blo 127788 621245 := bstep (se 3 (by rfl) ⟨116483, by rfl⟩ : syracuseStep 621245 = 232967) B232967
theorem B129759 : Blo 127788 129759 := bstep (se 1 (by rfl) ⟨97319, by rfl⟩ : syracuseStep 129759 = 194639) B194639
theorem B293651 : Blo 127788 293651 := bstep (se 1 (by rfl) ⟨220238, by rfl⟩ : syracuseStep 293651 = 440477) B440477
theorem B129839 : Blo 127788 129839 := bstep (se 1 (by rfl) ⟨97379, by rfl⟩ : syracuseStep 129839 = 194759) B194759
theorem B195407 : Blo 127788 195407 := bstep (se 1 (by rfl) ⟨146555, by rfl⟩ : syracuseStep 195407 = 293111) B293111
theorem B1145707 : Blo 127788 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B129947 : Blo 127788 129947 := bstep (se 1 (by rfl) ⟨97460, by rfl⟩ : syracuseStep 129947 = 194921) B194921
theorem B129999 : Blo 127788 129999 := bstep (se 1 (by rfl) ⟨97499, by rfl⟩ : syracuseStep 129999 = 194999) B194999
theorem B130023 : Blo 127788 130023 := bstep (se 1 (by rfl) ⟨97517, by rfl⟩ : syracuseStep 130023 = 195035) B195035
theorem B294011 : Blo 127788 294011 := bstep (se 1 (by rfl) ⟨220508, by rfl⟩ : syracuseStep 294011 = 441017) B441017
theorem B982205 : Blo 127788 982205 := bstep (se 3 (by rfl) ⟨184163, by rfl⟩ : syracuseStep 982205 = 368327) B368327
theorem B326855 : Blo 127788 326855 := bstep (se 1 (by rfl) ⟨245141, by rfl⟩ : syracuseStep 326855 = 490283) B490283
theorem B326875 : Blo 127788 326875 := bstep (se 1 (by rfl) ⟨245156, by rfl⟩ : syracuseStep 326875 = 490313) B490313
theorem B195803 : Blo 127788 195803 := bstep (se 1 (by rfl) ⟨146852, by rfl⟩ : syracuseStep 195803 = 293705) B293705
theorem B294121 : Blo 127788 294121 := bstep (se 2 (by rfl) ⟨110295, by rfl⟩ : syracuseStep 294121 = 220591) B220591
theorem B294137 : Blo 127788 294137 := bstep (se 2 (by rfl) ⟨110301, by rfl⟩ : syracuseStep 294137 = 220603) B220603
theorem B130335 : Blo 127788 130335 := bstep (se 1 (by rfl) ⟨97751, by rfl⟩ : syracuseStep 130335 = 195503) B195503
theorem B130395 : Blo 127788 130395 := bstep (se 1 (by rfl) ⟨97796, by rfl⟩ : syracuseStep 130395 = 195593) B195593
theorem B130415 : Blo 127788 130415 := bstep (se 1 (by rfl) ⟨97811, by rfl⟩ : syracuseStep 130415 = 195623) B195623
theorem B195977 : Blo 127788 195977 := bstep (se 2 (by rfl) ⟨73491, by rfl⟩ : syracuseStep 195977 = 146983) B146983
theorem B294281 : Blo 127788 294281 := bstep (se 2 (by rfl) ⟨110355, by rfl⟩ : syracuseStep 294281 = 220711) B220711
theorem B130471 : Blo 127788 130471 := bstep (se 1 (by rfl) ⟨97853, by rfl⟩ : syracuseStep 130471 = 195707) B195707
theorem B392635 : Blo 127788 392635 := bstep (se 1 (by rfl) ⟨294476, by rfl⟩ : syracuseStep 392635 = 588953) B588953
theorem B490967 : Blo 127788 490967 := bstep (se 1 (by rfl) ⟨368225, by rfl⟩ : syracuseStep 490967 = 736451) B736451
theorem B130555 : Blo 127788 130555 := bstep (se 1 (by rfl) ⟨97916, by rfl⟩ : syracuseStep 130555 = 195833) B195833
theorem B294407 : Blo 127788 294407 := bstep (se 1 (by rfl) ⟨220805, by rfl⟩ : syracuseStep 294407 = 441611) B441611
theorem B130623 : Blo 127788 130623 := bstep (se 1 (by rfl) ⟨97967, by rfl⟩ : syracuseStep 130623 = 195935) B195935
theorem B130631 : Blo 127788 130631 := bstep (se 1 (by rfl) ⟨97973, by rfl⟩ : syracuseStep 130631 = 195947) B195947
theorem B294587 : Blo 127788 294587 := bstep (se 1 (by rfl) ⟨220940, by rfl⟩ : syracuseStep 294587 = 441881) B441881
theorem B130783 : Blo 127788 130783 := bstep (se 1 (by rfl) ⟨98087, by rfl⟩ : syracuseStep 130783 = 196175) B196175
theorem B196331 : Blo 127788 196331 := bstep (se 1 (by rfl) ⟨147248, by rfl⟩ : syracuseStep 196331 = 294497) B294497
theorem B130863 : Blo 127788 130863 := bstep (se 1 (by rfl) ⟨98147, by rfl⟩ : syracuseStep 130863 = 196295) B196295
theorem B425785 : Blo 127788 425785 := bstep (se 2 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 425785 = 319339) B319339
theorem B294713 : Blo 127788 294713 := bstep (se 2 (by rfl) ⟨110517, by rfl⟩ : syracuseStep 294713 = 221035) B221035
theorem B130971 : Blo 127788 130971 := bstep (se 1 (by rfl) ⟨98228, by rfl⟩ : syracuseStep 130971 = 196457) B196457
theorem B1638305 : Blo 127788 1638305 := bstep (se 2 (by rfl) ⟨614364, by rfl⟩ : syracuseStep 1638305 = 1228729) B1228729
theorem B131023 : Blo 127788 131023 := bstep (se 1 (by rfl) ⟨98267, by rfl⟩ : syracuseStep 131023 = 196535) B196535
theorem B196559 : Blo 127788 196559 := bstep (se 1 (by rfl) ⟨147419, by rfl⟩ : syracuseStep 196559 = 294839) B294839
theorem B131047 : Blo 127788 131047 := bstep (se 1 (by rfl) ⟨98285, by rfl⟩ : syracuseStep 131047 = 196571) B196571
theorem B5898269 : Blo 127788 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B131303 : Blo 127788 131303 := bstep (se 1 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 131303 = 196955) B196955
theorem B295199 : Blo 127788 295199 := bstep (se 1 (by rfl) ⟨221399, by rfl⟩ : syracuseStep 295199 = 442799) B442799
theorem B196895 : Blo 127788 196895 := bstep (se 1 (by rfl) ⟨147671, by rfl⟩ : syracuseStep 196895 = 295343) B295343
theorem B196919 : Blo 127788 196919 := bstep (se 1 (by rfl) ⟨147689, by rfl⟩ : syracuseStep 196919 = 295379) B295379
theorem B196991 : Blo 127788 196991 := bstep (se 1 (by rfl) ⟨147743, by rfl⟩ : syracuseStep 196991 = 295487) B295487
theorem B131455 : Blo 127788 131455 := bstep (se 1 (by rfl) ⟨98591, by rfl⟩ : syracuseStep 131455 = 197183) B197183
theorem B197063 : Blo 127788 197063 := bstep (se 1 (by rfl) ⟨147797, by rfl⟩ : syracuseStep 197063 = 295595) B295595
theorem B131535 : Blo 127788 131535 := bstep (se 1 (by rfl) ⟨98651, by rfl⟩ : syracuseStep 131535 = 197303) B197303
theorem B131687 : Blo 127788 131687 := bstep (se 1 (by rfl) ⟨98765, by rfl⟩ : syracuseStep 131687 = 197531) B197531
theorem B3703481 : Blo 127788 3703481 := bstep (se 2 (by rfl) ⟨1388805, by rfl⟩ : syracuseStep 3703481 = 2777611) B2777611
theorem B492227 : Blo 127788 492227 := bstep (se 1 (by rfl) ⟨369170, by rfl⟩ : syracuseStep 492227 = 738341) B738341
theorem B197417 : Blo 127788 197417 := bstep (se 2 (by rfl) ⟨74031, by rfl⟩ : syracuseStep 197417 = 148063) B148063
theorem B328495 : Blo 127788 328495 := bstep (se 1 (by rfl) ⟨246371, by rfl⟩ : syracuseStep 328495 = 492743) B492743
theorem B197423 : Blo 127788 197423 := bstep (se 1 (by rfl) ⟨148067, by rfl⟩ : syracuseStep 197423 = 296135) B296135
theorem B295847 : Blo 127788 295847 := bstep (se 1 (by rfl) ⟨221885, by rfl⟩ : syracuseStep 295847 = 443771) B443771
theorem B197543 : Blo 127788 197543 := bstep (se 1 (by rfl) ⟨148157, by rfl⟩ : syracuseStep 197543 = 296315) B296315
theorem B197627 : Blo 127788 197627 := bstep (se 1 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 197627 = 296441) B296441
theorem B395567 : Blo 127788 395567 := bstep (se 1 (by rfl) ⟨296675, by rfl⟩ : syracuseStep 395567 = 593351) B593351
theorem B1116463 : Blo 127788 1116463 := bstep (se 1 (by rfl) ⟨837347, by rfl⟩ : syracuseStep 1116463 = 1674695) B1674695
theorem B821947 : Blo 127788 821947 := bstep (se 1 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 821947 = 1232921) B1232921
theorem B232247 : Blo 127788 232247 := bstep (se 1 (by rfl) ⟨174185, by rfl⟩ : syracuseStep 232247 = 348371) B348371
theorem B330551 : Blo 127788 330551 := bstep (se 1 (by rfl) ⟨247913, by rfl⟩ : syracuseStep 330551 = 495827) B495827
theorem B1182757 : Blo 127788 1182757 := bstep (se 4 (by rfl) ⟨110883, by rfl⟩ : syracuseStep 1182757 = 221767) B221767
theorem B560351 : Blo 127788 560351 := bstep (se 1 (by rfl) ⟨420263, by rfl⟩ : syracuseStep 560351 = 840527) B840527
theorem B331087 : Blo 127788 331087 := bstep (se 1 (by rfl) ⟨248315, by rfl⟩ : syracuseStep 331087 = 496631) B496631
theorem B396733 : Blo 127788 396733 := bstep (se 3 (by rfl) ⟨74387, by rfl⟩ : syracuseStep 396733 = 148775) B148775
theorem B1478225 : Blo 127788 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B2100853 : Blo 127788 2100853 := bstep (se 5 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 2100853 = 196955) B196955
theorem B1281737 : Blo 127788 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B364409 : Blo 127788 364409 := bstep (se 2 (by rfl) ⟨136653, by rfl⟩ : syracuseStep 364409 = 273307) B273307
theorem B233371 : Blo 127788 233371 := bstep (se 1 (by rfl) ⟨175028, by rfl⟩ : syracuseStep 233371 = 350057) B350057
theorem B233659 : Blo 127788 233659 := bstep (se 1 (by rfl) ⟨175244, by rfl⟩ : syracuseStep 233659 = 350489) B350489
theorem B299513 : Blo 127788 299513 := bstep (se 2 (by rfl) ⟨112317, by rfl⟩ : syracuseStep 299513 = 224635) B224635
theorem B332383 : Blo 127788 332383 := bstep (se 1 (by rfl) ⟨249287, by rfl⟩ : syracuseStep 332383 = 498575) B498575
theorem B234247 : Blo 127788 234247 := bstep (se 1 (by rfl) ⟨175685, by rfl⟩ : syracuseStep 234247 = 351371) B351371
theorem B3150899 : Blo 127788 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B4199633 : Blo 127788 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B333011 : Blo 127788 333011 := bstep (se 1 (by rfl) ⟨249758, by rfl⟩ : syracuseStep 333011 = 499517) B499517
theorem B366049 : Blo 127788 366049 := bstep (se 2 (by rfl) ⟨137268, by rfl⟩ : syracuseStep 366049 = 274537) B274537
theorem B1250873 : Blo 127788 1250873 := bstep (se 2 (by rfl) ⟨469077, by rfl⟩ : syracuseStep 1250873 = 938155) B938155
theorem B923309 : Blo 127788 923309 := bstep (se 3 (by rfl) ⟨173120, by rfl⟩ : syracuseStep 923309 = 346241) B346241
theorem B235361 : Blo 127788 235361 := bstep (se 2 (by rfl) ⟨88260, by rfl⟩ : syracuseStep 235361 = 176521) B176521
theorem B366551 : Blo 127788 366551 := bstep (se 1 (by rfl) ⟨274913, by rfl⟩ : syracuseStep 366551 = 549827) B549827
theorem B1251409 : Blo 127788 1251409 := bstep (se 2 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 1251409 = 938557) B938557
theorem B596413 : Blo 127788 596413 := bstep (se 3 (by rfl) ⟨111827, by rfl⟩ : syracuseStep 596413 = 223655) B223655
theorem B924317 : Blo 127788 924317 := bstep (se 3 (by rfl) ⟨173309, by rfl⟩ : syracuseStep 924317 = 346619) B346619
theorem B432863 : Blo 127788 432863 := bstep (se 1 (by rfl) ⟨324647, by rfl⟩ : syracuseStep 432863 = 649295) B649295
theorem B1776491 : Blo 127788 1776491 := bstep (se 1 (by rfl) ⟨1332368, by rfl⟩ : syracuseStep 1776491 = 2664737) B2664737
theorem B760747 : Blo 127788 760747 := bstep (se 1 (by rfl) ⟨570560, by rfl⟩ : syracuseStep 760747 = 1141121) B1141121
theorem B695441 : Blo 127788 695441 := bstep (se 2 (by rfl) ⟨260790, by rfl⟩ : syracuseStep 695441 = 521581) B521581
theorem B433619 : Blo 127788 433619 := bstep (se 1 (by rfl) ⟨325214, by rfl⟩ : syracuseStep 433619 = 650429) B650429
theorem B368135 : Blo 127788 368135 := bstep (se 1 (by rfl) ⟨276101, by rfl⟩ : syracuseStep 368135 = 552203) B552203
theorem B433889 : Blo 127788 433889 := bstep (se 2 (by rfl) ⟨162708, by rfl⟩ : syracuseStep 433889 = 325417) B325417
theorem B1515311 : Blo 127788 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B5775533 : Blo 127788 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B500201 : Blo 127788 500201 := bstep (se 2 (by rfl) ⟨187575, by rfl⟩ : syracuseStep 500201 = 375151) B375151
theorem B631435 : Blo 127788 631435 := bstep (se 1 (by rfl) ⟨473576, by rfl⟩ : syracuseStep 631435 = 947153) B947153
theorem B205897 : Blo 127788 205897 := bstep (se 2 (by rfl) ⟨77211, by rfl⟩ : syracuseStep 205897 = 154423) B154423
theorem B435563 : Blo 127788 435563 := bstep (se 1 (by rfl) ⟨326672, by rfl⟩ : syracuseStep 435563 = 653345) B653345
theorem B435671 : Blo 127788 435671 := bstep (se 1 (by rfl) ⟨326753, by rfl⟩ : syracuseStep 435671 = 653507) B653507
theorem B665171 : Blo 127788 665171 := bstep (se 1 (by rfl) ⟨498878, by rfl⟩ : syracuseStep 665171 = 997757) B997757
theorem B435833 : Blo 127788 435833 := bstep (se 2 (by rfl) ⟨163437, by rfl⟩ : syracuseStep 435833 = 326875) B326875
theorem B1320581 : Blo 127788 1320581 := bstep (se 4 (by rfl) ⟨123804, by rfl⟩ : syracuseStep 1320581 = 247609) B247609
theorem B1845125 : Blo 127788 1845125 := bstep (se 4 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 1845125 = 345961) B345961
theorem B468935 : Blo 127788 468935 := bstep (se 1 (by rfl) ⟨351701, by rfl⟩ : syracuseStep 468935 = 703403) B703403
theorem B1845281 : Blo 127788 1845281 := bstep (se 2 (by rfl) ⟨691980, by rfl⟩ : syracuseStep 1845281 = 1383961) B1383961
theorem B567713 : Blo 127788 567713 := bstep (se 2 (by rfl) ⟨212892, by rfl⟩ : syracuseStep 567713 = 425785) B425785
theorem B1092203 : Blo 127788 1092203 := bstep (se 1 (by rfl) ⟨819152, by rfl⟩ : syracuseStep 1092203 = 1638305) B1638305
theorem B797359 : Blo 127788 797359 := bstep (se 1 (by rfl) ⟨598019, by rfl⟩ : syracuseStep 797359 = 1196039) B1196039
theorem B535531 : Blo 127788 535531 := bstep (se 1 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 535531 = 803297) B803297
theorem B437345 : Blo 127788 437345 := bstep (se 2 (by rfl) ⟨164004, by rfl⟩ : syracuseStep 437345 = 328009) B328009
theorem B994841 : Blo 127788 994841 := bstep (se 2 (by rfl) ⟨373065, by rfl⟩ : syracuseStep 994841 = 746131) B746131
theorem B437885 : Blo 127788 437885 := bstep (se 3 (by rfl) ⟨82103, by rfl⟩ : syracuseStep 437885 = 164207) B164207
theorem B274195 : Blo 127788 274195 := bstep (se 1 (by rfl) ⟨205646, by rfl⟩ : syracuseStep 274195 = 411293) B411293
theorem B438155 : Blo 127788 438155 := bstep (se 1 (by rfl) ⟨328616, by rfl⟩ : syracuseStep 438155 = 657233) B657233
theorem B1388461 : Blo 127788 1388461 := bstep (se 3 (by rfl) ⟨260336, by rfl⟩ : syracuseStep 1388461 = 520673) B520673
theorem B241631 : Blo 127788 241631 := bstep (se 1 (by rfl) ⟨181223, by rfl⟩ : syracuseStep 241631 = 362447) B362447
theorem B831455 : Blo 127788 831455 := bstep (se 1 (by rfl) ⟨623591, by rfl⟩ : syracuseStep 831455 = 1247183) B1247183
theorem B16330817 : Blo 127788 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B1487159 : Blo 127788 1487159 := bstep (se 1 (by rfl) ⟨1115369, by rfl⟩ : syracuseStep 1487159 = 2230739) B2230739
theorem B438695 : Blo 127788 438695 := bstep (se 1 (by rfl) ⟨329021, by rfl⟩ : syracuseStep 438695 = 658043) B658043
theorem B995813 : Blo 127788 995813 := bstep (se 4 (by rfl) ⟨93357, by rfl⟩ : syracuseStep 995813 = 186715) B186715
theorem B373511 : Blo 127788 373511 := bstep (se 1 (by rfl) ⟨280133, by rfl⟩ : syracuseStep 373511 = 560267) B560267
theorem B308009 : Blo 127788 308009 := bstep (se 2 (by rfl) ⟨115503, by rfl⟩ : syracuseStep 308009 = 231007) B231007
theorem B832427 : Blo 127788 832427 := bstep (se 1 (by rfl) ⟨624320, by rfl⟩ : syracuseStep 832427 = 1248641) B1248641
theorem B308279 : Blo 127788 308279 := bstep (se 1 (by rfl) ⟨231209, by rfl⟩ : syracuseStep 308279 = 462419) B462419
theorem B1881265 : Blo 127788 1881265 := bstep (se 2 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 1881265 = 1410949) B1410949
theorem B2504357 : Blo 127788 2504357 := bstep (se 4 (by rfl) ⟨234783, by rfl⟩ : syracuseStep 2504357 = 469567) B469567
theorem B439991 : Blo 127788 439991 := bstep (se 1 (by rfl) ⟨329993, by rfl⟩ : syracuseStep 439991 = 659987) B659987
theorem B145147 : Blo 127788 145147 := bstep (se 1 (by rfl) ⟨108860, by rfl⟩ : syracuseStep 145147 = 217721) B217721
theorem B145183 : Blo 127788 145183 := bstep (se 1 (by rfl) ⟨108887, by rfl⟩ : syracuseStep 145183 = 217775) B217775
theorem B472969 : Blo 127788 472969 := bstep (se 2 (by rfl) ⟨177363, by rfl⟩ : syracuseStep 472969 = 354727) B354727
theorem B276443 : Blo 127788 276443 := bstep (se 1 (by rfl) ⟨207332, by rfl⟩ : syracuseStep 276443 = 414665) B414665
theorem B834067 : Blo 127788 834067 := bstep (se 1 (by rfl) ⟨625550, by rfl⟩ : syracuseStep 834067 = 1251101) B1251101
theorem B277339 : Blo 127788 277339 := bstep (se 1 (by rfl) ⟨208004, by rfl⟩ : syracuseStep 277339 = 416009) B416009
theorem B441179 : Blo 127788 441179 := bstep (se 1 (by rfl) ⟨330884, by rfl⟩ : syracuseStep 441179 = 661769) B661769
theorem B146335 : Blo 127788 146335 := bstep (se 1 (by rfl) ⟨109751, by rfl⟩ : syracuseStep 146335 = 219503) B219503
theorem B244777 : Blo 127788 244777 := bstep (se 2 (by rfl) ⟨91791, by rfl⟩ : syracuseStep 244777 = 183583) B183583
theorem B146479 : Blo 127788 146479 := bstep (se 1 (by rfl) ⟨109859, by rfl⟩ : syracuseStep 146479 = 219719) B219719
theorem B6110437 : Blo 127788 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B638237 : Blo 127788 638237 := bstep (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) B239339
theorem B146767 : Blo 127788 146767 := bstep (se 1 (by rfl) ⟨110075, by rfl⟩ : syracuseStep 146767 = 220151) B220151
theorem B441935 : Blo 127788 441935 := bstep (se 1 (by rfl) ⟨331451, by rfl⟩ : syracuseStep 441935 = 662903) B662903
theorem B245339 : Blo 127788 245339 := bstep (se 1 (by rfl) ⟨184004, by rfl⟩ : syracuseStep 245339 = 368009) B368009
theorem B278159 : Blo 127788 278159 := bstep (se 1 (by rfl) ⟨208619, by rfl⟩ : syracuseStep 278159 = 417239) B417239
theorem B442043 : Blo 127788 442043 := bstep (se 1 (by rfl) ⟨331532, by rfl⟩ : syracuseStep 442043 = 663065) B663065
theorem B147271 : Blo 127788 147271 := bstep (se 1 (by rfl) ⟨110453, by rfl⟩ : syracuseStep 147271 = 220907) B220907
theorem B901187 : Blo 127788 901187 := bstep (se 1 (by rfl) ⟨675890, by rfl⟩ : syracuseStep 901187 = 1351781) B1351781
theorem B704591 : Blo 127788 704591 := bstep (se 1 (by rfl) ⟨528443, by rfl⟩ : syracuseStep 704591 = 1056887) B1056887
theorem B311435 : Blo 127788 311435 := bstep (se 1 (by rfl) ⟨233576, by rfl⟩ : syracuseStep 311435 = 467153) B467153
theorem B999863 : Blo 127788 999863 := bstep (se 1 (by rfl) ⟨749897, by rfl⟩ : syracuseStep 999863 = 1499795) B1499795
theorem B147919 : Blo 127788 147919 := bstep (se 1 (by rfl) ⟨110939, by rfl⟩ : syracuseStep 147919 = 221879) B221879
theorem B705131 : Blo 127788 705131 := bstep (se 1 (by rfl) ⟨528848, by rfl⟩ : syracuseStep 705131 = 1057697) B1057697
theorem B934841 : Blo 127788 934841 := bstep (se 2 (by rfl) ⟨350565, by rfl⟩ : syracuseStep 934841 = 701131) B701131
theorem B738841 : Blo 127788 738841 := bstep (se 2 (by rfl) ⟨277065, by rfl⟩ : syracuseStep 738841 = 554131) B554131
theorem B443987 : Blo 127788 443987 := bstep (se 1 (by rfl) ⟨332990, by rfl⟩ : syracuseStep 443987 = 665981) B665981
theorem B1230497 : Blo 127788 1230497 := bstep (se 2 (by rfl) ⟨461436, by rfl⟩ : syracuseStep 1230497 = 922873) B922873
theorem B444257 : Blo 127788 444257 := bstep (se 2 (by rfl) ⟨166596, by rfl⟩ : syracuseStep 444257 = 333193) B333193
theorem B247799 : Blo 127788 247799 := bstep (se 1 (by rfl) ⟨185849, by rfl⟩ : syracuseStep 247799 = 371699) B371699
theorem B1001521 : Blo 127788 1001521 := bstep (se 2 (by rfl) ⟨375570, by rfl⟩ : syracuseStep 1001521 = 751141) B751141
theorem B182569 : Blo 127788 182569 := bstep (se 2 (by rfl) ⟨68463, by rfl⟩ : syracuseStep 182569 = 136927) B136927
theorem B1428101 : Blo 127788 1428101 := bstep (se 4 (by rfl) ⟨133884, by rfl⟩ : syracuseStep 1428101 = 267769) B267769
theorem B215689 : Blo 127788 215689 := bstep (se 2 (by rfl) ⟨80883, by rfl⟩ : syracuseStep 215689 = 161767) B161767
theorem B249257 : Blo 127788 249257 := bstep (se 2 (by rfl) ⟨93471, by rfl⟩ : syracuseStep 249257 = 186943) B186943
theorem B445943 : Blo 127788 445943 := bstep (se 1 (by rfl) ⟨334457, by rfl⟩ : syracuseStep 445943 = 668915) B668915
theorem B217471 : Blo 127788 217471 := bstep (se 1 (by rfl) ⟨163103, by rfl⟩ : syracuseStep 217471 = 326207) B326207
theorem B414163 : Blo 127788 414163 := bstep (se 1 (by rfl) ⟨310622, by rfl⟩ : syracuseStep 414163 = 621245) B621245
theorem B971513 : Blo 127788 971513 := bstep (se 2 (by rfl) ⟨364317, by rfl⟩ : syracuseStep 971513 = 728635) B728635
theorem B3822329 : Blo 127788 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B4510505 : Blo 127788 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B217903 : Blo 127788 217903 := bstep (se 1 (by rfl) ⟨163427, by rfl⟩ : syracuseStep 217903 = 326855) B326855
theorem B185755 : Blo 127788 185755 := bstep (se 1 (by rfl) ⟨139316, by rfl⟩ : syracuseStep 185755 = 278633) B278633
theorem B218875 : Blo 127788 218875 := bstep (se 1 (by rfl) ⟨164156, by rfl⟩ : syracuseStep 218875 = 328313) B328313
theorem B219017 : Blo 127788 219017 := bstep (se 2 (by rfl) ⟨82131, by rfl⟩ : syracuseStep 219017 = 164263) B164263
theorem B448571 : Blo 127788 448571 := bstep (se 1 (by rfl) ⟨336428, by rfl⟩ : syracuseStep 448571 = 672857) B672857
theorem B219449 : Blo 127788 219449 := bstep (se 2 (by rfl) ⟨82293, by rfl⟩ : syracuseStep 219449 = 164587) B164587
theorem B547195 : Blo 127788 547195 := bstep (se 1 (by rfl) ⟨410396, by rfl⟩ : syracuseStep 547195 = 820793) B820793
theorem B252283 : Blo 127788 252283 := bstep (se 1 (by rfl) ⟨189212, by rfl⟩ : syracuseStep 252283 = 378425) B378425
theorem B220063 : Blo 127788 220063 := bstep (se 1 (by rfl) ⟨165047, by rfl⟩ : syracuseStep 220063 = 330095) B330095
theorem B1006573 : Blo 127788 1006573 := bstep (se 3 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 1006573 = 377465) B377465
theorem B2219075 : Blo 127788 2219075 := bstep (se 1 (by rfl) ⟨1664306, by rfl⟩ : syracuseStep 2219075 = 3328613) B3328613
theorem B416983 : Blo 127788 416983 := bstep (se 1 (by rfl) ⟨312737, by rfl⟩ : syracuseStep 416983 = 625475) B625475
theorem B351485 : Blo 127788 351485 := bstep (se 3 (by rfl) ⟨65903, by rfl⟩ : syracuseStep 351485 = 131807) B131807
theorem B220495 : Blo 127788 220495 := bstep (se 1 (by rfl) ⟨165371, by rfl⟩ : syracuseStep 220495 = 330743) B330743
theorem B417163 : Blo 127788 417163 := bstep (se 1 (by rfl) ⟨312872, by rfl⟩ : syracuseStep 417163 = 625745) B625745
theorem B220583 : Blo 127788 220583 := bstep (se 1 (by rfl) ⟨165437, by rfl⟩ : syracuseStep 220583 = 330875) B330875
theorem B220745 : Blo 127788 220745 := bstep (se 2 (by rfl) ⟨82779, by rfl⟩ : syracuseStep 220745 = 165559) B165559
theorem B1663213 : Blo 127788 1663213 := bstep (se 3 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 1663213 = 623705) B623705
theorem B221647 : Blo 127788 221647 := bstep (se 1 (by rfl) ⟨166235, by rfl⟩ : syracuseStep 221647 = 332471) B332471
theorem B418367 : Blo 127788 418367 := bstep (se 1 (by rfl) ⟨313775, by rfl⟩ : syracuseStep 418367 = 627551) B627551
theorem B221791 : Blo 127788 221791 := bstep (se 1 (by rfl) ⟨166343, by rfl⟩ : syracuseStep 221791 = 332687) B332687
theorem B3629873 : Blo 127788 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B746405 : Blo 127788 746405 := bstep (se 4 (by rfl) ⟨69975, by rfl⟩ : syracuseStep 746405 = 139951) B139951
theorem B222203 : Blo 127788 222203 := bstep (se 1 (by rfl) ⟨166652, by rfl⟩ : syracuseStep 222203 = 333305) B333305
theorem B779453 : Blo 127788 779453 := bstep (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) B292295
theorem B288107 : Blo 127788 288107 := bstep (se 1 (by rfl) ⟨216080, by rfl⟩ : syracuseStep 288107 = 432161) B432161
theorem B747089 : Blo 127788 747089 := bstep (se 2 (by rfl) ⟨280158, by rfl⟩ : syracuseStep 747089 = 560317) B560317
theorem B288377 : Blo 127788 288377 := bstep (se 2 (by rfl) ⟨108141, by rfl⟩ : syracuseStep 288377 = 216283) B216283
theorem B4745603 : Blo 127788 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B289385 : Blo 127788 289385 := bstep (se 2 (by rfl) ⟨108519, by rfl⟩ : syracuseStep 289385 = 217039) B217039
theorem B224327 : Blo 127788 224327 := bstep (se 1 (by rfl) ⟨168245, by rfl⟩ : syracuseStep 224327 = 336491) B336491
theorem B191711 : Blo 127788 191711 := bstep (se 1 (by rfl) ⟨143783, by rfl⟩ : syracuseStep 191711 = 287567) B287567
theorem B290015 : Blo 127788 290015 := bstep (se 1 (by rfl) ⟨217511, by rfl⟩ : syracuseStep 290015 = 435023) B435023
theorem B191753 : Blo 127788 191753 := bstep (se 2 (by rfl) ⟨71907, by rfl⟩ : syracuseStep 191753 = 143815) B143815
theorem B191855 : Blo 127788 191855 := bstep (se 1 (by rfl) ⟨143891, by rfl⟩ : syracuseStep 191855 = 287783) B287783
theorem B290231 : Blo 127788 290231 := bstep (se 1 (by rfl) ⟨217673, by rfl⟩ : syracuseStep 290231 = 435347) B435347
theorem B191975 : Blo 127788 191975 := bstep (se 1 (by rfl) ⟨143981, by rfl⟩ : syracuseStep 191975 = 287963) B287963
theorem B749047 : Blo 127788 749047 := bstep (se 1 (by rfl) ⟨561785, by rfl⟩ : syracuseStep 749047 = 1123571) B1123571
theorem B192107 : Blo 127788 192107 := bstep (se 1 (by rfl) ⟨144080, by rfl⟩ : syracuseStep 192107 = 288161) B288161
theorem B290411 : Blo 127788 290411 := bstep (se 1 (by rfl) ⟨217808, by rfl⟩ : syracuseStep 290411 = 435617) B435617
theorem B192233 : Blo 127788 192233 := bstep (se 2 (by rfl) ⟨72087, by rfl⟩ : syracuseStep 192233 = 144175) B144175
theorem B192377 : Blo 127788 192377 := bstep (se 2 (by rfl) ⟨72141, by rfl⟩ : syracuseStep 192377 = 144283) B144283
theorem B290681 : Blo 127788 290681 := bstep (se 2 (by rfl) ⟨109005, by rfl⟩ : syracuseStep 290681 = 218011) B218011
theorem B192479 : Blo 127788 192479 := bstep (se 1 (by rfl) ⟨144359, by rfl⟩ : syracuseStep 192479 = 288719) B288719
theorem B1077371 : Blo 127788 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B192731 : Blo 127788 192731 := bstep (se 1 (by rfl) ⟨144548, by rfl⟩ : syracuseStep 192731 = 289097) B289097
theorem B192743 : Blo 127788 192743 := bstep (se 1 (by rfl) ⟨144557, by rfl⟩ : syracuseStep 192743 = 289115) B289115
theorem B192905 : Blo 127788 192905 := bstep (se 2 (by rfl) ⟨72339, by rfl⟩ : syracuseStep 192905 = 144679) B144679
theorem B193001 : Blo 127788 193001 := bstep (se 2 (by rfl) ⟨72375, by rfl⟩ : syracuseStep 193001 = 144751) B144751
theorem B1896949 : Blo 127788 1896949 := bstep (se 5 (by rfl) ⟨88919, by rfl⟩ : syracuseStep 1896949 = 177839) B177839
theorem B881239 : Blo 127788 881239 := bstep (se 1 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 881239 = 1321859) B1321859
theorem B193127 : Blo 127788 193127 := bstep (se 1 (by rfl) ⟨144845, by rfl⟩ : syracuseStep 193127 = 289691) B289691
theorem B1471121 : Blo 127788 1471121 := bstep (se 2 (by rfl) ⟨551670, by rfl⟩ : syracuseStep 1471121 = 1103341) B1103341
theorem B946835 : Blo 127788 946835 := bstep (se 1 (by rfl) ⟨710126, by rfl⟩ : syracuseStep 946835 = 1420253) B1420253
theorem B193259 : Blo 127788 193259 := bstep (se 1 (by rfl) ⟨144944, by rfl⟩ : syracuseStep 193259 = 289889) B289889
theorem B193289 : Blo 127788 193289 := bstep (se 2 (by rfl) ⟨72483, by rfl⟩ : syracuseStep 193289 = 144967) B144967
theorem B13202189 : Blo 127788 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B127855 : Blo 127788 127855 := bstep (se 1 (by rfl) ⟨95891, by rfl⟩ : syracuseStep 127855 = 191783) B191783
theorem B193391 : Blo 127788 193391 := bstep (se 1 (by rfl) ⟨145043, by rfl⟩ : syracuseStep 193391 = 290087) B290087
theorem B127911 : Blo 127788 127911 := bstep (se 1 (by rfl) ⟨95933, by rfl⟩ : syracuseStep 127911 = 191867) B191867
theorem B127995 : Blo 127788 127995 := bstep (se 1 (by rfl) ⟨95996, by rfl⟩ : syracuseStep 127995 = 191993) B191993
theorem B128063 : Blo 127788 128063 := bstep (se 1 (by rfl) ⟨96047, by rfl⟩ : syracuseStep 128063 = 192095) B192095
theorem B193643 : Blo 127788 193643 := bstep (se 1 (by rfl) ⟨145232, by rfl⟩ : syracuseStep 193643 = 290465) B290465
theorem B128207 : Blo 127788 128207 := bstep (se 1 (by rfl) ⟨96155, by rfl⟩ : syracuseStep 128207 = 192311) B192311
theorem B292187 : Blo 127788 292187 := bstep (se 1 (by rfl) ⟨219140, by rfl⟩ : syracuseStep 292187 = 438281) B438281
theorem B193883 : Blo 127788 193883 := bstep (se 1 (by rfl) ⟨145412, by rfl⟩ : syracuseStep 193883 = 290825) B290825
theorem B128411 : Blo 127788 128411 := bstep (se 1 (by rfl) ⟨96308, by rfl⟩ : syracuseStep 128411 = 192617) B192617
theorem B128623 : Blo 127788 128623 := bstep (se 1 (by rfl) ⟨96467, by rfl⟩ : syracuseStep 128623 = 192935) B192935
theorem B194159 : Blo 127788 194159 := bstep (se 1 (by rfl) ⟨145619, by rfl⟩ : syracuseStep 194159 = 291239) B291239
theorem B128679 : Blo 127788 128679 := bstep (se 1 (by rfl) ⟨96509, by rfl⟩ : syracuseStep 128679 = 193019) B193019
theorem B194231 : Blo 127788 194231 := bstep (se 1 (by rfl) ⟨145673, by rfl⟩ : syracuseStep 194231 = 291347) B291347
theorem B292535 : Blo 127788 292535 := bstep (se 1 (by rfl) ⟨219401, by rfl⟩ : syracuseStep 292535 = 438803) B438803
theorem B226999 : Blo 127788 226999 := bstep (se 1 (by rfl) ⟨170249, by rfl⟩ : syracuseStep 226999 = 340499) B340499
theorem B194267 : Blo 127788 194267 := bstep (se 1 (by rfl) ⟨145700, by rfl⟩ : syracuseStep 194267 = 291401) B291401
theorem B128763 : Blo 127788 128763 := bstep (se 1 (by rfl) ⟨96572, by rfl⟩ : syracuseStep 128763 = 193145) B193145
theorem B128799 : Blo 127788 128799 := bstep (se 1 (by rfl) ⟨96599, by rfl⟩ : syracuseStep 128799 = 193199) B193199
theorem B128831 : Blo 127788 128831 := bstep (se 1 (by rfl) ⟨96623, by rfl⟩ : syracuseStep 128831 = 193247) B193247
theorem B194441 : Blo 127788 194441 := bstep (se 2 (by rfl) ⟨72915, by rfl⟩ : syracuseStep 194441 = 145831) B145831
theorem B129007 : Blo 127788 129007 := bstep (se 1 (by rfl) ⟨96755, by rfl⟩ : syracuseStep 129007 = 193511) B193511
theorem B194543 : Blo 127788 194543 := bstep (se 1 (by rfl) ⟨145907, by rfl⟩ : syracuseStep 194543 = 291815) B291815
theorem B129179 : Blo 127788 129179 := bstep (se 1 (by rfl) ⟨96884, by rfl⟩ : syracuseStep 129179 = 193769) B193769
theorem B129215 : Blo 127788 129215 := bstep (se 1 (by rfl) ⟨96911, by rfl⟩ : syracuseStep 129215 = 193823) B193823
theorem B194795 : Blo 127788 194795 := bstep (se 1 (by rfl) ⟨146096, by rfl⟩ : syracuseStep 194795 = 292193) B292193
theorem B194855 : Blo 127788 194855 := bstep (se 1 (by rfl) ⟨146141, by rfl⟩ : syracuseStep 194855 = 292283) B292283
theorem B129327 : Blo 127788 129327 := bstep (se 1 (by rfl) ⟨96995, by rfl⟩ : syracuseStep 129327 = 193991) B193991
theorem B194939 : Blo 127788 194939 := bstep (se 1 (by rfl) ⟨146204, by rfl⟩ : syracuseStep 194939 = 292409) B292409
theorem B129563 : Blo 127788 129563 := bstep (se 1 (by rfl) ⟨97172, by rfl⟩ : syracuseStep 129563 = 194345) B194345
theorem B129567 : Blo 127788 129567 := bstep (se 1 (by rfl) ⟨97175, by rfl⟩ : syracuseStep 129567 = 194351) B194351
theorem B195209 : Blo 127788 195209 := bstep (se 2 (by rfl) ⟨73203, by rfl⟩ : syracuseStep 195209 = 146407) B146407
theorem B195383 : Blo 127788 195383 := bstep (se 1 (by rfl) ⟨146537, by rfl⟩ : syracuseStep 195383 = 293075) B293075
theorem B129883 : Blo 127788 129883 := bstep (se 1 (by rfl) ⟨97412, by rfl⟩ : syracuseStep 129883 = 194825) B194825
theorem B195419 : Blo 127788 195419 := bstep (se 1 (by rfl) ⟨146564, by rfl⟩ : syracuseStep 195419 = 293129) B293129
theorem B293723 : Blo 127788 293723 := bstep (se 1 (by rfl) ⟨220292, by rfl⟩ : syracuseStep 293723 = 440585) B440585
theorem B129951 : Blo 127788 129951 := bstep (se 1 (by rfl) ⟨97463, by rfl⟩ : syracuseStep 129951 = 194927) B194927
theorem B392161 : Blo 127788 392161 := bstep (se 2 (by rfl) ⟨147060, by rfl⟩ : syracuseStep 392161 = 294121) B294121
theorem B195563 : Blo 127788 195563 := bstep (se 1 (by rfl) ⟨146672, by rfl⟩ : syracuseStep 195563 = 293345) B293345
theorem B130095 : Blo 127788 130095 := bstep (se 1 (by rfl) ⟨97571, by rfl⟩ : syracuseStep 130095 = 195143) B195143
theorem B130119 : Blo 127788 130119 := bstep (se 1 (by rfl) ⟨97589, by rfl⟩ : syracuseStep 130119 = 195179) B195179
theorem B195767 : Blo 127788 195767 := bstep (se 1 (by rfl) ⟨146825, by rfl⟩ : syracuseStep 195767 = 293651) B293651
theorem B130271 : Blo 127788 130271 := bstep (se 1 (by rfl) ⟨97703, by rfl⟩ : syracuseStep 130271 = 195407) B195407
theorem B523513 : Blo 127788 523513 := bstep (se 2 (by rfl) ⟨196317, by rfl⟩ : syracuseStep 523513 = 392635) B392635
theorem B196007 : Blo 127788 196007 := bstep (se 1 (by rfl) ⟨147005, by rfl⟩ : syracuseStep 196007 = 294011) B294011
theorem B654803 : Blo 127788 654803 := bstep (se 1 (by rfl) ⟨491102, by rfl⟩ : syracuseStep 654803 = 982205) B982205
theorem B130535 : Blo 127788 130535 := bstep (se 1 (by rfl) ⟨97901, by rfl⟩ : syracuseStep 130535 = 195803) B195803
theorem B1474037 : Blo 127788 1474037 := bstep (se 5 (by rfl) ⟨69095, by rfl⟩ : syracuseStep 1474037 = 138191) B138191
theorem B196091 : Blo 127788 196091 := bstep (se 1 (by rfl) ⟨147068, by rfl⟩ : syracuseStep 196091 = 294137) B294137
theorem B294479 : Blo 127788 294479 := bstep (se 1 (by rfl) ⟨220859, by rfl⟩ : syracuseStep 294479 = 441719) B441719
theorem B130651 : Blo 127788 130651 := bstep (se 1 (by rfl) ⟨97988, by rfl⟩ : syracuseStep 130651 = 195977) B195977
theorem B196187 : Blo 127788 196187 := bstep (se 1 (by rfl) ⟨147140, by rfl⟩ : syracuseStep 196187 = 294281) B294281
theorem B327311 : Blo 127788 327311 := bstep (se 1 (by rfl) ⟨245483, by rfl⟩ : syracuseStep 327311 = 490967) B490967
theorem B196271 : Blo 127788 196271 := bstep (se 1 (by rfl) ⟨147203, by rfl⟩ : syracuseStep 196271 = 294407) B294407
theorem B491255 : Blo 127788 491255 := bstep (se 1 (by rfl) ⟨368441, by rfl⟩ : syracuseStep 491255 = 736883) B736883
theorem B196391 : Blo 127788 196391 := bstep (se 1 (by rfl) ⟨147293, by rfl⟩ : syracuseStep 196391 = 294587) B294587
theorem B130887 : Blo 127788 130887 := bstep (se 1 (by rfl) ⟨98165, by rfl⟩ : syracuseStep 130887 = 196331) B196331
theorem B294779 : Blo 127788 294779 := bstep (se 1 (by rfl) ⟨221084, by rfl⟩ : syracuseStep 294779 = 442169) B442169
theorem B196475 : Blo 127788 196475 := bstep (se 1 (by rfl) ⟨147356, by rfl⟩ : syracuseStep 196475 = 294713) B294713
theorem B131039 : Blo 127788 131039 := bstep (se 1 (by rfl) ⟨98279, by rfl⟩ : syracuseStep 131039 = 196559) B196559
theorem B15728717 : Blo 127788 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B196799 : Blo 127788 196799 := bstep (se 1 (by rfl) ⟨147599, by rfl⟩ : syracuseStep 196799 = 295199) B295199
theorem B131263 : Blo 127788 131263 := bstep (se 1 (by rfl) ⟨98447, by rfl⟩ : syracuseStep 131263 = 196895) B196895
theorem B131279 : Blo 127788 131279 := bstep (se 1 (by rfl) ⟨98459, by rfl⟩ : syracuseStep 131279 = 196919) B196919
theorem B131327 : Blo 127788 131327 := bstep (se 1 (by rfl) ⟨98495, by rfl⟩ : syracuseStep 131327 = 196991) B196991
theorem B131375 : Blo 127788 131375 := bstep (se 1 (by rfl) ⟨98531, by rfl⟩ : syracuseStep 131375 = 197063) B197063
theorem B328151 : Blo 127788 328151 := bstep (se 1 (by rfl) ⟨246113, by rfl⟩ : syracuseStep 328151 = 492227) B492227
theorem B131611 : Blo 127788 131611 := bstep (se 1 (by rfl) ⟨98708, by rfl⟩ : syracuseStep 131611 = 197417) B197417
theorem B131615 : Blo 127788 131615 := bstep (se 1 (by rfl) ⟨98711, by rfl⟩ : syracuseStep 131615 = 197423) B197423
theorem B295529 : Blo 127788 295529 := bstep (se 2 (by rfl) ⟨110823, by rfl⟩ : syracuseStep 295529 = 221647) B221647
theorem B197225 : Blo 127788 197225 := bstep (se 2 (by rfl) ⟨73959, by rfl⟩ : syracuseStep 197225 = 147919) B147919
theorem B197231 : Blo 127788 197231 := bstep (se 1 (by rfl) ⟨147923, by rfl⟩ : syracuseStep 197231 = 295847) B295847
theorem B131695 : Blo 127788 131695 := bstep (se 1 (by rfl) ⟨98771, by rfl⟩ : syracuseStep 131695 = 197543) B197543
theorem B623227 : Blo 127788 623227 := bstep (se 1 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 623227 = 934841) B934841
theorem B131751 : Blo 127788 131751 := bstep (se 1 (by rfl) ⟨98813, by rfl⟩ : syracuseStep 131751 = 197627) B197627
theorem B295721 : Blo 127788 295721 := bstep (se 2 (by rfl) ⟨110895, by rfl⟩ : syracuseStep 295721 = 221791) B221791
theorem B295991 : Blo 127788 295991 := bstep (se 1 (by rfl) ⟨221993, by rfl⟩ : syracuseStep 295991 = 443987) B443987
theorem B820331 : Blo 127788 820331 := bstep (se 1 (by rfl) ⟨615248, by rfl⟩ : syracuseStep 820331 = 1230497) B1230497
theorem B296171 : Blo 127788 296171 := bstep (se 1 (by rfl) ⟨222128, by rfl⟩ : syracuseStep 296171 = 444257) B444257
theorem B263711 : Blo 127788 263711 := bstep (se 1 (by rfl) ⟨197783, by rfl⟩ : syracuseStep 263711 = 395567) B395567
theorem B952067 : Blo 127788 952067 := bstep (se 1 (by rfl) ⟨714050, by rfl⟩ : syracuseStep 952067 = 1428101) B1428101
theorem B10192877 : Blo 127788 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B985121 : Blo 127788 985121 := bstep (se 2 (by rfl) ⟨369420, by rfl⟩ : syracuseStep 985121 = 738841) B738841
theorem B3180869 : Blo 127788 3180869 := bstep (se 4 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 3180869 = 596413) B596413
theorem B985483 : Blo 127788 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B854491 : Blo 127788 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B199675 : Blo 127788 199675 := bstep (se 1 (by rfl) ⟨149756, by rfl⟩ : syracuseStep 199675 = 299513) B299513
theorem B2100599 : Blo 127788 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B299047 : Blo 127788 299047 := bstep (se 1 (by rfl) ⟨224285, by rfl⟩ : syracuseStep 299047 = 448571) B448571
theorem B1577009 : Blo 127788 1577009 := bstep (se 2 (by rfl) ⟨591378, by rfl⟩ : syracuseStep 1577009 = 1182757) B1182757
theorem B1184327 : Blo 127788 1184327 := bstep (se 1 (by rfl) ⟨888245, by rfl⟩ : syracuseStep 1184327 = 1776491) B1776491
theorem B528977 : Blo 127788 528977 := bstep (se 2 (by rfl) ⟨198366, by rfl⟩ : syracuseStep 528977 = 396733) B396733
theorem B1479383 : Blo 127788 1479383 := bstep (se 1 (by rfl) ⟨1109537, by rfl⟩ : syracuseStep 1479383 = 2219075) B2219075
theorem B463627 : Blo 127788 463627 := bstep (se 1 (by rfl) ⟨347720, by rfl⟩ : syracuseStep 463627 = 695441) B695441
theorem B234323 : Blo 127788 234323 := bstep (se 1 (by rfl) ⟨175742, by rfl⟩ : syracuseStep 234323 = 351485) B351485
theorem B660797 : Blo 127788 660797 := bstep (se 3 (by rfl) ⟨123899, by rfl⟩ : syracuseStep 660797 = 247799) B247799
theorem B4920749 : Blo 127788 4920749 := bstep (se 3 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 4920749 = 1845281) B1845281
theorem B333467 : Blo 127788 333467 := bstep (se 1 (by rfl) ⟨250100, by rfl⟩ : syracuseStep 333467 = 500201) B500201
theorem B497603 : Blo 127788 497603 := bstep (se 1 (by rfl) ⟨373202, by rfl⟩ : syracuseStep 497603 = 746405) B746405
theorem B2529265 : Blo 127788 2529265 := bstep (se 2 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 2529265 = 1896949) B1896949
theorem B498059 : Blo 127788 498059 := bstep (se 1 (by rfl) ⟨373544, by rfl⟩ : syracuseStep 498059 = 747089) B747089
theorem B2792069 : Blo 127788 2792069 := bstep (se 4 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 2792069 = 523513) B523513
theorem B728135 : Blo 127788 728135 := bstep (se 1 (by rfl) ⟨546101, by rfl⟩ : syracuseStep 728135 = 1092203) B1092203
theorem B302665 : Blo 127788 302665 := bstep (se 2 (by rfl) ⟨113499, by rfl⟩ : syracuseStep 302665 = 226999) B226999
theorem B663227 : Blo 127788 663227 := bstep (se 1 (by rfl) ⟨497420, by rfl⟩ : syracuseStep 663227 = 994841) B994841
theorem B10887211 : Blo 127788 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B598205 : Blo 127788 598205 := bstep (se 3 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 598205 = 224327) B224327
theorem B991439 : Blo 127788 991439 := bstep (se 1 (by rfl) ⟨743579, by rfl⟩ : syracuseStep 991439 = 1487159) B1487159
theorem B663875 : Blo 127788 663875 := bstep (se 1 (by rfl) ⟨497906, by rfl⟩ : syracuseStep 663875 = 995813) B995813
theorem B631223 : Blo 127788 631223 := bstep (se 1 (by rfl) ⟨473417, by rfl⟩ : syracuseStep 631223 = 946835) B946835
theorem B729593 : Blo 127788 729593 := bstep (se 2 (by rfl) ⟨273597, by rfl⟩ : syracuseStep 729593 = 547195) B547195
theorem B336377 : Blo 127788 336377 := bstep (se 2 (by rfl) ⟨126141, by rfl⟩ : syracuseStep 336377 = 252283) B252283
theorem B205339 : Blo 127788 205339 := bstep (se 1 (by rfl) ⟨154004, by rfl⟩ : syracuseStep 205339 = 308009) B308009
theorem B205519 : Blo 127788 205519 := bstep (se 1 (by rfl) ⟨154139, by rfl⟩ : syracuseStep 205519 = 308279) B308279
theorem B664685 : Blo 127788 664685 := bstep (se 3 (by rfl) ⟨124628, by rfl⟩ : syracuseStep 664685 = 249257) B249257
theorem B369785 : Blo 127788 369785 := bstep (se 2 (by rfl) ⟨138669, by rfl⟩ : syracuseStep 369785 = 277339) B277339
theorem B1189181 : Blo 127788 1189181 := bstep (se 3 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 1189181 = 445943) B445943
theorem B436535 : Blo 127788 436535 := bstep (se 1 (by rfl) ⟨327401, by rfl⟩ : syracuseStep 436535 = 654803) B654803
theorem B600791 : Blo 127788 600791 := bstep (se 1 (by rfl) ⟨450593, by rfl⟩ : syracuseStep 600791 = 901187) B901187
theorem B469727 : Blo 127788 469727 := bstep (se 1 (by rfl) ⟨352295, by rfl⟩ : syracuseStep 469727 = 704591) B704591
theorem B207623 : Blo 127788 207623 := bstep (se 1 (by rfl) ⟨155717, by rfl⟩ : syracuseStep 207623 = 311435) B311435
theorem B666575 : Blo 127788 666575 := bstep (se 1 (by rfl) ⟨499931, by rfl⟩ : syracuseStep 666575 = 999863) B999863
theorem B470087 : Blo 127788 470087 := bstep (se 1 (by rfl) ⟨352565, by rfl⟩ : syracuseStep 470087 = 705131) B705131
theorem B2468987 : Blo 127788 2468987 := bstep (se 1 (by rfl) ⟨1851740, by rfl⟩ : syracuseStep 2468987 = 3703481) B3703481
theorem B437993 : Blo 127788 437993 := bstep (se 2 (by rfl) ⟨164247, by rfl⟩ : syracuseStep 437993 = 328495) B328495
theorem B274529 : Blo 127788 274529 := bstep (se 2 (by rfl) ⟨102948, by rfl⟩ : syracuseStep 274529 = 205897) B205897
theorem B9679661 : Blo 127788 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B373567 : Blo 127788 373567 := bstep (se 1 (by rfl) ⟨280175, by rfl⟩ : syracuseStep 373567 = 560351) B560351
theorem B2208869 : Blo 127788 2208869 := bstep (se 4 (by rfl) ⟨207081, by rfl⟩ : syracuseStep 2208869 = 414163) B414163
theorem B242939 : Blo 127788 242939 := bstep (se 1 (by rfl) ⟨182204, by rfl⟩ : syracuseStep 242939 = 364409) B364409
theorem B243425 : Blo 127788 243425 := bstep (se 2 (by rfl) ⟨91284, by rfl⟩ : syracuseStep 243425 = 182569) B182569
theorem B1488617 : Blo 127788 1488617 := bstep (se 2 (by rfl) ⟨558231, by rfl⟩ : syracuseStep 1488617 = 1116463) B1116463
theorem B2799755 : Blo 127788 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B1063145 : Blo 127788 1063145 := bstep (se 2 (by rfl) ⟨398679, by rfl⟩ : syracuseStep 1063145 = 797359) B797359
theorem B1095929 : Blo 127788 1095929 := bstep (se 2 (by rfl) ⟨410973, by rfl⟩ : syracuseStep 1095929 = 821947) B821947
theorem B833915 : Blo 127788 833915 := bstep (se 1 (by rfl) ⟨625436, by rfl⟩ : syracuseStep 833915 = 1250873) B1250873
theorem B146011 : Blo 127788 146011 := bstep (se 1 (by rfl) ⟨109508, by rfl⟩ : syracuseStep 146011 = 219017) B219017
theorem B244367 : Blo 127788 244367 := bstep (se 1 (by rfl) ⟨183275, by rfl⟩ : syracuseStep 244367 = 366551) B366551
theorem B146299 : Blo 127788 146299 := bstep (se 1 (by rfl) ⟨109724, by rfl⟩ : syracuseStep 146299 = 219449) B219449
theorem B3521549 : Blo 127788 3521549 := bstep (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) B1320581
theorem B441449 : Blo 127788 441449 := bstep (se 2 (by rfl) ⟨165543, by rfl⟩ : syracuseStep 441449 = 331087) B331087
theorem B998729 : Blo 127788 998729 := bstep (se 2 (by rfl) ⟨374523, by rfl⟩ : syracuseStep 998729 = 749047) B749047
theorem B2801137 : Blo 127788 2801137 := bstep (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) B2100853
theorem B147055 : Blo 127788 147055 := bstep (se 1 (by rfl) ⟨110291, by rfl⟩ : syracuseStep 147055 = 220583) B220583
theorem B245423 : Blo 127788 245423 := bstep (se 1 (by rfl) ⟨184067, by rfl⟩ : syracuseStep 245423 = 368135) B368135
theorem B147163 : Blo 127788 147163 := bstep (se 1 (by rfl) ⟨110372, by rfl⟩ : syracuseStep 147163 = 220745) B220745
theorem B1851281 : Blo 127788 1851281 := bstep (se 2 (by rfl) ⟨694230, by rfl⟩ : syracuseStep 1851281 = 1388461) B1388461
theorem B3850355 : Blo 127788 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B311545 : Blo 127788 311545 := bstep (se 2 (by rfl) ⟨116829, by rfl⟩ : syracuseStep 311545 = 233659) B233659
theorem B278911 : Blo 127788 278911 := bstep (se 1 (by rfl) ⟨209183, by rfl⟩ : syracuseStep 278911 = 418367) B418367
theorem B148135 : Blo 127788 148135 := bstep (se 1 (by rfl) ⟨111101, by rfl⟩ : syracuseStep 148135 = 222203) B222203
theorem B443177 : Blo 127788 443177 := bstep (se 2 (by rfl) ⟨166191, by rfl⟩ : syracuseStep 443177 = 332383) B332383
theorem B312329 : Blo 127788 312329 := bstep (se 2 (by rfl) ⟨117123, by rfl⟩ : syracuseStep 312329 = 234247) B234247
theorem B443447 : Blo 127788 443447 := bstep (se 1 (by rfl) ⟨332585, by rfl⟩ : syracuseStep 443447 = 665171) B665171
theorem B1230083 : Blo 127788 1230083 := bstep (se 1 (by rfl) ⟨922562, by rfl⟩ : syracuseStep 1230083 = 1845125) B1845125
theorem B312623 : Blo 127788 312623 := bstep (se 1 (by rfl) ⟨234467, by rfl⟩ : syracuseStep 312623 = 468935) B468935
theorem B2508353 : Blo 127788 2508353 := bstep (se 2 (by rfl) ⟨940632, by rfl⟩ : syracuseStep 2508353 = 1881265) B1881265
theorem B3163735 : Blo 127788 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B378475 : Blo 127788 378475 := bstep (se 1 (by rfl) ⟨283856, by rfl⟩ : syracuseStep 378475 = 567713) B567713
theorem B247673 : Blo 127788 247673 := bstep (se 2 (by rfl) ⟨92877, by rfl⟩ : syracuseStep 247673 = 185755) B185755
theorem B249007 : Blo 127788 249007 := bstep (se 1 (by rfl) ⟨186755, by rfl⟩ : syracuseStep 249007 = 373511) B373511
theorem B8801459 : Blo 127788 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B184295 : Blo 127788 184295 := bstep (se 1 (by rfl) ⟨138221, by rfl⟩ : syracuseStep 184295 = 276443) B276443
theorem B1462373 : Blo 127788 1462373 := bstep (se 4 (by rfl) ⟨137097, by rfl⟩ : syracuseStep 1462373 = 274195) B274195
theorem B8147249 : Blo 127788 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B741757 : Blo 127788 741757 := bstep (se 3 (by rfl) ⟨139079, by rfl⟩ : syracuseStep 741757 = 278159) B278159
theorem B218207 : Blo 127788 218207 := bstep (se 1 (by rfl) ⟨163655, by rfl⟩ : syracuseStep 218207 = 327311) B327311
theorem B2217617 : Blo 127788 2217617 := bstep (se 2 (by rfl) ⟨831606, by rfl⟩ : syracuseStep 2217617 = 1663213) B1663213
theorem B841913 : Blo 127788 841913 := bstep (se 2 (by rfl) ⟨315717, by rfl⟩ : syracuseStep 841913 = 631435) B631435
theorem B220367 : Blo 127788 220367 := bstep (se 1 (by rfl) ⟨165275, by rfl⟩ : syracuseStep 220367 = 330551) B330551
theorem B1335361 : Blo 127788 1335361 := bstep (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) B1001521
theorem B647675 : Blo 127788 647675 := bstep (se 1 (by rfl) ⟨485756, by rfl⟩ : syracuseStep 647675 = 971513) B971513
theorem B3007003 : Blo 127788 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B222007 : Blo 127788 222007 := bstep (se 1 (by rfl) ⟨166505, by rfl⟩ : syracuseStep 222007 = 333011) B333011
theorem B287585 : Blo 127788 287585 := bstep (se 2 (by rfl) ⟨107844, by rfl⟩ : syracuseStep 287585 = 215689) B215689
theorem B779165 : Blo 127788 779165 := bstep (se 3 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 779165 = 292187) B292187
theorem B615539 : Blo 127788 615539 := bstep (se 1 (by rfl) ⟨461654, by rfl⟩ : syracuseStep 615539 = 923309) B923309
theorem B156907 : Blo 127788 156907 := bstep (se 1 (by rfl) ⟨117680, by rfl⟩ : syracuseStep 156907 = 235361) B235361
theorem B714041 : Blo 127788 714041 := bstep (se 2 (by rfl) ⟨267765, by rfl⟩ : syracuseStep 714041 = 535531) B535531
theorem B616211 : Blo 127788 616211 := bstep (se 1 (by rfl) ⟨462158, by rfl⟩ : syracuseStep 616211 = 924317) B924317
theorem B288575 : Blo 127788 288575 := bstep (se 1 (by rfl) ⟨216431, by rfl⟩ : syracuseStep 288575 = 432863) B432863
theorem B289079 : Blo 127788 289079 := bstep (se 1 (by rfl) ⟨216809, by rfl⟩ : syracuseStep 289079 = 433619) B433619
theorem B289259 : Blo 127788 289259 := bstep (se 1 (by rfl) ⟨216944, by rfl⟩ : syracuseStep 289259 = 433889) B433889
theorem B1010207 : Blo 127788 1010207 := bstep (se 1 (by rfl) ⟨757655, by rfl⟩ : syracuseStep 1010207 = 1515311) B1515311
theorem B289961 : Blo 127788 289961 := bstep (se 2 (by rfl) ⟨108735, by rfl⟩ : syracuseStep 289961 = 217471) B217471
theorem B1174985 : Blo 127788 1174985 := bstep (se 2 (by rfl) ⟨440619, by rfl⟩ : syracuseStep 1174985 = 881239) B881239
theorem B519635 : Blo 127788 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B192071 : Blo 127788 192071 := bstep (se 1 (by rfl) ⟨144053, by rfl⟩ : syracuseStep 192071 = 288107) B288107
theorem B290375 : Blo 127788 290375 := bstep (se 1 (by rfl) ⟨217781, by rfl⟩ : syracuseStep 290375 = 435563) B435563
theorem B290447 : Blo 127788 290447 := bstep (se 1 (by rfl) ⟨217835, by rfl⟩ : syracuseStep 290447 = 435671) B435671
theorem B290537 : Blo 127788 290537 := bstep (se 2 (by rfl) ⟨108951, by rfl⟩ : syracuseStep 290537 = 217903) B217903
theorem B192251 : Blo 127788 192251 := bstep (se 1 (by rfl) ⟨144188, by rfl⟩ : syracuseStep 192251 = 288377) B288377
theorem B290555 : Blo 127788 290555 := bstep (se 1 (by rfl) ⟨217916, by rfl⟩ : syracuseStep 290555 = 435833) B435833
theorem B192923 : Blo 127788 192923 := bstep (se 1 (by rfl) ⟨144692, by rfl⟩ : syracuseStep 192923 = 289385) B289385
theorem B488065 : Blo 127788 488065 := bstep (se 2 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 488065 = 366049) B366049
theorem B291563 : Blo 127788 291563 := bstep (se 1 (by rfl) ⟨218672, by rfl⟩ : syracuseStep 291563 = 437345) B437345
theorem B619325 : Blo 127788 619325 := bstep (se 3 (by rfl) ⟨116123, by rfl⟩ : syracuseStep 619325 = 232247) B232247
theorem B127807 : Blo 127788 127807 := bstep (se 1 (by rfl) ⟨95855, by rfl⟩ : syracuseStep 127807 = 191711) B191711
theorem B193343 : Blo 127788 193343 := bstep (se 1 (by rfl) ⟨145007, by rfl⟩ : syracuseStep 193343 = 290015) B290015
theorem B127835 : Blo 127788 127835 := bstep (se 1 (by rfl) ⟨95876, by rfl⟩ : syracuseStep 127835 = 191753) B191753
theorem B127903 : Blo 127788 127903 := bstep (se 1 (by rfl) ⟨95927, by rfl⟩ : syracuseStep 127903 = 191855) B191855
theorem B193487 : Blo 127788 193487 := bstep (se 1 (by rfl) ⟨145115, by rfl⟩ : syracuseStep 193487 = 290231) B290231
theorem B127983 : Blo 127788 127983 := bstep (se 1 (by rfl) ⟨95987, by rfl⟩ : syracuseStep 127983 = 191975) B191975
theorem B193529 : Blo 127788 193529 := bstep (se 2 (by rfl) ⟨72573, by rfl⟩ : syracuseStep 193529 = 145147) B145147
theorem B291833 : Blo 127788 291833 := bstep (se 2 (by rfl) ⟨109437, by rfl⟩ : syracuseStep 291833 = 218875) B218875
theorem B193577 : Blo 127788 193577 := bstep (se 2 (by rfl) ⟨72591, by rfl⟩ : syracuseStep 193577 = 145183) B145183
theorem B128071 : Blo 127788 128071 := bstep (se 1 (by rfl) ⟨96053, by rfl⟩ : syracuseStep 128071 = 192107) B192107
theorem B193607 : Blo 127788 193607 := bstep (se 1 (by rfl) ⟨145205, by rfl⟩ : syracuseStep 193607 = 290411) B290411
theorem B291923 : Blo 127788 291923 := bstep (se 1 (by rfl) ⟨218942, by rfl⟩ : syracuseStep 291923 = 437885) B437885
theorem B128155 : Blo 127788 128155 := bstep (se 1 (by rfl) ⟨96116, by rfl⟩ : syracuseStep 128155 = 192233) B192233
theorem B128251 : Blo 127788 128251 := bstep (se 1 (by rfl) ⟨96188, by rfl⟩ : syracuseStep 128251 = 192377) B192377
theorem B193787 : Blo 127788 193787 := bstep (se 1 (by rfl) ⟨145340, by rfl⟩ : syracuseStep 193787 = 290681) B290681
theorem B292103 : Blo 127788 292103 := bstep (se 1 (by rfl) ⟨219077, by rfl⟩ : syracuseStep 292103 = 438155) B438155
theorem B128319 : Blo 127788 128319 := bstep (se 1 (by rfl) ⟨96239, by rfl⟩ : syracuseStep 128319 = 192479) B192479
theorem B161087 : Blo 127788 161087 := bstep (se 1 (by rfl) ⟨120815, by rfl⟩ : syracuseStep 161087 = 241631) B241631
theorem B554303 : Blo 127788 554303 := bstep (se 1 (by rfl) ⟨415727, by rfl⟩ : syracuseStep 554303 = 831455) B831455
theorem B718247 : Blo 127788 718247 := bstep (se 1 (by rfl) ⟨538685, by rfl⟩ : syracuseStep 718247 = 1077371) B1077371
theorem B1668545 : Blo 127788 1668545 := bstep (se 2 (by rfl) ⟨625704, by rfl⟩ : syracuseStep 1668545 = 1251409) B1251409
theorem B128487 : Blo 127788 128487 := bstep (se 1 (by rfl) ⟨96365, by rfl⟩ : syracuseStep 128487 = 192731) B192731
theorem B128495 : Blo 127788 128495 := bstep (se 1 (by rfl) ⟨96371, by rfl⟩ : syracuseStep 128495 = 192743) B192743
theorem B128603 : Blo 127788 128603 := bstep (se 1 (by rfl) ⟨96452, by rfl⟩ : syracuseStep 128603 = 192905) B192905
theorem B292463 : Blo 127788 292463 := bstep (se 1 (by rfl) ⟨219347, by rfl⟩ : syracuseStep 292463 = 438695) B438695
theorem B128667 : Blo 127788 128667 := bstep (se 1 (by rfl) ⟨96500, by rfl⟩ : syracuseStep 128667 = 193001) B193001
theorem B128751 : Blo 127788 128751 := bstep (se 1 (by rfl) ⟨96563, by rfl⟩ : syracuseStep 128751 = 193127) B193127
theorem B980747 : Blo 127788 980747 := bstep (se 1 (by rfl) ⟨735560, by rfl⟩ : syracuseStep 980747 = 1471121) B1471121
theorem B128839 : Blo 127788 128839 := bstep (se 1 (by rfl) ⟨96629, by rfl⟩ : syracuseStep 128839 = 193259) B193259
theorem B128859 : Blo 127788 128859 := bstep (se 1 (by rfl) ⟨96644, by rfl⟩ : syracuseStep 128859 = 193289) B193289
theorem B128927 : Blo 127788 128927 := bstep (se 1 (by rfl) ⟨96695, by rfl⟩ : syracuseStep 128927 = 193391) B193391
theorem B554951 : Blo 127788 554951 := bstep (se 1 (by rfl) ⟨416213, by rfl⟩ : syracuseStep 554951 = 832427) B832427
theorem B1112089 : Blo 127788 1112089 := bstep (se 2 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 1112089 = 834067) B834067
theorem B129095 : Blo 127788 129095 := bstep (se 1 (by rfl) ⟨96821, by rfl⟩ : syracuseStep 129095 = 193643) B193643
theorem B1701965 : Blo 127788 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B129255 : Blo 127788 129255 := bstep (se 1 (by rfl) ⟨96941, by rfl⟩ : syracuseStep 129255 = 193883) B193883
theorem B129439 : Blo 127788 129439 := bstep (se 1 (by rfl) ⟨97079, by rfl⟩ : syracuseStep 129439 = 194159) B194159
theorem B1669571 : Blo 127788 1669571 := bstep (se 1 (by rfl) ⟨1252178, by rfl⟩ : syracuseStep 1669571 = 2504357) B2504357
theorem B129487 : Blo 127788 129487 := bstep (se 1 (by rfl) ⟨97115, by rfl⟩ : syracuseStep 129487 = 194231) B194231
theorem B195023 : Blo 127788 195023 := bstep (se 1 (by rfl) ⟨146267, by rfl⟩ : syracuseStep 195023 = 292535) B292535
theorem B293327 : Blo 127788 293327 := bstep (se 1 (by rfl) ⟨219995, by rfl⟩ : syracuseStep 293327 = 439991) B439991
theorem B129511 : Blo 127788 129511 := bstep (se 1 (by rfl) ⟨97133, by rfl⟩ : syracuseStep 129511 = 194267) B194267
theorem B195113 : Blo 127788 195113 := bstep (se 2 (by rfl) ⟨73167, by rfl⟩ : syracuseStep 195113 = 146335) B146335
theorem B293417 : Blo 127788 293417 := bstep (se 2 (by rfl) ⟨110031, by rfl⟩ : syracuseStep 293417 = 220063) B220063
theorem B1014329 : Blo 127788 1014329 := bstep (se 2 (by rfl) ⟨380373, by rfl⟩ : syracuseStep 1014329 = 760747) B760747
theorem B129627 : Blo 127788 129627 := bstep (se 1 (by rfl) ⟨97220, by rfl⟩ : syracuseStep 129627 = 194441) B194441
theorem B522881 : Blo 127788 522881 := bstep (se 2 (by rfl) ⟨196080, by rfl⟩ : syracuseStep 522881 = 392161) B392161
theorem B1342097 : Blo 127788 1342097 := bstep (se 2 (by rfl) ⟨503286, by rfl⟩ : syracuseStep 1342097 = 1006573) B1006573
theorem B129695 : Blo 127788 129695 := bstep (se 1 (by rfl) ⟨97271, by rfl⟩ : syracuseStep 129695 = 194543) B194543
theorem B326369 : Blo 127788 326369 := bstep (se 2 (by rfl) ⟨122388, by rfl⟩ : syracuseStep 326369 = 244777) B244777
theorem B195305 : Blo 127788 195305 := bstep (se 2 (by rfl) ⟨73239, by rfl⟩ : syracuseStep 195305 = 146479) B146479
theorem B129863 : Blo 127788 129863 := bstep (se 1 (by rfl) ⟨97397, by rfl⟩ : syracuseStep 129863 = 194795) B194795
theorem B129903 : Blo 127788 129903 := bstep (se 1 (by rfl) ⟨97427, by rfl⟩ : syracuseStep 129903 = 194855) B194855
theorem B129959 : Blo 127788 129959 := bstep (se 1 (by rfl) ⟨97469, by rfl⟩ : syracuseStep 129959 = 194939) B194939
theorem B555977 : Blo 127788 555977 := bstep (se 2 (by rfl) ⟨208491, by rfl⟩ : syracuseStep 555977 = 416983) B416983
theorem B130139 : Blo 127788 130139 := bstep (se 1 (by rfl) ⟨97604, by rfl⟩ : syracuseStep 130139 = 195209) B195209
theorem B195689 : Blo 127788 195689 := bstep (se 2 (by rfl) ⟨73383, by rfl⟩ : syracuseStep 195689 = 146767) B146767
theorem B293993 : Blo 127788 293993 := bstep (se 2 (by rfl) ⟨110247, by rfl⟩ : syracuseStep 293993 = 220495) B220495
theorem B556217 : Blo 127788 556217 := bstep (se 2 (by rfl) ⟨208581, by rfl⟩ : syracuseStep 556217 = 417163) B417163
theorem B130255 : Blo 127788 130255 := bstep (se 1 (by rfl) ⟨97691, by rfl⟩ : syracuseStep 130255 = 195383) B195383
theorem B130279 : Blo 127788 130279 := bstep (se 1 (by rfl) ⟨97709, by rfl⟩ : syracuseStep 130279 = 195419) B195419
theorem B195815 : Blo 127788 195815 := bstep (se 1 (by rfl) ⟨146861, by rfl⟩ : syracuseStep 195815 = 293723) B293723
theorem B294119 : Blo 127788 294119 := bstep (se 1 (by rfl) ⟨220589, by rfl⟩ : syracuseStep 294119 = 441179) B441179
theorem B130375 : Blo 127788 130375 := bstep (se 1 (by rfl) ⟨97781, by rfl⟩ : syracuseStep 130375 = 195563) B195563
theorem B2522501 : Blo 127788 2522501 := bstep (se 4 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 2522501 = 472969) B472969
theorem B130511 : Blo 127788 130511 := bstep (se 1 (by rfl) ⟨97883, by rfl⟩ : syracuseStep 130511 = 195767) B195767
theorem B1244645 : Blo 127788 1244645 := bstep (se 4 (by rfl) ⟨116685, by rfl⟩ : syracuseStep 1244645 = 233371) B233371
theorem B130671 : Blo 127788 130671 := bstep (se 1 (by rfl) ⟨98003, by rfl⟩ : syracuseStep 130671 = 196007) B196007
theorem B982691 : Blo 127788 982691 := bstep (se 1 (by rfl) ⟨737018, by rfl⟩ : syracuseStep 982691 = 1474037) B1474037
theorem B130727 : Blo 127788 130727 := bstep (se 1 (by rfl) ⟨98045, by rfl⟩ : syracuseStep 130727 = 196091) B196091
theorem B294623 : Blo 127788 294623 := bstep (se 1 (by rfl) ⟨220967, by rfl⟩ : syracuseStep 294623 = 441935) B441935
theorem B196319 : Blo 127788 196319 := bstep (se 1 (by rfl) ⟨147239, by rfl⟩ : syracuseStep 196319 = 294479) B294479
theorem B163559 : Blo 127788 163559 := bstep (se 1 (by rfl) ⟨122669, by rfl⟩ : syracuseStep 163559 = 245339) B245339
theorem B130791 : Blo 127788 130791 := bstep (se 1 (by rfl) ⟨98093, by rfl⟩ : syracuseStep 130791 = 196187) B196187
theorem B196361 : Blo 127788 196361 := bstep (se 2 (by rfl) ⟨73635, by rfl⟩ : syracuseStep 196361 = 147271) B147271
theorem B130847 : Blo 127788 130847 := bstep (se 1 (by rfl) ⟨98135, by rfl⟩ : syracuseStep 130847 = 196271) B196271
theorem B294695 : Blo 127788 294695 := bstep (se 1 (by rfl) ⟨221021, by rfl⟩ : syracuseStep 294695 = 442043) B442043
theorem B327503 : Blo 127788 327503 := bstep (se 1 (by rfl) ⟨245627, by rfl⟩ : syracuseStep 327503 = 491255) B491255
theorem B130927 : Blo 127788 130927 := bstep (se 1 (by rfl) ⟨98195, by rfl⟩ : syracuseStep 130927 = 196391) B196391
theorem B196519 : Blo 127788 196519 := bstep (se 1 (by rfl) ⟨147389, by rfl⟩ : syracuseStep 196519 = 294779) B294779
theorem B130983 : Blo 127788 130983 := bstep (se 1 (by rfl) ⟨98237, by rfl⟩ : syracuseStep 130983 = 196475) B196475
theorem B10485811 : Blo 127788 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B14516281 : Blo 127788 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B131199 : Blo 127788 131199 := bstep (se 1 (by rfl) ⟨98399, by rfl⟩ : syracuseStep 131199 = 196799) B196799
theorem B131483 : Blo 127788 131483 := bstep (se 1 (by rfl) ⟨98612, by rfl⟩ : syracuseStep 131483 = 197225) B197225
theorem B131487 : Blo 127788 131487 := bstep (se 1 (by rfl) ⟨98615, by rfl⟩ : syracuseStep 131487 = 197231) B197231
theorem B295451 : Blo 127788 295451 := bstep (se 1 (by rfl) ⟨221588, by rfl⟩ : syracuseStep 295451 = 443177) B443177
theorem B197147 : Blo 127788 197147 := bstep (se 1 (by rfl) ⟨147860, by rfl⟩ : syracuseStep 197147 = 295721) B295721
theorem B295631 : Blo 127788 295631 := bstep (se 1 (by rfl) ⟨221723, by rfl⟩ : syracuseStep 295631 = 443447) B443447
theorem B197327 : Blo 127788 197327 := bstep (se 1 (by rfl) ⟨147995, by rfl⟩ : syracuseStep 197327 = 295991) B295991
theorem B197447 : Blo 127788 197447 := bstep (se 1 (by rfl) ⟨148085, by rfl⟩ : syracuseStep 197447 = 296171) B296171
theorem B820055 : Blo 127788 820055 := bstep (se 1 (by rfl) ⟨615041, by rfl⟩ : syracuseStep 820055 = 1230083) B1230083
theorem B197513 : Blo 127788 197513 := bstep (se 2 (by rfl) ⟨74067, by rfl⟩ : syracuseStep 197513 = 148135) B148135
theorem B1672235 : Blo 127788 1672235 := bstep (se 1 (by rfl) ⟨1254176, by rfl⟩ : syracuseStep 1672235 = 2508353) B2508353
theorem B296009 : Blo 127788 296009 := bstep (se 2 (by rfl) ⟨111003, by rfl⟩ : syracuseStep 296009 = 222007) B222007
theorem B165115 : Blo 127788 165115 := bstep (se 1 (by rfl) ⟨123836, by rfl⟩ : syracuseStep 165115 = 247673) B247673
theorem B656747 : Blo 127788 656747 := bstep (se 1 (by rfl) ⟨492560, by rfl⟩ : syracuseStep 656747 = 985121) B985121
theorem B1410605 : Blo 127788 1410605 := bstep (se 3 (by rfl) ⟨264488, by rfl⟩ : syracuseStep 1410605 = 528977) B528977
theorem B788077 : Blo 127788 788077 := bstep (se 3 (by rfl) ⟨147764, by rfl⟩ : syracuseStep 788077 = 295529) B295529
theorem B5867639 : Blo 127788 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B1051339 : Blo 127788 1051339 := bstep (se 1 (by rfl) ⟨788504, by rfl⟩ : syracuseStep 1051339 = 1577009) B1577009
theorem B986093 : Blo 127788 986093 := bstep (se 3 (by rfl) ⟨184892, by rfl⟩ : syracuseStep 986093 = 369785) B369785
theorem B789551 : Blo 127788 789551 := bstep (se 1 (by rfl) ⟨592163, by rfl⟩ : syracuseStep 789551 = 1184327) B1184327
theorem B986255 : Blo 127788 986255 := bstep (se 1 (by rfl) ⟨739691, by rfl⟩ : syracuseStep 986255 = 1479383) B1479383
theorem B1313977 : Blo 127788 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B3280499 : Blo 127788 3280499 := bstep (se 1 (by rfl) ⟨2460374, by rfl⟩ : syracuseStep 3280499 = 4920749) B4920749
theorem B1478411 : Blo 127788 1478411 := bstep (se 1 (by rfl) ⟨1108808, by rfl⟩ : syracuseStep 1478411 = 2217617) B2217617
theorem B331735 : Blo 127788 331735 := bstep (se 1 (by rfl) ⟨248801, by rfl⟩ : syracuseStep 331735 = 497603) B497603
theorem B561275 : Blo 127788 561275 := bstep (se 1 (by rfl) ⟨420956, by rfl⟩ : syracuseStep 561275 = 841913) B841913
theorem B332009 : Blo 127788 332009 := bstep (se 2 (by rfl) ⟨124503, by rfl⟩ : syracuseStep 332009 = 249007) B249007
theorem B332039 : Blo 127788 332039 := bstep (se 1 (by rfl) ⟨249029, by rfl⟩ : syracuseStep 332039 = 498059) B498059
theorem B1479869 : Blo 127788 1479869 := bstep (se 3 (by rfl) ⟨277475, by rfl⟩ : syracuseStep 1479869 = 554951) B554951
theorem B398729 : Blo 127788 398729 := bstep (se 2 (by rfl) ⟨149523, by rfl⟩ : syracuseStep 398729 = 299047) B299047
theorem B660959 : Blo 127788 660959 := bstep (se 1 (by rfl) ⟨495719, by rfl⟩ : syracuseStep 660959 = 991439) B991439
theorem B431783 : Blo 127788 431783 := bstep (se 1 (by rfl) ⟨323837, by rfl⟩ : syracuseStep 431783 = 647675) B647675
theorem B989009 : Blo 127788 989009 := bstep (se 2 (by rfl) ⟨370878, by rfl⟩ : syracuseStep 989009 = 741757) B741757
theorem B498089 : Blo 127788 498089 := bstep (se 2 (by rfl) ⟨186783, by rfl⟩ : syracuseStep 498089 = 373567) B373567
theorem B1645991 : Blo 127788 1645991 := bstep (se 1 (by rfl) ⟨1234493, by rfl⟩ : syracuseStep 1645991 = 2468987) B2468987
theorem B1482785 : Blo 127788 1482785 := bstep (se 2 (by rfl) ⟨556044, by rfl⟩ : syracuseStep 1482785 = 1112089) B1112089
theorem B369535 : Blo 127788 369535 := bstep (se 1 (by rfl) ⟨277151, by rfl⟩ : syracuseStep 369535 = 554303) B554303
theorem B992411 : Blo 127788 992411 := bstep (se 1 (by rfl) ⟨744308, by rfl⟩ : syracuseStep 992411 = 1488617) B1488617
theorem B1385693 : Blo 127788 1385693 := bstep (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) B519635
theorem B730619 : Blo 127788 730619 := bstep (se 1 (by rfl) ⟨547964, by rfl⟩ : syracuseStep 730619 = 1095929) B1095929
theorem B894731 : Blo 127788 894731 := bstep (se 1 (by rfl) ⟨671048, by rfl⟩ : syracuseStep 894731 = 1342097) B1342097
theorem B436157 : Blo 127788 436157 := bstep (se 3 (by rfl) ⟨81779, by rfl⟩ : syracuseStep 436157 = 163559) B163559
theorem B370651 : Blo 127788 370651 := bstep (se 1 (by rfl) ⟨277988, by rfl⟩ : syracuseStep 370651 = 555977) B555977
theorem B403553 : Blo 127788 403553 := bstep (se 2 (by rfl) ⟨151332, by rfl⟩ : syracuseStep 403553 = 302665) B302665
theorem B370811 : Blo 127788 370811 := bstep (se 1 (by rfl) ⟨278108, by rfl⟩ : syracuseStep 370811 = 556217) B556217
theorem B665819 : Blo 127788 665819 := bstep (se 1 (by rfl) ⟨499364, by rfl⟩ : syracuseStep 665819 = 998729) B998729
theorem B1681667 : Blo 127788 1681667 := bstep (se 1 (by rfl) ⟨1261250, by rfl⟩ : syracuseStep 1681667 = 2522501) B2522501
theorem B829763 : Blo 127788 829763 := bstep (se 1 (by rfl) ⟨622322, by rfl⟩ : syracuseStep 829763 = 1244645) B1244645
theorem B2566903 : Blo 127788 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B1780481 : Blo 127788 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B732077 : Blo 127788 732077 := bstep (se 3 (by rfl) ⟨137264, by rfl⟩ : syracuseStep 732077 = 274529) B274529
theorem B371881 : Blo 127788 371881 := bstep (se 2 (by rfl) ⟨139455, by rfl⟩ : syracuseStep 371881 = 278911) B278911
theorem B208219 : Blo 127788 208219 := bstep (se 1 (by rfl) ⟨156164, by rfl⟩ : syracuseStep 208219 = 312329) B312329
theorem B273785 : Blo 127788 273785 := bstep (se 2 (by rfl) ⟨102669, by rfl⟩ : syracuseStep 273785 = 205339) B205339
theorem B4009337 : Blo 127788 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B830969 : Blo 127788 830969 := bstep (se 2 (by rfl) ⟨311613, by rfl⟩ : syracuseStep 830969 = 623227) B623227
theorem B208415 : Blo 127788 208415 := bstep (se 1 (by rfl) ⟨156311, by rfl⟩ : syracuseStep 208415 = 312623) B312623
theorem B274025 : Blo 127788 274025 := bstep (se 2 (by rfl) ⟨102759, by rfl⟩ : syracuseStep 274025 = 205519) B205519
theorem B175807 : Blo 127788 175807 := bstep (se 1 (by rfl) ⟨131855, by rfl⟩ : syracuseStep 175807 = 263711) B263711
theorem B634711 : Blo 127788 634711 := bstep (se 1 (by rfl) ⟨476033, by rfl⟩ : syracuseStep 634711 = 952067) B952067
theorem B6795251 : Blo 127788 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B1718261 : Blo 127788 1718261 := bstep (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) B161087
theorem B145471 : Blo 127788 145471 := bstep (se 1 (by rfl) ⟨109103, by rfl⟩ : syracuseStep 145471 = 218207) B218207
theorem B440531 : Blo 127788 440531 := bstep (se 1 (by rfl) ⟨330398, by rfl⟩ : syracuseStep 440531 = 660797) B660797
theorem B2472677 : Blo 127788 2472677 := bstep (se 4 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 2472677 = 463627) B463627
theorem B146911 : Blo 127788 146911 := bstep (se 1 (by rfl) ⟨110183, by rfl⟩ : syracuseStep 146911 = 220367) B220367
theorem B442151 : Blo 127788 442151 := bstep (se 1 (by rfl) ⟨331613, by rfl⟩ : syracuseStep 442151 = 663227) B663227
theorem B1064933 : Blo 127788 1064933 := bstep (se 4 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 1064933 = 199675) B199675
theorem B442583 : Blo 127788 442583 := bstep (se 1 (by rfl) ⟨331937, by rfl⟩ : syracuseStep 442583 = 663875) B663875
theorem B443123 : Blo 127788 443123 := bstep (se 1 (by rfl) ⟨332342, by rfl⟩ : syracuseStep 443123 = 664685) B664685
theorem B410359 : Blo 127788 410359 := bstep (se 1 (by rfl) ⟨307769, by rfl⟩ : syracuseStep 410359 = 615539) B615539
theorem B476027 : Blo 127788 476027 := bstep (se 1 (by rfl) ⟨357020, by rfl⟩ : syracuseStep 476027 = 714041) B714041
theorem B410807 : Blo 127788 410807 := bstep (se 1 (by rfl) ⟨308105, by rfl⟩ : syracuseStep 410807 = 616211) B616211
theorem B836837 : Blo 127788 836837 := bstep (se 4 (by rfl) ⟨78453, by rfl⟩ : syracuseStep 836837 = 156907) B156907
theorem B673471 : Blo 127788 673471 := bstep (se 1 (by rfl) ⟨505103, by rfl⟩ : syracuseStep 673471 = 1010207) B1010207
theorem B313151 : Blo 127788 313151 := bstep (se 1 (by rfl) ⟨234863, by rfl⟩ : syracuseStep 313151 = 469727) B469727
theorem B444383 : Blo 127788 444383 := bstep (se 1 (by rfl) ⟨333287, by rfl⟩ : syracuseStep 444383 = 666575) B666575
theorem B313391 : Blo 127788 313391 := bstep (se 1 (by rfl) ⟨235043, by rfl⟩ : syracuseStep 313391 = 470087) B470087
theorem B412883 : Blo 127788 412883 := bstep (se 1 (by rfl) ⟨309662, by rfl⟩ : syracuseStep 412883 = 619325) B619325
theorem B2018533 : Blo 127788 2018533 := bstep (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) B378475
theorem B478831 : Blo 127788 478831 := bstep (se 1 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 478831 = 718247) B718247
theorem B1134643 : Blo 127788 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B708763 : Blo 127788 708763 := bstep (se 1 (by rfl) ⟨531572, by rfl⟩ : syracuseStep 708763 = 1063145) B1063145
theorem B676219 : Blo 127788 676219 := bstep (se 1 (by rfl) ⟨507164, by rfl⟩ : syracuseStep 676219 = 1014329) B1014329
theorem B348587 : Blo 127788 348587 := bstep (se 1 (by rfl) ⟨261440, by rfl⟩ : syracuseStep 348587 = 522881) B522881
theorem B217579 : Blo 127788 217579 := bstep (se 1 (by rfl) ⟨163184, by rfl⟩ : syracuseStep 217579 = 326369) B326369
theorem B2347699 : Blo 127788 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B218335 : Blo 127788 218335 := bstep (se 1 (by rfl) ⟨163751, by rfl⟩ : syracuseStep 218335 = 327503) B327503
theorem B1234187 : Blo 127788 1234187 := bstep (se 1 (by rfl) ⟨925640, by rfl⟩ : syracuseStep 1234187 = 1851281) B1851281
theorem B218767 : Blo 127788 218767 := bstep (se 1 (by rfl) ⟨164075, by rfl⟩ : syracuseStep 218767 = 328151) B328151
theorem B1595213 : Blo 127788 1595213 := bstep (se 3 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 1595213 = 598205) B598205
theorem B546887 : Blo 127788 546887 := bstep (se 1 (by rfl) ⟨410165, by rfl⟩ : syracuseStep 546887 = 820331) B820331
theorem B1661573 : Blo 127788 1661573 := bstep (se 4 (by rfl) ⟨155772, by rfl⟩ : syracuseStep 1661573 = 311545) B311545
theorem B2120579 : Blo 127788 2120579 := bstep (se 1 (by rfl) ⟨1590434, by rfl⟩ : syracuseStep 2120579 = 3180869) B3180869
theorem B4218313 : Blo 127788 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B1400399 : Blo 127788 1400399 := bstep (se 1 (by rfl) ⟨1050299, by rfl⟩ : syracuseStep 1400399 = 2100599) B2100599
theorem B974915 : Blo 127788 974915 := bstep (se 1 (by rfl) ⟨731186, by rfl⟩ : syracuseStep 974915 = 1462373) B1462373
theorem B5431499 : Blo 127788 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B156215 : Blo 127788 156215 := bstep (se 1 (by rfl) ⟨117161, by rfl⟩ : syracuseStep 156215 = 234323) B234323
theorem B1139321 : Blo 127788 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B647837 : Blo 127788 647837 := bstep (se 3 (by rfl) ⟨121469, by rfl⟩ : syracuseStep 647837 = 242939) B242939
theorem B3171149 : Blo 127788 3171149 := bstep (se 3 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 3171149 = 1189181) B1189181
theorem B222311 : Blo 127788 222311 := bstep (se 1 (by rfl) ⟨166733, by rfl⟩ : syracuseStep 222311 = 333467) B333467
theorem B1861379 : Blo 127788 1861379 := bstep (se 1 (by rfl) ⟨1396034, by rfl⟩ : syracuseStep 1861379 = 2792069) B2792069
theorem B649133 : Blo 127788 649133 := bstep (se 3 (by rfl) ⟨121712, by rfl⟩ : syracuseStep 649133 = 243425) B243425
theorem B485423 : Blo 127788 485423 := bstep (se 1 (by rfl) ⟨364067, by rfl⟩ : syracuseStep 485423 = 728135) B728135
theorem B420815 : Blo 127788 420815 := bstep (se 1 (by rfl) ⟨315611, by rfl⟩ : syracuseStep 420815 = 631223) B631223
theorem B486395 : Blo 127788 486395 := bstep (se 1 (by rfl) ⟨364796, by rfl⟩ : syracuseStep 486395 = 729593) B729593
theorem B224251 : Blo 127788 224251 := bstep (se 1 (by rfl) ⟨168188, by rfl⟩ : syracuseStep 224251 = 336377) B336377
theorem B191723 : Blo 127788 191723 := bstep (se 1 (by rfl) ⟨143792, by rfl⟩ : syracuseStep 191723 = 287585) B287585
theorem B519443 : Blo 127788 519443 := bstep (se 1 (by rfl) ⟨389582, by rfl⟩ : syracuseStep 519443 = 779165) B779165
theorem B650753 : Blo 127788 650753 := bstep (se 2 (by rfl) ⟨244032, by rfl⟩ : syracuseStep 650753 = 488065) B488065
theorem B192383 : Blo 127788 192383 := bstep (se 1 (by rfl) ⟨144287, by rfl⟩ : syracuseStep 192383 = 288575) B288575
theorem B192719 : Blo 127788 192719 := bstep (se 1 (by rfl) ⟨144539, by rfl⟩ : syracuseStep 192719 = 289079) B289079
theorem B291023 : Blo 127788 291023 := bstep (se 1 (by rfl) ⟨218267, by rfl⟩ : syracuseStep 291023 = 436535) B436535
theorem B192839 : Blo 127788 192839 := bstep (se 1 (by rfl) ⟨144629, by rfl⟩ : syracuseStep 192839 = 289259) B289259
theorem B1602109 : Blo 127788 1602109 := bstep (se 3 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 1602109 = 600791) B600791
theorem B553661 : Blo 127788 553661 := bstep (se 3 (by rfl) ⟨103811, by rfl⟩ : syracuseStep 553661 = 207623) B207623
theorem B193307 : Blo 127788 193307 := bstep (se 1 (by rfl) ⟨144980, by rfl⟩ : syracuseStep 193307 = 289961) B289961
theorem B783323 : Blo 127788 783323 := bstep (se 1 (by rfl) ⟨587492, by rfl⟩ : syracuseStep 783323 = 1174985) B1174985
theorem B128047 : Blo 127788 128047 := bstep (se 1 (by rfl) ⟨96035, by rfl⟩ : syracuseStep 128047 = 192071) B192071
theorem B193583 : Blo 127788 193583 := bstep (se 1 (by rfl) ⟨145187, by rfl⟩ : syracuseStep 193583 = 290375) B290375
theorem B193631 : Blo 127788 193631 := bstep (se 1 (by rfl) ⟨145223, by rfl⟩ : syracuseStep 193631 = 290447) B290447
theorem B193691 : Blo 127788 193691 := bstep (se 1 (by rfl) ⟨145268, by rfl⟩ : syracuseStep 193691 = 290537) B290537
theorem B291995 : Blo 127788 291995 := bstep (se 1 (by rfl) ⟨218996, by rfl⟩ : syracuseStep 291995 = 437993) B437993
theorem B128167 : Blo 127788 128167 := bstep (se 1 (by rfl) ⟨96125, by rfl⟩ : syracuseStep 128167 = 192251) B192251
theorem B193703 : Blo 127788 193703 := bstep (se 1 (by rfl) ⟨145277, by rfl⟩ : syracuseStep 193703 = 290555) B290555
theorem B3372353 : Blo 127788 3372353 := bstep (se 2 (by rfl) ⟨1264632, by rfl⟩ : syracuseStep 3372353 = 2529265) B2529265
theorem B128615 : Blo 127788 128615 := bstep (se 1 (by rfl) ⟨96461, by rfl⟩ : syracuseStep 128615 = 192923) B192923
theorem B194375 : Blo 127788 194375 := bstep (se 1 (by rfl) ⟨145781, by rfl⟩ : syracuseStep 194375 = 291563) B291563
theorem B6453107 : Blo 127788 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B128895 : Blo 127788 128895 := bstep (se 1 (by rfl) ⟨96671, by rfl⟩ : syracuseStep 128895 = 193343) B193343
theorem B128991 : Blo 127788 128991 := bstep (se 1 (by rfl) ⟨96743, by rfl⟩ : syracuseStep 128991 = 193487) B193487
theorem B129019 : Blo 127788 129019 := bstep (se 1 (by rfl) ⟨96764, by rfl⟩ : syracuseStep 129019 = 193529) B193529
theorem B194555 : Blo 127788 194555 := bstep (se 1 (by rfl) ⟨145916, by rfl⟩ : syracuseStep 194555 = 291833) B291833
theorem B129051 : Blo 127788 129051 := bstep (se 1 (by rfl) ⟨96788, by rfl⟩ : syracuseStep 129051 = 193577) B193577
theorem B129071 : Blo 127788 129071 := bstep (se 1 (by rfl) ⟨96803, by rfl⟩ : syracuseStep 129071 = 193607) B193607
theorem B194615 : Blo 127788 194615 := bstep (se 1 (by rfl) ⟨145961, by rfl⟩ : syracuseStep 194615 = 291923) B291923
theorem B1472579 : Blo 127788 1472579 := bstep (se 1 (by rfl) ⟨1104434, by rfl⟩ : syracuseStep 1472579 = 2208869) B2208869
theorem B194681 : Blo 127788 194681 := bstep (se 2 (by rfl) ⟨73005, by rfl⟩ : syracuseStep 194681 = 146011) B146011
theorem B129191 : Blo 127788 129191 := bstep (se 1 (by rfl) ⟨96893, by rfl⟩ : syracuseStep 129191 = 193787) B193787
theorem B194735 : Blo 127788 194735 := bstep (se 1 (by rfl) ⟨146051, by rfl⟩ : syracuseStep 194735 = 292103) B292103
theorem B1112363 : Blo 127788 1112363 := bstep (se 1 (by rfl) ⟨834272, by rfl⟩ : syracuseStep 1112363 = 1668545) B1668545
theorem B194975 : Blo 127788 194975 := bstep (se 1 (by rfl) ⟨146231, by rfl⟩ : syracuseStep 194975 = 292463) B292463
theorem B195065 : Blo 127788 195065 := bstep (se 2 (by rfl) ⟨73149, by rfl⟩ : syracuseStep 195065 = 146299) B146299
theorem B653831 : Blo 127788 653831 := bstep (se 1 (by rfl) ⟨490373, by rfl⟩ : syracuseStep 653831 = 980747) B980747
theorem B1866503 : Blo 127788 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B555943 : Blo 127788 555943 := bstep (se 1 (by rfl) ⟨416957, by rfl⟩ : syracuseStep 555943 = 833915) B833915
theorem B1113047 : Blo 127788 1113047 := bstep (se 1 (by rfl) ⟨834785, by rfl⟩ : syracuseStep 1113047 = 1669571) B1669571
theorem B130015 : Blo 127788 130015 := bstep (se 1 (by rfl) ⟨97511, by rfl⟩ : syracuseStep 130015 = 195023) B195023
theorem B195551 : Blo 127788 195551 := bstep (se 1 (by rfl) ⟨146663, by rfl⟩ : syracuseStep 195551 = 293327) B293327
theorem B130075 : Blo 127788 130075 := bstep (se 1 (by rfl) ⟨97556, by rfl⟩ : syracuseStep 130075 = 195113) B195113
theorem B195611 : Blo 127788 195611 := bstep (se 1 (by rfl) ⟨146708, by rfl⟩ : syracuseStep 195611 = 293417) B293417
theorem B162911 : Blo 127788 162911 := bstep (se 1 (by rfl) ⟨122183, by rfl⟩ : syracuseStep 162911 = 244367) B244367
theorem B130203 : Blo 127788 130203 := bstep (se 1 (by rfl) ⟨97652, by rfl⟩ : syracuseStep 130203 = 195305) B195305
theorem B3734849 : Blo 127788 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B130459 : Blo 127788 130459 := bstep (se 1 (by rfl) ⟨97844, by rfl⟩ : syracuseStep 130459 = 195689) B195689
theorem B195995 : Blo 127788 195995 := bstep (se 1 (by rfl) ⟨146996, by rfl⟩ : syracuseStep 195995 = 293993) B293993
theorem B294299 : Blo 127788 294299 := bstep (se 1 (by rfl) ⟨220724, by rfl⟩ : syracuseStep 294299 = 441449) B441449
theorem B196073 : Blo 127788 196073 := bstep (se 2 (by rfl) ⟨73527, by rfl⟩ : syracuseStep 196073 = 147055) B147055
theorem B130543 : Blo 127788 130543 := bstep (se 1 (by rfl) ⟨97907, by rfl⟩ : syracuseStep 130543 = 195815) B195815
theorem B196079 : Blo 127788 196079 := bstep (se 1 (by rfl) ⟨147059, by rfl⟩ : syracuseStep 196079 = 294119) B294119
theorem B196217 : Blo 127788 196217 := bstep (se 2 (by rfl) ⟨73581, by rfl⟩ : syracuseStep 196217 = 147163) B147163
theorem B655127 : Blo 127788 655127 := bstep (se 1 (by rfl) ⟨491345, by rfl⟩ : syracuseStep 655127 = 982691) B982691
theorem B163615 : Blo 127788 163615 := bstep (se 1 (by rfl) ⟨122711, by rfl⟩ : syracuseStep 163615 = 245423) B245423
theorem B196415 : Blo 127788 196415 := bstep (se 1 (by rfl) ⟨147311, by rfl⟩ : syracuseStep 196415 = 294623) B294623
theorem B130879 : Blo 127788 130879 := bstep (se 1 (by rfl) ⟨98159, by rfl⟩ : syracuseStep 130879 = 196319) B196319
theorem B130907 : Blo 127788 130907 := bstep (se 1 (by rfl) ⟨98180, by rfl⟩ : syracuseStep 130907 = 196361) B196361
theorem B196463 : Blo 127788 196463 := bstep (se 1 (by rfl) ⟨147347, by rfl⟩ : syracuseStep 196463 = 294695) B294695
theorem B262025 : Blo 127788 262025 := bstep (se 2 (by rfl) ⟨98259, by rfl⟩ : syracuseStep 262025 = 196519) B196519
theorem B491453 : Blo 127788 491453 := bstep (se 3 (by rfl) ⟨92147, by rfl⟩ : syracuseStep 491453 = 184295) B184295
theorem B295055 : Blo 127788 295055 := bstep (se 1 (by rfl) ⟨221291, by rfl⟩ : syracuseStep 295055 = 442583) B442583
theorem B196967 : Blo 127788 196967 := bstep (se 1 (by rfl) ⟨147725, by rfl⟩ : syracuseStep 196967 = 295451) B295451
theorem B131431 : Blo 127788 131431 := bstep (se 1 (by rfl) ⟨98573, by rfl⟩ : syracuseStep 131431 = 197147) B197147
theorem B197087 : Blo 127788 197087 := bstep (se 1 (by rfl) ⟨147815, by rfl⟩ : syracuseStep 197087 = 295631) B295631
theorem B131551 : Blo 127788 131551 := bstep (se 1 (by rfl) ⟨98663, by rfl⟩ : syracuseStep 131551 = 197327) B197327
theorem B295415 : Blo 127788 295415 := bstep (se 1 (by rfl) ⟨221561, by rfl⟩ : syracuseStep 295415 = 443123) B443123
theorem B131631 : Blo 127788 131631 := bstep (se 1 (by rfl) ⟨98723, by rfl⟩ : syracuseStep 131631 = 197447) B197447
theorem B131675 : Blo 127788 131675 := bstep (se 1 (by rfl) ⟨98756, by rfl⟩ : syracuseStep 131675 = 197513) B197513
theorem B1114823 : Blo 127788 1114823 := bstep (se 1 (by rfl) ⟨836117, by rfl⟩ : syracuseStep 1114823 = 1672235) B1672235
theorem B197339 : Blo 127788 197339 := bstep (se 1 (by rfl) ⟨148004, by rfl⟩ : syracuseStep 197339 = 296009) B296009
theorem B557891 : Blo 127788 557891 := bstep (se 1 (by rfl) ⟨418418, by rfl⟩ : syracuseStep 557891 = 836837) B836837
theorem B492713 : Blo 127788 492713 := bstep (se 2 (by rfl) ⟨184767, by rfl⟩ : syracuseStep 492713 = 369535) B369535
theorem B296255 : Blo 127788 296255 := bstep (se 1 (by rfl) ⟨222191, by rfl⟩ : syracuseStep 296255 = 444383) B444383
theorem B657395 : Blo 127788 657395 := bstep (se 1 (by rfl) ⟨493046, by rfl⟩ : syracuseStep 657395 = 986093) B986093
theorem B526367 : Blo 127788 526367 := bstep (se 1 (by rfl) ⟨394775, by rfl⟩ : syracuseStep 526367 = 789551) B789551
theorem B657503 : Blo 127788 657503 := bstep (se 1 (by rfl) ⟨493127, by rfl⟩ : syracuseStep 657503 = 986255) B986255
theorem B1050769 : Blo 127788 1050769 := bstep (se 2 (by rfl) ⟨394038, by rfl⟩ : syracuseStep 1050769 = 788077) B788077
theorem B985607 : Blo 127788 985607 := bstep (se 1 (by rfl) ⟨739205, by rfl⟩ : syracuseStep 985607 = 1478411) B1478411
theorem B494201 : Blo 127788 494201 := bstep (se 2 (by rfl) ⟨185325, by rfl⟩ : syracuseStep 494201 = 370651) B370651
theorem B232391 : Blo 127788 232391 := bstep (se 1 (by rfl) ⟨174293, by rfl⟩ : syracuseStep 232391 = 348587) B348587
theorem B986579 : Blo 127788 986579 := bstep (se 1 (by rfl) ⟨739934, by rfl⟩ : syracuseStep 986579 = 1479869) B1479869
theorem B822791 : Blo 127788 822791 := bstep (se 1 (by rfl) ⟨617093, by rfl⟩ : syracuseStep 822791 = 1234187) B1234187
theorem B659339 : Blo 127788 659339 := bstep (se 1 (by rfl) ⟨494504, by rfl⟩ : syracuseStep 659339 = 989009) B989009
theorem B364591 : Blo 127788 364591 := bstep (se 1 (by rfl) ⟨273443, by rfl⟩ : syracuseStep 364591 = 546887) B546887
theorem B495841 : Blo 127788 495841 := bstep (se 2 (by rfl) ⟨185940, by rfl⟩ : syracuseStep 495841 = 371881) B371881
theorem B332059 : Blo 127788 332059 := bstep (se 1 (by rfl) ⟨249044, by rfl⟩ : syracuseStep 332059 = 498089) B498089
theorem B2691377 : Blo 127788 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B1413719 : Blo 127788 1413719 := bstep (se 1 (by rfl) ⟨1060289, by rfl⟩ : syracuseStep 1413719 = 2120579) B2120579
theorem B234409 : Blo 127788 234409 := bstep (se 2 (by rfl) ⟨87903, by rfl⟩ : syracuseStep 234409 = 175807) B175807
theorem B988523 : Blo 127788 988523 := bstep (se 1 (by rfl) ⟨741392, by rfl⟩ : syracuseStep 988523 = 1482785) B1482785
theorem B1512857 : Blo 127788 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B759547 : Blo 127788 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B431891 : Blo 127788 431891 := bstep (se 1 (by rfl) ⟨323918, by rfl⟩ : syracuseStep 431891 = 647837) B647837
theorem B2136145 : Blo 127788 2136145 := bstep (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) B1602109
theorem B661607 : Blo 127788 661607 := bstep (se 1 (by rfl) ⟨496205, by rfl⟩ : syracuseStep 661607 = 992411) B992411
theorem B923795 : Blo 127788 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B432755 : Blo 127788 432755 := bstep (se 1 (by rfl) ⟨324566, by rfl⟩ : syracuseStep 432755 = 649133) B649133
theorem B1121111 : Blo 127788 1121111 := bstep (se 1 (by rfl) ⟨840833, by rfl⟩ : syracuseStep 1121111 = 1681667) B1681667
theorem B1186987 : Blo 127788 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B433835 : Blo 127788 433835 := bstep (se 1 (by rfl) ⟨325376, by rfl⟩ : syracuseStep 433835 = 650753) B650753
theorem B138943 : Blo 127788 138943 := bstep (se 1 (by rfl) ⟨104207, by rfl⟩ : syracuseStep 138943 = 208415) B208415
theorem B1122173 : Blo 127788 1122173 := bstep (se 3 (by rfl) ⟨210407, by rfl⟩ : syracuseStep 1122173 = 420815) B420815
theorem B4530167 : Blo 127788 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B434429 : Blo 127788 434429 := bstep (se 3 (by rfl) ⟨81455, by rfl⟩ : syracuseStep 434429 = 162911) B162911
theorem B369107 : Blo 127788 369107 := bstep (se 1 (by rfl) ⟨276830, by rfl⟩ : syracuseStep 369107 = 553661) B553661
theorem B730093 : Blo 127788 730093 := bstep (se 3 (by rfl) ⟨136892, by rfl⟩ : syracuseStep 730093 = 273785) B273785
theorem B4302071 : Blo 127788 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B435887 : Blo 127788 435887 := bstep (se 1 (by rfl) ⟨326915, by rfl⟩ : syracuseStep 435887 = 653831) B653831
theorem B1648451 : Blo 127788 1648451 := bstep (se 1 (by rfl) ⟨1236338, by rfl⟩ : syracuseStep 1648451 = 2472677) B2472677
theorem B436751 : Blo 127788 436751 := bstep (se 1 (by rfl) ⟨327563, by rfl⟩ : syracuseStep 436751 = 655127) B655127
theorem B174683 : Blo 127788 174683 := bstep (se 1 (by rfl) ⟨131012, by rfl⟩ : syracuseStep 174683 = 262025) B262025
theorem B273871 : Blo 127788 273871 := bstep (se 1 (by rfl) ⟨205403, by rfl⟩ : syracuseStep 273871 = 410807) B410807
theorem B437831 : Blo 127788 437831 := bstep (se 1 (by rfl) ⟨328373, by rfl⟩ : syracuseStep 437831 = 656747) B656747
theorem B208927 : Blo 127788 208927 := bstep (se 1 (by rfl) ⟨156695, by rfl⟩ : syracuseStep 208927 = 313391) B313391
theorem B3911759 : Blo 127788 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B275255 : Blo 127788 275255 := bstep (se 1 (by rfl) ⟨206441, by rfl⟩ : syracuseStep 275255 = 412883) B412883
theorem B897961 : Blo 127788 897961 := bstep (se 2 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 897961 = 673471) B673471
theorem B374183 : Blo 127788 374183 := bstep (se 1 (by rfl) ⟨280637, by rfl⟩ : syracuseStep 374183 = 561275) B561275
theorem B440639 : Blo 127788 440639 := bstep (se 1 (by rfl) ⟨330479, by rfl⟩ : syracuseStep 440639 = 660959) B660959
theorem B3422537 : Blo 127788 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B1063277 : Blo 127788 1063277 := bstep (se 3 (by rfl) ⟨199364, by rfl⟩ : syracuseStep 1063277 = 398729) B398729
theorem B1063475 : Blo 127788 1063475 := bstep (se 1 (by rfl) ⟨797606, by rfl⟩ : syracuseStep 1063475 = 1595213) B1595213
theorem B1751969 : Blo 127788 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B277625 : Blo 127788 277625 := bstep (se 2 (by rfl) ⟨104109, by rfl⟩ : syracuseStep 277625 = 208219) B208219
theorem B638441 : Blo 127788 638441 := bstep (se 2 (by rfl) ⟨239415, by rfl⟩ : syracuseStep 638441 = 478831) B478831
theorem B835069 : Blo 127788 835069 := bstep (se 3 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 835069 = 313151) B313151
theorem B1097327 : Blo 127788 1097327 := bstep (se 1 (by rfl) ⟨822995, by rfl⟩ : syracuseStep 1097327 = 1645991) B1645991
theorem B933599 : Blo 127788 933599 := bstep (se 1 (by rfl) ⟨700199, by rfl⟩ : syracuseStep 933599 = 1400399) B1400399
theorem B442313 : Blo 127788 442313 := bstep (se 2 (by rfl) ⟨165867, by rfl⟩ : syracuseStep 442313 = 331735) B331735
theorem B1196005 : Blo 127788 1196005 := bstep (se 4 (by rfl) ⟨112125, by rfl⟩ : syracuseStep 1196005 = 224251) B224251
theorem B3620999 : Blo 127788 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B901625 : Blo 127788 901625 := bstep (se 2 (by rfl) ⟨338109, by rfl⟩ : syracuseStep 901625 = 676219) B676219
theorem B2114099 : Blo 127788 2114099 := bstep (se 1 (by rfl) ⟨1585574, by rfl⟩ : syracuseStep 2114099 = 3171149) B3171149
theorem B148207 : Blo 127788 148207 := bstep (se 1 (by rfl) ⟨111155, by rfl⟩ : syracuseStep 148207 = 222311) B222311
theorem B3130265 : Blo 127788 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B247207 : Blo 127788 247207 := bstep (se 1 (by rfl) ⟨185405, by rfl⟩ : syracuseStep 247207 = 370811) B370811
theorem B443879 : Blo 127788 443879 := bstep (se 1 (by rfl) ⟨332909, by rfl⟩ : syracuseStep 443879 = 665819) B665819
theorem B346295 : Blo 127788 346295 := bstep (se 1 (by rfl) ⟨259721, by rfl⟩ : syracuseStep 346295 = 519443) B519443
theorem B2672891 : Blo 127788 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B182683 : Blo 127788 182683 := bstep (se 1 (by rfl) ⟨137012, by rfl⟩ : syracuseStep 182683 = 274025) B274025
theorem B2248235 : Blo 127788 2248235 := bstep (se 1 (by rfl) ⟨1686176, by rfl⟩ : syracuseStep 2248235 = 3372353) B3372353
theorem B741257 : Blo 127788 741257 := bstep (se 2 (by rfl) ⟨277971, by rfl⟩ : syracuseStep 741257 = 555943) B555943
theorem B741575 : Blo 127788 741575 := bstep (se 1 (by rfl) ⟨556181, by rfl⟩ : syracuseStep 741575 = 1112363) B1112363
theorem B5624417 : Blo 127788 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B742031 : Blo 127788 742031 := bstep (se 1 (by rfl) ⟨556523, by rfl⟩ : syracuseStep 742031 = 1113047) B1113047
theorem B218153 : Blo 127788 218153 := bstep (se 2 (by rfl) ⟨81807, by rfl⟩ : syracuseStep 218153 = 163615) B163615
theorem B709955 : Blo 127788 709955 := bstep (se 1 (by rfl) ⟨532466, by rfl⟩ : syracuseStep 709955 = 1064933) B1064933
theorem B13981081 : Blo 127788 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B19355041 : Blo 127788 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B317351 : Blo 127788 317351 := bstep (se 1 (by rfl) ⟨238013, by rfl⟩ : syracuseStep 317351 = 476027) B476027
theorem B547145 : Blo 127788 547145 := bstep (se 2 (by rfl) ⟨205179, by rfl⟩ : syracuseStep 547145 = 410359) B410359
theorem B940403 : Blo 127788 940403 := bstep (se 1 (by rfl) ⟨705302, by rfl⟩ : syracuseStep 940403 = 1410605) B1410605
theorem B416573 : Blo 127788 416573 := bstep (se 3 (by rfl) ⟨78107, by rfl⟩ : syracuseStep 416573 = 156215) B156215
theorem B220153 : Blo 127788 220153 := bstep (se 2 (by rfl) ⟨82557, by rfl⟩ : syracuseStep 220153 = 165115) B165115
theorem B2186813 : Blo 127788 2186813 := bstep (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) B820055
theorem B2186999 : Blo 127788 2186999 := bstep (se 1 (by rfl) ⟨1640249, by rfl⟩ : syracuseStep 2186999 = 3280499) B3280499
theorem B221339 : Blo 127788 221339 := bstep (se 1 (by rfl) ⟨166004, by rfl⟩ : syracuseStep 221339 = 332009) B332009
theorem B221359 : Blo 127788 221359 := bstep (se 1 (by rfl) ⟨166019, by rfl⟩ : syracuseStep 221359 = 332039) B332039
theorem B1401785 : Blo 127788 1401785 := bstep (se 2 (by rfl) ⟨525669, by rfl⟩ : syracuseStep 1401785 = 1051339) B1051339
theorem B287855 : Blo 127788 287855 := bstep (se 1 (by rfl) ⟨215891, by rfl⟩ : syracuseStep 287855 = 431783) B431783
theorem B1107715 : Blo 127788 1107715 := bstep (se 1 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 1107715 = 1661573) B1661573
theorem B2385949 : Blo 127788 2385949 := bstep (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) B894731
theorem B846281 : Blo 127788 846281 := bstep (se 2 (by rfl) ⟨317355, by rfl⟩ : syracuseStep 846281 = 634711) B634711
theorem B649943 : Blo 127788 649943 := bstep (se 1 (by rfl) ⟨487457, by rfl⟩ : syracuseStep 649943 = 974915) B974915
theorem B945017 : Blo 127788 945017 := bstep (se 2 (by rfl) ⟨354381, by rfl⟩ : syracuseStep 945017 = 708763) B708763
theorem B1076141 : Blo 127788 1076141 := bstep (se 3 (by rfl) ⟨201776, by rfl⟩ : syracuseStep 1076141 = 403553) B403553
theorem B290105 : Blo 127788 290105 := bstep (se 2 (by rfl) ⟨108789, by rfl⟩ : syracuseStep 290105 = 217579) B217579
theorem B487079 : Blo 127788 487079 := bstep (se 1 (by rfl) ⟨365309, by rfl⟩ : syracuseStep 487079 = 730619) B730619
theorem B1240919 : Blo 127788 1240919 := bstep (se 1 (by rfl) ⟨930689, by rfl⟩ : syracuseStep 1240919 = 1861379) B1861379
theorem B290771 : Blo 127788 290771 := bstep (se 1 (by rfl) ⟨218078, by rfl⟩ : syracuseStep 290771 = 436157) B436157
theorem B323615 : Blo 127788 323615 := bstep (se 1 (by rfl) ⟨242711, by rfl⟩ : syracuseStep 323615 = 485423) B485423
theorem B553175 : Blo 127788 553175 := bstep (se 1 (by rfl) ⟨414881, by rfl⟩ : syracuseStep 553175 = 829763) B829763
theorem B291113 : Blo 127788 291113 := bstep (se 2 (by rfl) ⟨109167, by rfl⟩ : syracuseStep 291113 = 218335) B218335
theorem B488051 : Blo 127788 488051 := bstep (se 1 (by rfl) ⟨366038, by rfl⟩ : syracuseStep 488051 = 732077) B732077
theorem B324263 : Blo 127788 324263 := bstep (se 1 (by rfl) ⟨243197, by rfl⟩ : syracuseStep 324263 = 486395) B486395
theorem B127815 : Blo 127788 127815 := bstep (se 1 (by rfl) ⟨95861, by rfl⟩ : syracuseStep 127815 = 191723) B191723
theorem B291689 : Blo 127788 291689 := bstep (se 2 (by rfl) ⟨109383, by rfl⟩ : syracuseStep 291689 = 218767) B218767
theorem B553979 : Blo 127788 553979 := bstep (se 1 (by rfl) ⟨415484, by rfl⟩ : syracuseStep 553979 = 830969) B830969
theorem B128255 : Blo 127788 128255 := bstep (se 1 (by rfl) ⟨96191, by rfl⟩ : syracuseStep 128255 = 192383) B192383
theorem B193961 : Blo 127788 193961 := bstep (se 2 (by rfl) ⟨72735, by rfl⟩ : syracuseStep 193961 = 145471) B145471
theorem B128479 : Blo 127788 128479 := bstep (se 1 (by rfl) ⟨96359, by rfl⟩ : syracuseStep 128479 = 192719) B192719
theorem B194015 : Blo 127788 194015 := bstep (se 1 (by rfl) ⟨145511, by rfl⟩ : syracuseStep 194015 = 291023) B291023
theorem B128559 : Blo 127788 128559 := bstep (se 1 (by rfl) ⟨96419, by rfl⟩ : syracuseStep 128559 = 192839) B192839
theorem B128871 : Blo 127788 128871 := bstep (se 1 (by rfl) ⟨96653, by rfl⟩ : syracuseStep 128871 = 193307) B193307
theorem B522215 : Blo 127788 522215 := bstep (se 1 (by rfl) ⟨391661, by rfl⟩ : syracuseStep 522215 = 783323) B783323
theorem B129055 : Blo 127788 129055 := bstep (se 1 (by rfl) ⟨96791, by rfl⟩ : syracuseStep 129055 = 193583) B193583
theorem B129087 : Blo 127788 129087 := bstep (se 1 (by rfl) ⟨96815, by rfl⟩ : syracuseStep 129087 = 193631) B193631
theorem B129127 : Blo 127788 129127 := bstep (se 1 (by rfl) ⟨96845, by rfl⟩ : syracuseStep 129127 = 193691) B193691
theorem B194663 : Blo 127788 194663 := bstep (se 1 (by rfl) ⟨145997, by rfl⟩ : syracuseStep 194663 = 291995) B291995
theorem B129135 : Blo 127788 129135 := bstep (se 1 (by rfl) ⟨96851, by rfl⟩ : syracuseStep 129135 = 193703) B193703
theorem B129583 : Blo 127788 129583 := bstep (se 1 (by rfl) ⟨97187, by rfl⟩ : syracuseStep 129583 = 194375) B194375
theorem B1145507 : Blo 127788 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B129703 : Blo 127788 129703 := bstep (se 1 (by rfl) ⟨97277, by rfl⟩ : syracuseStep 129703 = 194555) B194555
theorem B129743 : Blo 127788 129743 := bstep (se 1 (by rfl) ⟨97307, by rfl⟩ : syracuseStep 129743 = 194615) B194615
theorem B981719 : Blo 127788 981719 := bstep (se 1 (by rfl) ⟨736289, by rfl⟩ : syracuseStep 981719 = 1472579) B1472579
theorem B129787 : Blo 127788 129787 := bstep (se 1 (by rfl) ⟨97340, by rfl⟩ : syracuseStep 129787 = 194681) B194681
theorem B129823 : Blo 127788 129823 := bstep (se 1 (by rfl) ⟨97367, by rfl⟩ : syracuseStep 129823 = 194735) B194735
theorem B293687 : Blo 127788 293687 := bstep (se 1 (by rfl) ⟨220265, by rfl⟩ : syracuseStep 293687 = 440531) B440531
theorem B129983 : Blo 127788 129983 := bstep (se 1 (by rfl) ⟨97487, by rfl⟩ : syracuseStep 129983 = 194975) B194975
theorem B130043 : Blo 127788 130043 := bstep (se 1 (by rfl) ⟨97532, by rfl⟩ : syracuseStep 130043 = 195065) B195065
theorem B1244335 : Blo 127788 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B195881 : Blo 127788 195881 := bstep (se 2 (by rfl) ⟨73455, by rfl⟩ : syracuseStep 195881 = 146911) B146911
theorem B130367 : Blo 127788 130367 := bstep (se 1 (by rfl) ⟨97775, by rfl⟩ : syracuseStep 130367 = 195551) B195551
theorem B130407 : Blo 127788 130407 := bstep (se 1 (by rfl) ⟨97805, by rfl⟩ : syracuseStep 130407 = 195611) B195611
theorem B2489899 : Blo 127788 2489899 := bstep (se 1 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 2489899 = 3734849) B3734849
theorem B130663 : Blo 127788 130663 := bstep (se 1 (by rfl) ⟨97997, by rfl⟩ : syracuseStep 130663 = 195995) B195995
theorem B196199 : Blo 127788 196199 := bstep (se 1 (by rfl) ⟨147149, by rfl⟩ : syracuseStep 196199 = 294299) B294299
theorem B130715 : Blo 127788 130715 := bstep (se 1 (by rfl) ⟨98036, by rfl⟩ : syracuseStep 130715 = 196073) B196073
theorem B130719 : Blo 127788 130719 := bstep (se 1 (by rfl) ⟨98039, by rfl⟩ : syracuseStep 130719 = 196079) B196079
theorem B130811 : Blo 127788 130811 := bstep (se 1 (by rfl) ⟨98108, by rfl⟩ : syracuseStep 130811 = 196217) B196217
theorem B294767 : Blo 127788 294767 := bstep (se 1 (by rfl) ⟨221075, by rfl⟩ : syracuseStep 294767 = 442151) B442151
theorem B130943 : Blo 127788 130943 := bstep (se 1 (by rfl) ⟨98207, by rfl⟩ : syracuseStep 130943 = 196415) B196415
theorem B130975 : Blo 127788 130975 := bstep (se 1 (by rfl) ⟨98231, by rfl⟩ : syracuseStep 130975 = 196463) B196463
theorem B327635 : Blo 127788 327635 := bstep (se 1 (by rfl) ⟨245726, by rfl⟩ : syracuseStep 327635 = 491453) B491453
theorem B196703 : Blo 127788 196703 := bstep (se 1 (by rfl) ⟨147527, by rfl⟩ : syracuseStep 196703 = 295055) B295055
theorem B295145 : Blo 127788 295145 := bstep (se 2 (by rfl) ⟨110679, by rfl⟩ : syracuseStep 295145 = 221359) B221359
theorem B131311 : Blo 127788 131311 := bstep (se 1 (by rfl) ⟨98483, by rfl⟩ : syracuseStep 131311 = 196967) B196967
theorem B131391 : Blo 127788 131391 := bstep (se 1 (by rfl) ⟨98543, by rfl⟩ : syracuseStep 131391 = 197087) B197087
theorem B196943 : Blo 127788 196943 := bstep (se 1 (by rfl) ⟨147707, by rfl⟩ : syracuseStep 196943 = 295415) B295415
theorem B1409399 : Blo 127788 1409399 := bstep (se 1 (by rfl) ⟨1057049, by rfl⟩ : syracuseStep 1409399 = 2114099) B2114099
theorem B131559 : Blo 127788 131559 := bstep (se 1 (by rfl) ⟨98669, by rfl⟩ : syracuseStep 131559 = 197339) B197339
theorem B328475 : Blo 127788 328475 := bstep (se 1 (by rfl) ⟨246356, by rfl⟩ : syracuseStep 328475 = 492713) B492713
theorem B197609 : Blo 127788 197609 := bstep (se 2 (by rfl) ⟨74103, by rfl⟩ : syracuseStep 197609 = 148207) B148207
theorem B295919 : Blo 127788 295919 := bstep (se 1 (by rfl) ⟨221939, by rfl⟩ : syracuseStep 295919 = 443879) B443879
theorem B230863 : Blo 127788 230863 := bstep (se 1 (by rfl) ⟨173147, by rfl⟩ : syracuseStep 230863 = 346295) B346295
theorem B657071 : Blo 127788 657071 := bstep (se 1 (by rfl) ⟨492803, by rfl⟩ : syracuseStep 657071 = 985607) B985607
theorem B329467 : Blo 127788 329467 := bstep (se 1 (by rfl) ⟨247100, by rfl⟩ : syracuseStep 329467 = 494201) B494201
theorem B329609 : Blo 127788 329609 := bstep (se 2 (by rfl) ⟨123603, by rfl⟩ : syracuseStep 329609 = 247207) B247207
theorem B657719 : Blo 127788 657719 := bstep (se 1 (by rfl) ⟨493289, by rfl⟩ : syracuseStep 657719 = 986579) B986579
theorem B1476953 : Blo 127788 1476953 := bstep (se 2 (by rfl) ⟨553857, by rfl⟩ : syracuseStep 1476953 = 1107715) B1107715
theorem B494171 : Blo 127788 494171 := bstep (se 1 (by rfl) ⟨370628, by rfl⟩ : syracuseStep 494171 = 741257) B741257
theorem B3181265 : Blo 127788 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B494383 : Blo 127788 494383 := bstep (se 1 (by rfl) ⟨370787, by rfl⟩ : syracuseStep 494383 = 741575) B741575
theorem B494687 : Blo 127788 494687 := bstep (se 1 (by rfl) ⟨371015, by rfl⟩ : syracuseStep 494687 = 742031) B742031
theorem B790013 : Blo 127788 790013 := bstep (se 3 (by rfl) ⟨148127, by rfl⟩ : syracuseStep 790013 = 296255) B296255
theorem B659015 : Blo 127788 659015 := bstep (se 1 (by rfl) ⟨494261, by rfl⟩ : syracuseStep 659015 = 988523) B988523
theorem B4034285 : Blo 127788 4034285 := bstep (se 3 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 4034285 = 1512857) B1512857
theorem B364763 : Blo 127788 364763 := bstep (se 1 (by rfl) ⟨273572, by rfl⟩ : syracuseStep 364763 = 547145) B547145
theorem B626935 : Blo 127788 626935 := bstep (se 1 (by rfl) ⟨470201, by rfl⟩ : syracuseStep 626935 = 940403) B940403
theorem B365161 : Blo 127788 365161 := bstep (se 2 (by rfl) ⟨136935, by rfl⟩ : syracuseStep 365161 = 273871) B273871
theorem B3020111 : Blo 127788 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B661121 : Blo 127788 661121 := bstep (se 2 (by rfl) ⟨247920, by rfl⟩ : syracuseStep 661121 = 495841) B495841
theorem B465821 : Blo 127788 465821 := bstep (se 3 (by rfl) ⟨87341, by rfl⟩ : syracuseStep 465821 = 174683) B174683
theorem B564187 : Blo 127788 564187 := bstep (se 1 (by rfl) ⟨423140, by rfl⟩ : syracuseStep 564187 = 846281) B846281
theorem B3054685 : Blo 127788 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B433295 : Blo 127788 433295 := bstep (se 1 (by rfl) ⟨324971, by rfl⟩ : syracuseStep 433295 = 649943) B649943
theorem B630011 : Blo 127788 630011 := bstep (se 1 (by rfl) ⟨472508, by rfl⟩ : syracuseStep 630011 = 945017) B945017
theorem B827279 : Blo 127788 827279 := bstep (se 1 (by rfl) ⟨620459, by rfl⟩ : syracuseStep 827279 = 1240919) B1240919
theorem B368783 : Blo 127788 368783 := bstep (se 1 (by rfl) ⟨276587, by rfl⟩ : syracuseStep 368783 = 553175) B553175
theorem B369319 : Blo 127788 369319 := bstep (se 1 (by rfl) ⟨276989, by rfl⟩ : syracuseStep 369319 = 553979) B553979
theorem B1582649 : Blo 127788 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B3319865 : Blo 127788 3319865 := bstep (se 2 (by rfl) ⟨1244949, by rfl⟩ : syracuseStep 3319865 = 2489899) B2489899
theorem B731551 : Blo 127788 731551 := bstep (se 1 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 731551 = 1097327) B1097327
theorem B371927 : Blo 127788 371927 := bstep (se 1 (by rfl) ⟨278945, by rfl⟩ : syracuseStep 371927 = 557891) B557891
theorem B2404333 : Blo 127788 2404333 := bstep (se 3 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 2404333 = 901625) B901625
theorem B438263 : Blo 127788 438263 := bstep (se 1 (by rfl) ⟨328697, by rfl⟩ : syracuseStep 438263 = 657395) B657395
theorem B438335 : Blo 127788 438335 := bstep (se 1 (by rfl) ⟨328751, by rfl⟩ : syracuseStep 438335 = 657503) B657503
theorem B1781927 : Blo 127788 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B439559 : Blo 127788 439559 := bstep (se 1 (by rfl) ⟨329669, by rfl⟩ : syracuseStep 439559 = 659339) B659339
theorem B3749611 : Blo 127788 3749611 := bstep (se 1 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 3749611 = 5624417) B5624417
theorem B243577 : Blo 127788 243577 := bstep (se 2 (by rfl) ⟨91341, by rfl⟩ : syracuseStep 243577 = 182683) B182683
theorem B145435 : Blo 127788 145435 := bstep (se 1 (by rfl) ⟨109076, by rfl⟩ : syracuseStep 145435 = 218153) B218153
theorem B473303 : Blo 127788 473303 := bstep (se 1 (by rfl) ⟨354977, by rfl⟩ : syracuseStep 473303 = 709955) B709955
theorem B211567 : Blo 127788 211567 := bstep (se 1 (by rfl) ⟨158675, by rfl⟩ : syracuseStep 211567 = 317351) B317351
theorem B441071 : Blo 127788 441071 := bstep (se 1 (by rfl) ⟨330803, by rfl⟩ : syracuseStep 441071 = 661607) B661607
theorem B277715 : Blo 127788 277715 := bstep (se 1 (by rfl) ⟨208286, by rfl⟩ : syracuseStep 277715 = 416573) B416573
theorem B1457875 : Blo 127788 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B1457999 : Blo 127788 1457999 := bstep (se 1 (by rfl) ⟨1093499, by rfl⟩ : syracuseStep 1457999 = 2186999) B2186999
theorem B278569 : Blo 127788 278569 := bstep (se 2 (by rfl) ⟨104463, by rfl⟩ : syracuseStep 278569 = 208927) B208927
theorem B147559 : Blo 127788 147559 := bstep (se 1 (by rfl) ⟨110669, by rfl⟩ : syracuseStep 147559 = 221339) B221339
theorem B246071 : Blo 127788 246071 := bstep (se 1 (by rfl) ⟨184553, by rfl⟩ : syracuseStep 246071 = 369107) B369107
theorem B442745 : Blo 127788 442745 := bstep (se 2 (by rfl) ⟨166029, by rfl⟩ : syracuseStep 442745 = 332059) B332059
theorem B934523 : Blo 127788 934523 := bstep (se 1 (by rfl) ⟨700892, by rfl⟩ : syracuseStep 934523 = 1401785) B1401785
theorem B2868047 : Blo 127788 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B1098967 : Blo 127788 1098967 := bstep (se 1 (by rfl) ⟨824225, by rfl⟩ : syracuseStep 1098967 = 1648451) B1648451
theorem B312545 : Blo 127788 312545 := bstep (se 2 (by rfl) ⟨117204, by rfl⟩ : syracuseStep 312545 = 234409) B234409
theorem B1197281 : Blo 127788 1197281 := bstep (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) B897961
theorem B25806721 : Blo 127788 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B215743 : Blo 127788 215743 := bstep (se 1 (by rfl) ⟨161807, by rfl⟩ : syracuseStep 215743 = 323615) B323615
theorem B2607839 : Blo 127788 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B740333 : Blo 127788 740333 := bstep (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) B277625
theorem B216175 : Blo 127788 216175 := bstep (se 1 (by rfl) ⟨162131, by rfl⟩ : syracuseStep 216175 = 324263) B324263
theorem B183503 : Blo 127788 183503 := bstep (se 1 (by rfl) ⟨137627, by rfl⟩ : syracuseStep 183503 = 275255) B275255
theorem B249455 : Blo 127788 249455 := bstep (se 1 (by rfl) ⟨187091, by rfl⟩ : syracuseStep 249455 = 374183) B374183
theorem B4050917 : Blo 127788 4050917 := bstep (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) B759547
theorem B348143 : Blo 127788 348143 := bstep (se 1 (by rfl) ⟨261107, by rfl⟩ : syracuseStep 348143 = 522215) B522215
theorem B2281691 : Blo 127788 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B1659113 : Blo 127788 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B708851 : Blo 127788 708851 := bstep (se 1 (by rfl) ⟨531638, by rfl⟩ : syracuseStep 708851 = 1063277) B1063277
theorem B708983 : Blo 127788 708983 := bstep (se 1 (by rfl) ⟨531737, by rfl⟩ : syracuseStep 708983 = 1063475) B1063475
theorem B1167979 : Blo 127788 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B185257 : Blo 127788 185257 := bstep (se 2 (by rfl) ⟨69471, by rfl⟩ : syracuseStep 185257 = 138943) B138943
theorem B1594673 : Blo 127788 1594673 := bstep (se 2 (by rfl) ⟨598002, by rfl⟩ : syracuseStep 1594673 = 1196005) B1196005
theorem B218423 : Blo 127788 218423 := bstep (se 1 (by rfl) ⟨163817, by rfl⟩ : syracuseStep 218423 = 327635) B327635
theorem B2413999 : Blo 127788 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B743215 : Blo 127788 743215 := bstep (se 1 (by rfl) ⟨557411, by rfl⟩ : syracuseStep 743215 = 1114823) B1114823
theorem B2086843 : Blo 127788 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B973457 : Blo 127788 973457 := bstep (se 2 (by rfl) ⟨365046, by rfl⟩ : syracuseStep 973457 = 730093) B730093
theorem B350911 : Blo 127788 350911 := bstep (se 1 (by rfl) ⟨263183, by rfl⟩ : syracuseStep 350911 = 526367) B526367
theorem B154927 : Blo 127788 154927 := bstep (se 1 (by rfl) ⟨116195, by rfl⟩ : syracuseStep 154927 = 232391) B232391
theorem B548527 : Blo 127788 548527 := bstep (se 1 (by rfl) ⟨411395, by rfl⟩ : syracuseStep 548527 = 822791) B822791
theorem B1498823 : Blo 127788 1498823 := bstep (se 1 (by rfl) ⟨1124117, by rfl⟩ : syracuseStep 1498823 = 2248235) B2248235
theorem B1401025 : Blo 127788 1401025 := bstep (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) B1050769
theorem B1794251 : Blo 127788 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B942479 : Blo 127788 942479 := bstep (se 1 (by rfl) ⟨706859, by rfl⟩ : syracuseStep 942479 = 1413719) B1413719
theorem B287927 : Blo 127788 287927 := bstep (se 1 (by rfl) ⟨215945, by rfl⟩ : syracuseStep 287927 = 431891) B431891
theorem B615863 : Blo 127788 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B288503 : Blo 127788 288503 := bstep (se 1 (by rfl) ⟨216377, by rfl⟩ : syracuseStep 288503 = 432755) B432755
theorem B747407 : Blo 127788 747407 := bstep (se 1 (by rfl) ⟨560555, by rfl⟩ : syracuseStep 747407 = 1121111) B1121111
theorem B289223 : Blo 127788 289223 := bstep (se 1 (by rfl) ⟨216917, by rfl⟩ : syracuseStep 289223 = 433835) B433835
theorem B748115 : Blo 127788 748115 := bstep (se 1 (by rfl) ⟨561086, by rfl⟩ : syracuseStep 748115 = 1122173) B1122173
theorem B486121 : Blo 127788 486121 := bstep (se 2 (by rfl) ⟨182295, by rfl⟩ : syracuseStep 486121 = 364591) B364591
theorem B289619 : Blo 127788 289619 := bstep (se 1 (by rfl) ⟨217214, by rfl⟩ : syracuseStep 289619 = 434429) B434429
theorem B191903 : Blo 127788 191903 := bstep (se 1 (by rfl) ⟨143927, by rfl⟩ : syracuseStep 191903 = 287855) B287855
theorem B290591 : Blo 127788 290591 := bstep (se 1 (by rfl) ⟨217943, by rfl⟩ : syracuseStep 290591 = 435887) B435887
theorem B291167 : Blo 127788 291167 := bstep (se 1 (by rfl) ⟨218375, by rfl⟩ : syracuseStep 291167 = 436751) B436751
theorem B18641441 : Blo 127788 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B717427 : Blo 127788 717427 := bstep (se 1 (by rfl) ⟨538070, by rfl⟩ : syracuseStep 717427 = 1076141) B1076141
theorem B193403 : Blo 127788 193403 := bstep (se 1 (by rfl) ⟨145052, by rfl⟩ : syracuseStep 193403 = 290105) B290105
theorem B291887 : Blo 127788 291887 := bstep (se 1 (by rfl) ⟨218915, by rfl⟩ : syracuseStep 291887 = 437831) B437831
theorem B324719 : Blo 127788 324719 := bstep (se 1 (by rfl) ⟨243539, by rfl⟩ : syracuseStep 324719 = 487079) B487079
theorem B193847 : Blo 127788 193847 := bstep (se 1 (by rfl) ⟨145385, by rfl⟩ : syracuseStep 193847 = 290771) B290771
theorem B2848193 : Blo 127788 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B194075 : Blo 127788 194075 := bstep (se 1 (by rfl) ⟨145556, by rfl⟩ : syracuseStep 194075 = 291113) B291113
theorem B325367 : Blo 127788 325367 := bstep (se 1 (by rfl) ⟨244025, by rfl⟩ : syracuseStep 325367 = 488051) B488051
theorem B194459 : Blo 127788 194459 := bstep (se 1 (by rfl) ⟨145844, by rfl⟩ : syracuseStep 194459 = 291689) B291689
theorem B129307 : Blo 127788 129307 := bstep (se 1 (by rfl) ⟨96980, by rfl⟩ : syracuseStep 129307 = 193961) B193961
theorem B129343 : Blo 127788 129343 := bstep (se 1 (by rfl) ⟨97007, by rfl⟩ : syracuseStep 129343 = 194015) B194015
theorem B293537 : Blo 127788 293537 := bstep (se 2 (by rfl) ⟨110076, by rfl⟩ : syracuseStep 293537 = 220153) B220153
theorem B129775 : Blo 127788 129775 := bstep (se 1 (by rfl) ⟨97331, by rfl⟩ : syracuseStep 129775 = 194663) B194663
theorem B293759 : Blo 127788 293759 := bstep (se 1 (by rfl) ⟨220319, by rfl⟩ : syracuseStep 293759 = 440639) B440639
theorem B654479 : Blo 127788 654479 := bstep (se 1 (by rfl) ⟨490859, by rfl⟩ : syracuseStep 654479 = 981719) B981719
theorem B195791 : Blo 127788 195791 := bstep (se 1 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 195791 = 293687) B293687
theorem B1113425 : Blo 127788 1113425 := bstep (se 2 (by rfl) ⟨417534, by rfl⟩ : syracuseStep 1113425 = 835069) B835069
theorem B130587 : Blo 127788 130587 := bstep (se 1 (by rfl) ⟨97940, by rfl⟩ : syracuseStep 130587 = 195881) B195881
theorem B425627 : Blo 127788 425627 := bstep (se 1 (by rfl) ⟨319220, by rfl⟩ : syracuseStep 425627 = 638441) B638441
theorem B130799 : Blo 127788 130799 := bstep (se 1 (by rfl) ⟨98099, by rfl⟩ : syracuseStep 130799 = 196199) B196199
theorem B622399 : Blo 127788 622399 := bstep (se 1 (by rfl) ⟨466799, by rfl⟩ : syracuseStep 622399 = 933599) B933599
theorem B196511 : Blo 127788 196511 := bstep (se 1 (by rfl) ⟨147383, by rfl⟩ : syracuseStep 196511 = 294767) B294767
theorem B294875 : Blo 127788 294875 := bstep (se 1 (by rfl) ⟨221156, by rfl⟩ : syracuseStep 294875 = 442313) B442313
theorem B131135 : Blo 127788 131135 := bstep (se 1 (by rfl) ⟨98351, by rfl⟩ : syracuseStep 131135 = 196703) B196703
theorem B196745 : Blo 127788 196745 := bstep (se 2 (by rfl) ⟨73779, by rfl⟩ : syracuseStep 196745 = 147559) B147559
theorem B196763 : Blo 127788 196763 := bstep (se 1 (by rfl) ⟨147572, by rfl⟩ : syracuseStep 196763 = 295145) B295145
theorem B164047 : Blo 127788 164047 := bstep (se 1 (by rfl) ⟨123035, by rfl⟩ : syracuseStep 164047 = 246071) B246071
theorem B131295 : Blo 127788 131295 := bstep (se 1 (by rfl) ⟨98471, by rfl⟩ : syracuseStep 131295 = 196943) B196943
theorem B295163 : Blo 127788 295163 := bstep (se 1 (by rfl) ⟨221372, by rfl⟩ : syracuseStep 295163 = 442745) B442745
theorem B1868033 : Blo 127788 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B623015 : Blo 127788 623015 := bstep (se 1 (by rfl) ⟨467261, by rfl⟩ : syracuseStep 623015 = 934523) B934523
theorem B131739 : Blo 127788 131739 := bstep (se 1 (by rfl) ⟨98804, by rfl⟩ : syracuseStep 131739 = 197609) B197609
theorem B197279 : Blo 127788 197279 := bstep (se 1 (by rfl) ⟨147959, by rfl⟩ : syracuseStep 197279 = 295919) B295919
theorem B492425 : Blo 127788 492425 := bstep (se 2 (by rfl) ⟨184659, by rfl⟩ : syracuseStep 492425 = 369319) B369319
theorem B984635 : Blo 127788 984635 := bstep (se 1 (by rfl) ⟨738476, by rfl⟩ : syracuseStep 984635 = 1476953) B1476953
theorem B329447 : Blo 127788 329447 := bstep (se 1 (by rfl) ⟨247085, by rfl⟩ : syracuseStep 329447 = 494171) B494171
theorem B1738559 : Blo 127788 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B329791 : Blo 127788 329791 := bstep (se 1 (by rfl) ⟨247343, by rfl⟩ : syracuseStep 329791 = 494687) B494687
theorem B526675 : Blo 127788 526675 := bstep (se 1 (by rfl) ⟨395006, by rfl⟩ : syracuseStep 526675 = 790013) B790013
theorem B166303 : Blo 127788 166303 := bstep (se 1 (by rfl) ⟨124727, by rfl⟩ : syracuseStep 166303 = 249455) B249455
theorem B2689523 : Blo 127788 2689523 := bstep (se 1 (by rfl) ⟨2017142, by rfl⟩ : syracuseStep 2689523 = 4034285) B4034285
theorem B34408961 : Blo 127788 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B1871525 : Blo 127788 1871525 := bstep (se 4 (by rfl) ⟨175455, by rfl⟩ : syracuseStep 1871525 = 350911) B350911
theorem B659177 : Blo 127788 659177 := bstep (se 2 (by rfl) ⟨247191, by rfl⟩ : syracuseStep 659177 = 494383) B494383
theorem B1642301 : Blo 127788 1642301 := bstep (se 3 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 1642301 = 615863) B615863
theorem B988037 : Blo 127788 988037 := bstep (se 4 (by rfl) ⟨92628, by rfl⟩ : syracuseStep 988037 = 185257) B185257
theorem B628319 : Blo 127788 628319 := bstep (se 1 (by rfl) ⟨471239, by rfl⟩ : syracuseStep 628319 = 942479) B942479
theorem B956569 : Blo 127788 956569 := bstep (se 2 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 956569 = 717427) B717427
theorem B1055099 : Blo 127788 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B498271 : Blo 127788 498271 := bstep (se 1 (by rfl) ⟨373703, by rfl⟩ : syracuseStep 498271 = 747407) B747407
theorem B498743 : Blo 127788 498743 := bstep (se 1 (by rfl) ⟨374057, by rfl⟩ : syracuseStep 498743 = 748115) B748115
theorem B3218665 : Blo 127788 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B990953 : Blo 127788 990953 := bstep (se 2 (by rfl) ⟨371607, by rfl⟩ : syracuseStep 990953 = 743215) B743215
theorem B1974221 : Blo 127788 1974221 := bstep (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) B740333
theorem B1187951 : Blo 127788 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B12427627 : Blo 127788 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B4072913 : Blo 127788 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B206569 : Blo 127788 206569 := bstep (se 2 (by rfl) ⟨77463, by rfl⟩ : syracuseStep 206569 = 154927) B154927
theorem B436319 : Blo 127788 436319 := bstep (se 1 (by rfl) ⟨327239, by rfl⟩ : syracuseStep 436319 = 654479) B654479
theorem B731369 : Blo 127788 731369 := bstep (se 2 (by rfl) ⟨274263, by rfl⟩ : syracuseStep 731369 = 548527) B548527
theorem B1943833 : Blo 127788 1943833 := bstep (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) B1457875
theorem B829865 : Blo 127788 829865 := bstep (se 2 (by rfl) ⟨311199, by rfl⟩ : syracuseStep 829865 = 622399) B622399
theorem B3713525 : Blo 127788 3713525 := bstep (se 5 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 3713525 = 348143) B348143
theorem B1485701 : Blo 127788 1485701 := bstep (se 4 (by rfl) ⟨139284, by rfl⟩ : syracuseStep 1485701 = 278569) B278569
theorem B1912031 : Blo 127788 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B208363 : Blo 127788 208363 := bstep (se 1 (by rfl) ⟨156272, by rfl⟩ : syracuseStep 208363 = 312545) B312545
theorem B798187 : Blo 127788 798187 := bstep (se 1 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 798187 = 1197281) B1197281
theorem B438047 : Blo 127788 438047 := bstep (se 1 (by rfl) ⟨328535, by rfl⟩ : syracuseStep 438047 = 657071) B657071
theorem B438479 : Blo 127788 438479 := bstep (se 1 (by rfl) ⟨328859, by rfl⟩ : syracuseStep 438479 = 657719) B657719
theorem B307817 : Blo 127788 307817 := bstep (se 2 (by rfl) ⟨115431, by rfl⟩ : syracuseStep 307817 = 230863) B230863
theorem B439289 : Blo 127788 439289 := bstep (se 2 (by rfl) ⟨164733, by rfl⟩ : syracuseStep 439289 = 329467) B329467
theorem B439343 : Blo 127788 439343 := bstep (se 1 (by rfl) ⟨329507, by rfl⟩ : syracuseStep 439343 = 659015) B659015
theorem B2700611 : Blo 127788 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B243175 : Blo 127788 243175 := bstep (se 1 (by rfl) ⟨182381, by rfl⟩ : syracuseStep 243175 = 364763) B364763
theorem B1521127 : Blo 127788 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B472567 : Blo 127788 472567 := bstep (se 1 (by rfl) ⟨354425, by rfl⟩ : syracuseStep 472567 = 708851) B708851
theorem B472655 : Blo 127788 472655 := bstep (se 1 (by rfl) ⟨354491, by rfl⟩ : syracuseStep 472655 = 708983) B708983
theorem B833453 : Blo 127788 833453 := bstep (se 3 (by rfl) ⟨156272, by rfl⟩ : syracuseStep 833453 = 312545) B312545
theorem B1063115 : Blo 127788 1063115 := bstep (se 1 (by rfl) ⟨797336, by rfl⟩ : syracuseStep 1063115 = 1594673) B1594673
theorem B145615 : Blo 127788 145615 := bstep (se 1 (by rfl) ⟨109211, by rfl⟩ : syracuseStep 145615 = 218423) B218423
theorem B2013407 : Blo 127788 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B440747 : Blo 127788 440747 := bstep (se 1 (by rfl) ⟨330560, by rfl⟩ : syracuseStep 440747 = 661121) B661121
theorem B310547 : Blo 127788 310547 := bstep (se 1 (by rfl) ⟨232910, by rfl⟩ : syracuseStep 310547 = 465821) B465821
theorem B999215 : Blo 127788 999215 := bstep (se 1 (by rfl) ⟨749411, by rfl⟩ : syracuseStep 999215 = 1498823) B1498823
theorem B245855 : Blo 127788 245855 := bstep (se 1 (by rfl) ⟨184391, by rfl⟩ : syracuseStep 245855 = 368783) B368783
theorem B1196167 : Blo 127788 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B835913 : Blo 127788 835913 := bstep (se 2 (by rfl) ⟨313467, by rfl⟩ : syracuseStep 835913 = 626935) B626935
theorem B1262141 : Blo 127788 1262141 := bstep (se 3 (by rfl) ⟨236651, by rfl⟩ : syracuseStep 1262141 = 473303) B473303
theorem B1557305 : Blo 127788 1557305 := bstep (se 2 (by rfl) ⟨583989, by rfl⟩ : syracuseStep 1557305 = 1167979) B1167979
theorem B2213243 : Blo 127788 2213243 := bstep (se 1 (by rfl) ⟨1659932, by rfl⟩ : syracuseStep 2213243 = 3319865) B3319865
theorem B247951 : Blo 127788 247951 := bstep (se 1 (by rfl) ⟨185963, by rfl⟩ : syracuseStep 247951 = 371927) B371927
theorem B4999481 : Blo 127788 4999481 := bstep (se 2 (by rfl) ⟨1874805, by rfl⟩ : syracuseStep 4999481 = 3749611) B3749611
theorem B740573 : Blo 127788 740573 := bstep (se 3 (by rfl) ⟨138857, by rfl⟩ : syracuseStep 740573 = 277715) B277715
theorem B216479 : Blo 127788 216479 := bstep (se 1 (by rfl) ⟨162359, by rfl⟩ : syracuseStep 216479 = 324719) B324719
theorem B282089 : Blo 127788 282089 := bstep (se 2 (by rfl) ⟨105783, by rfl⟩ : syracuseStep 282089 = 211567) B211567
theorem B216911 : Blo 127788 216911 := bstep (se 1 (by rfl) ⟨162683, by rfl⟩ : syracuseStep 216911 = 325367) B325367
theorem B742283 : Blo 127788 742283 := bstep (se 1 (by rfl) ⟨556712, by rfl⟩ : syracuseStep 742283 = 1113425) B1113425
theorem B283751 : Blo 127788 283751 := bstep (se 1 (by rfl) ⟨212813, by rfl⟩ : syracuseStep 283751 = 425627) B425627
theorem B971999 : Blo 127788 971999 := bstep (se 1 (by rfl) ⟨728999, by rfl⟩ : syracuseStep 971999 = 1457999) B1457999
theorem B939599 : Blo 127788 939599 := bstep (se 1 (by rfl) ⟨704699, by rfl⟩ : syracuseStep 939599 = 1409399) B1409399
theorem B218983 : Blo 127788 218983 := bstep (se 1 (by rfl) ⟨164237, by rfl⟩ : syracuseStep 218983 = 328475) B328475
theorem B219739 : Blo 127788 219739 := bstep (se 1 (by rfl) ⟨164804, by rfl⟩ : syracuseStep 219739 = 329609) B329609
theorem B1465289 : Blo 127788 1465289 := bstep (se 2 (by rfl) ⟨549483, by rfl⟩ : syracuseStep 1465289 = 1098967) B1098967
theorem B2120843 : Blo 127788 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B1106075 : Blo 127788 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B975401 : Blo 127788 975401 := bstep (se 2 (by rfl) ⟨365775, by rfl⟩ : syracuseStep 975401 = 731551) B731551
theorem B287657 : Blo 127788 287657 := bstep (se 2 (by rfl) ⟨107871, by rfl⟩ : syracuseStep 287657 = 215743) B215743
theorem B648161 : Blo 127788 648161 := bstep (se 2 (by rfl) ⟨243060, by rfl⟩ : syracuseStep 648161 = 486121) B486121
theorem B288233 : Blo 127788 288233 := bstep (se 2 (by rfl) ⟨108087, by rfl⟩ : syracuseStep 288233 = 216175) B216175
theorem B648971 : Blo 127788 648971 := bstep (se 1 (by rfl) ⟨486728, by rfl⟩ : syracuseStep 648971 = 973457) B973457
theorem B288863 : Blo 127788 288863 := bstep (se 1 (by rfl) ⟨216647, by rfl⟩ : syracuseStep 288863 = 433295) B433295
theorem B420007 : Blo 127788 420007 := bstep (se 1 (by rfl) ⟨315005, by rfl⟩ : syracuseStep 420007 = 630011) B630011
theorem B551519 : Blo 127788 551519 := bstep (se 1 (by rfl) ⟨413639, by rfl⟩ : syracuseStep 551519 = 827279) B827279
theorem B3205777 : Blo 127788 3205777 := bstep (se 2 (by rfl) ⟨1202166, by rfl⟩ : syracuseStep 3205777 = 2404333) B2404333
theorem B191951 : Blo 127788 191951 := bstep (se 1 (by rfl) ⟨143963, by rfl⟩ : syracuseStep 191951 = 287927) B287927
theorem B486881 : Blo 127788 486881 := bstep (se 2 (by rfl) ⟨182580, by rfl⟩ : syracuseStep 486881 = 365161) B365161
theorem B192335 : Blo 127788 192335 := bstep (se 1 (by rfl) ⟨144251, by rfl⟩ : syracuseStep 192335 = 288503) B288503
theorem B192815 : Blo 127788 192815 := bstep (se 1 (by rfl) ⟨144611, by rfl⟩ : syracuseStep 192815 = 289223) B289223
theorem B193079 : Blo 127788 193079 := bstep (se 1 (by rfl) ⟨144809, by rfl⟩ : syracuseStep 193079 = 289619) B289619
theorem B127935 : Blo 127788 127935 := bstep (se 1 (by rfl) ⟨95951, by rfl⟩ : syracuseStep 127935 = 191903) B191903
theorem B324769 : Blo 127788 324769 := bstep (se 2 (by rfl) ⟨121788, by rfl⟩ : syracuseStep 324769 = 243577) B243577
theorem B193727 : Blo 127788 193727 := bstep (se 1 (by rfl) ⟨145295, by rfl⟩ : syracuseStep 193727 = 290591) B290591
theorem B2782457 : Blo 127788 2782457 := bstep (se 2 (by rfl) ⟨1043421, by rfl⟩ : syracuseStep 2782457 = 2086843) B2086843
theorem B292175 : Blo 127788 292175 := bstep (se 1 (by rfl) ⟨219131, by rfl⟩ : syracuseStep 292175 = 438263) B438263
theorem B193913 : Blo 127788 193913 := bstep (se 2 (by rfl) ⟨72717, by rfl⟩ : syracuseStep 193913 = 145435) B145435
theorem B292223 : Blo 127788 292223 := bstep (se 1 (by rfl) ⟨219167, by rfl⟩ : syracuseStep 292223 = 438335) B438335
theorem B194111 : Blo 127788 194111 := bstep (se 1 (by rfl) ⟨145583, by rfl⟩ : syracuseStep 194111 = 291167) B291167
theorem B489341 : Blo 127788 489341 := bstep (se 3 (by rfl) ⟨91751, by rfl⟩ : syracuseStep 489341 = 183503) B183503
theorem B128935 : Blo 127788 128935 := bstep (se 1 (by rfl) ⟨96701, by rfl⟩ : syracuseStep 128935 = 193403) B193403
theorem B194591 : Blo 127788 194591 := bstep (se 1 (by rfl) ⟨145943, by rfl⟩ : syracuseStep 194591 = 291887) B291887
theorem B293039 : Blo 127788 293039 := bstep (se 1 (by rfl) ⟨219779, by rfl⟩ : syracuseStep 293039 = 439559) B439559
theorem B129231 : Blo 127788 129231 := bstep (se 1 (by rfl) ⟨96923, by rfl⟩ : syracuseStep 129231 = 193847) B193847
theorem B1898795 : Blo 127788 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B129383 : Blo 127788 129383 := bstep (se 1 (by rfl) ⟨97037, by rfl⟩ : syracuseStep 129383 = 194075) B194075
theorem B129639 : Blo 127788 129639 := bstep (se 1 (by rfl) ⟨97229, by rfl⟩ : syracuseStep 129639 = 194459) B194459
theorem B752249 : Blo 127788 752249 := bstep (se 2 (by rfl) ⟨282093, by rfl⟩ : syracuseStep 752249 = 564187) B564187
theorem B195691 : Blo 127788 195691 := bstep (se 1 (by rfl) ⟨146768, by rfl⟩ : syracuseStep 195691 = 293537) B293537
theorem B294047 : Blo 127788 294047 := bstep (se 1 (by rfl) ⟨220535, by rfl⟩ : syracuseStep 294047 = 441071) B441071
theorem B195839 : Blo 127788 195839 := bstep (se 1 (by rfl) ⟨146879, by rfl⟩ : syracuseStep 195839 = 293759) B293759
theorem B130527 : Blo 127788 130527 := bstep (se 1 (by rfl) ⟨97895, by rfl⟩ : syracuseStep 130527 = 195791) B195791
theorem B131007 : Blo 127788 131007 := bstep (se 1 (by rfl) ⟨98255, by rfl⟩ : syracuseStep 131007 = 196511) B196511
theorem B196583 : Blo 127788 196583 := bstep (se 1 (by rfl) ⟨147437, by rfl⟩ : syracuseStep 196583 = 294875) B294875
theorem B131163 : Blo 127788 131163 := bstep (se 1 (by rfl) ⟨98372, by rfl⟩ : syracuseStep 131163 = 196745) B196745
theorem B131175 : Blo 127788 131175 := bstep (se 1 (by rfl) ⟨98381, by rfl⟩ : syracuseStep 131175 = 196763) B196763
theorem B196775 : Blo 127788 196775 := bstep (se 1 (by rfl) ⟨147581, by rfl⟩ : syracuseStep 196775 = 295163) B295163
theorem B557275 : Blo 127788 557275 := bstep (se 1 (by rfl) ⟨417956, by rfl⟩ : syracuseStep 557275 = 835913) B835913
theorem B655613 : Blo 127788 655613 := bstep (se 3 (by rfl) ⟨122927, by rfl⟩ : syracuseStep 655613 = 245855) B245855
theorem B131519 : Blo 127788 131519 := bstep (se 1 (by rfl) ⟨98639, by rfl⟩ : syracuseStep 131519 = 197279) B197279
theorem B328283 : Blo 127788 328283 := bstep (se 1 (by rfl) ⟨246212, by rfl⟩ : syracuseStep 328283 = 492425) B492425
theorem B4981421 : Blo 127788 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B1475495 : Blo 127788 1475495 := bstep (se 1 (by rfl) ⟨1106621, by rfl⟩ : syracuseStep 1475495 = 2213243) B2213243
theorem B656423 : Blo 127788 656423 := bstep (se 1 (by rfl) ⟨492317, by rfl⟩ : syracuseStep 656423 = 984635) B984635
theorem B22939307 : Blo 127788 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B493715 : Blo 127788 493715 := bstep (se 1 (by rfl) ⟨370286, by rfl⟩ : syracuseStep 493715 = 740573) B740573
theorem B1247683 : Blo 127788 1247683 := bstep (se 1 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 1247683 = 1871525) B1871525
theorem B330601 : Blo 127788 330601 := bstep (se 2 (by rfl) ⟨123975, by rfl⟩ : syracuseStep 330601 = 247951) B247951
theorem B560009 : Blo 127788 560009 := bstep (se 2 (by rfl) ⟨210003, by rfl⟩ : syracuseStep 560009 = 420007) B420007
theorem B2591777 : Blo 127788 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B658691 : Blo 127788 658691 := bstep (se 1 (by rfl) ⟨494018, by rfl⟩ : syracuseStep 658691 = 988037) B988037
theorem B494855 : Blo 127788 494855 := bstep (se 1 (by rfl) ⟨371141, by rfl⟩ : syracuseStep 494855 = 742283) B742283
theorem B626399 : Blo 127788 626399 := bstep (se 1 (by rfl) ⟨469799, by rfl⟩ : syracuseStep 626399 = 939599) B939599
theorem B332495 : Blo 127788 332495 := bstep (se 1 (by rfl) ⟨249371, by rfl⟩ : syracuseStep 332495 = 498743) B498743
theorem B1413895 : Blo 127788 1413895 := bstep (se 1 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 1413895 = 2120843) B2120843
theorem B660635 : Blo 127788 660635 := bstep (se 1 (by rfl) ⟨495476, by rfl⟩ : syracuseStep 660635 = 990953) B990953
theorem B1316147 : Blo 127788 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B432107 : Blo 127788 432107 := bstep (se 1 (by rfl) ⟨324080, by rfl⟩ : syracuseStep 432107 = 648161) B648161
theorem B432647 : Blo 127788 432647 := bstep (se 1 (by rfl) ⟨324485, by rfl⟩ : syracuseStep 432647 = 648971) B648971
theorem B433025 : Blo 127788 433025 := bstep (se 2 (by rfl) ⟨162384, by rfl⟩ : syracuseStep 433025 = 324769) B324769
theorem B367679 : Blo 127788 367679 := bstep (se 1 (by rfl) ⟨275759, by rfl⟩ : syracuseStep 367679 = 551519) B551519
theorem B990467 : Blo 127788 990467 := bstep (se 1 (by rfl) ⟨742850, by rfl⟩ : syracuseStep 990467 = 1485701) B1485701
theorem B630089 : Blo 127788 630089 := bstep (se 2 (by rfl) ⟨236283, by rfl⟩ : syracuseStep 630089 = 472567) B472567
theorem B205211 : Blo 127788 205211 := bstep (se 1 (by rfl) ⟨153908, by rfl⟩ : syracuseStep 205211 = 307817) B307817
theorem B664361 : Blo 127788 664361 := bstep (se 2 (by rfl) ⟨249135, by rfl⟩ : syracuseStep 664361 = 498271) B498271
theorem B501499 : Blo 127788 501499 := bstep (se 1 (by rfl) ⟨376124, by rfl⟩ : syracuseStep 501499 = 752249) B752249
theorem B207031 : Blo 127788 207031 := bstep (se 1 (by rfl) ⟨155273, by rfl⟩ : syracuseStep 207031 = 310547) B310547
theorem B666143 : Blo 127788 666143 := bstep (se 1 (by rfl) ⟨499607, by rfl⟩ : syracuseStep 666143 = 999215) B999215
theorem B1159039 : Blo 127788 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B144319 : Blo 127788 144319 := bstep (se 1 (by rfl) ⟨108239, by rfl⟩ : syracuseStep 144319 = 216479) B216479
theorem B439451 : Blo 127788 439451 := bstep (se 1 (by rfl) ⟨329588, by rfl⟩ : syracuseStep 439451 = 659177) B659177
theorem B1094867 : Blo 127788 1094867 := bstep (se 1 (by rfl) ⟨821150, by rfl⟩ : syracuseStep 1094867 = 1642301) B1642301
theorem B144607 : Blo 127788 144607 := bstep (se 1 (by rfl) ⟨108455, by rfl⟩ : syracuseStep 144607 = 216911) B216911
theorem B439721 : Blo 127788 439721 := bstep (se 2 (by rfl) ⟨164895, by rfl⟩ : syracuseStep 439721 = 329791) B329791
theorem B702233 : Blo 127788 702233 := bstep (se 2 (by rfl) ⟨263337, by rfl⟩ : syracuseStep 702233 = 526675) B526675
theorem B4274369 : Blo 127788 4274369 := bstep (se 2 (by rfl) ⟨1602888, by rfl⟩ : syracuseStep 4274369 = 3205777) B3205777
theorem B703399 : Blo 127788 703399 := bstep (se 1 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 703399 = 1055099) B1055099
theorem B1064249 : Blo 127788 1064249 := bstep (se 2 (by rfl) ⟨399093, by rfl⟩ : syracuseStep 1064249 = 798187) B798187
theorem B737383 : Blo 127788 737383 := bstep (se 1 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 737383 = 1106075) B1106075
theorem B2475683 : Blo 127788 2475683 := bstep (se 1 (by rfl) ⟨1856762, by rfl⟩ : syracuseStep 2475683 = 3713525) B3713525
theorem B1854971 : Blo 127788 1854971 := bstep (se 1 (by rfl) ⟨1391228, by rfl⟩ : syracuseStep 1854971 = 2782457) B2782457
theorem B315103 : Blo 127788 315103 := bstep (se 1 (by rfl) ⟨236327, by rfl⟩ : syracuseStep 315103 = 472655) B472655
theorem B1101701 : Blo 127788 1101701 := bstep (se 4 (by rfl) ⟨103284, by rfl⟩ : syracuseStep 1101701 = 206569) B206569
theorem B708743 : Blo 127788 708743 := bstep (se 1 (by rfl) ⟨531557, by rfl⟩ : syracuseStep 708743 = 1063115) B1063115
theorem B1265863 : Blo 127788 1265863 := bstep (se 1 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 1265863 = 1898795) B1898795
theorem B4445077 : Blo 127788 4445077 := bstep (se 6 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 4445077 = 208363) B208363
theorem B1594889 : Blo 127788 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B218729 : Blo 127788 218729 := bstep (se 2 (by rfl) ⟨82023, by rfl⟩ : syracuseStep 218729 = 164047) B164047
theorem B415343 : Blo 127788 415343 := bstep (se 1 (by rfl) ⟨311507, by rfl⟩ : syracuseStep 415343 = 623015) B623015
theorem B841427 : Blo 127788 841427 := bstep (se 1 (by rfl) ⟨631070, by rfl⟩ : syracuseStep 841427 = 1262141) B1262141
theorem B16570169 : Blo 127788 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B1038203 : Blo 127788 1038203 := bstep (se 1 (by rfl) ⟨778652, by rfl⟩ : syracuseStep 1038203 = 1557305) B1557305
theorem B219631 : Blo 127788 219631 := bstep (se 1 (by rfl) ⟨164723, by rfl⟩ : syracuseStep 219631 = 329447) B329447
theorem B12671477 : Blo 127788 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B3332987 : Blo 127788 3332987 := bstep (se 1 (by rfl) ⟨2499740, by rfl⟩ : syracuseStep 3332987 = 4999481) B4999481
theorem B1793015 : Blo 127788 1793015 := bstep (se 1 (by rfl) ⟨1344761, by rfl⟩ : syracuseStep 1793015 = 2689523) B2689523
theorem B221737 : Blo 127788 221737 := bstep (se 2 (by rfl) ⟨83151, by rfl⟩ : syracuseStep 221737 = 166303) B166303
theorem B189167 : Blo 127788 189167 := bstep (se 1 (by rfl) ⟨141875, by rfl⟩ : syracuseStep 189167 = 283751) B283751
theorem B647999 : Blo 127788 647999 := bstep (se 1 (by rfl) ⟨485999, by rfl⟩ : syracuseStep 647999 = 971999) B971999
theorem B418879 : Blo 127788 418879 := bstep (se 1 (by rfl) ⟨314159, by rfl⟩ : syracuseStep 418879 = 628319) B628319
theorem B976859 : Blo 127788 976859 := bstep (se 1 (by rfl) ⟨732644, by rfl⟩ : syracuseStep 976859 = 1465289) B1465289
theorem B650267 : Blo 127788 650267 := bstep (se 1 (by rfl) ⟨487700, by rfl⟩ : syracuseStep 650267 = 975401) B975401
theorem B191771 : Blo 127788 191771 := bstep (se 1 (by rfl) ⟨143828, by rfl⟩ : syracuseStep 191771 = 287657) B287657
theorem B2715275 : Blo 127788 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B192155 : Blo 127788 192155 := bstep (se 1 (by rfl) ⟨144116, by rfl⟩ : syracuseStep 192155 = 288233) B288233
theorem B192575 : Blo 127788 192575 := bstep (se 1 (by rfl) ⟨144431, by rfl⟩ : syracuseStep 192575 = 288863) B288863
theorem B290879 : Blo 127788 290879 := bstep (se 1 (by rfl) ⟨218159, by rfl⟩ : syracuseStep 290879 = 436319) B436319
theorem B487579 : Blo 127788 487579 := bstep (se 1 (by rfl) ⟨365684, by rfl⟩ : syracuseStep 487579 = 731369) B731369
theorem B553243 : Blo 127788 553243 := bstep (se 1 (by rfl) ⟨414932, by rfl⟩ : syracuseStep 553243 = 829865) B829865
theorem B324233 : Blo 127788 324233 := bstep (se 2 (by rfl) ⟨121587, by rfl⟩ : syracuseStep 324233 = 243175) B243175
theorem B2028169 : Blo 127788 2028169 := bstep (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) B1521127
theorem B1274687 : Blo 127788 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B127967 : Blo 127788 127967 := bstep (se 1 (by rfl) ⟨95975, by rfl⟩ : syracuseStep 127967 = 191951) B191951
theorem B324587 : Blo 127788 324587 := bstep (se 1 (by rfl) ⟨243440, by rfl⟩ : syracuseStep 324587 = 486881) B486881
theorem B291977 : Blo 127788 291977 := bstep (se 2 (by rfl) ⟨109491, by rfl⟩ : syracuseStep 291977 = 218983) B218983
theorem B292031 : Blo 127788 292031 := bstep (se 1 (by rfl) ⟨219023, by rfl⟩ : syracuseStep 292031 = 438047) B438047
theorem B128223 : Blo 127788 128223 := bstep (se 1 (by rfl) ⟨96167, by rfl⟩ : syracuseStep 128223 = 192335) B192335
theorem B292319 : Blo 127788 292319 := bstep (se 1 (by rfl) ⟨219239, by rfl⟩ : syracuseStep 292319 = 438479) B438479
theorem B128543 : Blo 127788 128543 := bstep (se 1 (by rfl) ⟨96407, by rfl⟩ : syracuseStep 128543 = 192815) B192815
theorem B1275425 : Blo 127788 1275425 := bstep (se 2 (by rfl) ⟨478284, by rfl⟩ : syracuseStep 1275425 = 956569) B956569
theorem B194153 : Blo 127788 194153 := bstep (se 2 (by rfl) ⟨72807, by rfl⟩ : syracuseStep 194153 = 145615) B145615
theorem B128719 : Blo 127788 128719 := bstep (se 1 (by rfl) ⟨96539, by rfl⟩ : syracuseStep 128719 = 193079) B193079
theorem B292859 : Blo 127788 292859 := bstep (se 1 (by rfl) ⟨219644, by rfl⟩ : syracuseStep 292859 = 439289) B439289
theorem B292895 : Blo 127788 292895 := bstep (se 1 (by rfl) ⟨219671, by rfl⟩ : syracuseStep 292895 = 439343) B439343
theorem B292985 : Blo 127788 292985 := bstep (se 2 (by rfl) ⟨109869, by rfl⟩ : syracuseStep 292985 = 219739) B219739
theorem B129151 : Blo 127788 129151 := bstep (se 1 (by rfl) ⟨96863, by rfl⟩ : syracuseStep 129151 = 193727) B193727
theorem B1800407 : Blo 127788 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B194783 : Blo 127788 194783 := bstep (se 1 (by rfl) ⟨146087, by rfl⟩ : syracuseStep 194783 = 292175) B292175
theorem B129275 : Blo 127788 129275 := bstep (se 1 (by rfl) ⟨96956, by rfl⟩ : syracuseStep 129275 = 193913) B193913
theorem B194815 : Blo 127788 194815 := bstep (se 1 (by rfl) ⟨146111, by rfl⟩ : syracuseStep 194815 = 292223) B292223
theorem B129407 : Blo 127788 129407 := bstep (se 1 (by rfl) ⟨97055, by rfl⟩ : syracuseStep 129407 = 194111) B194111
theorem B326227 : Blo 127788 326227 := bstep (se 1 (by rfl) ⟨244670, by rfl⟩ : syracuseStep 326227 = 489341) B489341
theorem B752237 : Blo 127788 752237 := bstep (se 3 (by rfl) ⟨141044, by rfl⟩ : syracuseStep 752237 = 282089) B282089
theorem B555635 : Blo 127788 555635 := bstep (se 1 (by rfl) ⟨416726, by rfl⟩ : syracuseStep 555635 = 833453) B833453
theorem B129727 : Blo 127788 129727 := bstep (se 1 (by rfl) ⟨97295, by rfl⟩ : syracuseStep 129727 = 194591) B194591
theorem B195359 : Blo 127788 195359 := bstep (se 1 (by rfl) ⟨146519, by rfl⟩ : syracuseStep 195359 = 293039) B293039
theorem B260921 : Blo 127788 260921 := bstep (se 2 (by rfl) ⟨97845, by rfl⟩ : syracuseStep 260921 = 195691) B195691
theorem B1342271 : Blo 127788 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B293831 : Blo 127788 293831 := bstep (se 1 (by rfl) ⟨220373, by rfl⟩ : syracuseStep 293831 = 440747) B440747
theorem B4291553 : Blo 127788 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B196031 : Blo 127788 196031 := bstep (se 1 (by rfl) ⟨147023, by rfl⟩ : syracuseStep 196031 = 294047) B294047
theorem B130559 : Blo 127788 130559 := bstep (se 1 (by rfl) ⟨97919, by rfl⟩ : syracuseStep 130559 = 195839) B195839
theorem B131055 : Blo 127788 131055 := bstep (se 1 (by rfl) ⟨98291, by rfl⟩ : syracuseStep 131055 = 196583) B196583
theorem B131183 : Blo 127788 131183 := bstep (se 1 (by rfl) ⟨98387, by rfl⟩ : syracuseStep 131183 = 196775) B196775
theorem B983177 : Blo 127788 983177 := bstep (se 2 (by rfl) ⟨368691, by rfl⟩ : syracuseStep 983177 = 737383) B737383
theorem B983663 : Blo 127788 983663 := bstep (se 1 (by rfl) ⟨737747, by rfl⟩ : syracuseStep 983663 = 1475495) B1475495
theorem B295649 : Blo 127788 295649 := bstep (se 2 (by rfl) ⟨110868, by rfl⟩ : syracuseStep 295649 = 221737) B221737
theorem B558505 : Blo 127788 558505 := bstep (se 2 (by rfl) ⟨209439, by rfl⟩ : syracuseStep 558505 = 418879) B418879
theorem B329143 : Blo 127788 329143 := bstep (se 1 (by rfl) ⟨246857, by rfl⟩ : syracuseStep 329143 = 493715) B493715
theorem B329903 : Blo 127788 329903 := bstep (se 1 (by rfl) ⟨247427, by rfl⟩ : syracuseStep 329903 = 494855) B494855
theorem B3509725 : Blo 127788 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B560951 : Blo 127788 560951 := bstep (se 1 (by rfl) ⟨420713, by rfl⟩ : syracuseStep 560951 = 841427) B841427
theorem B11046779 : Blo 127788 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B692135 : Blo 127788 692135 := bstep (se 1 (by rfl) ⟨519101, by rfl⟩ : syracuseStep 692135 = 1038203) B1038203
theorem B660311 : Blo 127788 660311 := bstep (se 1 (by rfl) ⟨495233, by rfl⟩ : syracuseStep 660311 = 990467) B990467
theorem B431999 : Blo 127788 431999 := bstep (se 1 (by rfl) ⟨323999, by rfl⟩ : syracuseStep 431999 = 647999) B647999
theorem B433511 : Blo 127788 433511 := bstep (se 1 (by rfl) ⟨325133, by rfl⟩ : syracuseStep 433511 = 650267) B650267
theorem B695789 : Blo 127788 695789 := bstep (se 3 (by rfl) ⟨130460, by rfl⟩ : syracuseStep 695789 = 260921) B260921
theorem B3579389 : Blo 127788 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B1810183 : Blo 127788 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B11444141 : Blo 127788 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B434969 : Blo 127788 434969 := bstep (se 2 (by rfl) ⟨163113, by rfl⟩ : syracuseStep 434969 = 326227) B326227
theorem B729911 : Blo 127788 729911 := bstep (se 1 (by rfl) ⟨547433, by rfl⟩ : syracuseStep 729911 = 1094867) B1094867
theorem B468155 : Blo 127788 468155 := bstep (se 1 (by rfl) ⟨351116, by rfl⟩ : syracuseStep 468155 = 702233) B702233
theorem B501491 : Blo 127788 501491 := bstep (se 1 (by rfl) ⟨376118, by rfl⟩ : syracuseStep 501491 = 752237) B752237
theorem B370423 : Blo 127788 370423 := bstep (se 1 (by rfl) ⟨277817, by rfl⟩ : syracuseStep 370423 = 555635) B555635
theorem B437075 : Blo 127788 437075 := bstep (se 1 (by rfl) ⟨327806, by rfl⟩ : syracuseStep 437075 = 655613) B655613
theorem B3320947 : Blo 127788 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B437615 : Blo 127788 437615 := bstep (se 1 (by rfl) ⟨328211, by rfl⟩ : syracuseStep 437615 = 656423) B656423
theorem B1650455 : Blo 127788 1650455 := bstep (se 1 (by rfl) ⟨1237841, by rfl⟩ : syracuseStep 1650455 = 2475683) B2475683
theorem B373339 : Blo 127788 373339 := bstep (se 1 (by rfl) ⟨280004, by rfl⟩ : syracuseStep 373339 = 560009) B560009
theorem B439127 : Blo 127788 439127 := bstep (se 1 (by rfl) ⟨329345, by rfl⟩ : syracuseStep 439127 = 658691) B658691
theorem B668665 : Blo 127788 668665 := bstep (se 2 (by rfl) ⟨250749, by rfl⟩ : syracuseStep 668665 = 501499) B501499
theorem B734467 : Blo 127788 734467 := bstep (se 1 (by rfl) ⟨550850, by rfl⟩ : syracuseStep 734467 = 1101701) B1101701
theorem B472495 : Blo 127788 472495 := bstep (se 1 (by rfl) ⟨354371, by rfl⟩ : syracuseStep 472495 = 708743) B708743
theorem B276041 : Blo 127788 276041 := bstep (se 2 (by rfl) ⟨103515, by rfl⟩ : syracuseStep 276041 = 207031) B207031
theorem B440423 : Blo 127788 440423 := bstep (se 1 (by rfl) ⟨330317, by rfl⟩ : syracuseStep 440423 = 660635) B660635
theorem B1063259 : Blo 127788 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B145819 : Blo 127788 145819 := bstep (se 1 (by rfl) ⟨109364, by rfl⟩ : syracuseStep 145819 = 218729) B218729
theorem B276895 : Blo 127788 276895 := bstep (se 1 (by rfl) ⟨207671, by rfl⟩ : syracuseStep 276895 = 415343) B415343
theorem B440801 : Blo 127788 440801 := bstep (se 2 (by rfl) ⟨165300, by rfl⟩ : syracuseStep 440801 = 330601) B330601
theorem B1195343 : Blo 127788 1195343 := bstep (se 1 (by rfl) ⟨896507, by rfl⟩ : syracuseStep 1195343 = 1793015) B1793015
theorem B245119 : Blo 127788 245119 := bstep (se 1 (by rfl) ⟨183839, by rfl⟩ : syracuseStep 245119 = 367679) B367679
theorem B1687817 : Blo 127788 1687817 := bstep (se 2 (by rfl) ⟨632931, by rfl⟩ : syracuseStep 1687817 = 1265863) B1265863
theorem B737657 : Blo 127788 737657 := bstep (se 2 (by rfl) ⟨276621, by rfl⟩ : syracuseStep 737657 = 553243) B553243
theorem B442907 : Blo 127788 442907 := bstep (se 1 (by rfl) ⟨332180, by rfl⟩ : syracuseStep 442907 = 664361) B664361
theorem B2704225 : Blo 127788 2704225 := bstep (se 2 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 2704225 = 2028169) B2028169
theorem B1885193 : Blo 127788 1885193 := bstep (se 2 (by rfl) ⟨706947, by rfl⟩ : syracuseStep 1885193 = 1413895) B1413895
theorem B444095 : Blo 127788 444095 := bstep (se 1 (by rfl) ⟨333071, by rfl⟩ : syracuseStep 444095 = 666143) B666143
theorem B2017781 : Blo 127788 2017781 := bstep (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) B189167
theorem B216155 : Blo 127788 216155 := bstep (se 1 (by rfl) ⟨162116, by rfl⟩ : syracuseStep 216155 = 324233) B324233
theorem B216391 : Blo 127788 216391 := bstep (se 1 (by rfl) ⟨162293, by rfl⟩ : syracuseStep 216391 = 324587) B324587
theorem B937865 : Blo 127788 937865 := bstep (se 2 (by rfl) ⟨351699, by rfl⟩ : syracuseStep 937865 = 703399) B703399
theorem B1200271 : Blo 127788 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B6181541 : Blo 127788 6181541 := bstep (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) B1159039
theorem B709499 : Blo 127788 709499 := bstep (se 1 (by rfl) ⟨532124, by rfl⟩ : syracuseStep 709499 = 1064249) B1064249
theorem B743033 : Blo 127788 743033 := bstep (se 2 (by rfl) ⟨278637, by rfl⟩ : syracuseStep 743033 = 557275) B557275
theorem B218855 : Blo 127788 218855 := bstep (se 1 (by rfl) ⟨164141, by rfl⟩ : syracuseStep 218855 = 328283) B328283
theorem B547229 : Blo 127788 547229 := bstep (se 3 (by rfl) ⟨102605, by rfl⟩ : syracuseStep 547229 = 205211) B205211
theorem B15292871 : Blo 127788 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B1727851 : Blo 127788 1727851 := bstep (se 1 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 1727851 = 2591777) B2591777
theorem B1236647 : Blo 127788 1236647 := bstep (se 1 (by rfl) ⟨927485, by rfl⟩ : syracuseStep 1236647 = 1854971) B1854971
theorem B417599 : Blo 127788 417599 := bstep (se 1 (by rfl) ⟨313199, by rfl⟩ : syracuseStep 417599 = 626399) B626399
theorem B221663 : Blo 127788 221663 := bstep (se 1 (by rfl) ⟨166247, by rfl⟩ : syracuseStep 221663 = 332495) B332495
theorem B1663577 : Blo 127788 1663577 := bstep (se 2 (by rfl) ⟨623841, by rfl⟩ : syracuseStep 1663577 = 1247683) B1247683
theorem B288071 : Blo 127788 288071 := bstep (se 1 (by rfl) ⟨216053, by rfl⟩ : syracuseStep 288071 = 432107) B432107
theorem B8447651 : Blo 127788 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B288431 : Blo 127788 288431 := bstep (se 1 (by rfl) ⟨216323, by rfl⟩ : syracuseStep 288431 = 432647) B432647
theorem B2221991 : Blo 127788 2221991 := bstep (se 1 (by rfl) ⟨1666493, by rfl⟩ : syracuseStep 2221991 = 3332987) B3332987
theorem B288683 : Blo 127788 288683 := bstep (se 1 (by rfl) ⟨216512, by rfl⟩ : syracuseStep 288683 = 433025) B433025
theorem B420059 : Blo 127788 420059 := bstep (se 1 (by rfl) ⟨315044, by rfl⟩ : syracuseStep 420059 = 630089) B630089
theorem B420137 : Blo 127788 420137 := bstep (se 2 (by rfl) ⟨157551, by rfl⟩ : syracuseStep 420137 = 315103) B315103
theorem B650105 : Blo 127788 650105 := bstep (se 2 (by rfl) ⟨243789, by rfl⟩ : syracuseStep 650105 = 487579) B487579
theorem B5926769 : Blo 127788 5926769 := bstep (se 2 (by rfl) ⟨2222538, by rfl⟩ : syracuseStep 5926769 = 4445077) B4445077
theorem B192425 : Blo 127788 192425 := bstep (se 2 (by rfl) ⟨72159, by rfl⟩ : syracuseStep 192425 = 144319) B144319
theorem B651239 : Blo 127788 651239 := bstep (se 1 (by rfl) ⟨488429, by rfl⟩ : syracuseStep 651239 = 976859) B976859
theorem B192809 : Blo 127788 192809 := bstep (se 2 (by rfl) ⟨72303, by rfl⟩ : syracuseStep 192809 = 144607) B144607
theorem B127847 : Blo 127788 127847 := bstep (se 1 (by rfl) ⟨95885, by rfl⟩ : syracuseStep 127847 = 191771) B191771
theorem B128103 : Blo 127788 128103 := bstep (se 1 (by rfl) ⟨96077, by rfl⟩ : syracuseStep 128103 = 192155) B192155
theorem B128383 : Blo 127788 128383 := bstep (se 1 (by rfl) ⟨96287, by rfl⟩ : syracuseStep 128383 = 192575) B192575
theorem B193919 : Blo 127788 193919 := bstep (se 1 (by rfl) ⟨145439, by rfl⟩ : syracuseStep 193919 = 290879) B290879
theorem B259753 : Blo 127788 259753 := bstep (se 2 (by rfl) ⟨97407, by rfl⟩ : syracuseStep 259753 = 194815) B194815
theorem B849791 : Blo 127788 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B292841 : Blo 127788 292841 := bstep (se 2 (by rfl) ⟨109815, by rfl⟩ : syracuseStep 292841 = 219631) B219631
theorem B194651 : Blo 127788 194651 := bstep (se 1 (by rfl) ⟨145988, by rfl⟩ : syracuseStep 194651 = 291977) B291977
theorem B292967 : Blo 127788 292967 := bstep (se 1 (by rfl) ⟨219725, by rfl⟩ : syracuseStep 292967 = 439451) B439451
theorem B194687 : Blo 127788 194687 := bstep (se 1 (by rfl) ⟨146015, by rfl⟩ : syracuseStep 194687 = 292031) B292031
theorem B293147 : Blo 127788 293147 := bstep (se 1 (by rfl) ⟨219860, by rfl⟩ : syracuseStep 293147 = 439721) B439721
theorem B194879 : Blo 127788 194879 := bstep (se 1 (by rfl) ⟨146159, by rfl⟩ : syracuseStep 194879 = 292319) B292319
theorem B850283 : Blo 127788 850283 := bstep (se 1 (by rfl) ⟨637712, by rfl⟩ : syracuseStep 850283 = 1275425) B1275425
theorem B129435 : Blo 127788 129435 := bstep (se 1 (by rfl) ⟨97076, by rfl⟩ : syracuseStep 129435 = 194153) B194153
theorem B195239 : Blo 127788 195239 := bstep (se 1 (by rfl) ⟨146429, by rfl⟩ : syracuseStep 195239 = 292859) B292859
theorem B195263 : Blo 127788 195263 := bstep (se 1 (by rfl) ⟨146447, by rfl⟩ : syracuseStep 195263 = 292895) B292895
theorem B195323 : Blo 127788 195323 := bstep (se 1 (by rfl) ⟨146492, by rfl⟩ : syracuseStep 195323 = 292985) B292985
theorem B2849579 : Blo 127788 2849579 := bstep (se 1 (by rfl) ⟨2137184, by rfl⟩ : syracuseStep 2849579 = 4274369) B4274369
theorem B129855 : Blo 127788 129855 := bstep (se 1 (by rfl) ⟨97391, by rfl⟩ : syracuseStep 129855 = 194783) B194783
theorem B130239 : Blo 127788 130239 := bstep (se 1 (by rfl) ⟨97679, by rfl⟩ : syracuseStep 130239 = 195359) B195359
theorem B195887 : Blo 127788 195887 := bstep (se 1 (by rfl) ⟨146915, by rfl⟩ : syracuseStep 195887 = 293831) B293831
theorem B130687 : Blo 127788 130687 := bstep (se 1 (by rfl) ⟨98015, by rfl⟩ : syracuseStep 130687 = 196031) B196031
theorem B655451 : Blo 127788 655451 := bstep (se 1 (by rfl) ⟨491588, by rfl⟩ : syracuseStep 655451 = 983177) B983177
theorem B491771 : Blo 127788 491771 := bstep (se 1 (by rfl) ⟨368828, by rfl⟩ : syracuseStep 491771 = 737657) B737657
theorem B295271 : Blo 127788 295271 := bstep (se 1 (by rfl) ⟨221453, by rfl⟩ : syracuseStep 295271 = 442907) B442907
theorem B655775 : Blo 127788 655775 := bstep (se 1 (by rfl) ⟨491831, by rfl⟩ : syracuseStep 655775 = 983663) B983663
theorem B197099 : Blo 127788 197099 := bstep (se 1 (by rfl) ⟨147824, by rfl⟩ : syracuseStep 197099 = 295649) B295649
theorem B296063 : Blo 127788 296063 := bstep (se 1 (by rfl) ⟨222047, by rfl⟩ : syracuseStep 296063 = 444095) B444095
theorem B3605633 : Blo 127788 3605633 := bstep (se 2 (by rfl) ⟨1352112, by rfl⟩ : syracuseStep 3605633 = 2704225) B2704225
theorem B1345187 : Blo 127788 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B493897 : Blo 127788 493897 := bstep (se 2 (by rfl) ⟨185211, by rfl⟩ : syracuseStep 493897 = 370423) B370423
theorem B625243 : Blo 127788 625243 := bstep (se 1 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 625243 = 937865) B937865
theorem B461423 : Blo 127788 461423 := bstep (se 1 (by rfl) ⟨346067, by rfl⟩ : syracuseStep 461423 = 692135) B692135
theorem B495355 : Blo 127788 495355 := bstep (se 1 (by rfl) ⟨371516, by rfl⟩ : syracuseStep 495355 = 743033) B743033
theorem B4427929 : Blo 127788 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B364819 : Blo 127788 364819 := bstep (se 1 (by rfl) ⟨273614, by rfl⟩ : syracuseStep 364819 = 547229) B547229
theorem B10195247 : Blo 127788 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B463859 : Blo 127788 463859 := bstep (se 1 (by rfl) ⟨347894, by rfl⟩ : syracuseStep 463859 = 695789) B695789
theorem B824431 : Blo 127788 824431 := bstep (se 1 (by rfl) ⟨618323, by rfl⟩ : syracuseStep 824431 = 1236647) B1236647
theorem B497785 : Blo 127788 497785 := bstep (se 2 (by rfl) ⟨186669, by rfl⟩ : syracuseStep 497785 = 373339) B373339
theorem B334327 : Blo 127788 334327 := bstep (se 1 (by rfl) ⟨250745, by rfl⟩ : syracuseStep 334327 = 501491) B501491
theorem B1481327 : Blo 127788 1481327 := bstep (se 1 (by rfl) ⟨1110995, by rfl⟩ : syracuseStep 1481327 = 2221991) B2221991
theorem B629993 : Blo 127788 629993 := bstep (se 2 (by rfl) ⟨236247, by rfl⟩ : syracuseStep 629993 = 472495) B472495
theorem B433403 : Blo 127788 433403 := bstep (se 1 (by rfl) ⟨325052, by rfl⟩ : syracuseStep 433403 = 650105) B650105
theorem B434159 : Blo 127788 434159 := bstep (se 1 (by rfl) ⟨325619, by rfl⟩ : syracuseStep 434159 = 651239) B651239
theorem B369193 : Blo 127788 369193 := bstep (se 2 (by rfl) ⟨138447, by rfl⟩ : syracuseStep 369193 = 276895) B276895
theorem B566527 : Blo 127788 566527 := bstep (se 1 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 566527 = 849791) B849791
theorem B566855 : Blo 127788 566855 := bstep (se 1 (by rfl) ⟨425141, by rfl⟩ : syracuseStep 566855 = 850283) B850283
theorem B2303801 : Blo 127788 2303801 := bstep (se 2 (by rfl) ⟨863925, by rfl⟩ : syracuseStep 2303801 = 1727851) B1727851
theorem B796895 : Blo 127788 796895 := bstep (se 1 (by rfl) ⟨597671, by rfl⟩ : syracuseStep 796895 = 1195343) B1195343
theorem B1125211 : Blo 127788 1125211 := bstep (se 1 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 1125211 = 1687817) B1687817
theorem B1256795 : Blo 127788 1256795 := bstep (se 1 (by rfl) ⟨942596, by rfl⟩ : syracuseStep 1256795 = 1885193) B1885193
theorem B438857 : Blo 127788 438857 := bstep (se 2 (by rfl) ⟨164571, by rfl⟩ : syracuseStep 438857 = 329143) B329143
theorem B144103 : Blo 127788 144103 := bstep (se 1 (by rfl) ⟨108077, by rfl⟩ : syracuseStep 144103 = 216155) B216155
theorem B373967 : Blo 127788 373967 := bstep (se 1 (by rfl) ⟨280475, by rfl⟩ : syracuseStep 373967 = 560951) B560951
theorem B440207 : Blo 127788 440207 := bstep (se 1 (by rfl) ⟨330155, by rfl⟩ : syracuseStep 440207 = 660311) B660311
theorem B145903 : Blo 127788 145903 := bstep (se 1 (by rfl) ⟨109427, by rfl⟩ : syracuseStep 145903 = 218855) B218855
theorem B278399 : Blo 127788 278399 := bstep (se 1 (by rfl) ⟨208799, by rfl⟩ : syracuseStep 278399 = 417599) B417599
theorem B147775 : Blo 127788 147775 := bstep (se 1 (by rfl) ⟨110831, by rfl⟩ : syracuseStep 147775 = 221663) B221663
theorem B312103 : Blo 127788 312103 := bstep (se 1 (by rfl) ⟨234077, by rfl⟩ : syracuseStep 312103 = 468155) B468155
theorem B280039 : Blo 127788 280039 := bstep (se 1 (by rfl) ⟨210029, by rfl⟩ : syracuseStep 280039 = 420059) B420059
theorem B280091 : Blo 127788 280091 := bstep (se 1 (by rfl) ⟨210068, by rfl⟩ : syracuseStep 280091 = 420137) B420137
theorem B346337 : Blo 127788 346337 := bstep (se 2 (by rfl) ⟨129876, by rfl⟩ : syracuseStep 346337 = 259753) B259753
theorem B1100303 : Blo 127788 1100303 := bstep (se 1 (by rfl) ⟨825227, by rfl⟩ : syracuseStep 1100303 = 1650455) B1650455
theorem B3951179 : Blo 127788 3951179 := bstep (se 1 (by rfl) ⟨2963384, by rfl⟩ : syracuseStep 3951179 = 5926769) B5926769
theorem B184027 : Blo 127788 184027 := bstep (se 1 (by rfl) ⟨138020, by rfl⟩ : syracuseStep 184027 = 276041) B276041
theorem B708839 : Blo 127788 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B2413577 : Blo 127788 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B219935 : Blo 127788 219935 := bstep (se 1 (by rfl) ⟨164951, by rfl⟩ : syracuseStep 219935 = 329903) B329903
theorem B744673 : Blo 127788 744673 := bstep (se 2 (by rfl) ⟨279252, by rfl⟩ : syracuseStep 744673 = 558505) B558505
theorem B777701 : Blo 127788 777701 := bstep (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) B145819
theorem B1891997 : Blo 127788 1891997 := bstep (se 3 (by rfl) ⟨354749, by rfl⟩ : syracuseStep 1891997 = 709499) B709499
theorem B7364519 : Blo 127788 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B4121027 : Blo 127788 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B287999 : Blo 127788 287999 := bstep (se 1 (by rfl) ⟨215999, by rfl⟩ : syracuseStep 287999 = 431999) B431999
theorem B288521 : Blo 127788 288521 := bstep (se 2 (by rfl) ⟨108195, by rfl⟩ : syracuseStep 288521 = 216391) B216391
theorem B4679633 : Blo 127788 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B289007 : Blo 127788 289007 := bstep (se 1 (by rfl) ⟨216755, by rfl⟩ : syracuseStep 289007 = 433511) B433511
theorem B2386259 : Blo 127788 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B7629427 : Blo 127788 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B3566213 : Blo 127788 3566213 := bstep (se 4 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 3566213 = 668665) B668665
theorem B1600361 : Blo 127788 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B1109051 : Blo 127788 1109051 := bstep (se 1 (by rfl) ⟨831788, by rfl⟩ : syracuseStep 1109051 = 1663577) B1663577
theorem B289979 : Blo 127788 289979 := bstep (se 1 (by rfl) ⟨217484, by rfl⟩ : syracuseStep 289979 = 434969) B434969
theorem B486607 : Blo 127788 486607 := bstep (se 1 (by rfl) ⟨364955, by rfl⟩ : syracuseStep 486607 = 729911) B729911
theorem B192047 : Blo 127788 192047 := bstep (se 1 (by rfl) ⟨144035, by rfl⟩ : syracuseStep 192047 = 288071) B288071
theorem B5631767 : Blo 127788 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B192287 : Blo 127788 192287 := bstep (se 1 (by rfl) ⟨144215, by rfl⟩ : syracuseStep 192287 = 288431) B288431
theorem B192455 : Blo 127788 192455 := bstep (se 1 (by rfl) ⟨144341, by rfl⟩ : syracuseStep 192455 = 288683) B288683
theorem B979289 : Blo 127788 979289 := bstep (se 2 (by rfl) ⟨367233, by rfl⟩ : syracuseStep 979289 = 734467) B734467
theorem B291383 : Blo 127788 291383 := bstep (se 1 (by rfl) ⟨218537, by rfl⟩ : syracuseStep 291383 = 437075) B437075
theorem B291743 : Blo 127788 291743 := bstep (se 1 (by rfl) ⟨218807, by rfl⟩ : syracuseStep 291743 = 437615) B437615
theorem B128283 : Blo 127788 128283 := bstep (se 1 (by rfl) ⟨96212, by rfl⟩ : syracuseStep 128283 = 192425) B192425
theorem B128539 : Blo 127788 128539 := bstep (se 1 (by rfl) ⟨96404, by rfl⟩ : syracuseStep 128539 = 192809) B192809
theorem B292751 : Blo 127788 292751 := bstep (se 1 (by rfl) ⟨219563, by rfl⟩ : syracuseStep 292751 = 439127) B439127
theorem B129279 : Blo 127788 129279 := bstep (se 1 (by rfl) ⟨96959, by rfl⟩ : syracuseStep 129279 = 193919) B193919
theorem B195227 : Blo 127788 195227 := bstep (se 1 (by rfl) ⟨146420, by rfl⟩ : syracuseStep 195227 = 292841) B292841
theorem B129767 : Blo 127788 129767 := bstep (se 1 (by rfl) ⟨97325, by rfl⟩ : syracuseStep 129767 = 194651) B194651
theorem B195311 : Blo 127788 195311 := bstep (se 1 (by rfl) ⟨146483, by rfl⟩ : syracuseStep 195311 = 292967) B292967
theorem B293615 : Blo 127788 293615 := bstep (se 1 (by rfl) ⟨220211, by rfl⟩ : syracuseStep 293615 = 440423) B440423
theorem B129791 : Blo 127788 129791 := bstep (se 1 (by rfl) ⟨97343, by rfl⟩ : syracuseStep 129791 = 194687) B194687
theorem B195431 : Blo 127788 195431 := bstep (se 1 (by rfl) ⟨146573, by rfl⟩ : syracuseStep 195431 = 293147) B293147
theorem B129919 : Blo 127788 129919 := bstep (se 1 (by rfl) ⟨97439, by rfl⟩ : syracuseStep 129919 = 194879) B194879
theorem B293867 : Blo 127788 293867 := bstep (se 1 (by rfl) ⟨220400, by rfl⟩ : syracuseStep 293867 = 440801) B440801
theorem B130159 : Blo 127788 130159 := bstep (se 1 (by rfl) ⟨97619, by rfl⟩ : syracuseStep 130159 = 195239) B195239
theorem B130175 : Blo 127788 130175 := bstep (se 1 (by rfl) ⟨97631, by rfl⟩ : syracuseStep 130175 = 195263) B195263
theorem B130215 : Blo 127788 130215 := bstep (se 1 (by rfl) ⟨97661, by rfl⟩ : syracuseStep 130215 = 195323) B195323
theorem B326825 : Blo 127788 326825 := bstep (se 2 (by rfl) ⟨122559, by rfl⟩ : syracuseStep 326825 = 245119) B245119
theorem B1899719 : Blo 127788 1899719 := bstep (se 1 (by rfl) ⟨1424789, by rfl⟩ : syracuseStep 1899719 = 2849579) B2849579
theorem B130591 : Blo 127788 130591 := bstep (se 1 (by rfl) ⟨97943, by rfl⟩ : syracuseStep 130591 = 195887) B195887
theorem B327847 : Blo 127788 327847 := bstep (se 1 (by rfl) ⟨245885, by rfl⟩ : syracuseStep 327847 = 491771) B491771
theorem B196847 : Blo 127788 196847 := bstep (se 1 (by rfl) ⟨147635, by rfl⟩ : syracuseStep 196847 = 295271) B295271
theorem B131399 : Blo 127788 131399 := bstep (se 1 (by rfl) ⟨98549, by rfl⟩ : syracuseStep 131399 = 197099) B197099
theorem B197033 : Blo 127788 197033 := bstep (se 2 (by rfl) ⟨73887, by rfl⟩ : syracuseStep 197033 = 147775) B147775
theorem B492257 : Blo 127788 492257 := bstep (se 2 (by rfl) ⟨184596, by rfl⟩ : syracuseStep 492257 = 369193) B369193
theorem B197375 : Blo 127788 197375 := bstep (se 1 (by rfl) ⟨148031, by rfl⟩ : syracuseStep 197375 = 296063) B296063
theorem B230891 : Blo 127788 230891 := bstep (se 1 (by rfl) ⟨173168, by rfl⟩ : syracuseStep 230891 = 346337) B346337
theorem B755369 : Blo 127788 755369 := bstep (se 2 (by rfl) ⟨283263, by rfl⟩ : syracuseStep 755369 = 566527) B566527
theorem B658529 : Blo 127788 658529 := bstep (se 2 (by rfl) ⟨246948, by rfl⟩ : syracuseStep 658529 = 493897) B493897
theorem B987551 : Blo 127788 987551 := bstep (se 1 (by rfl) ⟨740663, by rfl⟩ : syracuseStep 987551 = 1481327) B1481327
theorem B660473 : Blo 127788 660473 := bstep (se 2 (by rfl) ⟨247677, by rfl⟩ : syracuseStep 660473 = 495355) B495355
theorem B531263 : Blo 127788 531263 := bstep (se 1 (by rfl) ⟨398447, by rfl⟩ : syracuseStep 531263 = 796895) B796895
theorem B663713 : Blo 127788 663713 := bstep (se 2 (by rfl) ⟨248892, by rfl⟩ : syracuseStep 663713 = 497785) B497785
theorem B2073869 : Blo 127788 2073869 := bstep (se 3 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 2073869 = 777701) B777701
theorem B992897 : Blo 127788 992897 := bstep (se 2 (by rfl) ⟨372336, by rfl⟩ : syracuseStep 992897 = 744673) B744673
theorem B436967 : Blo 127788 436967 := bstep (se 1 (by rfl) ⟨327725, by rfl⟩ : syracuseStep 436967 = 655451) B655451
theorem B437183 : Blo 127788 437183 := bstep (se 1 (by rfl) ⟨327887, by rfl⟩ : syracuseStep 437183 = 655775) B655775
theorem B2403755 : Blo 127788 2403755 := bstep (se 1 (by rfl) ⟨1802816, by rfl⟩ : syracuseStep 2403755 = 3605633) B3605633
theorem B896791 : Blo 127788 896791 := bstep (se 1 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 896791 = 1345187) B1345187
theorem B733535 : Blo 127788 733535 := bstep (se 1 (by rfl) ⟨550151, by rfl⟩ : syracuseStep 733535 = 1100303) B1100303
theorem B2634119 : Blo 127788 2634119 := bstep (se 1 (by rfl) ⟨1975589, by rfl⟩ : syracuseStep 2634119 = 3951179) B3951179
theorem B373385 : Blo 127788 373385 := bstep (se 2 (by rfl) ⟨140019, by rfl⟩ : syracuseStep 373385 = 280039) B280039
theorem B6436205 : Blo 127788 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B472559 : Blo 127788 472559 := bstep (se 1 (by rfl) ⟨354419, by rfl⟩ : syracuseStep 472559 = 708839) B708839
theorem B6796831 : Blo 127788 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B309239 : Blo 127788 309239 := bstep (se 1 (by rfl) ⟨231929, by rfl⟩ : syracuseStep 309239 = 463859) B463859
theorem B833657 : Blo 127788 833657 := bstep (se 2 (by rfl) ⟨312621, by rfl⟩ : syracuseStep 833657 = 625243) B625243
theorem B10172569 : Blo 127788 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B146623 : Blo 127788 146623 := bstep (se 1 (by rfl) ⟨109967, by rfl⟩ : syracuseStep 146623 = 219935) B219935
theorem B245369 : Blo 127788 245369 := bstep (se 2 (by rfl) ⟨92013, by rfl⟩ : syracuseStep 245369 = 184027) B184027
theorem B1261331 : Blo 127788 1261331 := bstep (se 1 (by rfl) ⟨945998, by rfl⟩ : syracuseStep 1261331 = 1891997) B1891997
theorem B377903 : Blo 127788 377903 := bstep (se 1 (by rfl) ⟨283427, by rfl⟩ : syracuseStep 377903 = 566855) B566855
theorem B1099241 : Blo 127788 1099241 := bstep (se 2 (by rfl) ⟨412215, by rfl⟩ : syracuseStep 1099241 = 824431) B824431
theorem B1590839 : Blo 127788 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B1230461 : Blo 127788 1230461 := bstep (se 3 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 1230461 = 461423) B461423
theorem B2377475 : Blo 127788 2377475 := bstep (se 1 (by rfl) ⟨1783106, by rfl⟩ : syracuseStep 2377475 = 3566213) B3566213
theorem B1066907 : Blo 127788 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B739367 : Blo 127788 739367 := bstep (se 1 (by rfl) ⟨554525, by rfl⟩ : syracuseStep 739367 = 1109051) B1109051
theorem B837863 : Blo 127788 837863 := bstep (se 1 (by rfl) ⟨628397, by rfl⟩ : syracuseStep 837863 = 1256795) B1256795
theorem B3754511 : Blo 127788 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B445769 : Blo 127788 445769 := bstep (se 2 (by rfl) ⟨167163, by rfl⟩ : syracuseStep 445769 = 334327) B334327
theorem B249311 : Blo 127788 249311 := bstep (se 1 (by rfl) ⟨186983, by rfl⟩ : syracuseStep 249311 = 373967) B373967
theorem B217883 : Blo 127788 217883 := bstep (se 1 (by rfl) ⟨163412, by rfl⟩ : syracuseStep 217883 = 326825) B326825
theorem B1266479 : Blo 127788 1266479 := bstep (se 1 (by rfl) ⟨949859, by rfl⟩ : syracuseStep 1266479 = 1899719) B1899719
theorem B185599 : Blo 127788 185599 := bstep (se 1 (by rfl) ⟨139199, by rfl⟩ : syracuseStep 185599 = 278399) B278399
theorem B23615621 : Blo 127788 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B186727 : Blo 127788 186727 := bstep (se 1 (by rfl) ⟨140045, by rfl⟩ : syracuseStep 186727 = 280091) B280091
theorem B1500281 : Blo 127788 1500281 := bstep (se 2 (by rfl) ⟨562605, by rfl⟩ : syracuseStep 1500281 = 1125211) B1125211
theorem B1664549 : Blo 127788 1664549 := bstep (se 4 (by rfl) ⟨156051, by rfl⟩ : syracuseStep 1664549 = 312103) B312103
theorem B648809 : Blo 127788 648809 := bstep (se 2 (by rfl) ⟨243303, by rfl⟩ : syracuseStep 648809 = 486607) B486607
theorem B419995 : Blo 127788 419995 := bstep (se 1 (by rfl) ⟨314996, by rfl⟩ : syracuseStep 419995 = 629993) B629993
theorem B288935 : Blo 127788 288935 := bstep (se 1 (by rfl) ⟨216701, by rfl⟩ : syracuseStep 288935 = 433403) B433403
theorem B12479021 : Blo 127788 12479021 := bstep (se 3 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 12479021 = 4679633) B4679633
theorem B4909679 : Blo 127788 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B289439 : Blo 127788 289439 := bstep (se 1 (by rfl) ⟨217079, by rfl⟩ : syracuseStep 289439 = 434159) B434159
theorem B2747351 : Blo 127788 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B486425 : Blo 127788 486425 := bstep (se 2 (by rfl) ⟨182409, by rfl⟩ : syracuseStep 486425 = 364819) B364819
theorem B191999 : Blo 127788 191999 := bstep (se 1 (by rfl) ⟨143999, by rfl⟩ : syracuseStep 191999 = 287999) B287999
theorem B192137 : Blo 127788 192137 := bstep (se 2 (by rfl) ⟨72051, by rfl⟩ : syracuseStep 192137 = 144103) B144103
theorem B192347 : Blo 127788 192347 := bstep (se 1 (by rfl) ⟨144260, by rfl⟩ : syracuseStep 192347 = 288521) B288521
theorem B1535867 : Blo 127788 1535867 := bstep (se 1 (by rfl) ⟨1151900, by rfl⟩ : syracuseStep 1535867 = 2303801) B2303801
theorem B192671 : Blo 127788 192671 := bstep (se 1 (by rfl) ⟨144503, by rfl⟩ : syracuseStep 192671 = 289007) B289007
theorem B193319 : Blo 127788 193319 := bstep (se 1 (by rfl) ⟨144989, by rfl⟩ : syracuseStep 193319 = 289979) B289979
theorem B128031 : Blo 127788 128031 := bstep (se 1 (by rfl) ⟨96023, by rfl⟩ : syracuseStep 128031 = 192047) B192047
theorem B128191 : Blo 127788 128191 := bstep (se 1 (by rfl) ⟨96143, by rfl⟩ : syracuseStep 128191 = 192287) B192287
theorem B128303 : Blo 127788 128303 := bstep (se 1 (by rfl) ⟨96227, by rfl⟩ : syracuseStep 128303 = 192455) B192455
theorem B652859 : Blo 127788 652859 := bstep (se 1 (by rfl) ⟨489644, by rfl⟩ : syracuseStep 652859 = 979289) B979289
theorem B194255 : Blo 127788 194255 := bstep (se 1 (by rfl) ⟨145691, by rfl⟩ : syracuseStep 194255 = 291383) B291383
theorem B292571 : Blo 127788 292571 := bstep (se 1 (by rfl) ⟨219428, by rfl⟩ : syracuseStep 292571 = 438857) B438857
theorem B194495 : Blo 127788 194495 := bstep (se 1 (by rfl) ⟨145871, by rfl⟩ : syracuseStep 194495 = 291743) B291743
theorem B194537 : Blo 127788 194537 := bstep (se 2 (by rfl) ⟨72951, by rfl⟩ : syracuseStep 194537 = 145903) B145903
theorem B195167 : Blo 127788 195167 := bstep (se 1 (by rfl) ⟨146375, by rfl⟩ : syracuseStep 195167 = 292751) B292751
theorem B293471 : Blo 127788 293471 := bstep (se 1 (by rfl) ⟨220103, by rfl⟩ : syracuseStep 293471 = 440207) B440207
theorem B130151 : Blo 127788 130151 := bstep (se 1 (by rfl) ⟨97613, by rfl⟩ : syracuseStep 130151 = 195227) B195227
theorem B130207 : Blo 127788 130207 := bstep (se 1 (by rfl) ⟨97655, by rfl⟩ : syracuseStep 130207 = 195311) B195311
theorem B195743 : Blo 127788 195743 := bstep (se 1 (by rfl) ⟨146807, by rfl⟩ : syracuseStep 195743 = 293615) B293615
theorem B130287 : Blo 127788 130287 := bstep (se 1 (by rfl) ⟨97715, by rfl⟩ : syracuseStep 130287 = 195431) B195431
theorem B195911 : Blo 127788 195911 := bstep (se 1 (by rfl) ⟨146933, by rfl⟩ : syracuseStep 195911 = 293867) B293867
theorem B131231 : Blo 127788 131231 := bstep (se 1 (by rfl) ⟨98423, by rfl⟩ : syracuseStep 131231 = 196847) B196847
theorem B131355 : Blo 127788 131355 := bstep (se 1 (by rfl) ⟨98516, by rfl⟩ : syracuseStep 131355 = 197033) B197033
theorem B328171 : Blo 127788 328171 := bstep (se 1 (by rfl) ⟨246128, by rfl⟩ : syracuseStep 328171 = 492257) B492257
theorem B131583 : Blo 127788 131583 := bstep (se 1 (by rfl) ⟨98687, by rfl⟩ : syracuseStep 131583 = 197375) B197375
theorem B820307 : Blo 127788 820307 := bstep (se 1 (by rfl) ⟨615230, by rfl⟩ : syracuseStep 820307 = 1230461) B1230461
theorem B492911 : Blo 127788 492911 := bstep (se 1 (by rfl) ⟨369683, by rfl⟩ : syracuseStep 492911 = 739367) B739367
theorem B558575 : Blo 127788 558575 := bstep (se 1 (by rfl) ⟨418931, by rfl⟩ : syracuseStep 558575 = 837863) B837863
theorem B297179 : Blo 127788 297179 := bstep (se 1 (by rfl) ⟨222884, by rfl⟩ : syracuseStep 297179 = 445769) B445769
theorem B166207 : Blo 127788 166207 := bstep (se 1 (by rfl) ⟨124655, by rfl⟩ : syracuseStep 166207 = 249311) B249311
theorem B559993 : Blo 127788 559993 := bstep (se 2 (by rfl) ⟨209997, by rfl⟩ : syracuseStep 559993 = 419995) B419995
theorem B658367 : Blo 127788 658367 := bstep (se 1 (by rfl) ⟨493775, by rfl⟩ : syracuseStep 658367 = 987551) B987551
theorem B1382579 : Blo 127788 1382579 := bstep (se 1 (by rfl) ⟨1036934, by rfl⟩ : syracuseStep 1382579 = 2073869) B2073869
theorem B432539 : Blo 127788 432539 := bstep (se 1 (by rfl) ⟨324404, by rfl⟩ : syracuseStep 432539 = 648809) B648809
theorem B661931 : Blo 127788 661931 := bstep (se 1 (by rfl) ⟨496448, by rfl⟩ : syracuseStep 661931 = 992897) B992897
theorem B1416701 : Blo 127788 1416701 := bstep (se 3 (by rfl) ⟨265631, by rfl⟩ : syracuseStep 1416701 = 531263) B531263
theorem B1023911 : Blo 127788 1023911 := bstep (se 1 (by rfl) ⟨767933, by rfl⟩ : syracuseStep 1023911 = 1535867) B1535867
theorem B435239 : Blo 127788 435239 := bstep (se 1 (by rfl) ⟨326429, by rfl⟩ : syracuseStep 435239 = 652859) B652859
theorem B206159 : Blo 127788 206159 := bstep (se 1 (by rfl) ⟨154619, by rfl⟩ : syracuseStep 206159 = 309239) B309239
theorem B437129 : Blo 127788 437129 := bstep (se 2 (by rfl) ⟨163923, by rfl⟩ : syracuseStep 437129 = 327847) B327847
theorem B732827 : Blo 127788 732827 := bstep (se 1 (by rfl) ⟨549620, by rfl⟩ : syracuseStep 732827 = 1099241) B1099241
theorem B1060559 : Blo 127788 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B503579 : Blo 127788 503579 := bstep (se 1 (by rfl) ⟨377684, by rfl⟩ : syracuseStep 503579 = 755369) B755369
theorem B1584983 : Blo 127788 1584983 := bstep (se 1 (by rfl) ⟨1188737, by rfl⟩ : syracuseStep 1584983 = 2377475) B2377475
theorem B8892341 : Blo 127788 8892341 := bstep (se 5 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 8892341 = 833657) B833657
theorem B2503007 : Blo 127788 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B439019 : Blo 127788 439019 := bstep (se 1 (by rfl) ⟨329264, by rfl⟩ : syracuseStep 439019 = 658529) B658529
theorem B145255 : Blo 127788 145255 := bstep (se 1 (by rfl) ⟨108941, by rfl⟩ : syracuseStep 145255 = 217883) B217883
theorem B440315 : Blo 127788 440315 := bstep (se 1 (by rfl) ⟨330236, by rfl⟩ : syracuseStep 440315 = 660473) B660473
theorem B1260157 : Blo 127788 1260157 := bstep (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) B472559
theorem B15743747 : Blo 127788 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B1195721 : Blo 127788 1195721 := bstep (se 2 (by rfl) ⟨448395, by rfl⟩ : syracuseStep 1195721 = 896791) B896791
theorem B442475 : Blo 127788 442475 := bstep (se 1 (by rfl) ⟨331856, by rfl⟩ : syracuseStep 442475 = 663713) B663713
theorem B1000187 : Blo 127788 1000187 := bstep (se 1 (by rfl) ⟨750140, by rfl⟩ : syracuseStep 1000187 = 1500281) B1500281
theorem B247465 : Blo 127788 247465 := bstep (se 2 (by rfl) ⟨92799, by rfl⟩ : syracuseStep 247465 = 185599) B185599
theorem B9062441 : Blo 127788 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B1756079 : Blo 127788 1756079 := bstep (se 1 (by rfl) ⟨1317059, by rfl⟩ : syracuseStep 1756079 = 2634119) B2634119
theorem B248923 : Blo 127788 248923 := bstep (se 1 (by rfl) ⟨186692, by rfl⟩ : syracuseStep 248923 = 373385) B373385
theorem B248969 : Blo 127788 248969 := bstep (se 2 (by rfl) ⟨93363, by rfl⟩ : syracuseStep 248969 = 186727) B186727
theorem B840887 : Blo 127788 840887 := bstep (se 1 (by rfl) ⟨630665, by rfl⟩ : syracuseStep 840887 = 1261331) B1261331
theorem B251935 : Blo 127788 251935 := bstep (se 1 (by rfl) ⟨188951, by rfl⟩ : syracuseStep 251935 = 377903) B377903
theorem B711271 : Blo 127788 711271 := bstep (se 1 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 711271 = 1066907) B1066907
theorem B844319 : Blo 127788 844319 := bstep (se 1 (by rfl) ⟨633239, by rfl⟩ : syracuseStep 844319 = 1266479) B1266479
theorem B615709 : Blo 127788 615709 := bstep (se 3 (by rfl) ⟨115445, by rfl⟩ : syracuseStep 615709 = 230891) B230891
theorem B1109699 : Blo 127788 1109699 := bstep (se 1 (by rfl) ⟨832274, by rfl⟩ : syracuseStep 1109699 = 1664549) B1664549
theorem B192623 : Blo 127788 192623 := bstep (se 1 (by rfl) ⟨144467, by rfl⟩ : syracuseStep 192623 = 288935) B288935
theorem B8319347 : Blo 127788 8319347 := bstep (se 1 (by rfl) ⟨6239510, by rfl⟩ : syracuseStep 8319347 = 12479021) B12479021
theorem B3273119 : Blo 127788 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B192959 : Blo 127788 192959 := bstep (se 1 (by rfl) ⟨144719, by rfl⟩ : syracuseStep 192959 = 289439) B289439
theorem B291311 : Blo 127788 291311 := bstep (se 1 (by rfl) ⟨218483, by rfl⟩ : syracuseStep 291311 = 436967) B436967
theorem B291455 : Blo 127788 291455 := bstep (se 1 (by rfl) ⟨218591, by rfl⟩ : syracuseStep 291455 = 437183) B437183
theorem B1831567 : Blo 127788 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B324283 : Blo 127788 324283 := bstep (se 1 (by rfl) ⟨243212, by rfl⟩ : syracuseStep 324283 = 486425) B486425
theorem B1602503 : Blo 127788 1602503 := bstep (se 1 (by rfl) ⟨1201877, by rfl⟩ : syracuseStep 1602503 = 2403755) B2403755
theorem B127999 : Blo 127788 127999 := bstep (se 1 (by rfl) ⟨95999, by rfl⟩ : syracuseStep 127999 = 191999) B191999
theorem B128091 : Blo 127788 128091 := bstep (se 1 (by rfl) ⟨96068, by rfl⟩ : syracuseStep 128091 = 192137) B192137
theorem B128231 : Blo 127788 128231 := bstep (se 1 (by rfl) ⟨96173, by rfl⟩ : syracuseStep 128231 = 192347) B192347
theorem B128447 : Blo 127788 128447 := bstep (se 1 (by rfl) ⟨96335, by rfl⟩ : syracuseStep 128447 = 192671) B192671
theorem B13563425 : Blo 127788 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B489023 : Blo 127788 489023 := bstep (se 1 (by rfl) ⟨366767, by rfl⟩ : syracuseStep 489023 = 733535) B733535
theorem B128879 : Blo 127788 128879 := bstep (se 1 (by rfl) ⟨96659, by rfl⟩ : syracuseStep 128879 = 193319) B193319
theorem B4290803 : Blo 127788 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B129503 : Blo 127788 129503 := bstep (se 1 (by rfl) ⟨97127, by rfl⟩ : syracuseStep 129503 = 194255) B194255
theorem B195047 : Blo 127788 195047 := bstep (se 1 (by rfl) ⟨146285, by rfl⟩ : syracuseStep 195047 = 292571) B292571
theorem B129663 : Blo 127788 129663 := bstep (se 1 (by rfl) ⟨97247, by rfl⟩ : syracuseStep 129663 = 194495) B194495
theorem B129691 : Blo 127788 129691 := bstep (se 1 (by rfl) ⟨97268, by rfl⟩ : syracuseStep 129691 = 194537) B194537
theorem B195497 : Blo 127788 195497 := bstep (se 2 (by rfl) ⟨73311, by rfl⟩ : syracuseStep 195497 = 146623) B146623
theorem B654317 : Blo 127788 654317 := bstep (se 3 (by rfl) ⟨122684, by rfl⟩ : syracuseStep 654317 = 245369) B245369
theorem B130111 : Blo 127788 130111 := bstep (se 1 (by rfl) ⟨97583, by rfl⟩ : syracuseStep 130111 = 195167) B195167
theorem B195647 : Blo 127788 195647 := bstep (se 1 (by rfl) ⟨146735, by rfl⟩ : syracuseStep 195647 = 293471) B293471
theorem B130495 : Blo 127788 130495 := bstep (se 1 (by rfl) ⟨97871, by rfl⟩ : syracuseStep 130495 = 195743) B195743
theorem B130607 : Blo 127788 130607 := bstep (se 1 (by rfl) ⟨97955, by rfl⟩ : syracuseStep 130607 = 195911) B195911
theorem B294983 : Blo 127788 294983 := bstep (se 1 (by rfl) ⟨221237, by rfl⟩ : syracuseStep 294983 = 442475) B442475
theorem B5374613 : Blo 127788 5374613 := bstep (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) B251935
theorem B328607 : Blo 127788 328607 := bstep (se 1 (by rfl) ⟨246455, by rfl⟩ : syracuseStep 328607 = 492911) B492911
theorem B198119 : Blo 127788 198119 := bstep (se 1 (by rfl) ⟨148589, by rfl⟩ : syracuseStep 198119 = 297179) B297179
theorem B820945 : Blo 127788 820945 := bstep (se 2 (by rfl) ⟨307854, by rfl⟩ : syracuseStep 820945 = 615709) B615709
theorem B165979 : Blo 127788 165979 := bstep (se 1 (by rfl) ⟨124484, by rfl⟩ : syracuseStep 165979 = 248969) B248969
theorem B329953 : Blo 127788 329953 := bstep (se 2 (by rfl) ⟨123732, by rfl⟩ : syracuseStep 329953 = 247465) B247465
theorem B560591 : Blo 127788 560591 := bstep (se 1 (by rfl) ⟨420443, by rfl⟩ : syracuseStep 560591 = 840887) B840887
theorem B921719 : Blo 127788 921719 := bstep (se 1 (by rfl) ⟨691289, by rfl⟩ : syracuseStep 921719 = 1382579) B1382579
theorem B331897 : Blo 127788 331897 := bstep (se 2 (by rfl) ⟨124461, by rfl⟩ : syracuseStep 331897 = 248923) B248923
theorem B562879 : Blo 127788 562879 := bstep (se 1 (by rfl) ⟨422159, by rfl⟩ : syracuseStep 562879 = 844319) B844319
theorem B432377 : Blo 127788 432377 := bstep (se 2 (by rfl) ⟨162141, by rfl⟩ : syracuseStep 432377 = 324283) B324283
theorem B335719 : Blo 127788 335719 := bstep (se 1 (by rfl) ⟨251789, by rfl⟩ : syracuseStep 335719 = 503579) B503579
theorem B1056655 : Blo 127788 1056655 := bstep (se 1 (by rfl) ⟨792491, by rfl⟩ : syracuseStep 1056655 = 1584983) B1584983
theorem B5546231 : Blo 127788 5546231 := bstep (se 1 (by rfl) ⟨4159673, by rfl⟩ : syracuseStep 5546231 = 8319347) B8319347
theorem B1680209 : Blo 127788 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B2860535 : Blo 127788 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B10495831 : Blo 127788 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B436211 : Blo 127788 436211 := bstep (se 1 (by rfl) ⟨327158, by rfl⟩ : syracuseStep 436211 = 654317) B654317
theorem B797147 : Blo 127788 797147 := bstep (se 1 (by rfl) ⟨597860, by rfl⟩ : syracuseStep 797147 = 1195721) B1195721
theorem B666791 : Blo 127788 666791 := bstep (se 1 (by rfl) ⟨500093, by rfl⟩ : syracuseStep 666791 = 1000187) B1000187
theorem B437561 : Blo 127788 437561 := bstep (se 2 (by rfl) ⟨164085, by rfl⟩ : syracuseStep 437561 = 328171) B328171
theorem B372383 : Blo 127788 372383 := bstep (se 1 (by rfl) ⟨279287, by rfl⟩ : syracuseStep 372383 = 558575) B558575
theorem B6041627 : Blo 127788 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B438911 : Blo 127788 438911 := bstep (se 1 (by rfl) ⟨329183, by rfl⟩ : syracuseStep 438911 = 658367) B658367
theorem B441287 : Blo 127788 441287 := bstep (se 1 (by rfl) ⟨330965, by rfl⟩ : syracuseStep 441287 = 661931) B661931
theorem B2442089 : Blo 127788 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B739799 : Blo 127788 739799 := bstep (se 1 (by rfl) ⟨554849, by rfl⟩ : syracuseStep 739799 = 1109699) B1109699
theorem B707039 : Blo 127788 707039 := bstep (se 1 (by rfl) ⟨530279, by rfl⟩ : syracuseStep 707039 = 1060559) B1060559
theorem B2182079 : Blo 127788 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B1068335 : Blo 127788 1068335 := bstep (se 1 (by rfl) ⟨801251, by rfl⟩ : syracuseStep 1068335 = 1602503) B1602503
theorem B546871 : Blo 127788 546871 := bstep (se 1 (by rfl) ⟨410153, by rfl⟩ : syracuseStep 546871 = 820307) B820307
theorem B1170719 : Blo 127788 1170719 := bstep (se 1 (by rfl) ⟨878039, by rfl⟩ : syracuseStep 1170719 = 1756079) B1756079
theorem B221609 : Blo 127788 221609 := bstep (se 2 (by rfl) ⟨83103, by rfl⟩ : syracuseStep 221609 = 166207) B166207
theorem B549757 : Blo 127788 549757 := bstep (se 3 (by rfl) ⟨103079, by rfl⟩ : syracuseStep 549757 = 206159) B206159
theorem B746657 : Blo 127788 746657 := bstep (se 2 (by rfl) ⟨279996, by rfl⟩ : syracuseStep 746657 = 559993) B559993
theorem B288359 : Blo 127788 288359 := bstep (se 1 (by rfl) ⟨216269, by rfl⟩ : syracuseStep 288359 = 432539) B432539
theorem B944467 : Blo 127788 944467 := bstep (se 1 (by rfl) ⟨708350, by rfl⟩ : syracuseStep 944467 = 1416701) B1416701
theorem B682607 : Blo 127788 682607 := bstep (se 1 (by rfl) ⟨511955, by rfl⟩ : syracuseStep 682607 = 1023911) B1023911
theorem B290159 : Blo 127788 290159 := bstep (se 1 (by rfl) ⟨217619, by rfl⟩ : syracuseStep 290159 = 435239) B435239
theorem B291419 : Blo 127788 291419 := bstep (se 1 (by rfl) ⟨218564, by rfl⟩ : syracuseStep 291419 = 437129) B437129
theorem B488551 : Blo 127788 488551 := bstep (se 1 (by rfl) ⟨366413, by rfl⟩ : syracuseStep 488551 = 732827) B732827
theorem B193673 : Blo 127788 193673 := bstep (se 2 (by rfl) ⟨72627, by rfl⟩ : syracuseStep 193673 = 145255) B145255
theorem B5928227 : Blo 127788 5928227 := bstep (se 1 (by rfl) ⟨4446170, by rfl⟩ : syracuseStep 5928227 = 8892341) B8892341
theorem B128415 : Blo 127788 128415 := bstep (se 1 (by rfl) ⟨96311, by rfl⟩ : syracuseStep 128415 = 192623) B192623
theorem B1668671 : Blo 127788 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B128639 : Blo 127788 128639 := bstep (se 1 (by rfl) ⟨96479, by rfl⟩ : syracuseStep 128639 = 192959) B192959
theorem B194207 : Blo 127788 194207 := bstep (se 1 (by rfl) ⟨145655, by rfl⟩ : syracuseStep 194207 = 291311) B291311
theorem B194303 : Blo 127788 194303 := bstep (se 1 (by rfl) ⟨145727, by rfl⟩ : syracuseStep 194303 = 291455) B291455
theorem B292679 : Blo 127788 292679 := bstep (se 1 (by rfl) ⟨219509, by rfl⟩ : syracuseStep 292679 = 439019) B439019
theorem B948361 : Blo 127788 948361 := bstep (se 2 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 948361 = 711271) B711271
theorem B9042283 : Blo 127788 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B326015 : Blo 127788 326015 := bstep (se 1 (by rfl) ⟨244511, by rfl⟩ : syracuseStep 326015 = 489023) B489023
theorem B293543 : Blo 127788 293543 := bstep (se 1 (by rfl) ⟨220157, by rfl⟩ : syracuseStep 293543 = 440315) B440315
theorem B130031 : Blo 127788 130031 := bstep (se 1 (by rfl) ⟨97523, by rfl⟩ : syracuseStep 130031 = 195047) B195047
theorem B130331 : Blo 127788 130331 := bstep (se 1 (by rfl) ⟨97748, by rfl⟩ : syracuseStep 130331 = 195497) B195497
theorem B130431 : Blo 127788 130431 := bstep (se 1 (by rfl) ⟨97823, by rfl⟩ : syracuseStep 130431 = 195647) B195647
theorem B196655 : Blo 127788 196655 := bstep (se 1 (by rfl) ⟨147491, by rfl⟩ : syracuseStep 196655 = 294983) B294983
theorem B132079 : Blo 127788 132079 := bstep (se 1 (by rfl) ⟨99059, by rfl⟩ : syracuseStep 132079 = 198119) B198119
theorem B493199 : Blo 127788 493199 := bstep (se 1 (by rfl) ⟨369899, by rfl⟩ : syracuseStep 493199 = 739799) B739799
theorem B13994441 : Blo 127788 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B1120139 : Blo 127788 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B497771 : Blo 127788 497771 := bstep (se 1 (by rfl) ⟨373328, by rfl⟩ : syracuseStep 497771 = 746657) B746657
theorem B1907023 : Blo 127788 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B531431 : Blo 127788 531431 := bstep (se 1 (by rfl) ⟨398573, by rfl⟩ : syracuseStep 531431 = 797147) B797147
theorem B729161 : Blo 127788 729161 := bstep (se 2 (by rfl) ⟨273435, by rfl⟩ : syracuseStep 729161 = 546871) B546871
theorem B733009 : Blo 127788 733009 := bstep (se 2 (by rfl) ⟨274878, by rfl⟩ : syracuseStep 733009 = 549757) B549757
theorem B471359 : Blo 127788 471359 := bstep (se 1 (by rfl) ⟨353519, by rfl⟩ : syracuseStep 471359 = 707039) B707039
theorem B14332301 : Blo 127788 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B1094593 : Blo 127788 1094593 := bstep (se 2 (by rfl) ⟨410472, by rfl⟩ : syracuseStep 1094593 = 820945) B820945
theorem B373727 : Blo 127788 373727 := bstep (se 1 (by rfl) ⟨280295, by rfl⟩ : syracuseStep 373727 = 560591) B560591
theorem B439937 : Blo 127788 439937 := bstep (se 2 (by rfl) ⟨164976, by rfl⟩ : syracuseStep 439937 = 329953) B329953
theorem B442529 : Blo 127788 442529 := bstep (se 2 (by rfl) ⟨165948, by rfl⟩ : syracuseStep 442529 = 331897) B331897
theorem B147739 : Blo 127788 147739 := bstep (se 1 (by rfl) ⟨110804, by rfl⟩ : syracuseStep 147739 = 221609) B221609
theorem B444527 : Blo 127788 444527 := bstep (se 1 (by rfl) ⟨333395, by rfl⟩ : syracuseStep 444527 = 666791) B666791
theorem B248255 : Blo 127788 248255 := bstep (se 1 (by rfl) ⟨186191, by rfl⟩ : syracuseStep 248255 = 372383) B372383
theorem B5818877 : Blo 127788 5818877 := bstep (se 3 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 5818877 = 2182079) B2182079
theorem B1264481 : Blo 127788 1264481 := bstep (se 2 (by rfl) ⟨474180, by rfl⟩ : syracuseStep 1264481 = 948361) B948361
theorem B3952151 : Blo 127788 3952151 := bstep (se 1 (by rfl) ⟨2964113, by rfl⟩ : syracuseStep 3952151 = 5928227) B5928227
theorem B217343 : Blo 127788 217343 := bstep (se 1 (by rfl) ⟨163007, by rfl⟩ : syracuseStep 217343 = 326015) B326015
theorem B447625 : Blo 127788 447625 := bstep (se 2 (by rfl) ⟨167859, by rfl⟩ : syracuseStep 447625 = 335719) B335719
theorem B1628059 : Blo 127788 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B219071 : Blo 127788 219071 := bstep (se 1 (by rfl) ⟨164303, by rfl⟩ : syracuseStep 219071 = 328607) B328607
theorem B5037157 : Blo 127788 5037157 := bstep (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) B944467
theorem B712223 : Blo 127788 712223 := bstep (se 1 (by rfl) ⟨534167, by rfl⟩ : syracuseStep 712223 = 1068335) B1068335
theorem B614479 : Blo 127788 614479 := bstep (se 1 (by rfl) ⟨460859, by rfl⟩ : syracuseStep 614479 = 921719) B921719
theorem B221305 : Blo 127788 221305 := bstep (se 2 (by rfl) ⟨82989, by rfl⟩ : syracuseStep 221305 = 165979) B165979
theorem B288251 : Blo 127788 288251 := bstep (se 1 (by rfl) ⟨216188, by rfl⟩ : syracuseStep 288251 = 432377) B432377
theorem B780479 : Blo 127788 780479 := bstep (se 1 (by rfl) ⟨585359, by rfl⟩ : syracuseStep 780479 = 1170719) B1170719
theorem B3697487 : Blo 127788 3697487 := bstep (se 1 (by rfl) ⟨2773115, by rfl⟩ : syracuseStep 3697487 = 5546231) B5546231
theorem B192239 : Blo 127788 192239 := bstep (se 1 (by rfl) ⟨144179, by rfl⟩ : syracuseStep 192239 = 288359) B288359
theorem B290807 : Blo 127788 290807 := bstep (se 1 (by rfl) ⟨218105, by rfl⟩ : syracuseStep 290807 = 436211) B436211
theorem B651401 : Blo 127788 651401 := bstep (se 2 (by rfl) ⟨244275, by rfl⟩ : syracuseStep 651401 = 488551) B488551
theorem B455071 : Blo 127788 455071 := bstep (se 1 (by rfl) ⟨341303, by rfl⟩ : syracuseStep 455071 = 682607) B682607
theorem B291707 : Blo 127788 291707 := bstep (se 1 (by rfl) ⟨218780, by rfl⟩ : syracuseStep 291707 = 437561) B437561
theorem B193439 : Blo 127788 193439 := bstep (se 1 (by rfl) ⟨145079, by rfl⟩ : syracuseStep 193439 = 290159) B290159
theorem B750505 : Blo 127788 750505 := bstep (se 2 (by rfl) ⟨281439, by rfl⟩ : syracuseStep 750505 = 562879) B562879
theorem B4027751 : Blo 127788 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B194279 : Blo 127788 194279 := bstep (se 1 (by rfl) ⟨145709, by rfl⟩ : syracuseStep 194279 = 291419) B291419
theorem B292607 : Blo 127788 292607 := bstep (se 1 (by rfl) ⟨219455, by rfl⟩ : syracuseStep 292607 = 438911) B438911
theorem B12056377 : Blo 127788 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B129115 : Blo 127788 129115 := bstep (se 1 (by rfl) ⟨96836, by rfl⟩ : syracuseStep 129115 = 193673) B193673
theorem B1112447 : Blo 127788 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B129471 : Blo 127788 129471 := bstep (se 1 (by rfl) ⟨97103, by rfl⟩ : syracuseStep 129471 = 194207) B194207
theorem B129535 : Blo 127788 129535 := bstep (se 1 (by rfl) ⟨97151, by rfl⟩ : syracuseStep 129535 = 194303) B194303
theorem B195119 : Blo 127788 195119 := bstep (se 1 (by rfl) ⟨146339, by rfl⟩ : syracuseStep 195119 = 292679) B292679
theorem B195695 : Blo 127788 195695 := bstep (se 1 (by rfl) ⟨146771, by rfl⟩ : syracuseStep 195695 = 293543) B293543
theorem B294191 : Blo 127788 294191 := bstep (se 1 (by rfl) ⟨220643, by rfl⟩ : syracuseStep 294191 = 441287) B441287
theorem B1408873 : Blo 127788 1408873 := bstep (se 2 (by rfl) ⟨528327, by rfl⟩ : syracuseStep 1408873 = 1056655) B1056655
theorem B131103 : Blo 127788 131103 := bstep (se 1 (by rfl) ⟨98327, by rfl⟩ : syracuseStep 131103 = 196655) B196655
theorem B819305 : Blo 127788 819305 := bstep (se 2 (by rfl) ⟨307239, by rfl⟩ : syracuseStep 819305 = 614479) B614479
theorem B295019 : Blo 127788 295019 := bstep (se 1 (by rfl) ⟨221264, by rfl⟩ : syracuseStep 295019 = 442529) B442529
theorem B295073 : Blo 127788 295073 := bstep (se 2 (by rfl) ⟨110652, by rfl⟩ : syracuseStep 295073 = 221305) B221305
theorem B196985 : Blo 127788 196985 := bstep (se 2 (by rfl) ⟨73869, by rfl⟩ : syracuseStep 196985 = 147739) B147739
theorem B328799 : Blo 127788 328799 := bstep (se 1 (by rfl) ⟨246599, by rfl⟩ : syracuseStep 328799 = 493199) B493199
theorem B296351 : Blo 127788 296351 := bstep (se 1 (by rfl) ⟨222263, by rfl⟩ : syracuseStep 296351 = 444527) B444527
theorem B165503 : Blo 127788 165503 := bstep (se 1 (by rfl) ⟨124127, by rfl⟩ : syracuseStep 165503 = 248255) B248255
theorem B331847 : Blo 127788 331847 := bstep (se 1 (by rfl) ⟨248885, by rfl⟩ : syracuseStep 331847 = 497771) B497771
theorem B2464991 : Blo 127788 2464991 := bstep (se 1 (by rfl) ⟨1848743, by rfl⟩ : syracuseStep 2464991 = 3697487) B3697487
theorem B2170745 : Blo 127788 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B434267 : Blo 127788 434267 := bstep (se 1 (by rfl) ⟨325700, by rfl⟩ : syracuseStep 434267 = 651401) B651401
theorem B1878497 : Blo 127788 1878497 := bstep (se 2 (by rfl) ⟨704436, by rfl⟩ : syracuseStep 1878497 = 1408873) B1408873
theorem B1256957 : Blo 127788 1256957 := bstep (se 3 (by rfl) ⟨235679, by rfl⟩ : syracuseStep 1256957 = 471359) B471359
theorem B176105 : Blo 127788 176105 := bstep (se 2 (by rfl) ⟨66039, by rfl⟩ : syracuseStep 176105 = 132079) B132079
theorem B3879251 : Blo 127788 3879251 := bstep (se 1 (by rfl) ⟨2909438, by rfl⟩ : syracuseStep 3879251 = 5818877) B5818877
theorem B2634767 : Blo 127788 2634767 := bstep (se 1 (by rfl) ⟨1976075, by rfl⟩ : syracuseStep 2634767 = 3952151) B3952151
theorem B144895 : Blo 127788 144895 := bstep (se 1 (by rfl) ⟨108671, by rfl⟩ : syracuseStep 144895 = 217343) B217343
theorem B146047 : Blo 127788 146047 := bstep (se 1 (by rfl) ⟨109535, by rfl⟩ : syracuseStep 146047 = 219071) B219071
theorem B474815 : Blo 127788 474815 := bstep (se 1 (by rfl) ⟨356111, by rfl⟩ : syracuseStep 474815 = 712223) B712223
theorem B606761 : Blo 127788 606761 := bstep (se 2 (by rfl) ⟨227535, by rfl⟩ : syracuseStep 606761 = 455071) B455071
theorem B1000673 : Blo 127788 1000673 := bstep (se 2 (by rfl) ⟨375252, by rfl⟩ : syracuseStep 1000673 = 750505) B750505
theorem B1459457 : Blo 127788 1459457 := bstep (se 2 (by rfl) ⟨547296, by rfl⟩ : syracuseStep 1459457 = 1094593) B1094593
theorem B16075169 : Blo 127788 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B9554867 : Blo 127788 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B2542697 : Blo 127788 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B249151 : Blo 127788 249151 := bstep (se 1 (by rfl) ⟨186863, by rfl⟩ : syracuseStep 249151 = 373727) B373727
theorem B741631 : Blo 127788 741631 := bstep (se 1 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 741631 = 1112447) B1112447
theorem B9329627 : Blo 127788 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B842987 : Blo 127788 842987 := bstep (se 1 (by rfl) ⟨632240, by rfl⟩ : syracuseStep 842987 = 1264481) B1264481
theorem B746759 : Blo 127788 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B354287 : Blo 127788 354287 := bstep (se 1 (by rfl) ⟨265715, by rfl⟩ : syracuseStep 354287 = 531431) B531431
theorem B977345 : Blo 127788 977345 := bstep (se 2 (by rfl) ⟨366504, by rfl⟩ : syracuseStep 977345 = 733009) B733009
theorem B486107 : Blo 127788 486107 := bstep (se 1 (by rfl) ⟨364580, by rfl⟩ : syracuseStep 486107 = 729161) B729161
theorem B2387333 : Blo 127788 2387333 := bstep (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) B447625
theorem B192167 : Blo 127788 192167 := bstep (se 1 (by rfl) ⟨144125, by rfl⟩ : syracuseStep 192167 = 288251) B288251
theorem B520319 : Blo 127788 520319 := bstep (se 1 (by rfl) ⟨390239, by rfl⟩ : syracuseStep 520319 = 780479) B780479
theorem B128159 : Blo 127788 128159 := bstep (se 1 (by rfl) ⟨96119, by rfl⟩ : syracuseStep 128159 = 192239) B192239
theorem B193871 : Blo 127788 193871 := bstep (se 1 (by rfl) ⟨145403, by rfl⟩ : syracuseStep 193871 = 290807) B290807
theorem B194471 : Blo 127788 194471 := bstep (se 1 (by rfl) ⟨145853, by rfl⟩ : syracuseStep 194471 = 291707) B291707
theorem B128959 : Blo 127788 128959 := bstep (se 1 (by rfl) ⟨96719, by rfl⟩ : syracuseStep 128959 = 193439) B193439
theorem B2685167 : Blo 127788 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B293291 : Blo 127788 293291 := bstep (se 1 (by rfl) ⟨219968, by rfl⟩ : syracuseStep 293291 = 439937) B439937
theorem B129519 : Blo 127788 129519 := bstep (se 1 (by rfl) ⟨97139, by rfl⟩ : syracuseStep 129519 = 194279) B194279
theorem B195071 : Blo 127788 195071 := bstep (se 1 (by rfl) ⟨146303, by rfl⟩ : syracuseStep 195071 = 292607) B292607
theorem B6716209 : Blo 127788 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B130079 : Blo 127788 130079 := bstep (se 1 (by rfl) ⟨97559, by rfl⟩ : syracuseStep 130079 = 195119) B195119
theorem B130463 : Blo 127788 130463 := bstep (se 1 (by rfl) ⟨97847, by rfl⟩ : syracuseStep 130463 = 195695) B195695
theorem B196127 : Blo 127788 196127 := bstep (se 1 (by rfl) ⟨147095, by rfl⟩ : syracuseStep 196127 = 294191) B294191
theorem B196679 : Blo 127788 196679 := bstep (se 1 (by rfl) ⟨147509, by rfl⟩ : syracuseStep 196679 = 295019) B295019
theorem B196715 : Blo 127788 196715 := bstep (se 1 (by rfl) ⟨147536, by rfl⟩ : syracuseStep 196715 = 295073) B295073
theorem B131323 : Blo 127788 131323 := bstep (se 1 (by rfl) ⟨98492, by rfl⟩ : syracuseStep 131323 = 196985) B196985
theorem B197567 : Blo 127788 197567 := bstep (se 1 (by rfl) ⟨148175, by rfl⟩ : syracuseStep 197567 = 296351) B296351
theorem B10716779 : Blo 127788 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B332201 : Blo 127788 332201 := bstep (se 2 (by rfl) ⟨124575, by rfl⟩ : syracuseStep 332201 = 249151) B249151
theorem B1643327 : Blo 127788 1643327 := bstep (se 1 (by rfl) ⟨1232495, by rfl⟩ : syracuseStep 1643327 = 2464991) B2464991
theorem B561991 : Blo 127788 561991 := bstep (se 1 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 561991 = 842987) B842987
theorem B1447163 : Blo 127788 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B988841 : Blo 127788 988841 := bstep (se 2 (by rfl) ⟨370815, by rfl⟩ : syracuseStep 988841 = 741631) B741631
theorem B497839 : Blo 127788 497839 := bstep (se 1 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 497839 = 746759) B746759
theorem B236191 : Blo 127788 236191 := bstep (se 1 (by rfl) ⟨177143, by rfl⟩ : syracuseStep 236191 = 354287) B354287
theorem B1252331 : Blo 127788 1252331 := bstep (se 1 (by rfl) ⟨939248, by rfl⟩ : syracuseStep 1252331 = 1878497) B1878497
theorem B24879005 : Blo 127788 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B6366221 : Blo 127788 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B8954945 : Blo 127788 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B469613 : Blo 127788 469613 := bstep (se 3 (by rfl) ⟨88052, by rfl⟩ : syracuseStep 469613 = 176105) B176105
theorem B404507 : Blo 127788 404507 := bstep (se 1 (by rfl) ⟨303380, by rfl⟩ : syracuseStep 404507 = 606761) B606761
theorem B667115 : Blo 127788 667115 := bstep (se 1 (by rfl) ⟨500336, by rfl⟩ : syracuseStep 667115 = 1000673) B1000673
theorem B6369911 : Blo 127788 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B441341 : Blo 127788 441341 := bstep (se 3 (by rfl) ⟨82751, by rfl⟩ : syracuseStep 441341 = 165503) B165503
theorem B837971 : Blo 127788 837971 := bstep (se 1 (by rfl) ⟨628478, by rfl⟩ : syracuseStep 837971 = 1256957) B1256957
theorem B346879 : Blo 127788 346879 := bstep (se 1 (by rfl) ⟨260159, by rfl⟩ : syracuseStep 346879 = 520319) B520319
theorem B1756511 : Blo 127788 1756511 := bstep (se 1 (by rfl) ⟨1317383, by rfl⟩ : syracuseStep 1756511 = 2634767) B2634767
theorem B1790111 : Blo 127788 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B316543 : Blo 127788 316543 := bstep (se 1 (by rfl) ⟨237407, by rfl⟩ : syracuseStep 316543 = 474815) B474815
theorem B546203 : Blo 127788 546203 := bstep (se 1 (by rfl) ⟨409652, by rfl⟩ : syracuseStep 546203 = 819305) B819305
theorem B219199 : Blo 127788 219199 := bstep (se 1 (by rfl) ⟨164399, by rfl⟩ : syracuseStep 219199 = 328799) B328799
theorem B972971 : Blo 127788 972971 := bstep (se 1 (by rfl) ⟨729728, by rfl⟩ : syracuseStep 972971 = 1459457) B1459457
theorem B1695131 : Blo 127788 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B221231 : Blo 127788 221231 := bstep (se 1 (by rfl) ⟨165923, by rfl⟩ : syracuseStep 221231 = 331847) B331847
theorem B289511 : Blo 127788 289511 := bstep (se 1 (by rfl) ⟨217133, by rfl⟩ : syracuseStep 289511 = 434267) B434267
theorem B651563 : Blo 127788 651563 := bstep (se 1 (by rfl) ⟨488672, by rfl⟩ : syracuseStep 651563 = 977345) B977345
theorem B324071 : Blo 127788 324071 := bstep (se 1 (by rfl) ⟨243053, by rfl⟩ : syracuseStep 324071 = 486107) B486107
theorem B193193 : Blo 127788 193193 := bstep (se 2 (by rfl) ⟨72447, by rfl⟩ : syracuseStep 193193 = 144895) B144895
theorem B128111 : Blo 127788 128111 := bstep (se 1 (by rfl) ⟨96083, by rfl⟩ : syracuseStep 128111 = 192167) B192167
theorem B2586167 : Blo 127788 2586167 := bstep (se 1 (by rfl) ⟨1939625, by rfl⟩ : syracuseStep 2586167 = 3879251) B3879251
theorem B194729 : Blo 127788 194729 := bstep (se 2 (by rfl) ⟨73023, by rfl⟩ : syracuseStep 194729 = 146047) B146047
theorem B129247 : Blo 127788 129247 := bstep (se 1 (by rfl) ⟨96935, by rfl⟩ : syracuseStep 129247 = 193871) B193871
theorem B129647 : Blo 127788 129647 := bstep (se 1 (by rfl) ⟨97235, by rfl⟩ : syracuseStep 129647 = 194471) B194471
theorem B195527 : Blo 127788 195527 := bstep (se 1 (by rfl) ⟨146645, by rfl⟩ : syracuseStep 195527 = 293291) B293291
theorem B130047 : Blo 127788 130047 := bstep (se 1 (by rfl) ⟨97535, by rfl⟩ : syracuseStep 130047 = 195071) B195071
theorem B130751 : Blo 127788 130751 := bstep (se 1 (by rfl) ⟨98063, by rfl⟩ : syracuseStep 130751 = 196127) B196127
theorem B131119 : Blo 127788 131119 := bstep (se 1 (by rfl) ⟨98339, by rfl⟩ : syracuseStep 131119 = 196679) B196679
theorem B131143 : Blo 127788 131143 := bstep (se 1 (by rfl) ⟨98357, by rfl⟩ : syracuseStep 131143 = 196715) B196715
theorem B131711 : Blo 127788 131711 := bstep (se 1 (by rfl) ⟨98783, by rfl⟩ : syracuseStep 131711 = 197567) B197567
theorem B7144519 : Blo 127788 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B558647 : Blo 127788 558647 := bstep (se 1 (by rfl) ⟨418985, by rfl⟩ : syracuseStep 558647 = 837971) B837971
theorem B462505 : Blo 127788 462505 := bstep (se 2 (by rfl) ⟨173439, by rfl⟩ : syracuseStep 462505 = 346879) B346879
theorem B659227 : Blo 127788 659227 := bstep (se 1 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 659227 = 988841) B988841
theorem B16586003 : Blo 127788 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B5969963 : Blo 127788 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B269671 : Blo 127788 269671 := bstep (se 1 (by rfl) ⟨202253, by rfl⟩ : syracuseStep 269671 = 404507) B404507
theorem B434375 : Blo 127788 434375 := bstep (se 1 (by rfl) ⟨325781, by rfl⟩ : syracuseStep 434375 = 651563) B651563
theorem B663785 : Blo 127788 663785 := bstep (se 2 (by rfl) ⟨248919, by rfl⟩ : syracuseStep 663785 = 497839) B497839
theorem B1095551 : Blo 127788 1095551 := bstep (se 1 (by rfl) ⟨821663, by rfl⟩ : syracuseStep 1095551 = 1643327) B1643327
theorem B964775 : Blo 127788 964775 := bstep (se 1 (by rfl) ⟨723581, by rfl⟩ : syracuseStep 964775 = 1447163) B1447163
theorem B1456541 : Blo 127788 1456541 := bstep (se 3 (by rfl) ⟨273101, by rfl⟩ : syracuseStep 1456541 = 546203) B546203
theorem B834887 : Blo 127788 834887 := bstep (se 1 (by rfl) ⟨626165, by rfl⟩ : syracuseStep 834887 = 1252331) B1252331
theorem B1130087 : Blo 127788 1130087 := bstep (se 1 (by rfl) ⟨847565, by rfl⟩ : syracuseStep 1130087 = 1695131) B1695131
theorem B147487 : Blo 127788 147487 := bstep (se 1 (by rfl) ⟨110615, by rfl⟩ : syracuseStep 147487 = 221231) B221231
theorem B4244147 : Blo 127788 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B313075 : Blo 127788 313075 := bstep (se 1 (by rfl) ⟨234806, by rfl⟩ : syracuseStep 313075 = 469613) B469613
theorem B444743 : Blo 127788 444743 := bstep (se 1 (by rfl) ⟨333557, by rfl⟩ : syracuseStep 444743 = 667115) B667115
theorem B216047 : Blo 127788 216047 := bstep (se 1 (by rfl) ⟨162035, by rfl⟩ : syracuseStep 216047 = 324071) B324071
theorem B4246607 : Blo 127788 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B314921 : Blo 127788 314921 := bstep (se 2 (by rfl) ⟨118095, by rfl⟩ : syracuseStep 314921 = 236191) B236191
theorem B1724111 : Blo 127788 1724111 := bstep (se 1 (by rfl) ⟨1293083, by rfl⟩ : syracuseStep 1724111 = 2586167) B2586167
theorem B4773629 : Blo 127788 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B1171007 : Blo 127788 1171007 := bstep (se 1 (by rfl) ⟨878255, by rfl⟩ : syracuseStep 1171007 = 1756511) B1756511
theorem B221467 : Blo 127788 221467 := bstep (se 1 (by rfl) ⟨166100, by rfl⟩ : syracuseStep 221467 = 332201) B332201
theorem B648647 : Blo 127788 648647 := bstep (se 1 (by rfl) ⟨486485, by rfl⟩ : syracuseStep 648647 = 972971) B972971
theorem B749321 : Blo 127788 749321 := bstep (se 2 (by rfl) ⟨280995, by rfl⟩ : syracuseStep 749321 = 561991) B561991
theorem B422057 : Blo 127788 422057 := bstep (se 2 (by rfl) ⟨158271, by rfl⟩ : syracuseStep 422057 = 316543) B316543
theorem B193007 : Blo 127788 193007 := bstep (se 1 (by rfl) ⟨144755, by rfl⟩ : syracuseStep 193007 = 289511) B289511
theorem B292265 : Blo 127788 292265 := bstep (se 2 (by rfl) ⟨109599, by rfl⟩ : syracuseStep 292265 = 219199) B219199
theorem B128795 : Blo 127788 128795 := bstep (se 1 (by rfl) ⟨96596, by rfl⟩ : syracuseStep 128795 = 193193) B193193
theorem B129819 : Blo 127788 129819 := bstep (se 1 (by rfl) ⟨97364, by rfl⟩ : syracuseStep 129819 = 194729) B194729
theorem B130351 : Blo 127788 130351 := bstep (se 1 (by rfl) ⟨97763, by rfl⟩ : syracuseStep 130351 = 195527) B195527
theorem B294227 : Blo 127788 294227 := bstep (se 1 (by rfl) ⟨220670, by rfl⟩ : syracuseStep 294227 = 441341) B441341
theorem B196649 : Blo 127788 196649 := bstep (se 2 (by rfl) ⟨73743, by rfl⟩ : syracuseStep 196649 = 147487) B147487
theorem B295289 : Blo 127788 295289 := bstep (se 2 (by rfl) ⟨110733, by rfl⟩ : syracuseStep 295289 = 221467) B221467
theorem B296495 : Blo 127788 296495 := bstep (se 1 (by rfl) ⟨222371, by rfl⟩ : syracuseStep 296495 = 444743) B444743
theorem B1149407 : Blo 127788 1149407 := bstep (se 1 (by rfl) ⟨862055, by rfl⟩ : syracuseStep 1149407 = 1724111) B1724111
theorem B3182419 : Blo 127788 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B432431 : Blo 127788 432431 := bstep (se 1 (by rfl) ⟨324323, by rfl⟩ : syracuseStep 432431 = 648647) B648647
theorem B499547 : Blo 127788 499547 := bstep (se 1 (by rfl) ⟨374660, by rfl⟩ : syracuseStep 499547 = 749321) B749321
theorem B730367 : Blo 127788 730367 := bstep (se 1 (by rfl) ⟨547775, by rfl⟩ : syracuseStep 730367 = 1095551) B1095551
theorem B1125485 : Blo 127788 1125485 := bstep (se 3 (by rfl) ⟨211028, by rfl⟩ : syracuseStep 1125485 = 422057) B422057
theorem B2829431 : Blo 127788 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B372431 : Blo 127788 372431 := bstep (se 1 (by rfl) ⟨279323, by rfl⟩ : syracuseStep 372431 = 558647) B558647
theorem B144031 : Blo 127788 144031 := bstep (se 1 (by rfl) ⟨108023, by rfl⟩ : syracuseStep 144031 = 216047) B216047
theorem B2831071 : Blo 127788 2831071 := bstep (se 1 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 2831071 = 4246607) B4246607
theorem B209947 : Blo 127788 209947 := bstep (se 1 (by rfl) ⟨157460, by rfl⟩ : syracuseStep 209947 = 314921) B314921
theorem B3979975 : Blo 127788 3979975 := bstep (se 1 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 3979975 = 5969963) B5969963
theorem B442523 : Blo 127788 442523 := bstep (se 1 (by rfl) ⟨331892, by rfl⟩ : syracuseStep 442523 = 663785) B663785
theorem B643183 : Blo 127788 643183 := bstep (se 1 (by rfl) ⟨482387, by rfl⟩ : syracuseStep 643183 = 964775) B964775
theorem B971027 : Blo 127788 971027 := bstep (se 1 (by rfl) ⟨728270, by rfl⟩ : syracuseStep 971027 = 1456541) B1456541
theorem B9526025 : Blo 127788 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B417433 : Blo 127788 417433 := bstep (se 2 (by rfl) ⟨156537, by rfl⟩ : syracuseStep 417433 = 313075) B313075
theorem B44229341 : Blo 127788 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B616673 : Blo 127788 616673 := bstep (se 2 (by rfl) ⟨231252, by rfl⟩ : syracuseStep 616673 = 462505) B462505
theorem B878969 : Blo 127788 878969 := bstep (se 2 (by rfl) ⟨329613, by rfl⟩ : syracuseStep 878969 = 659227) B659227
theorem B780671 : Blo 127788 780671 := bstep (se 1 (by rfl) ⟨585503, by rfl⟩ : syracuseStep 780671 = 1171007) B1171007
theorem B289583 : Blo 127788 289583 := bstep (se 1 (by rfl) ⟨217187, by rfl⟩ : syracuseStep 289583 = 434375) B434375
theorem B128671 : Blo 127788 128671 := bstep (se 1 (by rfl) ⟨96503, by rfl⟩ : syracuseStep 128671 = 193007) B193007
theorem B2226365 : Blo 127788 2226365 := bstep (se 3 (by rfl) ⟨417443, by rfl⟩ : syracuseStep 2226365 = 834887) B834887
theorem B194843 : Blo 127788 194843 := bstep (se 1 (by rfl) ⟨146132, by rfl⟩ : syracuseStep 194843 = 292265) B292265
theorem B359561 : Blo 127788 359561 := bstep (se 2 (by rfl) ⟨134835, by rfl⟩ : syracuseStep 359561 = 269671) B269671
theorem B196151 : Blo 127788 196151 := bstep (se 1 (by rfl) ⟨147113, by rfl⟩ : syracuseStep 196151 = 294227) B294227
theorem B753391 : Blo 127788 753391 := bstep (se 1 (by rfl) ⟨565043, by rfl⟩ : syracuseStep 753391 = 1130087) B1130087
theorem B131099 : Blo 127788 131099 := bstep (se 1 (by rfl) ⟨98324, by rfl⟩ : syracuseStep 131099 = 196649) B196649
theorem B295015 : Blo 127788 295015 := bstep (se 1 (by rfl) ⟨221261, by rfl⟩ : syracuseStep 295015 = 442523) B442523
theorem B196859 : Blo 127788 196859 := bstep (se 1 (by rfl) ⟨147644, by rfl⟩ : syracuseStep 196859 = 295289) B295289
theorem B197663 : Blo 127788 197663 := bstep (se 1 (by rfl) ⟨148247, by rfl⟩ : syracuseStep 197663 = 296495) B296495
theorem B333031 : Blo 127788 333031 := bstep (se 1 (by rfl) ⟨249773, by rfl⟩ : syracuseStep 333031 = 499547) B499547
theorem B3774761 : Blo 127788 3774761 := bstep (se 2 (by rfl) ⟨1415535, by rfl⟩ : syracuseStep 3774761 = 2831071) B2831071
theorem B1484243 : Blo 127788 1484243 := bstep (se 1 (by rfl) ⟨1113182, by rfl⟩ : syracuseStep 1484243 = 2226365) B2226365
theorem B239707 : Blo 127788 239707 := bstep (se 1 (by rfl) ⟨179780, by rfl⟩ : syracuseStep 239707 = 359561) B359561
theorem B766271 : Blo 127788 766271 := bstep (se 1 (by rfl) ⟨574703, by rfl⟩ : syracuseStep 766271 = 1149407) B1149407
theorem B4243225 : Blo 127788 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B2343917 : Blo 127788 2343917 := bstep (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) B878969
theorem B279929 : Blo 127788 279929 := bstep (se 2 (by rfl) ⟨104973, by rfl⟩ : syracuseStep 279929 = 209947) B209947
theorem B411115 : Blo 127788 411115 := bstep (se 1 (by rfl) ⟨308336, by rfl⟩ : syracuseStep 411115 = 616673) B616673
theorem B1886287 : Blo 127788 1886287 := bstep (se 1 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 1886287 = 2829431) B2829431
theorem B248287 : Blo 127788 248287 := bstep (se 1 (by rfl) ⟨186215, by rfl⟩ : syracuseStep 248287 = 372431) B372431
theorem B1004521 : Blo 127788 1004521 := bstep (se 2 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 1004521 = 753391) B753391
theorem B13721237 : Blo 127788 13721237 := bstep (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) B643183
theorem B647351 : Blo 127788 647351 := bstep (se 1 (by rfl) ⟨485513, by rfl⟩ : syracuseStep 647351 = 971027) B971027
theorem B288287 : Blo 127788 288287 := bstep (se 1 (by rfl) ⟨216215, by rfl⟩ : syracuseStep 288287 = 432431) B432431
theorem B6350683 : Blo 127788 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B29486227 : Blo 127788 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B486911 : Blo 127788 486911 := bstep (se 1 (by rfl) ⟨365183, by rfl⟩ : syracuseStep 486911 = 730367) B730367
theorem B192041 : Blo 127788 192041 := bstep (se 2 (by rfl) ⟨72015, by rfl⟩ : syracuseStep 192041 = 144031) B144031
theorem B520447 : Blo 127788 520447 := bstep (se 1 (by rfl) ⟨390335, by rfl⟩ : syracuseStep 520447 = 780671) B780671
theorem B193055 : Blo 127788 193055 := bstep (se 1 (by rfl) ⟨144791, by rfl⟩ : syracuseStep 193055 = 289583) B289583
theorem B750323 : Blo 127788 750323 := bstep (se 1 (by rfl) ⟨562742, by rfl⟩ : syracuseStep 750323 = 1125485) B1125485
theorem B5306633 : Blo 127788 5306633 := bstep (se 2 (by rfl) ⟨1989987, by rfl⟩ : syracuseStep 5306633 = 3979975) B3979975
theorem B129895 : Blo 127788 129895 := bstep (se 1 (by rfl) ⟨97421, by rfl⟩ : syracuseStep 129895 = 194843) B194843
theorem B556577 : Blo 127788 556577 := bstep (se 2 (by rfl) ⟨208716, by rfl⟩ : syracuseStep 556577 = 417433) B417433
theorem B130767 : Blo 127788 130767 := bstep (se 1 (by rfl) ⟨98075, by rfl⟩ : syracuseStep 130767 = 196151) B196151
theorem B393353 : Blo 127788 393353 := bstep (se 2 (by rfl) ⟨147507, by rfl⟩ : syracuseStep 393353 = 295015) B295015
theorem B131239 : Blo 127788 131239 := bstep (se 1 (by rfl) ⟨98429, by rfl⟩ : syracuseStep 131239 = 196859) B196859
theorem B131775 : Blo 127788 131775 := bstep (se 1 (by rfl) ⟨98831, by rfl⟩ : syracuseStep 131775 = 197663) B197663
theorem B331049 : Blo 127788 331049 := bstep (se 2 (by rfl) ⟨124143, by rfl⟩ : syracuseStep 331049 = 248287) B248287
theorem B9147491 : Blo 127788 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B431567 : Blo 127788 431567 := bstep (se 1 (by rfl) ⟨323675, by rfl⟩ : syracuseStep 431567 = 647351) B647351
theorem B693929 : Blo 127788 693929 := bstep (se 2 (by rfl) ⟨260223, by rfl⟩ : syracuseStep 693929 = 520447) B520447
theorem B989495 : Blo 127788 989495 := bstep (se 1 (by rfl) ⟨742121, by rfl⟩ : syracuseStep 989495 = 1484243) B1484243
theorem B500215 : Blo 127788 500215 := bstep (se 1 (by rfl) ⟨375161, by rfl⟩ : syracuseStep 500215 = 750323) B750323
theorem B371051 : Blo 127788 371051 := bstep (se 1 (by rfl) ⟨278288, by rfl⟩ : syracuseStep 371051 = 556577) B556577
theorem B2043389 : Blo 127788 2043389 := bstep (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) B766271
theorem B8467577 : Blo 127788 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B444041 : Blo 127788 444041 := bstep (se 2 (by rfl) ⟨166515, by rfl⟩ : syracuseStep 444041 = 333031) B333031
theorem B5657633 : Blo 127788 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B1562611 : Blo 127788 1562611 := bstep (se 1 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 1562611 = 2343917) B2343917
theorem B186619 : Blo 127788 186619 := bstep (se 1 (by rfl) ⟨139964, by rfl⟩ : syracuseStep 186619 = 279929) B279929
theorem B548153 : Blo 127788 548153 := bstep (se 2 (by rfl) ⟨205557, by rfl⟩ : syracuseStep 548153 = 411115) B411115
theorem B2515049 : Blo 127788 2515049 := bstep (se 2 (by rfl) ⟨943143, by rfl⟩ : syracuseStep 2515049 = 1886287) B1886287
theorem B319609 : Blo 127788 319609 := bstep (se 2 (by rfl) ⟨119853, by rfl⟩ : syracuseStep 319609 = 239707) B239707
theorem B39314969 : Blo 127788 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B2516507 : Blo 127788 2516507 := bstep (se 1 (by rfl) ⟨1887380, by rfl⟩ : syracuseStep 2516507 = 3774761) B3774761
theorem B192191 : Blo 127788 192191 := bstep (se 1 (by rfl) ⟨144143, by rfl⟩ : syracuseStep 192191 = 288287) B288287
theorem B1339361 : Blo 127788 1339361 := bstep (se 2 (by rfl) ⟨502260, by rfl⟩ : syracuseStep 1339361 = 1004521) B1004521
theorem B324607 : Blo 127788 324607 := bstep (se 1 (by rfl) ⟨243455, by rfl⟩ : syracuseStep 324607 = 486911) B486911
theorem B128027 : Blo 127788 128027 := bstep (se 1 (by rfl) ⟨96020, by rfl⟩ : syracuseStep 128027 = 192041) B192041
theorem B128703 : Blo 127788 128703 := bstep (se 1 (by rfl) ⟨96527, by rfl⟩ : syracuseStep 128703 = 193055) B193055
theorem B3537755 : Blo 127788 3537755 := bstep (se 1 (by rfl) ⟨2653316, by rfl⟩ : syracuseStep 3537755 = 5306633) B5306633
theorem B262235 : Blo 127788 262235 := bstep (se 1 (by rfl) ⟨196676, by rfl⟩ : syracuseStep 262235 = 393353) B393353
theorem B426145 : Blo 127788 426145 := bstep (se 2 (by rfl) ⟨159804, by rfl⟩ : syracuseStep 426145 = 319609) B319609
theorem B296027 : Blo 127788 296027 := bstep (se 1 (by rfl) ⟨222020, by rfl⟩ : syracuseStep 296027 = 444041) B444041
theorem B3771755 : Blo 127788 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B6098327 : Blo 127788 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B462619 : Blo 127788 462619 := bstep (se 1 (by rfl) ⟨346964, by rfl⟩ : syracuseStep 462619 = 693929) B693929
theorem B659663 : Blo 127788 659663 := bstep (se 1 (by rfl) ⟨494747, by rfl⟩ : syracuseStep 659663 = 989495) B989495
theorem B365435 : Blo 127788 365435 := bstep (se 1 (by rfl) ⟨274076, by rfl⟩ : syracuseStep 365435 = 548153) B548153
theorem B1676699 : Blo 127788 1676699 := bstep (se 1 (by rfl) ⟨1257524, by rfl⟩ : syracuseStep 1676699 = 2515049) B2515049
theorem B1677671 : Blo 127788 1677671 := bstep (se 1 (by rfl) ⟨1258253, by rfl⟩ : syracuseStep 1677671 = 2516507) B2516507
theorem B432809 : Blo 127788 432809 := bstep (se 2 (by rfl) ⟨162303, by rfl⟩ : syracuseStep 432809 = 324607) B324607
theorem B892907 : Blo 127788 892907 := bstep (se 1 (by rfl) ⟨669680, by rfl⟩ : syracuseStep 892907 = 1339361) B1339361
theorem B5645051 : Blo 127788 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B5449037 : Blo 127788 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B666953 : Blo 127788 666953 := bstep (se 2 (by rfl) ⟨250107, by rfl⟩ : syracuseStep 666953 = 500215) B500215
theorem B247367 : Blo 127788 247367 := bstep (se 1 (by rfl) ⟨185525, by rfl⟩ : syracuseStep 247367 = 371051) B371051
theorem B2083481 : Blo 127788 2083481 := bstep (se 2 (by rfl) ⟨781305, by rfl⟩ : syracuseStep 2083481 = 1562611) B1562611
theorem B248825 : Blo 127788 248825 := bstep (se 2 (by rfl) ⟨93309, by rfl⟩ : syracuseStep 248825 = 186619) B186619
theorem B220699 : Blo 127788 220699 := bstep (se 1 (by rfl) ⟨165524, by rfl⟩ : syracuseStep 220699 = 331049) B331049
theorem B287711 : Blo 127788 287711 := bstep (se 1 (by rfl) ⟨215783, by rfl⟩ : syracuseStep 287711 = 431567) B431567
theorem B26209979 : Blo 127788 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B128127 : Blo 127788 128127 := bstep (se 1 (by rfl) ⟨96095, by rfl⟩ : syracuseStep 128127 = 192191) B192191
theorem B2358503 : Blo 127788 2358503 := bstep (se 1 (by rfl) ⟨1768877, by rfl⟩ : syracuseStep 2358503 = 3537755) B3537755
theorem B197351 : Blo 127788 197351 := bstep (se 1 (by rfl) ⟨148013, by rfl⟩ : syracuseStep 197351 = 296027) B296027
theorem B164911 : Blo 127788 164911 := bstep (se 1 (by rfl) ⟨123683, by rfl⟩ : syracuseStep 164911 = 247367) B247367
theorem B165883 : Blo 127788 165883 := bstep (se 1 (by rfl) ⟨124412, by rfl⟩ : syracuseStep 165883 = 248825) B248825
theorem B4065551 : Blo 127788 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B1117799 : Blo 127788 1117799 := bstep (se 1 (by rfl) ⟨838349, by rfl⟩ : syracuseStep 1117799 = 1676699) B1676699
theorem B1118447 : Blo 127788 1118447 := bstep (se 1 (by rfl) ⟨838835, by rfl⟩ : syracuseStep 1118447 = 1677671) B1677671
theorem B595271 : Blo 127788 595271 := bstep (se 1 (by rfl) ⟨446453, by rfl⟩ : syracuseStep 595271 = 892907) B892907
theorem B17473319 : Blo 127788 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B568193 : Blo 127788 568193 := bstep (se 2 (by rfl) ⟨213072, by rfl⟩ : syracuseStep 568193 = 426145) B426145
theorem B699293 : Blo 127788 699293 := bstep (se 3 (by rfl) ⟨131117, by rfl⟩ : syracuseStep 699293 = 262235) B262235
theorem B1388987 : Blo 127788 1388987 := bstep (se 1 (by rfl) ⟨1041740, by rfl⟩ : syracuseStep 1388987 = 2083481) B2083481
theorem B439775 : Blo 127788 439775 := bstep (se 1 (by rfl) ⟨329831, by rfl⟩ : syracuseStep 439775 = 659663) B659663
theorem B243623 : Blo 127788 243623 := bstep (se 1 (by rfl) ⟨182717, by rfl⟩ : syracuseStep 243623 = 365435) B365435
theorem B14530765 : Blo 127788 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B444635 : Blo 127788 444635 := bstep (se 1 (by rfl) ⟨333476, by rfl⟩ : syracuseStep 444635 = 666953) B666953
theorem B2514503 : Blo 127788 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B288539 : Blo 127788 288539 := bstep (se 1 (by rfl) ⟨216404, by rfl⟩ : syracuseStep 288539 = 432809) B432809
theorem B616825 : Blo 127788 616825 := bstep (se 2 (by rfl) ⟨231309, by rfl⟩ : syracuseStep 616825 = 462619) B462619
theorem B3763367 : Blo 127788 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B191807 : Blo 127788 191807 := bstep (se 1 (by rfl) ⟨143855, by rfl⟩ : syracuseStep 191807 = 287711) B287711
theorem B294265 : Blo 127788 294265 := bstep (se 2 (by rfl) ⟨110349, by rfl⟩ : syracuseStep 294265 = 220699) B220699
theorem B1572335 : Blo 127788 1572335 := bstep (se 1 (by rfl) ⟨1179251, by rfl⟩ : syracuseStep 1572335 = 2358503) B2358503
theorem B131567 : Blo 127788 131567 := bstep (se 1 (by rfl) ⟨98675, by rfl⟩ : syracuseStep 131567 = 197351) B197351
theorem B296423 : Blo 127788 296423 := bstep (se 1 (by rfl) ⟨222317, by rfl⟩ : syracuseStep 296423 = 444635) B444635
theorem B822433 : Blo 127788 822433 := bstep (se 2 (by rfl) ⟨308412, by rfl⟩ : syracuseStep 822433 = 616825) B616825
theorem B396847 : Blo 127788 396847 := bstep (se 1 (by rfl) ⟨297635, by rfl⟩ : syracuseStep 396847 = 595271) B595271
theorem B1676335 : Blo 127788 1676335 := bstep (se 1 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 1676335 = 2514503) B2514503
theorem B1515181 : Blo 127788 1515181 := bstep (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) B568193
theorem B19374353 : Blo 127788 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B925991 : Blo 127788 925991 := bstep (se 1 (by rfl) ⟨694493, by rfl⟩ : syracuseStep 925991 = 1388987) B1388987
theorem B11648879 : Blo 127788 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B2508911 : Blo 127788 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B219881 : Blo 127788 219881 := bstep (se 2 (by rfl) ⟨82455, by rfl⟩ : syracuseStep 219881 = 164911) B164911
theorem B2710367 : Blo 127788 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B745199 : Blo 127788 745199 := bstep (se 1 (by rfl) ⟨558899, by rfl⟩ : syracuseStep 745199 = 1117799) B1117799
theorem B221177 : Blo 127788 221177 := bstep (se 2 (by rfl) ⟨82941, by rfl⟩ : syracuseStep 221177 = 165883) B165883
theorem B745631 : Blo 127788 745631 := bstep (se 1 (by rfl) ⟨559223, by rfl⟩ : syracuseStep 745631 = 1118447) B1118447
theorem B192359 : Blo 127788 192359 := bstep (se 1 (by rfl) ⟨144269, by rfl⟩ : syracuseStep 192359 = 288539) B288539
theorem B127871 : Blo 127788 127871 := bstep (se 1 (by rfl) ⟨95903, by rfl⟩ : syracuseStep 127871 = 191807) B191807
theorem B1864781 : Blo 127788 1864781 := bstep (se 3 (by rfl) ⟨349646, by rfl⟩ : syracuseStep 1864781 = 699293) B699293
theorem B293183 : Blo 127788 293183 := bstep (se 1 (by rfl) ⟨219887, by rfl⟩ : syracuseStep 293183 = 439775) B439775
theorem B162415 : Blo 127788 162415 := bstep (se 1 (by rfl) ⟨121811, by rfl⟩ : syracuseStep 162415 = 243623) B243623
theorem B392353 : Blo 127788 392353 := bstep (se 2 (by rfl) ⟨147132, by rfl⟩ : syracuseStep 392353 = 294265) B294265
theorem B1048223 : Blo 127788 1048223 := bstep (se 1 (by rfl) ⟨786167, by rfl⟩ : syracuseStep 1048223 = 1572335) B1572335
theorem B197615 : Blo 127788 197615 := bstep (se 1 (by rfl) ⟨148211, by rfl⟩ : syracuseStep 197615 = 296423) B296423
theorem B1672607 : Blo 127788 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B1806911 : Blo 127788 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B529129 : Blo 127788 529129 := bstep (se 2 (by rfl) ⟨198423, by rfl⟩ : syracuseStep 529129 = 396847) B396847
theorem B496799 : Blo 127788 496799 := bstep (se 1 (by rfl) ⟨372599, by rfl⟩ : syracuseStep 496799 = 745199) B745199
theorem B497087 : Blo 127788 497087 := bstep (se 1 (by rfl) ⟨372815, by rfl⟩ : syracuseStep 497087 = 745631) B745631
theorem B12916235 : Blo 127788 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B2235113 : Blo 127788 2235113 := bstep (se 2 (by rfl) ⟨838167, by rfl⟩ : syracuseStep 2235113 = 1676335) B1676335
theorem B698815 : Blo 127788 698815 := bstep (se 1 (by rfl) ⟨524111, by rfl⟩ : syracuseStep 698815 = 1048223) B1048223
theorem B1096577 : Blo 127788 1096577 := bstep (se 2 (by rfl) ⟨411216, by rfl⟩ : syracuseStep 1096577 = 822433) B822433
theorem B146587 : Blo 127788 146587 := bstep (se 1 (by rfl) ⟨109940, by rfl⟩ : syracuseStep 146587 = 219881) B219881
theorem B147451 : Blo 127788 147451 := bstep (se 1 (by rfl) ⟨110588, by rfl⟩ : syracuseStep 147451 = 221177) B221177
theorem B216553 : Blo 127788 216553 := bstep (se 2 (by rfl) ⟨81207, by rfl⟩ : syracuseStep 216553 = 162415) B162415
theorem B2020241 : Blo 127788 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B617327 : Blo 127788 617327 := bstep (se 1 (by rfl) ⟨462995, by rfl⟩ : syracuseStep 617327 = 925991) B925991
theorem B2092549 : Blo 127788 2092549 := bstep (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) B392353
theorem B128239 : Blo 127788 128239 := bstep (se 1 (by rfl) ⟨96179, by rfl⟩ : syracuseStep 128239 = 192359) B192359
theorem B1243187 : Blo 127788 1243187 := bstep (se 1 (by rfl) ⟨932390, by rfl⟩ : syracuseStep 1243187 = 1864781) B1864781
theorem B195455 : Blo 127788 195455 := bstep (se 1 (by rfl) ⟨146591, by rfl⟩ : syracuseStep 195455 = 293183) B293183
theorem B7765919 : Blo 127788 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B131743 : Blo 127788 131743 := bstep (se 1 (by rfl) ⟨98807, by rfl⟩ : syracuseStep 131743 = 197615) B197615
theorem B1346827 : Blo 127788 1346827 := bstep (se 1 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 1346827 = 2020241) B2020241
theorem B331199 : Blo 127788 331199 := bstep (se 1 (by rfl) ⟨248399, by rfl⟩ : syracuseStep 331199 = 496799) B496799
theorem B331391 : Blo 127788 331391 := bstep (se 1 (by rfl) ⟨248543, by rfl⟩ : syracuseStep 331391 = 497087) B497087
theorem B4460285 : Blo 127788 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B2790065 : Blo 127788 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B828791 : Blo 127788 828791 := bstep (se 1 (by rfl) ⟨621593, by rfl⟩ : syracuseStep 828791 = 1243187) B1243187
theorem B731051 : Blo 127788 731051 := bstep (se 1 (by rfl) ⟨548288, by rfl⟩ : syracuseStep 731051 = 1096577) B1096577
theorem B931753 : Blo 127788 931753 := bstep (se 2 (by rfl) ⟨349407, by rfl⟩ : syracuseStep 931753 = 698815) B698815
theorem B1490075 : Blo 127788 1490075 := bstep (se 1 (by rfl) ⟨1117556, by rfl⟩ : syracuseStep 1490075 = 2235113) B2235113
theorem B705505 : Blo 127788 705505 := bstep (se 2 (by rfl) ⟨264564, by rfl⟩ : syracuseStep 705505 = 529129) B529129
theorem B411551 : Blo 127788 411551 := bstep (se 1 (by rfl) ⟨308663, by rfl⟩ : syracuseStep 411551 = 617327) B617327
theorem B1204607 : Blo 127788 1204607 := bstep (se 1 (by rfl) ⟨903455, by rfl⟩ : syracuseStep 1204607 = 1806911) B1806911
theorem B8610823 : Blo 127788 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B288737 : Blo 127788 288737 := bstep (se 2 (by rfl) ⟨108276, by rfl⟩ : syracuseStep 288737 = 216553) B216553
theorem B195449 : Blo 127788 195449 := bstep (se 2 (by rfl) ⟨73293, by rfl⟩ : syracuseStep 195449 = 146587) B146587
theorem B130303 : Blo 127788 130303 := bstep (se 1 (by rfl) ⟨97727, by rfl⟩ : syracuseStep 130303 = 195455) B195455
theorem B5177279 : Blo 127788 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B196601 : Blo 127788 196601 := bstep (se 2 (by rfl) ⟨73725, by rfl⟩ : syracuseStep 196601 = 147451) B147451
theorem B7440173 : Blo 127788 7440173 := bstep (se 3 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 7440173 = 2790065) B2790065
theorem B993383 : Blo 127788 993383 := bstep (se 1 (by rfl) ⟨745037, by rfl⟩ : syracuseStep 993383 = 1490075) B1490075
theorem B13806077 : Blo 127788 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B274367 : Blo 127788 274367 := bstep (se 1 (by rfl) ⟨205775, by rfl⟩ : syracuseStep 274367 = 411551) B411551
theorem B11481097 : Blo 127788 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B803071 : Blo 127788 803071 := bstep (se 1 (by rfl) ⟨602303, by rfl⟩ : syracuseStep 803071 = 1204607) B1204607
theorem B940673 : Blo 127788 940673 := bstep (se 2 (by rfl) ⟨352752, by rfl⟩ : syracuseStep 940673 = 705505) B705505
theorem B220799 : Blo 127788 220799 := bstep (se 1 (by rfl) ⟨165599, by rfl⟩ : syracuseStep 220799 = 331199) B331199
theorem B220927 : Blo 127788 220927 := bstep (se 1 (by rfl) ⟨165695, by rfl⟩ : syracuseStep 220927 = 331391) B331391
theorem B2973523 : Blo 127788 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B1795769 : Blo 127788 1795769 := bstep (se 2 (by rfl) ⟨673413, by rfl⟩ : syracuseStep 1795769 = 1346827) B1346827
theorem B552527 : Blo 127788 552527 := bstep (se 1 (by rfl) ⟨414395, by rfl⟩ : syracuseStep 552527 = 828791) B828791
theorem B487367 : Blo 127788 487367 := bstep (se 1 (by rfl) ⟨365525, by rfl⟩ : syracuseStep 487367 = 731051) B731051
theorem B192491 : Blo 127788 192491 := bstep (se 1 (by rfl) ⟨144368, by rfl⟩ : syracuseStep 192491 = 288737) B288737
theorem B1242337 : Blo 127788 1242337 := bstep (se 2 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 1242337 = 931753) B931753
theorem B130299 : Blo 127788 130299 := bstep (se 1 (by rfl) ⟨97724, by rfl⟩ : syracuseStep 130299 = 195449) B195449
theorem B131067 : Blo 127788 131067 := bstep (se 1 (by rfl) ⟨98300, by rfl⟩ : syracuseStep 131067 = 196601) B196601
theorem B627115 : Blo 127788 627115 := bstep (se 1 (by rfl) ⟨470336, by rfl⟩ : syracuseStep 627115 = 940673) B940673
theorem B15308129 : Blo 127788 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B662255 : Blo 127788 662255 := bstep (se 1 (by rfl) ⟨496691, by rfl⟩ : syracuseStep 662255 = 993383) B993383
theorem B368351 : Blo 127788 368351 := bstep (se 1 (by rfl) ⟨276263, by rfl⟩ : syracuseStep 368351 = 552527) B552527
theorem B4960115 : Blo 127788 4960115 := bstep (se 1 (by rfl) ⟨3720086, by rfl⟩ : syracuseStep 4960115 = 7440173) B7440173
theorem B147199 : Blo 127788 147199 := bstep (se 1 (by rfl) ⟨110399, by rfl⟩ : syracuseStep 147199 = 220799) B220799
theorem B1197179 : Blo 127788 1197179 := bstep (se 1 (by rfl) ⟨897884, by rfl⟩ : syracuseStep 1197179 = 1795769) B1795769
theorem B36816205 : Blo 127788 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B1656449 : Blo 127788 1656449 := bstep (se 2 (by rfl) ⟨621168, by rfl⟩ : syracuseStep 1656449 = 1242337) B1242337
theorem B182911 : Blo 127788 182911 := bstep (se 1 (by rfl) ⟨137183, by rfl⟩ : syracuseStep 182911 = 274367) B274367
theorem B1070761 : Blo 127788 1070761 := bstep (se 2 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 1070761 = 803071) B803071
theorem B324911 : Blo 127788 324911 := bstep (se 1 (by rfl) ⟨243683, by rfl⟩ : syracuseStep 324911 = 487367) B487367
theorem B128327 : Blo 127788 128327 := bstep (se 1 (by rfl) ⟨96245, by rfl⟩ : syracuseStep 128327 = 192491) B192491
theorem B294569 : Blo 127788 294569 := bstep (se 2 (by rfl) ⟨110463, by rfl⟩ : syracuseStep 294569 = 220927) B220927
theorem B3964697 : Blo 127788 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B49088273 : Blo 127788 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B798119 : Blo 127788 798119 := bstep (se 1 (by rfl) ⟨598589, by rfl⟩ : syracuseStep 798119 = 1197179) B1197179
theorem B243881 : Blo 127788 243881 := bstep (se 2 (by rfl) ⟨91455, by rfl⟩ : syracuseStep 243881 = 182911) B182911
theorem B441503 : Blo 127788 441503 := bstep (se 1 (by rfl) ⟨331127, by rfl⟩ : syracuseStep 441503 = 662255) B662255
theorem B245567 : Blo 127788 245567 := bstep (se 1 (by rfl) ⟨184175, by rfl⟩ : syracuseStep 245567 = 368351) B368351
theorem B836153 : Blo 127788 836153 := bstep (se 2 (by rfl) ⟨313557, by rfl⟩ : syracuseStep 836153 = 627115) B627115
theorem B1427681 : Blo 127788 1427681 := bstep (se 2 (by rfl) ⟨535380, by rfl⟩ : syracuseStep 1427681 = 1070761) B1070761
theorem B216607 : Blo 127788 216607 := bstep (se 1 (by rfl) ⟨162455, by rfl⟩ : syracuseStep 216607 = 324911) B324911
theorem B2643131 : Blo 127788 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B1104299 : Blo 127788 1104299 := bstep (se 1 (by rfl) ⟨828224, by rfl⟩ : syracuseStep 1104299 = 1656449) B1656449
theorem B40821677 : Blo 127788 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B3306743 : Blo 127788 3306743 := bstep (se 1 (by rfl) ⟨2480057, by rfl⟩ : syracuseStep 3306743 = 4960115) B4960115
theorem B196265 : Blo 127788 196265 := bstep (se 2 (by rfl) ⟨73599, by rfl⟩ : syracuseStep 196265 = 147199) B147199
theorem B196379 : Blo 127788 196379 := bstep (se 1 (by rfl) ⟨147284, by rfl⟩ : syracuseStep 196379 = 294569) B294569
theorem B557435 : Blo 127788 557435 := bstep (se 1 (by rfl) ⟨418076, by rfl⟩ : syracuseStep 557435 = 836153) B836153
theorem B951787 : Blo 127788 951787 := bstep (se 1 (by rfl) ⟨713840, by rfl⟩ : syracuseStep 951787 = 1427681) B1427681
theorem B532079 : Blo 127788 532079 := bstep (se 1 (by rfl) ⟨399059, by rfl⟩ : syracuseStep 532079 = 798119) B798119
theorem B523608245 : Blo 127788 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B2204495 : Blo 127788 2204495 := bstep (se 1 (by rfl) ⟨1653371, by rfl⟩ : syracuseStep 2204495 = 3306743) B3306743
theorem B736199 : Blo 127788 736199 := bstep (se 1 (by rfl) ⟨552149, by rfl⟩ : syracuseStep 736199 = 1104299) B1104299
theorem B27214451 : Blo 127788 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B1762087 : Blo 127788 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B288809 : Blo 127788 288809 := bstep (se 2 (by rfl) ⟨108303, by rfl⟩ : syracuseStep 288809 = 216607) B216607
theorem B162587 : Blo 127788 162587 := bstep (se 1 (by rfl) ⟨121940, by rfl⟩ : syracuseStep 162587 = 243881) B243881
theorem B294335 : Blo 127788 294335 := bstep (se 1 (by rfl) ⟨220751, by rfl⟩ : syracuseStep 294335 = 441503) B441503
theorem B130843 : Blo 127788 130843 := bstep (se 1 (by rfl) ⟨98132, by rfl⟩ : syracuseStep 130843 = 196265) B196265
theorem B130919 : Blo 127788 130919 := bstep (se 1 (by rfl) ⟨98189, by rfl⟩ : syracuseStep 130919 = 196379) B196379
theorem B163711 : Blo 127788 163711 := bstep (se 1 (by rfl) ⟨122783, by rfl⟩ : syracuseStep 163711 = 245567) B245567
theorem B433565 : Blo 127788 433565 := bstep (se 3 (by rfl) ⟨81293, by rfl⟩ : syracuseStep 433565 = 162587) B162587
theorem B371623 : Blo 127788 371623 := bstep (se 1 (by rfl) ⟨278717, by rfl⟩ : syracuseStep 371623 = 557435) B557435
theorem B218281 : Blo 127788 218281 := bstep (se 2 (by rfl) ⟨81855, by rfl⟩ : syracuseStep 218281 = 163711) B163711
theorem B18142967 : Blo 127788 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B2349449 : Blo 127788 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B1269049 : Blo 127788 1269049 := bstep (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) B951787
theorem B354719 : Blo 127788 354719 := bstep (se 1 (by rfl) ⟨266039, by rfl⟩ : syracuseStep 354719 = 532079) B532079
theorem B349072163 : Blo 127788 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B1469663 : Blo 127788 1469663 := bstep (se 1 (by rfl) ⟨1102247, by rfl⟩ : syracuseStep 1469663 = 2204495) B2204495
theorem B192539 : Blo 127788 192539 := bstep (se 1 (by rfl) ⟨144404, by rfl⟩ : syracuseStep 192539 = 288809) B288809
theorem B490799 : Blo 127788 490799 := bstep (se 1 (by rfl) ⟨368099, by rfl⟩ : syracuseStep 490799 = 736199) B736199
theorem B196223 : Blo 127788 196223 := bstep (se 1 (by rfl) ⟨147167, by rfl⟩ : syracuseStep 196223 = 294335) B294335
theorem B495497 : Blo 127788 495497 := bstep (se 2 (by rfl) ⟨185811, by rfl⟩ : syracuseStep 495497 = 371623) B371623
theorem B236479 : Blo 127788 236479 := bstep (se 1 (by rfl) ⟨177359, by rfl⟩ : syracuseStep 236479 = 354719) B354719
theorem B48381245 : Blo 127788 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B1692065 : Blo 127788 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B1566299 : Blo 127788 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B289043 : Blo 127788 289043 := bstep (se 1 (by rfl) ⟨216782, by rfl⟩ : syracuseStep 289043 = 433565) B433565
theorem B291041 : Blo 127788 291041 := bstep (se 2 (by rfl) ⟨109140, by rfl⟩ : syracuseStep 291041 = 218281) B218281
theorem B232714775 : Blo 127788 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B979775 : Blo 127788 979775 := bstep (se 1 (by rfl) ⟨734831, by rfl⟩ : syracuseStep 979775 = 1469663) B1469663
theorem B128359 : Blo 127788 128359 := bstep (se 1 (by rfl) ⟨96269, by rfl⟩ : syracuseStep 128359 = 192539) B192539
theorem B327199 : Blo 127788 327199 := bstep (se 1 (by rfl) ⟨245399, by rfl⟩ : syracuseStep 327199 = 490799) B490799
theorem B130815 : Blo 127788 130815 := bstep (se 1 (by rfl) ⟨98111, by rfl⟩ : syracuseStep 130815 = 196223) B196223
theorem B436265 : Blo 127788 436265 := bstep (se 2 (by rfl) ⟨163599, by rfl⟩ : syracuseStep 436265 = 327199) B327199
theorem B32254163 : Blo 127788 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B1321325 : Blo 127788 1321325 := bstep (se 3 (by rfl) ⟨247748, by rfl⟩ : syracuseStep 1321325 = 495497) B495497
theorem B1128043 : Blo 127788 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B155143183 : Blo 127788 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B315305 : Blo 127788 315305 := bstep (se 2 (by rfl) ⟨118239, by rfl⟩ : syracuseStep 315305 = 236479) B236479
theorem B1044199 : Blo 127788 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B192695 : Blo 127788 192695 := bstep (se 1 (by rfl) ⟨144521, by rfl⟩ : syracuseStep 192695 = 289043) B289043
theorem B194027 : Blo 127788 194027 := bstep (se 1 (by rfl) ⟨145520, by rfl⟩ : syracuseStep 194027 = 291041) B291041
theorem B653183 : Blo 127788 653183 := bstep (se 1 (by rfl) ⟨489887, by rfl⟩ : syracuseStep 653183 = 979775) B979775
theorem B21502775 : Blo 127788 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B435455 : Blo 127788 435455 := bstep (se 1 (by rfl) ⟨326591, by rfl⟩ : syracuseStep 435455 = 653183) B653183
theorem B210203 : Blo 127788 210203 := bstep (se 1 (by rfl) ⟨157652, by rfl⟩ : syracuseStep 210203 = 315305) B315305
theorem B1392265 : Blo 127788 1392265 := bstep (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) B1044199
theorem B206857577 : Blo 127788 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B290843 : Blo 127788 290843 := bstep (se 1 (by rfl) ⟨218132, by rfl⟩ : syracuseStep 290843 = 436265) B436265
theorem B880883 : Blo 127788 880883 := bstep (se 1 (by rfl) ⟨660662, by rfl⟩ : syracuseStep 880883 = 1321325) B1321325
theorem B1504057 : Blo 127788 1504057 := bstep (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) B1128043
theorem B128463 : Blo 127788 128463 := bstep (se 1 (by rfl) ⟨96347, by rfl⟩ : syracuseStep 128463 = 192695) B192695
theorem B129351 : Blo 127788 129351 := bstep (se 1 (by rfl) ⟨97013, by rfl⟩ : syracuseStep 129351 = 194027) B194027
theorem B2005409 : Blo 127788 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B140135 : Blo 127788 140135 := bstep (se 1 (by rfl) ⟨105101, by rfl⟩ : syracuseStep 140135 = 210203) B210203
theorem B14335183 : Blo 127788 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B137905051 : Blo 127788 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B1856353 : Blo 127788 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B290303 : Blo 127788 290303 := bstep (se 1 (by rfl) ⟨217727, by rfl⟩ : syracuseStep 290303 = 435455) B435455
theorem B193895 : Blo 127788 193895 := bstep (se 1 (by rfl) ⟨145421, by rfl⟩ : syracuseStep 193895 = 290843) B290843
theorem B587255 : Blo 127788 587255 := bstep (se 1 (by rfl) ⟨440441, by rfl⟩ : syracuseStep 587255 = 880883) B880883
theorem B5347757 : Blo 127788 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B19113577 : Blo 127788 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B183873401 : Blo 127788 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B373693 : Blo 127788 373693 := bstep (se 3 (by rfl) ⟨70067, by rfl⟩ : syracuseStep 373693 = 140135) B140135
theorem B2475137 : Blo 127788 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B1566013 : Blo 127788 1566013 := bstep (se 3 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 1566013 = 587255) B587255
theorem B193535 : Blo 127788 193535 := bstep (se 1 (by rfl) ⟨145151, by rfl⟩ : syracuseStep 193535 = 290303) B290303
theorem B129263 : Blo 127788 129263 := bstep (se 1 (by rfl) ⟨96947, by rfl⟩ : syracuseStep 129263 = 193895) B193895
theorem B498257 : Blo 127788 498257 := bstep (se 2 (by rfl) ⟨186846, by rfl⟩ : syracuseStep 498257 = 373693) B373693
theorem B1650091 : Blo 127788 1650091 := bstep (se 1 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 1650091 = 2475137) B2475137
theorem B2088017 : Blo 127788 2088017 := bstep (se 2 (by rfl) ⟨783006, by rfl⟩ : syracuseStep 2088017 = 1566013) B1566013
theorem B3565171 : Blo 127788 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B122582267 : Blo 127788 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B101939077 : Blo 127788 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B129023 : Blo 127788 129023 := bstep (se 1 (by rfl) ⟨96767, by rfl⟩ : syracuseStep 129023 = 193535) B193535
theorem B4753561 : Blo 127788 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B332171 : Blo 127788 332171 := bstep (se 1 (by rfl) ⟨249128, by rfl⟩ : syracuseStep 332171 = 498257) B498257
theorem B2200121 : Blo 127788 2200121 := bstep (se 2 (by rfl) ⟨825045, by rfl⟩ : syracuseStep 2200121 = 1650091) B1650091
theorem B1392011 : Blo 127788 1392011 := bstep (se 1 (by rfl) ⟨1044008, by rfl⟩ : syracuseStep 1392011 = 2088017) B2088017
theorem B135918769 : Blo 127788 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B81721511 : Blo 127788 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B928007 : Blo 127788 928007 := bstep (se 1 (by rfl) ⟨696005, by rfl⟩ : syracuseStep 928007 = 1392011) B1392011
theorem B6338081 : Blo 127788 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B181225025 : Blo 127788 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B54481007 : Blo 127788 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B221447 : Blo 127788 221447 := bstep (se 1 (by rfl) ⟨166085, by rfl⟩ : syracuseStep 221447 = 332171) B332171
theorem B1466747 : Blo 127788 1466747 := bstep (se 1 (by rfl) ⟨1100060, by rfl⟩ : syracuseStep 1466747 = 2200121) B2200121
theorem B120816683 : Blo 127788 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B36320671 : Blo 127788 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B147631 : Blo 127788 147631 := bstep (se 1 (by rfl) ⟨110723, by rfl⟩ : syracuseStep 147631 = 221447) B221447
theorem B977831 : Blo 127788 977831 := bstep (se 1 (by rfl) ⟨733373, by rfl⟩ : syracuseStep 977831 = 1466747) B1466747
theorem B618671 : Blo 127788 618671 := bstep (se 1 (by rfl) ⟨464003, by rfl⟩ : syracuseStep 618671 = 928007) B928007
theorem B4225387 : Blo 127788 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B196841 : Blo 127788 196841 := bstep (se 2 (by rfl) ⟨73815, by rfl⟩ : syracuseStep 196841 = 147631) B147631
theorem B80544455 : Blo 127788 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B412447 : Blo 127788 412447 := bstep (se 1 (by rfl) ⟨309335, by rfl⟩ : syracuseStep 412447 = 618671) B618671
theorem B48427561 : Blo 127788 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B651887 : Blo 127788 651887 := bstep (se 1 (by rfl) ⟨488915, by rfl⟩ : syracuseStep 651887 = 977831) B977831
theorem B5633849 : Blo 127788 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B131227 : Blo 127788 131227 := bstep (se 1 (by rfl) ⟨98420, by rfl⟩ : syracuseStep 131227 = 196841) B196841
theorem B434591 : Blo 127788 434591 := bstep (se 1 (by rfl) ⟨325943, by rfl⟩ : syracuseStep 434591 = 651887) B651887
theorem B64570081 : Blo 127788 64570081 := bstep (se 2 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 64570081 = 48427561) B48427561
theorem B3755899 : Blo 127788 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B53696303 : Blo 127788 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B549929 : Blo 127788 549929 := bstep (se 2 (by rfl) ⟨206223, by rfl⟩ : syracuseStep 549929 = 412447) B412447
theorem B366619 : Blo 127788 366619 := bstep (se 1 (by rfl) ⟨274964, by rfl⟩ : syracuseStep 366619 = 549929) B549929
theorem B86093441 : Blo 127788 86093441 := bstep (se 2 (by rfl) ⟨32285040, by rfl⟩ : syracuseStep 86093441 = 64570081) B64570081
theorem B35797535 : Blo 127788 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B5007865 : Blo 127788 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B289727 : Blo 127788 289727 := bstep (se 1 (by rfl) ⟨217295, by rfl⟩ : syracuseStep 289727 = 434591) B434591
theorem B23865023 : Blo 127788 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B57395627 : Blo 127788 57395627 := bstep (se 1 (by rfl) ⟨43046720, by rfl⟩ : syracuseStep 57395627 = 86093441) B86093441
theorem B6677153 : Blo 127788 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B193151 : Blo 127788 193151 := bstep (se 1 (by rfl) ⟨144863, by rfl⟩ : syracuseStep 193151 = 289727) B289727
theorem B488825 : Blo 127788 488825 := bstep (se 2 (by rfl) ⟨183309, by rfl⟩ : syracuseStep 488825 = 366619) B366619
theorem B15910015 : Blo 127788 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B38263751 : Blo 127788 38263751 := bstep (se 1 (by rfl) ⟨28697813, by rfl⟩ : syracuseStep 38263751 = 57395627) B57395627
theorem B4451435 : Blo 127788 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B128767 : Blo 127788 128767 := bstep (se 1 (by rfl) ⟨96575, by rfl⟩ : syracuseStep 128767 = 193151) B193151
theorem B325883 : Blo 127788 325883 := bstep (se 1 (by rfl) ⟨244412, by rfl⟩ : syracuseStep 325883 = 488825) B488825
theorem B21213353 : Blo 127788 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B25509167 : Blo 127788 25509167 := bstep (se 1 (by rfl) ⟨19131875, by rfl⟩ : syracuseStep 25509167 = 38263751) B38263751
theorem B2967623 : Blo 127788 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B217255 : Blo 127788 217255 := bstep (se 1 (by rfl) ⟨162941, by rfl⟩ : syracuseStep 217255 = 325883) B325883
theorem B1978415 : Blo 127788 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B14142235 : Blo 127788 14142235 := bstep (se 1 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 14142235 = 21213353) B21213353
theorem B289673 : Blo 127788 289673 := bstep (se 2 (by rfl) ⟨108627, by rfl⟩ : syracuseStep 289673 = 217255) B217255
theorem B17006111 : Blo 127788 17006111 := bstep (se 1 (by rfl) ⟨12754583, by rfl⟩ : syracuseStep 17006111 = 25509167) B25509167
theorem B1318943 : Blo 127788 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B18856313 : Blo 127788 18856313 := bstep (se 2 (by rfl) ⟨7071117, by rfl⟩ : syracuseStep 18856313 = 14142235) B14142235
theorem B193115 : Blo 127788 193115 := bstep (se 1 (by rfl) ⟨144836, by rfl⟩ : syracuseStep 193115 = 289673) B289673
theorem B11337407 : Blo 127788 11337407 := bstep (se 1 (by rfl) ⟨8503055, by rfl⟩ : syracuseStep 11337407 = 17006111) B17006111
theorem B12570875 : Blo 127788 12570875 := bstep (se 1 (by rfl) ⟨9428156, by rfl⟩ : syracuseStep 12570875 = 18856313) B18856313
theorem B7558271 : Blo 127788 7558271 := bstep (se 1 (by rfl) ⟨5668703, by rfl⟩ : syracuseStep 7558271 = 11337407) B11337407
theorem B879295 : Blo 127788 879295 := bstep (se 1 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 879295 = 1318943) B1318943
theorem B128743 : Blo 127788 128743 := bstep (se 1 (by rfl) ⟨96557, by rfl⟩ : syracuseStep 128743 = 193115) B193115
theorem B8380583 : Blo 127788 8380583 := bstep (se 1 (by rfl) ⟨6285437, by rfl⟩ : syracuseStep 8380583 = 12570875) B12570875
theorem B5038847 : Blo 127788 5038847 := bstep (se 1 (by rfl) ⟨3779135, by rfl⟩ : syracuseStep 5038847 = 7558271) B7558271
theorem B1172393 : Blo 127788 1172393 := bstep (se 2 (by rfl) ⟨439647, by rfl⟩ : syracuseStep 1172393 = 879295) B879295
theorem B5587055 : Blo 127788 5587055 := bstep (se 1 (by rfl) ⟨4190291, by rfl⟩ : syracuseStep 5587055 = 8380583) B8380583
theorem B3359231 : Blo 127788 3359231 := bstep (se 1 (by rfl) ⟨2519423, by rfl⟩ : syracuseStep 3359231 = 5038847) B5038847
theorem B781595 : Blo 127788 781595 := bstep (se 1 (by rfl) ⟨586196, by rfl⟩ : syracuseStep 781595 = 1172393) B1172393
theorem B2239487 : Blo 127788 2239487 := bstep (se 1 (by rfl) ⟨1679615, by rfl⟩ : syracuseStep 2239487 = 3359231) B3359231
theorem B3724703 : Blo 127788 3724703 := bstep (se 1 (by rfl) ⟨2793527, by rfl⟩ : syracuseStep 3724703 = 5587055) B5587055
theorem B521063 : Blo 127788 521063 := bstep (se 1 (by rfl) ⟨390797, by rfl⟩ : syracuseStep 521063 = 781595) B781595
theorem B1492991 : Blo 127788 1492991 := bstep (se 1 (by rfl) ⟨1119743, by rfl⟩ : syracuseStep 1492991 = 2239487) B2239487
theorem B347375 : Blo 127788 347375 := bstep (se 1 (by rfl) ⟨260531, by rfl⟩ : syracuseStep 347375 = 521063) B521063
theorem B2483135 : Blo 127788 2483135 := bstep (se 1 (by rfl) ⟨1862351, by rfl⟩ : syracuseStep 2483135 = 3724703) B3724703
theorem B231583 : Blo 127788 231583 := bstep (se 1 (by rfl) ⟨173687, by rfl⟩ : syracuseStep 231583 = 347375) B347375
theorem B995327 : Blo 127788 995327 := bstep (se 1 (by rfl) ⟨746495, by rfl⟩ : syracuseStep 995327 = 1492991) B1492991
theorem B1655423 : Blo 127788 1655423 := bstep (se 1 (by rfl) ⟨1241567, by rfl⟩ : syracuseStep 1655423 = 2483135) B2483135
theorem B663551 : Blo 127788 663551 := bstep (se 1 (by rfl) ⟨497663, by rfl⟩ : syracuseStep 663551 = 995327) B995327
theorem B308777 : Blo 127788 308777 := bstep (se 2 (by rfl) ⟨115791, by rfl⟩ : syracuseStep 308777 = 231583) B231583
theorem B1103615 : Blo 127788 1103615 := bstep (se 1 (by rfl) ⟨827711, by rfl⟩ : syracuseStep 1103615 = 1655423) B1655423
theorem B735743 : Blo 127788 735743 := bstep (se 1 (by rfl) ⟨551807, by rfl⟩ : syracuseStep 735743 = 1103615) B1103615
theorem B442367 : Blo 127788 442367 := bstep (se 1 (by rfl) ⟨331775, by rfl⟩ : syracuseStep 442367 = 663551) B663551
theorem B3293621 : Blo 127788 3293621 := bstep (se 5 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 3293621 = 308777) B308777
theorem B2195747 : Blo 127788 2195747 := bstep (se 1 (by rfl) ⟨1646810, by rfl⟩ : syracuseStep 2195747 = 3293621) B3293621
theorem B294911 : Blo 127788 294911 := bstep (se 1 (by rfl) ⟨221183, by rfl⟩ : syracuseStep 294911 = 442367) B442367
theorem B490495 : Blo 127788 490495 := bstep (se 1 (by rfl) ⟨367871, by rfl⟩ : syracuseStep 490495 = 735743) B735743
theorem B196607 : Blo 127788 196607 := bstep (se 1 (by rfl) ⟨147455, by rfl⟩ : syracuseStep 196607 = 294911) B294911
theorem B1463831 : Blo 127788 1463831 := bstep (se 1 (by rfl) ⟨1097873, by rfl⟩ : syracuseStep 1463831 = 2195747) B2195747
theorem B653993 : Blo 127788 653993 := bstep (se 2 (by rfl) ⟨245247, by rfl⟩ : syracuseStep 653993 = 490495) B490495
theorem B435995 : Blo 127788 435995 := bstep (se 1 (by rfl) ⟨326996, by rfl⟩ : syracuseStep 435995 = 653993) B653993
theorem B975887 : Blo 127788 975887 := bstep (se 1 (by rfl) ⟨731915, by rfl⟩ : syracuseStep 975887 = 1463831) B1463831
theorem B131071 : Blo 127788 131071 := bstep (se 1 (by rfl) ⟨98303, by rfl⟩ : syracuseStep 131071 = 196607) B196607
theorem B650591 : Blo 127788 650591 := bstep (se 1 (by rfl) ⟨487943, by rfl⟩ : syracuseStep 650591 = 975887) B975887
theorem B290663 : Blo 127788 290663 := bstep (se 1 (by rfl) ⟨217997, by rfl⟩ : syracuseStep 290663 = 435995) B435995
theorem B433727 : Blo 127788 433727 := bstep (se 1 (by rfl) ⟨325295, by rfl⟩ : syracuseStep 433727 = 650591) B650591
theorem B193775 : Blo 127788 193775 := bstep (se 1 (by rfl) ⟨145331, by rfl⟩ : syracuseStep 193775 = 290663) B290663
theorem B289151 : Blo 127788 289151 := bstep (se 1 (by rfl) ⟨216863, by rfl⟩ : syracuseStep 289151 = 433727) B433727
theorem B129183 : Blo 127788 129183 := bstep (se 1 (by rfl) ⟨96887, by rfl⟩ : syracuseStep 129183 = 193775) B193775
theorem B192767 : Blo 127788 192767 := bstep (se 1 (by rfl) ⟨144575, by rfl⟩ : syracuseStep 192767 = 289151) B289151
theorem B128511 : Blo 127788 128511 := bstep (se 1 (by rfl) ⟨96383, by rfl⟩ : syracuseStep 128511 = 192767) B192767

theorem C0 (j : ℕ) (h1 : 31947 ≤ j) (h2 : j ≤ 32646) : Blo 127788 (4 * j + 3) := by
  interval_cases j
  · exact B127791
  · exact B127795
  · exact B127799
  · exact B127803
  · exact B127807
  · exact B127811
  · exact B127815
  · exact B127819
  · exact B127823
  · exact B127827
  · exact B127831
  · exact B127835
  · exact B127839
  · exact B127843
  · exact B127847
  · exact B127851
  · exact B127855
  · exact B127859
  · exact B127863
  · exact B127867
  · exact B127871
  · exact B127875
  · exact B127879
  · exact B127883
  · exact B127887
  · exact B127891
  · exact B127895
  · exact B127899
  · exact B127903
  · exact B127907
  · exact B127911
  · exact B127915
  · exact B127919
  · exact B127923
  · exact B127927
  · exact B127931
  · exact B127935
  · exact B127939
  · exact B127943
  · exact B127947
  · exact B127951
  · exact B127955
  · exact B127959
  · exact B127963
  · exact B127967
  · exact B127971
  · exact B127975
  · exact B127979
  · exact B127983
  · exact B127987
  · exact B127991
  · exact B127995
  · exact B127999
  · exact B128003
  · exact B128007
  · exact B128011
  · exact B128015
  · exact B128019
  · exact B128023
  · exact B128027
  · exact B128031
  · exact B128035
  · exact B128039
  · exact B128043
  · exact B128047
  · exact B128051
  · exact B128055
  · exact B128059
  · exact B128063
  · exact B128067
  · exact B128071
  · exact B128075
  · exact B128079
  · exact B128083
  · exact B128087
  · exact B128091
  · exact B128095
  · exact B128099
  · exact B128103
  · exact B128107
  · exact B128111
  · exact B128115
  · exact B128119
  · exact B128123
  · exact B128127
  · exact B128131
  · exact B128135
  · exact B128139
  · exact B128143
  · exact B128147
  · exact B128151
  · exact B128155
  · exact B128159
  · exact B128163
  · exact B128167
  · exact B128171
  · exact B128175
  · exact B128179
  · exact B128183
  · exact B128187
  · exact B128191
  · exact B128195
  · exact B128199
  · exact B128203
  · exact B128207
  · exact B128211
  · exact B128215
  · exact B128219
  · exact B128223
  · exact B128227
  · exact B128231
  · exact B128235
  · exact B128239
  · exact B128243
  · exact B128247
  · exact B128251
  · exact B128255
  · exact B128259
  · exact B128263
  · exact B128267
  · exact B128271
  · exact B128275
  · exact B128279
  · exact B128283
  · exact B128287
  · exact B128291
  · exact B128295
  · exact B128299
  · exact B128303
  · exact B128307
  · exact B128311
  · exact B128315
  · exact B128319
  · exact B128323
  · exact B128327
  · exact B128331
  · exact B128335
  · exact B128339
  · exact B128343
  · exact B128347
  · exact B128351
  · exact B128355
  · exact B128359
  · exact B128363
  · exact B128367
  · exact B128371
  · exact B128375
  · exact B128379
  · exact B128383
  · exact B128387
  · exact B128391
  · exact B128395
  · exact B128399
  · exact B128403
  · exact B128407
  · exact B128411
  · exact B128415
  · exact B128419
  · exact B128423
  · exact B128427
  · exact B128431
  · exact B128435
  · exact B128439
  · exact B128443
  · exact B128447
  · exact B128451
  · exact B128455
  · exact B128459
  · exact B128463
  · exact B128467
  · exact B128471
  · exact B128475
  · exact B128479
  · exact B128483
  · exact B128487
  · exact B128491
  · exact B128495
  · exact B128499
  · exact B128503
  · exact B128507
  · exact B128511
  · exact B128515
  · exact B128519
  · exact B128523
  · exact B128527
  · exact B128531
  · exact B128535
  · exact B128539
  · exact B128543
  · exact B128547
  · exact B128551
  · exact B128555
  · exact B128559
  · exact B128563
  · exact B128567
  · exact B128571
  · exact B128575
  · exact B128579
  · exact B128583
  · exact B128587
  · exact B128591
  · exact B128595
  · exact B128599
  · exact B128603
  · exact B128607
  · exact B128611
  · exact B128615
  · exact B128619
  · exact B128623
  · exact B128627
  · exact B128631
  · exact B128635
  · exact B128639
  · exact B128643
  · exact B128647
  · exact B128651
  · exact B128655
  · exact B128659
  · exact B128663
  · exact B128667
  · exact B128671
  · exact B128675
  · exact B128679
  · exact B128683
  · exact B128687
  · exact B128691
  · exact B128695
  · exact B128699
  · exact B128703
  · exact B128707
  · exact B128711
  · exact B128715
  · exact B128719
  · exact B128723
  · exact B128727
  · exact B128731
  · exact B128735
  · exact B128739
  · exact B128743
  · exact B128747
  · exact B128751
  · exact B128755
  · exact B128759
  · exact B128763
  · exact B128767
  · exact B128771
  · exact B128775
  · exact B128779
  · exact B128783
  · exact B128787
  · exact B128791
  · exact B128795
  · exact B128799
  · exact B128803
  · exact B128807
  · exact B128811
  · exact B128815
  · exact B128819
  · exact B128823
  · exact B128827
  · exact B128831
  · exact B128835
  · exact B128839
  · exact B128843
  · exact B128847
  · exact B128851
  · exact B128855
  · exact B128859
  · exact B128863
  · exact B128867
  · exact B128871
  · exact B128875
  · exact B128879
  · exact B128883
  · exact B128887
  · exact B128891
  · exact B128895
  · exact B128899
  · exact B128903
  · exact B128907
  · exact B128911
  · exact B128915
  · exact B128919
  · exact B128923
  · exact B128927
  · exact B128931
  · exact B128935
  · exact B128939
  · exact B128943
  · exact B128947
  · exact B128951
  · exact B128955
  · exact B128959
  · exact B128963
  · exact B128967
  · exact B128971
  · exact B128975
  · exact B128979
  · exact B128983
  · exact B128987
  · exact B128991
  · exact B128995
  · exact B128999
  · exact B129003
  · exact B129007
  · exact B129011
  · exact B129015
  · exact B129019
  · exact B129023
  · exact B129027
  · exact B129031
  · exact B129035
  · exact B129039
  · exact B129043
  · exact B129047
  · exact B129051
  · exact B129055
  · exact B129059
  · exact B129063
  · exact B129067
  · exact B129071
  · exact B129075
  · exact B129079
  · exact B129083
  · exact B129087
  · exact B129091
  · exact B129095
  · exact B129099
  · exact B129103
  · exact B129107
  · exact B129111
  · exact B129115
  · exact B129119
  · exact B129123
  · exact B129127
  · exact B129131
  · exact B129135
  · exact B129139
  · exact B129143
  · exact B129147
  · exact B129151
  · exact B129155
  · exact B129159
  · exact B129163
  · exact B129167
  · exact B129171
  · exact B129175
  · exact B129179
  · exact B129183
  · exact B129187
  · exact B129191
  · exact B129195
  · exact B129199
  · exact B129203
  · exact B129207
  · exact B129211
  · exact B129215
  · exact B129219
  · exact B129223
  · exact B129227
  · exact B129231
  · exact B129235
  · exact B129239
  · exact B129243
  · exact B129247
  · exact B129251
  · exact B129255
  · exact B129259
  · exact B129263
  · exact B129267
  · exact B129271
  · exact B129275
  · exact B129279
  · exact B129283
  · exact B129287
  · exact B129291
  · exact B129295
  · exact B129299
  · exact B129303
  · exact B129307
  · exact B129311
  · exact B129315
  · exact B129319
  · exact B129323
  · exact B129327
  · exact B129331
  · exact B129335
  · exact B129339
  · exact B129343
  · exact B129347
  · exact B129351
  · exact B129355
  · exact B129359
  · exact B129363
  · exact B129367
  · exact B129371
  · exact B129375
  · exact B129379
  · exact B129383
  · exact B129387
  · exact B129391
  · exact B129395
  · exact B129399
  · exact B129403
  · exact B129407
  · exact B129411
  · exact B129415
  · exact B129419
  · exact B129423
  · exact B129427
  · exact B129431
  · exact B129435
  · exact B129439
  · exact B129443
  · exact B129447
  · exact B129451
  · exact B129455
  · exact B129459
  · exact B129463
  · exact B129467
  · exact B129471
  · exact B129475
  · exact B129479
  · exact B129483
  · exact B129487
  · exact B129491
  · exact B129495
  · exact B129499
  · exact B129503
  · exact B129507
  · exact B129511
  · exact B129515
  · exact B129519
  · exact B129523
  · exact B129527
  · exact B129531
  · exact B129535
  · exact B129539
  · exact B129543
  · exact B129547
  · exact B129551
  · exact B129555
  · exact B129559
  · exact B129563
  · exact B129567
  · exact B129571
  · exact B129575
  · exact B129579
  · exact B129583
  · exact B129587
  · exact B129591
  · exact B129595
  · exact B129599
  · exact B129603
  · exact B129607
  · exact B129611
  · exact B129615
  · exact B129619
  · exact B129623
  · exact B129627
  · exact B129631
  · exact B129635
  · exact B129639
  · exact B129643
  · exact B129647
  · exact B129651
  · exact B129655
  · exact B129659
  · exact B129663
  · exact B129667
  · exact B129671
  · exact B129675
  · exact B129679
  · exact B129683
  · exact B129687
  · exact B129691
  · exact B129695
  · exact B129699
  · exact B129703
  · exact B129707
  · exact B129711
  · exact B129715
  · exact B129719
  · exact B129723
  · exact B129727
  · exact B129731
  · exact B129735
  · exact B129739
  · exact B129743
  · exact B129747
  · exact B129751
  · exact B129755
  · exact B129759
  · exact B129763
  · exact B129767
  · exact B129771
  · exact B129775
  · exact B129779
  · exact B129783
  · exact B129787
  · exact B129791
  · exact B129795
  · exact B129799
  · exact B129803
  · exact B129807
  · exact B129811
  · exact B129815
  · exact B129819
  · exact B129823
  · exact B129827
  · exact B129831
  · exact B129835
  · exact B129839
  · exact B129843
  · exact B129847
  · exact B129851
  · exact B129855
  · exact B129859
  · exact B129863
  · exact B129867
  · exact B129871
  · exact B129875
  · exact B129879
  · exact B129883
  · exact B129887
  · exact B129891
  · exact B129895
  · exact B129899
  · exact B129903
  · exact B129907
  · exact B129911
  · exact B129915
  · exact B129919
  · exact B129923
  · exact B129927
  · exact B129931
  · exact B129935
  · exact B129939
  · exact B129943
  · exact B129947
  · exact B129951
  · exact B129955
  · exact B129959
  · exact B129963
  · exact B129967
  · exact B129971
  · exact B129975
  · exact B129979
  · exact B129983
  · exact B129987
  · exact B129991
  · exact B129995
  · exact B129999
  · exact B130003
  · exact B130007
  · exact B130011
  · exact B130015
  · exact B130019
  · exact B130023
  · exact B130027
  · exact B130031
  · exact B130035
  · exact B130039
  · exact B130043
  · exact B130047
  · exact B130051
  · exact B130055
  · exact B130059
  · exact B130063
  · exact B130067
  · exact B130071
  · exact B130075
  · exact B130079
  · exact B130083
  · exact B130087
  · exact B130091
  · exact B130095
  · exact B130099
  · exact B130103
  · exact B130107
  · exact B130111
  · exact B130115
  · exact B130119
  · exact B130123
  · exact B130127
  · exact B130131
  · exact B130135
  · exact B130139
  · exact B130143
  · exact B130147
  · exact B130151
  · exact B130155
  · exact B130159
  · exact B130163
  · exact B130167
  · exact B130171
  · exact B130175
  · exact B130179
  · exact B130183
  · exact B130187
  · exact B130191
  · exact B130195
  · exact B130199
  · exact B130203
  · exact B130207
  · exact B130211
  · exact B130215
  · exact B130219
  · exact B130223
  · exact B130227
  · exact B130231
  · exact B130235
  · exact B130239
  · exact B130243
  · exact B130247
  · exact B130251
  · exact B130255
  · exact B130259
  · exact B130263
  · exact B130267
  · exact B130271
  · exact B130275
  · exact B130279
  · exact B130283
  · exact B130287
  · exact B130291
  · exact B130295
  · exact B130299
  · exact B130303
  · exact B130307
  · exact B130311
  · exact B130315
  · exact B130319
  · exact B130323
  · exact B130327
  · exact B130331
  · exact B130335
  · exact B130339
  · exact B130343
  · exact B130347
  · exact B130351
  · exact B130355
  · exact B130359
  · exact B130363
  · exact B130367
  · exact B130371
  · exact B130375
  · exact B130379
  · exact B130383
  · exact B130387
  · exact B130391
  · exact B130395
  · exact B130399
  · exact B130403
  · exact B130407
  · exact B130411
  · exact B130415
  · exact B130419
  · exact B130423
  · exact B130427
  · exact B130431
  · exact B130435
  · exact B130439
  · exact B130443
  · exact B130447
  · exact B130451
  · exact B130455
  · exact B130459
  · exact B130463
  · exact B130467
  · exact B130471
  · exact B130475
  · exact B130479
  · exact B130483
  · exact B130487
  · exact B130491
  · exact B130495
  · exact B130499
  · exact B130503
  · exact B130507
  · exact B130511
  · exact B130515
  · exact B130519
  · exact B130523
  · exact B130527
  · exact B130531
  · exact B130535
  · exact B130539
  · exact B130543
  · exact B130547
  · exact B130551
  · exact B130555
  · exact B130559
  · exact B130563
  · exact B130567
  · exact B130571
  · exact B130575
  · exact B130579
  · exact B130583
  · exact B130587

theorem C1 (j : ℕ) (h1 : 32647 ≤ j) (h2 : j ≤ 32946) : Blo 127788 (4 * j + 3) := by
  interval_cases j
  · exact B130591
  · exact B130595
  · exact B130599
  · exact B130603
  · exact B130607
  · exact B130611
  · exact B130615
  · exact B130619
  · exact B130623
  · exact B130627
  · exact B130631
  · exact B130635
  · exact B130639
  · exact B130643
  · exact B130647
  · exact B130651
  · exact B130655
  · exact B130659
  · exact B130663
  · exact B130667
  · exact B130671
  · exact B130675
  · exact B130679
  · exact B130683
  · exact B130687
  · exact B130691
  · exact B130695
  · exact B130699
  · exact B130703
  · exact B130707
  · exact B130711
  · exact B130715
  · exact B130719
  · exact B130723
  · exact B130727
  · exact B130731
  · exact B130735
  · exact B130739
  · exact B130743
  · exact B130747
  · exact B130751
  · exact B130755
  · exact B130759
  · exact B130763
  · exact B130767
  · exact B130771
  · exact B130775
  · exact B130779
  · exact B130783
  · exact B130787
  · exact B130791
  · exact B130795
  · exact B130799
  · exact B130803
  · exact B130807
  · exact B130811
  · exact B130815
  · exact B130819
  · exact B130823
  · exact B130827
  · exact B130831
  · exact B130835
  · exact B130839
  · exact B130843
  · exact B130847
  · exact B130851
  · exact B130855
  · exact B130859
  · exact B130863
  · exact B130867
  · exact B130871
  · exact B130875
  · exact B130879
  · exact B130883
  · exact B130887
  · exact B130891
  · exact B130895
  · exact B130899
  · exact B130903
  · exact B130907
  · exact B130911
  · exact B130915
  · exact B130919
  · exact B130923
  · exact B130927
  · exact B130931
  · exact B130935
  · exact B130939
  · exact B130943
  · exact B130947
  · exact B130951
  · exact B130955
  · exact B130959
  · exact B130963
  · exact B130967
  · exact B130971
  · exact B130975
  · exact B130979
  · exact B130983
  · exact B130987
  · exact B130991
  · exact B130995
  · exact B130999
  · exact B131003
  · exact B131007
  · exact B131011
  · exact B131015
  · exact B131019
  · exact B131023
  · exact B131027
  · exact B131031
  · exact B131035
  · exact B131039
  · exact B131043
  · exact B131047
  · exact B131051
  · exact B131055
  · exact B131059
  · exact B131063
  · exact B131067
  · exact B131071
  · exact B131075
  · exact B131079
  · exact B131083
  · exact B131087
  · exact B131091
  · exact B131095
  · exact B131099
  · exact B131103
  · exact B131107
  · exact B131111
  · exact B131115
  · exact B131119
  · exact B131123
  · exact B131127
  · exact B131131
  · exact B131135
  · exact B131139
  · exact B131143
  · exact B131147
  · exact B131151
  · exact B131155
  · exact B131159
  · exact B131163
  · exact B131167
  · exact B131171
  · exact B131175
  · exact B131179
  · exact B131183
  · exact B131187
  · exact B131191
  · exact B131195
  · exact B131199
  · exact B131203
  · exact B131207
  · exact B131211
  · exact B131215
  · exact B131219
  · exact B131223
  · exact B131227
  · exact B131231
  · exact B131235
  · exact B131239
  · exact B131243
  · exact B131247
  · exact B131251
  · exact B131255
  · exact B131259
  · exact B131263
  · exact B131267
  · exact B131271
  · exact B131275
  · exact B131279
  · exact B131283
  · exact B131287
  · exact B131291
  · exact B131295
  · exact B131299
  · exact B131303
  · exact B131307
  · exact B131311
  · exact B131315
  · exact B131319
  · exact B131323
  · exact B131327
  · exact B131331
  · exact B131335
  · exact B131339
  · exact B131343
  · exact B131347
  · exact B131351
  · exact B131355
  · exact B131359
  · exact B131363
  · exact B131367
  · exact B131371
  · exact B131375
  · exact B131379
  · exact B131383
  · exact B131387
  · exact B131391
  · exact B131395
  · exact B131399
  · exact B131403
  · exact B131407
  · exact B131411
  · exact B131415
  · exact B131419
  · exact B131423
  · exact B131427
  · exact B131431
  · exact B131435
  · exact B131439
  · exact B131443
  · exact B131447
  · exact B131451
  · exact B131455
  · exact B131459
  · exact B131463
  · exact B131467
  · exact B131471
  · exact B131475
  · exact B131479
  · exact B131483
  · exact B131487
  · exact B131491
  · exact B131495
  · exact B131499
  · exact B131503
  · exact B131507
  · exact B131511
  · exact B131515
  · exact B131519
  · exact B131523
  · exact B131527
  · exact B131531
  · exact B131535
  · exact B131539
  · exact B131543
  · exact B131547
  · exact B131551
  · exact B131555
  · exact B131559
  · exact B131563
  · exact B131567
  · exact B131571
  · exact B131575
  · exact B131579
  · exact B131583
  · exact B131587
  · exact B131591
  · exact B131595
  · exact B131599
  · exact B131603
  · exact B131607
  · exact B131611
  · exact B131615
  · exact B131619
  · exact B131623
  · exact B131627
  · exact B131631
  · exact B131635
  · exact B131639
  · exact B131643
  · exact B131647
  · exact B131651
  · exact B131655
  · exact B131659
  · exact B131663
  · exact B131667
  · exact B131671
  · exact B131675
  · exact B131679
  · exact B131683
  · exact B131687
  · exact B131691
  · exact B131695
  · exact B131699
  · exact B131703
  · exact B131707
  · exact B131711
  · exact B131715
  · exact B131719
  · exact B131723
  · exact B131727
  · exact B131731
  · exact B131735
  · exact B131739
  · exact B131743
  · exact B131747
  · exact B131751
  · exact B131755
  · exact B131759
  · exact B131763
  · exact B131767
  · exact B131771
  · exact B131775
  · exact B131779
  · exact B131783
  · exact B131787

theorem solution (m : ℕ) (hlo : 127788 ≤ m) (hhi : m ≤ 131788) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 31947 ≤ j := by omega
    have hj2 : j ≤ 32946 := by omega
    have hb : Blo 127788 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 32647 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
