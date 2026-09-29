-- Prove2me | solution 1 for syracuse_descends_range_183802_187802
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:47.85873+00:00
-- url     : https://prove2.me/submissions/9a2ded7e-29f4-4ca7-9da7-a486d4e9b525

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


theorem B196625 : Blo 183802 196625 := bbase (se 2 (by rfl) ⟨73734, by rfl⟩ : syracuseStep 196625 = 147469) (by norm_num)
theorem B524357 : Blo 183802 524357 := bbase (se 4 (by rfl) ⟨49158, by rfl⟩ : syracuseStep 524357 = 98317) (by norm_num)
theorem B950453 : Blo 183802 950453 := bbase (se 5 (by rfl) ⟨44552, by rfl⟩ : syracuseStep 950453 = 89105) (by norm_num)
theorem B196813 : Blo 183802 196813 := bbase (se 3 (by rfl) ⟨36902, by rfl⟩ : syracuseStep 196813 = 73805) (by norm_num)
theorem B786773 : Blo 183802 786773 := bbase (se 10 (by rfl) ⟨1152, by rfl⟩ : syracuseStep 786773 = 2305) (by norm_num)
theorem B196997 : Blo 183802 196997 := bbase (se 4 (by rfl) ⟨18468, by rfl⟩ : syracuseStep 196997 = 36937) (by norm_num)
theorem B622997 : Blo 183802 622997 := bbase (se 6 (by rfl) ⟨14601, by rfl⟩ : syracuseStep 622997 = 29203) (by norm_num)
theorem B393653 : Blo 183802 393653 := bbase (se 5 (by rfl) ⟨18452, by rfl⟩ : syracuseStep 393653 = 36905) (by norm_num)
theorem B524789 : Blo 183802 524789 := bbase (se 5 (by rfl) ⟨24599, by rfl⟩ : syracuseStep 524789 = 49199) (by norm_num)
theorem B393797 : Blo 183802 393797 := bbase (se 4 (by rfl) ⟨36918, by rfl⟩ : syracuseStep 393797 = 73837) (by norm_num)
theorem B590581 : Blo 183802 590581 := bbase (se 5 (by rfl) ⟨27683, by rfl⟩ : syracuseStep 590581 = 55367) (by norm_num)
theorem B590645 : Blo 183802 590645 := bbase (se 5 (by rfl) ⟨27686, by rfl⟩ : syracuseStep 590645 = 55373) (by norm_num)
theorem B295733 : Blo 183802 295733 := bbase (se 5 (by rfl) ⟨13862, by rfl⟩ : syracuseStep 295733 = 27725) (by norm_num)
theorem B623429 : Blo 183802 623429 := bbase (se 4 (by rfl) ⟨58446, by rfl⟩ : syracuseStep 623429 = 116893) (by norm_num)
theorem B263101 : Blo 183802 263101 := bbase (se 3 (by rfl) ⟨49331, by rfl⟩ : syracuseStep 263101 = 98663) (by norm_num)
theorem B197749 : Blo 183802 197749 := bbase (se 5 (by rfl) ⟨9269, by rfl⟩ : syracuseStep 197749 = 18539) (by norm_num)
theorem B361589 : Blo 183802 361589 := bbase (se 5 (by rfl) ⟨16949, by rfl⟩ : syracuseStep 361589 = 33899) (by norm_num)
theorem B296117 : Blo 183802 296117 := bbase (se 5 (by rfl) ⟨13880, by rfl⟩ : syracuseStep 296117 = 27761) (by norm_num)
theorem B197821 : Blo 183802 197821 := bbase (se 3 (by rfl) ⟨37091, by rfl⟩ : syracuseStep 197821 = 74183) (by norm_num)
theorem B525541 : Blo 183802 525541 := bbase (se 4 (by rfl) ⟨49269, by rfl⟩ : syracuseStep 525541 = 98539) (by norm_num)
theorem B623861 : Blo 183802 623861 := bbase (se 5 (by rfl) ⟨29243, by rfl⟩ : syracuseStep 623861 = 58487) (by norm_num)
theorem B722197 : Blo 183802 722197 := bbase (se 6 (by rfl) ⟨16926, by rfl⟩ : syracuseStep 722197 = 33853) (by norm_num)
theorem B394541 : Blo 183802 394541 := bbase (se 3 (by rfl) ⟨73976, by rfl⟩ : syracuseStep 394541 = 147953) (by norm_num)
theorem B787765 : Blo 183802 787765 := bbase (se 5 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 787765 = 73853) (by norm_num)
theorem B296245 : Blo 183802 296245 := bbase (se 5 (by rfl) ⟨13886, by rfl⟩ : syracuseStep 296245 = 27773) (by norm_num)
theorem B886085 : Blo 183802 886085 := bbase (se 4 (by rfl) ⟨83070, by rfl⟩ : syracuseStep 886085 = 166141) (by norm_num)
theorem B198001 : Blo 183802 198001 := bbase (se 2 (by rfl) ⟨74250, by rfl⟩ : syracuseStep 198001 = 148501) (by norm_num)
theorem B263693 : Blo 183802 263693 := bbase (se 3 (by rfl) ⟨49442, by rfl⟩ : syracuseStep 263693 = 98885) (by norm_num)
theorem B263773 : Blo 183802 263773 := bbase (se 3 (by rfl) ⟨49457, by rfl⟩ : syracuseStep 263773 = 98915) (by norm_num)
theorem B624293 : Blo 183802 624293 := bbase (se 4 (by rfl) ⟨58527, by rfl⟩ : syracuseStep 624293 = 117055) (by norm_num)
theorem B263893 : Blo 183802 263893 := bbase (se 7 (by rfl) ⟨3092, by rfl⟩ : syracuseStep 263893 = 6185) (by norm_num)
theorem B198445 : Blo 183802 198445 := bbase (se 3 (by rfl) ⟨37208, by rfl⟩ : syracuseStep 198445 = 74417) (by norm_num)
theorem B263989 : Blo 183802 263989 := bbase (se 5 (by rfl) ⟨12374, by rfl⟩ : syracuseStep 263989 = 24749) (by norm_num)
theorem B427933 : Blo 183802 427933 := bbase (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) (by norm_num)
theorem B198569 : Blo 183802 198569 := bbase (se 2 (by rfl) ⟨74463, by rfl⟩ : syracuseStep 198569 = 148927) (by norm_num)
theorem B395293 : Blo 183802 395293 := bbase (se 3 (by rfl) ⟨74117, by rfl⟩ : syracuseStep 395293 = 148235) (by norm_num)
theorem B624725 : Blo 183802 624725 := bbase (se 8 (by rfl) ⟨3660, by rfl⟩ : syracuseStep 624725 = 7321) (by norm_num)
theorem B198821 : Blo 183802 198821 := bbase (se 4 (by rfl) ⟨18639, by rfl⟩ : syracuseStep 198821 = 37279) (by norm_num)
theorem B395437 : Blo 183802 395437 := bbase (se 3 (by rfl) ⟨74144, by rfl⟩ : syracuseStep 395437 = 148289) (by norm_num)
theorem B297245 : Blo 183802 297245 := bbase (se 3 (by rfl) ⟨55733, by rfl⟩ : syracuseStep 297245 = 111467) (by norm_num)
theorem B264485 : Blo 183802 264485 := bbase (se 4 (by rfl) ⟨24795, by rfl⟩ : syracuseStep 264485 = 49591) (by norm_num)
theorem B297317 : Blo 183802 297317 := bbase (se 4 (by rfl) ⟨27873, by rfl⟩ : syracuseStep 297317 = 55747) (by norm_num)
theorem B297373 : Blo 183802 297373 := bbase (se 3 (by rfl) ⟨55757, by rfl⟩ : syracuseStep 297373 = 111515) (by norm_num)
theorem B428485 : Blo 183802 428485 := bbase (se 4 (by rfl) ⟨40170, by rfl⟩ : syracuseStep 428485 = 80341) (by norm_num)
theorem B625157 : Blo 183802 625157 := bbase (se 4 (by rfl) ⟨58608, by rfl⟩ : syracuseStep 625157 = 117217) (by norm_num)
theorem B395813 : Blo 183802 395813 := bbase (se 4 (by rfl) ⟨37107, by rfl⟩ : syracuseStep 395813 = 74215) (by norm_num)
theorem B199265 : Blo 183802 199265 := bbase (se 2 (by rfl) ⟨74724, by rfl⟩ : syracuseStep 199265 = 149449) (by norm_num)
theorem B559813 : Blo 183802 559813 := bbase (se 4 (by rfl) ⟨52482, by rfl⟩ : syracuseStep 559813 = 104965) (by norm_num)
theorem B1411829 : Blo 183802 1411829 := bbase (se 5 (by rfl) ⟨66179, by rfl⟩ : syracuseStep 1411829 = 132359) (by norm_num)
theorem B297757 : Blo 183802 297757 := bbase (se 3 (by rfl) ⟨55829, by rfl⟩ : syracuseStep 297757 = 111659) (by norm_num)
theorem B1575733 : Blo 183802 1575733 := bbase (se 5 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 1575733 = 147725) (by norm_num)
theorem B265037 : Blo 183802 265037 := bbase (se 3 (by rfl) ⟨49694, by rfl⟩ : syracuseStep 265037 = 99389) (by norm_num)
theorem B199513 : Blo 183802 199513 := bbase (se 2 (by rfl) ⟨74817, by rfl⟩ : syracuseStep 199513 = 149635) (by norm_num)
theorem B396181 : Blo 183802 396181 := bbase (se 6 (by rfl) ⟨9285, by rfl⟩ : syracuseStep 396181 = 18571) (by norm_num)
theorem B625589 : Blo 183802 625589 := bbase (se 5 (by rfl) ⟨29324, by rfl⟩ : syracuseStep 625589 = 58649) (by norm_num)
theorem B298013 : Blo 183802 298013 := bbase (se 3 (by rfl) ⟨55877, by rfl⟩ : syracuseStep 298013 = 111755) (by norm_num)
theorem B756869 : Blo 183802 756869 := bbase (se 4 (by rfl) ⟨70956, by rfl⟩ : syracuseStep 756869 = 141913) (by norm_num)
theorem B199957 : Blo 183802 199957 := bbase (se 6 (by rfl) ⟨4686, by rfl⟩ : syracuseStep 199957 = 9373) (by norm_num)
theorem B232733 : Blo 183802 232733 := bbase (se 3 (by rfl) ⟨43637, by rfl⟩ : syracuseStep 232733 = 87275) (by norm_num)
theorem B200017 : Blo 183802 200017 := bbase (se 2 (by rfl) ⟨75006, by rfl⟩ : syracuseStep 200017 = 150013) (by norm_num)
theorem B232789 : Blo 183802 232789 := bbase (se 11 (by rfl) ⟨170, by rfl⟩ : syracuseStep 232789 = 341) (by norm_num)
theorem B626021 : Blo 183802 626021 := bbase (se 4 (by rfl) ⟨58689, by rfl⟩ : syracuseStep 626021 = 117379) (by norm_num)
theorem B232885 : Blo 183802 232885 := bbase (se 5 (by rfl) ⟨10916, by rfl⟩ : syracuseStep 232885 = 21833) (by norm_num)
theorem B265789 : Blo 183802 265789 := bbase (se 3 (by rfl) ⟨49835, by rfl⟩ : syracuseStep 265789 = 99671) (by norm_num)
theorem B233057 : Blo 183802 233057 := bbase (se 2 (by rfl) ⟨87396, by rfl⟩ : syracuseStep 233057 = 174793) (by norm_num)
theorem B200333 : Blo 183802 200333 := bbase (se 3 (by rfl) ⟨37562, by rfl⟩ : syracuseStep 200333 = 75125) (by norm_num)
theorem B233113 : Blo 183802 233113 := bbase (se 2 (by rfl) ⟨87417, by rfl⟩ : syracuseStep 233113 = 174835) (by norm_num)
theorem B233209 : Blo 183802 233209 := bbase (se 2 (by rfl) ⟨87453, by rfl⟩ : syracuseStep 233209 = 174907) (by norm_num)
theorem B331517 : Blo 183802 331517 := bbase (se 3 (by rfl) ⟨62159, by rfl⟩ : syracuseStep 331517 = 124319) (by norm_num)
theorem B593669 : Blo 183802 593669 := bbase (se 4 (by rfl) ⟨55656, by rfl⟩ : syracuseStep 593669 = 111313) (by norm_num)
theorem B626453 : Blo 183802 626453 := bbase (se 6 (by rfl) ⟨14682, by rfl⟩ : syracuseStep 626453 = 29365) (by norm_num)
theorem B298885 : Blo 183802 298885 := bbase (se 4 (by rfl) ⟨28020, by rfl⟩ : syracuseStep 298885 = 56041) (by norm_num)
theorem B331661 : Blo 183802 331661 := bbase (se 3 (by rfl) ⟨62186, by rfl⟩ : syracuseStep 331661 = 124373) (by norm_num)
theorem B233381 : Blo 183802 233381 := bbase (se 4 (by rfl) ⟨21879, by rfl⟩ : syracuseStep 233381 = 43759) (by norm_num)
theorem B233437 : Blo 183802 233437 := bbase (se 3 (by rfl) ⟨43769, by rfl⟩ : syracuseStep 233437 = 87539) (by norm_num)
theorem B298981 : Blo 183802 298981 := bbase (se 4 (by rfl) ⟨28029, by rfl⟩ : syracuseStep 298981 = 56059) (by norm_num)
theorem B528389 : Blo 183802 528389 := bbase (se 4 (by rfl) ⟨49536, by rfl⟩ : syracuseStep 528389 = 99073) (by norm_num)
theorem B233533 : Blo 183802 233533 := bbase (se 3 (by rfl) ⟨43787, by rfl⟩ : syracuseStep 233533 = 87575) (by norm_num)
theorem B888965 : Blo 183802 888965 := bbase (se 4 (by rfl) ⟨83340, by rfl⟩ : syracuseStep 888965 = 166681) (by norm_num)
theorem B299141 : Blo 183802 299141 := bbase (se 4 (by rfl) ⟨28044, by rfl⟩ : syracuseStep 299141 = 56089) (by norm_num)
theorem B626885 : Blo 183802 626885 := bbase (se 4 (by rfl) ⟨58770, by rfl⟩ : syracuseStep 626885 = 117541) (by norm_num)
theorem B233705 : Blo 183802 233705 := bbase (se 2 (by rfl) ⟨87639, by rfl⟩ : syracuseStep 233705 = 175279) (by norm_num)
theorem B233761 : Blo 183802 233761 := bbase (se 2 (by rfl) ⟨87660, by rfl⟩ : syracuseStep 233761 = 175321) (by norm_num)
theorem B2003285 : Blo 183802 2003285 := bbase (se 10 (by rfl) ⟨2934, by rfl⟩ : syracuseStep 2003285 = 5869) (by norm_num)
theorem B266581 : Blo 183802 266581 := bbase (se 10 (by rfl) ⟨390, by rfl⟩ : syracuseStep 266581 = 781) (by norm_num)
theorem B397685 : Blo 183802 397685 := bbase (se 5 (by rfl) ⟨18641, by rfl⟩ : syracuseStep 397685 = 37283) (by norm_num)
theorem B233857 : Blo 183802 233857 := bbase (se 2 (by rfl) ⟨87696, by rfl⟩ : syracuseStep 233857 = 175393) (by norm_num)
theorem B397829 : Blo 183802 397829 := bbase (se 4 (by rfl) ⟨37296, by rfl⟩ : syracuseStep 397829 = 74593) (by norm_num)
theorem B1217045 : Blo 183802 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B234029 : Blo 183802 234029 := bbase (se 3 (by rfl) ⟨43880, by rfl⟩ : syracuseStep 234029 = 87761) (by norm_num)
theorem B1053269 : Blo 183802 1053269 := bbase (se 8 (by rfl) ⟨6171, by rfl⟩ : syracuseStep 1053269 = 12343) (by norm_num)
theorem B234085 : Blo 183802 234085 := bbase (se 4 (by rfl) ⟨21945, by rfl⟩ : syracuseStep 234085 = 43891) (by norm_num)
theorem B627317 : Blo 183802 627317 := bbase (se 5 (by rfl) ⟨29405, by rfl⟩ : syracuseStep 627317 = 58811) (by norm_num)
theorem B266917 : Blo 183802 266917 := bbase (se 4 (by rfl) ⟨25023, by rfl⟩ : syracuseStep 266917 = 50047) (by norm_num)
theorem B234181 : Blo 183802 234181 := bbase (se 4 (by rfl) ⟨21954, by rfl⟩ : syracuseStep 234181 = 43909) (by norm_num)
theorem B1577717 : Blo 183802 1577717 := bbase (se 5 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 1577717 = 147911) (by norm_num)
theorem B398189 : Blo 183802 398189 := bbase (se 3 (by rfl) ⟨74660, by rfl⟩ : syracuseStep 398189 = 149321) (by norm_num)
theorem B234353 : Blo 183802 234353 := bbase (se 2 (by rfl) ⟨87882, by rfl⟩ : syracuseStep 234353 = 175765) (by norm_num)
theorem B267133 : Blo 183802 267133 := bbase (se 3 (by rfl) ⟨50087, by rfl⟩ : syracuseStep 267133 = 100175) (by norm_num)
theorem B758693 : Blo 183802 758693 := bbase (se 4 (by rfl) ⟨71127, by rfl⟩ : syracuseStep 758693 = 142255) (by norm_num)
theorem B234409 : Blo 183802 234409 := bbase (se 2 (by rfl) ⟨87903, by rfl⟩ : syracuseStep 234409 = 175807) (by norm_num)
theorem B234505 : Blo 183802 234505 := bbase (se 2 (by rfl) ⟨87939, by rfl⟩ : syracuseStep 234505 = 175879) (by norm_num)
theorem B627749 : Blo 183802 627749 := bbase (se 4 (by rfl) ⟨58851, by rfl⟩ : syracuseStep 627749 = 117703) (by norm_num)
theorem B529573 : Blo 183802 529573 := bbase (se 4 (by rfl) ⟨49647, by rfl⟩ : syracuseStep 529573 = 99295) (by norm_num)
theorem B234677 : Blo 183802 234677 := bbase (se 5 (by rfl) ⟨11000, by rfl⟩ : syracuseStep 234677 = 22001) (by norm_num)
theorem B234733 : Blo 183802 234733 := bbase (se 3 (by rfl) ⟨44012, by rfl⟩ : syracuseStep 234733 = 88025) (by norm_num)
theorem B300269 : Blo 183802 300269 := bbase (se 3 (by rfl) ⟨56300, by rfl⟩ : syracuseStep 300269 = 112601) (by norm_num)
theorem B529733 : Blo 183802 529733 := bbase (se 4 (by rfl) ⟨49662, by rfl⟩ : syracuseStep 529733 = 99325) (by norm_num)
theorem B234829 : Blo 183802 234829 := bbase (se 3 (by rfl) ⟨44030, by rfl⟩ : syracuseStep 234829 = 88061) (by norm_num)
theorem B628181 : Blo 183802 628181 := bbase (se 7 (by rfl) ⟨7361, by rfl⟩ : syracuseStep 628181 = 14723) (by norm_num)
theorem B235001 : Blo 183802 235001 := bbase (se 2 (by rfl) ⟨88125, by rfl⟩ : syracuseStep 235001 = 176251) (by norm_num)
theorem B235057 : Blo 183802 235057 := bbase (se 2 (by rfl) ⟨88146, by rfl⟩ : syracuseStep 235057 = 176293) (by norm_num)
theorem B529973 : Blo 183802 529973 := bbase (se 5 (by rfl) ⟨24842, by rfl⟩ : syracuseStep 529973 = 49685) (by norm_num)
theorem B235153 : Blo 183802 235153 := bbase (se 2 (by rfl) ⟨88182, by rfl⟩ : syracuseStep 235153 = 176365) (by norm_num)
theorem B399077 : Blo 183802 399077 := bbase (se 4 (by rfl) ⟨37413, by rfl⟩ : syracuseStep 399077 = 74827) (by norm_num)
theorem B300781 : Blo 183802 300781 := bbase (se 3 (by rfl) ⟨56396, by rfl⟩ : syracuseStep 300781 = 112793) (by norm_num)
theorem B530165 : Blo 183802 530165 := bbase (se 5 (by rfl) ⟨24851, by rfl⟩ : syracuseStep 530165 = 49703) (by norm_num)
theorem B235325 : Blo 183802 235325 := bbase (se 3 (by rfl) ⟨44123, by rfl⟩ : syracuseStep 235325 = 88247) (by norm_num)
theorem B235381 : Blo 183802 235381 := bbase (se 5 (by rfl) ⟨11033, by rfl⟩ : syracuseStep 235381 = 22067) (by norm_num)
theorem B628613 : Blo 183802 628613 := bbase (se 4 (by rfl) ⟨58932, by rfl⟩ : syracuseStep 628613 = 117865) (by norm_num)
theorem B1185749 : Blo 183802 1185749 := bbase (se 7 (by rfl) ⟨13895, by rfl⟩ : syracuseStep 1185749 = 27791) (by norm_num)
theorem B235477 : Blo 183802 235477 := bbase (se 7 (by rfl) ⟨2759, by rfl⟩ : syracuseStep 235477 = 5519) (by norm_num)
theorem B399325 : Blo 183802 399325 := bbase (se 3 (by rfl) ⟨74873, by rfl⟩ : syracuseStep 399325 = 149747) (by norm_num)
theorem B235649 : Blo 183802 235649 := bbase (se 2 (by rfl) ⟨88368, by rfl⟩ : syracuseStep 235649 = 176737) (by norm_num)
theorem B235705 : Blo 183802 235705 := bbase (se 2 (by rfl) ⟨88389, by rfl⟩ : syracuseStep 235705 = 176779) (by norm_num)
theorem B792773 : Blo 183802 792773 := bbase (se 4 (by rfl) ⟨74322, by rfl⟩ : syracuseStep 792773 = 148645) (by norm_num)
theorem B891157 : Blo 183802 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B235801 : Blo 183802 235801 := bbase (se 2 (by rfl) ⟨88425, by rfl⟩ : syracuseStep 235801 = 176851) (by norm_num)
theorem B629045 : Blo 183802 629045 := bbase (se 5 (by rfl) ⟨29486, by rfl⟩ : syracuseStep 629045 = 58973) (by norm_num)
theorem B235973 : Blo 183802 235973 := bbase (se 4 (by rfl) ⟨22122, by rfl⟩ : syracuseStep 235973 = 44245) (by norm_num)
theorem B465365 : Blo 183802 465365 := bbase (se 7 (by rfl) ⟨5453, by rfl⟩ : syracuseStep 465365 = 10907) (by norm_num)
theorem B399829 : Blo 183802 399829 := bbase (se 7 (by rfl) ⟨4685, by rfl⟩ : syracuseStep 399829 = 9371) (by norm_num)
theorem B793061 : Blo 183802 793061 := bbase (se 4 (by rfl) ⟨74349, by rfl⟩ : syracuseStep 793061 = 148699) (by norm_num)
theorem B236029 : Blo 183802 236029 := bbase (se 3 (by rfl) ⟨44255, by rfl⟩ : syracuseStep 236029 = 88511) (by norm_num)
theorem B2103893 : Blo 183802 2103893 := bbase (se 8 (by rfl) ⟨12327, by rfl⟩ : syracuseStep 2103893 = 24655) (by norm_num)
theorem B236125 : Blo 183802 236125 := bbase (se 3 (by rfl) ⟨44273, by rfl⟩ : syracuseStep 236125 = 88547) (by norm_num)
theorem B531157 : Blo 183802 531157 := bbase (se 7 (by rfl) ⟨6224, by rfl⟩ : syracuseStep 531157 = 12449) (by norm_num)
theorem B629477 : Blo 183802 629477 := bbase (se 4 (by rfl) ⟨59013, by rfl⟩ : syracuseStep 629477 = 118027) (by norm_num)
theorem B236297 : Blo 183802 236297 := bbase (se 2 (by rfl) ⟨88611, by rfl⟩ : syracuseStep 236297 = 177223) (by norm_num)
theorem B465709 : Blo 183802 465709 := bbase (se 3 (by rfl) ⟨87320, by rfl⟩ : syracuseStep 465709 = 174641) (by norm_num)
theorem B236353 : Blo 183802 236353 := bbase (se 2 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 236353 = 177265) (by norm_num)
theorem B465821 : Blo 183802 465821 := bbase (se 3 (by rfl) ⟨87341, by rfl⟩ : syracuseStep 465821 = 174683) (by norm_num)
theorem B236449 : Blo 183802 236449 := bbase (se 2 (by rfl) ⟨88668, by rfl⟩ : syracuseStep 236449 = 177337) (by norm_num)
theorem B236621 : Blo 183802 236621 := bbase (se 3 (by rfl) ⟨44366, by rfl⟩ : syracuseStep 236621 = 88733) (by norm_num)
theorem B466013 : Blo 183802 466013 := bbase (se 3 (by rfl) ⟨87377, by rfl⟩ : syracuseStep 466013 = 174755) (by norm_num)
theorem B236677 : Blo 183802 236677 := bbase (se 4 (by rfl) ⟨22188, by rfl⟩ : syracuseStep 236677 = 44377) (by norm_num)
theorem B629909 : Blo 183802 629909 := bbase (se 6 (by rfl) ⟨14763, by rfl⟩ : syracuseStep 629909 = 29527) (by norm_num)
theorem B2399381 : Blo 183802 2399381 := bbase (se 6 (by rfl) ⟨56235, by rfl⟩ : syracuseStep 2399381 = 112471) (by norm_num)
theorem B793813 : Blo 183802 793813 := bbase (se 7 (by rfl) ⟨9302, by rfl⟩ : syracuseStep 793813 = 18605) (by norm_num)
theorem B236773 : Blo 183802 236773 := bbase (se 4 (by rfl) ⟨22197, by rfl⟩ : syracuseStep 236773 = 44395) (by norm_num)
theorem B400717 : Blo 183802 400717 := bbase (se 3 (by rfl) ⟨75134, by rfl⟩ : syracuseStep 400717 = 150269) (by norm_num)
theorem B269693 : Blo 183802 269693 := bbase (se 3 (by rfl) ⟨50567, by rfl⟩ : syracuseStep 269693 = 101135) (by norm_num)
theorem B236945 : Blo 183802 236945 := bbase (se 2 (by rfl) ⟨88854, by rfl⟩ : syracuseStep 236945 = 177709) (by norm_num)
theorem B466357 : Blo 183802 466357 := bbase (se 5 (by rfl) ⟨21860, by rfl⟩ : syracuseStep 466357 = 43721) (by norm_num)
theorem B237001 : Blo 183802 237001 := bbase (se 2 (by rfl) ⟨88875, by rfl⟩ : syracuseStep 237001 = 177751) (by norm_num)
theorem B597461 : Blo 183802 597461 := bbase (se 7 (by rfl) ⟨7001, by rfl⟩ : syracuseStep 597461 = 14003) (by norm_num)
theorem B466469 : Blo 183802 466469 := bbase (se 4 (by rfl) ⟨43731, by rfl⟩ : syracuseStep 466469 = 87463) (by norm_num)
theorem B237097 : Blo 183802 237097 := bbase (se 2 (by rfl) ⟨88911, by rfl⟩ : syracuseStep 237097 = 177823) (by norm_num)
theorem B630341 : Blo 183802 630341 := bbase (se 4 (by rfl) ⟨59094, by rfl⟩ : syracuseStep 630341 = 118189) (by norm_num)
theorem B237269 : Blo 183802 237269 := bbase (se 7 (by rfl) ⟨2780, by rfl⟩ : syracuseStep 237269 = 5561) (by norm_num)
theorem B466661 : Blo 183802 466661 := bbase (se 4 (by rfl) ⟨43749, by rfl⟩ : syracuseStep 466661 = 87499) (by norm_num)
theorem B237325 : Blo 183802 237325 := bbase (se 3 (by rfl) ⟨44498, by rfl⟩ : syracuseStep 237325 = 88997) (by norm_num)
theorem B532261 : Blo 183802 532261 := bbase (se 4 (by rfl) ⟨49899, by rfl⟩ : syracuseStep 532261 = 99799) (by norm_num)
theorem B237421 : Blo 183802 237421 := bbase (se 3 (by rfl) ⟨44516, by rfl⟩ : syracuseStep 237421 = 89033) (by norm_num)
theorem B237449 : Blo 183802 237449 := bbase (se 2 (by rfl) ⟨89043, by rfl⟩ : syracuseStep 237449 = 178087) (by norm_num)
theorem B794549 : Blo 183802 794549 := bbase (se 5 (by rfl) ⟨37244, by rfl⟩ : syracuseStep 794549 = 74489) (by norm_num)
theorem B1777621 : Blo 183802 1777621 := bbase (se 7 (by rfl) ⟨20831, by rfl⟩ : syracuseStep 1777621 = 41663) (by norm_num)
theorem B630773 : Blo 183802 630773 := bbase (se 5 (by rfl) ⟨29567, by rfl⟩ : syracuseStep 630773 = 59135) (by norm_num)
theorem B1351669 : Blo 183802 1351669 := bbase (se 5 (by rfl) ⟨63359, by rfl⟩ : syracuseStep 1351669 = 126719) (by norm_num)
theorem B335893 : Blo 183802 335893 := bbase (se 6 (by rfl) ⟨7872, by rfl⟩ : syracuseStep 335893 = 15745) (by norm_num)
theorem B237593 : Blo 183802 237593 := bbase (se 2 (by rfl) ⟨89097, by rfl⟩ : syracuseStep 237593 = 178195) (by norm_num)
theorem B467005 : Blo 183802 467005 := bbase (se 3 (by rfl) ⟨87563, by rfl⟩ : syracuseStep 467005 = 175127) (by norm_num)
theorem B237649 : Blo 183802 237649 := bbase (se 2 (by rfl) ⟨89118, by rfl⟩ : syracuseStep 237649 = 178237) (by norm_num)
theorem B499861 : Blo 183802 499861 := bbase (se 6 (by rfl) ⟨11715, by rfl⟩ : syracuseStep 499861 = 23431) (by norm_num)
theorem B467117 : Blo 183802 467117 := bbase (se 3 (by rfl) ⟨87584, by rfl⟩ : syracuseStep 467117 = 175169) (by norm_num)
theorem B2367701 : Blo 183802 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B598373 : Blo 183802 598373 := bbase (se 4 (by rfl) ⟨56097, by rfl⟩ : syracuseStep 598373 = 112195) (by norm_num)
theorem B467309 : Blo 183802 467309 := bbase (se 3 (by rfl) ⟨87620, by rfl⟩ : syracuseStep 467309 = 175241) (by norm_num)
theorem B631205 : Blo 183802 631205 := bbase (se 4 (by rfl) ⟨59175, by rfl⟩ : syracuseStep 631205 = 118351) (by norm_num)
theorem B467653 : Blo 183802 467653 := bbase (se 4 (by rfl) ⟨43842, by rfl⟩ : syracuseStep 467653 = 87685) (by norm_num)
theorem B402149 : Blo 183802 402149 := bbase (se 4 (by rfl) ⟨37701, by rfl⟩ : syracuseStep 402149 = 75403) (by norm_num)
theorem B402221 : Blo 183802 402221 := bbase (se 3 (by rfl) ⟨75416, by rfl⟩ : syracuseStep 402221 = 150833) (by norm_num)
theorem B467765 : Blo 183802 467765 := bbase (se 5 (by rfl) ⟨21926, by rfl⟩ : syracuseStep 467765 = 43853) (by norm_num)
theorem B631637 : Blo 183802 631637 := bbase (se 9 (by rfl) ⟨1850, by rfl⟩ : syracuseStep 631637 = 3701) (by norm_num)
theorem B3449749 : Blo 183802 3449749 := bbase (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) (by norm_num)
theorem B467957 : Blo 183802 467957 := bbase (se 5 (by rfl) ⟨21935, by rfl⟩ : syracuseStep 467957 = 43871) (by norm_num)
theorem B1123541 : Blo 183802 1123541 := bbase (se 7 (by rfl) ⟨13166, by rfl⟩ : syracuseStep 1123541 = 26333) (by norm_num)
theorem B632069 : Blo 183802 632069 := bbase (se 4 (by rfl) ⟨59256, by rfl⟩ : syracuseStep 632069 = 118513) (by norm_num)
theorem B533765 : Blo 183802 533765 := bbase (se 4 (by rfl) ⟨50040, by rfl⟩ : syracuseStep 533765 = 100081) (by norm_num)
theorem B468301 : Blo 183802 468301 := bbase (se 3 (by rfl) ⟨87806, by rfl⟩ : syracuseStep 468301 = 175613) (by norm_num)
theorem B599381 : Blo 183802 599381 := bbase (se 12 (by rfl) ⟨219, by rfl⟩ : syracuseStep 599381 = 439) (by norm_num)
theorem B468413 : Blo 183802 468413 := bbase (se 3 (by rfl) ⟨87827, by rfl⟩ : syracuseStep 468413 = 175655) (by norm_num)
theorem B4793813 : Blo 183802 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B468605 : Blo 183802 468605 := bbase (se 3 (by rfl) ⟨87863, by rfl⟩ : syracuseStep 468605 = 175727) (by norm_num)
theorem B599717 : Blo 183802 599717 := bbase (se 4 (by rfl) ⟨56223, by rfl⟩ : syracuseStep 599717 = 112447) (by norm_num)
theorem B337589 : Blo 183802 337589 := bbase (se 5 (by rfl) ⟨15824, by rfl⟩ : syracuseStep 337589 = 31649) (by norm_num)
theorem B632501 : Blo 183802 632501 := bbase (se 5 (by rfl) ⟨29648, by rfl⟩ : syracuseStep 632501 = 59297) (by norm_num)
theorem B206797 : Blo 183802 206797 := bbase (se 3 (by rfl) ⟨38774, by rfl⟩ : syracuseStep 206797 = 77549) (by norm_num)
theorem B468949 : Blo 183802 468949 := bbase (se 7 (by rfl) ⟨5495, by rfl⟩ : syracuseStep 468949 = 10991) (by norm_num)
theorem B206833 : Blo 183802 206833 := bbase (se 2 (by rfl) ⟨77562, by rfl⟩ : syracuseStep 206833 = 155125) (by norm_num)
theorem B206869 : Blo 183802 206869 := bbase (se 6 (by rfl) ⟨4848, by rfl⟩ : syracuseStep 206869 = 9697) (by norm_num)
theorem B206905 : Blo 183802 206905 := bbase (se 2 (by rfl) ⟨77589, by rfl⟩ : syracuseStep 206905 = 155179) (by norm_num)
theorem B469061 : Blo 183802 469061 := bbase (se 4 (by rfl) ⟨43974, by rfl⟩ : syracuseStep 469061 = 87949) (by norm_num)
theorem B206941 : Blo 183802 206941 := bbase (se 3 (by rfl) ⟨38801, by rfl⟩ : syracuseStep 206941 = 77603) (by norm_num)
theorem B632933 : Blo 183802 632933 := bbase (se 4 (by rfl) ⟨59337, by rfl⟩ : syracuseStep 632933 = 118675) (by norm_num)
theorem B206977 : Blo 183802 206977 := bbase (se 2 (by rfl) ⟨77616, by rfl⟩ : syracuseStep 206977 = 155233) (by norm_num)
theorem B207013 : Blo 183802 207013 := bbase (se 4 (by rfl) ⟨19407, by rfl⟩ : syracuseStep 207013 = 38815) (by norm_num)
theorem B895157 : Blo 183802 895157 := bbase (se 5 (by rfl) ⟨41960, by rfl⟩ : syracuseStep 895157 = 83921) (by norm_num)
theorem B207049 : Blo 183802 207049 := bbase (se 2 (by rfl) ⟨77643, by rfl⟩ : syracuseStep 207049 = 155287) (by norm_num)
theorem B207085 : Blo 183802 207085 := bbase (se 3 (by rfl) ⟨38828, by rfl⟩ : syracuseStep 207085 = 77657) (by norm_num)
theorem B469253 : Blo 183802 469253 := bbase (se 4 (by rfl) ⟨43992, by rfl⟩ : syracuseStep 469253 = 87985) (by norm_num)
theorem B207121 : Blo 183802 207121 := bbase (se 2 (by rfl) ⟨77670, by rfl⟩ : syracuseStep 207121 = 155341) (by norm_num)
theorem B207157 : Blo 183802 207157 := bbase (se 5 (by rfl) ⟨9710, by rfl⟩ : syracuseStep 207157 = 19421) (by norm_num)
theorem B1419605 : Blo 183802 1419605 := bbase (se 10 (by rfl) ⟨2079, by rfl⟩ : syracuseStep 1419605 = 4159) (by norm_num)
theorem B207193 : Blo 183802 207193 := bbase (se 2 (by rfl) ⟨77697, by rfl⟩ : syracuseStep 207193 = 155395) (by norm_num)
theorem B207229 : Blo 183802 207229 := bbase (se 3 (by rfl) ⟨38855, by rfl⟩ : syracuseStep 207229 = 77711) (by norm_num)
theorem B567685 : Blo 183802 567685 := bbase (se 4 (by rfl) ⟨53220, by rfl⟩ : syracuseStep 567685 = 106441) (by norm_num)
theorem B207265 : Blo 183802 207265 := bbase (se 2 (by rfl) ⟨77724, by rfl⟩ : syracuseStep 207265 = 155449) (by norm_num)
theorem B207301 : Blo 183802 207301 := bbase (se 4 (by rfl) ⟨19434, by rfl⟩ : syracuseStep 207301 = 38869) (by norm_num)
theorem B207337 : Blo 183802 207337 := bbase (se 2 (by rfl) ⟨77751, by rfl⟩ : syracuseStep 207337 = 155503) (by norm_num)
theorem B207373 : Blo 183802 207373 := bbase (se 3 (by rfl) ⟨38882, by rfl⟩ : syracuseStep 207373 = 77765) (by norm_num)
theorem B633365 : Blo 183802 633365 := bbase (se 6 (by rfl) ⟨14844, by rfl⟩ : syracuseStep 633365 = 29689) (by norm_num)
theorem B207409 : Blo 183802 207409 := bbase (se 2 (by rfl) ⟨77778, by rfl⟩ : syracuseStep 207409 = 155557) (by norm_num)
theorem B404021 : Blo 183802 404021 := bbase (se 5 (by rfl) ⟨18938, by rfl⟩ : syracuseStep 404021 = 37877) (by norm_num)
theorem B207445 : Blo 183802 207445 := bbase (se 8 (by rfl) ⟨1215, by rfl⟩ : syracuseStep 207445 = 2431) (by norm_num)
theorem B469597 : Blo 183802 469597 := bbase (se 3 (by rfl) ⟨88049, by rfl⟩ : syracuseStep 469597 = 176099) (by norm_num)
theorem B207481 : Blo 183802 207481 := bbase (se 2 (by rfl) ⟨77805, by rfl⟩ : syracuseStep 207481 = 155611) (by norm_num)
theorem B207517 : Blo 183802 207517 := bbase (se 3 (by rfl) ⟨38909, by rfl⟩ : syracuseStep 207517 = 77819) (by norm_num)
theorem B207553 : Blo 183802 207553 := bbase (se 2 (by rfl) ⟨77832, by rfl⟩ : syracuseStep 207553 = 155665) (by norm_num)
theorem B404165 : Blo 183802 404165 := bbase (se 4 (by rfl) ⟨37890, by rfl⟩ : syracuseStep 404165 = 75781) (by norm_num)
theorem B469709 : Blo 183802 469709 := bbase (se 3 (by rfl) ⟨88070, by rfl⟩ : syracuseStep 469709 = 176141) (by norm_num)
theorem B207589 : Blo 183802 207589 := bbase (se 4 (by rfl) ⟨19461, by rfl⟩ : syracuseStep 207589 = 38923) (by norm_num)
theorem B207625 : Blo 183802 207625 := bbase (se 2 (by rfl) ⟨77859, by rfl⟩ : syracuseStep 207625 = 155719) (by norm_num)
theorem B207661 : Blo 183802 207661 := bbase (se 3 (by rfl) ⟨38936, by rfl⟩ : syracuseStep 207661 = 77873) (by norm_num)
theorem B207697 : Blo 183802 207697 := bbase (se 2 (by rfl) ⟨77886, by rfl⟩ : syracuseStep 207697 = 155773) (by norm_num)
theorem B207733 : Blo 183802 207733 := bbase (se 5 (by rfl) ⟨9737, by rfl⟩ : syracuseStep 207733 = 19475) (by norm_num)
theorem B502661 : Blo 183802 502661 := bbase (se 4 (by rfl) ⟨47124, by rfl⟩ : syracuseStep 502661 = 94249) (by norm_num)
theorem B469901 : Blo 183802 469901 := bbase (se 3 (by rfl) ⟨88106, by rfl⟩ : syracuseStep 469901 = 176213) (by norm_num)
theorem B207769 : Blo 183802 207769 := bbase (se 2 (by rfl) ⟨77913, by rfl⟩ : syracuseStep 207769 = 155827) (by norm_num)
theorem B207805 : Blo 183802 207805 := bbase (se 3 (by rfl) ⟨38963, by rfl⟩ : syracuseStep 207805 = 77927) (by norm_num)
theorem B633797 : Blo 183802 633797 := bbase (se 4 (by rfl) ⟨59418, by rfl⟩ : syracuseStep 633797 = 118837) (by norm_num)
theorem B207841 : Blo 183802 207841 := bbase (se 2 (by rfl) ⟨77940, by rfl⟩ : syracuseStep 207841 = 155881) (by norm_num)
theorem B207877 : Blo 183802 207877 := bbase (se 4 (by rfl) ⟨19488, by rfl⟩ : syracuseStep 207877 = 38977) (by norm_num)
theorem B207913 : Blo 183802 207913 := bbase (se 2 (by rfl) ⟨77967, by rfl⟩ : syracuseStep 207913 = 155935) (by norm_num)
theorem B601141 : Blo 183802 601141 := bbase (se 5 (by rfl) ⟨28178, by rfl⟩ : syracuseStep 601141 = 56357) (by norm_num)
theorem B699461 : Blo 183802 699461 := bbase (se 4 (by rfl) ⟨65574, by rfl⟩ : syracuseStep 699461 = 131149) (by norm_num)
theorem B207949 : Blo 183802 207949 := bbase (se 3 (by rfl) ⟨38990, by rfl⟩ : syracuseStep 207949 = 77981) (by norm_num)
theorem B207985 : Blo 183802 207985 := bbase (se 2 (by rfl) ⟨77994, by rfl⟩ : syracuseStep 207985 = 155989) (by norm_num)
theorem B208021 : Blo 183802 208021 := bbase (se 6 (by rfl) ⟨4875, by rfl⟩ : syracuseStep 208021 = 9751) (by norm_num)
theorem B797845 : Blo 183802 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B208057 : Blo 183802 208057 := bbase (se 2 (by rfl) ⟨78021, by rfl⟩ : syracuseStep 208057 = 156043) (by norm_num)
theorem B208093 : Blo 183802 208093 := bbase (se 3 (by rfl) ⟨39017, by rfl⟩ : syracuseStep 208093 = 78035) (by norm_num)
theorem B470245 : Blo 183802 470245 := bbase (se 4 (by rfl) ⟨44085, by rfl⟩ : syracuseStep 470245 = 88171) (by norm_num)
theorem B208129 : Blo 183802 208129 := bbase (se 2 (by rfl) ⟨78048, by rfl⟩ : syracuseStep 208129 = 156097) (by norm_num)
theorem B208165 : Blo 183802 208165 := bbase (se 4 (by rfl) ⟨19515, by rfl⟩ : syracuseStep 208165 = 39031) (by norm_num)
theorem B208201 : Blo 183802 208201 := bbase (se 2 (by rfl) ⟨78075, by rfl⟩ : syracuseStep 208201 = 156151) (by norm_num)
theorem B470357 : Blo 183802 470357 := bbase (se 11 (by rfl) ⟨344, by rfl⟩ : syracuseStep 470357 = 689) (by norm_num)
theorem B699749 : Blo 183802 699749 := bbase (se 4 (by rfl) ⟨65601, by rfl⟩ : syracuseStep 699749 = 131203) (by norm_num)
theorem B208237 : Blo 183802 208237 := bbase (se 3 (by rfl) ⟨39044, by rfl⟩ : syracuseStep 208237 = 78089) (by norm_num)
theorem B208273 : Blo 183802 208273 := bbase (se 2 (by rfl) ⟨78102, by rfl⟩ : syracuseStep 208273 = 156205) (by norm_num)
theorem B208309 : Blo 183802 208309 := bbase (se 5 (by rfl) ⟨9764, by rfl⟩ : syracuseStep 208309 = 19529) (by norm_num)
theorem B208345 : Blo 183802 208345 := bbase (se 2 (by rfl) ⟨78129, by rfl⟩ : syracuseStep 208345 = 156259) (by norm_num)
theorem B208381 : Blo 183802 208381 := bbase (se 3 (by rfl) ⟨39071, by rfl⟩ : syracuseStep 208381 = 78143) (by norm_num)
theorem B470549 : Blo 183802 470549 := bbase (se 6 (by rfl) ⟨11028, by rfl⟩ : syracuseStep 470549 = 22057) (by norm_num)
theorem B208417 : Blo 183802 208417 := bbase (se 2 (by rfl) ⟨78156, by rfl⟩ : syracuseStep 208417 = 156313) (by norm_num)
theorem B208453 : Blo 183802 208453 := bbase (se 4 (by rfl) ⟨19542, by rfl⟩ : syracuseStep 208453 = 39085) (by norm_num)
theorem B208489 : Blo 183802 208489 := bbase (se 2 (by rfl) ⟨78183, by rfl⟩ : syracuseStep 208489 = 156367) (by norm_num)
theorem B208525 : Blo 183802 208525 := bbase (se 3 (by rfl) ⟨39098, by rfl⟩ : syracuseStep 208525 = 78197) (by norm_num)
theorem B568997 : Blo 183802 568997 := bbase (se 4 (by rfl) ⟨53343, by rfl⟩ : syracuseStep 568997 = 106687) (by norm_num)
theorem B208561 : Blo 183802 208561 := bbase (se 2 (by rfl) ⟨78210, by rfl⟩ : syracuseStep 208561 = 156421) (by norm_num)
theorem B1814197 : Blo 183802 1814197 := bbase (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) (by norm_num)
theorem B1027765 : Blo 183802 1027765 := bbase (se 5 (by rfl) ⟨48176, by rfl⟩ : syracuseStep 1027765 = 96353) (by norm_num)
theorem B208597 : Blo 183802 208597 := bbase (se 7 (by rfl) ⟨2444, by rfl⟩ : syracuseStep 208597 = 4889) (by norm_num)
theorem B208633 : Blo 183802 208633 := bbase (se 2 (by rfl) ⟨78237, by rfl⟩ : syracuseStep 208633 = 156475) (by norm_num)
theorem B208669 : Blo 183802 208669 := bbase (se 3 (by rfl) ⟨39125, by rfl⟩ : syracuseStep 208669 = 78251) (by norm_num)
theorem B667445 : Blo 183802 667445 := bbase (se 5 (by rfl) ⟨31286, by rfl⟩ : syracuseStep 667445 = 62573) (by norm_num)
theorem B208705 : Blo 183802 208705 := bbase (se 2 (by rfl) ⟨78264, by rfl⟩ : syracuseStep 208705 = 156529) (by norm_num)
theorem B208741 : Blo 183802 208741 := bbase (se 4 (by rfl) ⟨19569, by rfl⟩ : syracuseStep 208741 = 39139) (by norm_num)
theorem B470893 : Blo 183802 470893 := bbase (se 3 (by rfl) ⟨88292, by rfl⟩ : syracuseStep 470893 = 176585) (by norm_num)
theorem B1781621 : Blo 183802 1781621 := bbase (se 5 (by rfl) ⟨83513, by rfl⟩ : syracuseStep 1781621 = 167027) (by norm_num)
theorem B208777 : Blo 183802 208777 := bbase (se 2 (by rfl) ⟨78291, by rfl⟩ : syracuseStep 208777 = 156583) (by norm_num)
theorem B208813 : Blo 183802 208813 := bbase (se 3 (by rfl) ⟨39152, by rfl⟩ : syracuseStep 208813 = 78305) (by norm_num)
theorem B208849 : Blo 183802 208849 := bbase (se 2 (by rfl) ⟨78318, by rfl⟩ : syracuseStep 208849 = 156637) (by norm_num)
theorem B471005 : Blo 183802 471005 := bbase (se 3 (by rfl) ⟨88313, by rfl⟩ : syracuseStep 471005 = 176627) (by norm_num)
theorem B208885 : Blo 183802 208885 := bbase (se 5 (by rfl) ⟨9791, by rfl⟩ : syracuseStep 208885 = 19583) (by norm_num)
theorem B208921 : Blo 183802 208921 := bbase (se 2 (by rfl) ⟨78345, by rfl⟩ : syracuseStep 208921 = 156691) (by norm_num)
theorem B208957 : Blo 183802 208957 := bbase (se 3 (by rfl) ⟨39179, by rfl⟩ : syracuseStep 208957 = 78359) (by norm_num)
theorem B634949 : Blo 183802 634949 := bbase (se 4 (by rfl) ⟨59526, by rfl⟩ : syracuseStep 634949 = 119053) (by norm_num)
theorem B208993 : Blo 183802 208993 := bbase (se 2 (by rfl) ⟨78372, by rfl⟩ : syracuseStep 208993 = 156745) (by norm_num)
theorem B209029 : Blo 183802 209029 := bbase (se 4 (by rfl) ⟨19596, by rfl⟩ : syracuseStep 209029 = 39193) (by norm_num)
theorem B471197 : Blo 183802 471197 := bbase (se 3 (by rfl) ⟨88349, by rfl⟩ : syracuseStep 471197 = 176699) (by norm_num)
theorem B209065 : Blo 183802 209065 := bbase (se 2 (by rfl) ⟨78399, by rfl⟩ : syracuseStep 209065 = 156799) (by norm_num)
theorem B209101 : Blo 183802 209101 := bbase (se 3 (by rfl) ⟨39206, by rfl⟩ : syracuseStep 209101 = 78413) (by norm_num)
theorem B209137 : Blo 183802 209137 := bbase (se 2 (by rfl) ⟨78426, by rfl⟩ : syracuseStep 209137 = 156853) (by norm_num)
theorem B209173 : Blo 183802 209173 := bbase (se 6 (by rfl) ⟨4902, by rfl⟩ : syracuseStep 209173 = 9805) (by norm_num)
theorem B209209 : Blo 183802 209209 := bbase (se 2 (by rfl) ⟨78453, by rfl⟩ : syracuseStep 209209 = 156907) (by norm_num)
theorem B209245 : Blo 183802 209245 := bbase (se 3 (by rfl) ⟨39233, by rfl⟩ : syracuseStep 209245 = 78467) (by norm_num)
theorem B209281 : Blo 183802 209281 := bbase (se 2 (by rfl) ⟨78480, by rfl⟩ : syracuseStep 209281 = 156961) (by norm_num)
theorem B209317 : Blo 183802 209317 := bbase (se 4 (by rfl) ⟨19623, by rfl⟩ : syracuseStep 209317 = 39247) (by norm_num)
theorem B209353 : Blo 183802 209353 := bbase (se 2 (by rfl) ⟨78507, by rfl⟩ : syracuseStep 209353 = 157015) (by norm_num)
theorem B1061333 : Blo 183802 1061333 := bbase (se 7 (by rfl) ⟨12437, by rfl⟩ : syracuseStep 1061333 = 24875) (by norm_num)
theorem B209389 : Blo 183802 209389 := bbase (se 3 (by rfl) ⟨39260, by rfl⟩ : syracuseStep 209389 = 78521) (by norm_num)
theorem B471541 : Blo 183802 471541 := bbase (se 5 (by rfl) ⟨22103, by rfl⟩ : syracuseStep 471541 = 44207) (by norm_num)
theorem B700933 : Blo 183802 700933 := bbase (se 4 (by rfl) ⟨65712, by rfl⟩ : syracuseStep 700933 = 131425) (by norm_num)
theorem B209425 : Blo 183802 209425 := bbase (se 2 (by rfl) ⟨78534, by rfl⟩ : syracuseStep 209425 = 157069) (by norm_num)
theorem B209461 : Blo 183802 209461 := bbase (se 5 (by rfl) ⟨9818, by rfl⟩ : syracuseStep 209461 = 19637) (by norm_num)
theorem B209497 : Blo 183802 209497 := bbase (se 2 (by rfl) ⟨78561, by rfl⟩ : syracuseStep 209497 = 157123) (by norm_num)
theorem B471653 : Blo 183802 471653 := bbase (se 4 (by rfl) ⟨44217, by rfl⟩ : syracuseStep 471653 = 88435) (by norm_num)
theorem B209533 : Blo 183802 209533 := bbase (se 3 (by rfl) ⟨39287, by rfl⟩ : syracuseStep 209533 = 78575) (by norm_num)
theorem B209569 : Blo 183802 209569 := bbase (se 2 (by rfl) ⟨78588, by rfl⟩ : syracuseStep 209569 = 157177) (by norm_num)
theorem B209605 : Blo 183802 209605 := bbase (se 4 (by rfl) ⟨19650, by rfl⟩ : syracuseStep 209605 = 39301) (by norm_num)
theorem B209641 : Blo 183802 209641 := bbase (se 2 (by rfl) ⟨78615, by rfl⟩ : syracuseStep 209641 = 157231) (by norm_num)
theorem B209677 : Blo 183802 209677 := bbase (se 3 (by rfl) ⟨39314, by rfl⟩ : syracuseStep 209677 = 78629) (by norm_num)
theorem B471845 : Blo 183802 471845 := bbase (se 4 (by rfl) ⟨44235, by rfl⟩ : syracuseStep 471845 = 88471) (by norm_num)
theorem B209713 : Blo 183802 209713 := bbase (se 2 (by rfl) ⟨78642, by rfl⟩ : syracuseStep 209713 = 157285) (by norm_num)
theorem B701237 : Blo 183802 701237 := bbase (se 5 (by rfl) ⟨32870, by rfl⟩ : syracuseStep 701237 = 65741) (by norm_num)
theorem B340805 : Blo 183802 340805 := bbase (se 4 (by rfl) ⟨31950, by rfl⟩ : syracuseStep 340805 = 63901) (by norm_num)
theorem B209749 : Blo 183802 209749 := bbase (se 9 (by rfl) ⟨614, by rfl⟩ : syracuseStep 209749 = 1229) (by norm_num)
theorem B209785 : Blo 183802 209785 := bbase (se 2 (by rfl) ⟨78669, by rfl⟩ : syracuseStep 209785 = 157339) (by norm_num)
theorem B471941 : Blo 183802 471941 := bbase (se 4 (by rfl) ⟨44244, by rfl⟩ : syracuseStep 471941 = 88489) (by norm_num)
theorem B209821 : Blo 183802 209821 := bbase (se 3 (by rfl) ⟨39341, by rfl⟩ : syracuseStep 209821 = 78683) (by norm_num)
theorem B209857 : Blo 183802 209857 := bbase (se 2 (by rfl) ⟨78696, by rfl⟩ : syracuseStep 209857 = 157393) (by norm_num)
theorem B209893 : Blo 183802 209893 := bbase (se 4 (by rfl) ⟨19677, by rfl⟩ : syracuseStep 209893 = 39355) (by norm_num)
theorem B209929 : Blo 183802 209929 := bbase (se 2 (by rfl) ⟨78723, by rfl⟩ : syracuseStep 209929 = 157447) (by norm_num)
theorem B766997 : Blo 183802 766997 := bbase (se 6 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 766997 = 35953) (by norm_num)
theorem B209965 : Blo 183802 209965 := bbase (se 3 (by rfl) ⟨39368, by rfl⟩ : syracuseStep 209965 = 78737) (by norm_num)
theorem B210001 : Blo 183802 210001 := bbase (se 2 (by rfl) ⟨78750, by rfl⟩ : syracuseStep 210001 = 157501) (by norm_num)
theorem B210037 : Blo 183802 210037 := bbase (se 5 (by rfl) ⟨9845, by rfl⟩ : syracuseStep 210037 = 19691) (by norm_num)
theorem B472189 : Blo 183802 472189 := bbase (se 3 (by rfl) ⟨88535, by rfl⟩ : syracuseStep 472189 = 177071) (by norm_num)
theorem B210073 : Blo 183802 210073 := bbase (se 2 (by rfl) ⟨78777, by rfl⟩ : syracuseStep 210073 = 157555) (by norm_num)
theorem B210109 : Blo 183802 210109 := bbase (se 3 (by rfl) ⟨39395, by rfl⟩ : syracuseStep 210109 = 78791) (by norm_num)
theorem B931013 : Blo 183802 931013 := bbase (se 4 (by rfl) ⟨87282, by rfl⟩ : syracuseStep 931013 = 174565) (by norm_num)
theorem B210145 : Blo 183802 210145 := bbase (se 2 (by rfl) ⟨78804, by rfl⟩ : syracuseStep 210145 = 157609) (by norm_num)
theorem B472301 : Blo 183802 472301 := bbase (se 3 (by rfl) ⟨88556, by rfl⟩ : syracuseStep 472301 = 177113) (by norm_num)
theorem B275717 : Blo 183802 275717 := bbase (se 4 (by rfl) ⟨25848, by rfl⟩ : syracuseStep 275717 = 51697) (by norm_num)
theorem B210181 : Blo 183802 210181 := bbase (se 4 (by rfl) ⟨19704, by rfl⟩ : syracuseStep 210181 = 39409) (by norm_num)
theorem B275741 : Blo 183802 275741 := bbase (se 3 (by rfl) ⟨51701, by rfl⟩ : syracuseStep 275741 = 103403) (by norm_num)
theorem B210217 : Blo 183802 210217 := bbase (se 2 (by rfl) ⟨78831, by rfl⟩ : syracuseStep 210217 = 157663) (by norm_num)
theorem B275765 : Blo 183802 275765 := bbase (se 5 (by rfl) ⟨12926, by rfl⟩ : syracuseStep 275765 = 25853) (by norm_num)
theorem B210253 : Blo 183802 210253 := bbase (se 3 (by rfl) ⟨39422, by rfl⟩ : syracuseStep 210253 = 78845) (by norm_num)
theorem B275789 : Blo 183802 275789 := bbase (se 3 (by rfl) ⟨51710, by rfl⟩ : syracuseStep 275789 = 103421) (by norm_num)
theorem B275813 : Blo 183802 275813 := bbase (se 4 (by rfl) ⟨25857, by rfl⟩ : syracuseStep 275813 = 51715) (by norm_num)
theorem B210289 : Blo 183802 210289 := bbase (se 2 (by rfl) ⟨78858, by rfl⟩ : syracuseStep 210289 = 157717) (by norm_num)
theorem B275837 : Blo 183802 275837 := bbase (se 3 (by rfl) ⟨51719, by rfl⟩ : syracuseStep 275837 = 103439) (by norm_num)
theorem B275861 : Blo 183802 275861 := bbase (se 6 (by rfl) ⟨6465, by rfl⟩ : syracuseStep 275861 = 12931) (by norm_num)
theorem B210325 : Blo 183802 210325 := bbase (se 6 (by rfl) ⟨4929, by rfl⟩ : syracuseStep 210325 = 9859) (by norm_num)
theorem B570773 : Blo 183802 570773 := bbase (se 6 (by rfl) ⟨13377, by rfl⟩ : syracuseStep 570773 = 26755) (by norm_num)
theorem B275885 : Blo 183802 275885 := bbase (se 3 (by rfl) ⟨51728, by rfl⟩ : syracuseStep 275885 = 103457) (by norm_num)
theorem B472493 : Blo 183802 472493 := bbase (se 3 (by rfl) ⟨88592, by rfl⟩ : syracuseStep 472493 = 177185) (by norm_num)
theorem B210361 : Blo 183802 210361 := bbase (se 2 (by rfl) ⟨78885, by rfl⟩ : syracuseStep 210361 = 157771) (by norm_num)
theorem B275909 : Blo 183802 275909 := bbase (se 4 (by rfl) ⟨25866, by rfl⟩ : syracuseStep 275909 = 51733) (by norm_num)
theorem B275933 : Blo 183802 275933 := bbase (se 3 (by rfl) ⟨51737, by rfl⟩ : syracuseStep 275933 = 103475) (by norm_num)
theorem B210397 : Blo 183802 210397 := bbase (se 3 (by rfl) ⟨39449, by rfl⟩ : syracuseStep 210397 = 78899) (by norm_num)
theorem B275957 : Blo 183802 275957 := bbase (se 5 (by rfl) ⟨12935, by rfl⟩ : syracuseStep 275957 = 25871) (by norm_num)
theorem B210433 : Blo 183802 210433 := bbase (se 2 (by rfl) ⟨78912, by rfl⟩ : syracuseStep 210433 = 157825) (by norm_num)
theorem B275981 : Blo 183802 275981 := bbase (se 3 (by rfl) ⟨51746, by rfl⟩ : syracuseStep 275981 = 103493) (by norm_num)
theorem B276005 : Blo 183802 276005 := bbase (se 4 (by rfl) ⟨25875, by rfl⟩ : syracuseStep 276005 = 51751) (by norm_num)
theorem B210469 : Blo 183802 210469 := bbase (se 4 (by rfl) ⟨19731, by rfl⟩ : syracuseStep 210469 = 39463) (by norm_num)
theorem B276029 : Blo 183802 276029 := bbase (se 3 (by rfl) ⟨51755, by rfl⟩ : syracuseStep 276029 = 103511) (by norm_num)
theorem B210505 : Blo 183802 210505 := bbase (se 2 (by rfl) ⟨78939, by rfl⟩ : syracuseStep 210505 = 157879) (by norm_num)
theorem B276053 : Blo 183802 276053 := bbase (se 8 (by rfl) ⟨1617, by rfl⟩ : syracuseStep 276053 = 3235) (by norm_num)
theorem B276077 : Blo 183802 276077 := bbase (se 3 (by rfl) ⟨51764, by rfl⟩ : syracuseStep 276077 = 103529) (by norm_num)
theorem B210541 : Blo 183802 210541 := bbase (se 3 (by rfl) ⟨39476, by rfl⟩ : syracuseStep 210541 = 78953) (by norm_num)
theorem B1062517 : Blo 183802 1062517 := bbase (se 5 (by rfl) ⟨49805, by rfl⟩ : syracuseStep 1062517 = 99611) (by norm_num)
theorem B276101 : Blo 183802 276101 := bbase (se 4 (by rfl) ⟨25884, by rfl⟩ : syracuseStep 276101 = 51769) (by norm_num)
theorem B210577 : Blo 183802 210577 := bbase (se 2 (by rfl) ⟨78966, by rfl⟩ : syracuseStep 210577 = 157933) (by norm_num)
theorem B505493 : Blo 183802 505493 := bbase (se 6 (by rfl) ⟨11847, by rfl⟩ : syracuseStep 505493 = 23695) (by norm_num)
theorem B276125 : Blo 183802 276125 := bbase (se 3 (by rfl) ⟨51773, by rfl⟩ : syracuseStep 276125 = 103547) (by norm_num)
theorem B276149 : Blo 183802 276149 := bbase (se 5 (by rfl) ⟨12944, by rfl⟩ : syracuseStep 276149 = 25889) (by norm_num)
theorem B210613 : Blo 183802 210613 := bbase (se 5 (by rfl) ⟨9872, by rfl⟩ : syracuseStep 210613 = 19745) (by norm_num)
theorem B276173 : Blo 183802 276173 := bbase (se 3 (by rfl) ⟨51782, by rfl⟩ : syracuseStep 276173 = 103565) (by norm_num)
theorem B210649 : Blo 183802 210649 := bbase (se 2 (by rfl) ⟨78993, by rfl⟩ : syracuseStep 210649 = 157987) (by norm_num)
theorem B276197 : Blo 183802 276197 := bbase (se 4 (by rfl) ⟨25893, by rfl⟩ : syracuseStep 276197 = 51787) (by norm_num)
theorem B898789 : Blo 183802 898789 := bbase (se 4 (by rfl) ⟨84261, by rfl⟩ : syracuseStep 898789 = 168523) (by norm_num)
theorem B341741 : Blo 183802 341741 := bbase (se 3 (by rfl) ⟨64076, by rfl⟩ : syracuseStep 341741 = 128153) (by norm_num)
theorem B276221 : Blo 183802 276221 := bbase (se 3 (by rfl) ⟨51791, by rfl⟩ : syracuseStep 276221 = 103583) (by norm_num)
theorem B210685 : Blo 183802 210685 := bbase (se 3 (by rfl) ⟨39503, by rfl⟩ : syracuseStep 210685 = 79007) (by norm_num)
theorem B472837 : Blo 183802 472837 := bbase (se 4 (by rfl) ⟨44328, by rfl⟩ : syracuseStep 472837 = 88657) (by norm_num)
theorem B276245 : Blo 183802 276245 := bbase (se 6 (by rfl) ⟨6474, by rfl⟩ : syracuseStep 276245 = 12949) (by norm_num)
theorem B210721 : Blo 183802 210721 := bbase (se 2 (by rfl) ⟨79020, by rfl⟩ : syracuseStep 210721 = 158041) (by norm_num)
theorem B276269 : Blo 183802 276269 := bbase (se 3 (by rfl) ⟨51800, by rfl⟩ : syracuseStep 276269 = 103601) (by norm_num)
theorem B276293 : Blo 183802 276293 := bbase (se 4 (by rfl) ⟨25902, by rfl⟩ : syracuseStep 276293 = 51805) (by norm_num)
theorem B210757 : Blo 183802 210757 := bbase (se 4 (by rfl) ⟨19758, by rfl⟩ : syracuseStep 210757 = 39517) (by norm_num)
theorem B505685 : Blo 183802 505685 := bbase (se 9 (by rfl) ⟨1481, by rfl⟩ : syracuseStep 505685 = 2963) (by norm_num)
theorem B276317 : Blo 183802 276317 := bbase (se 3 (by rfl) ⟨51809, by rfl⟩ : syracuseStep 276317 = 103619) (by norm_num)
theorem B210793 : Blo 183802 210793 := bbase (se 2 (by rfl) ⟨79047, by rfl⟩ : syracuseStep 210793 = 158095) (by norm_num)
theorem B276341 : Blo 183802 276341 := bbase (se 5 (by rfl) ⟨12953, by rfl⟩ : syracuseStep 276341 = 25907) (by norm_num)
theorem B472949 : Blo 183802 472949 := bbase (se 5 (by rfl) ⟨22169, by rfl⟩ : syracuseStep 472949 = 44339) (by norm_num)
theorem B276365 : Blo 183802 276365 := bbase (se 3 (by rfl) ⟨51818, by rfl⟩ : syracuseStep 276365 = 103637) (by norm_num)
theorem B210829 : Blo 183802 210829 := bbase (se 3 (by rfl) ⟨39530, by rfl⟩ : syracuseStep 210829 = 79061) (by norm_num)
theorem B276389 : Blo 183802 276389 := bbase (se 4 (by rfl) ⟨25911, by rfl⟩ : syracuseStep 276389 = 51823) (by norm_num)
theorem B210865 : Blo 183802 210865 := bbase (se 2 (by rfl) ⟨79074, by rfl⟩ : syracuseStep 210865 = 158149) (by norm_num)
theorem B276413 : Blo 183802 276413 := bbase (se 3 (by rfl) ⟨51827, by rfl⟩ : syracuseStep 276413 = 103655) (by norm_num)
theorem B276437 : Blo 183802 276437 := bbase (se 7 (by rfl) ⟨3239, by rfl⟩ : syracuseStep 276437 = 6479) (by norm_num)
theorem B210901 : Blo 183802 210901 := bbase (se 7 (by rfl) ⟨2471, by rfl⟩ : syracuseStep 210901 = 4943) (by norm_num)
theorem B276461 : Blo 183802 276461 := bbase (se 3 (by rfl) ⟨51836, by rfl⟩ : syracuseStep 276461 = 103673) (by norm_num)
theorem B210937 : Blo 183802 210937 := bbase (se 2 (by rfl) ⟨79101, by rfl⟩ : syracuseStep 210937 = 158203) (by norm_num)
theorem B276485 : Blo 183802 276485 := bbase (se 4 (by rfl) ⟨25920, by rfl⟩ : syracuseStep 276485 = 51841) (by norm_num)
theorem B276509 : Blo 183802 276509 := bbase (se 3 (by rfl) ⟨51845, by rfl⟩ : syracuseStep 276509 = 103691) (by norm_num)
theorem B210973 : Blo 183802 210973 := bbase (se 3 (by rfl) ⟨39557, by rfl⟩ : syracuseStep 210973 = 79115) (by norm_num)
theorem B276533 : Blo 183802 276533 := bbase (se 5 (by rfl) ⟨12962, by rfl⟩ : syracuseStep 276533 = 25925) (by norm_num)
theorem B473141 : Blo 183802 473141 := bbase (se 5 (by rfl) ⟨22178, by rfl⟩ : syracuseStep 473141 = 44357) (by norm_num)
theorem B211009 : Blo 183802 211009 := bbase (se 2 (by rfl) ⟨79128, by rfl⟩ : syracuseStep 211009 = 158257) (by norm_num)
theorem B800837 : Blo 183802 800837 := bbase (se 4 (by rfl) ⟨75078, by rfl⟩ : syracuseStep 800837 = 150157) (by norm_num)
theorem B276557 : Blo 183802 276557 := bbase (se 3 (by rfl) ⟨51854, by rfl⟩ : syracuseStep 276557 = 103709) (by norm_num)
theorem B276581 : Blo 183802 276581 := bbase (se 4 (by rfl) ⟨25929, by rfl⟩ : syracuseStep 276581 = 51859) (by norm_num)
theorem B211045 : Blo 183802 211045 := bbase (se 4 (by rfl) ⟨19785, by rfl⟩ : syracuseStep 211045 = 39571) (by norm_num)
theorem B276605 : Blo 183802 276605 := bbase (se 3 (by rfl) ⟨51863, by rfl⟩ : syracuseStep 276605 = 103727) (by norm_num)
theorem B211081 : Blo 183802 211081 := bbase (se 2 (by rfl) ⟨79155, by rfl⟩ : syracuseStep 211081 = 158311) (by norm_num)
theorem B276629 : Blo 183802 276629 := bbase (se 6 (by rfl) ⟨6483, by rfl⟩ : syracuseStep 276629 = 12967) (by norm_num)
theorem B276653 : Blo 183802 276653 := bbase (se 3 (by rfl) ⟨51872, by rfl⟩ : syracuseStep 276653 = 103745) (by norm_num)
theorem B211117 : Blo 183802 211117 := bbase (se 3 (by rfl) ⟨39584, by rfl⟩ : syracuseStep 211117 = 79169) (by norm_num)
theorem B276677 : Blo 183802 276677 := bbase (se 4 (by rfl) ⟨25938, by rfl⟩ : syracuseStep 276677 = 51877) (by norm_num)
theorem B211153 : Blo 183802 211153 := bbase (se 2 (by rfl) ⟨79182, by rfl⟩ : syracuseStep 211153 = 158365) (by norm_num)
theorem B276701 : Blo 183802 276701 := bbase (se 3 (by rfl) ⟨51881, by rfl⟩ : syracuseStep 276701 = 103763) (by norm_num)
theorem B276725 : Blo 183802 276725 := bbase (se 5 (by rfl) ⟨12971, by rfl⟩ : syracuseStep 276725 = 25943) (by norm_num)
theorem B669941 : Blo 183802 669941 := bbase (se 5 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 669941 = 62807) (by norm_num)
theorem B211189 : Blo 183802 211189 := bbase (se 5 (by rfl) ⟨9899, by rfl⟩ : syracuseStep 211189 = 19799) (by norm_num)
theorem B276749 : Blo 183802 276749 := bbase (se 3 (by rfl) ⟨51890, by rfl⟩ : syracuseStep 276749 = 103781) (by norm_num)
theorem B211225 : Blo 183802 211225 := bbase (se 2 (by rfl) ⟨79209, by rfl⟩ : syracuseStep 211225 = 158419) (by norm_num)
theorem B276773 : Blo 183802 276773 := bbase (se 4 (by rfl) ⟨25947, by rfl⟩ : syracuseStep 276773 = 51895) (by norm_num)
theorem B899381 : Blo 183802 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B276797 : Blo 183802 276797 := bbase (se 3 (by rfl) ⟨51899, by rfl⟩ : syracuseStep 276797 = 103799) (by norm_num)
theorem B211261 : Blo 183802 211261 := bbase (se 3 (by rfl) ⟨39611, by rfl⟩ : syracuseStep 211261 = 79223) (by norm_num)
theorem B276821 : Blo 183802 276821 := bbase (se 10 (by rfl) ⟨405, by rfl⟩ : syracuseStep 276821 = 811) (by norm_num)
theorem B276845 : Blo 183802 276845 := bbase (se 3 (by rfl) ⟨51908, by rfl⟩ : syracuseStep 276845 = 103817) (by norm_num)
theorem B276869 : Blo 183802 276869 := bbase (se 4 (by rfl) ⟨25956, by rfl⟩ : syracuseStep 276869 = 51913) (by norm_num)
theorem B473485 : Blo 183802 473485 := bbase (se 3 (by rfl) ⟨88778, by rfl⟩ : syracuseStep 473485 = 177557) (by norm_num)
theorem B276893 : Blo 183802 276893 := bbase (se 3 (by rfl) ⟨51917, by rfl⟩ : syracuseStep 276893 = 103835) (by norm_num)
theorem B276917 : Blo 183802 276917 := bbase (se 5 (by rfl) ⟨12980, by rfl⟩ : syracuseStep 276917 = 25961) (by norm_num)
theorem B276941 : Blo 183802 276941 := bbase (se 3 (by rfl) ⟨51926, by rfl⟩ : syracuseStep 276941 = 103853) (by norm_num)
theorem B932309 : Blo 183802 932309 := bbase (se 7 (by rfl) ⟨10925, by rfl⟩ : syracuseStep 932309 = 21851) (by norm_num)
theorem B276965 : Blo 183802 276965 := bbase (se 4 (by rfl) ⟨25965, by rfl⟩ : syracuseStep 276965 = 51931) (by norm_num)
theorem B506341 : Blo 183802 506341 := bbase (se 4 (by rfl) ⟨47469, by rfl⟩ : syracuseStep 506341 = 94939) (by norm_num)
theorem B276989 : Blo 183802 276989 := bbase (se 3 (by rfl) ⟨51935, by rfl⟩ : syracuseStep 276989 = 103871) (by norm_num)
theorem B375293 : Blo 183802 375293 := bbase (se 3 (by rfl) ⟨70367, by rfl⟩ : syracuseStep 375293 = 140735) (by norm_num)
theorem B473597 : Blo 183802 473597 := bbase (se 3 (by rfl) ⟨88799, by rfl⟩ : syracuseStep 473597 = 177599) (by norm_num)
theorem B277013 : Blo 183802 277013 := bbase (se 6 (by rfl) ⟨6492, by rfl⟩ : syracuseStep 277013 = 12985) (by norm_num)
theorem B277037 : Blo 183802 277037 := bbase (se 3 (by rfl) ⟨51944, by rfl⟩ : syracuseStep 277037 = 103889) (by norm_num)
theorem B277061 : Blo 183802 277061 := bbase (se 4 (by rfl) ⟨25974, by rfl⟩ : syracuseStep 277061 = 51949) (by norm_num)
theorem B277085 : Blo 183802 277085 := bbase (se 3 (by rfl) ⟨51953, by rfl⟩ : syracuseStep 277085 = 103907) (by norm_num)
theorem B277109 : Blo 183802 277109 := bbase (se 5 (by rfl) ⟨12989, by rfl⟩ : syracuseStep 277109 = 25979) (by norm_num)
theorem B211577 : Blo 183802 211577 := bbase (se 2 (by rfl) ⟨79341, by rfl⟩ : syracuseStep 211577 = 158683) (by norm_num)
theorem B277133 : Blo 183802 277133 := bbase (se 3 (by rfl) ⟨51962, by rfl⟩ : syracuseStep 277133 = 103925) (by norm_num)
theorem B277157 : Blo 183802 277157 := bbase (se 4 (by rfl) ⟨25983, by rfl⟩ : syracuseStep 277157 = 51967) (by norm_num)
theorem B277181 : Blo 183802 277181 := bbase (se 3 (by rfl) ⟨51971, by rfl⟩ : syracuseStep 277181 = 103943) (by norm_num)
theorem B473789 : Blo 183802 473789 := bbase (se 3 (by rfl) ⟨88835, by rfl⟩ : syracuseStep 473789 = 177671) (by norm_num)
theorem B277205 : Blo 183802 277205 := bbase (se 7 (by rfl) ⟨3248, by rfl⟩ : syracuseStep 277205 = 6497) (by norm_num)
theorem B277229 : Blo 183802 277229 := bbase (se 3 (by rfl) ⟨51980, by rfl⟩ : syracuseStep 277229 = 103961) (by norm_num)
theorem B277253 : Blo 183802 277253 := bbase (se 4 (by rfl) ⟨25992, by rfl⟩ : syracuseStep 277253 = 51985) (by norm_num)
theorem B277277 : Blo 183802 277277 := bbase (se 3 (by rfl) ⟨51989, by rfl⟩ : syracuseStep 277277 = 103979) (by norm_num)
theorem B277301 : Blo 183802 277301 := bbase (se 5 (by rfl) ⟨12998, by rfl⟩ : syracuseStep 277301 = 25997) (by norm_num)
theorem B277325 : Blo 183802 277325 := bbase (se 3 (by rfl) ⟨51998, by rfl⟩ : syracuseStep 277325 = 103997) (by norm_num)
theorem B277349 : Blo 183802 277349 := bbase (se 4 (by rfl) ⟨26001, by rfl⟩ : syracuseStep 277349 = 52003) (by norm_num)
theorem B703349 : Blo 183802 703349 := bbase (se 5 (by rfl) ⟨32969, by rfl⟩ : syracuseStep 703349 = 65939) (by norm_num)
theorem B277373 : Blo 183802 277373 := bbase (se 3 (by rfl) ⟨52007, by rfl⟩ : syracuseStep 277373 = 104015) (by norm_num)
theorem B277397 : Blo 183802 277397 := bbase (se 6 (by rfl) ⟨6501, by rfl⟩ : syracuseStep 277397 = 13003) (by norm_num)
theorem B310189 : Blo 183802 310189 := bbase (se 3 (by rfl) ⟨58160, by rfl⟩ : syracuseStep 310189 = 116321) (by norm_num)
theorem B277421 : Blo 183802 277421 := bbase (se 3 (by rfl) ⟨52016, by rfl⟩ : syracuseStep 277421 = 104033) (by norm_num)
theorem B277445 : Blo 183802 277445 := bbase (se 4 (by rfl) ⟨26010, by rfl⟩ : syracuseStep 277445 = 52021) (by norm_num)
theorem B277469 : Blo 183802 277469 := bbase (se 3 (by rfl) ⟨52025, by rfl⟩ : syracuseStep 277469 = 104051) (by norm_num)
theorem B277493 : Blo 183802 277493 := bbase (se 5 (by rfl) ⟨13007, by rfl⟩ : syracuseStep 277493 = 26015) (by norm_num)
theorem B310277 : Blo 183802 310277 := bbase (se 4 (by rfl) ⟨29088, by rfl⟩ : syracuseStep 310277 = 58177) (by norm_num)
theorem B277517 : Blo 183802 277517 := bbase (se 3 (by rfl) ⟨52034, by rfl⟩ : syracuseStep 277517 = 104069) (by norm_num)
theorem B474133 : Blo 183802 474133 := bbase (se 6 (by rfl) ⟨11112, by rfl⟩ : syracuseStep 474133 = 22225) (by norm_num)
theorem B277541 : Blo 183802 277541 := bbase (se 4 (by rfl) ⟨26019, by rfl⟩ : syracuseStep 277541 = 52039) (by norm_num)
theorem B801845 : Blo 183802 801845 := bbase (se 5 (by rfl) ⟨37586, by rfl⟩ : syracuseStep 801845 = 75173) (by norm_num)
theorem B277565 : Blo 183802 277565 := bbase (se 3 (by rfl) ⟨52043, by rfl⟩ : syracuseStep 277565 = 104087) (by norm_num)
theorem B277589 : Blo 183802 277589 := bbase (se 8 (by rfl) ⟨1626, by rfl⟩ : syracuseStep 277589 = 3253) (by norm_num)
theorem B277613 : Blo 183802 277613 := bbase (se 3 (by rfl) ⟨52052, by rfl⟩ : syracuseStep 277613 = 104105) (by norm_num)
theorem B310405 : Blo 183802 310405 := bbase (se 4 (by rfl) ⟨29100, by rfl⟩ : syracuseStep 310405 = 58201) (by norm_num)
theorem B277637 : Blo 183802 277637 := bbase (se 4 (by rfl) ⟨26028, by rfl⟩ : syracuseStep 277637 = 52057) (by norm_num)
theorem B474245 : Blo 183802 474245 := bbase (se 4 (by rfl) ⟨44460, by rfl⟩ : syracuseStep 474245 = 88921) (by norm_num)
theorem B703637 : Blo 183802 703637 := bbase (se 6 (by rfl) ⟨16491, by rfl⟩ : syracuseStep 703637 = 32983) (by norm_num)
theorem B277661 : Blo 183802 277661 := bbase (se 3 (by rfl) ⟨52061, by rfl⟩ : syracuseStep 277661 = 104123) (by norm_num)
theorem B277685 : Blo 183802 277685 := bbase (se 5 (by rfl) ⟨13016, by rfl⟩ : syracuseStep 277685 = 26033) (by norm_num)
theorem B277709 : Blo 183802 277709 := bbase (se 3 (by rfl) ⟨52070, by rfl⟩ : syracuseStep 277709 = 104141) (by norm_num)
theorem B310493 : Blo 183802 310493 := bbase (se 3 (by rfl) ⟨58217, by rfl⟩ : syracuseStep 310493 = 116435) (by norm_num)
theorem B277733 : Blo 183802 277733 := bbase (se 4 (by rfl) ⟨26037, by rfl⟩ : syracuseStep 277733 = 52075) (by norm_num)
theorem B277757 : Blo 183802 277757 := bbase (se 3 (by rfl) ⟨52079, by rfl⟩ : syracuseStep 277757 = 104159) (by norm_num)
theorem B277781 : Blo 183802 277781 := bbase (se 6 (by rfl) ⟨6510, by rfl⟩ : syracuseStep 277781 = 13021) (by norm_num)
theorem B1359125 : Blo 183802 1359125 := bbase (se 6 (by rfl) ⟨31854, by rfl⟩ : syracuseStep 1359125 = 63709) (by norm_num)
theorem B277805 : Blo 183802 277805 := bbase (se 3 (by rfl) ⟨52088, by rfl⟩ : syracuseStep 277805 = 104177) (by norm_num)
theorem B277829 : Blo 183802 277829 := bbase (se 4 (by rfl) ⟨26046, by rfl⟩ : syracuseStep 277829 = 52093) (by norm_num)
theorem B474437 : Blo 183802 474437 := bbase (se 4 (by rfl) ⟨44478, by rfl⟩ : syracuseStep 474437 = 88957) (by norm_num)
theorem B310621 : Blo 183802 310621 := bbase (se 3 (by rfl) ⟨58241, by rfl⟩ : syracuseStep 310621 = 116483) (by norm_num)
theorem B277853 : Blo 183802 277853 := bbase (se 3 (by rfl) ⟨52097, by rfl⟩ : syracuseStep 277853 = 104195) (by norm_num)
theorem B277877 : Blo 183802 277877 := bbase (se 5 (by rfl) ⟨13025, by rfl⟩ : syracuseStep 277877 = 26051) (by norm_num)
theorem B277901 : Blo 183802 277901 := bbase (se 3 (by rfl) ⟨52106, by rfl⟩ : syracuseStep 277901 = 104213) (by norm_num)
theorem B277925 : Blo 183802 277925 := bbase (se 4 (by rfl) ⟨26055, by rfl⟩ : syracuseStep 277925 = 52111) (by norm_num)
theorem B310709 : Blo 183802 310709 := bbase (se 5 (by rfl) ⟨14564, by rfl⟩ : syracuseStep 310709 = 29129) (by norm_num)
theorem B277949 : Blo 183802 277949 := bbase (se 3 (by rfl) ⟨52115, by rfl⟩ : syracuseStep 277949 = 104231) (by norm_num)
theorem B277973 : Blo 183802 277973 := bbase (se 7 (by rfl) ⟨3257, by rfl⟩ : syracuseStep 277973 = 6515) (by norm_num)
theorem B277997 : Blo 183802 277997 := bbase (se 3 (by rfl) ⟨52124, by rfl⟩ : syracuseStep 277997 = 104249) (by norm_num)
theorem B278021 : Blo 183802 278021 := bbase (se 4 (by rfl) ⟨26064, by rfl⟩ : syracuseStep 278021 = 52129) (by norm_num)
theorem B278045 : Blo 183802 278045 := bbase (se 3 (by rfl) ⟨52133, by rfl⟩ : syracuseStep 278045 = 104267) (by norm_num)
theorem B310837 : Blo 183802 310837 := bbase (se 5 (by rfl) ⟨14570, by rfl⟩ : syracuseStep 310837 = 29141) (by norm_num)
theorem B278069 : Blo 183802 278069 := bbase (se 5 (by rfl) ⟨13034, by rfl⟩ : syracuseStep 278069 = 26069) (by norm_num)
theorem B1064501 : Blo 183802 1064501 := bbase (se 5 (by rfl) ⟨49898, by rfl⟩ : syracuseStep 1064501 = 99797) (by norm_num)
theorem B278093 : Blo 183802 278093 := bbase (se 3 (by rfl) ⟨52142, by rfl⟩ : syracuseStep 278093 = 104285) (by norm_num)
theorem B278117 : Blo 183802 278117 := bbase (se 4 (by rfl) ⟨26073, by rfl⟩ : syracuseStep 278117 = 52147) (by norm_num)
theorem B212581 : Blo 183802 212581 := bbase (se 4 (by rfl) ⟨19929, by rfl⟩ : syracuseStep 212581 = 39859) (by norm_num)
theorem B278141 : Blo 183802 278141 := bbase (se 3 (by rfl) ⟨52151, by rfl⟩ : syracuseStep 278141 = 104303) (by norm_num)
theorem B310925 : Blo 183802 310925 := bbase (se 3 (by rfl) ⟨58298, by rfl⟩ : syracuseStep 310925 = 116597) (by norm_num)
theorem B278165 : Blo 183802 278165 := bbase (se 6 (by rfl) ⟨6519, by rfl⟩ : syracuseStep 278165 = 13039) (by norm_num)
theorem B474781 : Blo 183802 474781 := bbase (se 3 (by rfl) ⟨89021, by rfl⟩ : syracuseStep 474781 = 178043) (by norm_num)
theorem B278189 : Blo 183802 278189 := bbase (se 3 (by rfl) ⟨52160, by rfl⟩ : syracuseStep 278189 = 104321) (by norm_num)
theorem B278213 : Blo 183802 278213 := bbase (se 4 (by rfl) ⟨26082, by rfl⟩ : syracuseStep 278213 = 52165) (by norm_num)
theorem B376525 : Blo 183802 376525 := bbase (se 3 (by rfl) ⟨70598, by rfl⟩ : syracuseStep 376525 = 141197) (by norm_num)
theorem B278237 : Blo 183802 278237 := bbase (se 3 (by rfl) ⟨52169, by rfl⟩ : syracuseStep 278237 = 104339) (by norm_num)
theorem B933605 : Blo 183802 933605 := bbase (se 4 (by rfl) ⟨87525, by rfl⟩ : syracuseStep 933605 = 175051) (by norm_num)
theorem B278261 : Blo 183802 278261 := bbase (se 5 (by rfl) ⟨13043, by rfl⟩ : syracuseStep 278261 = 26087) (by norm_num)
theorem B311053 : Blo 183802 311053 := bbase (se 3 (by rfl) ⟨58322, by rfl⟩ : syracuseStep 311053 = 116645) (by norm_num)
theorem B278285 : Blo 183802 278285 := bbase (se 3 (by rfl) ⟨52178, by rfl⟩ : syracuseStep 278285 = 104357) (by norm_num)
theorem B474893 : Blo 183802 474893 := bbase (se 3 (by rfl) ⟨89042, by rfl⟩ : syracuseStep 474893 = 178085) (by norm_num)
theorem B278309 : Blo 183802 278309 := bbase (se 4 (by rfl) ⟨26091, by rfl⟩ : syracuseStep 278309 = 52183) (by norm_num)
theorem B278333 : Blo 183802 278333 := bbase (se 3 (by rfl) ⟨52187, by rfl⟩ : syracuseStep 278333 = 104375) (by norm_num)
theorem B278357 : Blo 183802 278357 := bbase (se 9 (by rfl) ⟨815, by rfl⟩ : syracuseStep 278357 = 1631) (by norm_num)
theorem B311141 : Blo 183802 311141 := bbase (se 4 (by rfl) ⟨29169, by rfl⟩ : syracuseStep 311141 = 58339) (by norm_num)
theorem B278381 : Blo 183802 278381 := bbase (se 3 (by rfl) ⟨52196, by rfl⟩ : syracuseStep 278381 = 104393) (by norm_num)
theorem B278405 : Blo 183802 278405 := bbase (se 4 (by rfl) ⟨26100, by rfl⟩ : syracuseStep 278405 = 52201) (by norm_num)
theorem B278429 : Blo 183802 278429 := bbase (se 3 (by rfl) ⟨52205, by rfl⟩ : syracuseStep 278429 = 104411) (by norm_num)
theorem B278453 : Blo 183802 278453 := bbase (se 5 (by rfl) ⟨13052, by rfl⟩ : syracuseStep 278453 = 26105) (by norm_num)
theorem B278477 : Blo 183802 278477 := bbase (se 3 (by rfl) ⟨52214, by rfl⟩ : syracuseStep 278477 = 104429) (by norm_num)
theorem B475085 : Blo 183802 475085 := bbase (se 3 (by rfl) ⟨89078, by rfl⟩ : syracuseStep 475085 = 178157) (by norm_num)
theorem B311269 : Blo 183802 311269 := bbase (se 4 (by rfl) ⟨29181, by rfl⟩ : syracuseStep 311269 = 58363) (by norm_num)
theorem B278501 : Blo 183802 278501 := bbase (se 4 (by rfl) ⟨26109, by rfl⟩ : syracuseStep 278501 = 52219) (by norm_num)
theorem B278525 : Blo 183802 278525 := bbase (se 3 (by rfl) ⟨52223, by rfl⟩ : syracuseStep 278525 = 104447) (by norm_num)
theorem B278549 : Blo 183802 278549 := bbase (se 6 (by rfl) ⟨6528, by rfl⟩ : syracuseStep 278549 = 13057) (by norm_num)
theorem B278573 : Blo 183802 278573 := bbase (se 3 (by rfl) ⟨52232, by rfl⟩ : syracuseStep 278573 = 104465) (by norm_num)
theorem B311357 : Blo 183802 311357 := bbase (se 3 (by rfl) ⟨58379, by rfl⟩ : syracuseStep 311357 = 116759) (by norm_num)
theorem B278597 : Blo 183802 278597 := bbase (se 4 (by rfl) ⟨26118, by rfl⟩ : syracuseStep 278597 = 52237) (by norm_num)
theorem B278621 : Blo 183802 278621 := bbase (se 3 (by rfl) ⟨52241, by rfl⟩ : syracuseStep 278621 = 104483) (by norm_num)
theorem B278645 : Blo 183802 278645 := bbase (se 5 (by rfl) ⟨13061, by rfl⟩ : syracuseStep 278645 = 26123) (by norm_num)
theorem B278669 : Blo 183802 278669 := bbase (se 3 (by rfl) ⟨52250, by rfl⟩ : syracuseStep 278669 = 104501) (by norm_num)
theorem B1130645 : Blo 183802 1130645 := bbase (se 6 (by rfl) ⟨26499, by rfl⟩ : syracuseStep 1130645 = 52999) (by norm_num)
theorem B278693 : Blo 183802 278693 := bbase (se 4 (by rfl) ⟨26127, by rfl⟩ : syracuseStep 278693 = 52255) (by norm_num)
theorem B311485 : Blo 183802 311485 := bbase (se 3 (by rfl) ⟨58403, by rfl⟩ : syracuseStep 311485 = 116807) (by norm_num)
theorem B278717 : Blo 183802 278717 := bbase (se 3 (by rfl) ⟨52259, by rfl⟩ : syracuseStep 278717 = 104519) (by norm_num)
theorem B278741 : Blo 183802 278741 := bbase (se 7 (by rfl) ⟨3266, by rfl⟩ : syracuseStep 278741 = 6533) (by norm_num)
theorem B278765 : Blo 183802 278765 := bbase (se 3 (by rfl) ⟨52268, by rfl⟩ : syracuseStep 278765 = 104537) (by norm_num)
theorem B213229 : Blo 183802 213229 := bbase (se 3 (by rfl) ⟨39980, by rfl⟩ : syracuseStep 213229 = 79961) (by norm_num)
theorem B278789 : Blo 183802 278789 := bbase (se 4 (by rfl) ⟨26136, by rfl⟩ : syracuseStep 278789 = 52273) (by norm_num)
theorem B311573 : Blo 183802 311573 := bbase (se 6 (by rfl) ⟨7302, by rfl⟩ : syracuseStep 311573 = 14605) (by norm_num)
theorem B278813 : Blo 183802 278813 := bbase (se 3 (by rfl) ⟨52277, by rfl⟩ : syracuseStep 278813 = 104555) (by norm_num)
theorem B704821 : Blo 183802 704821 := bbase (se 5 (by rfl) ⟨33038, by rfl⟩ : syracuseStep 704821 = 66077) (by norm_num)
theorem B278837 : Blo 183802 278837 := bbase (se 5 (by rfl) ⟨13070, by rfl⟩ : syracuseStep 278837 = 26141) (by norm_num)
theorem B278861 : Blo 183802 278861 := bbase (se 3 (by rfl) ⟨52286, by rfl⟩ : syracuseStep 278861 = 104573) (by norm_num)
theorem B278885 : Blo 183802 278885 := bbase (se 4 (by rfl) ⟨26145, by rfl⟩ : syracuseStep 278885 = 52291) (by norm_num)
theorem B278909 : Blo 183802 278909 := bbase (se 3 (by rfl) ⟨52295, by rfl⟩ : syracuseStep 278909 = 104591) (by norm_num)
theorem B311701 : Blo 183802 311701 := bbase (se 6 (by rfl) ⟨7305, by rfl⟩ : syracuseStep 311701 = 14611) (by norm_num)
theorem B278933 : Blo 183802 278933 := bbase (se 6 (by rfl) ⟨6537, by rfl⟩ : syracuseStep 278933 = 13075) (by norm_num)
theorem B213401 : Blo 183802 213401 := bbase (se 2 (by rfl) ⟨80025, by rfl⟩ : syracuseStep 213401 = 160051) (by norm_num)
theorem B278957 : Blo 183802 278957 := bbase (se 3 (by rfl) ⟨52304, by rfl⟩ : syracuseStep 278957 = 104609) (by norm_num)
theorem B278981 : Blo 183802 278981 := bbase (se 4 (by rfl) ⟨26154, by rfl⟩ : syracuseStep 278981 = 52309) (by norm_num)
theorem B4047317 : Blo 183802 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B279005 : Blo 183802 279005 := bbase (se 3 (by rfl) ⟨52313, by rfl⟩ : syracuseStep 279005 = 104627) (by norm_num)
theorem B311789 : Blo 183802 311789 := bbase (se 3 (by rfl) ⟨58460, by rfl⟩ : syracuseStep 311789 = 116921) (by norm_num)
theorem B279029 : Blo 183802 279029 := bbase (se 5 (by rfl) ⟨13079, by rfl⟩ : syracuseStep 279029 = 26159) (by norm_num)
theorem B279053 : Blo 183802 279053 := bbase (se 3 (by rfl) ⟨52322, by rfl⟩ : syracuseStep 279053 = 104645) (by norm_num)
theorem B279077 : Blo 183802 279077 := bbase (se 4 (by rfl) ⟨26163, by rfl⟩ : syracuseStep 279077 = 52327) (by norm_num)
theorem B1589813 : Blo 183802 1589813 := bbase (se 5 (by rfl) ⟨74522, by rfl⟩ : syracuseStep 1589813 = 149045) (by norm_num)
theorem B541237 : Blo 183802 541237 := bbase (se 5 (by rfl) ⟨25370, by rfl⟩ : syracuseStep 541237 = 50741) (by norm_num)
theorem B279101 : Blo 183802 279101 := bbase (se 3 (by rfl) ⟨52331, by rfl⟩ : syracuseStep 279101 = 104663) (by norm_num)
theorem B279125 : Blo 183802 279125 := bbase (se 8 (by rfl) ⟨1635, by rfl⟩ : syracuseStep 279125 = 3271) (by norm_num)
theorem B705125 : Blo 183802 705125 := bbase (se 4 (by rfl) ⟨66105, by rfl⟩ : syracuseStep 705125 = 132211) (by norm_num)
theorem B311917 : Blo 183802 311917 := bbase (se 3 (by rfl) ⟨58484, by rfl⟩ : syracuseStep 311917 = 116969) (by norm_num)
theorem B279149 : Blo 183802 279149 := bbase (se 3 (by rfl) ⟨52340, by rfl⟩ : syracuseStep 279149 = 104681) (by norm_num)
theorem B279173 : Blo 183802 279173 := bbase (se 4 (by rfl) ⟨26172, by rfl⟩ : syracuseStep 279173 = 52345) (by norm_num)
theorem B279197 : Blo 183802 279197 := bbase (se 3 (by rfl) ⟨52349, by rfl⟩ : syracuseStep 279197 = 104699) (by norm_num)
theorem B279221 : Blo 183802 279221 := bbase (se 5 (by rfl) ⟨13088, by rfl⟩ : syracuseStep 279221 = 26177) (by norm_num)
theorem B312005 : Blo 183802 312005 := bbase (se 4 (by rfl) ⟨29250, by rfl⟩ : syracuseStep 312005 = 58501) (by norm_num)
theorem B279245 : Blo 183802 279245 := bbase (se 3 (by rfl) ⟨52358, by rfl⟩ : syracuseStep 279245 = 104717) (by norm_num)
theorem B541397 : Blo 183802 541397 := bbase (se 7 (by rfl) ⟨6344, by rfl⟩ : syracuseStep 541397 = 12689) (by norm_num)
theorem B279269 : Blo 183802 279269 := bbase (se 4 (by rfl) ⟨26181, by rfl⟩ : syracuseStep 279269 = 52363) (by norm_num)
theorem B279293 : Blo 183802 279293 := bbase (se 3 (by rfl) ⟨52367, by rfl⟩ : syracuseStep 279293 = 104735) (by norm_num)
theorem B279317 : Blo 183802 279317 := bbase (se 6 (by rfl) ⟨6546, by rfl⟩ : syracuseStep 279317 = 13093) (by norm_num)
theorem B279341 : Blo 183802 279341 := bbase (se 3 (by rfl) ⟨52376, by rfl⟩ : syracuseStep 279341 = 104753) (by norm_num)
theorem B312133 : Blo 183802 312133 := bbase (se 4 (by rfl) ⟨29262, by rfl⟩ : syracuseStep 312133 = 58525) (by norm_num)
theorem B279365 : Blo 183802 279365 := bbase (se 4 (by rfl) ⟨26190, by rfl⟩ : syracuseStep 279365 = 52381) (by norm_num)
theorem B1491797 : Blo 183802 1491797 := bbase (se 9 (by rfl) ⟨4370, by rfl⟩ : syracuseStep 1491797 = 8741) (by norm_num)
theorem B279389 : Blo 183802 279389 := bbase (se 3 (by rfl) ⟨52385, by rfl⟩ : syracuseStep 279389 = 104771) (by norm_num)
theorem B377693 : Blo 183802 377693 := bbase (se 3 (by rfl) ⟨70817, by rfl⟩ : syracuseStep 377693 = 141635) (by norm_num)
theorem B279413 : Blo 183802 279413 := bbase (se 5 (by rfl) ⟨13097, by rfl⟩ : syracuseStep 279413 = 26195) (by norm_num)
theorem B279437 : Blo 183802 279437 := bbase (se 3 (by rfl) ⟨52394, by rfl⟩ : syracuseStep 279437 = 104789) (by norm_num)
theorem B312221 : Blo 183802 312221 := bbase (se 3 (by rfl) ⟨58541, by rfl⟩ : syracuseStep 312221 = 117083) (by norm_num)
theorem B279461 : Blo 183802 279461 := bbase (se 4 (by rfl) ⟨26199, by rfl⟩ : syracuseStep 279461 = 52399) (by norm_num)
theorem B574373 : Blo 183802 574373 := bbase (se 4 (by rfl) ⟨53847, by rfl⟩ : syracuseStep 574373 = 107695) (by norm_num)
theorem B279485 : Blo 183802 279485 := bbase (se 3 (by rfl) ⟨52403, by rfl⟩ : syracuseStep 279485 = 104807) (by norm_num)
theorem B279509 : Blo 183802 279509 := bbase (se 7 (by rfl) ⟨3275, by rfl⟩ : syracuseStep 279509 = 6551) (by norm_num)
theorem B279533 : Blo 183802 279533 := bbase (se 3 (by rfl) ⟨52412, by rfl⟩ : syracuseStep 279533 = 104825) (by norm_num)
theorem B934901 : Blo 183802 934901 := bbase (se 5 (by rfl) ⟨43823, by rfl⟩ : syracuseStep 934901 = 87647) (by norm_num)
theorem B279557 : Blo 183802 279557 := bbase (se 4 (by rfl) ⟨26208, by rfl⟩ : syracuseStep 279557 = 52417) (by norm_num)
theorem B312349 : Blo 183802 312349 := bbase (se 3 (by rfl) ⟨58565, by rfl⟩ : syracuseStep 312349 = 117131) (by norm_num)
theorem B279581 : Blo 183802 279581 := bbase (se 3 (by rfl) ⟨52421, by rfl⟩ : syracuseStep 279581 = 104843) (by norm_num)
theorem B279605 : Blo 183802 279605 := bbase (se 5 (by rfl) ⟨13106, by rfl⟩ : syracuseStep 279605 = 26213) (by norm_num)
theorem B279629 : Blo 183802 279629 := bbase (se 3 (by rfl) ⟨52430, by rfl⟩ : syracuseStep 279629 = 104861) (by norm_num)
theorem B279653 : Blo 183802 279653 := bbase (se 4 (by rfl) ⟨26217, by rfl⟩ : syracuseStep 279653 = 52435) (by norm_num)
theorem B312437 : Blo 183802 312437 := bbase (se 5 (by rfl) ⟨14645, by rfl⟩ : syracuseStep 312437 = 29291) (by norm_num)
theorem B279677 : Blo 183802 279677 := bbase (se 3 (by rfl) ⟨52439, by rfl⟩ : syracuseStep 279677 = 104879) (by norm_num)
theorem B279701 : Blo 183802 279701 := bbase (se 6 (by rfl) ⟨6555, by rfl⟩ : syracuseStep 279701 = 13111) (by norm_num)
theorem B279725 : Blo 183802 279725 := bbase (se 3 (by rfl) ⟨52448, by rfl⟩ : syracuseStep 279725 = 104897) (by norm_num)
theorem B279749 : Blo 183802 279749 := bbase (se 4 (by rfl) ⟨26226, by rfl⟩ : syracuseStep 279749 = 52453) (by norm_num)
theorem B279773 : Blo 183802 279773 := bbase (se 3 (by rfl) ⟨52457, by rfl⟩ : syracuseStep 279773 = 104915) (by norm_num)
theorem B312565 : Blo 183802 312565 := bbase (se 5 (by rfl) ⟨14651, by rfl⟩ : syracuseStep 312565 = 29303) (by norm_num)
theorem B279797 : Blo 183802 279797 := bbase (se 5 (by rfl) ⟨13115, by rfl⟩ : syracuseStep 279797 = 26231) (by norm_num)
theorem B279821 : Blo 183802 279821 := bbase (se 3 (by rfl) ⟨52466, by rfl⟩ : syracuseStep 279821 = 104933) (by norm_num)
theorem B279845 : Blo 183802 279845 := bbase (se 4 (by rfl) ⟨26235, by rfl⟩ : syracuseStep 279845 = 52471) (by norm_num)
theorem B279869 : Blo 183802 279869 := bbase (se 3 (by rfl) ⟨52475, by rfl⟩ : syracuseStep 279869 = 104951) (by norm_num)
theorem B312653 : Blo 183802 312653 := bbase (se 3 (by rfl) ⟨58622, by rfl⟩ : syracuseStep 312653 = 117245) (by norm_num)
theorem B279893 : Blo 183802 279893 := bbase (se 12 (by rfl) ⟨102, by rfl⟩ : syracuseStep 279893 = 205) (by norm_num)
theorem B279917 : Blo 183802 279917 := bbase (se 3 (by rfl) ⟨52484, by rfl⟩ : syracuseStep 279917 = 104969) (by norm_num)
theorem B378245 : Blo 183802 378245 := bbase (se 4 (by rfl) ⟨35460, by rfl⟩ : syracuseStep 378245 = 70921) (by norm_num)
theorem B279941 : Blo 183802 279941 := bbase (se 4 (by rfl) ⟨26244, by rfl⟩ : syracuseStep 279941 = 52489) (by norm_num)
theorem B279965 : Blo 183802 279965 := bbase (se 3 (by rfl) ⟨52493, by rfl⟩ : syracuseStep 279965 = 104987) (by norm_num)
theorem B279989 : Blo 183802 279989 := bbase (se 5 (by rfl) ⟨13124, by rfl⟩ : syracuseStep 279989 = 26249) (by norm_num)
theorem B312781 : Blo 183802 312781 := bbase (se 3 (by rfl) ⟨58646, by rfl⟩ : syracuseStep 312781 = 117293) (by norm_num)
theorem B280013 : Blo 183802 280013 := bbase (se 3 (by rfl) ⟨52502, by rfl⟩ : syracuseStep 280013 = 105005) (by norm_num)
theorem B2803157 : Blo 183802 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B280037 : Blo 183802 280037 := bbase (se 4 (by rfl) ⟨26253, by rfl⟩ : syracuseStep 280037 = 52507) (by norm_num)
theorem B280061 : Blo 183802 280061 := bbase (se 3 (by rfl) ⟨52511, by rfl⟩ : syracuseStep 280061 = 105023) (by norm_num)
theorem B280085 : Blo 183802 280085 := bbase (se 6 (by rfl) ⟨6564, by rfl⟩ : syracuseStep 280085 = 13129) (by norm_num)
theorem B312869 : Blo 183802 312869 := bbase (se 4 (by rfl) ⟨29331, by rfl⟩ : syracuseStep 312869 = 58663) (by norm_num)
theorem B280109 : Blo 183802 280109 := bbase (se 3 (by rfl) ⟨52520, by rfl⟩ : syracuseStep 280109 = 105041) (by norm_num)
theorem B280133 : Blo 183802 280133 := bbase (se 4 (by rfl) ⟨26262, by rfl⟩ : syracuseStep 280133 = 52525) (by norm_num)
theorem B280157 : Blo 183802 280157 := bbase (se 3 (by rfl) ⟨52529, by rfl⟩ : syracuseStep 280157 = 105059) (by norm_num)
theorem B280181 : Blo 183802 280181 := bbase (se 5 (by rfl) ⟨13133, by rfl⟩ : syracuseStep 280181 = 26267) (by norm_num)
theorem B280205 : Blo 183802 280205 := bbase (se 3 (by rfl) ⟨52538, by rfl⟩ : syracuseStep 280205 = 105077) (by norm_num)
theorem B312997 : Blo 183802 312997 := bbase (se 4 (by rfl) ⟨29343, by rfl⟩ : syracuseStep 312997 = 58687) (by norm_num)
theorem B280229 : Blo 183802 280229 := bbase (se 4 (by rfl) ⟨26271, by rfl⟩ : syracuseStep 280229 = 52543) (by norm_num)
theorem B280253 : Blo 183802 280253 := bbase (se 3 (by rfl) ⟨52547, by rfl⟩ : syracuseStep 280253 = 105095) (by norm_num)
theorem B476869 : Blo 183802 476869 := bbase (se 4 (by rfl) ⟨44706, by rfl⟩ : syracuseStep 476869 = 89413) (by norm_num)
theorem B280277 : Blo 183802 280277 := bbase (se 7 (by rfl) ⟨3284, by rfl⟩ : syracuseStep 280277 = 6569) (by norm_num)
theorem B1066709 : Blo 183802 1066709 := bbase (se 7 (by rfl) ⟨12500, by rfl⟩ : syracuseStep 1066709 = 25001) (by norm_num)
theorem B280301 : Blo 183802 280301 := bbase (se 3 (by rfl) ⟨52556, by rfl⟩ : syracuseStep 280301 = 105113) (by norm_num)
theorem B313085 : Blo 183802 313085 := bbase (se 3 (by rfl) ⟨58703, by rfl⟩ : syracuseStep 313085 = 117407) (by norm_num)
theorem B280325 : Blo 183802 280325 := bbase (se 4 (by rfl) ⟨26280, by rfl⟩ : syracuseStep 280325 = 52561) (by norm_num)
theorem B280349 : Blo 183802 280349 := bbase (se 3 (by rfl) ⟨52565, by rfl⟩ : syracuseStep 280349 = 105131) (by norm_num)
theorem B280373 : Blo 183802 280373 := bbase (se 5 (by rfl) ⟨13142, by rfl⟩ : syracuseStep 280373 = 26285) (by norm_num)
theorem B280397 : Blo 183802 280397 := bbase (se 3 (by rfl) ⟨52574, by rfl⟩ : syracuseStep 280397 = 105149) (by norm_num)
theorem B280421 : Blo 183802 280421 := bbase (se 4 (by rfl) ⟨26289, by rfl⟩ : syracuseStep 280421 = 52579) (by norm_num)
theorem B313213 : Blo 183802 313213 := bbase (se 3 (by rfl) ⟨58727, by rfl⟩ : syracuseStep 313213 = 117455) (by norm_num)
theorem B280445 : Blo 183802 280445 := bbase (se 3 (by rfl) ⟨52583, by rfl⟩ : syracuseStep 280445 = 105167) (by norm_num)
theorem B280469 : Blo 183802 280469 := bbase (se 6 (by rfl) ⟨6573, by rfl⟩ : syracuseStep 280469 = 13147) (by norm_num)
theorem B280493 : Blo 183802 280493 := bbase (se 3 (by rfl) ⟨52592, by rfl⟩ : syracuseStep 280493 = 105185) (by norm_num)
theorem B1427381 : Blo 183802 1427381 := bbase (se 5 (by rfl) ⟨66908, by rfl⟩ : syracuseStep 1427381 = 133817) (by norm_num)
theorem B280517 : Blo 183802 280517 := bbase (se 4 (by rfl) ⟨26298, by rfl⟩ : syracuseStep 280517 = 52597) (by norm_num)
theorem B313301 : Blo 183802 313301 := bbase (se 7 (by rfl) ⟨3671, by rfl⟩ : syracuseStep 313301 = 7343) (by norm_num)
theorem B280541 : Blo 183802 280541 := bbase (se 3 (by rfl) ⟨52601, by rfl⟩ : syracuseStep 280541 = 105203) (by norm_num)
theorem B280565 : Blo 183802 280565 := bbase (se 5 (by rfl) ⟨13151, by rfl⟩ : syracuseStep 280565 = 26303) (by norm_num)
theorem B280589 : Blo 183802 280589 := bbase (se 3 (by rfl) ⟨52610, by rfl⟩ : syracuseStep 280589 = 105221) (by norm_num)
theorem B280613 : Blo 183802 280613 := bbase (se 4 (by rfl) ⟨26307, by rfl⟩ : syracuseStep 280613 = 52615) (by norm_num)
theorem B280637 : Blo 183802 280637 := bbase (se 3 (by rfl) ⟨52619, by rfl⟩ : syracuseStep 280637 = 105239) (by norm_num)
theorem B313429 : Blo 183802 313429 := bbase (se 8 (by rfl) ⟨1836, by rfl⟩ : syracuseStep 313429 = 3673) (by norm_num)
theorem B280661 : Blo 183802 280661 := bbase (se 8 (by rfl) ⟨1644, by rfl⟩ : syracuseStep 280661 = 3289) (by norm_num)
theorem B280685 : Blo 183802 280685 := bbase (se 3 (by rfl) ⟨52628, by rfl⟩ : syracuseStep 280685 = 105257) (by norm_num)
theorem B280709 : Blo 183802 280709 := bbase (se 4 (by rfl) ⟨26316, by rfl⟩ : syracuseStep 280709 = 52633) (by norm_num)
theorem B280733 : Blo 183802 280733 := bbase (se 3 (by rfl) ⟨52637, by rfl⟩ : syracuseStep 280733 = 105275) (by norm_num)
theorem B313517 : Blo 183802 313517 := bbase (se 3 (by rfl) ⟨58784, by rfl⟩ : syracuseStep 313517 = 117569) (by norm_num)
theorem B280757 : Blo 183802 280757 := bbase (se 5 (by rfl) ⟨13160, by rfl⟩ : syracuseStep 280757 = 26321) (by norm_num)
theorem B280781 : Blo 183802 280781 := bbase (se 3 (by rfl) ⟨52646, by rfl⟩ : syracuseStep 280781 = 105293) (by norm_num)
theorem B280805 : Blo 183802 280805 := bbase (se 4 (by rfl) ⟨26325, by rfl⟩ : syracuseStep 280805 = 52651) (by norm_num)
theorem B280829 : Blo 183802 280829 := bbase (se 3 (by rfl) ⟨52655, by rfl⟩ : syracuseStep 280829 = 105311) (by norm_num)
theorem B936197 : Blo 183802 936197 := bbase (se 4 (by rfl) ⟨87768, by rfl⟩ : syracuseStep 936197 = 175537) (by norm_num)
theorem B280853 : Blo 183802 280853 := bbase (se 6 (by rfl) ⟨6582, by rfl⟩ : syracuseStep 280853 = 13165) (by norm_num)
theorem B313645 : Blo 183802 313645 := bbase (se 3 (by rfl) ⟨58808, by rfl⟩ : syracuseStep 313645 = 117617) (by norm_num)
theorem B280877 : Blo 183802 280877 := bbase (se 3 (by rfl) ⟨52664, by rfl⟩ : syracuseStep 280877 = 105329) (by norm_num)
theorem B280901 : Blo 183802 280901 := bbase (se 4 (by rfl) ⟨26334, by rfl⟩ : syracuseStep 280901 = 52669) (by norm_num)
theorem B280925 : Blo 183802 280925 := bbase (se 3 (by rfl) ⟨52673, by rfl⟩ : syracuseStep 280925 = 105347) (by norm_num)
theorem B444781 : Blo 183802 444781 := bbase (se 3 (by rfl) ⟨83396, by rfl⟩ : syracuseStep 444781 = 166793) (by norm_num)
theorem B280949 : Blo 183802 280949 := bbase (se 5 (by rfl) ⟨13169, by rfl⟩ : syracuseStep 280949 = 26339) (by norm_num)
theorem B313733 : Blo 183802 313733 := bbase (se 4 (by rfl) ⟨29412, by rfl⟩ : syracuseStep 313733 = 58825) (by norm_num)
theorem B280973 : Blo 183802 280973 := bbase (se 3 (by rfl) ⟨52682, by rfl⟩ : syracuseStep 280973 = 105365) (by norm_num)
theorem B280997 : Blo 183802 280997 := bbase (se 4 (by rfl) ⟨26343, by rfl⟩ : syracuseStep 280997 = 52687) (by norm_num)
theorem B281021 : Blo 183802 281021 := bbase (se 3 (by rfl) ⟨52691, by rfl⟩ : syracuseStep 281021 = 105383) (by norm_num)
theorem B281045 : Blo 183802 281045 := bbase (se 7 (by rfl) ⟨3293, by rfl⟩ : syracuseStep 281045 = 6587) (by norm_num)
theorem B281069 : Blo 183802 281069 := bbase (se 3 (by rfl) ⟨52700, by rfl⟩ : syracuseStep 281069 = 105401) (by norm_num)
theorem B313861 : Blo 183802 313861 := bbase (se 4 (by rfl) ⟨29424, by rfl⟩ : syracuseStep 313861 = 58849) (by norm_num)
theorem B281093 : Blo 183802 281093 := bbase (se 4 (by rfl) ⟨26352, by rfl⟩ : syracuseStep 281093 = 52705) (by norm_num)
theorem B1198613 : Blo 183802 1198613 := bbase (se 6 (by rfl) ⟨28092, by rfl⟩ : syracuseStep 1198613 = 56185) (by norm_num)
theorem B281117 : Blo 183802 281117 := bbase (se 3 (by rfl) ⟨52709, by rfl⟩ : syracuseStep 281117 = 105419) (by norm_num)
theorem B281141 : Blo 183802 281141 := bbase (se 5 (by rfl) ⟨13178, by rfl⟩ : syracuseStep 281141 = 26357) (by norm_num)
theorem B281165 : Blo 183802 281165 := bbase (se 3 (by rfl) ⟨52718, by rfl⟩ : syracuseStep 281165 = 105437) (by norm_num)
theorem B313949 : Blo 183802 313949 := bbase (se 3 (by rfl) ⟨58865, by rfl⟩ : syracuseStep 313949 = 117731) (by norm_num)
theorem B281189 : Blo 183802 281189 := bbase (se 4 (by rfl) ⟨26361, by rfl⟩ : syracuseStep 281189 = 52723) (by norm_num)
theorem B281213 : Blo 183802 281213 := bbase (se 3 (by rfl) ⟨52727, by rfl⟩ : syracuseStep 281213 = 105455) (by norm_num)
theorem B281237 : Blo 183802 281237 := bbase (se 6 (by rfl) ⟨6591, by rfl⟩ : syracuseStep 281237 = 13183) (by norm_num)
theorem B707237 : Blo 183802 707237 := bbase (se 4 (by rfl) ⟨66303, by rfl⟩ : syracuseStep 707237 = 132607) (by norm_num)
theorem B281261 : Blo 183802 281261 := bbase (se 3 (by rfl) ⟨52736, by rfl⟩ : syracuseStep 281261 = 105473) (by norm_num)
theorem B281285 : Blo 183802 281285 := bbase (se 4 (by rfl) ⟨26370, by rfl⟩ : syracuseStep 281285 = 52741) (by norm_num)
theorem B314077 : Blo 183802 314077 := bbase (se 3 (by rfl) ⟨58889, by rfl⟩ : syracuseStep 314077 = 117779) (by norm_num)
theorem B281309 : Blo 183802 281309 := bbase (se 3 (by rfl) ⟨52745, by rfl⟩ : syracuseStep 281309 = 105491) (by norm_num)
theorem B281333 : Blo 183802 281333 := bbase (se 5 (by rfl) ⟨13187, by rfl⟩ : syracuseStep 281333 = 26375) (by norm_num)
theorem B281357 : Blo 183802 281357 := bbase (se 3 (by rfl) ⟨52754, by rfl⟩ : syracuseStep 281357 = 105509) (by norm_num)
theorem B281381 : Blo 183802 281381 := bbase (se 4 (by rfl) ⟨26379, by rfl⟩ : syracuseStep 281381 = 52759) (by norm_num)
theorem B314165 : Blo 183802 314165 := bbase (se 5 (by rfl) ⟨14726, by rfl⟩ : syracuseStep 314165 = 29453) (by norm_num)
theorem B281405 : Blo 183802 281405 := bbase (se 3 (by rfl) ⟨52763, by rfl⟩ : syracuseStep 281405 = 105527) (by norm_num)
theorem B281429 : Blo 183802 281429 := bbase (se 9 (by rfl) ⟨824, by rfl⟩ : syracuseStep 281429 = 1649) (by norm_num)
theorem B281453 : Blo 183802 281453 := bbase (se 3 (by rfl) ⟨52772, by rfl⟩ : syracuseStep 281453 = 105545) (by norm_num)
theorem B281477 : Blo 183802 281477 := bbase (se 4 (by rfl) ⟨26388, by rfl⟩ : syracuseStep 281477 = 52777) (by norm_num)
theorem B281501 : Blo 183802 281501 := bbase (se 3 (by rfl) ⟨52781, by rfl⟩ : syracuseStep 281501 = 105563) (by norm_num)
theorem B314293 : Blo 183802 314293 := bbase (se 5 (by rfl) ⟨14732, by rfl⟩ : syracuseStep 314293 = 29465) (by norm_num)
theorem B281525 : Blo 183802 281525 := bbase (se 5 (by rfl) ⟨13196, by rfl⟩ : syracuseStep 281525 = 26393) (by norm_num)
theorem B707525 : Blo 183802 707525 := bbase (se 4 (by rfl) ⟨66330, by rfl⟩ : syracuseStep 707525 = 132661) (by norm_num)
theorem B281549 : Blo 183802 281549 := bbase (se 3 (by rfl) ⟨52790, by rfl⟩ : syracuseStep 281549 = 105581) (by norm_num)
theorem B281573 : Blo 183802 281573 := bbase (se 4 (by rfl) ⟨26397, by rfl⟩ : syracuseStep 281573 = 52795) (by norm_num)
theorem B281597 : Blo 183802 281597 := bbase (se 3 (by rfl) ⟨52799, by rfl⟩ : syracuseStep 281597 = 105599) (by norm_num)
theorem B445445 : Blo 183802 445445 := bbase (se 4 (by rfl) ⟨41760, by rfl⟩ : syracuseStep 445445 = 83521) (by norm_num)
theorem B248845 : Blo 183802 248845 := bbase (se 3 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 248845 = 93317) (by norm_num)
theorem B314381 : Blo 183802 314381 := bbase (se 3 (by rfl) ⟨58946, by rfl⟩ : syracuseStep 314381 = 117893) (by norm_num)
theorem B281621 : Blo 183802 281621 := bbase (se 6 (by rfl) ⟨6600, by rfl⟩ : syracuseStep 281621 = 13201) (by norm_num)
theorem B281645 : Blo 183802 281645 := bbase (se 3 (by rfl) ⟨52808, by rfl⟩ : syracuseStep 281645 = 105617) (by norm_num)
theorem B281669 : Blo 183802 281669 := bbase (se 4 (by rfl) ⟨26406, by rfl⟩ : syracuseStep 281669 = 52813) (by norm_num)
theorem B281693 : Blo 183802 281693 := bbase (se 3 (by rfl) ⟨52817, by rfl⟩ : syracuseStep 281693 = 105635) (by norm_num)
theorem B314509 : Blo 183802 314509 := bbase (se 3 (by rfl) ⟨58970, by rfl⟩ : syracuseStep 314509 = 117941) (by norm_num)
theorem B314597 : Blo 183802 314597 := bbase (se 4 (by rfl) ⟨29493, by rfl⟩ : syracuseStep 314597 = 58987) (by norm_num)
theorem B445733 : Blo 183802 445733 := bbase (se 4 (by rfl) ⟨41787, by rfl⟩ : syracuseStep 445733 = 83575) (by norm_num)
theorem B249157 : Blo 183802 249157 := bbase (se 4 (by rfl) ⟨23358, by rfl⟩ : syracuseStep 249157 = 46717) (by norm_num)
theorem B314725 : Blo 183802 314725 := bbase (se 4 (by rfl) ⟨29505, by rfl⟩ : syracuseStep 314725 = 59011) (by norm_num)
theorem B281981 : Blo 183802 281981 := bbase (se 3 (by rfl) ⟨52871, by rfl⟩ : syracuseStep 281981 = 105743) (by norm_num)
theorem B314813 : Blo 183802 314813 := bbase (se 3 (by rfl) ⟨59027, by rfl⟩ : syracuseStep 314813 = 118055) (by norm_num)
theorem B282053 : Blo 183802 282053 := bbase (se 4 (by rfl) ⟨26442, by rfl⟩ : syracuseStep 282053 = 52885) (by norm_num)
theorem B675317 : Blo 183802 675317 := bbase (se 5 (by rfl) ⟨31655, by rfl⟩ : syracuseStep 675317 = 63311) (by norm_num)
theorem B937493 : Blo 183802 937493 := bbase (se 6 (by rfl) ⟨21972, by rfl⟩ : syracuseStep 937493 = 43945) (by norm_num)
theorem B1134101 : Blo 183802 1134101 := bbase (se 6 (by rfl) ⟨26580, by rfl⟩ : syracuseStep 1134101 = 53161) (by norm_num)
theorem B1396277 : Blo 183802 1396277 := bbase (se 5 (by rfl) ⟨65450, by rfl⟩ : syracuseStep 1396277 = 130901) (by norm_num)
theorem B314941 : Blo 183802 314941 := bbase (se 3 (by rfl) ⟨59051, by rfl⟩ : syracuseStep 314941 = 118103) (by norm_num)
theorem B315029 : Blo 183802 315029 := bbase (se 6 (by rfl) ⟨7383, by rfl⟩ : syracuseStep 315029 = 14767) (by norm_num)
theorem B315157 : Blo 183802 315157 := bbase (se 6 (by rfl) ⟨7386, by rfl⟩ : syracuseStep 315157 = 14773) (by norm_num)
theorem B315245 : Blo 183802 315245 := bbase (se 3 (by rfl) ⟨59108, by rfl⟩ : syracuseStep 315245 = 118217) (by norm_num)
theorem B675749 : Blo 183802 675749 := bbase (se 4 (by rfl) ⟨63351, by rfl⟩ : syracuseStep 675749 = 126703) (by norm_num)
theorem B413621 : Blo 183802 413621 := bbase (se 5 (by rfl) ⟨19388, by rfl⟩ : syracuseStep 413621 = 38777) (by norm_num)
theorem B708533 : Blo 183802 708533 := bbase (se 5 (by rfl) ⟨33212, by rfl⟩ : syracuseStep 708533 = 66425) (by norm_num)
theorem B249805 : Blo 183802 249805 := bbase (se 3 (by rfl) ⟨46838, by rfl⟩ : syracuseStep 249805 = 93677) (by norm_num)
theorem B315373 : Blo 183802 315373 := bbase (se 3 (by rfl) ⟨59132, by rfl⟩ : syracuseStep 315373 = 118265) (by norm_num)
theorem B413693 : Blo 183802 413693 := bbase (se 3 (by rfl) ⟨77567, by rfl⟩ : syracuseStep 413693 = 155135) (by norm_num)
theorem B413765 : Blo 183802 413765 := bbase (se 4 (by rfl) ⟨38790, by rfl⟩ : syracuseStep 413765 = 77581) (by norm_num)
theorem B315461 : Blo 183802 315461 := bbase (se 4 (by rfl) ⟨29574, by rfl⟩ : syracuseStep 315461 = 59149) (by norm_num)
theorem B708709 : Blo 183802 708709 := bbase (se 4 (by rfl) ⟨66441, by rfl⟩ : syracuseStep 708709 = 132883) (by norm_num)
theorem B413837 : Blo 183802 413837 := bbase (se 3 (by rfl) ⟨77594, by rfl⟩ : syracuseStep 413837 = 155189) (by norm_num)
theorem B315589 : Blo 183802 315589 := bbase (se 4 (by rfl) ⟨29586, by rfl⟩ : syracuseStep 315589 = 59173) (by norm_num)
theorem B413909 : Blo 183802 413909 := bbase (se 7 (by rfl) ⟨4850, by rfl⟩ : syracuseStep 413909 = 9701) (by norm_num)
theorem B1003765 : Blo 183802 1003765 := bbase (se 5 (by rfl) ⟨47051, by rfl⟩ : syracuseStep 1003765 = 94103) (by norm_num)
theorem B413981 : Blo 183802 413981 := bbase (se 3 (by rfl) ⟨77621, by rfl⟩ : syracuseStep 413981 = 155243) (by norm_num)
theorem B315677 : Blo 183802 315677 := bbase (se 3 (by rfl) ⟨59189, by rfl⟩ : syracuseStep 315677 = 118379) (by norm_num)
theorem B414053 : Blo 183802 414053 := bbase (se 4 (by rfl) ⟨38817, by rfl⟩ : syracuseStep 414053 = 77635) (by norm_num)
theorem B709013 : Blo 183802 709013 := bbase (se 6 (by rfl) ⟨16617, by rfl⟩ : syracuseStep 709013 = 33235) (by norm_num)
theorem B315805 : Blo 183802 315805 := bbase (se 3 (by rfl) ⟨59213, by rfl⟩ : syracuseStep 315805 = 118427) (by norm_num)
theorem B414125 : Blo 183802 414125 := bbase (se 3 (by rfl) ⟨77648, by rfl⟩ : syracuseStep 414125 = 155297) (by norm_num)
theorem B414197 : Blo 183802 414197 := bbase (se 5 (by rfl) ⟨19415, by rfl⟩ : syracuseStep 414197 = 38831) (by norm_num)
theorem B315893 : Blo 183802 315893 := bbase (se 5 (by rfl) ⟨14807, by rfl⟩ : syracuseStep 315893 = 29615) (by norm_num)
theorem B414269 : Blo 183802 414269 := bbase (se 3 (by rfl) ⟨77675, by rfl⟩ : syracuseStep 414269 = 155351) (by norm_num)
theorem B316021 : Blo 183802 316021 := bbase (se 5 (by rfl) ⟨14813, by rfl⟩ : syracuseStep 316021 = 29627) (by norm_num)
theorem B414341 : Blo 183802 414341 := bbase (se 4 (by rfl) ⟨38844, by rfl⟩ : syracuseStep 414341 = 77689) (by norm_num)
theorem B414413 : Blo 183802 414413 := bbase (se 3 (by rfl) ⟨77702, by rfl⟩ : syracuseStep 414413 = 155405) (by norm_num)
theorem B316109 : Blo 183802 316109 := bbase (se 3 (by rfl) ⟨59270, by rfl⟩ : syracuseStep 316109 = 118541) (by norm_num)
theorem B348941 : Blo 183802 348941 := bbase (se 3 (by rfl) ⟨65426, by rfl⟩ : syracuseStep 348941 = 130853) (by norm_num)
theorem B414485 : Blo 183802 414485 := bbase (se 6 (by rfl) ⟨9714, by rfl⟩ : syracuseStep 414485 = 19429) (by norm_num)
theorem B938789 : Blo 183802 938789 := bbase (se 4 (by rfl) ⟨88011, by rfl⟩ : syracuseStep 938789 = 176023) (by norm_num)
theorem B316237 : Blo 183802 316237 := bbase (se 3 (by rfl) ⟨59294, by rfl⟩ : syracuseStep 316237 = 118589) (by norm_num)
theorem B414557 : Blo 183802 414557 := bbase (se 3 (by rfl) ⟨77729, by rfl⟩ : syracuseStep 414557 = 155459) (by norm_num)
theorem B349085 : Blo 183802 349085 := bbase (se 3 (by rfl) ⟨65453, by rfl⟩ : syracuseStep 349085 = 130907) (by norm_num)
theorem B414629 : Blo 183802 414629 := bbase (se 4 (by rfl) ⟨38871, by rfl⟩ : syracuseStep 414629 = 77743) (by norm_num)
theorem B316325 : Blo 183802 316325 := bbase (se 4 (by rfl) ⟨29655, by rfl⟩ : syracuseStep 316325 = 59311) (by norm_num)
theorem B1004501 : Blo 183802 1004501 := bbase (se 7 (by rfl) ⟨11771, by rfl⟩ : syracuseStep 1004501 = 23543) (by norm_num)
theorem B414701 : Blo 183802 414701 := bbase (se 3 (by rfl) ⟨77756, by rfl⟩ : syracuseStep 414701 = 155513) (by norm_num)
theorem B316453 : Blo 183802 316453 := bbase (se 4 (by rfl) ⟨29667, by rfl⟩ : syracuseStep 316453 = 59335) (by norm_num)
theorem B414773 : Blo 183802 414773 := bbase (se 5 (by rfl) ⟨19442, by rfl⟩ : syracuseStep 414773 = 38885) (by norm_num)
theorem B414845 : Blo 183802 414845 := bbase (se 3 (by rfl) ⟨77783, by rfl⟩ : syracuseStep 414845 = 155567) (by norm_num)
theorem B316541 : Blo 183802 316541 := bbase (se 3 (by rfl) ⟨59351, by rfl⟩ : syracuseStep 316541 = 118703) (by norm_num)
theorem B349373 : Blo 183802 349373 := bbase (se 3 (by rfl) ⟨65507, by rfl⟩ : syracuseStep 349373 = 131015) (by norm_num)
theorem B414917 : Blo 183802 414917 := bbase (se 4 (by rfl) ⟨38898, by rfl⟩ : syracuseStep 414917 = 77797) (by norm_num)
theorem B316669 : Blo 183802 316669 := bbase (se 3 (by rfl) ⟨59375, by rfl⟩ : syracuseStep 316669 = 118751) (by norm_num)
theorem B414989 : Blo 183802 414989 := bbase (se 3 (by rfl) ⟨77810, by rfl⟩ : syracuseStep 414989 = 155621) (by norm_num)
theorem B447781 : Blo 183802 447781 := bbase (se 4 (by rfl) ⟨41979, by rfl⟩ : syracuseStep 447781 = 83959) (by norm_num)
theorem B349525 : Blo 183802 349525 := bbase (se 20 (by rfl) ⟨0, by rfl⟩ : syracuseStep 349525 = 1) (by norm_num)
theorem B415061 : Blo 183802 415061 := bbase (se 16 (by rfl) ⟨9, by rfl⟩ : syracuseStep 415061 = 19) (by norm_num)
theorem B316757 : Blo 183802 316757 := bbase (se 15 (by rfl) ⟨14, by rfl⟩ : syracuseStep 316757 = 29) (by norm_num)
theorem B415133 : Blo 183802 415133 := bbase (se 3 (by rfl) ⟨77837, by rfl⟩ : syracuseStep 415133 = 155675) (by norm_num)
theorem B284077 : Blo 183802 284077 := bbase (se 3 (by rfl) ⟨53264, by rfl⟩ : syracuseStep 284077 = 106529) (by norm_num)
theorem B1496501 : Blo 183802 1496501 := bbase (se 5 (by rfl) ⟨70148, by rfl⟩ : syracuseStep 1496501 = 140297) (by norm_num)
theorem B2840021 : Blo 183802 2840021 := bbase (se 7 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 2840021 = 66563) (by norm_num)
theorem B316885 : Blo 183802 316885 := bbase (se 7 (by rfl) ⟨3713, by rfl⟩ : syracuseStep 316885 = 7427) (by norm_num)
theorem B415205 : Blo 183802 415205 := bbase (se 4 (by rfl) ⟨38925, by rfl⟩ : syracuseStep 415205 = 77851) (by norm_num)
theorem B415277 : Blo 183802 415277 := bbase (se 3 (by rfl) ⟨77864, by rfl⟩ : syracuseStep 415277 = 155729) (by norm_num)
theorem B415349 : Blo 183802 415349 := bbase (se 5 (by rfl) ⟨19469, by rfl⟩ : syracuseStep 415349 = 38939) (by norm_num)
theorem B349829 : Blo 183802 349829 := bbase (se 4 (by rfl) ⟨32796, by rfl⟩ : syracuseStep 349829 = 65593) (by norm_num)
theorem B415421 : Blo 183802 415421 := bbase (se 3 (by rfl) ⟨77891, by rfl⟩ : syracuseStep 415421 = 155783) (by norm_num)
theorem B415493 : Blo 183802 415493 := bbase (se 4 (by rfl) ⟨38952, by rfl⟩ : syracuseStep 415493 = 77905) (by norm_num)
theorem B415565 : Blo 183802 415565 := bbase (se 3 (by rfl) ⟨77918, by rfl⟩ : syracuseStep 415565 = 155837) (by norm_num)
theorem B415637 : Blo 183802 415637 := bbase (se 6 (by rfl) ⟨9741, by rfl⟩ : syracuseStep 415637 = 19483) (by norm_num)
theorem B415709 : Blo 183802 415709 := bbase (se 3 (by rfl) ⟨77945, by rfl⟩ : syracuseStep 415709 = 155891) (by norm_num)
theorem B186349 : Blo 183802 186349 := bbase (se 3 (by rfl) ⟨34940, by rfl⟩ : syracuseStep 186349 = 69881) (by norm_num)
theorem B186365 : Blo 183802 186365 := bbase (se 3 (by rfl) ⟨34943, by rfl⟩ : syracuseStep 186365 = 69887) (by norm_num)
theorem B415781 : Blo 183802 415781 := bbase (se 4 (by rfl) ⟨38979, by rfl⟩ : syracuseStep 415781 = 77959) (by norm_num)
theorem B940085 : Blo 183802 940085 := bbase (se 5 (by rfl) ⟨44066, by rfl⟩ : syracuseStep 940085 = 88133) (by norm_num)
theorem B415853 : Blo 183802 415853 := bbase (se 3 (by rfl) ⟨77972, by rfl⟩ : syracuseStep 415853 = 155945) (by norm_num)
theorem B415925 : Blo 183802 415925 := bbase (se 5 (by rfl) ⟨19496, by rfl⟩ : syracuseStep 415925 = 38993) (by norm_num)
theorem B252109 : Blo 183802 252109 := bbase (se 3 (by rfl) ⟨47270, by rfl⟩ : syracuseStep 252109 = 94541) (by norm_num)
theorem B415997 : Blo 183802 415997 := bbase (se 3 (by rfl) ⟨77999, by rfl⟩ : syracuseStep 415997 = 155999) (by norm_num)
theorem B612613 : Blo 183802 612613 := bbase (se 4 (by rfl) ⟨57432, by rfl⟩ : syracuseStep 612613 = 114865) (by norm_num)
theorem B1202485 : Blo 183802 1202485 := bbase (se 5 (by rfl) ⟨56366, by rfl⟩ : syracuseStep 1202485 = 112733) (by norm_num)
theorem B416069 : Blo 183802 416069 := bbase (se 4 (by rfl) ⟨39006, by rfl⟩ : syracuseStep 416069 = 78013) (by norm_num)
theorem B350581 : Blo 183802 350581 := bbase (se 5 (by rfl) ⟨16433, by rfl⟩ : syracuseStep 350581 = 32867) (by norm_num)
theorem B416141 : Blo 183802 416141 := bbase (se 3 (by rfl) ⟨78026, by rfl⟩ : syracuseStep 416141 = 156053) (by norm_num)
theorem B416213 : Blo 183802 416213 := bbase (se 7 (by rfl) ⟨4877, by rfl⟩ : syracuseStep 416213 = 9755) (by norm_num)
theorem B711125 : Blo 183802 711125 := bbase (se 7 (by rfl) ⟨8333, by rfl⟩ : syracuseStep 711125 = 16667) (by norm_num)
theorem B350725 : Blo 183802 350725 := bbase (se 4 (by rfl) ⟨32880, by rfl⟩ : syracuseStep 350725 = 65761) (by norm_num)
theorem B416285 : Blo 183802 416285 := bbase (se 3 (by rfl) ⟨78053, by rfl⟩ : syracuseStep 416285 = 156107) (by norm_num)
theorem B186949 : Blo 183802 186949 := bbase (se 4 (by rfl) ⟨17526, by rfl⟩ : syracuseStep 186949 = 35053) (by norm_num)
theorem B416357 : Blo 183802 416357 := bbase (se 4 (by rfl) ⟨39033, by rfl⟩ : syracuseStep 416357 = 78067) (by norm_num)
theorem B350885 : Blo 183802 350885 := bbase (se 4 (by rfl) ⟨32895, by rfl⟩ : syracuseStep 350885 = 65791) (by norm_num)
theorem B416429 : Blo 183802 416429 := bbase (se 3 (by rfl) ⟨78080, by rfl⟩ : syracuseStep 416429 = 156161) (by norm_num)
theorem B416501 : Blo 183802 416501 := bbase (se 5 (by rfl) ⟨19523, by rfl⟩ : syracuseStep 416501 = 39047) (by norm_num)
theorem B711413 : Blo 183802 711413 := bbase (se 5 (by rfl) ⟨33347, by rfl⟩ : syracuseStep 711413 = 66695) (by norm_num)
theorem B351029 : Blo 183802 351029 := bbase (se 5 (by rfl) ⟨16454, by rfl⟩ : syracuseStep 351029 = 32909) (by norm_num)
theorem B252725 : Blo 183802 252725 := bbase (se 5 (by rfl) ⟨11846, by rfl⟩ : syracuseStep 252725 = 23693) (by norm_num)
theorem B416573 : Blo 183802 416573 := bbase (se 3 (by rfl) ⟨78107, by rfl⟩ : syracuseStep 416573 = 156215) (by norm_num)
theorem B318269 : Blo 183802 318269 := bbase (se 3 (by rfl) ⟨59675, by rfl⟩ : syracuseStep 318269 = 119351) (by norm_num)
theorem B416645 : Blo 183802 416645 := bbase (se 4 (by rfl) ⟨39060, by rfl⟩ : syracuseStep 416645 = 78121) (by norm_num)
theorem B416717 : Blo 183802 416717 := bbase (se 3 (by rfl) ⟨78134, by rfl⟩ : syracuseStep 416717 = 156269) (by norm_num)
theorem B416789 : Blo 183802 416789 := bbase (se 6 (by rfl) ⟨9768, by rfl⟩ : syracuseStep 416789 = 19537) (by norm_num)
theorem B351317 : Blo 183802 351317 := bbase (se 8 (by rfl) ⟨2058, by rfl⟩ : syracuseStep 351317 = 4117) (by norm_num)
theorem B416861 : Blo 183802 416861 := bbase (se 3 (by rfl) ⟨78161, by rfl⟩ : syracuseStep 416861 = 156323) (by norm_num)
theorem B187525 : Blo 183802 187525 := bbase (se 4 (by rfl) ⟨17580, by rfl⟩ : syracuseStep 187525 = 35161) (by norm_num)
theorem B416933 : Blo 183802 416933 := bbase (se 4 (by rfl) ⟨39087, by rfl⟩ : syracuseStep 416933 = 78175) (by norm_num)
theorem B875717 : Blo 183802 875717 := bbase (se 4 (by rfl) ⟨82098, by rfl⟩ : syracuseStep 875717 = 164197) (by norm_num)
theorem B351469 : Blo 183802 351469 := bbase (se 3 (by rfl) ⟨65900, by rfl⟩ : syracuseStep 351469 = 131801) (by norm_num)
theorem B417005 : Blo 183802 417005 := bbase (se 3 (by rfl) ⟨78188, by rfl⟩ : syracuseStep 417005 = 156377) (by norm_num)
theorem B417077 : Blo 183802 417077 := bbase (se 5 (by rfl) ⟨19550, by rfl⟩ : syracuseStep 417077 = 39101) (by norm_num)
theorem B941381 : Blo 183802 941381 := bbase (se 4 (by rfl) ⟨88254, by rfl⟩ : syracuseStep 941381 = 176509) (by norm_num)
theorem B417149 : Blo 183802 417149 := bbase (se 3 (by rfl) ⟨78215, by rfl⟩ : syracuseStep 417149 = 156431) (by norm_num)
theorem B253309 : Blo 183802 253309 := bbase (se 3 (by rfl) ⟨47495, by rfl⟩ : syracuseStep 253309 = 94991) (by norm_num)
theorem B1793461 : Blo 183802 1793461 := bbase (se 5 (by rfl) ⟨84068, by rfl⟩ : syracuseStep 1793461 = 168137) (by norm_num)
theorem B417221 : Blo 183802 417221 := bbase (se 4 (by rfl) ⟨39114, by rfl⟩ : syracuseStep 417221 = 78229) (by norm_num)
theorem B2252245 : Blo 183802 2252245 := bbase (se 7 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 2252245 = 52787) (by norm_num)
theorem B712165 : Blo 183802 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B417293 : Blo 183802 417293 := bbase (se 3 (by rfl) ⟨78242, by rfl⟩ : syracuseStep 417293 = 156485) (by norm_num)
theorem B351773 : Blo 183802 351773 := bbase (se 3 (by rfl) ⟨65957, by rfl⟩ : syracuseStep 351773 = 131915) (by norm_num)
theorem B253477 : Blo 183802 253477 := bbase (se 4 (by rfl) ⟨23763, by rfl⟩ : syracuseStep 253477 = 47527) (by norm_num)
theorem B843317 : Blo 183802 843317 := bbase (se 5 (by rfl) ⟨39530, by rfl⟩ : syracuseStep 843317 = 79061) (by norm_num)
theorem B417365 : Blo 183802 417365 := bbase (se 8 (by rfl) ⟨2445, by rfl⟩ : syracuseStep 417365 = 4891) (by norm_num)
theorem B253525 : Blo 183802 253525 := bbase (se 8 (by rfl) ⟨1485, by rfl⟩ : syracuseStep 253525 = 2971) (by norm_num)
theorem B450173 : Blo 183802 450173 := bbase (se 3 (by rfl) ⟨84407, by rfl⟩ : syracuseStep 450173 = 168815) (by norm_num)
theorem B417437 : Blo 183802 417437 := bbase (se 3 (by rfl) ⟨78269, by rfl⟩ : syracuseStep 417437 = 156539) (by norm_num)
theorem B220853 : Blo 183802 220853 := bbase (se 5 (by rfl) ⟨10352, by rfl⟩ : syracuseStep 220853 = 20705) (by norm_num)
theorem B417509 : Blo 183802 417509 := bbase (se 4 (by rfl) ⟨39141, by rfl⟩ : syracuseStep 417509 = 78283) (by norm_num)
theorem B450317 : Blo 183802 450317 := bbase (se 3 (by rfl) ⟨84434, by rfl⟩ : syracuseStep 450317 = 168869) (by norm_num)
theorem B417581 : Blo 183802 417581 := bbase (se 3 (by rfl) ⟨78296, by rfl⟩ : syracuseStep 417581 = 156593) (by norm_num)
theorem B417653 : Blo 183802 417653 := bbase (se 5 (by rfl) ⟨19577, by rfl⟩ : syracuseStep 417653 = 39155) (by norm_num)
theorem B712597 : Blo 183802 712597 := bbase (se 6 (by rfl) ⟨16701, by rfl⟩ : syracuseStep 712597 = 33403) (by norm_num)
theorem B319405 : Blo 183802 319405 := bbase (se 3 (by rfl) ⟨59888, by rfl⟩ : syracuseStep 319405 = 119777) (by norm_num)
theorem B417725 : Blo 183802 417725 := bbase (se 3 (by rfl) ⟨78323, by rfl⟩ : syracuseStep 417725 = 156647) (by norm_num)
theorem B417797 : Blo 183802 417797 := bbase (se 4 (by rfl) ⟨39168, by rfl⟩ : syracuseStep 417797 = 78337) (by norm_num)
theorem B450629 : Blo 183802 450629 := bbase (se 4 (by rfl) ⟨42246, by rfl⟩ : syracuseStep 450629 = 84493) (by norm_num)
theorem B417869 : Blo 183802 417869 := bbase (se 3 (by rfl) ⟨78350, by rfl⟩ : syracuseStep 417869 = 156701) (by norm_num)
theorem B221329 : Blo 183802 221329 := bbase (se 2 (by rfl) ⟨82998, by rfl⟩ : syracuseStep 221329 = 165997) (by norm_num)
theorem B1597589 : Blo 183802 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B417941 : Blo 183802 417941 := bbase (se 6 (by rfl) ⟨9795, by rfl⟩ : syracuseStep 417941 = 19591) (by norm_num)
theorem B221357 : Blo 183802 221357 := bbase (se 3 (by rfl) ⟨41504, by rfl⟩ : syracuseStep 221357 = 83009) (by norm_num)
theorem B712901 : Blo 183802 712901 := bbase (se 4 (by rfl) ⟨66834, by rfl⟩ : syracuseStep 712901 = 133669) (by norm_num)
theorem B418013 : Blo 183802 418013 := bbase (se 3 (by rfl) ⟨78377, by rfl⟩ : syracuseStep 418013 = 156755) (by norm_num)
theorem B352525 : Blo 183802 352525 := bbase (se 3 (by rfl) ⟨66098, by rfl⟩ : syracuseStep 352525 = 132197) (by norm_num)
theorem B909605 : Blo 183802 909605 := bbase (se 4 (by rfl) ⟨85275, by rfl⟩ : syracuseStep 909605 = 170551) (by norm_num)
theorem B254245 : Blo 183802 254245 := bbase (se 4 (by rfl) ⟨23835, by rfl⟩ : syracuseStep 254245 = 47671) (by norm_num)
theorem B418085 : Blo 183802 418085 := bbase (se 4 (by rfl) ⟨39195, by rfl⟩ : syracuseStep 418085 = 78391) (by norm_num)
theorem B680293 : Blo 183802 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B221545 : Blo 183802 221545 := bbase (se 2 (by rfl) ⟨83079, by rfl⟩ : syracuseStep 221545 = 166159) (by norm_num)
theorem B418157 : Blo 183802 418157 := bbase (se 3 (by rfl) ⟨78404, by rfl⟩ : syracuseStep 418157 = 156809) (by norm_num)
theorem B352669 : Blo 183802 352669 := bbase (se 3 (by rfl) ⟨66125, by rfl⟩ : syracuseStep 352669 = 132251) (by norm_num)
theorem B418229 : Blo 183802 418229 := bbase (se 5 (by rfl) ⟨19604, by rfl⟩ : syracuseStep 418229 = 39209) (by norm_num)
theorem B1597877 : Blo 183802 1597877 := bbase (se 5 (by rfl) ⟨74900, by rfl⟩ : syracuseStep 1597877 = 149801) (by norm_num)
theorem B221665 : Blo 183802 221665 := bbase (se 2 (by rfl) ⟨83124, by rfl⟩ : syracuseStep 221665 = 166249) (by norm_num)
theorem B418301 : Blo 183802 418301 := bbase (se 3 (by rfl) ⟨78431, by rfl⟩ : syracuseStep 418301 = 156863) (by norm_num)
theorem B352829 : Blo 183802 352829 := bbase (se 3 (by rfl) ⟨66155, by rfl⟩ : syracuseStep 352829 = 132311) (by norm_num)
theorem B418373 : Blo 183802 418373 := bbase (se 4 (by rfl) ⟨39222, by rfl⟩ : syracuseStep 418373 = 78445) (by norm_num)
theorem B942677 : Blo 183802 942677 := bbase (se 8 (by rfl) ⟨5523, by rfl⟩ : syracuseStep 942677 = 11047) (by norm_num)
theorem B418445 : Blo 183802 418445 := bbase (se 3 (by rfl) ⟨78458, by rfl⟩ : syracuseStep 418445 = 156917) (by norm_num)
theorem B189073 : Blo 183802 189073 := bbase (se 2 (by rfl) ⟨70902, by rfl⟩ : syracuseStep 189073 = 141805) (by norm_num)
theorem B352973 : Blo 183802 352973 := bbase (se 3 (by rfl) ⟨66182, by rfl⟩ : syracuseStep 352973 = 132365) (by norm_num)
theorem B418517 : Blo 183802 418517 := bbase (se 7 (by rfl) ⟨4904, by rfl⟩ : syracuseStep 418517 = 9809) (by norm_num)
theorem B418589 : Blo 183802 418589 := bbase (se 3 (by rfl) ⟨78485, by rfl⟩ : syracuseStep 418589 = 156971) (by norm_num)
theorem B418661 : Blo 183802 418661 := bbase (se 4 (by rfl) ⟨39249, by rfl⟩ : syracuseStep 418661 = 78499) (by norm_num)
theorem B418733 : Blo 183802 418733 := bbase (se 3 (by rfl) ⟨78512, by rfl⟩ : syracuseStep 418733 = 157025) (by norm_num)
theorem B189365 : Blo 183802 189365 := bbase (se 5 (by rfl) ⟨8876, by rfl⟩ : syracuseStep 189365 = 17753) (by norm_num)
theorem B353261 : Blo 183802 353261 := bbase (se 3 (by rfl) ⟨66236, by rfl⟩ : syracuseStep 353261 = 132473) (by norm_num)
theorem B418805 : Blo 183802 418805 := bbase (se 5 (by rfl) ⟨19631, by rfl⟩ : syracuseStep 418805 = 39263) (by norm_num)
theorem B418877 : Blo 183802 418877 := bbase (se 3 (by rfl) ⟨78539, by rfl⟩ : syracuseStep 418877 = 157079) (by norm_num)
theorem B353413 : Blo 183802 353413 := bbase (se 4 (by rfl) ⟨33132, by rfl⟩ : syracuseStep 353413 = 66265) (by norm_num)
theorem B418949 : Blo 183802 418949 := bbase (se 4 (by rfl) ⟨39276, by rfl⟩ : syracuseStep 418949 = 78553) (by norm_num)
theorem B419021 : Blo 183802 419021 := bbase (se 3 (by rfl) ⟨78566, by rfl⟩ : syracuseStep 419021 = 157133) (by norm_num)
theorem B419093 : Blo 183802 419093 := bbase (se 6 (by rfl) ⟨9822, by rfl⟩ : syracuseStep 419093 = 19645) (by norm_num)
theorem B419165 : Blo 183802 419165 := bbase (se 3 (by rfl) ⟨78593, by rfl⟩ : syracuseStep 419165 = 157187) (by norm_num)
theorem B419237 : Blo 183802 419237 := bbase (se 4 (by rfl) ⟨39303, by rfl⟩ : syracuseStep 419237 = 78607) (by norm_num)
theorem B353717 : Blo 183802 353717 := bbase (se 5 (by rfl) ⟨16580, by rfl⟩ : syracuseStep 353717 = 33161) (by norm_num)
theorem B419309 : Blo 183802 419309 := bbase (se 3 (by rfl) ⟨78620, by rfl⟩ : syracuseStep 419309 = 157241) (by norm_num)
theorem B419381 : Blo 183802 419381 := bbase (se 5 (by rfl) ⟨19658, by rfl⟩ : syracuseStep 419381 = 39317) (by norm_num)
theorem B419453 : Blo 183802 419453 := bbase (se 3 (by rfl) ⟨78647, by rfl⟩ : syracuseStep 419453 = 157295) (by norm_num)
theorem B419525 : Blo 183802 419525 := bbase (se 4 (by rfl) ⟨39330, by rfl⟩ : syracuseStep 419525 = 78661) (by norm_num)
theorem B419597 : Blo 183802 419597 := bbase (se 3 (by rfl) ⟨78674, by rfl⟩ : syracuseStep 419597 = 157349) (by norm_num)
theorem B419669 : Blo 183802 419669 := bbase (se 9 (by rfl) ⟨1229, by rfl⟩ : syracuseStep 419669 = 2459) (by norm_num)
theorem B943973 : Blo 183802 943973 := bbase (se 4 (by rfl) ⟨88497, by rfl⟩ : syracuseStep 943973 = 176995) (by norm_num)
theorem B419741 : Blo 183802 419741 := bbase (se 3 (by rfl) ⟨78701, by rfl⟩ : syracuseStep 419741 = 157403) (by norm_num)
theorem B419813 : Blo 183802 419813 := bbase (se 4 (by rfl) ⟨39357, by rfl⟩ : syracuseStep 419813 = 78715) (by norm_num)
theorem B223241 : Blo 183802 223241 := bbase (se 2 (by rfl) ⟨83715, by rfl⟩ : syracuseStep 223241 = 167431) (by norm_num)
theorem B419885 : Blo 183802 419885 := bbase (se 3 (by rfl) ⟨78728, by rfl⟩ : syracuseStep 419885 = 157457) (by norm_num)
theorem B911477 : Blo 183802 911477 := bbase (se 5 (by rfl) ⟨42725, by rfl⟩ : syracuseStep 911477 = 85451) (by norm_num)
theorem B419957 : Blo 183802 419957 := bbase (se 5 (by rfl) ⟨19685, by rfl⟩ : syracuseStep 419957 = 39371) (by norm_num)
theorem B354469 : Blo 183802 354469 := bbase (se 4 (by rfl) ⟨33231, by rfl⟩ : syracuseStep 354469 = 66463) (by norm_num)
theorem B420029 : Blo 183802 420029 := bbase (se 3 (by rfl) ⟨78755, by rfl⟩ : syracuseStep 420029 = 157511) (by norm_num)
theorem B420101 : Blo 183802 420101 := bbase (se 4 (by rfl) ⟨39384, by rfl⟩ : syracuseStep 420101 = 78769) (by norm_num)
theorem B354613 : Blo 183802 354613 := bbase (se 5 (by rfl) ⟨16622, by rfl⟩ : syracuseStep 354613 = 33245) (by norm_num)
theorem B420173 : Blo 183802 420173 := bbase (se 3 (by rfl) ⟨78782, by rfl⟩ : syracuseStep 420173 = 157565) (by norm_num)
theorem B4811093 : Blo 183802 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B420245 : Blo 183802 420245 := bbase (se 6 (by rfl) ⟨9849, by rfl⟩ : syracuseStep 420245 = 19699) (by norm_num)
theorem B354773 : Blo 183802 354773 := bbase (se 7 (by rfl) ⟨4157, by rfl⟩ : syracuseStep 354773 = 8315) (by norm_num)
theorem B420317 : Blo 183802 420317 := bbase (se 3 (by rfl) ⟨78809, by rfl⟩ : syracuseStep 420317 = 157619) (by norm_num)
theorem B420389 : Blo 183802 420389 := bbase (se 4 (by rfl) ⟨39411, by rfl⟩ : syracuseStep 420389 = 78823) (by norm_num)
theorem B354917 : Blo 183802 354917 := bbase (se 4 (by rfl) ⟨33273, by rfl⟩ : syracuseStep 354917 = 66547) (by norm_num)
theorem B420461 : Blo 183802 420461 := bbase (se 3 (by rfl) ⟨78836, by rfl⟩ : syracuseStep 420461 = 157673) (by norm_num)
theorem B420533 : Blo 183802 420533 := bbase (se 5 (by rfl) ⟨19712, by rfl⟩ : syracuseStep 420533 = 39425) (by norm_num)
theorem B223933 : Blo 183802 223933 := bbase (se 3 (by rfl) ⟨41987, by rfl⟩ : syracuseStep 223933 = 83975) (by norm_num)
theorem B420605 : Blo 183802 420605 := bbase (se 3 (by rfl) ⟨78863, by rfl⟩ : syracuseStep 420605 = 157727) (by norm_num)
theorem B224029 : Blo 183802 224029 := bbase (se 3 (by rfl) ⟨42005, by rfl⟩ : syracuseStep 224029 = 84011) (by norm_num)
theorem B420677 : Blo 183802 420677 := bbase (se 4 (by rfl) ⟨39438, by rfl⟩ : syracuseStep 420677 = 78877) (by norm_num)
theorem B4025173 : Blo 183802 4025173 := bbase (se 9 (by rfl) ⟨11792, by rfl⟩ : syracuseStep 4025173 = 23585) (by norm_num)
theorem B355205 : Blo 183802 355205 := bbase (se 4 (by rfl) ⟨33300, by rfl⟩ : syracuseStep 355205 = 66601) (by norm_num)
theorem B420749 : Blo 183802 420749 := bbase (se 3 (by rfl) ⟨78890, by rfl⟩ : syracuseStep 420749 = 157781) (by norm_num)
theorem B420821 : Blo 183802 420821 := bbase (se 7 (by rfl) ⟨4931, by rfl⟩ : syracuseStep 420821 = 9863) (by norm_num)
theorem B191489 : Blo 183802 191489 := bbase (se 2 (by rfl) ⟨71808, by rfl⟩ : syracuseStep 191489 = 143617) (by norm_num)
theorem B420893 : Blo 183802 420893 := bbase (se 3 (by rfl) ⟨78917, by rfl⟩ : syracuseStep 420893 = 157835) (by norm_num)
theorem B355357 : Blo 183802 355357 := bbase (se 3 (by rfl) ⟨66629, by rfl⟩ : syracuseStep 355357 = 133259) (by norm_num)
theorem B420965 : Blo 183802 420965 := bbase (se 4 (by rfl) ⟨39465, by rfl⟩ : syracuseStep 420965 = 78931) (by norm_num)
theorem B945269 : Blo 183802 945269 := bbase (se 5 (by rfl) ⟨44309, by rfl⟩ : syracuseStep 945269 = 88619) (by norm_num)
theorem B1404053 : Blo 183802 1404053 := bbase (se 6 (by rfl) ⟨32907, by rfl⟩ : syracuseStep 1404053 = 65815) (by norm_num)
theorem B421037 : Blo 183802 421037 := bbase (se 3 (by rfl) ⟨78944, by rfl⟩ : syracuseStep 421037 = 157889) (by norm_num)
theorem B1338581 : Blo 183802 1338581 := bbase (se 7 (by rfl) ⟨15686, by rfl⟩ : syracuseStep 1338581 = 31373) (by norm_num)
theorem B421109 : Blo 183802 421109 := bbase (se 5 (by rfl) ⟨19739, by rfl⟩ : syracuseStep 421109 = 39479) (by norm_num)
theorem B421181 : Blo 183802 421181 := bbase (se 3 (by rfl) ⟨78971, by rfl⟩ : syracuseStep 421181 = 157943) (by norm_num)
theorem B355661 : Blo 183802 355661 := bbase (se 3 (by rfl) ⟨66686, by rfl⟩ : syracuseStep 355661 = 133373) (by norm_num)
theorem B421253 : Blo 183802 421253 := bbase (se 4 (by rfl) ⟨39492, by rfl⟩ : syracuseStep 421253 = 78985) (by norm_num)
theorem B716197 : Blo 183802 716197 := bbase (se 4 (by rfl) ⟨67143, by rfl⟩ : syracuseStep 716197 = 134287) (by norm_num)
theorem B421325 : Blo 183802 421325 := bbase (se 3 (by rfl) ⟨78998, by rfl⟩ : syracuseStep 421325 = 157997) (by norm_num)
theorem B421397 : Blo 183802 421397 := bbase (se 6 (by rfl) ⟨9876, by rfl⟩ : syracuseStep 421397 = 19753) (by norm_num)
theorem B224813 : Blo 183802 224813 := bbase (se 3 (by rfl) ⟨42152, by rfl⟩ : syracuseStep 224813 = 84305) (by norm_num)
theorem B192065 : Blo 183802 192065 := bbase (se 2 (by rfl) ⟨72024, by rfl⟩ : syracuseStep 192065 = 144049) (by norm_num)
theorem B224857 : Blo 183802 224857 := bbase (se 2 (by rfl) ⟨84321, by rfl⟩ : syracuseStep 224857 = 168643) (by norm_num)
theorem B421469 : Blo 183802 421469 := bbase (se 3 (by rfl) ⟨79025, by rfl⟩ : syracuseStep 421469 = 158051) (by norm_num)
theorem B355981 : Blo 183802 355981 := bbase (se 3 (by rfl) ⟨66746, by rfl⟩ : syracuseStep 355981 = 133493) (by norm_num)
theorem B421541 : Blo 183802 421541 := bbase (se 4 (by rfl) ⟨39519, by rfl⟩ : syracuseStep 421541 = 79039) (by norm_num)
theorem B421613 : Blo 183802 421613 := bbase (se 3 (by rfl) ⟨79052, by rfl⟩ : syracuseStep 421613 = 158105) (by norm_num)
theorem B421685 : Blo 183802 421685 := bbase (se 5 (by rfl) ⟨19766, by rfl⟩ : syracuseStep 421685 = 39533) (by norm_num)
theorem B225121 : Blo 183802 225121 := bbase (se 2 (by rfl) ⟨84420, by rfl⟩ : syracuseStep 225121 = 168841) (by norm_num)
theorem B421757 : Blo 183802 421757 := bbase (se 3 (by rfl) ⟨79079, by rfl⟩ : syracuseStep 421757 = 158159) (by norm_num)
theorem B421829 : Blo 183802 421829 := bbase (se 4 (by rfl) ⟨39546, by rfl⟩ : syracuseStep 421829 = 79093) (by norm_num)
theorem B421901 : Blo 183802 421901 := bbase (se 3 (by rfl) ⟨79106, by rfl⟩ : syracuseStep 421901 = 158213) (by norm_num)
theorem B356413 : Blo 183802 356413 := bbase (se 3 (by rfl) ⟨66827, by rfl⟩ : syracuseStep 356413 = 133655) (by norm_num)
theorem B421973 : Blo 183802 421973 := bbase (se 8 (by rfl) ⟨2472, by rfl⟩ : syracuseStep 421973 = 4945) (by norm_num)
theorem B323693 : Blo 183802 323693 := bbase (se 3 (by rfl) ⟨60692, by rfl⟩ : syracuseStep 323693 = 121385) (by norm_num)
theorem B389269 : Blo 183802 389269 := bbase (se 6 (by rfl) ⟨9123, by rfl⟩ : syracuseStep 389269 = 18247) (by norm_num)
theorem B422045 : Blo 183802 422045 := bbase (se 3 (by rfl) ⟨79133, by rfl⟩ : syracuseStep 422045 = 158267) (by norm_num)
theorem B422117 : Blo 183802 422117 := bbase (se 4 (by rfl) ⟨39573, by rfl⟩ : syracuseStep 422117 = 79147) (by norm_num)
theorem B225509 : Blo 183802 225509 := bbase (se 4 (by rfl) ⟨21141, by rfl⟩ : syracuseStep 225509 = 42283) (by norm_num)
theorem B422189 : Blo 183802 422189 := bbase (se 3 (by rfl) ⟨79160, by rfl⟩ : syracuseStep 422189 = 158321) (by norm_num)
theorem B422261 : Blo 183802 422261 := bbase (se 5 (by rfl) ⟨19793, by rfl⟩ : syracuseStep 422261 = 39587) (by norm_num)
theorem B946565 : Blo 183802 946565 := bbase (se 4 (by rfl) ⟨88740, by rfl⟩ : syracuseStep 946565 = 177481) (by norm_num)
theorem B422333 : Blo 183802 422333 := bbase (se 3 (by rfl) ⟨79187, by rfl⟩ : syracuseStep 422333 = 158375) (by norm_num)
theorem B422405 : Blo 183802 422405 := bbase (se 4 (by rfl) ⟨39600, by rfl⟩ : syracuseStep 422405 = 79201) (by norm_num)
theorem B422477 : Blo 183802 422477 := bbase (se 3 (by rfl) ⟨79214, by rfl⟩ : syracuseStep 422477 = 158429) (by norm_num)
theorem B422549 : Blo 183802 422549 := bbase (se 6 (by rfl) ⟨9903, by rfl⟩ : syracuseStep 422549 = 19807) (by norm_num)
theorem B1504021 : Blo 183802 1504021 := bbase (se 6 (by rfl) ⟨35250, by rfl⟩ : syracuseStep 1504021 = 70501) (by norm_num)
theorem B750389 : Blo 183802 750389 := bbase (se 5 (by rfl) ⟨35174, by rfl⟩ : syracuseStep 750389 = 70349) (by norm_num)
theorem B455557 : Blo 183802 455557 := bbase (se 4 (by rfl) ⟨42708, by rfl⟩ : syracuseStep 455557 = 85417) (by norm_num)
theorem B1766549 : Blo 183802 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B1340597 : Blo 183802 1340597 := bbase (se 5 (by rfl) ⟨62840, by rfl⟩ : syracuseStep 1340597 = 125681) (by norm_num)
theorem B423245 : Blo 183802 423245 := bbase (se 3 (by rfl) ⟨79358, by rfl⟩ : syracuseStep 423245 = 158717) (by norm_num)
theorem B456245 : Blo 183802 456245 := bbase (se 5 (by rfl) ⟨21386, by rfl⟩ : syracuseStep 456245 = 42773) (by norm_num)
theorem B292405 : Blo 183802 292405 := bbase (se 5 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 292405 = 27413) (by norm_num)
theorem B1799765 : Blo 183802 1799765 := bbase (se 8 (by rfl) ⟨10545, by rfl⟩ : syracuseStep 1799765 = 21091) (by norm_num)
theorem B947861 : Blo 183802 947861 := bbase (se 6 (by rfl) ⟨22215, by rfl⟩ : syracuseStep 947861 = 44431) (by norm_num)
theorem B620405 : Blo 183802 620405 := bbase (se 5 (by rfl) ⟨29081, by rfl⟩ : syracuseStep 620405 = 58163) (by norm_num)
theorem B620837 : Blo 183802 620837 := bbase (se 4 (by rfl) ⟨58203, by rfl⟩ : syracuseStep 620837 = 116407) (by norm_num)
theorem B621269 : Blo 183802 621269 := bbase (se 7 (by rfl) ⟨7280, by rfl⟩ : syracuseStep 621269 = 14561) (by norm_num)
theorem B949157 : Blo 183802 949157 := bbase (se 4 (by rfl) ⟨88983, by rfl⟩ : syracuseStep 949157 = 177967) (by norm_num)
theorem B752645 : Blo 183802 752645 := bbase (se 4 (by rfl) ⟨70560, by rfl⟩ : syracuseStep 752645 = 141121) (by norm_num)
theorem B621701 : Blo 183802 621701 := bbase (se 4 (by rfl) ⟨58284, by rfl⟩ : syracuseStep 621701 = 116569) (by norm_num)
theorem B425197 : Blo 183802 425197 := bbase (se 3 (by rfl) ⟨79724, by rfl⟩ : syracuseStep 425197 = 159449) (by norm_num)
theorem B425261 : Blo 183802 425261 := bbase (se 3 (by rfl) ⟨79736, by rfl⟩ : syracuseStep 425261 = 159473) (by norm_num)
theorem B523685 : Blo 183802 523685 := bbase (se 4 (by rfl) ⟨49095, by rfl⟩ : syracuseStep 523685 = 98191) (by norm_num)
theorem B622133 : Blo 183802 622133 := bbase (se 5 (by rfl) ⟨29162, by rfl⟩ : syracuseStep 622133 = 58325) (by norm_num)
theorem B392789 : Blo 183802 392789 := bbase (se 8 (by rfl) ⟨2301, by rfl⟩ : syracuseStep 392789 = 4603) (by norm_num)
theorem B294605 : Blo 183802 294605 := bbase (se 3 (by rfl) ⟨55238, by rfl⟩ : syracuseStep 294605 = 110477) (by norm_num)
theorem B294797 : Blo 183802 294797 := bbase (se 3 (by rfl) ⟨55274, by rfl⟩ : syracuseStep 294797 = 110549) (by norm_num)
theorem B196553 : Blo 183802 196553 := bbase (se 2 (by rfl) ⟨73707, by rfl⟩ : syracuseStep 196553 = 147415) (by norm_num)
theorem B622565 : Blo 183802 622565 := bbase (se 4 (by rfl) ⟨58365, by rfl⟩ : syracuseStep 622565 = 116731) (by norm_num)
theorem B524333 : Blo 183802 524333 := bstep (se 3 (by rfl) ⟨98312, by rfl⟩ : syracuseStep 524333 = 196625) B196625
theorem B622673 : Blo 183802 622673 := bstep (se 2 (by rfl) ⟨233502, by rfl⟩ : syracuseStep 622673 = 467005) B467005
theorem B295105 : Blo 183802 295105 := bstep (se 2 (by rfl) ⟨110664, by rfl⟩ : syracuseStep 295105 = 221329) B221329
theorem B262435 : Blo 183802 262435 := bstep (se 1 (by rfl) ⟨196826, by rfl⟩ : syracuseStep 262435 = 393653) B393653
theorem B262531 : Blo 183802 262531 := bstep (se 1 (by rfl) ⟨196898, by rfl⟩ : syracuseStep 262531 = 393797) B393797
theorem B3015053 : Blo 183802 3015053 := bstep (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) B1130645
theorem B590285 : Blo 183802 590285 := bstep (se 3 (by rfl) ⟨110678, by rfl⟩ : syracuseStep 590285 = 221357) B221357
theorem B360931 : Blo 183802 360931 := bstep (se 1 (by rfl) ⟨270698, by rfl⟩ : syracuseStep 360931 = 541397) B541397
theorem B393763 : Blo 183802 393763 := bstep (se 1 (by rfl) ⟨295322, by rfl⟩ : syracuseStep 393763 = 590645) B590645
theorem B197155 : Blo 183802 197155 := bstep (se 1 (by rfl) ⟨147866, by rfl⟩ : syracuseStep 197155 = 295733) B295733
theorem B623213 : Blo 183802 623213 := bstep (se 3 (by rfl) ⟨116852, by rfl⟩ : syracuseStep 623213 = 233705) B233705
theorem B295553 : Blo 183802 295553 := bstep (se 2 (by rfl) ⟨110832, by rfl⟩ : syracuseStep 295553 = 221665) B221665
theorem B623267 : Blo 183802 623267 := bstep (se 1 (by rfl) ⟨467450, by rfl⟩ : syracuseStep 623267 = 934901) B934901
theorem B721649 : Blo 183802 721649 := bstep (se 2 (by rfl) ⟨270618, by rfl⟩ : syracuseStep 721649 = 541237) B541237
theorem B197411 : Blo 183802 197411 := bstep (se 1 (by rfl) ⟨148058, by rfl⟩ : syracuseStep 197411 = 296117) B296117
theorem B263027 : Blo 183802 263027 := bstep (se 1 (by rfl) ⟨197270, by rfl⟩ : syracuseStep 263027 = 394541) B394541
theorem B590723 : Blo 183802 590723 := bstep (se 1 (by rfl) ⟨443042, by rfl⟩ : syracuseStep 590723 = 886085) B886085
theorem B2098061 : Blo 183802 2098061 := bstep (se 3 (by rfl) ⟨393386, by rfl⟩ : syracuseStep 2098061 = 786773) B786773
theorem B623537 : Blo 183802 623537 := bstep (se 2 (by rfl) ⟨233826, by rfl⟩ : syracuseStep 623537 = 467653) B467653
theorem B1868771 : Blo 183802 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B787441 : Blo 183802 787441 := bstep (se 2 (by rfl) ⟨295290, by rfl⟩ : syracuseStep 787441 = 590581) B590581
theorem B525325 : Blo 183802 525325 := bstep (se 3 (by rfl) ⟨98498, by rfl⟩ : syracuseStep 525325 = 196997) B196997
theorem B1049669 : Blo 183802 1049669 := bstep (se 4 (by rfl) ⟨98406, by rfl⟩ : syracuseStep 1049669 = 196813) B196813
theorem B951587 : Blo 183802 951587 := bstep (se 1 (by rfl) ⟨713690, by rfl⟩ : syracuseStep 951587 = 1427381) B1427381
theorem B624077 : Blo 183802 624077 := bstep (se 3 (by rfl) ⟨117014, by rfl⟩ : syracuseStep 624077 = 234029) B234029
theorem B263665 : Blo 183802 263665 := bstep (se 2 (by rfl) ⟨98874, by rfl⟩ : syracuseStep 263665 = 197749) B197749
theorem B624131 : Blo 183802 624131 := bstep (se 1 (by rfl) ⟨468098, by rfl⟩ : syracuseStep 624131 = 936197) B936197
theorem B198163 : Blo 183802 198163 := bstep (se 1 (by rfl) ⟨148622, by rfl⟩ : syracuseStep 198163 = 297245) B297245
theorem B1050353 : Blo 183802 1050353 := bstep (se 2 (by rfl) ⟨393882, by rfl⟩ : syracuseStep 1050353 = 787765) B787765
theorem B394993 : Blo 183802 394993 := bstep (se 2 (by rfl) ⟨148122, by rfl⟩ : syracuseStep 394993 = 296245) B296245
theorem B624401 : Blo 183802 624401 := bstep (se 2 (by rfl) ⟨234150, by rfl⟩ : syracuseStep 624401 = 468301) B468301
theorem B264001 : Blo 183802 264001 := bstep (se 2 (by rfl) ⟨99000, by rfl⟩ : syracuseStep 264001 = 198001) B198001
theorem B1181573 : Blo 183802 1181573 := bstep (se 4 (by rfl) ⟨110772, by rfl⟩ : syracuseStep 1181573 = 221545) B221545
theorem B296963 : Blo 183802 296963 := bstep (se 1 (by rfl) ⟨222722, by rfl⟩ : syracuseStep 296963 = 445445) B445445
theorem B2001037 : Blo 183802 2001037 := bstep (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) B750389
theorem B297155 : Blo 183802 297155 := bstep (se 1 (by rfl) ⟨222866, by rfl⟩ : syracuseStep 297155 = 445733) B445733
theorem B624941 : Blo 183802 624941 := bstep (se 3 (by rfl) ⟨117176, by rfl⟩ : syracuseStep 624941 = 234353) B234353
theorem B624995 : Blo 183802 624995 := bstep (se 1 (by rfl) ⟨468746, by rfl⟩ : syracuseStep 624995 = 937493) B937493
theorem B756067 : Blo 183802 756067 := bstep (se 1 (by rfl) ⟨567050, by rfl⟩ : syracuseStep 756067 = 1134101) B1134101
theorem B264593 : Blo 183802 264593 := bstep (se 2 (by rfl) ⟨99222, by rfl⟩ : syracuseStep 264593 = 198445) B198445
theorem B395779 : Blo 183802 395779 := bstep (se 1 (by rfl) ⟨296834, by rfl⟩ : syracuseStep 395779 = 593669) B593669
theorem B625265 : Blo 183802 625265 := bstep (se 2 (by rfl) ⟨234474, by rfl⟩ : syracuseStep 625265 = 468949) B468949
theorem B527057 : Blo 183802 527057 := bstep (se 2 (by rfl) ⟨197646, by rfl⟩ : syracuseStep 527057 = 395293) B395293
theorem B592643 : Blo 183802 592643 := bstep (se 1 (by rfl) ⟨444482, by rfl⟩ : syracuseStep 592643 = 888965) B888965
theorem B199427 : Blo 183802 199427 := bstep (se 1 (by rfl) ⟨149570, by rfl⟩ : syracuseStep 199427 = 299141) B299141
theorem B527249 : Blo 183802 527249 := bstep (se 2 (by rfl) ⟨197718, by rfl⟩ : syracuseStep 527249 = 395437) B395437
theorem B265123 : Blo 183802 265123 := bstep (se 1 (by rfl) ⟨198842, by rfl⟩ : syracuseStep 265123 = 397685) B397685
theorem B625805 : Blo 183802 625805 := bstep (se 3 (by rfl) ⟨117338, by rfl⟩ : syracuseStep 625805 = 234677) B234677
theorem B3574925 : Blo 183802 3574925 := bstep (se 3 (by rfl) ⟨670298, by rfl⟩ : syracuseStep 3574925 = 1340597) B1340597
theorem B1051811 : Blo 183802 1051811 := bstep (se 1 (by rfl) ⟨788858, by rfl⟩ : syracuseStep 1051811 = 1577717) B1577717
theorem B756913 : Blo 183802 756913 := bstep (se 2 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 756913 = 567685) B567685
theorem B232627 : Blo 183802 232627 := bstep (se 1 (by rfl) ⟨174470, by rfl⟩ : syracuseStep 232627 = 348941) B348941
theorem B625859 : Blo 183802 625859 := bstep (se 1 (by rfl) ⟨469394, by rfl⟩ : syracuseStep 625859 = 938789) B938789
theorem B396497 : Blo 183802 396497 := bstep (se 2 (by rfl) ⟨148686, by rfl⟩ : syracuseStep 396497 = 297373) B297373
theorem B265459 : Blo 183802 265459 := bstep (se 1 (by rfl) ⟨199094, by rfl⟩ : syracuseStep 265459 = 398189) B398189
theorem B232723 : Blo 183802 232723 := bstep (se 1 (by rfl) ⟨174542, by rfl⟩ : syracuseStep 232723 = 349085) B349085
theorem B626129 : Blo 183802 626129 := bstep (se 2 (by rfl) ⟨234798, by rfl⟩ : syracuseStep 626129 = 469597) B469597
theorem B200179 : Blo 183802 200179 := bstep (se 1 (by rfl) ⟨150134, by rfl⟩ : syracuseStep 200179 = 300269) B300269
theorem B298577 : Blo 183802 298577 := bstep (se 2 (by rfl) ⟨111966, by rfl⟩ : syracuseStep 298577 = 223933) B223933
theorem B397009 : Blo 183802 397009 := bstep (se 2 (by rfl) ⟨148878, by rfl⟩ : syracuseStep 397009 = 297757) B297757
theorem B2100977 : Blo 183802 2100977 := bstep (se 2 (by rfl) ⟨787866, by rfl⟩ : syracuseStep 2100977 = 1575733) B1575733
theorem B233219 : Blo 183802 233219 := bstep (se 1 (by rfl) ⟨174914, by rfl⟩ : syracuseStep 233219 = 349829) B349829
theorem B266017 : Blo 183802 266017 := bstep (se 2 (by rfl) ⟨99756, by rfl⟩ : syracuseStep 266017 = 199513) B199513
theorem B266051 : Blo 183802 266051 := bstep (se 1 (by rfl) ⟨199538, by rfl⟩ : syracuseStep 266051 = 399077) B399077
theorem B528241 : Blo 183802 528241 := bstep (se 2 (by rfl) ⟨198090, by rfl⟩ : syracuseStep 528241 = 396181) B396181
theorem B790499 : Blo 183802 790499 := bstep (se 1 (by rfl) ⟨592874, by rfl⟩ : syracuseStep 790499 = 1185749) B1185749
theorem B626669 : Blo 183802 626669 := bstep (se 3 (by rfl) ⟨117500, by rfl⟩ : syracuseStep 626669 = 235001) B235001
theorem B331793 : Blo 183802 331793 := bstep (se 2 (by rfl) ⟨124422, by rfl⟩ : syracuseStep 331793 = 248845) B248845
theorem B626723 : Blo 183802 626723 := bstep (se 1 (by rfl) ⟨470042, by rfl⟩ : syracuseStep 626723 = 940085) B940085
theorem B528515 : Blo 183802 528515 := bstep (se 1 (by rfl) ⟨396386, by rfl⟩ : syracuseStep 528515 = 792773) B792773
theorem B626993 : Blo 183802 626993 := bstep (se 2 (by rfl) ⟨235122, by rfl⟩ : syracuseStep 626993 = 470245) B470245
theorem B528707 : Blo 183802 528707 := bstep (se 1 (by rfl) ⟨396530, by rfl⟩ : syracuseStep 528707 = 793061) B793061
theorem B266609 : Blo 183802 266609 := bstep (se 2 (by rfl) ⟨99978, by rfl⟩ : syracuseStep 266609 = 199957) B199957
theorem B332209 : Blo 183802 332209 := bstep (se 2 (by rfl) ⟨124578, by rfl⟩ : syracuseStep 332209 = 249157) B249157
theorem B266689 : Blo 183802 266689 := bstep (se 2 (by rfl) ⟨100008, by rfl⟩ : syracuseStep 266689 = 200017) B200017
theorem B233923 : Blo 183802 233923 := bstep (se 1 (by rfl) ⟨175442, by rfl⟩ : syracuseStep 233923 = 350885) B350885
theorem B234019 : Blo 183802 234019 := bstep (se 1 (by rfl) ⟨175514, by rfl⟩ : syracuseStep 234019 = 351029) B351029
theorem B954929 : Blo 183802 954929 := bstep (se 2 (by rfl) ⟨358098, by rfl⟩ : syracuseStep 954929 = 716197) B716197
theorem B1413773 : Blo 183802 1413773 := bstep (se 3 (by rfl) ⟨265082, by rfl⟩ : syracuseStep 1413773 = 530165) B530165
theorem B299809 : Blo 183802 299809 := bstep (se 2 (by rfl) ⟨112428, by rfl⟩ : syracuseStep 299809 = 224857) B224857
theorem B627533 : Blo 183802 627533 := bstep (se 3 (by rfl) ⟨117662, by rfl⟩ : syracuseStep 627533 = 235325) B235325
theorem B627587 : Blo 183802 627587 := bstep (se 1 (by rfl) ⟨470690, by rfl⟩ : syracuseStep 627587 = 941381) B941381
theorem B234515 : Blo 183802 234515 := bstep (se 1 (by rfl) ⟨175886, by rfl⟩ : syracuseStep 234515 = 351773) B351773
theorem B562211 : Blo 183802 562211 := bstep (se 1 (by rfl) ⟨421658, by rfl⟩ : syracuseStep 562211 = 843317) B843317
theorem B300115 : Blo 183802 300115 := bstep (se 1 (by rfl) ⟨225086, by rfl⟩ : syracuseStep 300115 = 450173) B450173
theorem B529517 : Blo 183802 529517 := bstep (se 3 (by rfl) ⟨99284, by rfl⟩ : syracuseStep 529517 = 198569) B198569
theorem B300161 : Blo 183802 300161 := bstep (se 2 (by rfl) ⟨112560, by rfl⟩ : syracuseStep 300161 = 225121) B225121
theorem B627857 : Blo 183802 627857 := bstep (se 2 (by rfl) ⟨235446, by rfl⟩ : syracuseStep 627857 = 470893) B470893
theorem B398513 : Blo 183802 398513 := bstep (se 2 (by rfl) ⟨149442, by rfl⟩ : syracuseStep 398513 = 298885) B298885
theorem B529699 : Blo 183802 529699 := bstep (se 1 (by rfl) ⟨397274, by rfl⟩ : syracuseStep 529699 = 794549) B794549
theorem B496973 : Blo 183802 496973 := bstep (se 3 (by rfl) ⟨93182, by rfl⟩ : syracuseStep 496973 = 186365) B186365
theorem B595309 : Blo 183802 595309 := bstep (se 3 (by rfl) ⟨111620, by rfl⟩ : syracuseStep 595309 = 223241) B223241
theorem B300419 : Blo 183802 300419 := bstep (se 1 (by rfl) ⟨225314, by rfl⟩ : syracuseStep 300419 = 450629) B450629
theorem B1578467 : Blo 183802 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B398915 : Blo 183802 398915 := bstep (se 1 (by rfl) ⟨299186, by rfl⟩ : syracuseStep 398915 = 598373) B598373
theorem B628397 : Blo 183802 628397 := bstep (se 3 (by rfl) ⟨117824, by rfl⟩ : syracuseStep 628397 = 235649) B235649
theorem B235219 : Blo 183802 235219 := bstep (se 1 (by rfl) ⟨176414, by rfl⟩ : syracuseStep 235219 = 352829) B352829
theorem B628451 : Blo 183802 628451 := bstep (se 1 (by rfl) ⟨471338, by rfl⟩ : syracuseStep 628451 = 942677) B942677
theorem B530189 : Blo 183802 530189 := bstep (se 3 (by rfl) ⟨99410, by rfl⟩ : syracuseStep 530189 = 198821) B198821
theorem B235315 : Blo 183802 235315 := bstep (se 1 (by rfl) ⟨176486, by rfl⟩ : syracuseStep 235315 = 352973) B352973
theorem B268147 : Blo 183802 268147 := bstep (se 1 (by rfl) ⟨201110, by rfl⟩ : syracuseStep 268147 = 402221) B402221
theorem B628721 : Blo 183802 628721 := bstep (se 2 (by rfl) ⟨235770, by rfl⟩ : syracuseStep 628721 = 471541) B471541
theorem B2398349 : Blo 183802 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B399587 : Blo 183802 399587 := bstep (se 1 (by rfl) ⟨299690, by rfl⟩ : syracuseStep 399587 = 599381) B599381
theorem B792845 : Blo 183802 792845 := bstep (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) B297317
theorem B235811 : Blo 183802 235811 := bstep (se 1 (by rfl) ⟨176858, by rfl⟩ : syracuseStep 235811 = 353717) B353717
theorem B1055045 : Blo 183802 1055045 := bstep (se 4 (by rfl) ⟨98910, by rfl⟩ : syracuseStep 1055045 = 197821) B197821
theorem B2005361 : Blo 183802 2005361 := bstep (se 2 (by rfl) ⟨752010, by rfl⟩ : syracuseStep 2005361 = 1504021) B1504021
theorem B399811 : Blo 183802 399811 := bstep (se 1 (by rfl) ⟨299858, by rfl⟩ : syracuseStep 399811 = 599717) B599717
theorem B629261 : Blo 183802 629261 := bstep (se 3 (by rfl) ⟨117986, by rfl⟩ : syracuseStep 629261 = 235973) B235973
theorem B629315 : Blo 183802 629315 := bstep (se 1 (by rfl) ⟨471986, by rfl⟩ : syracuseStep 629315 = 943973) B943973
theorem B1055501 : Blo 183802 1055501 := bstep (se 3 (by rfl) ⟨197906, by rfl⟩ : syracuseStep 1055501 = 395813) B395813
theorem B596771 : Blo 183802 596771 := bstep (se 1 (by rfl) ⟨447578, by rfl⟩ : syracuseStep 596771 = 895157) B895157
theorem B629585 : Blo 183802 629585 := bstep (se 2 (by rfl) ⟨236094, by rfl⟩ : syracuseStep 629585 = 472189) B472189
theorem B531373 : Blo 183802 531373 := bstep (se 3 (by rfl) ⟨99632, by rfl⟩ : syracuseStep 531373 = 199265) B199265
theorem B236515 : Blo 183802 236515 := bstep (se 1 (by rfl) ⟨177386, by rfl⟩ : syracuseStep 236515 = 354773) B354773
theorem B564205 : Blo 183802 564205 := bstep (se 3 (by rfl) ⟨105788, by rfl⟩ : syracuseStep 564205 = 211577) B211577
theorem B269347 : Blo 183802 269347 := bstep (se 1 (by rfl) ⟨202010, by rfl⟩ : syracuseStep 269347 = 404021) B404021
theorem B597041 : Blo 183802 597041 := bstep (se 2 (by rfl) ⟨223890, by rfl⟩ : syracuseStep 597041 = 447781) B447781
theorem B236611 : Blo 183802 236611 := bstep (se 1 (by rfl) ⟨177458, by rfl⟩ : syracuseStep 236611 = 354917) B354917
theorem B466033 : Blo 183802 466033 := bstep (se 2 (by rfl) ⟨174762, by rfl⟩ : syracuseStep 466033 = 349525) B349525
theorem B269443 : Blo 183802 269443 := bstep (se 1 (by rfl) ⟨202082, by rfl⟩ : syracuseStep 269443 = 404165) B404165
theorem B335107 : Blo 183802 335107 := bstep (se 1 (by rfl) ⟨251330, by rfl⟩ : syracuseStep 335107 = 502661) B502661
theorem B630125 : Blo 183802 630125 := bstep (se 3 (by rfl) ⟨118148, by rfl⟩ : syracuseStep 630125 = 236297) B236297
theorem B466307 : Blo 183802 466307 := bstep (se 1 (by rfl) ⟨349730, by rfl⟩ : syracuseStep 466307 = 699461) B699461
theorem B630179 : Blo 183802 630179 := bstep (se 1 (by rfl) ⟨472634, by rfl⟩ : syracuseStep 630179 = 945269) B945269
theorem B892387 : Blo 183802 892387 := bstep (se 1 (by rfl) ⟨669290, by rfl⟩ : syracuseStep 892387 = 1338581) B1338581
theorem B1416689 : Blo 183802 1416689 := bstep (se 2 (by rfl) ⟨531258, by rfl⟩ : syracuseStep 1416689 = 1062517) B1062517
theorem B237107 : Blo 183802 237107 := bstep (se 1 (by rfl) ⟨177830, by rfl⟩ : syracuseStep 237107 = 355661) B355661
theorem B466499 : Blo 183802 466499 := bstep (se 1 (by rfl) ⟨349874, by rfl⟩ : syracuseStep 466499 = 699749) B699749
theorem B401041 : Blo 183802 401041 := bstep (se 2 (by rfl) ⟨150390, by rfl⟩ : syracuseStep 401041 = 300781) B300781
theorem B630449 : Blo 183802 630449 := bstep (se 2 (by rfl) ⟨236418, by rfl⟩ : syracuseStep 630449 = 472837) B472837
theorem B1187747 : Blo 183802 1187747 := bstep (se 1 (by rfl) ⟨890810, by rfl⟩ : syracuseStep 1187747 = 1781621) B1781621
theorem B532433 : Blo 183802 532433 := bstep (se 2 (by rfl) ⟨199662, by rfl⟩ : syracuseStep 532433 = 399325) B399325
theorem B794701 : Blo 183802 794701 := bstep (se 3 (by rfl) ⟨149006, by rfl⟩ : syracuseStep 794701 = 298013) B298013
theorem B630989 : Blo 183802 630989 := bstep (se 3 (by rfl) ⟨118310, by rfl⟩ : syracuseStep 630989 = 236621) B236621
theorem B631043 : Blo 183802 631043 := bstep (se 1 (by rfl) ⟨473282, by rfl⟩ : syracuseStep 631043 = 946565) B946565
theorem B336145 : Blo 183802 336145 := bstep (se 2 (by rfl) ⟨126054, by rfl⟩ : syracuseStep 336145 = 252109) B252109
theorem B1188209 : Blo 183802 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B467441 : Blo 183802 467441 := bstep (se 2 (by rfl) ⟨175290, by rfl⟩ : syracuseStep 467441 = 350581) B350581
theorem B631313 : Blo 183802 631313 := bstep (se 2 (by rfl) ⟨236742, by rfl⟩ : syracuseStep 631313 = 473485) B473485
theorem B467491 : Blo 183802 467491 := bstep (se 1 (by rfl) ⟨350618, by rfl⟩ : syracuseStep 467491 = 701237) B701237
theorem B533105 : Blo 183802 533105 := bstep (se 2 (by rfl) ⟨199914, by rfl⟩ : syracuseStep 533105 = 399829) B399829
theorem B467633 : Blo 183802 467633 := bstep (se 2 (by rfl) ⟨175362, by rfl⟩ : syracuseStep 467633 = 350725) B350725
theorem B304163 : Blo 183802 304163 := bstep (se 1 (by rfl) ⟨228122, by rfl⟩ : syracuseStep 304163 = 456245) B456245
theorem B631853 : Blo 183802 631853 := bstep (se 3 (by rfl) ⟨118472, by rfl⟩ : syracuseStep 631853 = 236945) B236945
theorem B336995 : Blo 183802 336995 := bstep (se 1 (by rfl) ⟨252746, by rfl⟩ : syracuseStep 336995 = 505493) B505493
theorem B631907 : Blo 183802 631907 := bstep (se 1 (by rfl) ⟨473930, by rfl⟩ : syracuseStep 631907 = 947861) B947861
theorem B337123 : Blo 183802 337123 := bstep (se 1 (by rfl) ⟨252842, by rfl⟩ : syracuseStep 337123 = 505685) B505685
theorem B632177 : Blo 183802 632177 := bstep (se 2 (by rfl) ⟨237066, by rfl⟩ : syracuseStep 632177 = 474133) B474133
theorem B533891 : Blo 183802 533891 := bstep (se 1 (by rfl) ⟨400418, by rfl⟩ : syracuseStep 533891 = 800837) B800837
theorem B599501 : Blo 183802 599501 := bstep (se 3 (by rfl) ⟨112406, by rfl⟩ : syracuseStep 599501 = 224813) B224813
theorem B1058417 : Blo 183802 1058417 := bstep (se 2 (by rfl) ⟨396906, by rfl⟩ : syracuseStep 1058417 = 793813) B793813
theorem B468625 : Blo 183802 468625 := bstep (se 2 (by rfl) ⟨175734, by rfl⟩ : syracuseStep 468625 = 351469) B351469
theorem B566929 : Blo 183802 566929 := bstep (se 2 (by rfl) ⟨212598, by rfl⟩ : syracuseStep 566929 = 425197) B425197
theorem B534221 : Blo 183802 534221 := bstep (se 3 (by rfl) ⟨100166, by rfl⟩ : syracuseStep 534221 = 200333) B200333
theorem B534289 : Blo 183802 534289 := bstep (se 2 (by rfl) ⟨200358, by rfl⟩ : syracuseStep 534289 = 400717) B400717
theorem B337745 : Blo 183802 337745 := bstep (se 2 (by rfl) ⟨126654, by rfl⟩ : syracuseStep 337745 = 253309) B253309
theorem B632717 : Blo 183802 632717 := bstep (se 3 (by rfl) ⟨118634, by rfl⟩ : syracuseStep 632717 = 237269) B237269
theorem B468899 : Blo 183802 468899 := bstep (se 1 (by rfl) ⟨351674, by rfl⟩ : syracuseStep 468899 = 703349) B703349
theorem B632771 : Blo 183802 632771 := bstep (se 1 (by rfl) ⟨474578, by rfl⟩ : syracuseStep 632771 = 949157) B949157
theorem B206851 : Blo 183802 206851 := bstep (se 1 (by rfl) ⟨155138, by rfl⟩ : syracuseStep 206851 = 310277) B310277
theorem B501763 : Blo 183802 501763 := bstep (se 1 (by rfl) ⟨376322, by rfl⟩ : syracuseStep 501763 = 752645) B752645
theorem B534563 : Blo 183802 534563 := bstep (se 1 (by rfl) ⟨400922, by rfl⟩ : syracuseStep 534563 = 801845) B801845
theorem B337969 : Blo 183802 337969 := bstep (se 2 (by rfl) ⟨126738, by rfl⟩ : syracuseStep 337969 = 253477) B253477
theorem B469091 : Blo 183802 469091 := bstep (se 1 (by rfl) ⟨351818, by rfl⟩ : syracuseStep 469091 = 703637) B703637
theorem B338033 : Blo 183802 338033 := bstep (se 2 (by rfl) ⟨126762, by rfl⟩ : syracuseStep 338033 = 253525) B253525
theorem B1779853 : Blo 183802 1779853 := bstep (se 3 (by rfl) ⟨333722, by rfl⟩ : syracuseStep 1779853 = 667445) B667445
theorem B206995 : Blo 183802 206995 := bstep (se 1 (by rfl) ⟨155246, by rfl⟩ : syracuseStep 206995 = 310493) B310493
theorem B633041 : Blo 183802 633041 := bstep (se 2 (by rfl) ⟨237390, by rfl⟩ : syracuseStep 633041 = 474781) B474781
theorem B502033 : Blo 183802 502033 := bstep (se 2 (by rfl) ⟨188262, by rfl⟩ : syracuseStep 502033 = 376525) B376525
theorem B207139 : Blo 183802 207139 := bstep (se 1 (by rfl) ⟨155354, by rfl⟩ : syracuseStep 207139 = 310709) B310709
theorem B633197 : Blo 183802 633197 := bstep (se 3 (by rfl) ⟨118724, by rfl⟩ : syracuseStep 633197 = 237449) B237449
theorem B207283 : Blo 183802 207283 := bstep (se 1 (by rfl) ⟨155462, by rfl⟩ : syracuseStep 207283 = 310925) B310925
theorem B207427 : Blo 183802 207427 := bstep (se 1 (by rfl) ⟨155570, by rfl⟩ : syracuseStep 207427 = 311141) B311141
theorem B2370161 : Blo 183802 2370161 := bstep (se 2 (by rfl) ⟨888810, by rfl⟩ : syracuseStep 2370161 = 1777621) B1777621
theorem B207571 : Blo 183802 207571 := bstep (se 1 (by rfl) ⟨155678, by rfl⟩ : syracuseStep 207571 = 311357) B311357
theorem B633581 : Blo 183802 633581 := bstep (se 3 (by rfl) ⟨118796, by rfl⟩ : syracuseStep 633581 = 237593) B237593
theorem B633635 : Blo 183802 633635 := bstep (se 1 (by rfl) ⟨475226, by rfl⟩ : syracuseStep 633635 = 950453) B950453
theorem B207715 : Blo 183802 207715 := bstep (se 1 (by rfl) ⟨155786, by rfl⟩ : syracuseStep 207715 = 311573) B311573
theorem B666481 : Blo 183802 666481 := bstep (se 2 (by rfl) ⟨249930, by rfl⟩ : syracuseStep 666481 = 499861) B499861
theorem B2698211 : Blo 183802 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B207859 : Blo 183802 207859 := bstep (se 1 (by rfl) ⟨155894, by rfl⟩ : syracuseStep 207859 = 311789) B311789
theorem B470033 : Blo 183802 470033 := bstep (se 2 (by rfl) ⟨176262, by rfl⟩ : syracuseStep 470033 = 352525) B352525
theorem B1059875 : Blo 183802 1059875 := bstep (se 1 (by rfl) ⟨794906, by rfl⟩ : syracuseStep 1059875 = 1589813) B1589813
theorem B338993 : Blo 183802 338993 := bstep (se 2 (by rfl) ⟨127122, by rfl⟩ : syracuseStep 338993 = 254245) B254245
theorem B470083 : Blo 183802 470083 := bstep (se 1 (by rfl) ⟨352562, by rfl⟩ : syracuseStep 470083 = 705125) B705125
theorem B208003 : Blo 183802 208003 := bstep (se 1 (by rfl) ⟨156002, by rfl⟩ : syracuseStep 208003 = 312005) B312005
theorem B470225 : Blo 183802 470225 := bstep (se 2 (by rfl) ⟨176334, by rfl⟩ : syracuseStep 470225 = 352669) B352669
theorem B994531 : Blo 183802 994531 := bstep (se 1 (by rfl) ⟨745898, by rfl⟩ : syracuseStep 994531 = 1491797) B1491797
theorem B601357 : Blo 183802 601357 := bstep (se 3 (by rfl) ⟨112754, by rfl⟩ : syracuseStep 601357 = 225509) B225509
theorem B208147 : Blo 183802 208147 := bstep (se 1 (by rfl) ⟨156110, by rfl⟩ : syracuseStep 208147 = 312221) B312221
theorem B208291 : Blo 183802 208291 := bstep (se 1 (by rfl) ⟨156218, by rfl⟩ : syracuseStep 208291 = 312437) B312437
theorem B2076101 : Blo 183802 2076101 := bstep (se 4 (by rfl) ⟨194634, by rfl⟩ : syracuseStep 2076101 = 389269) B389269
theorem B208435 : Blo 183802 208435 := bstep (se 1 (by rfl) ⟨156326, by rfl⟩ : syracuseStep 208435 = 312653) B312653
theorem B208579 : Blo 183802 208579 := bstep (se 1 (by rfl) ⟨156434, by rfl⟩ : syracuseStep 208579 = 312869) B312869
theorem B569069 : Blo 183802 569069 := bstep (se 3 (by rfl) ⟨106700, by rfl⟩ : syracuseStep 569069 = 213401) B213401
theorem B208723 : Blo 183802 208723 := bstep (se 1 (by rfl) ⟨156542, by rfl⟩ : syracuseStep 208723 = 313085) B313085
theorem B4599665 : Blo 183802 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B208867 : Blo 183802 208867 := bstep (se 1 (by rfl) ⟨156650, by rfl⟩ : syracuseStep 208867 = 313301) B313301
theorem B1060877 : Blo 183802 1060877 := bstep (se 3 (by rfl) ⟨198914, by rfl⟩ : syracuseStep 1060877 = 397829) B397829
theorem B209011 : Blo 183802 209011 := bstep (se 1 (by rfl) ⟨156758, by rfl⟩ : syracuseStep 209011 = 313517) B313517
theorem B471217 : Blo 183802 471217 := bstep (se 2 (by rfl) ⟨176706, by rfl⟩ : syracuseStep 471217 = 353413) B353413
theorem B209155 : Blo 183802 209155 := bstep (se 1 (by rfl) ⟨156866, by rfl⟩ : syracuseStep 209155 = 313733) B313733
theorem B700721 : Blo 183802 700721 := bstep (se 2 (by rfl) ⟨262770, by rfl⟩ : syracuseStep 700721 = 525541) B525541
theorem B799075 : Blo 183802 799075 := bstep (se 1 (by rfl) ⟨599306, by rfl⟩ : syracuseStep 799075 = 1198613) B1198613
theorem B209299 : Blo 183802 209299 := bstep (se 1 (by rfl) ⟨156974, by rfl⟩ : syracuseStep 209299 = 313949) B313949
theorem B471491 : Blo 183802 471491 := bstep (se 1 (by rfl) ⟨353618, by rfl⟩ : syracuseStep 471491 = 707237) B707237
theorem B209443 : Blo 183802 209443 := bstep (se 1 (by rfl) ⟨157082, by rfl⟩ : syracuseStep 209443 = 314165) B314165
theorem B2372165 : Blo 183802 2372165 := bstep (se 4 (by rfl) ⟨222390, by rfl⟩ : syracuseStep 2372165 = 444781) B444781
theorem B471683 : Blo 183802 471683 := bstep (se 1 (by rfl) ⟨353762, by rfl⟩ : syracuseStep 471683 = 707525) B707525
theorem B209587 : Blo 183802 209587 := bstep (se 1 (by rfl) ⟨157190, by rfl⟩ : syracuseStep 209587 = 314381) B314381
theorem B209731 : Blo 183802 209731 := bstep (se 1 (by rfl) ⟨157298, by rfl⟩ : syracuseStep 209731 = 314597) B314597
theorem B635825 : Blo 183802 635825 := bstep (se 2 (by rfl) ⟨238434, by rfl⟩ : syracuseStep 635825 = 476869) B476869
theorem B209875 : Blo 183802 209875 := bstep (se 1 (by rfl) ⟨157406, by rfl⟩ : syracuseStep 209875 = 314813) B314813
theorem B930851 : Blo 183802 930851 := bstep (se 1 (by rfl) ⟨698138, by rfl⟩ : syracuseStep 930851 = 1396277) B1396277
theorem B210019 : Blo 183802 210019 := bstep (se 1 (by rfl) ⟨157514, by rfl⟩ : syracuseStep 210019 = 315029) B315029
theorem B504973 : Blo 183802 504973 := bstep (se 3 (by rfl) ⟨94682, by rfl⟩ : syracuseStep 504973 = 189365) B189365
theorem B2700485 : Blo 183802 2700485 := bstep (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) B506341
theorem B570577 : Blo 183802 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B210163 : Blo 183802 210163 := bstep (se 1 (by rfl) ⟨157622, by rfl⟩ : syracuseStep 210163 = 315245) B315245
theorem B275729 : Blo 183802 275729 := bstep (se 2 (by rfl) ⟨103398, by rfl⟩ : syracuseStep 275729 = 206797) B206797
theorem B275747 : Blo 183802 275747 := bstep (se 1 (by rfl) ⟨206810, by rfl⟩ : syracuseStep 275747 = 413621) B413621
theorem B472355 : Blo 183802 472355 := bstep (se 1 (by rfl) ⟨354266, by rfl⟩ : syracuseStep 472355 = 708533) B708533
theorem B275777 : Blo 183802 275777 := bstep (se 2 (by rfl) ⟨103416, by rfl⟩ : syracuseStep 275777 = 206833) B206833
theorem B275795 : Blo 183802 275795 := bstep (se 1 (by rfl) ⟨206846, by rfl⟩ : syracuseStep 275795 = 413693) B413693
theorem B275825 : Blo 183802 275825 := bstep (se 2 (by rfl) ⟨103434, by rfl⟩ : syracuseStep 275825 = 206869) B206869
theorem B275843 : Blo 183802 275843 := bstep (se 1 (by rfl) ⟨206882, by rfl⟩ : syracuseStep 275843 = 413765) B413765
theorem B210307 : Blo 183802 210307 := bstep (se 1 (by rfl) ⟨157730, by rfl⟩ : syracuseStep 210307 = 315461) B315461
theorem B275873 : Blo 183802 275873 := bstep (se 2 (by rfl) ⟨103452, by rfl⟩ : syracuseStep 275873 = 206905) B206905
theorem B275891 : Blo 183802 275891 := bstep (se 1 (by rfl) ⟨206918, by rfl⟩ : syracuseStep 275891 = 413837) B413837
theorem B275921 : Blo 183802 275921 := bstep (se 2 (by rfl) ⟨103470, by rfl⟩ : syracuseStep 275921 = 206941) B206941
theorem B275939 : Blo 183802 275939 := bstep (se 1 (by rfl) ⟨206954, by rfl⟩ : syracuseStep 275939 = 413909) B413909
theorem B275969 : Blo 183802 275969 := bstep (se 2 (by rfl) ⟨103488, by rfl⟩ : syracuseStep 275969 = 206977) B206977
theorem B210451 : Blo 183802 210451 := bstep (se 1 (by rfl) ⟨157838, by rfl⟩ : syracuseStep 210451 = 315677) B315677
theorem B275987 : Blo 183802 275987 := bstep (se 1 (by rfl) ⟨206990, by rfl⟩ : syracuseStep 275987 = 413981) B413981
theorem B472625 : Blo 183802 472625 := bstep (se 2 (by rfl) ⟨177234, by rfl⟩ : syracuseStep 472625 = 354469) B354469
theorem B276017 : Blo 183802 276017 := bstep (se 2 (by rfl) ⟨103506, by rfl⟩ : syracuseStep 276017 = 207013) B207013
theorem B276035 : Blo 183802 276035 := bstep (se 1 (by rfl) ⟨207026, by rfl⟩ : syracuseStep 276035 = 414053) B414053
theorem B276065 : Blo 183802 276065 := bstep (se 2 (by rfl) ⟨103524, by rfl⟩ : syracuseStep 276065 = 207049) B207049
theorem B472675 : Blo 183802 472675 := bstep (se 1 (by rfl) ⟨354506, by rfl⟩ : syracuseStep 472675 = 709013) B709013
theorem B276083 : Blo 183802 276083 := bstep (se 1 (by rfl) ⟨207062, by rfl⟩ : syracuseStep 276083 = 414125) B414125
theorem B964237 : Blo 183802 964237 := bstep (se 3 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 964237 = 361589) B361589
theorem B276113 : Blo 183802 276113 := bstep (se 2 (by rfl) ⟨103542, by rfl⟩ : syracuseStep 276113 = 207085) B207085
theorem B276131 : Blo 183802 276131 := bstep (se 1 (by rfl) ⟨207098, by rfl⟩ : syracuseStep 276131 = 414197) B414197
theorem B210595 : Blo 183802 210595 := bstep (se 1 (by rfl) ⟨157946, by rfl⟩ : syracuseStep 210595 = 315893) B315893
theorem B276161 : Blo 183802 276161 := bstep (se 2 (by rfl) ⟨103560, by rfl⟩ : syracuseStep 276161 = 207121) B207121
theorem B276179 : Blo 183802 276179 := bstep (se 1 (by rfl) ⟨207134, by rfl⟩ : syracuseStep 276179 = 414269) B414269
theorem B702179 : Blo 183802 702179 := bstep (se 1 (by rfl) ⟨526634, by rfl⟩ : syracuseStep 702179 = 1053269) B1053269
theorem B276209 : Blo 183802 276209 := bstep (se 2 (by rfl) ⟨103578, by rfl⟩ : syracuseStep 276209 = 207157) B207157
theorem B472817 : Blo 183802 472817 := bstep (se 2 (by rfl) ⟨177306, by rfl⟩ : syracuseStep 472817 = 354613) B354613
theorem B276227 : Blo 183802 276227 := bstep (se 1 (by rfl) ⟨207170, by rfl⟩ : syracuseStep 276227 = 414341) B414341
theorem B276257 : Blo 183802 276257 := bstep (se 2 (by rfl) ⟨103596, by rfl⟩ : syracuseStep 276257 = 207193) B207193
theorem B276275 : Blo 183802 276275 := bstep (se 1 (by rfl) ⟨207206, by rfl⟩ : syracuseStep 276275 = 414413) B414413
theorem B210739 : Blo 183802 210739 := bstep (se 1 (by rfl) ⟨158054, by rfl⟩ : syracuseStep 210739 = 316109) B316109
theorem B931661 : Blo 183802 931661 := bstep (se 3 (by rfl) ⟨174686, by rfl⟩ : syracuseStep 931661 = 349373) B349373
theorem B276305 : Blo 183802 276305 := bstep (se 2 (by rfl) ⟨103614, by rfl⟩ : syracuseStep 276305 = 207229) B207229
theorem B276323 : Blo 183802 276323 := bstep (se 1 (by rfl) ⟨207242, by rfl⟩ : syracuseStep 276323 = 414485) B414485
theorem B276353 : Blo 183802 276353 := bstep (se 2 (by rfl) ⟨103632, by rfl⟩ : syracuseStep 276353 = 207265) B207265
theorem B276371 : Blo 183802 276371 := bstep (se 1 (by rfl) ⟨207278, by rfl⟩ : syracuseStep 276371 = 414557) B414557
theorem B276401 : Blo 183802 276401 := bstep (se 2 (by rfl) ⟨103650, by rfl⟩ : syracuseStep 276401 = 207301) B207301
theorem B571313 : Blo 183802 571313 := bstep (se 2 (by rfl) ⟨214242, by rfl⟩ : syracuseStep 571313 = 428485) B428485
theorem B276419 : Blo 183802 276419 := bstep (se 1 (by rfl) ⟨207314, by rfl⟩ : syracuseStep 276419 = 414629) B414629
theorem B210883 : Blo 183802 210883 := bstep (se 1 (by rfl) ⟨158162, by rfl⟩ : syracuseStep 210883 = 316325) B316325
theorem B276449 : Blo 183802 276449 := bstep (se 2 (by rfl) ⟨103668, by rfl⟩ : syracuseStep 276449 = 207337) B207337
theorem B669667 : Blo 183802 669667 := bstep (se 1 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 669667 = 1004501) B1004501
theorem B276467 : Blo 183802 276467 := bstep (se 1 (by rfl) ⟨207350, by rfl⟩ : syracuseStep 276467 = 414701) B414701
theorem B276497 : Blo 183802 276497 := bstep (se 2 (by rfl) ⟨103686, by rfl⟩ : syracuseStep 276497 = 207373) B207373
theorem B276515 : Blo 183802 276515 := bstep (se 1 (by rfl) ⟨207386, by rfl⟩ : syracuseStep 276515 = 414773) B414773
theorem B276545 : Blo 183802 276545 := bstep (se 2 (by rfl) ⟨103704, by rfl⟩ : syracuseStep 276545 = 207409) B207409
theorem B276563 : Blo 183802 276563 := bstep (se 1 (by rfl) ⟨207422, by rfl⟩ : syracuseStep 276563 = 414845) B414845
theorem B211027 : Blo 183802 211027 := bstep (se 1 (by rfl) ⟨158270, by rfl⟩ : syracuseStep 211027 = 316541) B316541
theorem B276593 : Blo 183802 276593 := bstep (se 2 (by rfl) ⟨103722, by rfl⟩ : syracuseStep 276593 = 207445) B207445
theorem B276611 : Blo 183802 276611 := bstep (se 1 (by rfl) ⟨207458, by rfl⟩ : syracuseStep 276611 = 414917) B414917
theorem B276641 : Blo 183802 276641 := bstep (se 2 (by rfl) ⟨103740, by rfl⟩ : syracuseStep 276641 = 207481) B207481
theorem B276659 : Blo 183802 276659 := bstep (se 1 (by rfl) ⟨207494, by rfl⟩ : syracuseStep 276659 = 414989) B414989
theorem B1128653 : Blo 183802 1128653 := bstep (se 3 (by rfl) ⟨211622, by rfl⟩ : syracuseStep 1128653 = 423245) B423245
theorem B276689 : Blo 183802 276689 := bstep (se 2 (by rfl) ⟨103758, by rfl⟩ : syracuseStep 276689 = 207517) B207517
theorem B276707 : Blo 183802 276707 := bstep (se 1 (by rfl) ⟨207530, by rfl⟩ : syracuseStep 276707 = 415061) B415061
theorem B211171 : Blo 183802 211171 := bstep (se 1 (by rfl) ⟨158378, by rfl⟩ : syracuseStep 211171 = 316757) B316757
theorem B276737 : Blo 183802 276737 := bstep (se 2 (by rfl) ⟨103776, by rfl⟩ : syracuseStep 276737 = 207553) B207553
theorem B276755 : Blo 183802 276755 := bstep (se 1 (by rfl) ⟨207566, by rfl⟩ : syracuseStep 276755 = 415133) B415133
theorem B997667 : Blo 183802 997667 := bstep (se 1 (by rfl) ⟨748250, by rfl⟩ : syracuseStep 997667 = 1496501) B1496501
theorem B276785 : Blo 183802 276785 := bstep (se 2 (by rfl) ⟨103794, by rfl⟩ : syracuseStep 276785 = 207589) B207589
theorem B276803 : Blo 183802 276803 := bstep (se 1 (by rfl) ⟨207602, by rfl⟩ : syracuseStep 276803 = 415205) B415205
theorem B276833 : Blo 183802 276833 := bstep (se 2 (by rfl) ⟨103812, by rfl⟩ : syracuseStep 276833 = 207625) B207625
theorem B276851 : Blo 183802 276851 := bstep (se 1 (by rfl) ⟨207638, by rfl⟩ : syracuseStep 276851 = 415277) B415277
theorem B1522061 : Blo 183802 1522061 := bstep (se 3 (by rfl) ⟨285386, by rfl⟩ : syracuseStep 1522061 = 570773) B570773
theorem B276881 : Blo 183802 276881 := bstep (se 2 (by rfl) ⟨103830, by rfl⟩ : syracuseStep 276881 = 207661) B207661
theorem B276899 : Blo 183802 276899 := bstep (se 1 (by rfl) ⟨207674, by rfl⟩ : syracuseStep 276899 = 415349) B415349
theorem B276929 : Blo 183802 276929 := bstep (se 2 (by rfl) ⟨103848, by rfl⟩ : syracuseStep 276929 = 207697) B207697
theorem B276947 : Blo 183802 276947 := bstep (se 1 (by rfl) ⟨207710, by rfl⟩ : syracuseStep 276947 = 415421) B415421
theorem B276977 : Blo 183802 276977 := bstep (se 2 (by rfl) ⟨103866, by rfl⟩ : syracuseStep 276977 = 207733) B207733
theorem B276995 : Blo 183802 276995 := bstep (se 1 (by rfl) ⟨207746, by rfl⟩ : syracuseStep 276995 = 415493) B415493
theorem B277025 : Blo 183802 277025 := bstep (se 2 (by rfl) ⟨103884, by rfl⟩ : syracuseStep 277025 = 207769) B207769
theorem B277043 : Blo 183802 277043 := bstep (se 1 (by rfl) ⟨207782, by rfl⟩ : syracuseStep 277043 = 415565) B415565
theorem B277073 : Blo 183802 277073 := bstep (se 2 (by rfl) ⟨103902, by rfl⟩ : syracuseStep 277073 = 207805) B207805
theorem B277091 : Blo 183802 277091 := bstep (se 1 (by rfl) ⟨207818, by rfl⟩ : syracuseStep 277091 = 415637) B415637
theorem B277121 : Blo 183802 277121 := bstep (se 2 (by rfl) ⟨103920, by rfl⟩ : syracuseStep 277121 = 207841) B207841
theorem B277139 : Blo 183802 277139 := bstep (se 1 (by rfl) ⟨207854, by rfl⟩ : syracuseStep 277139 = 415709) B415709
theorem B277169 : Blo 183802 277169 := bstep (se 2 (by rfl) ⟨103938, by rfl⟩ : syracuseStep 277169 = 207877) B207877
theorem B277187 : Blo 183802 277187 := bstep (se 1 (by rfl) ⟨207890, by rfl⟩ : syracuseStep 277187 = 415781) B415781
theorem B703181 : Blo 183802 703181 := bstep (se 3 (by rfl) ⟨131846, by rfl⟩ : syracuseStep 703181 = 263693) B263693
theorem B473809 : Blo 183802 473809 := bstep (se 2 (by rfl) ⟨177678, by rfl⟩ : syracuseStep 473809 = 355357) B355357
theorem B277217 : Blo 183802 277217 := bstep (se 2 (by rfl) ⟨103956, by rfl⟩ : syracuseStep 277217 = 207913) B207913
theorem B801521 : Blo 183802 801521 := bstep (se 2 (by rfl) ⟨300570, by rfl⟩ : syracuseStep 801521 = 601141) B601141
theorem B277235 : Blo 183802 277235 := bstep (se 1 (by rfl) ⟨207926, by rfl⟩ : syracuseStep 277235 = 415853) B415853
theorem B277265 : Blo 183802 277265 := bstep (se 2 (by rfl) ⟨103974, by rfl⟩ : syracuseStep 277265 = 207949) B207949
theorem B277283 : Blo 183802 277283 := bstep (se 1 (by rfl) ⟨207962, by rfl⟩ : syracuseStep 277283 = 415925) B415925
theorem B277313 : Blo 183802 277313 := bstep (se 2 (by rfl) ⟨103992, by rfl⟩ : syracuseStep 277313 = 207985) B207985
theorem B1194821 : Blo 183802 1194821 := bstep (se 4 (by rfl) ⟨112014, by rfl⟩ : syracuseStep 1194821 = 224029) B224029
theorem B277331 : Blo 183802 277331 := bstep (se 1 (by rfl) ⟨207998, by rfl⟩ : syracuseStep 277331 = 415997) B415997
theorem B277361 : Blo 183802 277361 := bstep (se 2 (by rfl) ⟨104010, by rfl⟩ : syracuseStep 277361 = 208021) B208021
theorem B1063793 : Blo 183802 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B277379 : Blo 183802 277379 := bstep (se 1 (by rfl) ⟨208034, by rfl⟩ : syracuseStep 277379 = 416069) B416069
theorem B277409 : Blo 183802 277409 := bstep (se 2 (by rfl) ⟨104028, by rfl⟩ : syracuseStep 277409 = 208057) B208057
theorem B277427 : Blo 183802 277427 := bstep (se 1 (by rfl) ⟨208070, by rfl⟩ : syracuseStep 277427 = 416141) B416141
theorem B277457 : Blo 183802 277457 := bstep (se 2 (by rfl) ⟨104046, by rfl⟩ : syracuseStep 277457 = 208093) B208093
theorem B310243 : Blo 183802 310243 := bstep (se 1 (by rfl) ⟨232682, by rfl⟩ : syracuseStep 310243 = 465365) B465365
theorem B277475 : Blo 183802 277475 := bstep (se 1 (by rfl) ⟨208106, by rfl⟩ : syracuseStep 277475 = 416213) B416213
theorem B474083 : Blo 183802 474083 := bstep (se 1 (by rfl) ⟨355562, by rfl⟩ : syracuseStep 474083 = 711125) B711125
theorem B277505 : Blo 183802 277505 := bstep (se 2 (by rfl) ⟨104064, by rfl⟩ : syracuseStep 277505 = 208129) B208129
theorem B277523 : Blo 183802 277523 := bstep (se 1 (by rfl) ⟨208142, by rfl⟩ : syracuseStep 277523 = 416285) B416285
theorem B277553 : Blo 183802 277553 := bstep (se 2 (by rfl) ⟨104082, by rfl⟩ : syracuseStep 277553 = 208165) B208165
theorem B277571 : Blo 183802 277571 := bstep (se 1 (by rfl) ⟨208178, by rfl⟩ : syracuseStep 277571 = 416357) B416357
theorem B277601 : Blo 183802 277601 := bstep (se 2 (by rfl) ⟨104100, by rfl⟩ : syracuseStep 277601 = 208201) B208201
theorem B310385 : Blo 183802 310385 := bstep (se 2 (by rfl) ⟨116394, by rfl⟩ : syracuseStep 310385 = 232789) B232789
theorem B277619 : Blo 183802 277619 := bstep (se 1 (by rfl) ⟨208214, by rfl⟩ : syracuseStep 277619 = 416429) B416429
theorem B277649 : Blo 183802 277649 := bstep (se 2 (by rfl) ⟨104118, by rfl⟩ : syracuseStep 277649 = 208237) B208237
theorem B277667 : Blo 183802 277667 := bstep (se 1 (by rfl) ⟨208250, by rfl⟩ : syracuseStep 277667 = 416501) B416501
theorem B474275 : Blo 183802 474275 := bstep (se 1 (by rfl) ⟨355706, by rfl⟩ : syracuseStep 474275 = 711413) B711413
theorem B277697 : Blo 183802 277697 := bstep (se 2 (by rfl) ⟨104136, by rfl⟩ : syracuseStep 277697 = 208273) B208273
theorem B277715 : Blo 183802 277715 := bstep (se 1 (by rfl) ⟨208286, by rfl⟩ : syracuseStep 277715 = 416573) B416573
theorem B310513 : Blo 183802 310513 := bstep (se 2 (by rfl) ⟨116442, by rfl⟩ : syracuseStep 310513 = 232885) B232885
theorem B277745 : Blo 183802 277745 := bstep (se 2 (by rfl) ⟨104154, by rfl⟩ : syracuseStep 277745 = 208309) B208309
theorem B277763 : Blo 183802 277763 := bstep (se 1 (by rfl) ⟨208322, by rfl⟩ : syracuseStep 277763 = 416645) B416645
theorem B310547 : Blo 183802 310547 := bstep (se 1 (by rfl) ⟨232910, by rfl⟩ : syracuseStep 310547 = 465821) B465821
theorem B277793 : Blo 183802 277793 := bstep (se 2 (by rfl) ⟨104172, by rfl⟩ : syracuseStep 277793 = 208345) B208345
theorem B277811 : Blo 183802 277811 := bstep (se 1 (by rfl) ⟨208358, by rfl⟩ : syracuseStep 277811 = 416717) B416717
theorem B277841 : Blo 183802 277841 := bstep (se 2 (by rfl) ⟨104190, by rfl⟩ : syracuseStep 277841 = 208381) B208381
theorem B277859 : Blo 183802 277859 := bstep (se 1 (by rfl) ⟨208394, by rfl⟩ : syracuseStep 277859 = 416789) B416789
theorem B277889 : Blo 183802 277889 := bstep (se 2 (by rfl) ⟨104208, by rfl⟩ : syracuseStep 277889 = 208417) B208417
theorem B310675 : Blo 183802 310675 := bstep (se 1 (by rfl) ⟨233006, by rfl⟩ : syracuseStep 310675 = 466013) B466013
theorem B277907 : Blo 183802 277907 := bstep (se 1 (by rfl) ⟨208430, by rfl⟩ : syracuseStep 277907 = 416861) B416861
theorem B277937 : Blo 183802 277937 := bstep (se 2 (by rfl) ⟨104226, by rfl⟩ : syracuseStep 277937 = 208453) B208453
theorem B277955 : Blo 183802 277955 := bstep (se 1 (by rfl) ⟨208466, by rfl⟩ : syracuseStep 277955 = 416933) B416933
theorem B277985 : Blo 183802 277985 := bstep (se 2 (by rfl) ⟨104244, by rfl⟩ : syracuseStep 277985 = 208489) B208489
theorem B278003 : Blo 183802 278003 := bstep (se 1 (by rfl) ⟨208502, by rfl⟩ : syracuseStep 278003 = 417005) B417005
theorem B474641 : Blo 183802 474641 := bstep (se 2 (by rfl) ⟨177990, by rfl⟩ : syracuseStep 474641 = 355981) B355981
theorem B278033 : Blo 183802 278033 := bstep (se 2 (by rfl) ⟨104262, by rfl⟩ : syracuseStep 278033 = 208525) B208525
theorem B310817 : Blo 183802 310817 := bstep (se 2 (by rfl) ⟨116556, by rfl⟩ : syracuseStep 310817 = 233113) B233113
theorem B278051 : Blo 183802 278051 := bstep (se 1 (by rfl) ⟨208538, by rfl⟩ : syracuseStep 278051 = 417077) B417077
theorem B278081 : Blo 183802 278081 := bstep (se 2 (by rfl) ⟨104280, by rfl⟩ : syracuseStep 278081 = 208561) B208561
theorem B278099 : Blo 183802 278099 := bstep (se 1 (by rfl) ⟨208574, by rfl⟩ : syracuseStep 278099 = 417149) B417149
theorem B278129 : Blo 183802 278129 := bstep (se 2 (by rfl) ⟨104298, by rfl⟩ : syracuseStep 278129 = 208597) B208597
theorem B278147 : Blo 183802 278147 := bstep (se 1 (by rfl) ⟨208610, by rfl⟩ : syracuseStep 278147 = 417221) B417221
theorem B310945 : Blo 183802 310945 := bstep (se 2 (by rfl) ⟨116604, by rfl⟩ : syracuseStep 310945 = 233209) B233209
theorem B278177 : Blo 183802 278177 := bstep (se 2 (by rfl) ⟨104316, by rfl⟩ : syracuseStep 278177 = 208633) B208633
theorem B278195 : Blo 183802 278195 := bstep (se 1 (by rfl) ⟨208646, by rfl⟩ : syracuseStep 278195 = 417293) B417293
theorem B310979 : Blo 183802 310979 := bstep (se 1 (by rfl) ⟨233234, by rfl⟩ : syracuseStep 310979 = 466469) B466469
theorem B278225 : Blo 183802 278225 := bstep (se 2 (by rfl) ⟨104334, by rfl⟩ : syracuseStep 278225 = 208669) B208669
theorem B278243 : Blo 183802 278243 := bstep (se 1 (by rfl) ⟨208682, by rfl⟩ : syracuseStep 278243 = 417365) B417365
theorem B278273 : Blo 183802 278273 := bstep (se 2 (by rfl) ⟨104352, by rfl⟩ : syracuseStep 278273 = 208705) B208705
theorem B278291 : Blo 183802 278291 := bstep (se 1 (by rfl) ⟨208718, by rfl⟩ : syracuseStep 278291 = 417437) B417437
theorem B278321 : Blo 183802 278321 := bstep (se 2 (by rfl) ⟨104370, by rfl⟩ : syracuseStep 278321 = 208741) B208741
theorem B311107 : Blo 183802 311107 := bstep (se 1 (by rfl) ⟨233330, by rfl⟩ : syracuseStep 311107 = 466661) B466661
theorem B278339 : Blo 183802 278339 := bstep (se 1 (by rfl) ⟨208754, by rfl⟩ : syracuseStep 278339 = 417509) B417509
theorem B278369 : Blo 183802 278369 := bstep (se 2 (by rfl) ⟨104388, by rfl⟩ : syracuseStep 278369 = 208777) B208777
theorem B278387 : Blo 183802 278387 := bstep (se 1 (by rfl) ⟨208790, by rfl⟩ : syracuseStep 278387 = 417581) B417581
theorem B278417 : Blo 183802 278417 := bstep (se 2 (by rfl) ⟨104406, by rfl⟩ : syracuseStep 278417 = 208813) B208813
theorem B278435 : Blo 183802 278435 := bstep (se 1 (by rfl) ⟨208826, by rfl⟩ : syracuseStep 278435 = 417653) B417653
theorem B278465 : Blo 183802 278465 := bstep (se 2 (by rfl) ⟨104424, by rfl⟩ : syracuseStep 278465 = 208849) B208849
theorem B311249 : Blo 183802 311249 := bstep (se 2 (by rfl) ⟨116718, by rfl⟩ : syracuseStep 311249 = 233437) B233437
theorem B278483 : Blo 183802 278483 := bstep (se 1 (by rfl) ⟨208862, by rfl⟩ : syracuseStep 278483 = 417725) B417725
theorem B278513 : Blo 183802 278513 := bstep (se 2 (by rfl) ⟨104442, by rfl⟩ : syracuseStep 278513 = 208885) B208885
theorem B278531 : Blo 183802 278531 := bstep (se 1 (by rfl) ⟨208898, by rfl⟩ : syracuseStep 278531 = 417797) B417797
theorem B278561 : Blo 183802 278561 := bstep (se 2 (by rfl) ⟨104460, by rfl⟩ : syracuseStep 278561 = 208921) B208921
theorem B278579 : Blo 183802 278579 := bstep (se 1 (by rfl) ⟨208934, by rfl⟩ : syracuseStep 278579 = 417869) B417869
theorem B311377 : Blo 183802 311377 := bstep (se 2 (by rfl) ⟨116766, by rfl⟩ : syracuseStep 311377 = 233533) B233533
theorem B278609 : Blo 183802 278609 := bstep (se 2 (by rfl) ⟨104478, by rfl⟩ : syracuseStep 278609 = 208957) B208957
theorem B475217 : Blo 183802 475217 := bstep (se 2 (by rfl) ⟨178206, by rfl⟩ : syracuseStep 475217 = 356413) B356413
theorem B1065059 : Blo 183802 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B278627 : Blo 183802 278627 := bstep (se 1 (by rfl) ⟨208970, by rfl⟩ : syracuseStep 278627 = 417941) B417941
theorem B311411 : Blo 183802 311411 := bstep (se 1 (by rfl) ⟨233558, by rfl⟩ : syracuseStep 311411 = 467117) B467117
theorem B278657 : Blo 183802 278657 := bstep (se 2 (by rfl) ⟨104496, by rfl⟩ : syracuseStep 278657 = 208993) B208993
theorem B475267 : Blo 183802 475267 := bstep (se 1 (by rfl) ⟨356450, by rfl⟩ : syracuseStep 475267 = 712901) B712901
theorem B278675 : Blo 183802 278675 := bstep (se 1 (by rfl) ⟨209006, by rfl⟩ : syracuseStep 278675 = 418013) B418013
theorem B278705 : Blo 183802 278705 := bstep (se 2 (by rfl) ⟨104514, by rfl⟩ : syracuseStep 278705 = 209029) B209029
theorem B606403 : Blo 183802 606403 := bstep (se 1 (by rfl) ⟨454802, by rfl⟩ : syracuseStep 606403 = 909605) B909605
theorem B278723 : Blo 183802 278723 := bstep (se 1 (by rfl) ⟨209042, by rfl⟩ : syracuseStep 278723 = 418085) B418085
theorem B278753 : Blo 183802 278753 := bstep (se 2 (by rfl) ⟨104532, by rfl⟩ : syracuseStep 278753 = 209065) B209065
theorem B311539 : Blo 183802 311539 := bstep (se 1 (by rfl) ⟨233654, by rfl⟩ : syracuseStep 311539 = 467309) B467309
theorem B278771 : Blo 183802 278771 := bstep (se 1 (by rfl) ⟨209078, by rfl⟩ : syracuseStep 278771 = 418157) B418157
theorem B278801 : Blo 183802 278801 := bstep (se 2 (by rfl) ⟨104550, by rfl⟩ : syracuseStep 278801 = 209101) B209101
theorem B278819 : Blo 183802 278819 := bstep (se 1 (by rfl) ⟨209114, by rfl⟩ : syracuseStep 278819 = 418229) B418229
theorem B1065251 : Blo 183802 1065251 := bstep (se 1 (by rfl) ⟨798938, by rfl⟩ : syracuseStep 1065251 = 1597877) B1597877
theorem B278849 : Blo 183802 278849 := bstep (se 2 (by rfl) ⟨104568, by rfl⟩ : syracuseStep 278849 = 209137) B209137
theorem B278867 : Blo 183802 278867 := bstep (se 1 (by rfl) ⟨209150, by rfl⟩ : syracuseStep 278867 = 418301) B418301
theorem B278897 : Blo 183802 278897 := bstep (se 2 (by rfl) ⟨104586, by rfl⟩ : syracuseStep 278897 = 209173) B209173
theorem B311681 : Blo 183802 311681 := bstep (se 2 (by rfl) ⟨116880, by rfl⟩ : syracuseStep 311681 = 233761) B233761
theorem B278915 : Blo 183802 278915 := bstep (se 1 (by rfl) ⟨209186, by rfl⟩ : syracuseStep 278915 = 418373) B418373
theorem B278945 : Blo 183802 278945 := bstep (se 2 (by rfl) ⟨104604, by rfl⟩ : syracuseStep 278945 = 209209) B209209
theorem B278963 : Blo 183802 278963 := bstep (se 1 (by rfl) ⟨209222, by rfl⟩ : syracuseStep 278963 = 418445) B418445
theorem B278993 : Blo 183802 278993 := bstep (se 2 (by rfl) ⟨104622, by rfl⟩ : syracuseStep 278993 = 209245) B209245
theorem B279011 : Blo 183802 279011 := bstep (se 1 (by rfl) ⟨209258, by rfl⟩ : syracuseStep 279011 = 418517) B418517
theorem B311809 : Blo 183802 311809 := bstep (se 2 (by rfl) ⟨116928, by rfl⟩ : syracuseStep 311809 = 233857) B233857
theorem B279041 : Blo 183802 279041 := bstep (se 2 (by rfl) ⟨104640, by rfl⟩ : syracuseStep 279041 = 209281) B209281
theorem B279059 : Blo 183802 279059 := bstep (se 1 (by rfl) ⟨209294, by rfl⟩ : syracuseStep 279059 = 418589) B418589
theorem B311843 : Blo 183802 311843 := bstep (se 1 (by rfl) ⟨233882, by rfl⟩ : syracuseStep 311843 = 467765) B467765
theorem B279089 : Blo 183802 279089 := bstep (se 2 (by rfl) ⟨104658, by rfl⟩ : syracuseStep 279089 = 209317) B209317
theorem B279107 : Blo 183802 279107 := bstep (se 1 (by rfl) ⟨209330, by rfl⟩ : syracuseStep 279107 = 418661) B418661
theorem B279137 : Blo 183802 279137 := bstep (se 2 (by rfl) ⟨104676, by rfl⟩ : syracuseStep 279137 = 209353) B209353
theorem B279155 : Blo 183802 279155 := bstep (se 1 (by rfl) ⟨209366, by rfl⟩ : syracuseStep 279155 = 418733) B418733
theorem B279185 : Blo 183802 279185 := bstep (se 2 (by rfl) ⟨104694, by rfl⟩ : syracuseStep 279185 = 209389) B209389
theorem B311971 : Blo 183802 311971 := bstep (se 1 (by rfl) ⟨233978, by rfl⟩ : syracuseStep 311971 = 467957) B467957
theorem B279203 : Blo 183802 279203 := bstep (se 1 (by rfl) ⟨209402, by rfl⟩ : syracuseStep 279203 = 418805) B418805
theorem B934577 : Blo 183802 934577 := bstep (se 2 (by rfl) ⟨350466, by rfl⟩ : syracuseStep 934577 = 700933) B700933
theorem B279233 : Blo 183802 279233 := bstep (se 2 (by rfl) ⟨104712, by rfl⟩ : syracuseStep 279233 = 209425) B209425
theorem B1000133 : Blo 183802 1000133 := bstep (se 4 (by rfl) ⟨93762, by rfl⟩ : syracuseStep 1000133 = 187525) B187525
theorem B279251 : Blo 183802 279251 := bstep (se 1 (by rfl) ⟨209438, by rfl⟩ : syracuseStep 279251 = 418877) B418877
theorem B279281 : Blo 183802 279281 := bstep (se 2 (by rfl) ⟨104730, by rfl⟩ : syracuseStep 279281 = 209461) B209461
theorem B279299 : Blo 183802 279299 := bstep (se 1 (by rfl) ⟨209474, by rfl⟩ : syracuseStep 279299 = 418949) B418949
theorem B705293 : Blo 183802 705293 := bstep (se 3 (by rfl) ⟨132242, by rfl⟩ : syracuseStep 705293 = 264485) B264485
theorem B279329 : Blo 183802 279329 := bstep (se 2 (by rfl) ⟨104748, by rfl⟩ : syracuseStep 279329 = 209497) B209497
theorem B312113 : Blo 183802 312113 := bstep (se 2 (by rfl) ⟨117042, by rfl⟩ : syracuseStep 312113 = 234085) B234085
theorem B279347 : Blo 183802 279347 := bstep (se 1 (by rfl) ⟨209510, by rfl⟩ : syracuseStep 279347 = 419021) B419021
theorem B279377 : Blo 183802 279377 := bstep (se 2 (by rfl) ⟨104766, by rfl⟩ : syracuseStep 279377 = 209533) B209533
theorem B279395 : Blo 183802 279395 := bstep (se 1 (by rfl) ⟨209546, by rfl⟩ : syracuseStep 279395 = 419093) B419093
theorem B279425 : Blo 183802 279425 := bstep (se 2 (by rfl) ⟨104784, by rfl⟩ : syracuseStep 279425 = 209569) B209569
theorem B279443 : Blo 183802 279443 := bstep (se 1 (by rfl) ⟨209582, by rfl⟩ : syracuseStep 279443 = 419165) B419165
theorem B312241 : Blo 183802 312241 := bstep (se 2 (by rfl) ⟨117090, by rfl⟩ : syracuseStep 312241 = 234181) B234181
theorem B279473 : Blo 183802 279473 := bstep (se 2 (by rfl) ⟨104802, by rfl⟩ : syracuseStep 279473 = 209605) B209605
theorem B279491 : Blo 183802 279491 := bstep (se 1 (by rfl) ⟨209618, by rfl⟩ : syracuseStep 279491 = 419237) B419237
theorem B312275 : Blo 183802 312275 := bstep (se 1 (by rfl) ⟨234206, by rfl⟩ : syracuseStep 312275 = 468413) B468413
theorem B279521 : Blo 183802 279521 := bstep (se 2 (by rfl) ⟨104820, by rfl⟩ : syracuseStep 279521 = 209641) B209641
theorem B3195875 : Blo 183802 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B279539 : Blo 183802 279539 := bstep (se 1 (by rfl) ⟨209654, by rfl⟩ : syracuseStep 279539 = 419309) B419309
theorem B279569 : Blo 183802 279569 := bstep (se 2 (by rfl) ⟨104838, by rfl⟩ : syracuseStep 279569 = 209677) B209677
theorem B279587 : Blo 183802 279587 := bstep (se 1 (by rfl) ⟨209690, by rfl⟩ : syracuseStep 279587 = 419381) B419381
theorem B279617 : Blo 183802 279617 := bstep (se 2 (by rfl) ⟨104856, by rfl⟩ : syracuseStep 279617 = 209713) B209713
theorem B312403 : Blo 183802 312403 := bstep (se 1 (by rfl) ⟨234302, by rfl⟩ : syracuseStep 312403 = 468605) B468605
theorem B279635 : Blo 183802 279635 := bstep (se 1 (by rfl) ⟨209726, by rfl⟩ : syracuseStep 279635 = 419453) B419453
theorem B279665 : Blo 183802 279665 := bstep (se 2 (by rfl) ⟨104874, by rfl⟩ : syracuseStep 279665 = 209749) B209749
theorem B279683 : Blo 183802 279683 := bstep (se 1 (by rfl) ⟨209762, by rfl⟩ : syracuseStep 279683 = 419525) B419525
theorem B279713 : Blo 183802 279713 := bstep (se 2 (by rfl) ⟨104892, by rfl⟩ : syracuseStep 279713 = 209785) B209785
theorem B607409 : Blo 183802 607409 := bstep (se 2 (by rfl) ⟨227778, by rfl⟩ : syracuseStep 607409 = 455557) B455557
theorem B279731 : Blo 183802 279731 := bstep (se 1 (by rfl) ⟨209798, by rfl⟩ : syracuseStep 279731 = 419597) B419597
theorem B279761 : Blo 183802 279761 := bstep (se 2 (by rfl) ⟨104910, by rfl⟩ : syracuseStep 279761 = 209821) B209821
theorem B312545 : Blo 183802 312545 := bstep (se 2 (by rfl) ⟨117204, by rfl⟩ : syracuseStep 312545 = 234409) B234409
theorem B279779 : Blo 183802 279779 := bstep (se 1 (by rfl) ⟨209834, by rfl⟩ : syracuseStep 279779 = 419669) B419669
theorem B279809 : Blo 183802 279809 := bstep (se 2 (by rfl) ⟨104928, by rfl⟩ : syracuseStep 279809 = 209857) B209857
theorem B279827 : Blo 183802 279827 := bstep (se 1 (by rfl) ⟨209870, by rfl⟩ : syracuseStep 279827 = 419741) B419741
theorem B279857 : Blo 183802 279857 := bstep (se 2 (by rfl) ⟨104946, by rfl⟩ : syracuseStep 279857 = 209893) B209893
theorem B279875 : Blo 183802 279875 := bstep (se 1 (by rfl) ⟨209906, by rfl⟩ : syracuseStep 279875 = 419813) B419813
theorem B1000781 : Blo 183802 1000781 := bstep (se 3 (by rfl) ⟨187646, by rfl⟩ : syracuseStep 1000781 = 375293) B375293
theorem B312673 : Blo 183802 312673 := bstep (se 2 (by rfl) ⟨117252, by rfl⟩ : syracuseStep 312673 = 234505) B234505
theorem B279905 : Blo 183802 279905 := bstep (se 2 (by rfl) ⟨104964, by rfl⟩ : syracuseStep 279905 = 209929) B209929
theorem B279923 : Blo 183802 279923 := bstep (se 1 (by rfl) ⟨209942, by rfl⟩ : syracuseStep 279923 = 419885) B419885
theorem B312707 : Blo 183802 312707 := bstep (se 1 (by rfl) ⟨234530, by rfl⟩ : syracuseStep 312707 = 469061) B469061
theorem B279953 : Blo 183802 279953 := bstep (se 2 (by rfl) ⟨104982, by rfl⟩ : syracuseStep 279953 = 209965) B209965
theorem B607651 : Blo 183802 607651 := bstep (se 1 (by rfl) ⟨455738, by rfl⟩ : syracuseStep 607651 = 911477) B911477
theorem B279971 : Blo 183802 279971 := bstep (se 1 (by rfl) ⟨209978, by rfl⟩ : syracuseStep 279971 = 419957) B419957
theorem B280001 : Blo 183802 280001 := bstep (se 2 (by rfl) ⟨105000, by rfl⟩ : syracuseStep 280001 = 210001) B210001
theorem B3851717 : Blo 183802 3851717 := bstep (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) B722197
theorem B280019 : Blo 183802 280019 := bstep (se 1 (by rfl) ⟨210014, by rfl⟩ : syracuseStep 280019 = 420029) B420029
theorem B280049 : Blo 183802 280049 := bstep (se 2 (by rfl) ⟨105018, by rfl⟩ : syracuseStep 280049 = 210037) B210037
theorem B312835 : Blo 183802 312835 := bstep (se 1 (by rfl) ⟨234626, by rfl⟩ : syracuseStep 312835 = 469253) B469253
theorem B280067 : Blo 183802 280067 := bstep (se 1 (by rfl) ⟨210050, by rfl⟩ : syracuseStep 280067 = 420101) B420101
theorem B280097 : Blo 183802 280097 := bstep (se 2 (by rfl) ⟨105036, by rfl⟩ : syracuseStep 280097 = 210073) B210073
theorem B706097 : Blo 183802 706097 := bstep (se 2 (by rfl) ⟨264786, by rfl⟩ : syracuseStep 706097 = 529573) B529573
theorem B280115 : Blo 183802 280115 := bstep (se 1 (by rfl) ⟨210086, by rfl⟩ : syracuseStep 280115 = 420173) B420173
theorem B280145 : Blo 183802 280145 := bstep (se 2 (by rfl) ⟨105054, by rfl⟩ : syracuseStep 280145 = 210109) B210109
theorem B280163 : Blo 183802 280163 := bstep (se 1 (by rfl) ⟨210122, by rfl⟩ : syracuseStep 280163 = 420245) B420245
theorem B280193 : Blo 183802 280193 := bstep (se 2 (by rfl) ⟨105072, by rfl⟩ : syracuseStep 280193 = 210145) B210145
theorem B312977 : Blo 183802 312977 := bstep (se 2 (by rfl) ⟨117366, by rfl⟩ : syracuseStep 312977 = 234733) B234733
theorem B280211 : Blo 183802 280211 := bstep (se 1 (by rfl) ⟨210158, by rfl⟩ : syracuseStep 280211 = 420317) B420317
theorem B280241 : Blo 183802 280241 := bstep (se 2 (by rfl) ⟨105090, by rfl⟩ : syracuseStep 280241 = 210181) B210181
theorem B280259 : Blo 183802 280259 := bstep (se 1 (by rfl) ⟨210194, by rfl⟩ : syracuseStep 280259 = 420389) B420389
theorem B280289 : Blo 183802 280289 := bstep (se 2 (by rfl) ⟨105108, by rfl⟩ : syracuseStep 280289 = 210217) B210217
theorem B280307 : Blo 183802 280307 := bstep (se 1 (by rfl) ⟨210230, by rfl⟩ : syracuseStep 280307 = 420461) B420461
theorem B313105 : Blo 183802 313105 := bstep (se 2 (by rfl) ⟨117414, by rfl⟩ : syracuseStep 313105 = 234829) B234829
theorem B280337 : Blo 183802 280337 := bstep (se 2 (by rfl) ⟨105126, by rfl⟩ : syracuseStep 280337 = 210253) B210253
theorem B280355 : Blo 183802 280355 := bstep (se 1 (by rfl) ⟨210266, by rfl⟩ : syracuseStep 280355 = 420533) B420533
theorem B313139 : Blo 183802 313139 := bstep (se 1 (by rfl) ⟨234854, by rfl⟩ : syracuseStep 313139 = 469709) B469709
theorem B280385 : Blo 183802 280385 := bstep (se 2 (by rfl) ⟨105144, by rfl⟩ : syracuseStep 280385 = 210289) B210289
theorem B280403 : Blo 183802 280403 := bstep (se 1 (by rfl) ⟨210302, by rfl⟩ : syracuseStep 280403 = 420605) B420605
theorem B280433 : Blo 183802 280433 := bstep (se 2 (by rfl) ⟨105162, by rfl⟩ : syracuseStep 280433 = 210325) B210325
theorem B280451 : Blo 183802 280451 := bstep (se 1 (by rfl) ⟨210338, by rfl⟩ : syracuseStep 280451 = 420677) B420677
theorem B378769 : Blo 183802 378769 := bstep (se 2 (by rfl) ⟨142038, by rfl⟩ : syracuseStep 378769 = 284077) B284077
theorem B280481 : Blo 183802 280481 := bstep (se 2 (by rfl) ⟨105180, by rfl⟩ : syracuseStep 280481 = 210361) B210361
theorem B313267 : Blo 183802 313267 := bstep (se 1 (by rfl) ⟨234950, by rfl⟩ : syracuseStep 313267 = 469901) B469901
theorem B280499 : Blo 183802 280499 := bstep (se 1 (by rfl) ⟨210374, by rfl⟩ : syracuseStep 280499 = 420749) B420749
theorem B280529 : Blo 183802 280529 := bstep (se 2 (by rfl) ⟨105198, by rfl⟩ : syracuseStep 280529 = 210397) B210397
theorem B280547 : Blo 183802 280547 := bstep (se 1 (by rfl) ⟨210410, by rfl⟩ : syracuseStep 280547 = 420821) B420821
theorem B280577 : Blo 183802 280577 := bstep (se 2 (by rfl) ⟨105216, by rfl⟩ : syracuseStep 280577 = 210433) B210433
theorem B280595 : Blo 183802 280595 := bstep (se 1 (by rfl) ⟨210446, by rfl⟩ : syracuseStep 280595 = 420893) B420893
theorem B280625 : Blo 183802 280625 := bstep (se 2 (by rfl) ⟨105234, by rfl⟩ : syracuseStep 280625 = 210469) B210469
theorem B313409 : Blo 183802 313409 := bstep (se 2 (by rfl) ⟨117528, by rfl⟩ : syracuseStep 313409 = 235057) B235057
theorem B280643 : Blo 183802 280643 := bstep (se 1 (by rfl) ⟨210482, by rfl⟩ : syracuseStep 280643 = 420965) B420965
theorem B280673 : Blo 183802 280673 := bstep (se 2 (by rfl) ⟨105252, by rfl⟩ : syracuseStep 280673 = 210505) B210505
theorem B936035 : Blo 183802 936035 := bstep (se 1 (by rfl) ⟨702026, by rfl⟩ : syracuseStep 936035 = 1404053) B1404053
theorem B280691 : Blo 183802 280691 := bstep (se 1 (by rfl) ⟨210518, by rfl⟩ : syracuseStep 280691 = 421037) B421037
theorem B673933 : Blo 183802 673933 := bstep (se 3 (by rfl) ⟨126362, by rfl⟩ : syracuseStep 673933 = 252725) B252725
theorem B280721 : Blo 183802 280721 := bstep (se 2 (by rfl) ⟨105270, by rfl⟩ : syracuseStep 280721 = 210541) B210541
theorem B280739 : Blo 183802 280739 := bstep (se 1 (by rfl) ⟨210554, by rfl⟩ : syracuseStep 280739 = 421109) B421109
theorem B313537 : Blo 183802 313537 := bstep (se 2 (by rfl) ⟨117576, by rfl⟩ : syracuseStep 313537 = 235153) B235153
theorem B280769 : Blo 183802 280769 := bstep (se 2 (by rfl) ⟨105288, by rfl⟩ : syracuseStep 280769 = 210577) B210577
theorem B706765 : Blo 183802 706765 := bstep (se 3 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 706765 = 265037) B265037
theorem B280787 : Blo 183802 280787 := bstep (se 1 (by rfl) ⟨210590, by rfl⟩ : syracuseStep 280787 = 421181) B421181
theorem B313571 : Blo 183802 313571 := bstep (se 1 (by rfl) ⟨235178, by rfl⟩ : syracuseStep 313571 = 470357) B470357
theorem B280817 : Blo 183802 280817 := bstep (se 2 (by rfl) ⟨105306, by rfl⟩ : syracuseStep 280817 = 210613) B210613
theorem B280835 : Blo 183802 280835 := bstep (se 1 (by rfl) ⟨210626, by rfl⟩ : syracuseStep 280835 = 421253) B421253
theorem B280865 : Blo 183802 280865 := bstep (se 2 (by rfl) ⟨105324, by rfl⟩ : syracuseStep 280865 = 210649) B210649
theorem B1198385 : Blo 183802 1198385 := bstep (se 2 (by rfl) ⟨449394, by rfl⟩ : syracuseStep 1198385 = 898789) B898789
theorem B280883 : Blo 183802 280883 := bstep (se 1 (by rfl) ⟨210662, by rfl⟩ : syracuseStep 280883 = 421325) B421325
theorem B280913 : Blo 183802 280913 := bstep (se 2 (by rfl) ⟨105342, by rfl⟩ : syracuseStep 280913 = 210685) B210685
theorem B313699 : Blo 183802 313699 := bstep (se 1 (by rfl) ⟨235274, by rfl⟩ : syracuseStep 313699 = 470549) B470549
theorem B280931 : Blo 183802 280931 := bstep (se 1 (by rfl) ⟨210698, by rfl⟩ : syracuseStep 280931 = 421397) B421397
theorem B280961 : Blo 183802 280961 := bstep (se 2 (by rfl) ⟨105360, by rfl⟩ : syracuseStep 280961 = 210721) B210721
theorem B280979 : Blo 183802 280979 := bstep (se 1 (by rfl) ⟨210734, by rfl⟩ : syracuseStep 280979 = 421469) B421469
theorem B281009 : Blo 183802 281009 := bstep (se 2 (by rfl) ⟨105378, by rfl⟩ : syracuseStep 281009 = 210757) B210757
theorem B379331 : Blo 183802 379331 := bstep (se 1 (by rfl) ⟨284498, by rfl⟩ : syracuseStep 379331 = 568997) B568997
theorem B281027 : Blo 183802 281027 := bstep (se 1 (by rfl) ⟨210770, by rfl⟩ : syracuseStep 281027 = 421541) B421541
theorem B281057 : Blo 183802 281057 := bstep (se 2 (by rfl) ⟨105396, by rfl⟩ : syracuseStep 281057 = 210793) B210793
theorem B313841 : Blo 183802 313841 := bstep (se 2 (by rfl) ⟨117690, by rfl⟩ : syracuseStep 313841 = 235381) B235381
theorem B281075 : Blo 183802 281075 := bstep (se 1 (by rfl) ⟨210806, by rfl⟩ : syracuseStep 281075 = 421613) B421613
theorem B281105 : Blo 183802 281105 := bstep (se 2 (by rfl) ⟨105414, by rfl⟩ : syracuseStep 281105 = 210829) B210829
theorem B281123 : Blo 183802 281123 := bstep (se 1 (by rfl) ⟨210842, by rfl⟩ : syracuseStep 281123 = 421685) B421685
theorem B281153 : Blo 183802 281153 := bstep (se 2 (by rfl) ⟨105432, by rfl⟩ : syracuseStep 281153 = 210865) B210865
theorem B281171 : Blo 183802 281171 := bstep (se 1 (by rfl) ⟨210878, by rfl⟩ : syracuseStep 281171 = 421757) B421757
theorem B313969 : Blo 183802 313969 := bstep (se 2 (by rfl) ⟨117738, by rfl⟩ : syracuseStep 313969 = 235477) B235477
theorem B281201 : Blo 183802 281201 := bstep (se 2 (by rfl) ⟨105450, by rfl⟩ : syracuseStep 281201 = 210901) B210901
theorem B281219 : Blo 183802 281219 := bstep (se 1 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 281219 = 421829) B421829
theorem B248465 : Blo 183802 248465 := bstep (se 2 (by rfl) ⟨93174, by rfl⟩ : syracuseStep 248465 = 186349) B186349
theorem B314003 : Blo 183802 314003 := bstep (se 1 (by rfl) ⟨235502, by rfl⟩ : syracuseStep 314003 = 471005) B471005
theorem B281249 : Blo 183802 281249 := bstep (se 2 (by rfl) ⟨105468, by rfl⟩ : syracuseStep 281249 = 210937) B210937
theorem B510637 : Blo 183802 510637 := bstep (se 3 (by rfl) ⟨95744, by rfl⟩ : syracuseStep 510637 = 191489) B191489
theorem B281267 : Blo 183802 281267 := bstep (se 1 (by rfl) ⟨210950, by rfl⟩ : syracuseStep 281267 = 421901) B421901
theorem B281297 : Blo 183802 281297 := bstep (se 2 (by rfl) ⟨105486, by rfl⟩ : syracuseStep 281297 = 210973) B210973
theorem B281315 : Blo 183802 281315 := bstep (se 1 (by rfl) ⟨210986, by rfl⟩ : syracuseStep 281315 = 421973) B421973
theorem B215795 : Blo 183802 215795 := bstep (se 1 (by rfl) ⟨161846, by rfl⟩ : syracuseStep 215795 = 323693) B323693
theorem B281345 : Blo 183802 281345 := bstep (se 2 (by rfl) ⟨105504, by rfl⟩ : syracuseStep 281345 = 211009) B211009
theorem B314131 : Blo 183802 314131 := bstep (se 1 (by rfl) ⟨235598, by rfl⟩ : syracuseStep 314131 = 471197) B471197
theorem B281363 : Blo 183802 281363 := bstep (se 1 (by rfl) ⟨211022, by rfl⟩ : syracuseStep 281363 = 422045) B422045
theorem B281393 : Blo 183802 281393 := bstep (se 2 (by rfl) ⟨105522, by rfl⟩ : syracuseStep 281393 = 211045) B211045
theorem B281411 : Blo 183802 281411 := bstep (se 1 (by rfl) ⟨211058, by rfl⟩ : syracuseStep 281411 = 422117) B422117
theorem B281441 : Blo 183802 281441 := bstep (se 2 (by rfl) ⟨105540, by rfl⟩ : syracuseStep 281441 = 211081) B211081
theorem B281459 : Blo 183802 281459 := bstep (se 1 (by rfl) ⟨211094, by rfl⟩ : syracuseStep 281459 = 422189) B422189
theorem B936845 : Blo 183802 936845 := bstep (se 3 (by rfl) ⟨175658, by rfl⟩ : syracuseStep 936845 = 351317) B351317
theorem B281489 : Blo 183802 281489 := bstep (se 2 (by rfl) ⟨105558, by rfl⟩ : syracuseStep 281489 = 211117) B211117
theorem B314273 : Blo 183802 314273 := bstep (se 2 (by rfl) ⟨117852, by rfl⟩ : syracuseStep 314273 = 235705) B235705
theorem B281507 : Blo 183802 281507 := bstep (se 1 (by rfl) ⟨211130, by rfl⟩ : syracuseStep 281507 = 422261) B422261
theorem B281537 : Blo 183802 281537 := bstep (se 2 (by rfl) ⟨105576, by rfl⟩ : syracuseStep 281537 = 211153) B211153
theorem B281555 : Blo 183802 281555 := bstep (se 1 (by rfl) ⟨211166, by rfl⟩ : syracuseStep 281555 = 422333) B422333
theorem B707555 : Blo 183802 707555 := bstep (se 1 (by rfl) ⟨530666, by rfl⟩ : syracuseStep 707555 = 1061333) B1061333
theorem B281585 : Blo 183802 281585 := bstep (se 2 (by rfl) ⟨105594, by rfl⟩ : syracuseStep 281585 = 211189) B211189
theorem B281603 : Blo 183802 281603 := bstep (se 1 (by rfl) ⟨211202, by rfl⟩ : syracuseStep 281603 = 422405) B422405
theorem B2018317 : Blo 183802 2018317 := bstep (se 3 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 2018317 = 756869) B756869
theorem B314401 : Blo 183802 314401 := bstep (se 2 (by rfl) ⟨117900, by rfl⟩ : syracuseStep 314401 = 235801) B235801
theorem B281633 : Blo 183802 281633 := bstep (se 2 (by rfl) ⟨105612, by rfl⟩ : syracuseStep 281633 = 211225) B211225
theorem B281651 : Blo 183802 281651 := bstep (se 1 (by rfl) ⟨211238, by rfl⟩ : syracuseStep 281651 = 422477) B422477
theorem B314435 : Blo 183802 314435 := bstep (se 1 (by rfl) ⟨235826, by rfl⟩ : syracuseStep 314435 = 471653) B471653
theorem B281681 : Blo 183802 281681 := bstep (se 2 (by rfl) ⟨105630, by rfl⟩ : syracuseStep 281681 = 211261) B211261
theorem B281699 : Blo 183802 281699 := bstep (se 1 (by rfl) ⟨211274, by rfl⟩ : syracuseStep 281699 = 422549) B422549
theorem B314563 : Blo 183802 314563 := bstep (se 1 (by rfl) ⟨235922, by rfl⟩ : syracuseStep 314563 = 471845) B471845
theorem B314627 : Blo 183802 314627 := bstep (se 1 (by rfl) ⟨235970, by rfl⟩ : syracuseStep 314627 = 471941) B471941
theorem B314705 : Blo 183802 314705 := bstep (se 2 (by rfl) ⟨118014, by rfl⟩ : syracuseStep 314705 = 236029) B236029
theorem B511331 : Blo 183802 511331 := bstep (se 1 (by rfl) ⟨383498, by rfl⟩ : syracuseStep 511331 = 766997) B766997
theorem B249265 : Blo 183802 249265 := bstep (se 2 (by rfl) ⟨93474, by rfl⟩ : syracuseStep 249265 = 186949) B186949
theorem B314833 : Blo 183802 314833 := bstep (se 2 (by rfl) ⟨118062, by rfl⟩ : syracuseStep 314833 = 236125) B236125
theorem B314867 : Blo 183802 314867 := bstep (se 1 (by rfl) ⟨236150, by rfl⟩ : syracuseStep 314867 = 472301) B472301
theorem B183811 : Blo 183802 183811 := bstep (se 1 (by rfl) ⟨137858, by rfl⟩ : syracuseStep 183811 = 275717) B275717
theorem B183827 : Blo 183802 183827 := bstep (se 1 (by rfl) ⟨137870, by rfl⟩ : syracuseStep 183827 = 275741) B275741
theorem B183843 : Blo 183802 183843 := bstep (se 1 (by rfl) ⟨137882, by rfl⟩ : syracuseStep 183843 = 275765) B275765
theorem B183859 : Blo 183802 183859 := bstep (se 1 (by rfl) ⟨137894, by rfl⟩ : syracuseStep 183859 = 275789) B275789
theorem B183875 : Blo 183802 183875 := bstep (se 1 (by rfl) ⟨137906, by rfl⟩ : syracuseStep 183875 = 275813) B275813
theorem B183891 : Blo 183802 183891 := bstep (se 1 (by rfl) ⟨137918, by rfl⟩ : syracuseStep 183891 = 275837) B275837
theorem B183907 : Blo 183802 183907 := bstep (se 1 (by rfl) ⟨137930, by rfl⟩ : syracuseStep 183907 = 275861) B275861
theorem B708209 : Blo 183802 708209 := bstep (se 2 (by rfl) ⟨265578, by rfl⟩ : syracuseStep 708209 = 531157) B531157
theorem B183923 : Blo 183802 183923 := bstep (se 1 (by rfl) ⟨137942, by rfl⟩ : syracuseStep 183923 = 275885) B275885
theorem B314995 : Blo 183802 314995 := bstep (se 1 (by rfl) ⟨236246, by rfl⟩ : syracuseStep 314995 = 472493) B472493
theorem B183939 : Blo 183802 183939 := bstep (se 1 (by rfl) ⟨137954, by rfl⟩ : syracuseStep 183939 = 275909) B275909
theorem B183955 : Blo 183802 183955 := bstep (se 1 (by rfl) ⟨137966, by rfl⟩ : syracuseStep 183955 = 275933) B275933
theorem B183971 : Blo 183802 183971 := bstep (se 1 (by rfl) ⟨137978, by rfl⟩ : syracuseStep 183971 = 275957) B275957
theorem B183987 : Blo 183802 183987 := bstep (se 1 (by rfl) ⟨137990, by rfl⟩ : syracuseStep 183987 = 275981) B275981
theorem B184003 : Blo 183802 184003 := bstep (se 1 (by rfl) ⟨138002, by rfl⟩ : syracuseStep 184003 = 276005) B276005
theorem B184019 : Blo 183802 184019 := bstep (se 1 (by rfl) ⟨138014, by rfl⟩ : syracuseStep 184019 = 276029) B276029
theorem B184035 : Blo 183802 184035 := bstep (se 1 (by rfl) ⟨138026, by rfl⟩ : syracuseStep 184035 = 276053) B276053
theorem B1199843 : Blo 183802 1199843 := bstep (se 1 (by rfl) ⟨899882, by rfl⟩ : syracuseStep 1199843 = 1799765) B1799765
theorem B184051 : Blo 183802 184051 := bstep (se 1 (by rfl) ⟨138038, by rfl⟩ : syracuseStep 184051 = 276077) B276077
theorem B315137 : Blo 183802 315137 := bstep (se 2 (by rfl) ⟨118176, by rfl⟩ : syracuseStep 315137 = 236353) B236353
theorem B184067 : Blo 183802 184067 := bstep (se 1 (by rfl) ⟨138050, by rfl⟩ : syracuseStep 184067 = 276101) B276101
theorem B184083 : Blo 183802 184083 := bstep (se 1 (by rfl) ⟨138062, by rfl⟩ : syracuseStep 184083 = 276125) B276125
theorem B184099 : Blo 183802 184099 := bstep (se 1 (by rfl) ⟨138074, by rfl⟩ : syracuseStep 184099 = 276149) B276149
theorem B184115 : Blo 183802 184115 := bstep (se 1 (by rfl) ⟨138086, by rfl⟩ : syracuseStep 184115 = 276173) B276173
theorem B184131 : Blo 183802 184131 := bstep (se 1 (by rfl) ⟨138098, by rfl⟩ : syracuseStep 184131 = 276197) B276197
theorem B184147 : Blo 183802 184147 := bstep (se 1 (by rfl) ⟨138110, by rfl⟩ : syracuseStep 184147 = 276221) B276221
theorem B184163 : Blo 183802 184163 := bstep (se 1 (by rfl) ⟨138122, by rfl⟩ : syracuseStep 184163 = 276245) B276245
theorem B184179 : Blo 183802 184179 := bstep (se 1 (by rfl) ⟨138134, by rfl⟩ : syracuseStep 184179 = 276269) B276269
theorem B315265 : Blo 183802 315265 := bstep (se 2 (by rfl) ⟨118224, by rfl⟩ : syracuseStep 315265 = 236449) B236449
theorem B184195 : Blo 183802 184195 := bstep (se 1 (by rfl) ⟨138146, by rfl⟩ : syracuseStep 184195 = 276293) B276293
theorem B1593229 : Blo 183802 1593229 := bstep (se 3 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 1593229 = 597461) B597461
theorem B413585 : Blo 183802 413585 := bstep (se 2 (by rfl) ⟨155094, by rfl⟩ : syracuseStep 413585 = 310189) B310189
theorem B184211 : Blo 183802 184211 := bstep (se 1 (by rfl) ⟨138158, by rfl⟩ : syracuseStep 184211 = 276317) B276317
theorem B413603 : Blo 183802 413603 := bstep (se 1 (by rfl) ⟨310202, by rfl⟩ : syracuseStep 413603 = 620405) B620405
theorem B184227 : Blo 183802 184227 := bstep (se 1 (by rfl) ⟨138170, by rfl⟩ : syracuseStep 184227 = 276341) B276341
theorem B315299 : Blo 183802 315299 := bstep (se 1 (by rfl) ⟨236474, by rfl⟩ : syracuseStep 315299 = 472949) B472949
theorem B184243 : Blo 183802 184243 := bstep (se 1 (by rfl) ⟨138182, by rfl⟩ : syracuseStep 184243 = 276365) B276365
theorem B184259 : Blo 183802 184259 := bstep (se 1 (by rfl) ⟨138194, by rfl⟩ : syracuseStep 184259 = 276389) B276389
theorem B184275 : Blo 183802 184275 := bstep (se 1 (by rfl) ⟨138206, by rfl⟩ : syracuseStep 184275 = 276413) B276413
theorem B184291 : Blo 183802 184291 := bstep (se 1 (by rfl) ⟨138218, by rfl⟩ : syracuseStep 184291 = 276437) B276437
theorem B184307 : Blo 183802 184307 := bstep (se 1 (by rfl) ⟨138230, by rfl⟩ : syracuseStep 184307 = 276461) B276461
theorem B184323 : Blo 183802 184323 := bstep (se 1 (by rfl) ⟨138242, by rfl⟩ : syracuseStep 184323 = 276485) B276485
theorem B184339 : Blo 183802 184339 := bstep (se 1 (by rfl) ⟨138254, by rfl⟩ : syracuseStep 184339 = 276509) B276509
theorem B184355 : Blo 183802 184355 := bstep (se 1 (by rfl) ⟨138266, by rfl⟩ : syracuseStep 184355 = 276533) B276533
theorem B315427 : Blo 183802 315427 := bstep (se 1 (by rfl) ⟨236570, by rfl⟩ : syracuseStep 315427 = 473141) B473141
theorem B184371 : Blo 183802 184371 := bstep (se 1 (by rfl) ⟨138278, by rfl⟩ : syracuseStep 184371 = 276557) B276557
theorem B184387 : Blo 183802 184387 := bstep (se 1 (by rfl) ⟨138290, by rfl⟩ : syracuseStep 184387 = 276581) B276581
theorem B184403 : Blo 183802 184403 := bstep (se 1 (by rfl) ⟨138302, by rfl⟩ : syracuseStep 184403 = 276605) B276605
theorem B184419 : Blo 183802 184419 := bstep (se 1 (by rfl) ⟨138314, by rfl⟩ : syracuseStep 184419 = 276629) B276629
theorem B184435 : Blo 183802 184435 := bstep (se 1 (by rfl) ⟨138326, by rfl⟩ : syracuseStep 184435 = 276653) B276653
theorem B184451 : Blo 183802 184451 := bstep (se 1 (by rfl) ⟨138338, by rfl⟩ : syracuseStep 184451 = 276677) B276677
theorem B184467 : Blo 183802 184467 := bstep (se 1 (by rfl) ⟨138350, by rfl⟩ : syracuseStep 184467 = 276701) B276701
theorem B184483 : Blo 183802 184483 := bstep (se 1 (by rfl) ⟨138362, by rfl⟩ : syracuseStep 184483 = 276725) B276725
theorem B446627 : Blo 183802 446627 := bstep (se 1 (by rfl) ⟨334970, by rfl⟩ : syracuseStep 446627 = 669941) B669941
theorem B512173 : Blo 183802 512173 := bstep (se 3 (by rfl) ⟨96032, by rfl⟩ : syracuseStep 512173 = 192065) B192065
theorem B413873 : Blo 183802 413873 := bstep (se 2 (by rfl) ⟨155202, by rfl⟩ : syracuseStep 413873 = 310405) B310405
theorem B315569 : Blo 183802 315569 := bstep (se 2 (by rfl) ⟨118338, by rfl⟩ : syracuseStep 315569 = 236677) B236677
theorem B184499 : Blo 183802 184499 := bstep (se 1 (by rfl) ⟨138374, by rfl⟩ : syracuseStep 184499 = 276749) B276749
theorem B413891 : Blo 183802 413891 := bstep (se 1 (by rfl) ⟨310418, by rfl⟩ : syracuseStep 413891 = 620837) B620837
theorem B184515 : Blo 183802 184515 := bstep (se 1 (by rfl) ⟨138386, by rfl⟩ : syracuseStep 184515 = 276773) B276773
theorem B184531 : Blo 183802 184531 := bstep (se 1 (by rfl) ⟨138398, by rfl⟩ : syracuseStep 184531 = 276797) B276797
theorem B184547 : Blo 183802 184547 := bstep (se 1 (by rfl) ⟨138410, by rfl⟩ : syracuseStep 184547 = 276821) B276821
theorem B184563 : Blo 183802 184563 := bstep (se 1 (by rfl) ⟨138422, by rfl⟩ : syracuseStep 184563 = 276845) B276845
theorem B184579 : Blo 183802 184579 := bstep (se 1 (by rfl) ⟨138434, by rfl⟩ : syracuseStep 184579 = 276869) B276869
theorem B184595 : Blo 183802 184595 := bstep (se 1 (by rfl) ⟨138446, by rfl⟩ : syracuseStep 184595 = 276893) B276893
theorem B184611 : Blo 183802 184611 := bstep (se 1 (by rfl) ⟨138458, by rfl⟩ : syracuseStep 184611 = 276917) B276917
theorem B315697 : Blo 183802 315697 := bstep (se 2 (by rfl) ⟨118386, by rfl⟩ : syracuseStep 315697 = 236773) B236773
theorem B184627 : Blo 183802 184627 := bstep (se 1 (by rfl) ⟨138470, by rfl⟩ : syracuseStep 184627 = 276941) B276941
theorem B184643 : Blo 183802 184643 := bstep (se 1 (by rfl) ⟨138482, by rfl⟩ : syracuseStep 184643 = 276965) B276965
theorem B184659 : Blo 183802 184659 := bstep (se 1 (by rfl) ⟨138494, by rfl⟩ : syracuseStep 184659 = 276989) B276989
theorem B315731 : Blo 183802 315731 := bstep (se 1 (by rfl) ⟨236798, by rfl⟩ : syracuseStep 315731 = 473597) B473597
theorem B184675 : Blo 183802 184675 := bstep (se 1 (by rfl) ⟨138506, by rfl⟩ : syracuseStep 184675 = 277013) B277013
theorem B184691 : Blo 183802 184691 := bstep (se 1 (by rfl) ⟨138518, by rfl⟩ : syracuseStep 184691 = 277037) B277037
theorem B184707 : Blo 183802 184707 := bstep (se 1 (by rfl) ⟨138530, by rfl⟩ : syracuseStep 184707 = 277061) B277061
theorem B184723 : Blo 183802 184723 := bstep (se 1 (by rfl) ⟨138542, by rfl⟩ : syracuseStep 184723 = 277085) B277085
theorem B184739 : Blo 183802 184739 := bstep (se 1 (by rfl) ⟨138554, by rfl⟩ : syracuseStep 184739 = 277109) B277109
theorem B184755 : Blo 183802 184755 := bstep (se 1 (by rfl) ⟨138566, by rfl⟩ : syracuseStep 184755 = 277133) B277133
theorem B184771 : Blo 183802 184771 := bstep (se 1 (by rfl) ⟨138578, by rfl⟩ : syracuseStep 184771 = 277157) B277157
theorem B414161 : Blo 183802 414161 := bstep (se 2 (by rfl) ⟨155310, by rfl⟩ : syracuseStep 414161 = 310621) B310621
theorem B184787 : Blo 183802 184787 := bstep (se 1 (by rfl) ⟨138590, by rfl⟩ : syracuseStep 184787 = 277181) B277181
theorem B315859 : Blo 183802 315859 := bstep (se 1 (by rfl) ⟨236894, by rfl⟩ : syracuseStep 315859 = 473789) B473789
theorem B414179 : Blo 183802 414179 := bstep (se 1 (by rfl) ⟨310634, by rfl⟩ : syracuseStep 414179 = 621269) B621269
theorem B184803 : Blo 183802 184803 := bstep (se 1 (by rfl) ⟨138602, by rfl⟩ : syracuseStep 184803 = 277205) B277205
theorem B184819 : Blo 183802 184819 := bstep (se 1 (by rfl) ⟨138614, by rfl⟩ : syracuseStep 184819 = 277229) B277229
theorem B184835 : Blo 183802 184835 := bstep (se 1 (by rfl) ⟨138626, by rfl⟩ : syracuseStep 184835 = 277253) B277253
theorem B184851 : Blo 183802 184851 := bstep (se 1 (by rfl) ⟨138638, by rfl⟩ : syracuseStep 184851 = 277277) B277277
theorem B184867 : Blo 183802 184867 := bstep (se 1 (by rfl) ⟨138650, by rfl⟩ : syracuseStep 184867 = 277301) B277301
theorem B184883 : Blo 183802 184883 := bstep (se 1 (by rfl) ⟨138662, by rfl⟩ : syracuseStep 184883 = 277325) B277325
theorem B184899 : Blo 183802 184899 := bstep (se 1 (by rfl) ⟨138674, by rfl⟩ : syracuseStep 184899 = 277349) B277349
theorem B184915 : Blo 183802 184915 := bstep (se 1 (by rfl) ⟨138686, by rfl⟩ : syracuseStep 184915 = 277373) B277373
theorem B316001 : Blo 183802 316001 := bstep (se 2 (by rfl) ⟨118500, by rfl⟩ : syracuseStep 316001 = 237001) B237001
theorem B184931 : Blo 183802 184931 := bstep (se 1 (by rfl) ⟨138698, by rfl⟩ : syracuseStep 184931 = 277397) B277397
theorem B3002993 : Blo 183802 3002993 := bstep (se 2 (by rfl) ⟨1126122, by rfl⟩ : syracuseStep 3002993 = 2252245) B2252245
theorem B184947 : Blo 183802 184947 := bstep (se 1 (by rfl) ⟨138710, by rfl⟩ : syracuseStep 184947 = 277421) B277421
theorem B184963 : Blo 183802 184963 := bstep (se 1 (by rfl) ⟨138722, by rfl⟩ : syracuseStep 184963 = 277445) B277445
theorem B184979 : Blo 183802 184979 := bstep (se 1 (by rfl) ⟨138734, by rfl⟩ : syracuseStep 184979 = 277469) B277469
theorem B184995 : Blo 183802 184995 := bstep (se 1 (by rfl) ⟨138746, by rfl⟩ : syracuseStep 184995 = 277493) B277493
theorem B185011 : Blo 183802 185011 := bstep (se 1 (by rfl) ⟨138758, by rfl⟩ : syracuseStep 185011 = 277517) B277517
theorem B185027 : Blo 183802 185027 := bstep (se 1 (by rfl) ⟨138770, by rfl⟩ : syracuseStep 185027 = 277541) B277541
theorem B1200845 : Blo 183802 1200845 := bstep (se 3 (by rfl) ⟨225158, by rfl⟩ : syracuseStep 1200845 = 450317) B450317
theorem B185043 : Blo 183802 185043 := bstep (se 1 (by rfl) ⟨138782, by rfl⟩ : syracuseStep 185043 = 277565) B277565
theorem B316129 : Blo 183802 316129 := bstep (se 2 (by rfl) ⟨118548, by rfl⟩ : syracuseStep 316129 = 237097) B237097
theorem B185059 : Blo 183802 185059 := bstep (se 1 (by rfl) ⟨138794, by rfl⟩ : syracuseStep 185059 = 277589) B277589
theorem B414449 : Blo 183802 414449 := bstep (se 2 (by rfl) ⟨155418, by rfl⟩ : syracuseStep 414449 = 310837) B310837
theorem B185075 : Blo 183802 185075 := bstep (se 1 (by rfl) ⟨138806, by rfl⟩ : syracuseStep 185075 = 277613) B277613
theorem B414467 : Blo 183802 414467 := bstep (se 1 (by rfl) ⟨310850, by rfl⟩ : syracuseStep 414467 = 621701) B621701
theorem B185091 : Blo 183802 185091 := bstep (se 1 (by rfl) ⟨138818, by rfl⟩ : syracuseStep 185091 = 277637) B277637
theorem B316163 : Blo 183802 316163 := bstep (se 1 (by rfl) ⟨237122, by rfl⟩ : syracuseStep 316163 = 474245) B474245
theorem B185107 : Blo 183802 185107 := bstep (se 1 (by rfl) ⟨138830, by rfl⟩ : syracuseStep 185107 = 277661) B277661
theorem B185123 : Blo 183802 185123 := bstep (se 1 (by rfl) ⟨138842, by rfl⟩ : syracuseStep 185123 = 277685) B277685
theorem B283441 : Blo 183802 283441 := bstep (se 2 (by rfl) ⟨106290, by rfl⟩ : syracuseStep 283441 = 212581) B212581
theorem B185139 : Blo 183802 185139 := bstep (se 1 (by rfl) ⟨138854, by rfl⟩ : syracuseStep 185139 = 277709) B277709
theorem B185155 : Blo 183802 185155 := bstep (se 1 (by rfl) ⟨138866, by rfl⟩ : syracuseStep 185155 = 277733) B277733
theorem B185171 : Blo 183802 185171 := bstep (se 1 (by rfl) ⟨138878, by rfl⟩ : syracuseStep 185171 = 277757) B277757
theorem B185187 : Blo 183802 185187 := bstep (se 1 (by rfl) ⟨138890, by rfl⟩ : syracuseStep 185187 = 277781) B277781
theorem B906083 : Blo 183802 906083 := bstep (se 1 (by rfl) ⟨679562, by rfl⟩ : syracuseStep 906083 = 1359125) B1359125
theorem B185203 : Blo 183802 185203 := bstep (se 1 (by rfl) ⟨138902, by rfl⟩ : syracuseStep 185203 = 277805) B277805
theorem B283507 : Blo 183802 283507 := bstep (se 1 (by rfl) ⟨212630, by rfl⟩ : syracuseStep 283507 = 425261) B425261
theorem B185219 : Blo 183802 185219 := bstep (se 1 (by rfl) ⟨138914, by rfl⟩ : syracuseStep 185219 = 277829) B277829
theorem B316291 : Blo 183802 316291 := bstep (se 1 (by rfl) ⟨237218, by rfl⟩ : syracuseStep 316291 = 474437) B474437
theorem B185235 : Blo 183802 185235 := bstep (se 1 (by rfl) ⟨138926, by rfl⟩ : syracuseStep 185235 = 277853) B277853
theorem B185251 : Blo 183802 185251 := bstep (se 1 (by rfl) ⟨138938, by rfl⟩ : syracuseStep 185251 = 277877) B277877
theorem B185267 : Blo 183802 185267 := bstep (se 1 (by rfl) ⟨138950, by rfl⟩ : syracuseStep 185267 = 277901) B277901
theorem B349123 : Blo 183802 349123 := bstep (se 1 (by rfl) ⟨261842, by rfl⟩ : syracuseStep 349123 = 523685) B523685
theorem B185283 : Blo 183802 185283 := bstep (se 1 (by rfl) ⟨138962, by rfl⟩ : syracuseStep 185283 = 277925) B277925
theorem B185299 : Blo 183802 185299 := bstep (se 1 (by rfl) ⟨138974, by rfl⟩ : syracuseStep 185299 = 277949) B277949
theorem B185315 : Blo 183802 185315 := bstep (se 1 (by rfl) ⟨138986, by rfl⟩ : syracuseStep 185315 = 277973) B277973
theorem B185331 : Blo 183802 185331 := bstep (se 1 (by rfl) ⟨138998, by rfl⟩ : syracuseStep 185331 = 277997) B277997
theorem B185347 : Blo 183802 185347 := bstep (se 1 (by rfl) ⟨139010, by rfl⟩ : syracuseStep 185347 = 278021) B278021
theorem B414737 : Blo 183802 414737 := bstep (se 2 (by rfl) ⟨155526, by rfl⟩ : syracuseStep 414737 = 311053) B311053
theorem B316433 : Blo 183802 316433 := bstep (se 2 (by rfl) ⟨118662, by rfl⟩ : syracuseStep 316433 = 237325) B237325
theorem B185363 : Blo 183802 185363 := bstep (se 1 (by rfl) ⟨139022, by rfl⟩ : syracuseStep 185363 = 278045) B278045
theorem B414755 : Blo 183802 414755 := bstep (se 1 (by rfl) ⟨311066, by rfl⟩ : syracuseStep 414755 = 622133) B622133
theorem B185379 : Blo 183802 185379 := bstep (se 1 (by rfl) ⟨139034, by rfl⟩ : syracuseStep 185379 = 278069) B278069
theorem B709667 : Blo 183802 709667 := bstep (se 1 (by rfl) ⟨532250, by rfl⟩ : syracuseStep 709667 = 1064501) B1064501
theorem B709681 : Blo 183802 709681 := bstep (se 2 (by rfl) ⟨266130, by rfl⟩ : syracuseStep 709681 = 532261) B532261
theorem B185395 : Blo 183802 185395 := bstep (se 1 (by rfl) ⟨139046, by rfl⟩ : syracuseStep 185395 = 278093) B278093
theorem B185411 : Blo 183802 185411 := bstep (se 1 (by rfl) ⟨139058, by rfl⟩ : syracuseStep 185411 = 278117) B278117
theorem B1332293 : Blo 183802 1332293 := bstep (se 4 (by rfl) ⟨124902, by rfl⟩ : syracuseStep 1332293 = 249805) B249805
theorem B185427 : Blo 183802 185427 := bstep (se 1 (by rfl) ⟨139070, by rfl⟩ : syracuseStep 185427 = 278141) B278141
theorem B185443 : Blo 183802 185443 := bstep (se 1 (by rfl) ⟨139082, by rfl⟩ : syracuseStep 185443 = 278165) B278165
theorem B185459 : Blo 183802 185459 := bstep (se 1 (by rfl) ⟨139094, by rfl⟩ : syracuseStep 185459 = 278189) B278189
theorem B185475 : Blo 183802 185475 := bstep (se 1 (by rfl) ⟨139106, by rfl⟩ : syracuseStep 185475 = 278213) B278213
theorem B316561 : Blo 183802 316561 := bstep (se 2 (by rfl) ⟨118710, by rfl⟩ : syracuseStep 316561 = 237421) B237421
theorem B185491 : Blo 183802 185491 := bstep (se 1 (by rfl) ⟨139118, by rfl⟩ : syracuseStep 185491 = 278237) B278237
theorem B185507 : Blo 183802 185507 := bstep (se 1 (by rfl) ⟨139130, by rfl⟩ : syracuseStep 185507 = 278261) B278261
theorem B185523 : Blo 183802 185523 := bstep (se 1 (by rfl) ⟨139142, by rfl⟩ : syracuseStep 185523 = 278285) B278285
theorem B316595 : Blo 183802 316595 := bstep (se 1 (by rfl) ⟨237446, by rfl⟩ : syracuseStep 316595 = 474893) B474893
theorem B185539 : Blo 183802 185539 := bstep (se 1 (by rfl) ⟨139154, by rfl⟩ : syracuseStep 185539 = 278309) B278309
theorem B1594565 : Blo 183802 1594565 := bstep (se 4 (by rfl) ⟨149490, by rfl⟩ : syracuseStep 1594565 = 298981) B298981
theorem B185555 : Blo 183802 185555 := bstep (se 1 (by rfl) ⟨139166, by rfl⟩ : syracuseStep 185555 = 278333) B278333
theorem B185571 : Blo 183802 185571 := bstep (se 1 (by rfl) ⟨139178, by rfl⟩ : syracuseStep 185571 = 278357) B278357
theorem B185587 : Blo 183802 185587 := bstep (se 1 (by rfl) ⟨139190, by rfl⟩ : syracuseStep 185587 = 278381) B278381
theorem B185603 : Blo 183802 185603 := bstep (se 1 (by rfl) ⟨139202, by rfl⟩ : syracuseStep 185603 = 278405) B278405
theorem B185619 : Blo 183802 185619 := bstep (se 1 (by rfl) ⟨139214, by rfl⟩ : syracuseStep 185619 = 278429) B278429
theorem B185635 : Blo 183802 185635 := bstep (se 1 (by rfl) ⟨139226, by rfl⟩ : syracuseStep 185635 = 278453) B278453
theorem B415025 : Blo 183802 415025 := bstep (se 2 (by rfl) ⟨155634, by rfl⟩ : syracuseStep 415025 = 311269) B311269
theorem B185651 : Blo 183802 185651 := bstep (se 1 (by rfl) ⟨139238, by rfl⟩ : syracuseStep 185651 = 278477) B278477
theorem B316723 : Blo 183802 316723 := bstep (se 1 (by rfl) ⟨237542, by rfl⟩ : syracuseStep 316723 = 475085) B475085
theorem B415043 : Blo 183802 415043 := bstep (se 1 (by rfl) ⟨311282, by rfl⟩ : syracuseStep 415043 = 622565) B622565
theorem B185667 : Blo 183802 185667 := bstep (se 1 (by rfl) ⟨139250, by rfl⟩ : syracuseStep 185667 = 278501) B278501
theorem B185683 : Blo 183802 185683 := bstep (se 1 (by rfl) ⟨139262, by rfl⟩ : syracuseStep 185683 = 278525) B278525
theorem B185699 : Blo 183802 185699 := bstep (se 1 (by rfl) ⟨139274, by rfl⟩ : syracuseStep 185699 = 278549) B278549
theorem B447857 : Blo 183802 447857 := bstep (se 2 (by rfl) ⟨167946, by rfl⟩ : syracuseStep 447857 = 335893) B335893
theorem B185715 : Blo 183802 185715 := bstep (se 1 (by rfl) ⟨139286, by rfl⟩ : syracuseStep 185715 = 278573) B278573
theorem B349571 : Blo 183802 349571 := bstep (se 1 (by rfl) ⟨262178, by rfl⟩ : syracuseStep 349571 = 524357) B524357
theorem B185731 : Blo 183802 185731 := bstep (se 1 (by rfl) ⟨139298, by rfl⟩ : syracuseStep 185731 = 278597) B278597
theorem B185747 : Blo 183802 185747 := bstep (se 1 (by rfl) ⟨139310, by rfl⟩ : syracuseStep 185747 = 278621) B278621
theorem B185763 : Blo 183802 185763 := bstep (se 1 (by rfl) ⟨139322, by rfl⟩ : syracuseStep 185763 = 278645) B278645
theorem B185779 : Blo 183802 185779 := bstep (se 1 (by rfl) ⟨139334, by rfl⟩ : syracuseStep 185779 = 278669) B278669
theorem B316865 : Blo 183802 316865 := bstep (se 2 (by rfl) ⟨118824, by rfl⟩ : syracuseStep 316865 = 237649) B237649
theorem B185795 : Blo 183802 185795 := bstep (se 1 (by rfl) ⟨139346, by rfl⟩ : syracuseStep 185795 = 278693) B278693
theorem B185811 : Blo 183802 185811 := bstep (se 1 (by rfl) ⟨139358, by rfl⟩ : syracuseStep 185811 = 278717) B278717
theorem B185827 : Blo 183802 185827 := bstep (se 1 (by rfl) ⟨139370, by rfl⟩ : syracuseStep 185827 = 278741) B278741
theorem B185843 : Blo 183802 185843 := bstep (se 1 (by rfl) ⟨139382, by rfl⟩ : syracuseStep 185843 = 278765) B278765
theorem B185859 : Blo 183802 185859 := bstep (se 1 (by rfl) ⟨139394, by rfl⟩ : syracuseStep 185859 = 278789) B278789
theorem B185875 : Blo 183802 185875 := bstep (se 1 (by rfl) ⟨139406, by rfl⟩ : syracuseStep 185875 = 278813) B278813
theorem B185891 : Blo 183802 185891 := bstep (se 1 (by rfl) ⟨139418, by rfl⟩ : syracuseStep 185891 = 278837) B278837
theorem B185907 : Blo 183802 185907 := bstep (se 1 (by rfl) ⟨139430, by rfl⟩ : syracuseStep 185907 = 278861) B278861
theorem B185923 : Blo 183802 185923 := bstep (se 1 (by rfl) ⟨139442, by rfl⟩ : syracuseStep 185923 = 278885) B278885
theorem B415313 : Blo 183802 415313 := bstep (se 2 (by rfl) ⟨155742, by rfl⟩ : syracuseStep 415313 = 311485) B311485
theorem B185939 : Blo 183802 185939 := bstep (se 1 (by rfl) ⟨139454, by rfl⟩ : syracuseStep 185939 = 278909) B278909
theorem B415331 : Blo 183802 415331 := bstep (se 1 (by rfl) ⟨311498, by rfl⟩ : syracuseStep 415331 = 622997) B622997
theorem B185955 : Blo 183802 185955 := bstep (se 1 (by rfl) ⟨139466, by rfl⟩ : syracuseStep 185955 = 278933) B278933
theorem B185971 : Blo 183802 185971 := bstep (se 1 (by rfl) ⟨139478, by rfl⟩ : syracuseStep 185971 = 278957) B278957
theorem B185987 : Blo 183802 185987 := bstep (se 1 (by rfl) ⟨139490, by rfl⟩ : syracuseStep 185987 = 278981) B278981
theorem B284305 : Blo 183802 284305 := bstep (se 2 (by rfl) ⟨106614, by rfl⟩ : syracuseStep 284305 = 213229) B213229
theorem B186003 : Blo 183802 186003 := bstep (se 1 (by rfl) ⟨139502, by rfl⟩ : syracuseStep 186003 = 279005) B279005
theorem B349859 : Blo 183802 349859 := bstep (se 1 (by rfl) ⟨262394, by rfl⟩ : syracuseStep 349859 = 524789) B524789
theorem B186019 : Blo 183802 186019 := bstep (se 1 (by rfl) ⟨139514, by rfl⟩ : syracuseStep 186019 = 279029) B279029
theorem B186035 : Blo 183802 186035 := bstep (se 1 (by rfl) ⟨139526, by rfl⟩ : syracuseStep 186035 = 279053) B279053
theorem B186051 : Blo 183802 186051 := bstep (se 1 (by rfl) ⟨139538, by rfl⟩ : syracuseStep 186051 = 279077) B279077
theorem B186067 : Blo 183802 186067 := bstep (se 1 (by rfl) ⟨139550, by rfl⟩ : syracuseStep 186067 = 279101) B279101
theorem B186083 : Blo 183802 186083 := bstep (se 1 (by rfl) ⟨139562, by rfl⟩ : syracuseStep 186083 = 279125) B279125
theorem B939761 : Blo 183802 939761 := bstep (se 2 (by rfl) ⟨352410, by rfl⟩ : syracuseStep 939761 = 704821) B704821
theorem B186099 : Blo 183802 186099 := bstep (se 1 (by rfl) ⟨139574, by rfl⟩ : syracuseStep 186099 = 279149) B279149
theorem B186115 : Blo 183802 186115 := bstep (se 1 (by rfl) ⟨139586, by rfl⟩ : syracuseStep 186115 = 279173) B279173
theorem B186131 : Blo 183802 186131 := bstep (se 1 (by rfl) ⟨139598, by rfl⟩ : syracuseStep 186131 = 279197) B279197
theorem B186147 : Blo 183802 186147 := bstep (se 1 (by rfl) ⟨139610, by rfl⟩ : syracuseStep 186147 = 279221) B279221
theorem B907057 : Blo 183802 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B186163 : Blo 183802 186163 := bstep (se 1 (by rfl) ⟨139622, by rfl⟩ : syracuseStep 186163 = 279245) B279245
theorem B186179 : Blo 183802 186179 := bstep (se 1 (by rfl) ⟨139634, by rfl⟩ : syracuseStep 186179 = 279269) B279269
theorem B186195 : Blo 183802 186195 := bstep (se 1 (by rfl) ⟨139646, by rfl⟩ : syracuseStep 186195 = 279293) B279293
theorem B186211 : Blo 183802 186211 := bstep (se 1 (by rfl) ⟨139658, by rfl⟩ : syracuseStep 186211 = 279317) B279317
theorem B415601 : Blo 183802 415601 := bstep (se 2 (by rfl) ⟨155850, by rfl⟩ : syracuseStep 415601 = 311701) B311701
theorem B186227 : Blo 183802 186227 := bstep (se 1 (by rfl) ⟨139670, by rfl⟩ : syracuseStep 186227 = 279341) B279341
theorem B415619 : Blo 183802 415619 := bstep (se 1 (by rfl) ⟨311714, by rfl⟩ : syracuseStep 415619 = 623429) B623429
theorem B186243 : Blo 183802 186243 := bstep (se 1 (by rfl) ⟨139682, by rfl⟩ : syracuseStep 186243 = 279365) B279365
theorem B186259 : Blo 183802 186259 := bstep (se 1 (by rfl) ⟨139694, by rfl⟩ : syracuseStep 186259 = 279389) B279389
theorem B251795 : Blo 183802 251795 := bstep (se 1 (by rfl) ⟨188846, by rfl⟩ : syracuseStep 251795 = 377693) B377693
theorem B186275 : Blo 183802 186275 := bstep (se 1 (by rfl) ⟨139706, by rfl⟩ : syracuseStep 186275 = 279413) B279413
theorem B186291 : Blo 183802 186291 := bstep (se 1 (by rfl) ⟨139718, by rfl⟩ : syracuseStep 186291 = 279437) B279437
theorem B186307 : Blo 183802 186307 := bstep (se 1 (by rfl) ⟨139730, by rfl⟩ : syracuseStep 186307 = 279461) B279461
theorem B382915 : Blo 183802 382915 := bstep (se 1 (by rfl) ⟨287186, by rfl⟩ : syracuseStep 382915 = 574373) B574373
theorem B186323 : Blo 183802 186323 := bstep (se 1 (by rfl) ⟨139742, by rfl⟩ : syracuseStep 186323 = 279485) B279485
theorem B186339 : Blo 183802 186339 := bstep (se 1 (by rfl) ⟨139754, by rfl⟩ : syracuseStep 186339 = 279509) B279509
theorem B186355 : Blo 183802 186355 := bstep (se 1 (by rfl) ⟨139766, by rfl⟩ : syracuseStep 186355 = 279533) B279533
theorem B186371 : Blo 183802 186371 := bstep (se 1 (by rfl) ⟨139778, by rfl⟩ : syracuseStep 186371 = 279557) B279557
theorem B186387 : Blo 183802 186387 := bstep (se 1 (by rfl) ⟨139790, by rfl⟩ : syracuseStep 186387 = 279581) B279581
theorem B186403 : Blo 183802 186403 := bstep (se 1 (by rfl) ⟨139802, by rfl⟩ : syracuseStep 186403 = 279605) B279605
theorem B186419 : Blo 183802 186419 := bstep (se 1 (by rfl) ⟨139814, by rfl⟩ : syracuseStep 186419 = 279629) B279629
theorem B186435 : Blo 183802 186435 := bstep (se 1 (by rfl) ⟨139826, by rfl⟩ : syracuseStep 186435 = 279653) B279653
theorem B186451 : Blo 183802 186451 := bstep (se 1 (by rfl) ⟨139838, by rfl⟩ : syracuseStep 186451 = 279677) B279677
theorem B186467 : Blo 183802 186467 := bstep (se 1 (by rfl) ⟨139850, by rfl⟩ : syracuseStep 186467 = 279701) B279701
theorem B186483 : Blo 183802 186483 := bstep (se 1 (by rfl) ⟨139862, by rfl⟩ : syracuseStep 186483 = 279725) B279725
theorem B186499 : Blo 183802 186499 := bstep (se 1 (by rfl) ⟨139874, by rfl⟩ : syracuseStep 186499 = 279749) B279749
theorem B415889 : Blo 183802 415889 := bstep (se 2 (by rfl) ⟨155958, by rfl⟩ : syracuseStep 415889 = 311917) B311917
theorem B186515 : Blo 183802 186515 := bstep (se 1 (by rfl) ⟨139886, by rfl⟩ : syracuseStep 186515 = 279773) B279773
theorem B415907 : Blo 183802 415907 := bstep (se 1 (by rfl) ⟨311930, by rfl⟩ : syracuseStep 415907 = 623861) B623861
theorem B186531 : Blo 183802 186531 := bstep (se 1 (by rfl) ⟨139898, by rfl⟩ : syracuseStep 186531 = 279797) B279797
theorem B186547 : Blo 183802 186547 := bstep (se 1 (by rfl) ⟨139910, by rfl⟩ : syracuseStep 186547 = 279821) B279821
theorem B186563 : Blo 183802 186563 := bstep (se 1 (by rfl) ⟨139922, by rfl⟩ : syracuseStep 186563 = 279845) B279845
theorem B186579 : Blo 183802 186579 := bstep (se 1 (by rfl) ⟨139934, by rfl⟩ : syracuseStep 186579 = 279869) B279869
theorem B186595 : Blo 183802 186595 := bstep (se 1 (by rfl) ⟨139946, by rfl⟩ : syracuseStep 186595 = 279893) B279893
theorem B186611 : Blo 183802 186611 := bstep (se 1 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 186611 = 279917) B279917
theorem B252163 : Blo 183802 252163 := bstep (se 1 (by rfl) ⟨189122, by rfl⟩ : syracuseStep 252163 = 378245) B378245
theorem B186627 : Blo 183802 186627 := bstep (se 1 (by rfl) ⟨139970, by rfl⟩ : syracuseStep 186627 = 279941) B279941
theorem B186643 : Blo 183802 186643 := bstep (se 1 (by rfl) ⟨139982, by rfl⟩ : syracuseStep 186643 = 279965) B279965
theorem B186659 : Blo 183802 186659 := bstep (se 1 (by rfl) ⟨139994, by rfl⟩ : syracuseStep 186659 = 279989) B279989
theorem B186675 : Blo 183802 186675 := bstep (se 1 (by rfl) ⟨140006, by rfl⟩ : syracuseStep 186675 = 280013) B280013
theorem B186691 : Blo 183802 186691 := bstep (se 1 (by rfl) ⟨140018, by rfl⟩ : syracuseStep 186691 = 280037) B280037
theorem B186707 : Blo 183802 186707 := bstep (se 1 (by rfl) ⟨140030, by rfl⟩ : syracuseStep 186707 = 280061) B280061
theorem B186723 : Blo 183802 186723 := bstep (se 1 (by rfl) ⟨140042, by rfl⟩ : syracuseStep 186723 = 280085) B280085
theorem B186739 : Blo 183802 186739 := bstep (se 1 (by rfl) ⟨140054, by rfl⟩ : syracuseStep 186739 = 280109) B280109
theorem B186755 : Blo 183802 186755 := bstep (se 1 (by rfl) ⟨140066, by rfl⟩ : syracuseStep 186755 = 280133) B280133
theorem B186771 : Blo 183802 186771 := bstep (se 1 (by rfl) ⟨140078, by rfl⟩ : syracuseStep 186771 = 280157) B280157
theorem B186787 : Blo 183802 186787 := bstep (se 1 (by rfl) ⟨140090, by rfl⟩ : syracuseStep 186787 = 280181) B280181
theorem B416177 : Blo 183802 416177 := bstep (se 2 (by rfl) ⟨156066, by rfl⟩ : syracuseStep 416177 = 312133) B312133
theorem B186803 : Blo 183802 186803 := bstep (se 1 (by rfl) ⟨140102, by rfl⟩ : syracuseStep 186803 = 280205) B280205
theorem B416195 : Blo 183802 416195 := bstep (se 1 (by rfl) ⟨312146, by rfl⟩ : syracuseStep 416195 = 624293) B624293
theorem B186819 : Blo 183802 186819 := bstep (se 1 (by rfl) ⟨140114, by rfl⟩ : syracuseStep 186819 = 280229) B280229
theorem B186835 : Blo 183802 186835 := bstep (se 1 (by rfl) ⟨140126, by rfl⟩ : syracuseStep 186835 = 280253) B280253
theorem B186851 : Blo 183802 186851 := bstep (se 1 (by rfl) ⟨140138, by rfl⟩ : syracuseStep 186851 = 280277) B280277
theorem B711139 : Blo 183802 711139 := bstep (se 1 (by rfl) ⟨533354, by rfl⟩ : syracuseStep 711139 = 1066709) B1066709
theorem B186867 : Blo 183802 186867 := bstep (se 1 (by rfl) ⟨140150, by rfl⟩ : syracuseStep 186867 = 280301) B280301
theorem B186883 : Blo 183802 186883 := bstep (se 1 (by rfl) ⟨140162, by rfl⟩ : syracuseStep 186883 = 280325) B280325
theorem B186899 : Blo 183802 186899 := bstep (se 1 (by rfl) ⟨140174, by rfl⟩ : syracuseStep 186899 = 280349) B280349
theorem B186915 : Blo 183802 186915 := bstep (se 1 (by rfl) ⟨140186, by rfl⟩ : syracuseStep 186915 = 280373) B280373
theorem B186931 : Blo 183802 186931 := bstep (se 1 (by rfl) ⟨140198, by rfl⟩ : syracuseStep 186931 = 280397) B280397
theorem B186947 : Blo 183802 186947 := bstep (se 1 (by rfl) ⟨140210, by rfl⟩ : syracuseStep 186947 = 280421) B280421
theorem B350801 : Blo 183802 350801 := bstep (se 2 (by rfl) ⟨131550, by rfl⟩ : syracuseStep 350801 = 263101) B263101
theorem B186963 : Blo 183802 186963 := bstep (se 1 (by rfl) ⟨140222, by rfl⟩ : syracuseStep 186963 = 280445) B280445
theorem B186979 : Blo 183802 186979 := bstep (se 1 (by rfl) ⟨140234, by rfl⟩ : syracuseStep 186979 = 280469) B280469
theorem B186995 : Blo 183802 186995 := bstep (se 1 (by rfl) ⟨140246, by rfl⟩ : syracuseStep 186995 = 280493) B280493
theorem B187011 : Blo 183802 187011 := bstep (se 1 (by rfl) ⟨140258, by rfl⟩ : syracuseStep 187011 = 280517) B280517
theorem B187027 : Blo 183802 187027 := bstep (se 1 (by rfl) ⟨140270, by rfl⟩ : syracuseStep 187027 = 280541) B280541
theorem B187043 : Blo 183802 187043 := bstep (se 1 (by rfl) ⟨140282, by rfl⟩ : syracuseStep 187043 = 280565) B280565
theorem B187059 : Blo 183802 187059 := bstep (se 1 (by rfl) ⟨140294, by rfl⟩ : syracuseStep 187059 = 280589) B280589
theorem B187075 : Blo 183802 187075 := bstep (se 1 (by rfl) ⟨140306, by rfl⟩ : syracuseStep 187075 = 280613) B280613
theorem B416465 : Blo 183802 416465 := bstep (se 2 (by rfl) ⟨156174, by rfl⟩ : syracuseStep 416465 = 312349) B312349
theorem B187091 : Blo 183802 187091 := bstep (se 1 (by rfl) ⟨140318, by rfl⟩ : syracuseStep 187091 = 280637) B280637
theorem B416483 : Blo 183802 416483 := bstep (se 1 (by rfl) ⟨312362, by rfl⟩ : syracuseStep 416483 = 624725) B624725
theorem B187107 : Blo 183802 187107 := bstep (se 1 (by rfl) ⟨140330, by rfl⟩ : syracuseStep 187107 = 280661) B280661
theorem B187123 : Blo 183802 187123 := bstep (se 1 (by rfl) ⟨140342, by rfl⟩ : syracuseStep 187123 = 280685) B280685
theorem B187139 : Blo 183802 187139 := bstep (se 1 (by rfl) ⟨140354, by rfl⟩ : syracuseStep 187139 = 280709) B280709
theorem B187155 : Blo 183802 187155 := bstep (se 1 (by rfl) ⟨140366, by rfl⟩ : syracuseStep 187155 = 280733) B280733
theorem B187171 : Blo 183802 187171 := bstep (se 1 (by rfl) ⟨140378, by rfl⟩ : syracuseStep 187171 = 280757) B280757
theorem B187187 : Blo 183802 187187 := bstep (se 1 (by rfl) ⟨140390, by rfl⟩ : syracuseStep 187187 = 280781) B280781
theorem B187203 : Blo 183802 187203 := bstep (se 1 (by rfl) ⟨140402, by rfl⟩ : syracuseStep 187203 = 280805) B280805
theorem B187219 : Blo 183802 187219 := bstep (se 1 (by rfl) ⟨140414, by rfl⟩ : syracuseStep 187219 = 280829) B280829
theorem B187235 : Blo 183802 187235 := bstep (se 1 (by rfl) ⟨140426, by rfl⟩ : syracuseStep 187235 = 280853) B280853
theorem B187251 : Blo 183802 187251 := bstep (se 1 (by rfl) ⟨140438, by rfl⟩ : syracuseStep 187251 = 280877) B280877
theorem B187267 : Blo 183802 187267 := bstep (se 1 (by rfl) ⟨140450, by rfl⟩ : syracuseStep 187267 = 280901) B280901
theorem B187283 : Blo 183802 187283 := bstep (se 1 (by rfl) ⟨140462, by rfl⟩ : syracuseStep 187283 = 280925) B280925
theorem B187299 : Blo 183802 187299 := bstep (se 1 (by rfl) ⟨140474, by rfl⟩ : syracuseStep 187299 = 280949) B280949
theorem B187315 : Blo 183802 187315 := bstep (se 1 (by rfl) ⟨140486, by rfl⟩ : syracuseStep 187315 = 280973) B280973
theorem B187331 : Blo 183802 187331 := bstep (se 1 (by rfl) ⟨140498, by rfl⟩ : syracuseStep 187331 = 280997) B280997
theorem B187347 : Blo 183802 187347 := bstep (se 1 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 187347 = 281021) B281021
theorem B187363 : Blo 183802 187363 := bstep (se 1 (by rfl) ⟨140522, by rfl⟩ : syracuseStep 187363 = 281045) B281045
theorem B416753 : Blo 183802 416753 := bstep (se 2 (by rfl) ⟨156282, by rfl⟩ : syracuseStep 416753 = 312565) B312565
theorem B187379 : Blo 183802 187379 := bstep (se 1 (by rfl) ⟨140534, by rfl⟩ : syracuseStep 187379 = 281069) B281069
theorem B416771 : Blo 183802 416771 := bstep (se 1 (by rfl) ⟨312578, by rfl⟩ : syracuseStep 416771 = 625157) B625157
theorem B187395 : Blo 183802 187395 := bstep (se 1 (by rfl) ⟨140546, by rfl⟩ : syracuseStep 187395 = 281093) B281093
theorem B187411 : Blo 183802 187411 := bstep (se 1 (by rfl) ⟨140558, by rfl⟩ : syracuseStep 187411 = 281117) B281117
theorem B187427 : Blo 183802 187427 := bstep (se 1 (by rfl) ⟨140570, by rfl⟩ : syracuseStep 187427 = 281141) B281141
theorem B187443 : Blo 183802 187443 := bstep (se 1 (by rfl) ⟨140582, by rfl⟩ : syracuseStep 187443 = 281165) B281165
theorem B187459 : Blo 183802 187459 := bstep (se 1 (by rfl) ⟨140594, by rfl⟩ : syracuseStep 187459 = 281189) B281189
theorem B187475 : Blo 183802 187475 := bstep (se 1 (by rfl) ⟨140606, by rfl⟩ : syracuseStep 187475 = 281213) B281213
theorem B187491 : Blo 183802 187491 := bstep (se 1 (by rfl) ⟨140618, by rfl⟩ : syracuseStep 187491 = 281237) B281237
theorem B187507 : Blo 183802 187507 := bstep (se 1 (by rfl) ⟨140630, by rfl⟩ : syracuseStep 187507 = 281261) B281261
theorem B187523 : Blo 183802 187523 := bstep (se 1 (by rfl) ⟨140642, by rfl⟩ : syracuseStep 187523 = 281285) B281285
theorem B187539 : Blo 183802 187539 := bstep (se 1 (by rfl) ⟨140654, by rfl⟩ : syracuseStep 187539 = 281309) B281309
theorem B941219 : Blo 183802 941219 := bstep (se 1 (by rfl) ⟨705914, by rfl⟩ : syracuseStep 941219 = 1411829) B1411829
theorem B187555 : Blo 183802 187555 := bstep (se 1 (by rfl) ⟨140666, by rfl⟩ : syracuseStep 187555 = 281333) B281333
theorem B187571 : Blo 183802 187571 := bstep (se 1 (by rfl) ⟨140678, by rfl⟩ : syracuseStep 187571 = 281357) B281357
theorem B187587 : Blo 183802 187587 := bstep (se 1 (by rfl) ⟨140690, by rfl⟩ : syracuseStep 187587 = 281381) B281381
theorem B187603 : Blo 183802 187603 := bstep (se 1 (by rfl) ⟨140702, by rfl⟩ : syracuseStep 187603 = 281405) B281405
theorem B187619 : Blo 183802 187619 := bstep (se 1 (by rfl) ⟨140714, by rfl⟩ : syracuseStep 187619 = 281429) B281429
theorem B187635 : Blo 183802 187635 := bstep (se 1 (by rfl) ⟨140726, by rfl⟩ : syracuseStep 187635 = 281453) B281453
theorem B187651 : Blo 183802 187651 := bstep (se 1 (by rfl) ⟨140738, by rfl⟩ : syracuseStep 187651 = 281477) B281477
theorem B1072397 : Blo 183802 1072397 := bstep (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) B402149
theorem B417041 : Blo 183802 417041 := bstep (se 2 (by rfl) ⟨156390, by rfl⟩ : syracuseStep 417041 = 312781) B312781
theorem B187667 : Blo 183802 187667 := bstep (se 1 (by rfl) ⟨140750, by rfl⟩ : syracuseStep 187667 = 281501) B281501
theorem B417059 : Blo 183802 417059 := bstep (se 1 (by rfl) ⟨312794, by rfl⟩ : syracuseStep 417059 = 625589) B625589
theorem B187683 : Blo 183802 187683 := bstep (se 1 (by rfl) ⟨140762, by rfl⟩ : syracuseStep 187683 = 281525) B281525
theorem B187699 : Blo 183802 187699 := bstep (se 1 (by rfl) ⟨140774, by rfl⟩ : syracuseStep 187699 = 281549) B281549
theorem B187715 : Blo 183802 187715 := bstep (se 1 (by rfl) ⟨140786, by rfl⟩ : syracuseStep 187715 = 281573) B281573
theorem B187731 : Blo 183802 187731 := bstep (se 1 (by rfl) ⟨140798, by rfl⟩ : syracuseStep 187731 = 281597) B281597
theorem B187747 : Blo 183802 187747 := bstep (se 1 (by rfl) ⟨140810, by rfl⟩ : syracuseStep 187747 = 281621) B281621
theorem B187763 : Blo 183802 187763 := bstep (se 1 (by rfl) ⟨140822, by rfl⟩ : syracuseStep 187763 = 281645) B281645
theorem B187779 : Blo 183802 187779 := bstep (se 1 (by rfl) ⟨140834, by rfl⟩ : syracuseStep 187779 = 281669) B281669
theorem B187795 : Blo 183802 187795 := bstep (se 1 (by rfl) ⟨140846, by rfl⟩ : syracuseStep 187795 = 281693) B281693
theorem B351697 : Blo 183802 351697 := bstep (se 2 (by rfl) ⟨131886, by rfl⟩ : syracuseStep 351697 = 263773) B263773
theorem B908813 : Blo 183802 908813 := bstep (se 3 (by rfl) ⟨170402, by rfl⟩ : syracuseStep 908813 = 340805) B340805
theorem B417329 : Blo 183802 417329 := bstep (se 2 (by rfl) ⟨156498, by rfl⟩ : syracuseStep 417329 = 312997) B312997
theorem B417347 : Blo 183802 417347 := bstep (se 1 (by rfl) ⟨313010, by rfl⟩ : syracuseStep 417347 = 626021) B626021
theorem B351857 : Blo 183802 351857 := bstep (se 2 (by rfl) ⟨131946, by rfl⟩ : syracuseStep 351857 = 263893) B263893
theorem B450211 : Blo 183802 450211 := bstep (se 1 (by rfl) ⟨337658, by rfl⟩ : syracuseStep 450211 = 675317) B675317
theorem B2023181 : Blo 183802 2023181 := bstep (se 3 (by rfl) ⟨379346, by rfl⟩ : syracuseStep 2023181 = 758693) B758693
theorem B417617 : Blo 183802 417617 := bstep (se 2 (by rfl) ⟨156606, by rfl⟩ : syracuseStep 417617 = 313213) B313213
theorem B221011 : Blo 183802 221011 := bstep (se 1 (by rfl) ⟨165758, by rfl⟩ : syracuseStep 221011 = 331517) B331517
theorem B417635 : Blo 183802 417635 := bstep (se 1 (by rfl) ⟨313226, by rfl⟩ : syracuseStep 417635 = 626453) B626453
theorem B942029 : Blo 183802 942029 := bstep (se 3 (by rfl) ⟨176630, by rfl⟩ : syracuseStep 942029 = 353261) B353261
theorem B352259 : Blo 183802 352259 := bstep (se 1 (by rfl) ⟨264194, by rfl⟩ : syracuseStep 352259 = 528389) B528389
theorem B417905 : Blo 183802 417905 := bstep (se 2 (by rfl) ⟨156714, by rfl⟩ : syracuseStep 417905 = 313429) B313429
theorem B417923 : Blo 183802 417923 := bstep (se 1 (by rfl) ⟨313442, by rfl⟩ : syracuseStep 417923 = 626885) B626885
theorem B1335523 : Blo 183802 1335523 := bstep (se 1 (by rfl) ⟨1001642, by rfl⟩ : syracuseStep 1335523 = 2003285) B2003285
theorem B811363 : Blo 183802 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B4710797 : Blo 183802 4710797 := bstep (se 3 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 4710797 = 1766549) B1766549
theorem B418193 : Blo 183802 418193 := bstep (se 2 (by rfl) ⟨156822, by rfl⟩ : syracuseStep 418193 = 313645) B313645
theorem B418211 : Blo 183802 418211 := bstep (se 1 (by rfl) ⟨313658, by rfl⟩ : syracuseStep 418211 = 627317) B627317
theorem B418481 : Blo 183802 418481 := bstep (se 2 (by rfl) ⟨156930, by rfl⟩ : syracuseStep 418481 = 313861) B313861
theorem B418499 : Blo 183802 418499 := bstep (se 1 (by rfl) ⟨313874, by rfl⟩ : syracuseStep 418499 = 627749) B627749
theorem B1008389 : Blo 183802 1008389 := bstep (se 4 (by rfl) ⟨94536, by rfl⟩ : syracuseStep 1008389 = 189073) B189073
theorem B353155 : Blo 183802 353155 := bstep (se 1 (by rfl) ⟨264866, by rfl⟩ : syracuseStep 353155 = 529733) B529733
theorem B746417 : Blo 183802 746417 := bstep (se 2 (by rfl) ⟨279906, by rfl⟩ : syracuseStep 746417 = 559813) B559813
theorem B418769 : Blo 183802 418769 := bstep (se 2 (by rfl) ⟨157038, by rfl⟩ : syracuseStep 418769 = 314077) B314077
theorem B1893347 : Blo 183802 1893347 := bstep (se 1 (by rfl) ⟨1420010, by rfl⟩ : syracuseStep 1893347 = 2840021) B2840021
theorem B418787 : Blo 183802 418787 := bstep (se 1 (by rfl) ⟨314090, by rfl⟩ : syracuseStep 418787 = 628181) B628181
theorem B353315 : Blo 183802 353315 := bstep (se 1 (by rfl) ⟨264986, by rfl⟩ : syracuseStep 353315 = 529973) B529973
theorem B5366897 : Blo 183802 5366897 := bstep (se 2 (by rfl) ⟨2012586, by rfl⟩ : syracuseStep 5366897 = 4025173) B4025173
theorem B419057 : Blo 183802 419057 := bstep (se 2 (by rfl) ⟨157146, by rfl⟩ : syracuseStep 419057 = 314293) B314293
theorem B419075 : Blo 183802 419075 := bstep (se 1 (by rfl) ⟨314306, by rfl⟩ : syracuseStep 419075 = 628613) B628613
theorem B2876725 : Blo 183802 2876725 := bstep (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) B269693
theorem B419345 : Blo 183802 419345 := bstep (se 2 (by rfl) ⟨157254, by rfl⟩ : syracuseStep 419345 = 314509) B314509
theorem B419363 : Blo 183802 419363 := bstep (se 1 (by rfl) ⟨314522, by rfl⟩ : syracuseStep 419363 = 629045) B629045
theorem B1402595 : Blo 183802 1402595 := bstep (se 1 (by rfl) ⟨1051946, by rfl⟩ : syracuseStep 1402595 = 2103893) B2103893
theorem B419633 : Blo 183802 419633 := bstep (se 2 (by rfl) ⟨157362, by rfl⟩ : syracuseStep 419633 = 314725) B314725
theorem B419651 : Blo 183802 419651 := bstep (se 1 (by rfl) ⟨314738, by rfl⟩ : syracuseStep 419651 = 629477) B629477
theorem B419921 : Blo 183802 419921 := bstep (se 2 (by rfl) ⟨157470, by rfl⟩ : syracuseStep 419921 = 314941) B314941
theorem B354385 : Blo 183802 354385 := bstep (se 2 (by rfl) ⟨132894, by rfl⟩ : syracuseStep 354385 = 265789) B265789
theorem B419939 : Blo 183802 419939 := bstep (se 1 (by rfl) ⟨314954, by rfl⟩ : syracuseStep 419939 = 629909) B629909
theorem B1599587 : Blo 183802 1599587 := bstep (se 1 (by rfl) ⟨1199690, by rfl⟩ : syracuseStep 1599587 = 2399381) B2399381
theorem B583811 : Blo 183802 583811 := bstep (se 1 (by rfl) ⟨437858, by rfl⟩ : syracuseStep 583811 = 875717) B875717
theorem B2418929 : Blo 183802 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B1370353 : Blo 183802 1370353 := bstep (se 2 (by rfl) ⟨513882, by rfl⟩ : syracuseStep 1370353 = 1027765) B1027765
theorem B420209 : Blo 183802 420209 := bstep (se 2 (by rfl) ⟨157578, by rfl⟩ : syracuseStep 420209 = 315157) B315157
theorem B420227 : Blo 183802 420227 := bstep (se 1 (by rfl) ⟨315170, by rfl⟩ : syracuseStep 420227 = 630341) B630341
theorem B420497 : Blo 183802 420497 := bstep (se 2 (by rfl) ⟨157686, by rfl⟩ : syracuseStep 420497 = 315373) B315373
theorem B420515 : Blo 183802 420515 := bstep (se 1 (by rfl) ⟨315386, by rfl⟩ : syracuseStep 420515 = 630773) B630773
theorem B944945 : Blo 183802 944945 := bstep (se 2 (by rfl) ⟨354354, by rfl⟩ : syracuseStep 944945 = 708709) B708709
theorem B420785 : Blo 183802 420785 := bstep (se 2 (by rfl) ⟨157794, by rfl⟩ : syracuseStep 420785 = 315589) B315589
theorem B420803 : Blo 183802 420803 := bstep (se 1 (by rfl) ⟨315602, by rfl⟩ : syracuseStep 420803 = 631205) B631205
theorem B1338353 : Blo 183802 1338353 := bstep (se 2 (by rfl) ⟨501882, by rfl⟩ : syracuseStep 1338353 = 1003765) B1003765
theorem B355441 : Blo 183802 355441 := bstep (se 2 (by rfl) ⟨133290, by rfl⟩ : syracuseStep 355441 = 266581) B266581
theorem B421073 : Blo 183802 421073 := bstep (se 2 (by rfl) ⟨157902, by rfl⟩ : syracuseStep 421073 = 315805) B315805
theorem B421091 : Blo 183802 421091 := bstep (se 1 (by rfl) ⟨315818, by rfl⟩ : syracuseStep 421091 = 631637) B631637
theorem B749027 : Blo 183802 749027 := bstep (se 1 (by rfl) ⟨561770, by rfl⟩ : syracuseStep 749027 = 1123541) B1123541
theorem B421361 : Blo 183802 421361 := bstep (se 2 (by rfl) ⟨158010, by rfl⟩ : syracuseStep 421361 = 316021) B316021
theorem B421379 : Blo 183802 421379 := bstep (se 1 (by rfl) ⟨316034, by rfl⟩ : syracuseStep 421379 = 632069) B632069
theorem B355843 : Blo 183802 355843 := bstep (se 1 (by rfl) ⟨266882, by rfl⟩ : syracuseStep 355843 = 533765) B533765
theorem B355889 : Blo 183802 355889 := bstep (se 2 (by rfl) ⟨133458, by rfl⟩ : syracuseStep 355889 = 266917) B266917
theorem B421649 : Blo 183802 421649 := bstep (se 2 (by rfl) ⟨158118, by rfl⟩ : syracuseStep 421649 = 316237) B316237
theorem B421667 : Blo 183802 421667 := bstep (se 1 (by rfl) ⟨316250, by rfl⟩ : syracuseStep 421667 = 632501) B632501
theorem B356177 : Blo 183802 356177 := bstep (se 2 (by rfl) ⟨133566, by rfl⟩ : syracuseStep 356177 = 267133) B267133
theorem B421937 : Blo 183802 421937 := bstep (se 2 (by rfl) ⟨158226, by rfl⟩ : syracuseStep 421937 = 316453) B316453
theorem B421955 : Blo 183802 421955 := bstep (se 1 (by rfl) ⟨316466, by rfl⟩ : syracuseStep 421955 = 632933) B632933
theorem B946403 : Blo 183802 946403 := bstep (se 1 (by rfl) ⟨709802, by rfl⟩ : syracuseStep 946403 = 1419605) B1419605
theorem B3207395 : Blo 183802 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B422225 : Blo 183802 422225 := bstep (se 2 (by rfl) ⟨158334, by rfl⟩ : syracuseStep 422225 = 316669) B316669
theorem B422243 : Blo 183802 422243 := bstep (se 1 (by rfl) ⟨316682, by rfl⟩ : syracuseStep 422243 = 633365) B633365
theorem B3600949 : Blo 183802 3600949 := bstep (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) B337589
theorem B422513 : Blo 183802 422513 := bstep (se 2 (by rfl) ⟨158442, by rfl⟩ : syracuseStep 422513 = 316885) B316885
theorem B422531 : Blo 183802 422531 := bstep (se 1 (by rfl) ⟨316898, by rfl⟩ : syracuseStep 422531 = 633797) B633797
theorem B389873 : Blo 183802 389873 := bstep (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) B292405
theorem B848717 : Blo 183802 848717 := bstep (se 3 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 848717 = 318269) B318269
theorem B947213 : Blo 183802 947213 := bstep (se 3 (by rfl) ⟨177602, by rfl⟩ : syracuseStep 947213 = 355205) B355205
theorem B423299 : Blo 183802 423299 := bstep (se 1 (by rfl) ⟨317474, by rfl⟩ : syracuseStep 423299 = 634949) B634949
theorem B816817 : Blo 183802 816817 := bstep (se 2 (by rfl) ⟨306306, by rfl⟩ : syracuseStep 816817 = 612613) B612613
theorem B1603313 : Blo 183802 1603313 := bstep (se 2 (by rfl) ⟨601242, by rfl⟩ : syracuseStep 1603313 = 1202485) B1202485
theorem B620621 : Blo 183802 620621 := bstep (se 3 (by rfl) ⟨116366, by rfl⟩ : syracuseStep 620621 = 232733) B232733
theorem B620675 : Blo 183802 620675 := bstep (se 1 (by rfl) ⟨465506, by rfl⟩ : syracuseStep 620675 = 931013) B931013
theorem B751949 : Blo 183802 751949 := bstep (se 3 (by rfl) ⟨140990, by rfl⟩ : syracuseStep 751949 = 281981) B281981
theorem B620945 : Blo 183802 620945 := bstep (se 2 (by rfl) ⟨232854, by rfl⟩ : syracuseStep 620945 = 465709) B465709
theorem B227827 : Blo 183802 227827 := bstep (se 1 (by rfl) ⟨170870, by rfl⟩ : syracuseStep 227827 = 341741) B341741
theorem B752141 : Blo 183802 752141 := bstep (se 3 (by rfl) ⟨141026, by rfl⟩ : syracuseStep 752141 = 282053) B282053
theorem B1047437 : Blo 183802 1047437 := bstep (se 3 (by rfl) ⟨196394, by rfl⟩ : syracuseStep 1047437 = 392789) B392789
theorem B621485 : Blo 183802 621485 := bstep (se 3 (by rfl) ⟨116528, by rfl⟩ : syracuseStep 621485 = 233057) B233057
theorem B1407941 : Blo 183802 1407941 := bstep (se 4 (by rfl) ⟨131994, by rfl⟩ : syracuseStep 1407941 = 263989) B263989
theorem B621539 : Blo 183802 621539 := bstep (se 1 (by rfl) ⟨466154, by rfl⟩ : syracuseStep 621539 = 932309) B932309
theorem B588941 : Blo 183802 588941 := bstep (se 3 (by rfl) ⟨110426, by rfl⟩ : syracuseStep 588941 = 220853) B220853
theorem B621809 : Blo 183802 621809 := bstep (se 2 (by rfl) ⟨233178, by rfl⟩ : syracuseStep 621809 = 466357) B466357
theorem B2391281 : Blo 183802 2391281 := bstep (se 2 (by rfl) ⟨896730, by rfl⟩ : syracuseStep 2391281 = 1793461) B1793461
theorem B949553 : Blo 183802 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B786125 : Blo 183802 786125 := bstep (se 3 (by rfl) ⟨147398, by rfl⟩ : syracuseStep 786125 = 294797) B294797
theorem B884429 : Blo 183802 884429 := bstep (se 3 (by rfl) ⟨165830, by rfl⟩ : syracuseStep 884429 = 331661) B331661
theorem B622349 : Blo 183802 622349 := bstep (se 3 (by rfl) ⟨116690, by rfl⟩ : syracuseStep 622349 = 233381) B233381
theorem B1801997 : Blo 183802 1801997 := bstep (se 3 (by rfl) ⟨337874, by rfl⟩ : syracuseStep 1801997 = 675749) B675749
theorem B196403 : Blo 183802 196403 := bstep (se 1 (by rfl) ⟨147302, by rfl⟩ : syracuseStep 196403 = 294605) B294605
theorem B622403 : Blo 183802 622403 := bstep (se 1 (by rfl) ⟨466802, by rfl⟩ : syracuseStep 622403 = 933605) B933605
theorem B524141 : Blo 183802 524141 := bstep (se 3 (by rfl) ⟨98276, by rfl⟩ : syracuseStep 524141 = 196553) B196553
theorem B950129 : Blo 183802 950129 := bstep (se 2 (by rfl) ⟨356298, by rfl⟩ : syracuseStep 950129 = 712597) B712597
theorem B425873 : Blo 183802 425873 := bstep (se 2 (by rfl) ⟨159702, by rfl⟩ : syracuseStep 425873 = 319405) B319405
theorem B1802225 : Blo 183802 1802225 := bstep (se 2 (by rfl) ⟨675834, by rfl⟩ : syracuseStep 1802225 = 1351669) B1351669
theorem B393473 : Blo 183802 393473 := bstep (se 2 (by rfl) ⟨147552, by rfl⟩ : syracuseStep 393473 = 295105) B295105
theorem B197035 : Blo 183802 197035 := bstep (se 1 (by rfl) ⟨147776, by rfl⟩ : syracuseStep 197035 = 295553) B295553
theorem B623051 : Blo 183802 623051 := bstep (se 1 (by rfl) ⟨467288, by rfl⟩ : syracuseStep 623051 = 934577) B934577
theorem B1081817 : Blo 183802 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B393815 : Blo 183802 393815 := bstep (se 1 (by rfl) ⟨295361, by rfl⟩ : syracuseStep 393815 = 590723) B590723
theorem B8553053 : Blo 183802 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B2130583 : Blo 183802 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B525017 : Blo 183802 525017 := bstep (se 2 (by rfl) ⟨196881, by rfl⟩ : syracuseStep 525017 = 393763) B393763
theorem B262873 : Blo 183802 262873 := bstep (se 2 (by rfl) ⟨98577, by rfl⟩ : syracuseStep 262873 = 197155) B197155
theorem B623321 : Blo 183802 623321 := bstep (se 2 (by rfl) ⟨233745, by rfl⟩ : syracuseStep 623321 = 467491) B467491
theorem B1409885 : Blo 183802 1409885 := bstep (se 3 (by rfl) ⟨264353, by rfl⟩ : syracuseStep 1409885 = 528707) B528707
theorem B1574093 : Blo 183802 1574093 := bstep (se 3 (by rfl) ⟨295142, by rfl⟩ : syracuseStep 1574093 = 590285) B590285
theorem B787715 : Blo 183802 787715 := bstep (se 1 (by rfl) ⟨590786, by rfl⟩ : syracuseStep 787715 = 1181573) B1181573
theorem B1049921 : Blo 183802 1049921 := bstep (se 2 (by rfl) ⟨393720, by rfl⟩ : syracuseStep 1049921 = 787441) B787441
theorem B197975 : Blo 183802 197975 := bstep (se 1 (by rfl) ⟨148481, by rfl⟩ : syracuseStep 197975 = 296963) B296963
theorem B1344869 : Blo 183802 1344869 := bstep (se 4 (by rfl) ⟨126081, by rfl⟩ : syracuseStep 1344869 = 252163) B252163
theorem B624023 : Blo 183802 624023 := bstep (se 1 (by rfl) ⟨468017, by rfl⟩ : syracuseStep 624023 = 936035) B936035
theorem B3835633 : Blo 183802 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B624563 : Blo 183802 624563 := bstep (se 1 (by rfl) ⟨468422, by rfl⟩ : syracuseStep 624563 = 936845) B936845
theorem B264217 : Blo 183802 264217 := bstep (se 2 (by rfl) ⟨99081, by rfl⟩ : syracuseStep 264217 = 198163) B198163
theorem B526429 : Blo 183802 526429 := bstep (se 3 (by rfl) ⟨98705, by rfl⟩ : syracuseStep 526429 = 197411) B197411
theorem B264331 : Blo 183802 264331 := bstep (se 1 (by rfl) ⟨198248, by rfl⟩ : syracuseStep 264331 = 396497) B396497
theorem B624833 : Blo 183802 624833 := bstep (se 2 (by rfl) ⟨234312, by rfl⟩ : syracuseStep 624833 = 468625) B468625
theorem B755905 : Blo 183802 755905 := bstep (se 2 (by rfl) ⟨283464, by rfl⟩ : syracuseStep 755905 = 566929) B566929
theorem B526657 : Blo 183802 526657 := bstep (se 2 (by rfl) ⟨197496, by rfl⟩ : syracuseStep 526657 = 394993) B394993
theorem B4983389 : Blo 183802 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B526999 : Blo 183802 526999 := bstep (se 1 (by rfl) ⟨395249, by rfl⟩ : syracuseStep 526999 = 790499) B790499
theorem B625373 : Blo 183802 625373 := bstep (se 3 (by rfl) ⟨117257, by rfl⟩ : syracuseStep 625373 = 234515) B234515
theorem B297751 : Blo 183802 297751 := bstep (se 1 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 297751 = 446627) B446627
theorem B2001995 : Blo 183802 2001995 := bstep (se 1 (by rfl) ⟨1501496, by rfl⟩ : syracuseStep 2001995 = 3002993) B3002993
theorem B527705 : Blo 183802 527705 := bstep (se 2 (by rfl) ⟨197889, by rfl⟩ : syracuseStep 527705 = 395779) B395779
theorem B200107 : Blo 183802 200107 := bstep (se 1 (by rfl) ⟨150080, by rfl⟩ : syracuseStep 200107 = 300161) B300161
theorem B265675 : Blo 183802 265675 := bstep (se 1 (by rfl) ⟨199256, by rfl⟩ : syracuseStep 265675 = 398513) B398513
theorem B298571 : Blo 183802 298571 := bstep (se 1 (by rfl) ⟨223928, by rfl⟩ : syracuseStep 298571 = 447857) B447857
theorem B233047 : Blo 183802 233047 := bstep (se 1 (by rfl) ⟨174785, by rfl⟩ : syracuseStep 233047 = 349571) B349571
theorem B200279 : Blo 183802 200279 := bstep (se 1 (by rfl) ⟨150209, by rfl⟩ : syracuseStep 200279 = 300419) B300419
theorem B1052311 : Blo 183802 1052311 := bstep (se 1 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 1052311 = 1578467) B1578467
theorem B265943 : Blo 183802 265943 := bstep (se 1 (by rfl) ⟨199457, by rfl⟩ : syracuseStep 265943 = 398915) B398915
theorem B888641 : Blo 183802 888641 := bstep (se 2 (by rfl) ⟨333240, by rfl⟩ : syracuseStep 888641 = 666481) B666481
theorem B626507 : Blo 183802 626507 := bstep (se 1 (by rfl) ⟨469880, by rfl⟩ : syracuseStep 626507 = 939761) B939761
theorem B2691089 : Blo 183802 2691089 := bstep (se 2 (by rfl) ⟨1009158, by rfl⟩ : syracuseStep 2691089 = 2018317) B2018317
theorem B626777 : Blo 183802 626777 := bstep (se 2 (by rfl) ⟨235041, by rfl⟩ : syracuseStep 626777 = 470083) B470083
theorem B528563 : Blo 183802 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B233867 : Blo 183802 233867 := bstep (se 1 (by rfl) ⟨175400, by rfl⟩ : syracuseStep 233867 = 350801) B350801
theorem B397847 : Blo 183802 397847 := bstep (se 1 (by rfl) ⟨298385, by rfl⟩ : syracuseStep 397847 = 596771) B596771
theorem B332353 : Blo 183802 332353 := bstep (se 2 (by rfl) ⟨124632, by rfl⟩ : syracuseStep 332353 = 249265) B249265
theorem B1512037 : Blo 183802 1512037 := bstep (se 4 (by rfl) ⟨141753, by rfl⟩ : syracuseStep 1512037 = 283507) B283507
theorem B266905 : Blo 183802 266905 := bstep (se 2 (by rfl) ⟨100089, by rfl⟩ : syracuseStep 266905 = 200179) B200179
theorem B398027 : Blo 183802 398027 := bstep (se 1 (by rfl) ⟨298520, by rfl⟩ : syracuseStep 398027 = 597041) B597041
theorem B627479 : Blo 183802 627479 := bstep (se 1 (by rfl) ⟨470609, by rfl⟩ : syracuseStep 627479 = 941219) B941219
theorem B529345 : Blo 183802 529345 := bstep (se 2 (by rfl) ⟨198504, by rfl⟩ : syracuseStep 529345 = 397009) B397009
theorem B234571 : Blo 183802 234571 := bstep (se 1 (by rfl) ⟨175928, by rfl⟩ : syracuseStep 234571 = 351857) B351857
theorem B1348787 : Blo 183802 1348787 := bstep (se 1 (by rfl) ⟨1011590, by rfl⟩ : syracuseStep 1348787 = 2023181) B2023181
theorem B791831 : Blo 183802 791831 := bstep (se 1 (by rfl) ⟨593873, by rfl⟩ : syracuseStep 791831 = 1187747) B1187747
theorem B628019 : Blo 183802 628019 := bstep (se 1 (by rfl) ⟨471014, by rfl⟩ : syracuseStep 628019 = 942029) B942029
theorem B234839 : Blo 183802 234839 := bstep (se 1 (by rfl) ⟨176129, by rfl⟩ : syracuseStep 234839 = 352259) B352259
theorem B628289 : Blo 183802 628289 := bstep (se 2 (by rfl) ⟨235608, by rfl⟩ : syracuseStep 628289 = 471217) B471217
theorem B792139 : Blo 183802 792139 := bstep (se 1 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 792139 = 1188209) B1188209
theorem B792413 : Blo 183802 792413 := bstep (se 3 (by rfl) ⟨148577, by rfl⟩ : syracuseStep 792413 = 297155) B297155
theorem B497611 : Blo 183802 497611 := bstep (se 1 (by rfl) ⟨373208, by rfl⟩ : syracuseStep 497611 = 746417) B746417
theorem B202775 : Blo 183802 202775 := bstep (se 1 (by rfl) ⟨152081, by rfl⟩ : syracuseStep 202775 = 304163) B304163
theorem B235543 : Blo 183802 235543 := bstep (se 1 (by rfl) ⟨176657, by rfl⟩ : syracuseStep 235543 = 353315) B353315
theorem B2693189 : Blo 183802 2693189 := bstep (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) B504973
theorem B3577931 : Blo 183802 3577931 := bstep (se 1 (by rfl) ⟨2683448, by rfl⟩ : syracuseStep 3577931 = 5366897) B5366897
theorem B628829 : Blo 183802 628829 := bstep (se 3 (by rfl) ⟨117905, by rfl⟩ : syracuseStep 628829 = 235811) B235811
theorem B399667 : Blo 183802 399667 := bstep (se 1 (by rfl) ⟨299750, by rfl⟩ : syracuseStep 399667 = 599501) B599501
theorem B399745 : Blo 183802 399745 := bstep (se 2 (by rfl) ⟨149904, by rfl⟩ : syracuseStep 399745 = 299809) B299809
theorem B465497 : Blo 183802 465497 := bstep (se 2 (by rfl) ⟨174561, by rfl⟩ : syracuseStep 465497 = 349123) B349123
theorem B400153 : Blo 183802 400153 := bstep (se 2 (by rfl) ⟨150057, by rfl⟩ : syracuseStep 400153 = 300115) B300115
theorem B1612619 : Blo 183802 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B760769 : Blo 183802 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B662573 : Blo 183802 662573 := bstep (se 3 (by rfl) ⟨124232, by rfl⟩ : syracuseStep 662573 = 248465) B248465
theorem B1580107 : Blo 183802 1580107 := bstep (se 1 (by rfl) ⟨1185080, by rfl⟩ : syracuseStep 1580107 = 2370161) B2370161
theorem B793745 : Blo 183802 793745 := bstep (se 2 (by rfl) ⟨297654, by rfl⟩ : syracuseStep 793745 = 595309) B595309
theorem B629963 : Blo 183802 629963 := bstep (se 1 (by rfl) ⟨472472, by rfl⟩ : syracuseStep 629963 = 944945) B944945
theorem B892235 : Blo 183802 892235 := bstep (se 1 (by rfl) ⟨669176, by rfl⟩ : syracuseStep 892235 = 1338353) B1338353
theorem B1580381 : Blo 183802 1580381 := bstep (se 3 (by rfl) ⟨296321, by rfl⟩ : syracuseStep 1580381 = 592643) B592643
theorem B630233 : Blo 183802 630233 := bstep (se 2 (by rfl) ⟨236337, by rfl⟩ : syracuseStep 630233 = 472675) B472675
theorem B1285649 : Blo 183802 1285649 := bstep (se 2 (by rfl) ⟨482118, by rfl⟩ : syracuseStep 1285649 = 964237) B964237
theorem B1089089 : Blo 183802 1089089 := bstep (se 2 (by rfl) ⟨408408, by rfl⟩ : syracuseStep 1089089 = 816817) B816817
theorem B1384067 : Blo 183802 1384067 := bstep (se 1 (by rfl) ⟨1038050, by rfl⟩ : syracuseStep 1384067 = 2076101) B2076101
theorem B237259 : Blo 183802 237259 := bstep (se 1 (by rfl) ⟨177944, by rfl⟩ : syracuseStep 237259 = 355889) B355889
theorem B892889 : Blo 183802 892889 := bstep (se 2 (by rfl) ⟨334833, by rfl⟩ : syracuseStep 892889 = 669667) B669667
theorem B630935 : Blo 183802 630935 := bstep (se 1 (by rfl) ⟨473201, by rfl⟩ : syracuseStep 630935 = 946403) B946403
theorem B467147 : Blo 183802 467147 := bstep (se 1 (by rfl) ⟨350360, by rfl⟩ : syracuseStep 467147 = 700721) B700721
theorem B1581443 : Blo 183802 1581443 := bstep (se 1 (by rfl) ⟨1186082, by rfl⟩ : syracuseStep 1581443 = 2372165) B2372165
theorem B565811 : Blo 183802 565811 := bstep (se 1 (by rfl) ⟨424358, by rfl⟩ : syracuseStep 565811 = 848717) B848717
theorem B533081 : Blo 183802 533081 := bstep (se 2 (by rfl) ⟨199905, by rfl⟩ : syracuseStep 533081 = 399811) B399811
theorem B303769 : Blo 183802 303769 := bstep (se 2 (by rfl) ⟨113913, by rfl⟩ : syracuseStep 303769 = 227827) B227827
theorem B631475 : Blo 183802 631475 := bstep (se 1 (by rfl) ⟨473606, by rfl⟩ : syracuseStep 631475 = 947213) B947213
theorem B2859725 : Blo 183802 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B2138885 : Blo 183802 2138885 := bstep (se 4 (by rfl) ⟨200520, by rfl⟩ : syracuseStep 2138885 = 401041) B401041
theorem B631745 : Blo 183802 631745 := bstep (se 2 (by rfl) ⟨236904, by rfl⟩ : syracuseStep 631745 = 473809) B473809
theorem B468119 : Blo 183802 468119 := bstep (se 1 (by rfl) ⟨351089, by rfl⟩ : syracuseStep 468119 = 702179) B702179
theorem B632285 : Blo 183802 632285 := bstep (se 3 (by rfl) ⟨118553, by rfl⟩ : syracuseStep 632285 = 237107) B237107
theorem B665111 : Blo 183802 665111 := bstep (se 1 (by rfl) ⟨498833, by rfl⟩ : syracuseStep 665111 = 997667) B997667
theorem B796205 : Blo 183802 796205 := bstep (se 3 (by rfl) ⟨149288, by rfl⟩ : syracuseStep 796205 = 298577) B298577
theorem B501299 : Blo 183802 501299 := bstep (se 1 (by rfl) ⟨375974, by rfl⟩ : syracuseStep 501299 = 751949) B751949
theorem B501427 : Blo 183802 501427 := bstep (se 1 (by rfl) ⟨376070, by rfl⟩ : syracuseStep 501427 = 752141) B752141
theorem B468787 : Blo 183802 468787 := bstep (se 1 (by rfl) ⟨351590, by rfl⟩ : syracuseStep 468787 = 703181) B703181
theorem B534347 : Blo 183802 534347 := bstep (se 1 (by rfl) ⟨400760, by rfl⟩ : syracuseStep 534347 = 801521) B801521
theorem B796547 : Blo 183802 796547 := bstep (se 1 (by rfl) ⟨597410, by rfl⟩ : syracuseStep 796547 = 1194821) B1194821
theorem B698291 : Blo 183802 698291 := bstep (se 1 (by rfl) ⟨523718, by rfl⟩ : syracuseStep 698291 = 1047437) B1047437
theorem B468929 : Blo 183802 468929 := bstep (se 2 (by rfl) ⟨175848, by rfl⟩ : syracuseStep 468929 = 351697) B351697
theorem B1189849 : Blo 183802 1189849 := bstep (se 2 (by rfl) ⟨446193, by rfl⟩ : syracuseStep 1189849 = 892387) B892387
theorem B206923 : Blo 183802 206923 := bstep (se 1 (by rfl) ⟨155192, by rfl⟩ : syracuseStep 206923 = 310385) B310385
theorem B207031 : Blo 183802 207031 := bstep (se 1 (by rfl) ⟨155273, by rfl⟩ : syracuseStep 207031 = 310547) B310547
theorem B633035 : Blo 183802 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B600281 : Blo 183802 600281 := bstep (se 2 (by rfl) ⟨225105, by rfl⟩ : syracuseStep 600281 = 450211) B450211
theorem B207211 : Blo 183802 207211 := bstep (se 1 (by rfl) ⟨155408, by rfl⟩ : syracuseStep 207211 = 310817) B310817
theorem B207319 : Blo 183802 207319 := bstep (se 1 (by rfl) ⟨155489, by rfl⟩ : syracuseStep 207319 = 310979) B310979
theorem B633419 : Blo 183802 633419 := bstep (se 1 (by rfl) ⟨475064, by rfl⟩ : syracuseStep 633419 = 950129) B950129
theorem B207499 : Blo 183802 207499 := bstep (se 1 (by rfl) ⟨155624, by rfl⟩ : syracuseStep 207499 = 311249) B311249
theorem B207607 : Blo 183802 207607 := bstep (se 1 (by rfl) ⟨155705, by rfl⟩ : syracuseStep 207607 = 311411) B311411
theorem B1059601 : Blo 183802 1059601 := bstep (se 2 (by rfl) ⟨397350, by rfl⟩ : syracuseStep 1059601 = 794701) B794701
theorem B633689 : Blo 183802 633689 := bstep (se 2 (by rfl) ⟨237633, by rfl⟩ : syracuseStep 633689 = 475267) B475267
theorem B207787 : Blo 183802 207787 := bstep (se 1 (by rfl) ⟨155840, by rfl⟩ : syracuseStep 207787 = 311681) B311681
theorem B2010035 : Blo 183802 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B1780697 : Blo 183802 1780697 := bstep (se 2 (by rfl) ⟨667761, by rfl⟩ : syracuseStep 1780697 = 1335523) B1335523
theorem B207895 : Blo 183802 207895 := bstep (se 1 (by rfl) ⟨155921, by rfl⟩ : syracuseStep 207895 = 311843) B311843
theorem B666755 : Blo 183802 666755 := bstep (se 1 (by rfl) ⟨500066, by rfl⟩ : syracuseStep 666755 = 1000133) B1000133
theorem B470195 : Blo 183802 470195 := bstep (se 1 (by rfl) ⟨352646, by rfl⟩ : syracuseStep 470195 = 705293) B705293
theorem B208075 : Blo 183802 208075 := bstep (se 1 (by rfl) ⟨156056, by rfl⟩ : syracuseStep 208075 = 312113) B312113
theorem B208183 : Blo 183802 208183 := bstep (se 1 (by rfl) ⟨156137, by rfl⟩ : syracuseStep 208183 = 312275) B312275
theorem B699779 : Blo 183802 699779 := bstep (se 1 (by rfl) ⟨524834, by rfl⟩ : syracuseStep 699779 = 1049669) B1049669
theorem B404939 : Blo 183802 404939 := bstep (se 1 (by rfl) ⟨303704, by rfl⟩ : syracuseStep 404939 = 607409) B607409
theorem B208363 : Blo 183802 208363 := bstep (se 1 (by rfl) ⟨156272, by rfl⟩ : syracuseStep 208363 = 312545) B312545
theorem B634391 : Blo 183802 634391 := bstep (se 1 (by rfl) ⟨475793, by rfl⟩ : syracuseStep 634391 = 951587) B951587
theorem B667187 : Blo 183802 667187 := bstep (se 1 (by rfl) ⟨500390, by rfl⟩ : syracuseStep 667187 = 1000781) B1000781
theorem B208471 : Blo 183802 208471 := bstep (se 1 (by rfl) ⟨156353, by rfl⟩ : syracuseStep 208471 = 312707) B312707
theorem B470731 : Blo 183802 470731 := bstep (se 1 (by rfl) ⟨353048, by rfl⟩ : syracuseStep 470731 = 706097) B706097
theorem B208651 : Blo 183802 208651 := bstep (se 1 (by rfl) ⟨156488, by rfl⟩ : syracuseStep 208651 = 312977) B312977
theorem B700235 : Blo 183802 700235 := bstep (se 1 (by rfl) ⟨525176, by rfl⟩ : syracuseStep 700235 = 1050353) B1050353
theorem B470873 : Blo 183802 470873 := bstep (se 2 (by rfl) ⟨176577, by rfl⟩ : syracuseStep 470873 = 353155) B353155
theorem B208759 : Blo 183802 208759 := bstep (se 1 (by rfl) ⟨156569, by rfl⟩ : syracuseStep 208759 = 313139) B313139
theorem B700433 : Blo 183802 700433 := bstep (se 2 (by rfl) ⟨262662, by rfl⟩ : syracuseStep 700433 = 525325) B525325
theorem B208939 : Blo 183802 208939 := bstep (se 1 (by rfl) ⟨156704, by rfl⟩ : syracuseStep 208939 = 313409) B313409
theorem B209047 : Blo 183802 209047 := bstep (se 1 (by rfl) ⟨156785, by rfl⟩ : syracuseStep 209047 = 313571) B313571
theorem B798923 : Blo 183802 798923 := bstep (se 1 (by rfl) ⟨599192, by rfl⟩ : syracuseStep 798923 = 1198385) B1198385
theorem B209227 : Blo 183802 209227 := bstep (se 1 (by rfl) ⟨156920, by rfl⟩ : syracuseStep 209227 = 313841) B313841
theorem B209335 : Blo 183802 209335 := bstep (se 1 (by rfl) ⟨157001, by rfl⟩ : syracuseStep 209335 = 314003) B314003
theorem B209515 : Blo 183802 209515 := bstep (se 1 (by rfl) ⟨157136, by rfl⟩ : syracuseStep 209515 = 314273) B314273
theorem B471703 : Blo 183802 471703 := bstep (se 1 (by rfl) ⟨353777, by rfl⟩ : syracuseStep 471703 = 707555) B707555
theorem B209623 : Blo 183802 209623 := bstep (se 1 (by rfl) ⟨157217, by rfl⟩ : syracuseStep 209623 = 314435) B314435
theorem B701207 : Blo 183802 701207 := bstep (se 1 (by rfl) ⟨525905, by rfl⟩ : syracuseStep 701207 = 1051811) B1051811
theorem B209803 : Blo 183802 209803 := bstep (se 1 (by rfl) ⟨157352, by rfl⟩ : syracuseStep 209803 = 314705) B314705
theorem B701405 : Blo 183802 701405 := bstep (se 3 (by rfl) ⟨131513, by rfl⟩ : syracuseStep 701405 = 263027) B263027
theorem B209911 : Blo 183802 209911 := bstep (se 1 (by rfl) ⟨157433, by rfl⟩ : syracuseStep 209911 = 314867) B314867
theorem B472139 : Blo 183802 472139 := bstep (se 1 (by rfl) ⟨354104, by rfl⟩ : syracuseStep 472139 = 708209) B708209
theorem B799895 : Blo 183802 799895 := bstep (se 1 (by rfl) ⟨599921, by rfl⟩ : syracuseStep 799895 = 1199843) B1199843
theorem B210091 : Blo 183802 210091 := bstep (se 1 (by rfl) ⟨157568, by rfl⟩ : syracuseStep 210091 = 315137) B315137
theorem B505025 : Blo 183802 505025 := bstep (se 2 (by rfl) ⟨189384, by rfl⟩ : syracuseStep 505025 = 378769) B378769
theorem B275723 : Blo 183802 275723 := bstep (se 1 (by rfl) ⟨206792, by rfl⟩ : syracuseStep 275723 = 413585) B413585
theorem B275735 : Blo 183802 275735 := bstep (se 1 (by rfl) ⟨206801, by rfl⟩ : syracuseStep 275735 = 413603) B413603
theorem B210199 : Blo 183802 210199 := bstep (se 1 (by rfl) ⟨157649, by rfl⟩ : syracuseStep 210199 = 315299) B315299
theorem B275801 : Blo 183802 275801 := bstep (se 2 (by rfl) ⟨103425, by rfl⟩ : syracuseStep 275801 = 206851) B206851
theorem B669017 : Blo 183802 669017 := bstep (se 2 (by rfl) ⟨250881, by rfl⟩ : syracuseStep 669017 = 501763) B501763
theorem B472513 : Blo 183802 472513 := bstep (se 2 (by rfl) ⟨177192, by rfl⟩ : syracuseStep 472513 = 354385) B354385
theorem B275915 : Blo 183802 275915 := bstep (se 1 (by rfl) ⟨206936, by rfl⟩ : syracuseStep 275915 = 413873) B413873
theorem B210379 : Blo 183802 210379 := bstep (se 1 (by rfl) ⟨157784, by rfl⟩ : syracuseStep 210379 = 315569) B315569
theorem B275927 : Blo 183802 275927 := bstep (se 1 (by rfl) ⟨206945, by rfl⟩ : syracuseStep 275927 = 413891) B413891
theorem B3552781 : Blo 183802 3552781 := bstep (se 3 (by rfl) ⟨666146, by rfl⟩ : syracuseStep 3552781 = 1332293) B1332293
theorem B2668049 : Blo 183802 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B2373137 : Blo 183802 2373137 := bstep (se 2 (by rfl) ⟨889926, by rfl⟩ : syracuseStep 2373137 = 1779853) B1779853
theorem B898577 : Blo 183802 898577 := bstep (se 2 (by rfl) ⟨336966, by rfl⟩ : syracuseStep 898577 = 673933) B673933
theorem B275993 : Blo 183802 275993 := bstep (se 2 (by rfl) ⟨103497, by rfl⟩ : syracuseStep 275993 = 206995) B206995
theorem B210487 : Blo 183802 210487 := bstep (se 1 (by rfl) ⟨157865, by rfl⟩ : syracuseStep 210487 = 315731) B315731
theorem B276107 : Blo 183802 276107 := bstep (se 1 (by rfl) ⟨207080, by rfl⟩ : syracuseStep 276107 = 414161) B414161
theorem B276119 : Blo 183802 276119 := bstep (se 1 (by rfl) ⟨207089, by rfl⟩ : syracuseStep 276119 = 414179) B414179
theorem B669377 : Blo 183802 669377 := bstep (se 2 (by rfl) ⟨251016, by rfl⟩ : syracuseStep 669377 = 502033) B502033
theorem B636619 : Blo 183802 636619 := bstep (se 1 (by rfl) ⟨477464, by rfl⟩ : syracuseStep 636619 = 954929) B954929
theorem B276185 : Blo 183802 276185 := bstep (se 2 (by rfl) ⟨103569, by rfl⟩ : syracuseStep 276185 = 207139) B207139
theorem B210667 : Blo 183802 210667 := bstep (se 1 (by rfl) ⟨158000, by rfl⟩ : syracuseStep 210667 = 316001) B316001
theorem B800563 : Blo 183802 800563 := bstep (se 1 (by rfl) ⟨600422, by rfl⟩ : syracuseStep 800563 = 1200845) B1200845
theorem B276299 : Blo 183802 276299 := bstep (se 1 (by rfl) ⟨207224, by rfl⟩ : syracuseStep 276299 = 414449) B414449
theorem B276311 : Blo 183802 276311 := bstep (se 1 (by rfl) ⟨207233, by rfl⟩ : syracuseStep 276311 = 414467) B414467
theorem B210775 : Blo 183802 210775 := bstep (se 1 (by rfl) ⟨158081, by rfl⟩ : syracuseStep 210775 = 316163) B316163
theorem B604055 : Blo 183802 604055 := bstep (se 1 (by rfl) ⟨453041, by rfl⟩ : syracuseStep 604055 = 906083) B906083
theorem B276377 : Blo 183802 276377 := bstep (se 2 (by rfl) ⟨103641, by rfl⟩ : syracuseStep 276377 = 207283) B207283
theorem B276491 : Blo 183802 276491 := bstep (se 1 (by rfl) ⟨207368, by rfl⟩ : syracuseStep 276491 = 414737) B414737
theorem B210955 : Blo 183802 210955 := bstep (se 1 (by rfl) ⟨158216, by rfl⟩ : syracuseStep 210955 = 316433) B316433
theorem B473111 : Blo 183802 473111 := bstep (se 1 (by rfl) ⟨354833, by rfl⟩ : syracuseStep 473111 = 709667) B709667
theorem B276503 : Blo 183802 276503 := bstep (se 1 (by rfl) ⟨207377, by rfl⟩ : syracuseStep 276503 = 414755) B414755
theorem B374807 : Blo 183802 374807 := bstep (se 1 (by rfl) ⟨281105, by rfl⟩ : syracuseStep 374807 = 562211) B562211
theorem B276569 : Blo 183802 276569 := bstep (se 2 (by rfl) ⟨103713, by rfl⟩ : syracuseStep 276569 = 207427) B207427
theorem B211063 : Blo 183802 211063 := bstep (se 1 (by rfl) ⟨158297, by rfl⟩ : syracuseStep 211063 = 316595) B316595
theorem B1063043 : Blo 183802 1063043 := bstep (se 1 (by rfl) ⟨797282, by rfl⟩ : syracuseStep 1063043 = 1594565) B1594565
theorem B276683 : Blo 183802 276683 := bstep (se 1 (by rfl) ⟨207512, by rfl⟩ : syracuseStep 276683 = 415025) B415025
theorem B1325261 : Blo 183802 1325261 := bstep (se 3 (by rfl) ⟨248486, by rfl⟩ : syracuseStep 1325261 = 496973) B496973
theorem B276695 : Blo 183802 276695 := bstep (se 1 (by rfl) ⟨207521, by rfl⟩ : syracuseStep 276695 = 415043) B415043
theorem B276761 : Blo 183802 276761 := bstep (se 2 (by rfl) ⟨103785, by rfl⟩ : syracuseStep 276761 = 207571) B207571
theorem B211243 : Blo 183802 211243 := bstep (se 1 (by rfl) ⟨158432, by rfl⟩ : syracuseStep 211243 = 316865) B316865
theorem B276875 : Blo 183802 276875 := bstep (se 1 (by rfl) ⟨207656, by rfl⟩ : syracuseStep 276875 = 415313) B415313
theorem B276887 : Blo 183802 276887 := bstep (se 1 (by rfl) ⟨207665, by rfl⟩ : syracuseStep 276887 = 415331) B415331
theorem B276953 : Blo 183802 276953 := bstep (se 2 (by rfl) ⟨103857, by rfl⟩ : syracuseStep 276953 = 207715) B207715
theorem B10271245 : Blo 183802 10271245 := bstep (se 3 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 10271245 = 3851717) B3851717
theorem B277067 : Blo 183802 277067 := bstep (se 1 (by rfl) ⟨207800, by rfl⟩ : syracuseStep 277067 = 415601) B415601
theorem B277079 : Blo 183802 277079 := bstep (se 1 (by rfl) ⟨207809, by rfl⟩ : syracuseStep 277079 = 415619) B415619
theorem B277145 : Blo 183802 277145 := bstep (se 2 (by rfl) ⟨103929, by rfl⟩ : syracuseStep 277145 = 207859) B207859
theorem B277259 : Blo 183802 277259 := bstep (se 1 (by rfl) ⟨207944, by rfl⟩ : syracuseStep 277259 = 415889) B415889
theorem B277271 : Blo 183802 277271 := bstep (se 1 (by rfl) ⟨207953, by rfl⟩ : syracuseStep 277271 = 415907) B415907
theorem B473921 : Blo 183802 473921 := bstep (se 2 (by rfl) ⟨177720, by rfl⟩ : syracuseStep 473921 = 355441) B355441
theorem B277337 : Blo 183802 277337 := bstep (se 2 (by rfl) ⟨104001, by rfl⟩ : syracuseStep 277337 = 208003) B208003
theorem B703363 : Blo 183802 703363 := bstep (se 1 (by rfl) ⟨527522, by rfl⟩ : syracuseStep 703363 = 1055045) B1055045
theorem B310169 : Blo 183802 310169 := bstep (se 2 (by rfl) ⟨116313, by rfl⟩ : syracuseStep 310169 = 232627) B232627
theorem B277451 : Blo 183802 277451 := bstep (se 1 (by rfl) ⟨208088, by rfl⟩ : syracuseStep 277451 = 416177) B416177
theorem B277463 : Blo 183802 277463 := bstep (se 1 (by rfl) ⟨208097, by rfl⟩ : syracuseStep 277463 = 416195) B416195
theorem B1326041 : Blo 183802 1326041 := bstep (se 2 (by rfl) ⟨497265, by rfl⟩ : syracuseStep 1326041 = 994531) B994531
theorem B801809 : Blo 183802 801809 := bstep (se 2 (by rfl) ⟨300678, by rfl⟩ : syracuseStep 801809 = 601357) B601357
theorem B310297 : Blo 183802 310297 := bstep (se 2 (by rfl) ⟨116361, by rfl⟩ : syracuseStep 310297 = 232723) B232723
theorem B277529 : Blo 183802 277529 := bstep (se 2 (by rfl) ⟨104073, by rfl⟩ : syracuseStep 277529 = 208147) B208147
theorem B932957 : Blo 183802 932957 := bstep (se 3 (by rfl) ⟨174929, by rfl⟩ : syracuseStep 932957 = 349859) B349859
theorem B277643 : Blo 183802 277643 := bstep (se 1 (by rfl) ⟨208232, by rfl⟩ : syracuseStep 277643 = 416465) B416465
theorem B277655 : Blo 183802 277655 := bstep (se 1 (by rfl) ⟨208241, by rfl⟩ : syracuseStep 277655 = 416483) B416483
theorem B703667 : Blo 183802 703667 := bstep (se 1 (by rfl) ⟨527750, by rfl⟩ : syracuseStep 703667 = 1055501) B1055501
theorem B277721 : Blo 183802 277721 := bstep (se 2 (by rfl) ⟨104145, by rfl⟩ : syracuseStep 277721 = 208291) B208291
theorem B277835 : Blo 183802 277835 := bstep (se 1 (by rfl) ⟨208376, by rfl⟩ : syracuseStep 277835 = 416753) B416753
theorem B277847 : Blo 183802 277847 := bstep (se 1 (by rfl) ⟨208385, by rfl⟩ : syracuseStep 277847 = 416771) B416771
theorem B474457 : Blo 183802 474457 := bstep (se 2 (by rfl) ⟨177921, by rfl⟩ : syracuseStep 474457 = 355843) B355843
theorem B277913 : Blo 183802 277913 := bstep (se 2 (by rfl) ⟨104217, by rfl⟩ : syracuseStep 277913 = 208435) B208435
theorem B278027 : Blo 183802 278027 := bstep (se 1 (by rfl) ⟨208520, by rfl⟩ : syracuseStep 278027 = 417041) B417041
theorem B278039 : Blo 183802 278039 := bstep (se 1 (by rfl) ⟨208529, by rfl⟩ : syracuseStep 278039 = 417059) B417059
theorem B310871 : Blo 183802 310871 := bstep (se 1 (by rfl) ⟨233153, by rfl⟩ : syracuseStep 310871 = 466307) B466307
theorem B278105 : Blo 183802 278105 := bstep (se 2 (by rfl) ⟨104289, by rfl⟩ : syracuseStep 278105 = 208579) B208579
theorem B605875 : Blo 183802 605875 := bstep (se 1 (by rfl) ⟨454406, by rfl⟩ : syracuseStep 605875 = 908813) B908813
theorem B278219 : Blo 183802 278219 := bstep (se 1 (by rfl) ⟨208664, by rfl⟩ : syracuseStep 278219 = 417329) B417329
theorem B310999 : Blo 183802 310999 := bstep (se 1 (by rfl) ⟨233249, by rfl⟩ : syracuseStep 310999 = 466499) B466499
theorem B278231 : Blo 183802 278231 := bstep (se 1 (by rfl) ⟨208673, by rfl⟩ : syracuseStep 278231 = 417347) B417347
theorem B671453 : Blo 183802 671453 := bstep (se 3 (by rfl) ⟨125897, by rfl⟩ : syracuseStep 671453 = 251795) B251795
theorem B278297 : Blo 183802 278297 := bstep (se 2 (by rfl) ⟨104361, by rfl⟩ : syracuseStep 278297 = 208723) B208723
theorem B704321 : Blo 183802 704321 := bstep (se 2 (by rfl) ⟨264120, by rfl⟩ : syracuseStep 704321 = 528241) B528241
theorem B278411 : Blo 183802 278411 := bstep (se 1 (by rfl) ⟨208808, by rfl⟩ : syracuseStep 278411 = 417617) B417617
theorem B278423 : Blo 183802 278423 := bstep (se 1 (by rfl) ⟨208817, by rfl⟩ : syracuseStep 278423 = 417635) B417635
theorem B278489 : Blo 183802 278489 := bstep (se 2 (by rfl) ⟨104433, by rfl⟩ : syracuseStep 278489 = 208867) B208867
theorem B278603 : Blo 183802 278603 := bstep (se 1 (by rfl) ⟨208952, by rfl⟩ : syracuseStep 278603 = 417905) B417905
theorem B278615 : Blo 183802 278615 := bstep (se 1 (by rfl) ⟨208961, by rfl⟩ : syracuseStep 278615 = 417923) B417923
theorem B278681 : Blo 183802 278681 := bstep (se 2 (by rfl) ⟨104505, by rfl⟩ : syracuseStep 278681 = 209011) B209011
theorem B5062837 : Blo 183802 5062837 := bstep (se 5 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 5062837 = 474641) B474641
theorem B278795 : Blo 183802 278795 := bstep (se 1 (by rfl) ⟨209096, by rfl⟩ : syracuseStep 278795 = 418193) B418193
theorem B278807 : Blo 183802 278807 := bstep (se 1 (by rfl) ⟨209105, by rfl⟩ : syracuseStep 278807 = 418211) B418211
theorem B901421 : Blo 183802 901421 := bstep (se 3 (by rfl) ⟨169016, by rfl⟩ : syracuseStep 901421 = 338033) B338033
theorem B311627 : Blo 183802 311627 := bstep (se 1 (by rfl) ⟨233720, by rfl⟩ : syracuseStep 311627 = 467441) B467441
theorem B278873 : Blo 183802 278873 := bstep (se 2 (by rfl) ⟨104577, by rfl⟩ : syracuseStep 278873 = 209155) B209155
theorem B311755 : Blo 183802 311755 := bstep (se 1 (by rfl) ⟨233816, by rfl⟩ : syracuseStep 311755 = 467633) B467633
theorem B278987 : Blo 183802 278987 := bstep (se 1 (by rfl) ⟨209240, by rfl⟩ : syracuseStep 278987 = 418481) B418481
theorem B278999 : Blo 183802 278999 := bstep (se 1 (by rfl) ⟨209249, by rfl⟩ : syracuseStep 278999 = 418499) B418499
theorem B1065433 : Blo 183802 1065433 := bstep (se 2 (by rfl) ⟨399537, by rfl⟩ : syracuseStep 1065433 = 799075) B799075
theorem B672259 : Blo 183802 672259 := bstep (se 1 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 672259 = 1008389) B1008389
theorem B279065 : Blo 183802 279065 := bstep (se 2 (by rfl) ⟨104649, by rfl⟩ : syracuseStep 279065 = 209299) B209299
theorem B442945 : Blo 183802 442945 := bstep (se 2 (by rfl) ⟨166104, by rfl⟩ : syracuseStep 442945 = 332209) B332209
theorem B311897 : Blo 183802 311897 := bstep (se 2 (by rfl) ⟨116961, by rfl⟩ : syracuseStep 311897 = 233923) B233923
theorem B1065565 : Blo 183802 1065565 := bstep (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) B399587
theorem B279179 : Blo 183802 279179 := bstep (se 1 (by rfl) ⟨209384, by rfl⟩ : syracuseStep 279179 = 418769) B418769
theorem B1262231 : Blo 183802 1262231 := bstep (se 1 (by rfl) ⟨946673, by rfl⟩ : syracuseStep 1262231 = 1893347) B1893347
theorem B279191 : Blo 183802 279191 := bstep (se 1 (by rfl) ⟨209393, by rfl⟩ : syracuseStep 279191 = 418787) B418787
theorem B312025 : Blo 183802 312025 := bstep (se 2 (by rfl) ⟨117009, by rfl⟩ : syracuseStep 312025 = 234019) B234019
theorem B279257 : Blo 183802 279257 := bstep (se 2 (by rfl) ⟨104721, by rfl⟩ : syracuseStep 279257 = 209443) B209443
theorem B4801265 : Blo 183802 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B279371 : Blo 183802 279371 := bstep (se 1 (by rfl) ⟨209528, by rfl⟩ : syracuseStep 279371 = 419057) B419057
theorem B279383 : Blo 183802 279383 := bstep (se 1 (by rfl) ⟨209537, by rfl⟩ : syracuseStep 279383 = 419075) B419075
theorem B279449 : Blo 183802 279449 := bstep (se 2 (by rfl) ⟨104793, by rfl⟩ : syracuseStep 279449 = 209587) B209587
theorem B279563 : Blo 183802 279563 := bstep (se 1 (by rfl) ⟨209672, by rfl⟩ : syracuseStep 279563 = 419345) B419345
theorem B279575 : Blo 183802 279575 := bstep (se 1 (by rfl) ⟨209681, by rfl⟩ : syracuseStep 279575 = 419363) B419363
theorem B705581 : Blo 183802 705581 := bstep (se 3 (by rfl) ⟨132296, by rfl⟩ : syracuseStep 705581 = 264593) B264593
theorem B377921 : Blo 183802 377921 := bstep (se 2 (by rfl) ⟨141720, by rfl⟩ : syracuseStep 377921 = 283441) B283441
theorem B705611 : Blo 183802 705611 := bstep (se 1 (by rfl) ⟨529208, by rfl⟩ : syracuseStep 705611 = 1058417) B1058417
theorem B279641 : Blo 183802 279641 := bstep (se 2 (by rfl) ⟨104865, by rfl⟩ : syracuseStep 279641 = 209731) B209731
theorem B935063 : Blo 183802 935063 := bstep (se 1 (by rfl) ⟨701297, by rfl⟩ : syracuseStep 935063 = 1402595) B1402595
theorem B279755 : Blo 183802 279755 := bstep (se 1 (by rfl) ⟨209816, by rfl⟩ : syracuseStep 279755 = 419633) B419633
theorem B279767 : Blo 183802 279767 := bstep (se 1 (by rfl) ⟨209825, by rfl⟩ : syracuseStep 279767 = 419651) B419651
theorem B312599 : Blo 183802 312599 := bstep (se 1 (by rfl) ⟨234449, by rfl⟩ : syracuseStep 312599 = 468899) B468899
theorem B279833 : Blo 183802 279833 := bstep (se 2 (by rfl) ⟨104937, by rfl⟩ : syracuseStep 279833 = 209875) B209875
theorem B279947 : Blo 183802 279947 := bstep (se 1 (by rfl) ⟨209960, by rfl⟩ : syracuseStep 279947 = 419921) B419921
theorem B312727 : Blo 183802 312727 := bstep (se 1 (by rfl) ⟨234545, by rfl⟩ : syracuseStep 312727 = 469091) B469091
theorem B279959 : Blo 183802 279959 := bstep (se 1 (by rfl) ⟨209969, by rfl⟩ : syracuseStep 279959 = 419939) B419939
theorem B1066391 : Blo 183802 1066391 := bstep (se 1 (by rfl) ⟨799793, by rfl⟩ : syracuseStep 1066391 = 1599587) B1599587
theorem B280025 : Blo 183802 280025 := bstep (se 2 (by rfl) ⟨105009, by rfl⟩ : syracuseStep 280025 = 210019) B210019
theorem B280139 : Blo 183802 280139 := bstep (se 1 (by rfl) ⟨210104, by rfl⟩ : syracuseStep 280139 = 420209) B420209
theorem B280151 : Blo 183802 280151 := bstep (se 1 (by rfl) ⟨210113, by rfl⟩ : syracuseStep 280151 = 420227) B420227
theorem B280217 : Blo 183802 280217 := bstep (se 2 (by rfl) ⟨105081, by rfl⟩ : syracuseStep 280217 = 210163) B210163
theorem B706265 : Blo 183802 706265 := bstep (se 2 (by rfl) ⟨264849, by rfl⟩ : syracuseStep 706265 = 529699) B529699
theorem B280331 : Blo 183802 280331 := bstep (se 1 (by rfl) ⟨210248, by rfl⟩ : syracuseStep 280331 = 420497) B420497
theorem B280343 : Blo 183802 280343 := bstep (se 1 (by rfl) ⟨210257, by rfl⟩ : syracuseStep 280343 = 420515) B420515
theorem B280409 : Blo 183802 280409 := bstep (se 2 (by rfl) ⟨105153, by rfl⟩ : syracuseStep 280409 = 210307) B210307
theorem B280523 : Blo 183802 280523 := bstep (se 1 (by rfl) ⟨210392, by rfl⟩ : syracuseStep 280523 = 420785) B420785
theorem B280535 : Blo 183802 280535 := bstep (se 1 (by rfl) ⟨210401, by rfl⟩ : syracuseStep 280535 = 420803) B420803
theorem B575453 : Blo 183802 575453 := bstep (se 3 (by rfl) ⟨107897, by rfl⟩ : syracuseStep 575453 = 215795) B215795
theorem B313355 : Blo 183802 313355 := bstep (se 1 (by rfl) ⟨235016, by rfl⟩ : syracuseStep 313355 = 470033) B470033
theorem B706583 : Blo 183802 706583 := bstep (se 1 (by rfl) ⟨529937, by rfl⟩ : syracuseStep 706583 = 1059875) B1059875
theorem B280601 : Blo 183802 280601 := bstep (se 2 (by rfl) ⟨105225, by rfl⟩ : syracuseStep 280601 = 210451) B210451
theorem B313483 : Blo 183802 313483 := bstep (se 1 (by rfl) ⟨235112, by rfl⟩ : syracuseStep 313483 = 470225) B470225
theorem B280715 : Blo 183802 280715 := bstep (se 1 (by rfl) ⟨210536, by rfl⟩ : syracuseStep 280715 = 421073) B421073
theorem B280727 : Blo 183802 280727 := bstep (se 1 (by rfl) ⟨210545, by rfl⟩ : syracuseStep 280727 = 421091) B421091
theorem B379073 : Blo 183802 379073 := bstep (se 2 (by rfl) ⟨142152, by rfl⟩ : syracuseStep 379073 = 284305) B284305
theorem B280793 : Blo 183802 280793 := bstep (se 2 (by rfl) ⟨105297, by rfl⟩ : syracuseStep 280793 = 210595) B210595
theorem B313625 : Blo 183802 313625 := bstep (se 2 (by rfl) ⟨117609, by rfl⟩ : syracuseStep 313625 = 235219) B235219
theorem B280907 : Blo 183802 280907 := bstep (se 1 (by rfl) ⟨210680, by rfl⟩ : syracuseStep 280907 = 421361) B421361
theorem B280919 : Blo 183802 280919 := bstep (se 1 (by rfl) ⟨210689, by rfl⟩ : syracuseStep 280919 = 421379) B421379
theorem B313753 : Blo 183802 313753 := bstep (se 2 (by rfl) ⟨117657, by rfl⟩ : syracuseStep 313753 = 235315) B235315
theorem B280985 : Blo 183802 280985 := bstep (se 2 (by rfl) ⟨105369, by rfl⟩ : syracuseStep 280985 = 210739) B210739
theorem B379379 : Blo 183802 379379 := bstep (se 1 (by rfl) ⟨284534, by rfl⟩ : syracuseStep 379379 = 569069) B569069
theorem B281099 : Blo 183802 281099 := bstep (se 1 (by rfl) ⟨210824, by rfl⟩ : syracuseStep 281099 = 421649) B421649
theorem B281111 : Blo 183802 281111 := bstep (se 1 (by rfl) ⟨210833, by rfl⟩ : syracuseStep 281111 = 421667) B421667
theorem B3066443 : Blo 183802 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B510553 : Blo 183802 510553 := bstep (se 2 (by rfl) ⟨191457, by rfl⟩ : syracuseStep 510553 = 382915) B382915
theorem B281177 : Blo 183802 281177 := bstep (se 2 (by rfl) ⟨105441, by rfl⟩ : syracuseStep 281177 = 210883) B210883
theorem B707251 : Blo 183802 707251 := bstep (se 1 (by rfl) ⟨530438, by rfl⟩ : syracuseStep 707251 = 1060877) B1060877
theorem B281291 : Blo 183802 281291 := bstep (se 1 (by rfl) ⟨210968, by rfl⟩ : syracuseStep 281291 = 421937) B421937
theorem B281303 : Blo 183802 281303 := bstep (se 1 (by rfl) ⟨210977, by rfl⟩ : syracuseStep 281303 = 421955) B421955
theorem B281369 : Blo 183802 281369 := bstep (se 2 (by rfl) ⟨105513, by rfl⟩ : syracuseStep 281369 = 211027) B211027
theorem B281483 : Blo 183802 281483 := bstep (se 1 (by rfl) ⟨211112, by rfl⟩ : syracuseStep 281483 = 422225) B422225
theorem B281495 : Blo 183802 281495 := bstep (se 1 (by rfl) ⟨211121, by rfl⟩ : syracuseStep 281495 = 422243) B422243
theorem B314327 : Blo 183802 314327 := bstep (se 1 (by rfl) ⟨235745, by rfl⟩ : syracuseStep 314327 = 471491) B471491
theorem B281561 : Blo 183802 281561 := bstep (se 2 (by rfl) ⟨105585, by rfl⟩ : syracuseStep 281561 = 211171) B211171
theorem B281675 : Blo 183802 281675 := bstep (se 1 (by rfl) ⟨211256, by rfl⟩ : syracuseStep 281675 = 422513) B422513
theorem B314455 : Blo 183802 314455 := bstep (se 1 (by rfl) ⟨235841, by rfl⟩ : syracuseStep 314455 = 471683) B471683
theorem B281687 : Blo 183802 281687 := bstep (se 1 (by rfl) ⟨211265, by rfl⟩ : syracuseStep 281687 = 422531) B422531
theorem B839005 : Blo 183802 839005 := bstep (se 3 (by rfl) ⟨157313, by rfl⟩ : syracuseStep 839005 = 314627) B314627
theorem B183819 : Blo 183802 183819 := bstep (se 1 (by rfl) ⟨137864, by rfl⟩ : syracuseStep 183819 = 275729) B275729
theorem B183831 : Blo 183802 183831 := bstep (se 1 (by rfl) ⟨137873, by rfl⟩ : syracuseStep 183831 = 275747) B275747
theorem B314903 : Blo 183802 314903 := bstep (se 1 (by rfl) ⟨236177, by rfl⟩ : syracuseStep 314903 = 472355) B472355
theorem B183851 : Blo 183802 183851 := bstep (se 1 (by rfl) ⟨137888, by rfl⟩ : syracuseStep 183851 = 275777) B275777
theorem B183863 : Blo 183802 183863 := bstep (se 1 (by rfl) ⟨137897, by rfl⟩ : syracuseStep 183863 = 275795) B275795
theorem B183883 : Blo 183802 183883 := bstep (se 1 (by rfl) ⟨137912, by rfl⟩ : syracuseStep 183883 = 275825) B275825
theorem B183895 : Blo 183802 183895 := bstep (se 1 (by rfl) ⟨137921, by rfl⟩ : syracuseStep 183895 = 275843) B275843
theorem B282199 : Blo 183802 282199 := bstep (se 1 (by rfl) ⟨211649, by rfl⟩ : syracuseStep 282199 = 423299) B423299
theorem B1363549 : Blo 183802 1363549 := bstep (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) B511331
theorem B183915 : Blo 183802 183915 := bstep (se 1 (by rfl) ⟨137936, by rfl⟩ : syracuseStep 183915 = 275873) B275873
theorem B183927 : Blo 183802 183927 := bstep (se 1 (by rfl) ⟨137945, by rfl⟩ : syracuseStep 183927 = 275891) B275891
theorem B183947 : Blo 183802 183947 := bstep (se 1 (by rfl) ⟨137960, by rfl⟩ : syracuseStep 183947 = 275921) B275921
theorem B183959 : Blo 183802 183959 := bstep (se 1 (by rfl) ⟨137969, by rfl⟩ : syracuseStep 183959 = 275939) B275939
theorem B183979 : Blo 183802 183979 := bstep (se 1 (by rfl) ⟨137984, by rfl⟩ : syracuseStep 183979 = 275969) B275969
theorem B183991 : Blo 183802 183991 := bstep (se 1 (by rfl) ⟨137993, by rfl⟩ : syracuseStep 183991 = 275987) B275987
theorem B184011 : Blo 183802 184011 := bstep (se 1 (by rfl) ⟨138008, by rfl⟩ : syracuseStep 184011 = 276017) B276017
theorem B315083 : Blo 183802 315083 := bstep (se 1 (by rfl) ⟨236312, by rfl⟩ : syracuseStep 315083 = 472625) B472625
theorem B184023 : Blo 183802 184023 := bstep (se 1 (by rfl) ⟨138017, by rfl⟩ : syracuseStep 184023 = 276035) B276035
theorem B184043 : Blo 183802 184043 := bstep (se 1 (by rfl) ⟨138032, by rfl⟩ : syracuseStep 184043 = 276065) B276065
theorem B184055 : Blo 183802 184055 := bstep (se 1 (by rfl) ⟨138041, by rfl⟩ : syracuseStep 184055 = 276083) B276083
theorem B184075 : Blo 183802 184075 := bstep (se 1 (by rfl) ⟨138056, by rfl⟩ : syracuseStep 184075 = 276113) B276113
theorem B184087 : Blo 183802 184087 := bstep (se 1 (by rfl) ⟨138065, by rfl⟩ : syracuseStep 184087 = 276131) B276131
theorem B184107 : Blo 183802 184107 := bstep (se 1 (by rfl) ⟨138080, by rfl⟩ : syracuseStep 184107 = 276161) B276161
theorem B184119 : Blo 183802 184119 := bstep (se 1 (by rfl) ⟨138089, by rfl⟩ : syracuseStep 184119 = 276179) B276179
theorem B184139 : Blo 183802 184139 := bstep (se 1 (by rfl) ⟨138104, by rfl⟩ : syracuseStep 184139 = 276209) B276209
theorem B315211 : Blo 183802 315211 := bstep (se 1 (by rfl) ⟨236408, by rfl⟩ : syracuseStep 315211 = 472817) B472817
theorem B1068875 : Blo 183802 1068875 := bstep (se 1 (by rfl) ⟨801656, by rfl⟩ : syracuseStep 1068875 = 1603313) B1603313
theorem B184151 : Blo 183802 184151 := bstep (se 1 (by rfl) ⟨138113, by rfl⟩ : syracuseStep 184151 = 276227) B276227
theorem B184171 : Blo 183802 184171 := bstep (se 1 (by rfl) ⟨138128, by rfl⟩ : syracuseStep 184171 = 276257) B276257
theorem B184183 : Blo 183802 184183 := bstep (se 1 (by rfl) ⟨138137, by rfl⟩ : syracuseStep 184183 = 276275) B276275
theorem B184203 : Blo 183802 184203 := bstep (se 1 (by rfl) ⟨138152, by rfl⟩ : syracuseStep 184203 = 276305) B276305
theorem B708497 : Blo 183802 708497 := bstep (se 2 (by rfl) ⟨265686, by rfl⟩ : syracuseStep 708497 = 531373) B531373
theorem B184215 : Blo 183802 184215 := bstep (se 1 (by rfl) ⟨138161, by rfl⟩ : syracuseStep 184215 = 276323) B276323
theorem B184235 : Blo 183802 184235 := bstep (se 1 (by rfl) ⟨138176, by rfl⟩ : syracuseStep 184235 = 276353) B276353
theorem B184247 : Blo 183802 184247 := bstep (se 1 (by rfl) ⟨138185, by rfl⟩ : syracuseStep 184247 = 276371) B276371
theorem B184267 : Blo 183802 184267 := bstep (se 1 (by rfl) ⟨138200, by rfl⟩ : syracuseStep 184267 = 276401) B276401
theorem B380875 : Blo 183802 380875 := bstep (se 1 (by rfl) ⟨285656, by rfl⟩ : syracuseStep 380875 = 571313) B571313
theorem B184279 : Blo 183802 184279 := bstep (se 1 (by rfl) ⟨138209, by rfl⟩ : syracuseStep 184279 = 276419) B276419
theorem B413657 : Blo 183802 413657 := bstep (se 2 (by rfl) ⟨155121, by rfl⟩ : syracuseStep 413657 = 310243) B310243
theorem B315353 : Blo 183802 315353 := bstep (se 2 (by rfl) ⟨118257, by rfl⟩ : syracuseStep 315353 = 236515) B236515
theorem B184299 : Blo 183802 184299 := bstep (se 1 (by rfl) ⟨138224, by rfl⟩ : syracuseStep 184299 = 276449) B276449
theorem B184311 : Blo 183802 184311 := bstep (se 1 (by rfl) ⟨138233, by rfl⟩ : syracuseStep 184311 = 276467) B276467
theorem B184331 : Blo 183802 184331 := bstep (se 1 (by rfl) ⟨138248, by rfl⟩ : syracuseStep 184331 = 276497) B276497
theorem B184343 : Blo 183802 184343 := bstep (se 1 (by rfl) ⟨138257, by rfl⟩ : syracuseStep 184343 = 276515) B276515
theorem B184363 : Blo 183802 184363 := bstep (se 1 (by rfl) ⟨138272, by rfl⟩ : syracuseStep 184363 = 276545) B276545
theorem B413747 : Blo 183802 413747 := bstep (se 1 (by rfl) ⟨310310, by rfl⟩ : syracuseStep 413747 = 620621) B620621
theorem B184375 : Blo 183802 184375 := bstep (se 1 (by rfl) ⟨138281, by rfl⟩ : syracuseStep 184375 = 276563) B276563
theorem B184395 : Blo 183802 184395 := bstep (se 1 (by rfl) ⟨138296, by rfl⟩ : syracuseStep 184395 = 276593) B276593
theorem B413783 : Blo 183802 413783 := bstep (se 1 (by rfl) ⟨310337, by rfl⟩ : syracuseStep 413783 = 620675) B620675
theorem B184407 : Blo 183802 184407 := bstep (se 1 (by rfl) ⟨138305, by rfl⟩ : syracuseStep 184407 = 276611) B276611
theorem B315481 : Blo 183802 315481 := bstep (se 2 (by rfl) ⟨118305, by rfl⟩ : syracuseStep 315481 = 236611) B236611
theorem B184427 : Blo 183802 184427 := bstep (se 1 (by rfl) ⟨138320, by rfl⟩ : syracuseStep 184427 = 276641) B276641
theorem B184439 : Blo 183802 184439 := bstep (se 1 (by rfl) ⟨138329, by rfl⟩ : syracuseStep 184439 = 276659) B276659
theorem B184459 : Blo 183802 184459 := bstep (se 1 (by rfl) ⟨138344, by rfl⟩ : syracuseStep 184459 = 276689) B276689
theorem B184471 : Blo 183802 184471 := bstep (se 1 (by rfl) ⟨138353, by rfl⟩ : syracuseStep 184471 = 276707) B276707
theorem B184491 : Blo 183802 184491 := bstep (se 1 (by rfl) ⟨138368, by rfl⟩ : syracuseStep 184491 = 276737) B276737
theorem B184503 : Blo 183802 184503 := bstep (se 1 (by rfl) ⟨138377, by rfl⟩ : syracuseStep 184503 = 276755) B276755
theorem B184523 : Blo 183802 184523 := bstep (se 1 (by rfl) ⟨138392, by rfl⟩ : syracuseStep 184523 = 276785) B276785
theorem B184535 : Blo 183802 184535 := bstep (se 1 (by rfl) ⟨138401, by rfl⟩ : syracuseStep 184535 = 276803) B276803
theorem B184555 : Blo 183802 184555 := bstep (se 1 (by rfl) ⟨138416, by rfl⟩ : syracuseStep 184555 = 276833) B276833
theorem B184567 : Blo 183802 184567 := bstep (se 1 (by rfl) ⟨138425, by rfl⟩ : syracuseStep 184567 = 276851) B276851
theorem B4837637 : Blo 183802 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B413963 : Blo 183802 413963 := bstep (se 1 (by rfl) ⟨310472, by rfl⟩ : syracuseStep 413963 = 620945) B620945
theorem B184587 : Blo 183802 184587 := bstep (se 1 (by rfl) ⟨138440, by rfl⟩ : syracuseStep 184587 = 276881) B276881
theorem B184599 : Blo 183802 184599 := bstep (se 1 (by rfl) ⟨138449, by rfl⟩ : syracuseStep 184599 = 276899) B276899
theorem B184619 : Blo 183802 184619 := bstep (se 1 (by rfl) ⟨138464, by rfl⟩ : syracuseStep 184619 = 276929) B276929
theorem B184631 : Blo 183802 184631 := bstep (se 1 (by rfl) ⟨138473, by rfl⟩ : syracuseStep 184631 = 276947) B276947
theorem B414017 : Blo 183802 414017 := bstep (se 2 (by rfl) ⟨155256, by rfl⟩ : syracuseStep 414017 = 310513) B310513
theorem B184651 : Blo 183802 184651 := bstep (se 1 (by rfl) ⟨138488, by rfl⟩ : syracuseStep 184651 = 276977) B276977
theorem B184663 : Blo 183802 184663 := bstep (se 1 (by rfl) ⟨138497, by rfl⟩ : syracuseStep 184663 = 276995) B276995
theorem B446809 : Blo 183802 446809 := bstep (se 2 (by rfl) ⟨167553, by rfl⟩ : syracuseStep 446809 = 335107) B335107
theorem B184683 : Blo 183802 184683 := bstep (se 1 (by rfl) ⟨138512, by rfl⟩ : syracuseStep 184683 = 277025) B277025
theorem B184695 : Blo 183802 184695 := bstep (se 1 (by rfl) ⟨138521, by rfl⟩ : syracuseStep 184695 = 277043) B277043
theorem B184715 : Blo 183802 184715 := bstep (se 1 (by rfl) ⟨138536, by rfl⟩ : syracuseStep 184715 = 277073) B277073
theorem B184727 : Blo 183802 184727 := bstep (se 1 (by rfl) ⟨138545, by rfl⟩ : syracuseStep 184727 = 277091) B277091
theorem B184747 : Blo 183802 184747 := bstep (se 1 (by rfl) ⟨138560, by rfl⟩ : syracuseStep 184747 = 277121) B277121
theorem B184759 : Blo 183802 184759 := bstep (se 1 (by rfl) ⟨138569, by rfl⟩ : syracuseStep 184759 = 277139) B277139
theorem B184779 : Blo 183802 184779 := bstep (se 1 (by rfl) ⟨138584, by rfl⟩ : syracuseStep 184779 = 277169) B277169
theorem B184791 : Blo 183802 184791 := bstep (se 1 (by rfl) ⟨138593, by rfl⟩ : syracuseStep 184791 = 277187) B277187
theorem B184811 : Blo 183802 184811 := bstep (se 1 (by rfl) ⟨138608, by rfl⟩ : syracuseStep 184811 = 277217) B277217
theorem B184823 : Blo 183802 184823 := bstep (se 1 (by rfl) ⟨138617, by rfl⟩ : syracuseStep 184823 = 277235) B277235
theorem B184843 : Blo 183802 184843 := bstep (se 1 (by rfl) ⟨138632, by rfl⟩ : syracuseStep 184843 = 277265) B277265
theorem B184855 : Blo 183802 184855 := bstep (se 1 (by rfl) ⟨138641, by rfl⟩ : syracuseStep 184855 = 277283) B277283
theorem B414233 : Blo 183802 414233 := bstep (se 2 (by rfl) ⟨155337, by rfl⟩ : syracuseStep 414233 = 310675) B310675
theorem B184875 : Blo 183802 184875 := bstep (se 1 (by rfl) ⟨138656, by rfl⟩ : syracuseStep 184875 = 277313) B277313
theorem B184887 : Blo 183802 184887 := bstep (se 1 (by rfl) ⟨138665, by rfl⟩ : syracuseStep 184887 = 277331) B277331
theorem B184907 : Blo 183802 184907 := bstep (se 1 (by rfl) ⟨138680, by rfl⟩ : syracuseStep 184907 = 277361) B277361
theorem B709195 : Blo 183802 709195 := bstep (se 1 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 709195 = 1063793) B1063793
theorem B184919 : Blo 183802 184919 := bstep (se 1 (by rfl) ⟨138689, by rfl⟩ : syracuseStep 184919 = 277379) B277379
theorem B184939 : Blo 183802 184939 := bstep (se 1 (by rfl) ⟨138704, by rfl⟩ : syracuseStep 184939 = 277409) B277409
theorem B414323 : Blo 183802 414323 := bstep (se 1 (by rfl) ⟨310742, by rfl⟩ : syracuseStep 414323 = 621485) B621485
theorem B184951 : Blo 183802 184951 := bstep (se 1 (by rfl) ⟨138713, by rfl⟩ : syracuseStep 184951 = 277427) B277427
theorem B938627 : Blo 183802 938627 := bstep (se 1 (by rfl) ⟨703970, by rfl⟩ : syracuseStep 938627 = 1407941) B1407941
theorem B184971 : Blo 183802 184971 := bstep (se 1 (by rfl) ⟨138728, by rfl⟩ : syracuseStep 184971 = 277457) B277457
theorem B414359 : Blo 183802 414359 := bstep (se 1 (by rfl) ⟨310769, by rfl⟩ : syracuseStep 414359 = 621539) B621539
theorem B184983 : Blo 183802 184983 := bstep (se 1 (by rfl) ⟨138737, by rfl⟩ : syracuseStep 184983 = 277475) B277475
theorem B316055 : Blo 183802 316055 := bstep (se 1 (by rfl) ⟨237041, by rfl⟩ : syracuseStep 316055 = 474083) B474083
theorem B185003 : Blo 183802 185003 := bstep (se 1 (by rfl) ⟨138752, by rfl⟩ : syracuseStep 185003 = 277505) B277505
theorem B185015 : Blo 183802 185015 := bstep (se 1 (by rfl) ⟨138761, by rfl⟩ : syracuseStep 185015 = 277523) B277523
theorem B185035 : Blo 183802 185035 := bstep (se 1 (by rfl) ⟨138776, by rfl⟩ : syracuseStep 185035 = 277553) B277553
theorem B185047 : Blo 183802 185047 := bstep (se 1 (by rfl) ⟨138785, by rfl⟩ : syracuseStep 185047 = 277571) B277571
theorem B185067 : Blo 183802 185067 := bstep (se 1 (by rfl) ⟨138800, by rfl⟩ : syracuseStep 185067 = 277601) B277601
theorem B185079 : Blo 183802 185079 := bstep (se 1 (by rfl) ⟨138809, by rfl⟩ : syracuseStep 185079 = 277619) B277619
theorem B185099 : Blo 183802 185099 := bstep (se 1 (by rfl) ⟨138824, by rfl⟩ : syracuseStep 185099 = 277649) B277649
theorem B185111 : Blo 183802 185111 := bstep (se 1 (by rfl) ⟨138833, by rfl⟩ : syracuseStep 185111 = 277667) B277667
theorem B316183 : Blo 183802 316183 := bstep (se 1 (by rfl) ⟨237137, by rfl⟩ : syracuseStep 316183 = 474275) B474275
theorem B185131 : Blo 183802 185131 := bstep (se 1 (by rfl) ⟨138848, by rfl⟩ : syracuseStep 185131 = 277697) B277697
theorem B185143 : Blo 183802 185143 := bstep (se 1 (by rfl) ⟨138857, by rfl⟩ : syracuseStep 185143 = 277715) B277715
theorem B414539 : Blo 183802 414539 := bstep (se 1 (by rfl) ⟨310904, by rfl⟩ : syracuseStep 414539 = 621809) B621809
theorem B185163 : Blo 183802 185163 := bstep (se 1 (by rfl) ⟨138872, by rfl⟩ : syracuseStep 185163 = 277745) B277745
theorem B1594187 : Blo 183802 1594187 := bstep (se 1 (by rfl) ⟨1195640, by rfl⟩ : syracuseStep 1594187 = 2391281) B2391281
theorem B185175 : Blo 183802 185175 := bstep (se 1 (by rfl) ⟨138881, by rfl⟩ : syracuseStep 185175 = 277763) B277763
theorem B709469 : Blo 183802 709469 := bstep (se 3 (by rfl) ⟨133025, by rfl⟩ : syracuseStep 709469 = 266051) B266051
theorem B185195 : Blo 183802 185195 := bstep (se 1 (by rfl) ⟨138896, by rfl⟩ : syracuseStep 185195 = 277793) B277793
theorem B185207 : Blo 183802 185207 := bstep (se 1 (by rfl) ⟨138905, by rfl⟩ : syracuseStep 185207 = 277811) B277811
theorem B414593 : Blo 183802 414593 := bstep (se 2 (by rfl) ⟨155472, by rfl⟩ : syracuseStep 414593 = 310945) B310945
theorem B185227 : Blo 183802 185227 := bstep (se 1 (by rfl) ⟨138920, by rfl⟩ : syracuseStep 185227 = 277841) B277841
theorem B185239 : Blo 183802 185239 := bstep (se 1 (by rfl) ⟨138929, by rfl⟩ : syracuseStep 185239 = 277859) B277859
theorem B185259 : Blo 183802 185259 := bstep (se 1 (by rfl) ⟨138944, by rfl⟩ : syracuseStep 185259 = 277889) B277889
theorem B185271 : Blo 183802 185271 := bstep (se 1 (by rfl) ⟨138953, by rfl⟩ : syracuseStep 185271 = 277907) B277907
theorem B185291 : Blo 183802 185291 := bstep (se 1 (by rfl) ⟨138968, by rfl⟩ : syracuseStep 185291 = 277937) B277937
theorem B185303 : Blo 183802 185303 := bstep (se 1 (by rfl) ⟨138977, by rfl⟩ : syracuseStep 185303 = 277955) B277955
theorem B185323 : Blo 183802 185323 := bstep (se 1 (by rfl) ⟨138992, by rfl⟩ : syracuseStep 185323 = 277985) B277985
theorem B185335 : Blo 183802 185335 := bstep (se 1 (by rfl) ⟨139001, by rfl⟩ : syracuseStep 185335 = 278003) B278003
theorem B185355 : Blo 183802 185355 := bstep (se 1 (by rfl) ⟨139016, by rfl⟩ : syracuseStep 185355 = 278033) B278033
theorem B185367 : Blo 183802 185367 := bstep (se 1 (by rfl) ⟨139025, by rfl⟩ : syracuseStep 185367 = 278051) B278051
theorem B185387 : Blo 183802 185387 := bstep (se 1 (by rfl) ⟨139040, by rfl⟩ : syracuseStep 185387 = 278081) B278081
theorem B185399 : Blo 183802 185399 := bstep (se 1 (by rfl) ⟨139049, by rfl⟩ : syracuseStep 185399 = 278099) B278099
theorem B185419 : Blo 183802 185419 := bstep (se 1 (by rfl) ⟨139064, by rfl⟩ : syracuseStep 185419 = 278129) B278129
theorem B185431 : Blo 183802 185431 := bstep (se 1 (by rfl) ⟨139073, by rfl⟩ : syracuseStep 185431 = 278147) B278147
theorem B414809 : Blo 183802 414809 := bstep (se 2 (by rfl) ⟨155553, by rfl⟩ : syracuseStep 414809 = 311107) B311107
theorem B185451 : Blo 183802 185451 := bstep (se 1 (by rfl) ⟨139088, by rfl⟩ : syracuseStep 185451 = 278177) B278177
theorem B185463 : Blo 183802 185463 := bstep (se 1 (by rfl) ⟨139097, by rfl⟩ : syracuseStep 185463 = 278195) B278195
theorem B185483 : Blo 183802 185483 := bstep (se 1 (by rfl) ⟨139112, by rfl⟩ : syracuseStep 185483 = 278225) B278225
theorem B185495 : Blo 183802 185495 := bstep (se 1 (by rfl) ⟨139121, by rfl⟩ : syracuseStep 185495 = 278243) B278243
theorem B185515 : Blo 183802 185515 := bstep (se 1 (by rfl) ⟨139136, by rfl⟩ : syracuseStep 185515 = 278273) B278273
theorem B414899 : Blo 183802 414899 := bstep (se 1 (by rfl) ⟨311174, by rfl⟩ : syracuseStep 414899 = 622349) B622349
theorem B1201331 : Blo 183802 1201331 := bstep (se 1 (by rfl) ⟨900998, by rfl⟩ : syracuseStep 1201331 = 1801997) B1801997
theorem B185527 : Blo 183802 185527 := bstep (se 1 (by rfl) ⟨139145, by rfl⟩ : syracuseStep 185527 = 278291) B278291
theorem B185547 : Blo 183802 185547 := bstep (se 1 (by rfl) ⟨139160, by rfl⟩ : syracuseStep 185547 = 278321) B278321
theorem B414935 : Blo 183802 414935 := bstep (se 1 (by rfl) ⟨311201, by rfl⟩ : syracuseStep 414935 = 622403) B622403
theorem B185559 : Blo 183802 185559 := bstep (se 1 (by rfl) ⟨139169, by rfl⟩ : syracuseStep 185559 = 278339) B278339
theorem B185579 : Blo 183802 185579 := bstep (se 1 (by rfl) ⟨139184, by rfl⟩ : syracuseStep 185579 = 278369) B278369
theorem B349427 : Blo 183802 349427 := bstep (se 1 (by rfl) ⟨262070, by rfl⟩ : syracuseStep 349427 = 524141) B524141
theorem B185591 : Blo 183802 185591 := bstep (se 1 (by rfl) ⟨139193, by rfl⟩ : syracuseStep 185591 = 278387) B278387
theorem B185611 : Blo 183802 185611 := bstep (se 1 (by rfl) ⟨139208, by rfl⟩ : syracuseStep 185611 = 278417) B278417
theorem B283915 : Blo 183802 283915 := bstep (se 1 (by rfl) ⟨212936, by rfl⟩ : syracuseStep 283915 = 425873) B425873
theorem B185623 : Blo 183802 185623 := bstep (se 1 (by rfl) ⟨139217, by rfl⟩ : syracuseStep 185623 = 278435) B278435
theorem B185643 : Blo 183802 185643 := bstep (se 1 (by rfl) ⟨139232, by rfl⟩ : syracuseStep 185643 = 278465) B278465
theorem B185655 : Blo 183802 185655 := bstep (se 1 (by rfl) ⟨139241, by rfl⟩ : syracuseStep 185655 = 278483) B278483
theorem B185675 : Blo 183802 185675 := bstep (se 1 (by rfl) ⟨139256, by rfl⟩ : syracuseStep 185675 = 278513) B278513
theorem B1201483 : Blo 183802 1201483 := bstep (se 1 (by rfl) ⟨901112, by rfl⟩ : syracuseStep 1201483 = 1802225) B1802225
theorem B185687 : Blo 183802 185687 := bstep (se 1 (by rfl) ⟨139265, by rfl⟩ : syracuseStep 185687 = 278531) B278531
theorem B185707 : Blo 183802 185707 := bstep (se 1 (by rfl) ⟨139280, by rfl⟩ : syracuseStep 185707 = 278561) B278561
theorem B185719 : Blo 183802 185719 := bstep (se 1 (by rfl) ⟨139289, by rfl⟩ : syracuseStep 185719 = 278579) B278579
theorem B415115 : Blo 183802 415115 := bstep (se 1 (by rfl) ⟨311336, by rfl⟩ : syracuseStep 415115 = 622673) B622673
theorem B185739 : Blo 183802 185739 := bstep (se 1 (by rfl) ⟨139304, by rfl⟩ : syracuseStep 185739 = 278609) B278609
theorem B316811 : Blo 183802 316811 := bstep (se 1 (by rfl) ⟨237608, by rfl⟩ : syracuseStep 316811 = 475217) B475217
theorem B710039 : Blo 183802 710039 := bstep (se 1 (by rfl) ⟨532529, by rfl⟩ : syracuseStep 710039 = 1065059) B1065059
theorem B185751 : Blo 183802 185751 := bstep (se 1 (by rfl) ⟨139313, by rfl⟩ : syracuseStep 185751 = 278627) B278627
theorem B185771 : Blo 183802 185771 := bstep (se 1 (by rfl) ⟨139328, by rfl⟩ : syracuseStep 185771 = 278657) B278657
theorem B185783 : Blo 183802 185783 := bstep (se 1 (by rfl) ⟨139337, by rfl⟩ : syracuseStep 185783 = 278675) B278675
theorem B415169 : Blo 183802 415169 := bstep (se 2 (by rfl) ⟨155688, by rfl⟩ : syracuseStep 415169 = 311377) B311377
theorem B185803 : Blo 183802 185803 := bstep (se 1 (by rfl) ⟨139352, by rfl⟩ : syracuseStep 185803 = 278705) B278705
theorem B1398221 : Blo 183802 1398221 := bstep (se 3 (by rfl) ⟨262166, by rfl⟩ : syracuseStep 1398221 = 524333) B524333
theorem B185815 : Blo 183802 185815 := bstep (se 1 (by rfl) ⟨139361, by rfl⟩ : syracuseStep 185815 = 278723) B278723
theorem B185835 : Blo 183802 185835 := bstep (se 1 (by rfl) ⟨139376, by rfl⟩ : syracuseStep 185835 = 278753) B278753
theorem B185847 : Blo 183802 185847 := bstep (se 1 (by rfl) ⟨139385, by rfl⟩ : syracuseStep 185847 = 278771) B278771
theorem B185867 : Blo 183802 185867 := bstep (se 1 (by rfl) ⟨139400, by rfl⟩ : syracuseStep 185867 = 278801) B278801
theorem B185879 : Blo 183802 185879 := bstep (se 1 (by rfl) ⟨139409, by rfl⟩ : syracuseStep 185879 = 278819) B278819
theorem B710167 : Blo 183802 710167 := bstep (se 1 (by rfl) ⟨532625, by rfl⟩ : syracuseStep 710167 = 1065251) B1065251
theorem B185899 : Blo 183802 185899 := bstep (se 1 (by rfl) ⟨139424, by rfl⟩ : syracuseStep 185899 = 278849) B278849
theorem B185911 : Blo 183802 185911 := bstep (se 1 (by rfl) ⟨139433, by rfl⟩ : syracuseStep 185911 = 278867) B278867
theorem B185931 : Blo 183802 185931 := bstep (se 1 (by rfl) ⟨139448, by rfl⟩ : syracuseStep 185931 = 278897) B278897
theorem B185943 : Blo 183802 185943 := bstep (se 1 (by rfl) ⟨139457, by rfl⟩ : syracuseStep 185943 = 278915) B278915
theorem B808537 : Blo 183802 808537 := bstep (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) B606403
theorem B185963 : Blo 183802 185963 := bstep (se 1 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 185963 = 278945) B278945
theorem B185975 : Blo 183802 185975 := bstep (se 1 (by rfl) ⟨139481, by rfl⟩ : syracuseStep 185975 = 278963) B278963
theorem B185995 : Blo 183802 185995 := bstep (se 1 (by rfl) ⟨139496, by rfl⟩ : syracuseStep 185995 = 278993) B278993
theorem B186007 : Blo 183802 186007 := bstep (se 1 (by rfl) ⟨139505, by rfl⟩ : syracuseStep 186007 = 279011) B279011
theorem B415385 : Blo 183802 415385 := bstep (se 2 (by rfl) ⟨155769, by rfl⟩ : syracuseStep 415385 = 311539) B311539
theorem B186027 : Blo 183802 186027 := bstep (se 1 (by rfl) ⟨139520, by rfl⟩ : syracuseStep 186027 = 279041) B279041
theorem B186039 : Blo 183802 186039 := bstep (se 1 (by rfl) ⟨139529, by rfl⟩ : syracuseStep 186039 = 279059) B279059
theorem B448193 : Blo 183802 448193 := bstep (se 2 (by rfl) ⟨168072, by rfl⟩ : syracuseStep 448193 = 336145) B336145
theorem B186059 : Blo 183802 186059 := bstep (se 1 (by rfl) ⟨139544, by rfl⟩ : syracuseStep 186059 = 279089) B279089
theorem B186071 : Blo 183802 186071 := bstep (se 1 (by rfl) ⟨139553, by rfl⟩ : syracuseStep 186071 = 279107) B279107
theorem B349913 : Blo 183802 349913 := bstep (se 2 (by rfl) ⟨131217, by rfl⟩ : syracuseStep 349913 = 262435) B262435
theorem B186091 : Blo 183802 186091 := bstep (se 1 (by rfl) ⟨139568, by rfl⟩ : syracuseStep 186091 = 279137) B279137
theorem B415475 : Blo 183802 415475 := bstep (se 1 (by rfl) ⟨311606, by rfl⟩ : syracuseStep 415475 = 623213) B623213
theorem B186103 : Blo 183802 186103 := bstep (se 1 (by rfl) ⟨139577, by rfl⟩ : syracuseStep 186103 = 279155) B279155
theorem B186123 : Blo 183802 186123 := bstep (se 1 (by rfl) ⟨139592, by rfl⟩ : syracuseStep 186123 = 279185) B279185
theorem B415511 : Blo 183802 415511 := bstep (se 1 (by rfl) ⟨311633, by rfl⟩ : syracuseStep 415511 = 623267) B623267
theorem B186135 : Blo 183802 186135 := bstep (se 1 (by rfl) ⟨139601, by rfl⟩ : syracuseStep 186135 = 279203) B279203
theorem B186155 : Blo 183802 186155 := bstep (se 1 (by rfl) ⟨139616, by rfl⟩ : syracuseStep 186155 = 279233) B279233
theorem B186167 : Blo 183802 186167 := bstep (se 1 (by rfl) ⟨139625, by rfl⟩ : syracuseStep 186167 = 279251) B279251
theorem B186187 : Blo 183802 186187 := bstep (se 1 (by rfl) ⟨139640, by rfl⟩ : syracuseStep 186187 = 279281) B279281
theorem B481099 : Blo 183802 481099 := bstep (se 1 (by rfl) ⟨360824, by rfl⟩ : syracuseStep 481099 = 721649) B721649
theorem B186199 : Blo 183802 186199 := bstep (se 1 (by rfl) ⟨139649, by rfl⟩ : syracuseStep 186199 = 279299) B279299
theorem B186219 : Blo 183802 186219 := bstep (se 1 (by rfl) ⟨139664, by rfl⟩ : syracuseStep 186219 = 279329) B279329
theorem B186231 : Blo 183802 186231 := bstep (se 1 (by rfl) ⟨139673, by rfl⟩ : syracuseStep 186231 = 279347) B279347
theorem B186251 : Blo 183802 186251 := bstep (se 1 (by rfl) ⟨139688, by rfl⟩ : syracuseStep 186251 = 279377) B279377
theorem B186263 : Blo 183802 186263 := bstep (se 1 (by rfl) ⟨139697, by rfl⟩ : syracuseStep 186263 = 279395) B279395
theorem B186283 : Blo 183802 186283 := bstep (se 1 (by rfl) ⟨139712, by rfl⟩ : syracuseStep 186283 = 279425) B279425
theorem B1398707 : Blo 183802 1398707 := bstep (se 1 (by rfl) ⟨1049030, by rfl⟩ : syracuseStep 1398707 = 2098061) B2098061
theorem B186295 : Blo 183802 186295 := bstep (se 1 (by rfl) ⟨139721, by rfl⟩ : syracuseStep 186295 = 279443) B279443
theorem B415691 : Blo 183802 415691 := bstep (se 1 (by rfl) ⟨311768, by rfl⟩ : syracuseStep 415691 = 623537) B623537
theorem B186315 : Blo 183802 186315 := bstep (se 1 (by rfl) ⟨139736, by rfl⟩ : syracuseStep 186315 = 279473) B279473
theorem B186327 : Blo 183802 186327 := bstep (se 1 (by rfl) ⟨139745, by rfl⟩ : syracuseStep 186327 = 279491) B279491
theorem B481241 : Blo 183802 481241 := bstep (se 2 (by rfl) ⟨180465, by rfl⟩ : syracuseStep 481241 = 360931) B360931
theorem B186347 : Blo 183802 186347 := bstep (se 1 (by rfl) ⟨139760, by rfl⟩ : syracuseStep 186347 = 279521) B279521
theorem B186359 : Blo 183802 186359 := bstep (se 1 (by rfl) ⟨139769, by rfl⟩ : syracuseStep 186359 = 279539) B279539
theorem B415745 : Blo 183802 415745 := bstep (se 2 (by rfl) ⟨155904, by rfl⟩ : syracuseStep 415745 = 311809) B311809
theorem B186379 : Blo 183802 186379 := bstep (se 1 (by rfl) ⟨139784, by rfl⟩ : syracuseStep 186379 = 279569) B279569
theorem B186391 : Blo 183802 186391 := bstep (se 1 (by rfl) ⟨139793, by rfl⟩ : syracuseStep 186391 = 279587) B279587
theorem B186411 : Blo 183802 186411 := bstep (se 1 (by rfl) ⟨139808, by rfl⟩ : syracuseStep 186411 = 279617) B279617
theorem B186423 : Blo 183802 186423 := bstep (se 1 (by rfl) ⟨139817, by rfl⟩ : syracuseStep 186423 = 279635) B279635
theorem B186443 : Blo 183802 186443 := bstep (se 1 (by rfl) ⟨139832, by rfl⟩ : syracuseStep 186443 = 279665) B279665
theorem B186455 : Blo 183802 186455 := bstep (se 1 (by rfl) ⟨139841, by rfl⟩ : syracuseStep 186455 = 279683) B279683
theorem B186475 : Blo 183802 186475 := bstep (se 1 (by rfl) ⟨139856, by rfl⟩ : syracuseStep 186475 = 279713) B279713
theorem B186487 : Blo 183802 186487 := bstep (se 1 (by rfl) ⟨139865, by rfl⟩ : syracuseStep 186487 = 279731) B279731
theorem B186507 : Blo 183802 186507 := bstep (se 1 (by rfl) ⟨139880, by rfl⟩ : syracuseStep 186507 = 279761) B279761
theorem B186519 : Blo 183802 186519 := bstep (se 1 (by rfl) ⟨139889, by rfl⟩ : syracuseStep 186519 = 279779) B279779
theorem B186539 : Blo 183802 186539 := bstep (se 1 (by rfl) ⟨139904, by rfl⟩ : syracuseStep 186539 = 279809) B279809
theorem B186551 : Blo 183802 186551 := bstep (se 1 (by rfl) ⟨139913, by rfl⟩ : syracuseStep 186551 = 279827) B279827
theorem B186571 : Blo 183802 186571 := bstep (se 1 (by rfl) ⟨139928, by rfl⟩ : syracuseStep 186571 = 279857) B279857
theorem B186583 : Blo 183802 186583 := bstep (se 1 (by rfl) ⟨139937, by rfl⟩ : syracuseStep 186583 = 279875) B279875
theorem B415961 : Blo 183802 415961 := bstep (se 2 (by rfl) ⟨155985, by rfl⟩ : syracuseStep 415961 = 311971) B311971
theorem B186603 : Blo 183802 186603 := bstep (se 1 (by rfl) ⟨139952, by rfl⟩ : syracuseStep 186603 = 279905) B279905
theorem B186615 : Blo 183802 186615 := bstep (se 1 (by rfl) ⟨139961, by rfl⟩ : syracuseStep 186615 = 279923) B279923
theorem B186635 : Blo 183802 186635 := bstep (se 1 (by rfl) ⟨139976, by rfl⟩ : syracuseStep 186635 = 279953) B279953
theorem B186647 : Blo 183802 186647 := bstep (se 1 (by rfl) ⟨139985, by rfl⟩ : syracuseStep 186647 = 279971) B279971
theorem B186667 : Blo 183802 186667 := bstep (se 1 (by rfl) ⟨140000, by rfl⟩ : syracuseStep 186667 = 280001) B280001
theorem B710957 : Blo 183802 710957 := bstep (se 3 (by rfl) ⟨133304, by rfl⟩ : syracuseStep 710957 = 266609) B266609
theorem B416051 : Blo 183802 416051 := bstep (se 1 (by rfl) ⟨312038, by rfl⟩ : syracuseStep 416051 = 624077) B624077
theorem B186679 : Blo 183802 186679 := bstep (se 1 (by rfl) ⟨140009, by rfl⟩ : syracuseStep 186679 = 280019) B280019
theorem B186699 : Blo 183802 186699 := bstep (se 1 (by rfl) ⟨140024, by rfl⟩ : syracuseStep 186699 = 280049) B280049
theorem B416087 : Blo 183802 416087 := bstep (se 1 (by rfl) ⟨312065, by rfl⟩ : syracuseStep 416087 = 624131) B624131
theorem B186711 : Blo 183802 186711 := bstep (se 1 (by rfl) ⟨140033, by rfl⟩ : syracuseStep 186711 = 280067) B280067
theorem B186731 : Blo 183802 186731 := bstep (se 1 (by rfl) ⟨140048, by rfl⟩ : syracuseStep 186731 = 280097) B280097
theorem B186743 : Blo 183802 186743 := bstep (se 1 (by rfl) ⟨140057, by rfl⟩ : syracuseStep 186743 = 280115) B280115
theorem B186763 : Blo 183802 186763 := bstep (se 1 (by rfl) ⟨140072, by rfl⟩ : syracuseStep 186763 = 280145) B280145
theorem B186775 : Blo 183802 186775 := bstep (se 1 (by rfl) ⟨140081, by rfl⟩ : syracuseStep 186775 = 280163) B280163
theorem B186795 : Blo 183802 186795 := bstep (se 1 (by rfl) ⟨140096, by rfl⟩ : syracuseStep 186795 = 280193) B280193
theorem B186807 : Blo 183802 186807 := bstep (se 1 (by rfl) ⟨140105, by rfl⟩ : syracuseStep 186807 = 280211) B280211
theorem B186827 : Blo 183802 186827 := bstep (se 1 (by rfl) ⟨140120, by rfl⟩ : syracuseStep 186827 = 280241) B280241
theorem B186839 : Blo 183802 186839 := bstep (se 1 (by rfl) ⟨140129, by rfl⟩ : syracuseStep 186839 = 280259) B280259
theorem B186859 : Blo 183802 186859 := bstep (se 1 (by rfl) ⟨140144, by rfl⟩ : syracuseStep 186859 = 280289) B280289
theorem B186871 : Blo 183802 186871 := bstep (se 1 (by rfl) ⟨140153, by rfl⟩ : syracuseStep 186871 = 280307) B280307
theorem B416267 : Blo 183802 416267 := bstep (se 1 (by rfl) ⟨312200, by rfl⟩ : syracuseStep 416267 = 624401) B624401
theorem B186891 : Blo 183802 186891 := bstep (se 1 (by rfl) ⟨140168, by rfl⟩ : syracuseStep 186891 = 280337) B280337
theorem B186903 : Blo 183802 186903 := bstep (se 1 (by rfl) ⟨140177, by rfl⟩ : syracuseStep 186903 = 280355) B280355
theorem B186923 : Blo 183802 186923 := bstep (se 1 (by rfl) ⟨140192, by rfl⟩ : syracuseStep 186923 = 280385) B280385
theorem B186935 : Blo 183802 186935 := bstep (se 1 (by rfl) ⟨140201, by rfl⟩ : syracuseStep 186935 = 280403) B280403
theorem B416321 : Blo 183802 416321 := bstep (se 2 (by rfl) ⟨156120, by rfl⟩ : syracuseStep 416321 = 312241) B312241
theorem B186955 : Blo 183802 186955 := bstep (se 1 (by rfl) ⟨140216, by rfl⟩ : syracuseStep 186955 = 280433) B280433
theorem B186967 : Blo 183802 186967 := bstep (se 1 (by rfl) ⟨140225, by rfl⟩ : syracuseStep 186967 = 280451) B280451
theorem B186987 : Blo 183802 186987 := bstep (se 1 (by rfl) ⟨140240, by rfl⟩ : syracuseStep 186987 = 280481) B280481
theorem B186999 : Blo 183802 186999 := bstep (se 1 (by rfl) ⟨140249, by rfl⟩ : syracuseStep 186999 = 280499) B280499
theorem B187019 : Blo 183802 187019 := bstep (se 1 (by rfl) ⟨140264, by rfl⟩ : syracuseStep 187019 = 280529) B280529
theorem B187031 : Blo 183802 187031 := bstep (se 1 (by rfl) ⟨140273, by rfl⟩ : syracuseStep 187031 = 280547) B280547
theorem B187051 : Blo 183802 187051 := bstep (se 1 (by rfl) ⟨140288, by rfl⟩ : syracuseStep 187051 = 280577) B280577
theorem B187063 : Blo 183802 187063 := bstep (se 1 (by rfl) ⟨140297, by rfl⟩ : syracuseStep 187063 = 280595) B280595
theorem B187083 : Blo 183802 187083 := bstep (se 1 (by rfl) ⟨140312, by rfl⟩ : syracuseStep 187083 = 280625) B280625
theorem B187095 : Blo 183802 187095 := bstep (se 1 (by rfl) ⟨140321, by rfl⟩ : syracuseStep 187095 = 280643) B280643
theorem B187115 : Blo 183802 187115 := bstep (se 1 (by rfl) ⟨140336, by rfl⟩ : syracuseStep 187115 = 280673) B280673
theorem B187127 : Blo 183802 187127 := bstep (se 1 (by rfl) ⟨140345, by rfl⟩ : syracuseStep 187127 = 280691) B280691
theorem B187147 : Blo 183802 187147 := bstep (se 1 (by rfl) ⟨140360, by rfl⟩ : syracuseStep 187147 = 280721) B280721
theorem B187159 : Blo 183802 187159 := bstep (se 1 (by rfl) ⟨140369, by rfl⟩ : syracuseStep 187159 = 280739) B280739
theorem B416537 : Blo 183802 416537 := bstep (se 2 (by rfl) ⟨156201, by rfl⟩ : syracuseStep 416537 = 312403) B312403
theorem B187179 : Blo 183802 187179 := bstep (se 1 (by rfl) ⟨140384, by rfl⟩ : syracuseStep 187179 = 280769) B280769
theorem B187191 : Blo 183802 187191 := bstep (se 1 (by rfl) ⟨140393, by rfl⟩ : syracuseStep 187191 = 280787) B280787
theorem B187211 : Blo 183802 187211 := bstep (se 1 (by rfl) ⟨140408, by rfl⟩ : syracuseStep 187211 = 280817) B280817
theorem B187223 : Blo 183802 187223 := bstep (se 1 (by rfl) ⟨140417, by rfl⟩ : syracuseStep 187223 = 280835) B280835
theorem B187243 : Blo 183802 187243 := bstep (se 1 (by rfl) ⟨140432, by rfl⟩ : syracuseStep 187243 = 280865) B280865
theorem B416627 : Blo 183802 416627 := bstep (se 1 (by rfl) ⟨312470, by rfl⟩ : syracuseStep 416627 = 624941) B624941
theorem B187255 : Blo 183802 187255 := bstep (se 1 (by rfl) ⟨140441, by rfl⟩ : syracuseStep 187255 = 280883) B280883
theorem B187275 : Blo 183802 187275 := bstep (se 1 (by rfl) ⟨140456, by rfl⟩ : syracuseStep 187275 = 280913) B280913
theorem B416663 : Blo 183802 416663 := bstep (se 1 (by rfl) ⟨312497, by rfl⟩ : syracuseStep 416663 = 624995) B624995
theorem B187287 : Blo 183802 187287 := bstep (se 1 (by rfl) ⟨140465, by rfl⟩ : syracuseStep 187287 = 280931) B280931
theorem B187307 : Blo 183802 187307 := bstep (se 1 (by rfl) ⟨140480, by rfl⟩ : syracuseStep 187307 = 280961) B280961
theorem B187319 : Blo 183802 187319 := bstep (se 1 (by rfl) ⟨140489, by rfl⟩ : syracuseStep 187319 = 280979) B280979
theorem B187339 : Blo 183802 187339 := bstep (se 1 (by rfl) ⟨140504, by rfl⟩ : syracuseStep 187339 = 281009) B281009
theorem B252887 : Blo 183802 252887 := bstep (se 1 (by rfl) ⟨189665, by rfl⟩ : syracuseStep 252887 = 379331) B379331
theorem B187351 : Blo 183802 187351 := bstep (se 1 (by rfl) ⟨140513, by rfl⟩ : syracuseStep 187351 = 281027) B281027
theorem B449497 : Blo 183802 449497 := bstep (se 2 (by rfl) ⟨168561, by rfl⟩ : syracuseStep 449497 = 337123) B337123
theorem B187371 : Blo 183802 187371 := bstep (se 1 (by rfl) ⟨140528, by rfl⟩ : syracuseStep 187371 = 281057) B281057
theorem B187383 : Blo 183802 187383 := bstep (se 1 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 187383 = 281075) B281075
theorem B187403 : Blo 183802 187403 := bstep (se 1 (by rfl) ⟨140552, by rfl⟩ : syracuseStep 187403 = 281105) B281105
theorem B187415 : Blo 183802 187415 := bstep (se 1 (by rfl) ⟨140561, by rfl⟩ : syracuseStep 187415 = 281123) B281123
theorem B187435 : Blo 183802 187435 := bstep (se 1 (by rfl) ⟨140576, by rfl⟩ : syracuseStep 187435 = 281153) B281153
theorem B187447 : Blo 183802 187447 := bstep (se 1 (by rfl) ⟨140585, by rfl⟩ : syracuseStep 187447 = 281171) B281171
theorem B416843 : Blo 183802 416843 := bstep (se 1 (by rfl) ⟨312632, by rfl⟩ : syracuseStep 416843 = 625265) B625265
theorem B187467 : Blo 183802 187467 := bstep (se 1 (by rfl) ⟨140600, by rfl⟩ : syracuseStep 187467 = 281201) B281201
theorem B187479 : Blo 183802 187479 := bstep (se 1 (by rfl) ⟨140609, by rfl⟩ : syracuseStep 187479 = 281219) B281219
theorem B187499 : Blo 183802 187499 := bstep (se 1 (by rfl) ⟨140624, by rfl⟩ : syracuseStep 187499 = 281249) B281249
theorem B187511 : Blo 183802 187511 := bstep (se 1 (by rfl) ⟨140633, by rfl⟩ : syracuseStep 187511 = 281267) B281267
theorem B416897 : Blo 183802 416897 := bstep (se 2 (by rfl) ⟨156336, by rfl⟩ : syracuseStep 416897 = 312673) B312673
theorem B351371 : Blo 183802 351371 := bstep (se 1 (by rfl) ⟨263528, by rfl⟩ : syracuseStep 351371 = 527057) B527057
theorem B187531 : Blo 183802 187531 := bstep (se 1 (by rfl) ⟨140648, by rfl⟩ : syracuseStep 187531 = 281297) B281297
theorem B187543 : Blo 183802 187543 := bstep (se 1 (by rfl) ⟨140657, by rfl⟩ : syracuseStep 187543 = 281315) B281315
theorem B187563 : Blo 183802 187563 := bstep (se 1 (by rfl) ⟨140672, by rfl⟩ : syracuseStep 187563 = 281345) B281345
theorem B187575 : Blo 183802 187575 := bstep (se 1 (by rfl) ⟨140681, by rfl⟩ : syracuseStep 187575 = 281363) B281363
theorem B187595 : Blo 183802 187595 := bstep (se 1 (by rfl) ⟨140696, by rfl⟩ : syracuseStep 187595 = 281393) B281393
theorem B187607 : Blo 183802 187607 := bstep (se 1 (by rfl) ⟨140705, by rfl⟩ : syracuseStep 187607 = 281411) B281411
theorem B187627 : Blo 183802 187627 := bstep (se 1 (by rfl) ⟨140720, by rfl⟩ : syracuseStep 187627 = 281441) B281441
theorem B187639 : Blo 183802 187639 := bstep (se 1 (by rfl) ⟨140729, by rfl⟩ : syracuseStep 187639 = 281459) B281459
theorem B187659 : Blo 183802 187659 := bstep (se 1 (by rfl) ⟨140744, by rfl⟩ : syracuseStep 187659 = 281489) B281489
theorem B187671 : Blo 183802 187671 := bstep (se 1 (by rfl) ⟨140753, by rfl⟩ : syracuseStep 187671 = 281507) B281507
theorem B187691 : Blo 183802 187691 := bstep (se 1 (by rfl) ⟨140768, by rfl⟩ : syracuseStep 187691 = 281537) B281537
theorem B1039661 : Blo 183802 1039661 := bstep (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) B389873
theorem B187703 : Blo 183802 187703 := bstep (se 1 (by rfl) ⟨140777, by rfl⟩ : syracuseStep 187703 = 281555) B281555
theorem B351553 : Blo 183802 351553 := bstep (se 2 (by rfl) ⟨131832, by rfl⟩ : syracuseStep 351553 = 263665) B263665
theorem B187723 : Blo 183802 187723 := bstep (se 1 (by rfl) ⟨140792, by rfl⟩ : syracuseStep 187723 = 281585) B281585
theorem B187735 : Blo 183802 187735 := bstep (se 1 (by rfl) ⟨140801, by rfl⟩ : syracuseStep 187735 = 281603) B281603
theorem B417113 : Blo 183802 417113 := bstep (se 2 (by rfl) ⟨156417, by rfl⟩ : syracuseStep 417113 = 312835) B312835
theorem B1400165 : Blo 183802 1400165 := bstep (se 4 (by rfl) ⟨131265, by rfl⟩ : syracuseStep 1400165 = 262531) B262531
theorem B187755 : Blo 183802 187755 := bstep (se 1 (by rfl) ⟨140816, by rfl⟩ : syracuseStep 187755 = 281633) B281633
theorem B187767 : Blo 183802 187767 := bstep (se 1 (by rfl) ⟨140825, by rfl⟩ : syracuseStep 187767 = 281651) B281651
theorem B187787 : Blo 183802 187787 := bstep (se 1 (by rfl) ⟨140840, by rfl⟩ : syracuseStep 187787 = 281681) B281681
theorem B187799 : Blo 183802 187799 := bstep (se 1 (by rfl) ⟨140849, by rfl⟩ : syracuseStep 187799 = 281699) B281699
theorem B417203 : Blo 183802 417203 := bstep (se 1 (by rfl) ⟨312902, by rfl⟩ : syracuseStep 417203 = 625805) B625805
theorem B2383283 : Blo 183802 2383283 := bstep (se 1 (by rfl) ⟨1787462, by rfl⟩ : syracuseStep 2383283 = 3574925) B3574925
theorem B417239 : Blo 183802 417239 := bstep (se 1 (by rfl) ⟨312929, by rfl⟩ : syracuseStep 417239 = 625859) B625859
theorem B417419 : Blo 183802 417419 := bstep (se 1 (by rfl) ⟨313064, by rfl⟩ : syracuseStep 417419 = 626129) B626129
theorem B417473 : Blo 183802 417473 := bstep (se 2 (by rfl) ⟨156552, by rfl⟩ : syracuseStep 417473 = 313105) B313105
theorem B712385 : Blo 183802 712385 := bstep (se 2 (by rfl) ⟨267144, by rfl⟩ : syracuseStep 712385 = 534289) B534289
theorem B352001 : Blo 183802 352001 := bstep (se 2 (by rfl) ⟨132000, by rfl⟩ : syracuseStep 352001 = 264001) B264001
theorem B1400651 : Blo 183802 1400651 := bstep (se 1 (by rfl) ⟨1050488, by rfl⟩ : syracuseStep 1400651 = 2100977) B2100977
theorem B417689 : Blo 183802 417689 := bstep (se 2 (by rfl) ⟨156633, by rfl⟩ : syracuseStep 417689 = 313267) B313267
theorem B417779 : Blo 183802 417779 := bstep (se 1 (by rfl) ⟨313334, by rfl⟩ : syracuseStep 417779 = 626669) B626669
theorem B221195 : Blo 183802 221195 := bstep (se 1 (by rfl) ⟨165896, by rfl⟩ : syracuseStep 221195 = 331793) B331793
theorem B417815 : Blo 183802 417815 := bstep (se 1 (by rfl) ⟨313361, by rfl⟩ : syracuseStep 417815 = 626723) B626723
theorem B450625 : Blo 183802 450625 := bstep (se 2 (by rfl) ⟨168984, by rfl⟩ : syracuseStep 450625 = 337969) B337969
theorem B352343 : Blo 183802 352343 := bstep (se 1 (by rfl) ⟨264257, by rfl⟩ : syracuseStep 352343 = 528515) B528515
theorem B417995 : Blo 183802 417995 := bstep (se 1 (by rfl) ⟨313496, by rfl⟩ : syracuseStep 417995 = 626993) B626993
theorem B418049 : Blo 183802 418049 := bstep (se 2 (by rfl) ⟨156768, by rfl⟩ : syracuseStep 418049 = 313537) B313537
theorem B942353 : Blo 183802 942353 := bstep (se 2 (by rfl) ⟨353382, by rfl⟩ : syracuseStep 942353 = 706765) B706765
theorem B1827137 : Blo 183802 1827137 := bstep (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) B1370353
theorem B942515 : Blo 183802 942515 := bstep (se 1 (by rfl) ⟨706886, by rfl⟩ : syracuseStep 942515 = 1413773) B1413773
theorem B418265 : Blo 183802 418265 := bstep (se 2 (by rfl) ⟨156849, by rfl⟩ : syracuseStep 418265 = 313699) B313699
theorem B1008089 : Blo 183802 1008089 := bstep (se 2 (by rfl) ⟨378033, by rfl⟩ : syracuseStep 1008089 = 756067) B756067
theorem B745949 : Blo 183802 745949 := bstep (se 3 (by rfl) ⟨139865, by rfl⟩ : syracuseStep 745949 = 279731) B279731
theorem B418355 : Blo 183802 418355 := bstep (se 1 (by rfl) ⟨313766, by rfl⟩ : syracuseStep 418355 = 627533) B627533
theorem B418391 : Blo 183802 418391 := bstep (se 1 (by rfl) ⟨313793, by rfl⟩ : syracuseStep 418391 = 627587) B627587
theorem B353011 : Blo 183802 353011 := bstep (se 1 (by rfl) ⟨264758, by rfl⟩ : syracuseStep 353011 = 529517) B529517
theorem B418571 : Blo 183802 418571 := bstep (se 1 (by rfl) ⟨313928, by rfl⟩ : syracuseStep 418571 = 627857) B627857
theorem B418625 : Blo 183802 418625 := bstep (se 2 (by rfl) ⟨156984, by rfl⟩ : syracuseStep 418625 = 313969) B313969
theorem B680849 : Blo 183802 680849 := bstep (se 2 (by rfl) ⟨255318, by rfl⟩ : syracuseStep 680849 = 510637) B510637
theorem B418841 : Blo 183802 418841 := bstep (se 2 (by rfl) ⟨157065, by rfl⟩ : syracuseStep 418841 = 314131) B314131
theorem B418931 : Blo 183802 418931 := bstep (se 1 (by rfl) ⟨314198, by rfl⟩ : syracuseStep 418931 = 628397) B628397
theorem B418967 : Blo 183802 418967 := bstep (se 1 (by rfl) ⟨314225, by rfl⟩ : syracuseStep 418967 = 628451) B628451
theorem B353459 : Blo 183802 353459 := bstep (se 1 (by rfl) ⟨265094, by rfl⟩ : syracuseStep 353459 = 530189) B530189
theorem B353497 : Blo 183802 353497 := bstep (se 2 (by rfl) ⟨132561, by rfl⟩ : syracuseStep 353497 = 265123) B265123
theorem B419147 : Blo 183802 419147 := bstep (se 1 (by rfl) ⟨314360, by rfl⟩ : syracuseStep 419147 = 628721) B628721
theorem B419201 : Blo 183802 419201 := bstep (se 2 (by rfl) ⟨157200, by rfl⟩ : syracuseStep 419201 = 314401) B314401
theorem B1598899 : Blo 183802 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B1009217 : Blo 183802 1009217 := bstep (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) B756913
theorem B1336907 : Blo 183802 1336907 := bstep (se 1 (by rfl) ⟨1002680, by rfl⟩ : syracuseStep 1336907 = 2005361) B2005361
theorem B419417 : Blo 183802 419417 := bstep (se 2 (by rfl) ⟨157281, by rfl⟩ : syracuseStep 419417 = 314563) B314563
theorem B353945 : Blo 183802 353945 := bstep (se 2 (by rfl) ⟨132729, by rfl⟩ : syracuseStep 353945 = 265459) B265459
theorem B419507 : Blo 183802 419507 := bstep (se 1 (by rfl) ⟨314630, by rfl⟩ : syracuseStep 419507 = 629261) B629261
theorem B419543 : Blo 183802 419543 := bstep (se 1 (by rfl) ⟨314657, by rfl⟩ : syracuseStep 419543 = 629315) B629315
theorem B419723 : Blo 183802 419723 := bstep (se 1 (by rfl) ⟨314792, by rfl⟩ : syracuseStep 419723 = 629585) B629585
theorem B419777 : Blo 183802 419777 := bstep (se 2 (by rfl) ⟨157416, by rfl⟩ : syracuseStep 419777 = 314833) B314833
theorem B419993 : Blo 183802 419993 := bstep (se 2 (by rfl) ⟨157497, by rfl⟩ : syracuseStep 419993 = 314995) B314995
theorem B420083 : Blo 183802 420083 := bstep (se 1 (by rfl) ⟨315062, by rfl⟩ : syracuseStep 420083 = 630125) B630125
theorem B420119 : Blo 183802 420119 := bstep (se 1 (by rfl) ⟨315089, by rfl⟩ : syracuseStep 420119 = 630179) B630179
theorem B944459 : Blo 183802 944459 := bstep (se 1 (by rfl) ⟨708344, by rfl⟩ : syracuseStep 944459 = 1416689) B1416689
theorem B354689 : Blo 183802 354689 := bstep (se 2 (by rfl) ⟨133008, by rfl⟩ : syracuseStep 354689 = 266017) B266017
theorem B420299 : Blo 183802 420299 := bstep (se 1 (by rfl) ⟨315224, by rfl⟩ : syracuseStep 420299 = 630449) B630449
theorem B420353 : Blo 183802 420353 := bstep (se 2 (by rfl) ⟨157632, by rfl⟩ : syracuseStep 420353 = 315265) B315265
theorem B2124305 : Blo 183802 2124305 := bstep (se 2 (by rfl) ⟨796614, by rfl⟩ : syracuseStep 2124305 = 1593229) B1593229
theorem B354955 : Blo 183802 354955 := bstep (se 1 (by rfl) ⟨266216, by rfl⟩ : syracuseStep 354955 = 532433) B532433
theorem B420569 : Blo 183802 420569 := bstep (se 2 (by rfl) ⟨157713, by rfl⟩ : syracuseStep 420569 = 315427) B315427
theorem B420659 : Blo 183802 420659 := bstep (se 1 (by rfl) ⟨315494, by rfl⟩ : syracuseStep 420659 = 630989) B630989
theorem B420695 : Blo 183802 420695 := bstep (se 1 (by rfl) ⟨315521, by rfl⟩ : syracuseStep 420695 = 631043) B631043
theorem B682897 : Blo 183802 682897 := bstep (se 2 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 682897 = 512173) B512173
theorem B3140531 : Blo 183802 3140531 := bstep (se 1 (by rfl) ⟨2355398, by rfl⟩ : syracuseStep 3140531 = 4710797) B4710797
theorem B420875 : Blo 183802 420875 := bstep (se 1 (by rfl) ⟨315656, by rfl⟩ : syracuseStep 420875 = 631313) B631313
theorem B420929 : Blo 183802 420929 := bstep (se 2 (by rfl) ⟨157848, by rfl⟩ : syracuseStep 420929 = 315697) B315697
theorem B355403 : Blo 183802 355403 := bstep (se 1 (by rfl) ⟨266552, by rfl⟩ : syracuseStep 355403 = 533105) B533105
theorem B355585 : Blo 183802 355585 := bstep (se 2 (by rfl) ⟨133344, by rfl⟩ : syracuseStep 355585 = 266689) B266689
theorem B421145 : Blo 183802 421145 := bstep (se 2 (by rfl) ⟨157929, by rfl⟩ : syracuseStep 421145 = 315859) B315859
theorem B421235 : Blo 183802 421235 := bstep (se 1 (by rfl) ⟨315926, by rfl⟩ : syracuseStep 421235 = 631853) B631853
theorem B224663 : Blo 183802 224663 := bstep (se 1 (by rfl) ⟨168497, by rfl⟩ : syracuseStep 224663 = 336995) B336995
theorem B421271 : Blo 183802 421271 := bstep (se 1 (by rfl) ⟨315953, by rfl⟩ : syracuseStep 421271 = 631907) B631907
theorem B421451 : Blo 183802 421451 := bstep (se 1 (by rfl) ⟨316088, by rfl⟩ : syracuseStep 421451 = 632177) B632177
theorem B355927 : Blo 183802 355927 := bstep (se 1 (by rfl) ⟨266945, by rfl⟩ : syracuseStep 355927 = 533891) B533891
theorem B421505 : Blo 183802 421505 := bstep (se 2 (by rfl) ⟨158064, by rfl⟩ : syracuseStep 421505 = 316129) B316129
theorem B356147 : Blo 183802 356147 := bstep (se 1 (by rfl) ⟨267110, by rfl⟩ : syracuseStep 356147 = 534221) B534221
theorem B421721 : Blo 183802 421721 := bstep (se 2 (by rfl) ⟨158145, by rfl⟩ : syracuseStep 421721 = 316291) B316291
theorem B225163 : Blo 183802 225163 := bstep (se 1 (by rfl) ⟨168872, by rfl⟩ : syracuseStep 225163 = 337745) B337745
theorem B421811 : Blo 183802 421811 := bstep (se 1 (by rfl) ⟨316358, by rfl⟩ : syracuseStep 421811 = 632717) B632717
theorem B421847 : Blo 183802 421847 := bstep (se 1 (by rfl) ⟨316385, by rfl⟩ : syracuseStep 421847 = 632771) B632771
theorem B749533 : Blo 183802 749533 := bstep (se 3 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 749533 = 281075) B281075
theorem B356375 : Blo 183802 356375 := bstep (se 1 (by rfl) ⟨267281, by rfl⟩ : syracuseStep 356375 = 534563) B534563
theorem B946241 : Blo 183802 946241 := bstep (se 2 (by rfl) ⟨354840, by rfl⟩ : syracuseStep 946241 = 709681) B709681
theorem B389207 : Blo 183802 389207 := bstep (se 1 (by rfl) ⟨291905, by rfl⟩ : syracuseStep 389207 = 583811) B583811
theorem B422027 : Blo 183802 422027 := bstep (se 1 (by rfl) ⟨316520, by rfl⟩ : syracuseStep 422027 = 633041) B633041
theorem B422081 : Blo 183802 422081 := bstep (se 2 (by rfl) ⟨158280, by rfl⟩ : syracuseStep 422081 = 316561) B316561
theorem B422131 : Blo 183802 422131 := bstep (se 1 (by rfl) ⟨316598, by rfl⟩ : syracuseStep 422131 = 633197) B633197
theorem B422297 : Blo 183802 422297 := bstep (se 2 (by rfl) ⟨158361, by rfl⟩ : syracuseStep 422297 = 316723) B316723
theorem B422387 : Blo 183802 422387 := bstep (se 1 (by rfl) ⟨316790, by rfl⟩ : syracuseStep 422387 = 633581) B633581
theorem B422423 : Blo 183802 422423 := bstep (se 1 (by rfl) ⟨316817, by rfl⟩ : syracuseStep 422423 = 633635) B633635
theorem B1798807 : Blo 183802 1798807 := bstep (se 1 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 1798807 = 2698211) B2698211
theorem B225995 : Blo 183802 225995 := bstep (se 1 (by rfl) ⟨169496, by rfl⟩ : syracuseStep 225995 = 338993) B338993
theorem B3240805 : Blo 183802 3240805 := bstep (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) B607651
theorem B1995637 : Blo 183802 1995637 := bstep (se 5 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 1995637 = 187091) B187091
theorem B1405997 : Blo 183802 1405997 := bstep (se 3 (by rfl) ⟨263624, by rfl⟩ : syracuseStep 1405997 = 527249) B527249
theorem B357529 : Blo 183802 357529 := bstep (se 2 (by rfl) ⟨134073, by rfl⟩ : syracuseStep 357529 = 268147) B268147
theorem B2127221 : Blo 183802 2127221 := bstep (se 5 (by rfl) ⟨99713, by rfl⟩ : syracuseStep 2127221 = 199427) B199427
theorem B423883 : Blo 183802 423883 := bstep (se 1 (by rfl) ⟨317912, by rfl⟩ : syracuseStep 423883 = 635825) B635825
theorem B948185 : Blo 183802 948185 := bstep (se 2 (by rfl) ⟨355569, by rfl⟩ : syracuseStep 948185 = 711139) B711139
theorem B620567 : Blo 183802 620567 := bstep (se 1 (by rfl) ⟨465425, by rfl⟩ : syracuseStep 620567 = 930851) B930851
theorem B1800323 : Blo 183802 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B621107 : Blo 183802 621107 := bstep (se 1 (by rfl) ⟨465830, by rfl⟩ : syracuseStep 621107 = 931661) B931661
theorem B1997405 : Blo 183802 1997405 := bstep (se 3 (by rfl) ⟨374513, by rfl⟩ : syracuseStep 1997405 = 749027) B749027
theorem B752273 : Blo 183802 752273 := bstep (se 2 (by rfl) ⟨282102, by rfl⟩ : syracuseStep 752273 = 564205) B564205
theorem B359129 : Blo 183802 359129 := bstep (se 2 (by rfl) ⟨134673, by rfl⟩ : syracuseStep 359129 = 269347) B269347
theorem B752435 : Blo 183802 752435 := bstep (se 1 (by rfl) ⟨564326, by rfl⟩ : syracuseStep 752435 = 1128653) B1128653
theorem B621377 : Blo 183802 621377 := bstep (se 2 (by rfl) ⟨233016, by rfl⟩ : syracuseStep 621377 = 466033) B466033
theorem B359257 : Blo 183802 359257 := bstep (se 2 (by rfl) ⟨134721, by rfl⟩ : syracuseStep 359257 = 269443) B269443
theorem B1014707 : Blo 183802 1014707 := bstep (se 1 (by rfl) ⟨761030, by rfl⟩ : syracuseStep 1014707 = 1522061) B1522061
theorem B1178725 : Blo 183802 1178725 := bstep (se 4 (by rfl) ⟨110505, by rfl⟩ : syracuseStep 1178725 = 221011) B221011
theorem B621917 : Blo 183802 621917 := bstep (se 3 (by rfl) ⟨116609, by rfl⟩ : syracuseStep 621917 = 233219) B233219
theorem B392627 : Blo 183802 392627 := bstep (se 1 (by rfl) ⟨294470, by rfl⟩ : syracuseStep 392627 = 588941) B588941
theorem B523741 : Blo 183802 523741 := bstep (se 3 (by rfl) ⟨98201, by rfl⟩ : syracuseStep 523741 = 196403) B196403
theorem B949805 : Blo 183802 949805 := bstep (se 3 (by rfl) ⟨178088, by rfl⟩ : syracuseStep 949805 = 356177) B356177
theorem B524083 : Blo 183802 524083 := bstep (se 1 (by rfl) ⟨393062, by rfl⟩ : syracuseStep 524083 = 786125) B786125
theorem B589619 : Blo 183802 589619 := bstep (se 1 (by rfl) ⟨442214, by rfl⟩ : syracuseStep 589619 = 884429) B884429
theorem B589853 : Blo 183802 589853 := bstep (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) B221195
theorem B262315 : Blo 183802 262315 := bstep (se 1 (by rfl) ⟨196736, by rfl⟩ : syracuseStep 262315 = 393473) B393473
theorem B6750449 : Blo 183802 6750449 := bstep (se 2 (by rfl) ⟨2531418, by rfl⟩ : syracuseStep 6750449 = 5062837) B5062837
theorem B2162933 : Blo 183802 2162933 := bstep (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) B202775
theorem B262543 : Blo 183802 262543 := bstep (se 1 (by rfl) ⟨196907, by rfl⟩ : syracuseStep 262543 = 393815) B393815
theorem B1409501 : Blo 183802 1409501 := bstep (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) B528563
theorem B590593 : Blo 183802 590593 := bstep (se 2 (by rfl) ⟨221472, by rfl⟩ : syracuseStep 590593 = 442945) B442945
theorem B623375 : Blo 183802 623375 := bstep (se 1 (by rfl) ⟨467531, by rfl⟩ : syracuseStep 623375 = 935063) B935063
theorem B1049395 : Blo 183802 1049395 := bstep (se 1 (by rfl) ⟨787046, by rfl⟩ : syracuseStep 1049395 = 1574093) B1574093
theorem B525143 : Blo 183802 525143 := bstep (se 1 (by rfl) ⟨393857, by rfl⟩ : syracuseStep 525143 = 787715) B787715
theorem B623645 : Blo 183802 623645 := bstep (se 3 (by rfl) ⟨116933, by rfl⟩ : syracuseStep 623645 = 233867) B233867
theorem B22808141 : Blo 183802 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B2131865 : Blo 183802 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B1050853 : Blo 183802 1050853 := bstep (se 4 (by rfl) ⟨98517, by rfl⟩ : syracuseStep 1050853 = 197035) B197035
theorem B5114177 : Blo 183802 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B625049 : Blo 183802 625049 := bstep (se 2 (by rfl) ⟨234393, by rfl⟩ : syracuseStep 625049 = 468787) B468787
theorem B592427 : Blo 183802 592427 := bstep (se 1 (by rfl) ⟨444320, by rfl⟩ : syracuseStep 592427 = 888641) B888641
theorem B1772549 : Blo 183802 1772549 := bstep (se 4 (by rfl) ⟨166176, by rfl⟩ : syracuseStep 1772549 = 332353) B332353
theorem B265231 : Blo 183802 265231 := bstep (se 1 (by rfl) ⟨198923, by rfl⟩ : syracuseStep 265231 = 397847) B397847
theorem B2133053 : Blo 183802 2133053 := bstep (se 3 (by rfl) ⟨399947, by rfl⟩ : syracuseStep 2133053 = 799895) B799895
theorem B625751 : Blo 183802 625751 := bstep (se 1 (by rfl) ⟨469313, by rfl⟩ : syracuseStep 625751 = 938627) B938627
theorem B265351 : Blo 183802 265351 := bstep (se 1 (by rfl) ⟨199013, by rfl⟩ : syracuseStep 265351 = 398027) B398027
theorem B232951 : Blo 183802 232951 := bstep (se 1 (by rfl) ⟨174713, by rfl⟩ : syracuseStep 232951 = 349427) B349427
theorem B527887 : Blo 183802 527887 := bstep (se 1 (by rfl) ⟨395915, by rfl⟩ : syracuseStep 527887 = 791831) B791831
theorem B527933 : Blo 183802 527933 := bstep (se 3 (by rfl) ⟨98987, by rfl⟩ : syracuseStep 527933 = 197975) B197975
theorem B626237 : Blo 183802 626237 := bstep (se 3 (by rfl) ⟨117419, by rfl⟩ : syracuseStep 626237 = 234839) B234839
theorem B1412801 : Blo 183802 1412801 := bstep (se 2 (by rfl) ⟨529800, by rfl⟩ : syracuseStep 1412801 = 1059601) B1059601
theorem B397001 : Blo 183802 397001 := bstep (se 2 (by rfl) ⟨148875, by rfl⟩ : syracuseStep 397001 = 297751) B297751
theorem B233275 : Blo 183802 233275 := bstep (se 1 (by rfl) ⟨174956, by rfl⟩ : syracuseStep 233275 = 349913) B349913
theorem B528275 : Blo 183802 528275 := bstep (se 1 (by rfl) ⟨396206, by rfl⟩ : syracuseStep 528275 = 792413) B792413
theorem B2691245 : Blo 183802 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B2396405 : Blo 183802 2396405 := bstep (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) B224663
theorem B266809 : Blo 183802 266809 := bstep (se 2 (by rfl) ⟨100053, by rfl⟩ : syracuseStep 266809 = 200107) B200107
theorem B234247 : Blo 183802 234247 := bstep (se 1 (by rfl) ⟨175685, by rfl⟩ : syracuseStep 234247 = 351371) B351371
theorem B529163 : Blo 183802 529163 := bstep (se 1 (by rfl) ⟨396872, by rfl⟩ : syracuseStep 529163 = 793745) B793745
theorem B693107 : Blo 183802 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B594823 : Blo 183802 594823 := bstep (se 1 (by rfl) ⟨446117, by rfl⟩ : syracuseStep 594823 = 892235) B892235
theorem B1053587 : Blo 183802 1053587 := bstep (se 1 (by rfl) ⟨790190, by rfl⟩ : syracuseStep 1053587 = 1580381) B1580381
theorem B627641 : Blo 183802 627641 := bstep (se 2 (by rfl) ⟨235365, by rfl⟩ : syracuseStep 627641 = 470731) B470731
theorem B857099 : Blo 183802 857099 := bstep (se 1 (by rfl) ⟨642824, by rfl⟩ : syracuseStep 857099 = 1285649) B1285649
theorem B726059 : Blo 183802 726059 := bstep (se 1 (by rfl) ⟨544544, by rfl⟩ : syracuseStep 726059 = 1089089) B1089089
theorem B1610813 : Blo 183802 1610813 := bstep (se 3 (by rfl) ⟨302027, by rfl⟩ : syracuseStep 1610813 = 604055) B604055
theorem B922711 : Blo 183802 922711 := bstep (se 1 (by rfl) ⟨692033, by rfl⟩ : syracuseStep 922711 = 1384067) B1384067
theorem B234667 : Blo 183802 234667 := bstep (se 1 (by rfl) ⟨176000, by rfl⟩ : syracuseStep 234667 = 352001) B352001
theorem B1283309 : Blo 183802 1283309 := bstep (se 3 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 1283309 = 481241) B481241
theorem B595259 : Blo 183802 595259 := bstep (se 1 (by rfl) ⟨446444, by rfl⟩ : syracuseStep 595259 = 892889) B892889
theorem B234895 : Blo 183802 234895 := bstep (se 1 (by rfl) ⟨176171, by rfl⟩ : syracuseStep 234895 = 352343) B352343
theorem B628235 : Blo 183802 628235 := bstep (se 1 (by rfl) ⟨471176, by rfl⟩ : syracuseStep 628235 = 942353) B942353
theorem B1218091 : Blo 183802 1218091 := bstep (se 1 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 1218091 = 1827137) B1827137
theorem B1054295 : Blo 183802 1054295 := bstep (se 1 (by rfl) ⟨790721, by rfl⟩ : syracuseStep 1054295 = 1581443) B1581443
theorem B628343 : Blo 183802 628343 := bstep (se 1 (by rfl) ⟨471257, by rfl⟩ : syracuseStep 628343 = 942515) B942515
theorem B497299 : Blo 183802 497299 := bstep (se 1 (by rfl) ⟨372974, by rfl⟩ : syracuseStep 497299 = 745949) B745949
theorem B562841 : Blo 183802 562841 := bstep (se 2 (by rfl) ⟨211065, by rfl⟩ : syracuseStep 562841 = 422131) B422131
theorem B595745 : Blo 183802 595745 := bstep (se 2 (by rfl) ⟨223404, by rfl⟩ : syracuseStep 595745 = 446809) B446809
theorem B235639 : Blo 183802 235639 := bstep (se 1 (by rfl) ⟨176729, by rfl⟩ : syracuseStep 235639 = 353459) B353459
theorem B628937 : Blo 183802 628937 := bstep (se 2 (by rfl) ⟨235851, by rfl⟩ : syracuseStep 628937 = 471703) B471703
theorem B2398409 : Blo 183802 2398409 := bstep (se 2 (by rfl) ⟨899403, by rfl⟩ : syracuseStep 2398409 = 1798807) B1798807
theorem B530803 : Blo 183802 530803 := bstep (se 1 (by rfl) ⟨398102, by rfl⟩ : syracuseStep 530803 = 796205) B796205
theorem B334199 : Blo 183802 334199 := bstep (se 1 (by rfl) ⟨250649, by rfl⟩ : syracuseStep 334199 = 501299) B501299
theorem B891271 : Blo 183802 891271 := bstep (se 1 (by rfl) ⟨668453, by rfl⟩ : syracuseStep 891271 = 1336907) B1336907
theorem B235963 : Blo 183802 235963 := bstep (se 1 (by rfl) ⟨176972, by rfl⟩ : syracuseStep 235963 = 353945) B353945
theorem B2660849 : Blo 183802 2660849 := bstep (se 2 (by rfl) ⟨997818, by rfl⟩ : syracuseStep 2660849 = 1995637) B1995637
theorem B531031 : Blo 183802 531031 := bstep (se 1 (by rfl) ⟨398273, by rfl⟩ : syracuseStep 531031 = 796547) B796547
theorem B465527 : Blo 183802 465527 := bstep (se 1 (by rfl) ⟨349145, by rfl⟩ : syracuseStep 465527 = 698291) B698291
theorem B400187 : Blo 183802 400187 := bstep (se 1 (by rfl) ⟨300140, by rfl⟩ : syracuseStep 400187 = 600281) B600281
theorem B629639 : Blo 183802 629639 := bstep (se 1 (by rfl) ⟨472229, by rfl⟩ : syracuseStep 629639 = 944459) B944459
theorem B236459 : Blo 183802 236459 := bstep (se 1 (by rfl) ⟨177344, by rfl⟩ : syracuseStep 236459 = 354689) B354689
theorem B1416203 : Blo 183802 1416203 := bstep (se 1 (by rfl) ⟨1062152, by rfl⟩ : syracuseStep 1416203 = 2124305) B2124305
theorem B630017 : Blo 183802 630017 := bstep (se 2 (by rfl) ⟨236256, by rfl⟩ : syracuseStep 630017 = 472513) B472513
theorem B1187131 : Blo 183802 1187131 := bstep (se 1 (by rfl) ⟨890348, by rfl⟩ : syracuseStep 1187131 = 1780697) B1780697
theorem B236935 : Blo 183802 236935 := bstep (se 1 (by rfl) ⟨177701, by rfl⟩ : syracuseStep 236935 = 355403) B355403
theorem B1056185 : Blo 183802 1056185 := bstep (se 2 (by rfl) ⟨396069, by rfl⟩ : syracuseStep 1056185 = 792139) B792139
theorem B466519 : Blo 183802 466519 := bstep (se 1 (by rfl) ⟨349889, by rfl⟩ : syracuseStep 466519 = 699779) B699779
theorem B237431 : Blo 183802 237431 := bstep (se 1 (by rfl) ⟨178073, by rfl⟩ : syracuseStep 237431 = 356147) B356147
theorem B466823 : Blo 183802 466823 := bstep (se 1 (by rfl) ⟨350117, by rfl⟩ : syracuseStep 466823 = 700235) B700235
theorem B663481 : Blo 183802 663481 := bstep (se 2 (by rfl) ⟨248805, by rfl⟩ : syracuseStep 663481 = 497611) B497611
theorem B565177 : Blo 183802 565177 := bstep (se 2 (by rfl) ⟨211941, by rfl⟩ : syracuseStep 565177 = 423883) B423883
theorem B466955 : Blo 183802 466955 := bstep (se 1 (by rfl) ⟨350216, by rfl⟩ : syracuseStep 466955 = 700433) B700433
theorem B237583 : Blo 183802 237583 := bstep (se 1 (by rfl) ⟨178187, by rfl⟩ : syracuseStep 237583 = 356375) B356375
theorem B630827 : Blo 183802 630827 := bstep (se 1 (by rfl) ⟨473120, by rfl⟩ : syracuseStep 630827 = 946241) B946241
theorem B532615 : Blo 183802 532615 := bstep (se 1 (by rfl) ⟨399461, by rfl⟩ : syracuseStep 532615 = 798923) B798923
theorem B532889 : Blo 183802 532889 := bstep (se 2 (by rfl) ⟨199833, by rfl⟩ : syracuseStep 532889 = 399667) B399667
theorem B532993 : Blo 183802 532993 := bstep (se 2 (by rfl) ⟨199872, by rfl⟩ : syracuseStep 532993 = 399745) B399745
theorem B467471 : Blo 183802 467471 := bstep (se 1 (by rfl) ⟨350603, by rfl⟩ : syracuseStep 467471 = 701207) B701207
theorem B467603 : Blo 183802 467603 := bstep (se 1 (by rfl) ⟨350702, by rfl⟩ : syracuseStep 467603 = 701405) B701405
theorem B336683 : Blo 183802 336683 := bstep (se 1 (by rfl) ⟨252512, by rfl⟩ : syracuseStep 336683 = 505025) B505025
theorem B1418147 : Blo 183802 1418147 := bstep (se 1 (by rfl) ⟨1063610, by rfl⟩ : syracuseStep 1418147 = 2127221) B2127221
theorem B1778699 : Blo 183802 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B1582091 : Blo 183802 1582091 := bstep (se 1 (by rfl) ⟨1186568, by rfl⟩ : syracuseStep 1582091 = 2373137) B2373137
theorem B599051 : Blo 183802 599051 := bstep (se 1 (by rfl) ⟨449288, by rfl⟩ : syracuseStep 599051 = 898577) B898577
theorem B533537 : Blo 183802 533537 := bstep (se 2 (by rfl) ⟨200076, by rfl⟩ : syracuseStep 533537 = 400153) B400153
theorem B599329 : Blo 183802 599329 := bstep (se 2 (by rfl) ⟨224748, by rfl⟩ : syracuseStep 599329 = 449497) B449497
theorem B632123 : Blo 183802 632123 := bstep (se 1 (by rfl) ⟨474092, by rfl⟩ : syracuseStep 632123 = 948185) B948185
theorem B2106809 : Blo 183802 2106809 := bstep (se 2 (by rfl) ⟨790053, by rfl⟩ : syracuseStep 2106809 = 1580107) B1580107
theorem B796189 : Blo 183802 796189 := bstep (se 3 (by rfl) ⟨149285, by rfl⟩ : syracuseStep 796189 = 298571) B298571
theorem B534077 : Blo 183802 534077 := bstep (se 3 (by rfl) ⟨100139, by rfl⟩ : syracuseStep 534077 = 200279) B200279
theorem B468737 : Blo 183802 468737 := bstep (se 2 (by rfl) ⟨175776, by rfl⟩ : syracuseStep 468737 = 351553) B351553
theorem B501515 : Blo 183802 501515 := bstep (se 1 (by rfl) ⟨376136, by rfl⟩ : syracuseStep 501515 = 752273) B752273
theorem B632609 : Blo 183802 632609 := bstep (se 2 (by rfl) ⟨237228, by rfl⟩ : syracuseStep 632609 = 474457) B474457
theorem B239419 : Blo 183802 239419 := bstep (se 1 (by rfl) ⟨179564, by rfl⟩ : syracuseStep 239419 = 359129) B359129
theorem B501623 : Blo 183802 501623 := bstep (se 1 (by rfl) ⟨376217, by rfl⟩ : syracuseStep 501623 = 752435) B752435
theorem B206779 : Blo 183802 206779 := bstep (se 1 (by rfl) ⟨155084, by rfl⟩ : syracuseStep 206779 = 310169) B310169
theorem B698321 : Blo 183802 698321 := bstep (se 2 (by rfl) ⟨261870, by rfl⟩ : syracuseStep 698321 = 523741) B523741
theorem B534539 : Blo 183802 534539 := bstep (se 1 (by rfl) ⟨400904, by rfl⟩ : syracuseStep 534539 = 801809) B801809
theorem B469111 : Blo 183802 469111 := bstep (se 1 (by rfl) ⟨351833, by rfl⟩ : syracuseStep 469111 = 703667) B703667
theorem B2697461 : Blo 183802 2697461 := bstep (se 5 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 2697461 = 252887) B252887
theorem B633203 : Blo 183802 633203 := bstep (se 1 (by rfl) ⟨474902, by rfl⟩ : syracuseStep 633203 = 949805) B949805
theorem B207247 : Blo 183802 207247 := bstep (se 1 (by rfl) ⟨155435, by rfl⟩ : syracuseStep 207247 = 310871) B310871
theorem B698777 : Blo 183802 698777 := bstep (se 2 (by rfl) ⟨262041, by rfl⟩ : syracuseStep 698777 = 524083) B524083
theorem B469547 : Blo 183802 469547 := bstep (se 1 (by rfl) ⟨352160, by rfl⟩ : syracuseStep 469547 = 704321) B704321
theorem B600833 : Blo 183802 600833 := bstep (se 2 (by rfl) ⟨225312, by rfl⟩ : syracuseStep 600833 = 450625) B450625
theorem B600947 : Blo 183802 600947 := bstep (se 1 (by rfl) ⟨450710, by rfl⟩ : syracuseStep 600947 = 901421) B901421
theorem B207751 : Blo 183802 207751 := bstep (se 1 (by rfl) ⟨155813, by rfl⟩ : syracuseStep 207751 = 311627) B311627
theorem B207931 : Blo 183802 207931 := bstep (se 1 (by rfl) ⟨155948, by rfl⟩ : syracuseStep 207931 = 311897) B311897
theorem B1420577 : Blo 183802 1420577 := bstep (se 2 (by rfl) ⟨532716, by rfl⟩ : syracuseStep 1420577 = 1065433) B1065433
theorem B896345 : Blo 183802 896345 := bstep (se 2 (by rfl) ⟨336129, by rfl⟩ : syracuseStep 896345 = 672259) B672259
theorem B470387 : Blo 183802 470387 := bstep (se 1 (by rfl) ⟨352790, by rfl⟩ : syracuseStep 470387 = 705581) B705581
theorem B470407 : Blo 183802 470407 := bstep (se 1 (by rfl) ⟨352805, by rfl⟩ : syracuseStep 470407 = 705611) B705611
theorem B1420753 : Blo 183802 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B208399 : Blo 183802 208399 := bstep (se 1 (by rfl) ⟨156299, by rfl⟩ : syracuseStep 208399 = 312599) B312599
theorem B699947 : Blo 183802 699947 := bstep (se 1 (by rfl) ⟨524960, by rfl⟩ : syracuseStep 699947 = 1049921) B1049921
theorem B896579 : Blo 183802 896579 := bstep (se 1 (by rfl) ⟨672434, by rfl⟩ : syracuseStep 896579 = 1344869) B1344869
theorem B470681 : Blo 183802 470681 := bstep (se 2 (by rfl) ⟨176505, by rfl⟩ : syracuseStep 470681 = 353011) B353011
theorem B470843 : Blo 183802 470843 := bstep (se 1 (by rfl) ⟨353132, by rfl⟩ : syracuseStep 470843 = 706265) B706265
theorem B208903 : Blo 183802 208903 := bstep (se 1 (by rfl) ⟨156677, by rfl⟩ : syracuseStep 208903 = 313355) B313355
theorem B471055 : Blo 183802 471055 := bstep (se 1 (by rfl) ⟨353291, by rfl⟩ : syracuseStep 471055 = 706583) B706583
theorem B209083 : Blo 183802 209083 := bstep (se 1 (by rfl) ⟨156812, by rfl⟩ : syracuseStep 209083 = 313625) B313625
theorem B1421549 : Blo 183802 1421549 := bstep (se 3 (by rfl) ⟨266540, by rfl⟩ : syracuseStep 1421549 = 533081) B533081
theorem B471329 : Blo 183802 471329 := bstep (se 2 (by rfl) ⟨176748, by rfl⟩ : syracuseStep 471329 = 353497) B353497
theorem B2044295 : Blo 183802 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B3322259 : Blo 183802 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B602653 : Blo 183802 602653 := bstep (se 3 (by rfl) ⟨112997, by rfl⟩ : syracuseStep 602653 = 225995) B225995
theorem B209551 : Blo 183802 209551 := bstep (se 1 (by rfl) ⟨157163, by rfl⟩ : syracuseStep 209551 = 314327) B314327
theorem B668569 : Blo 183802 668569 := bstep (se 2 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 668569 = 501427) B501427
theorem B209935 : Blo 183802 209935 := bstep (se 1 (by rfl) ⟨157451, by rfl⟩ : syracuseStep 209935 = 314903) B314903
theorem B210055 : Blo 183802 210055 := bstep (se 1 (by rfl) ⟨157541, by rfl⟩ : syracuseStep 210055 = 315083) B315083
theorem B472331 : Blo 183802 472331 := bstep (se 1 (by rfl) ⟨354248, by rfl⟩ : syracuseStep 472331 = 708497) B708497
theorem B1586465 : Blo 183802 1586465 := bstep (se 2 (by rfl) ⟨594924, by rfl⟩ : syracuseStep 1586465 = 1189849) B1189849
theorem B275771 : Blo 183802 275771 := bstep (se 1 (by rfl) ⟨206828, by rfl⟩ : syracuseStep 275771 = 413657) B413657
theorem B210235 : Blo 183802 210235 := bstep (se 1 (by rfl) ⟨157676, by rfl⟩ : syracuseStep 210235 = 315353) B315353
theorem B275831 : Blo 183802 275831 := bstep (se 1 (by rfl) ⟨206873, by rfl⟩ : syracuseStep 275831 = 413747) B413747
theorem B275855 : Blo 183802 275855 := bstep (se 1 (by rfl) ⟨206891, by rfl⟩ : syracuseStep 275855 = 413783) B413783
theorem B275897 : Blo 183802 275897 := bstep (se 2 (by rfl) ⟨103461, by rfl⟩ : syracuseStep 275897 = 206923) B206923
theorem B701905 : Blo 183802 701905 := bstep (se 2 (by rfl) ⟨263214, by rfl⟩ : syracuseStep 701905 = 526429) B526429
theorem B3225091 : Blo 183802 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B275975 : Blo 183802 275975 := bstep (se 1 (by rfl) ⟨206981, by rfl⟩ : syracuseStep 275975 = 413963) B413963
theorem B276011 : Blo 183802 276011 := bstep (se 1 (by rfl) ⟨207008, by rfl⟩ : syracuseStep 276011 = 414017) B414017
theorem B276041 : Blo 183802 276041 := bstep (se 2 (by rfl) ⟨103515, by rfl⟩ : syracuseStep 276041 = 207031) B207031
theorem B276155 : Blo 183802 276155 := bstep (se 1 (by rfl) ⟨207116, by rfl⟩ : syracuseStep 276155 = 414233) B414233
theorem B276215 : Blo 183802 276215 := bstep (se 1 (by rfl) ⟨207161, by rfl⟩ : syracuseStep 276215 = 414323) B414323
theorem B702209 : Blo 183802 702209 := bstep (se 2 (by rfl) ⟨263328, by rfl⟩ : syracuseStep 702209 = 526657) B526657
theorem B276239 : Blo 183802 276239 := bstep (se 1 (by rfl) ⟨207179, by rfl⟩ : syracuseStep 276239 = 414359) B414359
theorem B210703 : Blo 183802 210703 := bstep (se 1 (by rfl) ⟨158027, by rfl⟩ : syracuseStep 210703 = 316055) B316055
theorem B276281 : Blo 183802 276281 := bstep (se 2 (by rfl) ⟨103605, by rfl⟩ : syracuseStep 276281 = 207211) B207211
theorem B276359 : Blo 183802 276359 := bstep (se 1 (by rfl) ⟨207269, by rfl⟩ : syracuseStep 276359 = 414539) B414539
theorem B1062791 : Blo 183802 1062791 := bstep (se 1 (by rfl) ⟨797093, by rfl⟩ : syracuseStep 1062791 = 1594187) B1594187
theorem B472979 : Blo 183802 472979 := bstep (se 1 (by rfl) ⟨354734, by rfl⟩ : syracuseStep 472979 = 709469) B709469
theorem B276395 : Blo 183802 276395 := bstep (se 1 (by rfl) ⟨207296, by rfl⟩ : syracuseStep 276395 = 414593) B414593
theorem B276425 : Blo 183802 276425 := bstep (se 2 (by rfl) ⟨103659, by rfl⟩ : syracuseStep 276425 = 207319) B207319
theorem B276539 : Blo 183802 276539 := bstep (se 1 (by rfl) ⟨207404, by rfl⟩ : syracuseStep 276539 = 414809) B414809
theorem B276599 : Blo 183802 276599 := bstep (se 1 (by rfl) ⟨207449, by rfl⟩ : syracuseStep 276599 = 414899) B414899
theorem B899191 : Blo 183802 899191 := bstep (se 1 (by rfl) ⟨674393, by rfl⟩ : syracuseStep 899191 = 1348787) B1348787
theorem B800887 : Blo 183802 800887 := bstep (se 1 (by rfl) ⟨600665, by rfl⟩ : syracuseStep 800887 = 1201331) B1201331
theorem B1620101 : Blo 183802 1620101 := bstep (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) B303769
theorem B1423493 : Blo 183802 1423493 := bstep (se 4 (by rfl) ⟨133452, by rfl⟩ : syracuseStep 1423493 = 266905) B266905
theorem B276623 : Blo 183802 276623 := bstep (se 1 (by rfl) ⟨207467, by rfl⟩ : syracuseStep 276623 = 414935) B414935
theorem B473273 : Blo 183802 473273 := bstep (se 2 (by rfl) ⟨177477, by rfl⟩ : syracuseStep 473273 = 354955) B354955
theorem B276665 : Blo 183802 276665 := bstep (se 2 (by rfl) ⟨103749, by rfl⟩ : syracuseStep 276665 = 207499) B207499
theorem B702665 : Blo 183802 702665 := bstep (se 2 (by rfl) ⟨263499, by rfl⟩ : syracuseStep 702665 = 526999) B526999
theorem B1784045 : Blo 183802 1784045 := bstep (se 3 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 1784045 = 669017) B669017
theorem B276743 : Blo 183802 276743 := bstep (se 1 (by rfl) ⟨207557, by rfl⟩ : syracuseStep 276743 = 415115) B415115
theorem B211207 : Blo 183802 211207 := bstep (se 1 (by rfl) ⟨158405, by rfl⟩ : syracuseStep 211207 = 316811) B316811
theorem B473359 : Blo 183802 473359 := bstep (se 1 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 473359 = 710039) B710039
theorem B276779 : Blo 183802 276779 := bstep (se 1 (by rfl) ⟨207584, by rfl⟩ : syracuseStep 276779 = 415169) B415169
theorem B932147 : Blo 183802 932147 := bstep (se 1 (by rfl) ⟨699110, by rfl⟩ : syracuseStep 932147 = 1398221) B1398221
theorem B276809 : Blo 183802 276809 := bstep (se 2 (by rfl) ⟨103803, by rfl⟩ : syracuseStep 276809 = 207607) B207607
theorem B276923 : Blo 183802 276923 := bstep (se 1 (by rfl) ⟨207692, by rfl⟩ : syracuseStep 276923 = 415385) B415385
theorem B276983 : Blo 183802 276983 := bstep (se 1 (by rfl) ⟨207737, by rfl⟩ : syracuseStep 276983 = 415475) B415475
theorem B277007 : Blo 183802 277007 := bstep (se 1 (by rfl) ⟨207755, by rfl⟩ : syracuseStep 277007 = 415511) B415511
theorem B277049 : Blo 183802 277049 := bstep (se 2 (by rfl) ⟨103893, by rfl⟩ : syracuseStep 277049 = 207787) B207787
theorem B932471 : Blo 183802 932471 := bstep (se 1 (by rfl) ⟨699353, by rfl⟩ : syracuseStep 932471 = 1398707) B1398707
theorem B277127 : Blo 183802 277127 := bstep (se 1 (by rfl) ⟨207845, by rfl⟩ : syracuseStep 277127 = 415691) B415691
theorem B277163 : Blo 183802 277163 := bstep (se 1 (by rfl) ⟨207872, by rfl⟩ : syracuseStep 277163 = 415745) B415745
theorem B277193 : Blo 183802 277193 := bstep (se 2 (by rfl) ⟨103947, by rfl⟩ : syracuseStep 277193 = 207895) B207895
theorem B277307 : Blo 183802 277307 := bstep (se 1 (by rfl) ⟨207980, by rfl⟩ : syracuseStep 277307 = 415961) B415961
theorem B473971 : Blo 183802 473971 := bstep (se 1 (by rfl) ⟨355478, by rfl⟩ : syracuseStep 473971 = 710957) B710957
theorem B277367 : Blo 183802 277367 := bstep (se 1 (by rfl) ⟨208025, by rfl⟩ : syracuseStep 277367 = 416051) B416051
theorem B277391 : Blo 183802 277391 := bstep (se 1 (by rfl) ⟨208043, by rfl⟩ : syracuseStep 277391 = 416087) B416087
theorem B277433 : Blo 183802 277433 := bstep (se 2 (by rfl) ⟨104037, by rfl⟩ : syracuseStep 277433 = 208075) B208075
theorem B474113 : Blo 183802 474113 := bstep (se 2 (by rfl) ⟨177792, by rfl⟩ : syracuseStep 474113 = 355585) B355585
theorem B277511 : Blo 183802 277511 := bstep (se 1 (by rfl) ⟨208133, by rfl⟩ : syracuseStep 277511 = 416267) B416267
theorem B277547 : Blo 183802 277547 := bstep (se 1 (by rfl) ⟨208160, by rfl⟩ : syracuseStep 277547 = 416321) B416321
theorem B310331 : Blo 183802 310331 := bstep (se 1 (by rfl) ⟨232748, by rfl⟩ : syracuseStep 310331 = 465497) B465497
theorem B277577 : Blo 183802 277577 := bstep (se 2 (by rfl) ⟨104091, by rfl⟩ : syracuseStep 277577 = 208183) B208183
theorem B1195181 : Blo 183802 1195181 := bstep (se 3 (by rfl) ⟨224096, by rfl⟩ : syracuseStep 1195181 = 448193) B448193
theorem B277691 : Blo 183802 277691 := bstep (se 1 (by rfl) ⟨208268, by rfl⟩ : syracuseStep 277691 = 416537) B416537
theorem B277751 : Blo 183802 277751 := bstep (se 1 (by rfl) ⟨208313, by rfl⟩ : syracuseStep 277751 = 416627) B416627
theorem B277775 : Blo 183802 277775 := bstep (se 1 (by rfl) ⟨208331, by rfl⟩ : syracuseStep 277775 = 416663) B416663
theorem B507179 : Blo 183802 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B277817 : Blo 183802 277817 := bstep (se 2 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 277817 = 208363) B208363
theorem B441715 : Blo 183802 441715 := bstep (se 1 (by rfl) ⟨331286, by rfl⟩ : syracuseStep 441715 = 662573) B662573
theorem B277895 : Blo 183802 277895 := bstep (se 1 (by rfl) ⟨208421, by rfl⟩ : syracuseStep 277895 = 416843) B416843
theorem B277931 : Blo 183802 277931 := bstep (se 1 (by rfl) ⟨208448, by rfl⟩ : syracuseStep 277931 = 416897) B416897
theorem B310729 : Blo 183802 310729 := bstep (se 2 (by rfl) ⟨116523, by rfl⟩ : syracuseStep 310729 = 233047) B233047
theorem B277961 : Blo 183802 277961 := bstep (se 2 (by rfl) ⟨104235, by rfl⟩ : syracuseStep 277961 = 208471) B208471
theorem B376265 : Blo 183802 376265 := bstep (se 2 (by rfl) ⟨141099, by rfl⟩ : syracuseStep 376265 = 282199) B282199
theorem B474569 : Blo 183802 474569 := bstep (se 2 (by rfl) ⟨177963, by rfl⟩ : syracuseStep 474569 = 355927) B355927
theorem B1818065 : Blo 183802 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B278075 : Blo 183802 278075 := bstep (se 1 (by rfl) ⟨208556, by rfl⟩ : syracuseStep 278075 = 417113) B417113
theorem B933443 : Blo 183802 933443 := bstep (se 1 (by rfl) ⟨700082, by rfl⟩ : syracuseStep 933443 = 1400165) B1400165
theorem B278135 : Blo 183802 278135 := bstep (se 1 (by rfl) ⟨208601, by rfl⟩ : syracuseStep 278135 = 417203) B417203
theorem B1588855 : Blo 183802 1588855 := bstep (se 1 (by rfl) ⟨1191641, by rfl⟩ : syracuseStep 1588855 = 2383283) B2383283
theorem B278159 : Blo 183802 278159 := bstep (se 1 (by rfl) ⟨208619, by rfl⟩ : syracuseStep 278159 = 417239) B417239
theorem B278201 : Blo 183802 278201 := bstep (se 2 (by rfl) ⟨104325, by rfl⟩ : syracuseStep 278201 = 208651) B208651
theorem B278279 : Blo 183802 278279 := bstep (se 1 (by rfl) ⟨208709, by rfl⟩ : syracuseStep 278279 = 417419) B417419
theorem B278315 : Blo 183802 278315 := bstep (se 1 (by rfl) ⟨208736, by rfl⟩ : syracuseStep 278315 = 417473) B417473
theorem B474923 : Blo 183802 474923 := bstep (se 1 (by rfl) ⟨356192, by rfl⟩ : syracuseStep 474923 = 712385) B712385
theorem B278345 : Blo 183802 278345 := bstep (se 2 (by rfl) ⟨104379, by rfl⟩ : syracuseStep 278345 = 208759) B208759
theorem B933767 : Blo 183802 933767 := bstep (se 1 (by rfl) ⟨700325, by rfl⟩ : syracuseStep 933767 = 1400651) B1400651
theorem B507833 : Blo 183802 507833 := bstep (se 2 (by rfl) ⟨190437, by rfl⟩ : syracuseStep 507833 = 380875) B380875
theorem B278459 : Blo 183802 278459 := bstep (se 1 (by rfl) ⟨208844, by rfl⟩ : syracuseStep 278459 = 417689) B417689
theorem B999377 : Blo 183802 999377 := bstep (se 2 (by rfl) ⟨374766, by rfl⟩ : syracuseStep 999377 = 749533) B749533
theorem B278519 : Blo 183802 278519 := bstep (se 1 (by rfl) ⟨208889, by rfl⟩ : syracuseStep 278519 = 417779) B417779
theorem B278543 : Blo 183802 278543 := bstep (se 1 (by rfl) ⟨208907, by rfl⟩ : syracuseStep 278543 = 417815) B417815
theorem B278585 : Blo 183802 278585 := bstep (se 2 (by rfl) ⟨104469, by rfl⟩ : syracuseStep 278585 = 208939) B208939
theorem B311431 : Blo 183802 311431 := bstep (se 1 (by rfl) ⟨233573, by rfl⟩ : syracuseStep 311431 = 467147) B467147
theorem B278663 : Blo 183802 278663 := bstep (se 1 (by rfl) ⟨208997, by rfl⟩ : syracuseStep 278663 = 417995) B417995
theorem B278699 : Blo 183802 278699 := bstep (se 1 (by rfl) ⟨209024, by rfl⟩ : syracuseStep 278699 = 418049) B418049
theorem B278729 : Blo 183802 278729 := bstep (se 2 (by rfl) ⟨104523, by rfl⟩ : syracuseStep 278729 = 209047) B209047
theorem B278843 : Blo 183802 278843 := bstep (se 1 (by rfl) ⟨209132, by rfl⟩ : syracuseStep 278843 = 418265) B418265
theorem B672059 : Blo 183802 672059 := bstep (se 1 (by rfl) ⟨504044, by rfl⟩ : syracuseStep 672059 = 1008089) B1008089
theorem B278903 : Blo 183802 278903 := bstep (se 1 (by rfl) ⟨209177, by rfl⟩ : syracuseStep 278903 = 418355) B418355
theorem B377207 : Blo 183802 377207 := bstep (se 1 (by rfl) ⟨282905, by rfl⟩ : syracuseStep 377207 = 565811) B565811
theorem B278927 : Blo 183802 278927 := bstep (se 1 (by rfl) ⟨209195, by rfl⟩ : syracuseStep 278927 = 418391) B418391
theorem B278969 : Blo 183802 278969 := bstep (se 2 (by rfl) ⟨104613, by rfl⟩ : syracuseStep 278969 = 209227) B209227
theorem B1425923 : Blo 183802 1425923 := bstep (se 1 (by rfl) ⟨1069442, by rfl⟩ : syracuseStep 1425923 = 2138885) B2138885
theorem B279047 : Blo 183802 279047 := bstep (se 1 (by rfl) ⟨209285, by rfl⟩ : syracuseStep 279047 = 418571) B418571
theorem B279083 : Blo 183802 279083 := bstep (se 1 (by rfl) ⟨209312, by rfl⟩ : syracuseStep 279083 = 418625) B418625
theorem B279113 : Blo 183802 279113 := bstep (se 2 (by rfl) ⟨104667, by rfl⟩ : syracuseStep 279113 = 209335) B209335
theorem B279227 : Blo 183802 279227 := bstep (se 1 (by rfl) ⟨209420, by rfl⟩ : syracuseStep 279227 = 418841) B418841
theorem B279287 : Blo 183802 279287 := bstep (se 1 (by rfl) ⟨209465, by rfl⟩ : syracuseStep 279287 = 418931) B418931
theorem B312079 : Blo 183802 312079 := bstep (se 1 (by rfl) ⟨234059, by rfl⟩ : syracuseStep 312079 = 468119) B468119
theorem B279311 : Blo 183802 279311 := bstep (se 1 (by rfl) ⟨209483, by rfl⟩ : syracuseStep 279311 = 418967) B418967
theorem B2016049 : Blo 183802 2016049 := bstep (se 2 (by rfl) ⟨756018, by rfl⟩ : syracuseStep 2016049 = 1512037) B1512037
theorem B279353 : Blo 183802 279353 := bstep (se 2 (by rfl) ⟨104757, by rfl⟩ : syracuseStep 279353 = 209515) B209515
theorem B279431 : Blo 183802 279431 := bstep (se 1 (by rfl) ⟨209573, by rfl⟩ : syracuseStep 279431 = 419147) B419147
theorem B279467 : Blo 183802 279467 := bstep (se 1 (by rfl) ⟨209600, by rfl⟩ : syracuseStep 279467 = 419201) B419201
theorem B279497 : Blo 183802 279497 := bstep (se 2 (by rfl) ⟨104811, by rfl⟩ : syracuseStep 279497 = 209623) B209623
theorem B443407 : Blo 183802 443407 := bstep (se 1 (by rfl) ⟨332555, by rfl⟩ : syracuseStep 443407 = 665111) B665111
theorem B279611 : Blo 183802 279611 := bstep (se 1 (by rfl) ⟨209708, by rfl⟩ : syracuseStep 279611 = 419417) B419417
theorem B279671 : Blo 183802 279671 := bstep (se 1 (by rfl) ⟨209753, by rfl⟩ : syracuseStep 279671 = 419507) B419507
theorem B279695 : Blo 183802 279695 := bstep (se 1 (by rfl) ⟨209771, by rfl⟩ : syracuseStep 279695 = 419543) B419543
theorem B279737 : Blo 183802 279737 := bstep (se 2 (by rfl) ⟨104901, by rfl⟩ : syracuseStep 279737 = 209803) B209803
theorem B705793 : Blo 183802 705793 := bstep (se 2 (by rfl) ⟨264672, by rfl⟩ : syracuseStep 705793 = 529345) B529345
theorem B279815 : Blo 183802 279815 := bstep (se 1 (by rfl) ⟨209861, by rfl⟩ : syracuseStep 279815 = 419723) B419723
theorem B312619 : Blo 183802 312619 := bstep (se 1 (by rfl) ⟨234464, by rfl⟩ : syracuseStep 312619 = 468929) B468929
theorem B279851 : Blo 183802 279851 := bstep (se 1 (by rfl) ⟨209888, by rfl⟩ : syracuseStep 279851 = 419777) B419777
theorem B279881 : Blo 183802 279881 := bstep (se 2 (by rfl) ⟨104955, by rfl⟩ : syracuseStep 279881 = 209911) B209911
theorem B312761 : Blo 183802 312761 := bstep (se 2 (by rfl) ⟨117285, by rfl⟩ : syracuseStep 312761 = 234571) B234571
theorem B279995 : Blo 183802 279995 := bstep (se 1 (by rfl) ⟨209996, by rfl⟩ : syracuseStep 279995 = 419993) B419993
theorem B280055 : Blo 183802 280055 := bstep (se 1 (by rfl) ⟨210041, by rfl⟩ : syracuseStep 280055 = 420083) B420083
theorem B280079 : Blo 183802 280079 := bstep (se 1 (by rfl) ⟨210059, by rfl⟩ : syracuseStep 280079 = 420119) B420119
theorem B476705 : Blo 183802 476705 := bstep (se 2 (by rfl) ⟨178764, by rfl⟩ : syracuseStep 476705 = 357529) B357529
theorem B280121 : Blo 183802 280121 := bstep (se 2 (by rfl) ⟨105045, by rfl⟩ : syracuseStep 280121 = 210091) B210091
theorem B280199 : Blo 183802 280199 := bstep (se 1 (by rfl) ⟨210149, by rfl⟩ : syracuseStep 280199 = 420299) B420299
theorem B280235 : Blo 183802 280235 := bstep (se 1 (by rfl) ⟨210176, by rfl⟩ : syracuseStep 280235 = 420353) B420353
theorem B378553 : Blo 183802 378553 := bstep (se 2 (by rfl) ⟨141957, by rfl⟩ : syracuseStep 378553 = 283915) B283915
theorem B280265 : Blo 183802 280265 := bstep (se 2 (by rfl) ⟨105099, by rfl⟩ : syracuseStep 280265 = 210199) B210199
theorem B280379 : Blo 183802 280379 := bstep (se 1 (by rfl) ⟨210284, by rfl⟩ : syracuseStep 280379 = 420569) B420569
theorem B4474693 : Blo 183802 4474693 := bstep (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) B839005
theorem B280439 : Blo 183802 280439 := bstep (se 1 (by rfl) ⟨210329, by rfl⟩ : syracuseStep 280439 = 420659) B420659
theorem B280463 : Blo 183802 280463 := bstep (se 1 (by rfl) ⟨210347, by rfl⟩ : syracuseStep 280463 = 420695) B420695
theorem B280505 : Blo 183802 280505 := bstep (se 2 (by rfl) ⟨105189, by rfl⟩ : syracuseStep 280505 = 210379) B210379
theorem B280583 : Blo 183802 280583 := bstep (se 1 (by rfl) ⟨210437, by rfl⟩ : syracuseStep 280583 = 420875) B420875
theorem B4737041 : Blo 183802 4737041 := bstep (se 2 (by rfl) ⟨1776390, by rfl⟩ : syracuseStep 4737041 = 3552781) B3552781
theorem B280619 : Blo 183802 280619 := bstep (se 1 (by rfl) ⟨210464, by rfl⟩ : syracuseStep 280619 = 420929) B420929
theorem B280649 : Blo 183802 280649 := bstep (se 2 (by rfl) ⟨105243, by rfl⟩ : syracuseStep 280649 = 210487) B210487
theorem B444503 : Blo 183802 444503 := bstep (se 1 (by rfl) ⟨333377, by rfl⟩ : syracuseStep 444503 = 666755) B666755
theorem B313463 : Blo 183802 313463 := bstep (se 1 (by rfl) ⟨235097, by rfl⟩ : syracuseStep 313463 = 470195) B470195
theorem B280763 : Blo 183802 280763 := bstep (se 1 (by rfl) ⟨210572, by rfl⟩ : syracuseStep 280763 = 421145) B421145
theorem B280823 : Blo 183802 280823 := bstep (se 1 (by rfl) ⟨210617, by rfl⟩ : syracuseStep 280823 = 421235) B421235
theorem B280847 : Blo 183802 280847 := bstep (se 1 (by rfl) ⟨210635, by rfl⟩ : syracuseStep 280847 = 421271) B421271
theorem B280889 : Blo 183802 280889 := bstep (se 2 (by rfl) ⟨105333, by rfl⟩ : syracuseStep 280889 = 210667) B210667
theorem B444791 : Blo 183802 444791 := bstep (se 1 (by rfl) ⟨333593, by rfl⟩ : syracuseStep 444791 = 667187) B667187
theorem B280967 : Blo 183802 280967 := bstep (se 1 (by rfl) ⟨210725, by rfl⟩ : syracuseStep 280967 = 421451) B421451
theorem B1067417 : Blo 183802 1067417 := bstep (se 2 (by rfl) ⟨400281, by rfl⟩ : syracuseStep 1067417 = 800563) B800563
theorem B281003 : Blo 183802 281003 := bstep (se 1 (by rfl) ⟨210752, by rfl⟩ : syracuseStep 281003 = 421505) B421505
theorem B641465 : Blo 183802 641465 := bstep (se 2 (by rfl) ⟨240549, by rfl⟩ : syracuseStep 641465 = 481099) B481099
theorem B281033 : Blo 183802 281033 := bstep (se 2 (by rfl) ⟨105387, by rfl⟩ : syracuseStep 281033 = 210775) B210775
theorem B313915 : Blo 183802 313915 := bstep (se 1 (by rfl) ⟨235436, by rfl⟩ : syracuseStep 313915 = 470873) B470873
theorem B281147 : Blo 183802 281147 := bstep (se 1 (by rfl) ⟨210860, by rfl⟩ : syracuseStep 281147 = 421721) B421721
theorem B281207 : Blo 183802 281207 := bstep (se 1 (by rfl) ⟨210905, by rfl⟩ : syracuseStep 281207 = 421811) B421811
theorem B281231 : Blo 183802 281231 := bstep (se 1 (by rfl) ⟨210923, by rfl⟩ : syracuseStep 281231 = 421847) B421847
theorem B281273 : Blo 183802 281273 := bstep (se 2 (by rfl) ⟨105477, by rfl⟩ : syracuseStep 281273 = 210955) B210955
theorem B314057 : Blo 183802 314057 := bstep (se 2 (by rfl) ⟨117771, by rfl⟩ : syracuseStep 314057 = 235543) B235543
theorem B281351 : Blo 183802 281351 := bstep (se 1 (by rfl) ⟨211013, by rfl⟩ : syracuseStep 281351 = 422027) B422027
theorem B281387 : Blo 183802 281387 := bstep (se 1 (by rfl) ⟨211040, by rfl⟩ : syracuseStep 281387 = 422081) B422081
theorem B281417 : Blo 183802 281417 := bstep (se 2 (by rfl) ⟨105531, by rfl⟩ : syracuseStep 281417 = 211063) B211063
theorem B281531 : Blo 183802 281531 := bstep (se 1 (by rfl) ⟨211148, by rfl⟩ : syracuseStep 281531 = 422297) B422297
theorem B281591 : Blo 183802 281591 := bstep (se 1 (by rfl) ⟨211193, by rfl⟩ : syracuseStep 281591 = 422387) B422387
theorem B281615 : Blo 183802 281615 := bstep (se 1 (by rfl) ⟨211211, by rfl⟩ : syracuseStep 281615 = 422423) B422423
theorem B281657 : Blo 183802 281657 := bstep (se 2 (by rfl) ⟨105621, by rfl⟩ : syracuseStep 281657 = 211243) B211243
theorem B937331 : Blo 183802 937331 := bstep (se 1 (by rfl) ⟨702998, by rfl⟩ : syracuseStep 937331 = 1405997) B1405997
theorem B314759 : Blo 183802 314759 := bstep (se 1 (by rfl) ⟨236069, by rfl⟩ : syracuseStep 314759 = 472139) B472139
theorem B183815 : Blo 183802 183815 := bstep (se 1 (by rfl) ⟨137861, by rfl⟩ : syracuseStep 183815 = 275723) B275723
theorem B183823 : Blo 183802 183823 := bstep (se 1 (by rfl) ⟨137867, by rfl⟩ : syracuseStep 183823 = 275735) B275735
theorem B183867 : Blo 183802 183867 := bstep (se 1 (by rfl) ⟨137900, by rfl⟩ : syracuseStep 183867 = 275801) B275801
theorem B183943 : Blo 183802 183943 := bstep (se 1 (by rfl) ⟨137957, by rfl⟩ : syracuseStep 183943 = 275915) B275915
theorem B183951 : Blo 183802 183951 := bstep (se 1 (by rfl) ⟨137963, by rfl⟩ : syracuseStep 183951 = 275927) B275927
theorem B183995 : Blo 183802 183995 := bstep (se 1 (by rfl) ⟨137996, by rfl⟩ : syracuseStep 183995 = 275993) B275993
theorem B46157525 : Blo 183802 46157525 := bstep (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) B1081817
theorem B184071 : Blo 183802 184071 := bstep (se 1 (by rfl) ⟨138053, by rfl⟩ : syracuseStep 184071 = 276107) B276107
theorem B184079 : Blo 183802 184079 := bstep (se 1 (by rfl) ⟨138059, by rfl⟩ : syracuseStep 184079 = 276119) B276119
theorem B479009 : Blo 183802 479009 := bstep (se 2 (by rfl) ⟨179628, by rfl⟩ : syracuseStep 479009 = 359257) B359257
theorem B446251 : Blo 183802 446251 := bstep (se 1 (by rfl) ⟨334688, by rfl⟩ : syracuseStep 446251 = 669377) B669377
theorem B184123 : Blo 183802 184123 := bstep (se 1 (by rfl) ⟨138092, by rfl⟩ : syracuseStep 184123 = 276185) B276185
theorem B937817 : Blo 183802 937817 := bstep (se 2 (by rfl) ⟨351681, by rfl⟩ : syracuseStep 937817 = 703363) B703363
theorem B184199 : Blo 183802 184199 := bstep (se 1 (by rfl) ⟨138149, by rfl⟩ : syracuseStep 184199 = 276299) B276299
theorem B184207 : Blo 183802 184207 := bstep (se 1 (by rfl) ⟨138155, by rfl⟩ : syracuseStep 184207 = 276311) B276311
theorem B184251 : Blo 183802 184251 := bstep (se 1 (by rfl) ⟨138188, by rfl⟩ : syracuseStep 184251 = 276377) B276377
theorem B184327 : Blo 183802 184327 := bstep (se 1 (by rfl) ⟨138245, by rfl⟩ : syracuseStep 184327 = 276491) B276491
theorem B413711 : Blo 183802 413711 := bstep (se 1 (by rfl) ⟨310283, by rfl⟩ : syracuseStep 413711 = 620567) B620567
theorem B184335 : Blo 183802 184335 := bstep (se 1 (by rfl) ⟨138251, by rfl⟩ : syracuseStep 184335 = 276503) B276503
theorem B249871 : Blo 183802 249871 := bstep (se 1 (by rfl) ⟨187403, by rfl⟩ : syracuseStep 249871 = 374807) B374807
theorem B315407 : Blo 183802 315407 := bstep (se 1 (by rfl) ⟨236555, by rfl⟩ : syracuseStep 315407 = 473111) B473111
theorem B413729 : Blo 183802 413729 := bstep (se 2 (by rfl) ⟨155148, by rfl⟩ : syracuseStep 413729 = 310297) B310297
theorem B184379 : Blo 183802 184379 := bstep (se 1 (by rfl) ⟨138284, by rfl⟩ : syracuseStep 184379 = 276569) B276569
theorem B1200215 : Blo 183802 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B708695 : Blo 183802 708695 := bstep (se 1 (by rfl) ⟨531521, by rfl⟩ : syracuseStep 708695 = 1063043) B1063043
theorem B184455 : Blo 183802 184455 := bstep (se 1 (by rfl) ⟨138341, by rfl⟩ : syracuseStep 184455 = 276683) B276683
theorem B184463 : Blo 183802 184463 := bstep (se 1 (by rfl) ⟨138347, by rfl⟩ : syracuseStep 184463 = 276695) B276695
theorem B184507 : Blo 183802 184507 := bstep (se 1 (by rfl) ⟨138380, by rfl⟩ : syracuseStep 184507 = 276761) B276761
theorem B184583 : Blo 183802 184583 := bstep (se 1 (by rfl) ⟨138437, by rfl⟩ : syracuseStep 184583 = 276875) B276875
theorem B184591 : Blo 183802 184591 := bstep (se 1 (by rfl) ⟨138443, by rfl⟩ : syracuseStep 184591 = 276887) B276887
theorem B184635 : Blo 183802 184635 := bstep (se 1 (by rfl) ⟨138476, by rfl⟩ : syracuseStep 184635 = 276953) B276953
theorem B414071 : Blo 183802 414071 := bstep (se 1 (by rfl) ⟨310553, by rfl⟩ : syracuseStep 414071 = 621107) B621107
theorem B184711 : Blo 183802 184711 := bstep (se 1 (by rfl) ⟨138533, by rfl⟩ : syracuseStep 184711 = 277067) B277067
theorem B184719 : Blo 183802 184719 := bstep (se 1 (by rfl) ⟨138539, by rfl⟩ : syracuseStep 184719 = 277079) B277079
theorem B1331603 : Blo 183802 1331603 := bstep (se 1 (by rfl) ⟨998702, by rfl⟩ : syracuseStep 1331603 = 1997405) B1997405
theorem B184763 : Blo 183802 184763 := bstep (se 1 (by rfl) ⟨138572, by rfl⟩ : syracuseStep 184763 = 277145) B277145
theorem B184839 : Blo 183802 184839 := bstep (se 1 (by rfl) ⟨138629, by rfl⟩ : syracuseStep 184839 = 277259) B277259
theorem B184847 : Blo 183802 184847 := bstep (se 1 (by rfl) ⟨138635, by rfl⟩ : syracuseStep 184847 = 277271) B277271
theorem B414251 : Blo 183802 414251 := bstep (se 1 (by rfl) ⟨310688, by rfl⟩ : syracuseStep 414251 = 621377) B621377
theorem B315947 : Blo 183802 315947 := bstep (se 1 (by rfl) ⟨236960, by rfl⟩ : syracuseStep 315947 = 473921) B473921
theorem B184891 : Blo 183802 184891 := bstep (se 1 (by rfl) ⟨138668, by rfl⟩ : syracuseStep 184891 = 277337) B277337
theorem B709181 : Blo 183802 709181 := bstep (se 3 (by rfl) ⟨132971, by rfl⟩ : syracuseStep 709181 = 265943) B265943
theorem B676471 : Blo 183802 676471 := bstep (se 1 (by rfl) ⟨507353, by rfl⟩ : syracuseStep 676471 = 1014707) B1014707
theorem B184967 : Blo 183802 184967 := bstep (se 1 (by rfl) ⟨138725, by rfl⟩ : syracuseStep 184967 = 277451) B277451
theorem B184975 : Blo 183802 184975 := bstep (se 1 (by rfl) ⟨138731, by rfl⟩ : syracuseStep 184975 = 277463) B277463
theorem B185019 : Blo 183802 185019 := bstep (se 1 (by rfl) ⟨138764, by rfl⟩ : syracuseStep 185019 = 277529) B277529
theorem B1200869 : Blo 183802 1200869 := bstep (se 4 (by rfl) ⟨112581, by rfl⟩ : syracuseStep 1200869 = 225163) B225163
theorem B185095 : Blo 183802 185095 := bstep (se 1 (by rfl) ⟨138821, by rfl⟩ : syracuseStep 185095 = 277643) B277643
theorem B185103 : Blo 183802 185103 := bstep (se 1 (by rfl) ⟨138827, by rfl⟩ : syracuseStep 185103 = 277655) B277655
theorem B185147 : Blo 183802 185147 := bstep (se 1 (by rfl) ⟨138860, by rfl⟩ : syracuseStep 185147 = 277721) B277721
theorem B185223 : Blo 183802 185223 := bstep (se 1 (by rfl) ⟨138917, by rfl⟩ : syracuseStep 185223 = 277835) B277835
theorem B185231 : Blo 183802 185231 := bstep (se 1 (by rfl) ⟨138923, by rfl⟩ : syracuseStep 185231 = 277847) B277847
theorem B414611 : Blo 183802 414611 := bstep (se 1 (by rfl) ⟨310958, by rfl⟩ : syracuseStep 414611 = 621917) B621917
theorem B807833 : Blo 183802 807833 := bstep (se 2 (by rfl) ⟨302937, by rfl⟩ : syracuseStep 807833 = 605875) B605875
theorem B316345 : Blo 183802 316345 := bstep (se 2 (by rfl) ⟨118629, by rfl⟩ : syracuseStep 316345 = 237259) B237259
theorem B185275 : Blo 183802 185275 := bstep (se 1 (by rfl) ⟨138956, by rfl⟩ : syracuseStep 185275 = 277913) B277913
theorem B414665 : Blo 183802 414665 := bstep (se 2 (by rfl) ⟨155499, by rfl⟩ : syracuseStep 414665 = 310999) B310999
theorem B185351 : Blo 183802 185351 := bstep (se 1 (by rfl) ⟨139013, by rfl⟩ : syracuseStep 185351 = 278027) B278027
theorem B185359 : Blo 183802 185359 := bstep (se 1 (by rfl) ⟨139019, by rfl⟩ : syracuseStep 185359 = 278039) B278039
theorem B185403 : Blo 183802 185403 := bstep (se 1 (by rfl) ⟨139052, by rfl⟩ : syracuseStep 185403 = 278105) B278105
theorem B185479 : Blo 183802 185479 := bstep (se 1 (by rfl) ⟨139109, by rfl⟩ : syracuseStep 185479 = 278219) B278219
theorem B185487 : Blo 183802 185487 := bstep (se 1 (by rfl) ⟨139115, by rfl⟩ : syracuseStep 185487 = 278231) B278231
theorem B447635 : Blo 183802 447635 := bstep (se 1 (by rfl) ⟨335726, by rfl⟩ : syracuseStep 447635 = 671453) B671453
theorem B185531 : Blo 183802 185531 := bstep (se 1 (by rfl) ⟨139148, by rfl⟩ : syracuseStep 185531 = 278297) B278297
theorem B185607 : Blo 183802 185607 := bstep (se 1 (by rfl) ⟨139205, by rfl⟩ : syracuseStep 185607 = 278411) B278411
theorem B185615 : Blo 183802 185615 := bstep (se 1 (by rfl) ⟨139211, by rfl⟩ : syracuseStep 185615 = 278423) B278423
theorem B185659 : Blo 183802 185659 := bstep (se 1 (by rfl) ⟨139244, by rfl⟩ : syracuseStep 185659 = 278489) B278489
theorem B185735 : Blo 183802 185735 := bstep (se 1 (by rfl) ⟨139301, by rfl⟩ : syracuseStep 185735 = 278603) B278603
theorem B185743 : Blo 183802 185743 := bstep (se 1 (by rfl) ⟨139307, by rfl⟩ : syracuseStep 185743 = 278615) B278615
theorem B185787 : Blo 183802 185787 := bstep (se 1 (by rfl) ⟨139340, by rfl⟩ : syracuseStep 185787 = 278681) B278681
theorem B185863 : Blo 183802 185863 := bstep (se 1 (by rfl) ⟨139397, by rfl⟩ : syracuseStep 185863 = 278795) B278795
theorem B185871 : Blo 183802 185871 := bstep (se 1 (by rfl) ⟨139403, by rfl⟩ : syracuseStep 185871 = 278807) B278807
theorem B185915 : Blo 183802 185915 := bstep (se 1 (by rfl) ⟨139436, by rfl⟩ : syracuseStep 185915 = 278873) B278873
theorem B415367 : Blo 183802 415367 := bstep (se 1 (by rfl) ⟨311525, by rfl⟩ : syracuseStep 415367 = 623051) B623051
theorem B185991 : Blo 183802 185991 := bstep (se 1 (by rfl) ⟨139493, by rfl⟩ : syracuseStep 185991 = 278987) B278987
theorem B185999 : Blo 183802 185999 := bstep (se 1 (by rfl) ⟨139499, by rfl⟩ : syracuseStep 185999 = 278999) B278999
theorem B186043 : Blo 183802 186043 := bstep (se 1 (by rfl) ⟨139532, by rfl⟩ : syracuseStep 186043 = 279065) B279065
theorem B186119 : Blo 183802 186119 := bstep (se 1 (by rfl) ⟨139589, by rfl⟩ : syracuseStep 186119 = 279179) B279179
theorem B841487 : Blo 183802 841487 := bstep (se 1 (by rfl) ⟨631115, by rfl⟩ : syracuseStep 841487 = 1262231) B1262231
theorem B186127 : Blo 183802 186127 := bstep (se 1 (by rfl) ⟨139595, by rfl⟩ : syracuseStep 186127 = 279191) B279191
theorem B350011 : Blo 183802 350011 := bstep (se 1 (by rfl) ⟨262508, by rfl⟩ : syracuseStep 350011 = 525017) B525017
theorem B415547 : Blo 183802 415547 := bstep (se 1 (by rfl) ⟨311660, by rfl⟩ : syracuseStep 415547 = 623321) B623321
theorem B186171 : Blo 183802 186171 := bstep (se 1 (by rfl) ⟨139628, by rfl⟩ : syracuseStep 186171 = 279257) B279257
theorem B3200843 : Blo 183802 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B186247 : Blo 183802 186247 := bstep (se 1 (by rfl) ⟨139685, by rfl⟩ : syracuseStep 186247 = 279371) B279371
theorem B186255 : Blo 183802 186255 := bstep (se 1 (by rfl) ⟨139691, by rfl⟩ : syracuseStep 186255 = 279383) B279383
theorem B939923 : Blo 183802 939923 := bstep (se 1 (by rfl) ⟨704942, by rfl⟩ : syracuseStep 939923 = 1409885) B1409885
theorem B415673 : Blo 183802 415673 := bstep (se 2 (by rfl) ⟨155877, by rfl⟩ : syracuseStep 415673 = 311755) B311755
theorem B186299 : Blo 183802 186299 := bstep (se 1 (by rfl) ⟨139724, by rfl⟩ : syracuseStep 186299 = 279449) B279449
theorem B186375 : Blo 183802 186375 := bstep (se 1 (by rfl) ⟨139781, by rfl⟩ : syracuseStep 186375 = 279563) B279563
theorem B186383 : Blo 183802 186383 := bstep (se 1 (by rfl) ⟨139787, by rfl⟩ : syracuseStep 186383 = 279575) B279575
theorem B251947 : Blo 183802 251947 := bstep (se 1 (by rfl) ⟨188960, by rfl⟩ : syracuseStep 251947 = 377921) B377921
theorem B186427 : Blo 183802 186427 := bstep (se 1 (by rfl) ⟨139820, by rfl⟩ : syracuseStep 186427 = 279641) B279641
theorem B186503 : Blo 183802 186503 := bstep (se 1 (by rfl) ⟨139877, by rfl⟩ : syracuseStep 186503 = 279755) B279755
theorem B186511 : Blo 183802 186511 := bstep (se 1 (by rfl) ⟨139883, by rfl⟩ : syracuseStep 186511 = 279767) B279767
theorem B186555 : Blo 183802 186555 := bstep (se 1 (by rfl) ⟨139916, by rfl⟩ : syracuseStep 186555 = 279833) B279833
theorem B2840777 : Blo 183802 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B186631 : Blo 183802 186631 := bstep (se 1 (by rfl) ⟨139973, by rfl⟩ : syracuseStep 186631 = 279947) B279947
theorem B416015 : Blo 183802 416015 := bstep (se 1 (by rfl) ⟨312011, by rfl⟩ : syracuseStep 416015 = 624023) B624023
theorem B186639 : Blo 183802 186639 := bstep (se 1 (by rfl) ⟨139979, by rfl⟩ : syracuseStep 186639 = 279959) B279959
theorem B710927 : Blo 183802 710927 := bstep (se 1 (by rfl) ⟨533195, by rfl⟩ : syracuseStep 710927 = 1066391) B1066391
theorem B350497 : Blo 183802 350497 := bstep (se 2 (by rfl) ⟨131436, by rfl⟩ : syracuseStep 350497 = 262873) B262873
theorem B416033 : Blo 183802 416033 := bstep (se 2 (by rfl) ⟨156012, by rfl⟩ : syracuseStep 416033 = 312025) B312025
theorem B186683 : Blo 183802 186683 := bstep (se 1 (by rfl) ⟨140012, by rfl⟩ : syracuseStep 186683 = 280025) B280025
theorem B186759 : Blo 183802 186759 := bstep (se 1 (by rfl) ⟨140069, by rfl⟩ : syracuseStep 186759 = 280139) B280139
theorem B186767 : Blo 183802 186767 := bstep (se 1 (by rfl) ⟨140075, by rfl⟩ : syracuseStep 186767 = 280151) B280151
theorem B186811 : Blo 183802 186811 := bstep (se 1 (by rfl) ⟨140108, by rfl⟩ : syracuseStep 186811 = 280217) B280217
theorem B186887 : Blo 183802 186887 := bstep (se 1 (by rfl) ⟨140165, by rfl⟩ : syracuseStep 186887 = 280331) B280331
theorem B186895 : Blo 183802 186895 := bstep (se 1 (by rfl) ⟨140171, by rfl⟩ : syracuseStep 186895 = 280343) B280343
theorem B186939 : Blo 183802 186939 := bstep (se 1 (by rfl) ⟨140204, by rfl⟩ : syracuseStep 186939 = 280409) B280409
theorem B416375 : Blo 183802 416375 := bstep (se 1 (by rfl) ⟨312281, by rfl⟩ : syracuseStep 416375 = 624563) B624563
theorem B187015 : Blo 183802 187015 := bstep (se 1 (by rfl) ⟨140261, by rfl⟩ : syracuseStep 187015 = 280523) B280523
theorem B187023 : Blo 183802 187023 := bstep (se 1 (by rfl) ⟨140267, by rfl⟩ : syracuseStep 187023 = 280535) B280535
theorem B383635 : Blo 183802 383635 := bstep (se 1 (by rfl) ⟨287726, by rfl⟩ : syracuseStep 383635 = 575453) B575453
theorem B187067 : Blo 183802 187067 := bstep (se 1 (by rfl) ⟨140300, by rfl⟩ : syracuseStep 187067 = 280601) B280601
theorem B187143 : Blo 183802 187143 := bstep (se 1 (by rfl) ⟨140357, by rfl⟩ : syracuseStep 187143 = 280715) B280715
theorem B187151 : Blo 183802 187151 := bstep (se 1 (by rfl) ⟨140363, by rfl⟩ : syracuseStep 187151 = 280727) B280727
theorem B416555 : Blo 183802 416555 := bstep (se 1 (by rfl) ⟨312416, by rfl⟩ : syracuseStep 416555 = 624833) B624833
theorem B252715 : Blo 183802 252715 := bstep (se 1 (by rfl) ⟨189536, by rfl⟩ : syracuseStep 252715 = 379073) B379073
theorem B187195 : Blo 183802 187195 := bstep (se 1 (by rfl) ⟨140396, by rfl⟩ : syracuseStep 187195 = 280793) B280793
theorem B187271 : Blo 183802 187271 := bstep (se 1 (by rfl) ⟨140453, by rfl⟩ : syracuseStep 187271 = 280907) B280907
theorem B187279 : Blo 183802 187279 := bstep (se 1 (by rfl) ⟨140459, by rfl⟩ : syracuseStep 187279 = 280919) B280919
theorem B187323 : Blo 183802 187323 := bstep (se 1 (by rfl) ⟨140492, by rfl⟩ : syracuseStep 187323 = 280985) B280985
theorem B252919 : Blo 183802 252919 := bstep (se 1 (by rfl) ⟨189689, by rfl⟩ : syracuseStep 252919 = 379379) B379379
theorem B187399 : Blo 183802 187399 := bstep (se 1 (by rfl) ⟨140549, by rfl⟩ : syracuseStep 187399 = 281099) B281099
theorem B187407 : Blo 183802 187407 := bstep (se 1 (by rfl) ⟨140555, by rfl⟩ : syracuseStep 187407 = 281111) B281111
theorem B187451 : Blo 183802 187451 := bstep (se 1 (by rfl) ⟨140588, by rfl⟩ : syracuseStep 187451 = 281177) B281177
theorem B187527 : Blo 183802 187527 := bstep (se 1 (by rfl) ⟨140645, by rfl⟩ : syracuseStep 187527 = 281291) B281291
theorem B187535 : Blo 183802 187535 := bstep (se 1 (by rfl) ⟨140651, by rfl⟩ : syracuseStep 187535 = 281303) B281303
theorem B416915 : Blo 183802 416915 := bstep (se 1 (by rfl) ⟨312686, by rfl⟩ : syracuseStep 416915 = 625373) B625373
theorem B187579 : Blo 183802 187579 := bstep (se 1 (by rfl) ⟨140684, by rfl⟩ : syracuseStep 187579 = 281369) B281369
theorem B416969 : Blo 183802 416969 := bstep (se 2 (by rfl) ⟨156363, by rfl⟩ : syracuseStep 416969 = 312727) B312727
theorem B7625933 : Blo 183802 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B187655 : Blo 183802 187655 := bstep (se 1 (by rfl) ⟨140741, by rfl⟩ : syracuseStep 187655 = 281483) B281483
theorem B187663 : Blo 183802 187663 := bstep (se 1 (by rfl) ⟨140747, by rfl⟩ : syracuseStep 187663 = 281495) B281495
theorem B187707 : Blo 183802 187707 := bstep (se 1 (by rfl) ⟨140780, by rfl⟩ : syracuseStep 187707 = 281561) B281561
theorem B1334663 : Blo 183802 1334663 := bstep (se 1 (by rfl) ⟨1000997, by rfl⟩ : syracuseStep 1334663 = 2001995) B2001995
theorem B187783 : Blo 183802 187783 := bstep (se 1 (by rfl) ⟨140837, by rfl⟩ : syracuseStep 187783 = 281675) B281675
theorem B187791 : Blo 183802 187791 := bstep (se 1 (by rfl) ⟨140843, by rfl⟩ : syracuseStep 187791 = 281687) B281687
theorem B351803 : Blo 183802 351803 := bstep (se 1 (by rfl) ⟨263852, by rfl⟩ : syracuseStep 351803 = 527705) B527705
theorem B417671 : Blo 183802 417671 := bstep (se 1 (by rfl) ⟨313253, by rfl⟩ : syracuseStep 417671 = 626507) B626507
theorem B712583 : Blo 183802 712583 := bstep (se 1 (by rfl) ⟨534437, by rfl⟩ : syracuseStep 712583 = 1068875) B1068875
theorem B1794059 : Blo 183802 1794059 := bstep (se 1 (by rfl) ⟨1345544, by rfl⟩ : syracuseStep 1794059 = 2691089) B2691089
theorem B352289 : Blo 183802 352289 := bstep (se 2 (by rfl) ⟨132108, by rfl⟩ : syracuseStep 352289 = 264217) B264217
theorem B417851 : Blo 183802 417851 := bstep (se 1 (by rfl) ⟨313388, by rfl⟩ : syracuseStep 417851 = 626777) B626777
theorem B352441 : Blo 183802 352441 := bstep (se 2 (by rfl) ⟨132165, by rfl⟩ : syracuseStep 352441 = 264331) B264331
theorem B417977 : Blo 183802 417977 := bstep (se 2 (by rfl) ⟨156741, by rfl⟩ : syracuseStep 417977 = 313483) B313483
theorem B1007873 : Blo 183802 1007873 := bstep (se 2 (by rfl) ⟨377952, by rfl⟩ : syracuseStep 1007873 = 755905) B755905
theorem B418319 : Blo 183802 418319 := bstep (se 1 (by rfl) ⟨313739, by rfl⟩ : syracuseStep 418319 = 627479) B627479
theorem B418337 : Blo 183802 418337 := bstep (se 2 (by rfl) ⟨156876, by rfl⟩ : syracuseStep 418337 = 313753) B313753
theorem B680737 : Blo 183802 680737 := bstep (se 2 (by rfl) ⟨255276, by rfl⟩ : syracuseStep 680737 = 510553) B510553
theorem B418679 : Blo 183802 418679 := bstep (se 1 (by rfl) ⟨314009, by rfl⟩ : syracuseStep 418679 = 628019) B628019
theorem B943001 : Blo 183802 943001 := bstep (se 2 (by rfl) ⟨353625, by rfl⟩ : syracuseStep 943001 = 707251) B707251
theorem B418859 : Blo 183802 418859 := bstep (se 1 (by rfl) ⟨314144, by rfl⟩ : syracuseStep 418859 = 628289) B628289
theorem B910529 : Blo 183802 910529 := bstep (se 2 (by rfl) ⟨341448, by rfl⟩ : syracuseStep 910529 = 682897) B682897
theorem B1795459 : Blo 183802 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B2385287 : Blo 183802 2385287 := bstep (se 1 (by rfl) ⟨1788965, by rfl⟩ : syracuseStep 2385287 = 3577931) B3577931
theorem B419219 : Blo 183802 419219 := bstep (se 1 (by rfl) ⟨314414, by rfl⟩ : syracuseStep 419219 = 628829) B628829
theorem B419273 : Blo 183802 419273 := bstep (se 2 (by rfl) ⟨157227, by rfl⟩ : syracuseStep 419273 = 314455) B314455
theorem B1075079 : Blo 183802 1075079 := bstep (se 1 (by rfl) ⟨806309, by rfl⟩ : syracuseStep 1075079 = 1612619) B1612619
theorem B354233 : Blo 183802 354233 := bstep (se 2 (by rfl) ⟨132837, by rfl⟩ : syracuseStep 354233 = 265675) B265675
theorem B419975 : Blo 183802 419975 := bstep (se 1 (by rfl) ⟨314981, by rfl⟩ : syracuseStep 419975 = 629963) B629963
theorem B1403081 : Blo 183802 1403081 := bstep (se 2 (by rfl) ⟨526155, by rfl⟩ : syracuseStep 1403081 = 1052311) B1052311
theorem B420155 : Blo 183802 420155 := bstep (se 1 (by rfl) ⟨315116, by rfl⟩ : syracuseStep 420155 = 630233) B630233
theorem B420281 : Blo 183802 420281 := bstep (se 2 (by rfl) ⟨157605, by rfl⟩ : syracuseStep 420281 = 315211) B315211
theorem B420623 : Blo 183802 420623 := bstep (se 1 (by rfl) ⟨315467, by rfl⟩ : syracuseStep 420623 = 630935) B630935
theorem B420641 : Blo 183802 420641 := bstep (se 2 (by rfl) ⟨157740, by rfl⟩ : syracuseStep 420641 = 315481) B315481
theorem B420983 : Blo 183802 420983 := bstep (se 1 (by rfl) ⟨315737, by rfl⟩ : syracuseStep 420983 = 631475) B631475
theorem B453899 : Blo 183802 453899 := bstep (se 1 (by rfl) ⟨340424, by rfl⟩ : syracuseStep 453899 = 680849) B680849
theorem B421163 : Blo 183802 421163 := bstep (se 1 (by rfl) ⟨315872, by rfl⟩ : syracuseStep 421163 = 631745) B631745
theorem B945593 : Blo 183802 945593 := bstep (se 2 (by rfl) ⟨354597, by rfl⟩ : syracuseStep 945593 = 709195) B709195
theorem B421523 : Blo 183802 421523 := bstep (se 1 (by rfl) ⟨316142, by rfl⟩ : syracuseStep 421523 = 632285) B632285
theorem B421577 : Blo 183802 421577 := bstep (se 2 (by rfl) ⟨158091, by rfl⟩ : syracuseStep 421577 = 316183) B316183
theorem B4321073 : Blo 183802 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B356231 : Blo 183802 356231 := bstep (se 1 (by rfl) ⟨267173, by rfl⟩ : syracuseStep 356231 = 534347) B534347
theorem B422023 : Blo 183802 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B422279 : Blo 183802 422279 := bstep (se 1 (by rfl) ⟨316709, by rfl⟩ : syracuseStep 422279 = 633419) B633419
theorem B1601977 : Blo 183802 1601977 := bstep (se 2 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 1601977 = 1201483) B1201483
theorem B422459 : Blo 183802 422459 := bstep (se 1 (by rfl) ⟨316844, by rfl⟩ : syracuseStep 422459 = 633689) B633689
theorem B2093687 : Blo 183802 2093687 := bstep (se 1 (by rfl) ⟨1570265, by rfl⟩ : syracuseStep 2093687 = 3140531) B3140531
theorem B1340023 : Blo 183802 1340023 := bstep (se 1 (by rfl) ⟨1005017, by rfl⟩ : syracuseStep 1340023 = 2010035) B2010035
theorem B946889 : Blo 183802 946889 := bstep (se 2 (by rfl) ⟨355083, by rfl⟩ : syracuseStep 946889 = 710167) B710167
theorem B1078049 : Blo 183802 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B848825 : Blo 183802 848825 := bstep (se 2 (by rfl) ⟨318309, by rfl⟩ : syracuseStep 848825 = 636619) B636619
theorem B422927 : Blo 183802 422927 := bstep (se 1 (by rfl) ⟨317195, by rfl⟩ : syracuseStep 422927 = 634391) B634391
theorem B259471 : Blo 183802 259471 := bstep (se 1 (by rfl) ⟨194603, by rfl⟩ : syracuseStep 259471 = 389207) B389207
theorem B13694993 : Blo 183802 13694993 := bstep (se 2 (by rfl) ⟨5135622, by rfl⟩ : syracuseStep 13694993 = 10271245) B10271245
theorem B1047005 : Blo 183802 1047005 := bstep (se 3 (by rfl) ⟨196313, by rfl⟩ : syracuseStep 1047005 = 392627) B392627
theorem B1079837 : Blo 183802 1079837 := bstep (se 3 (by rfl) ⟨202469, by rfl⟩ : syracuseStep 1079837 = 404939) B404939
theorem B1571633 : Blo 183802 1571633 := bstep (se 2 (by rfl) ⟨589362, by rfl⟩ : syracuseStep 1571633 = 1178725) B1178725
theorem B883507 : Blo 183802 883507 := bstep (se 1 (by rfl) ⟨662630, by rfl⟩ : syracuseStep 883507 = 1325261) B1325261
theorem B884027 : Blo 183802 884027 := bstep (se 1 (by rfl) ⟨663020, by rfl⟩ : syracuseStep 884027 = 1326041) B1326041
theorem B621971 : Blo 183802 621971 := bstep (se 1 (by rfl) ⟨466478, by rfl⟩ : syracuseStep 621971 = 932957) B932957
theorem B1572317 : Blo 183802 1572317 := bstep (se 3 (by rfl) ⟨294809, by rfl⟩ : syracuseStep 1572317 = 589619) B589619
theorem B1572941 : Blo 183802 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B1441955 : Blo 183802 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B950615 : Blo 183802 950615 := bstep (se 1 (by rfl) ⟨712961, by rfl⟩ : syracuseStep 950615 = 1425923) B1425923
theorem B787457 : Blo 183802 787457 := bstep (se 2 (by rfl) ⟨295296, by rfl⟩ : syracuseStep 787457 = 590593) B590593
theorem B15205427 : Blo 183802 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B2688065 : Blo 183802 2688065 := bstep (se 2 (by rfl) ⟨1008024, by rfl⟩ : syracuseStep 2688065 = 2016049) B2016049
theorem B591209 : Blo 183802 591209 := bstep (se 2 (by rfl) ⟨221703, by rfl⟩ : syracuseStep 591209 = 443407) B443407
theorem B296335 : Blo 183802 296335 := bstep (se 1 (by rfl) ⟨222251, by rfl⟩ : syracuseStep 296335 = 444503) B444503
theorem B3409451 : Blo 183802 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B296527 : Blo 183802 296527 := bstep (se 1 (by rfl) ⟨222395, by rfl⟩ : syracuseStep 296527 = 444791) B444791
theorem B427643 : Blo 183802 427643 := bstep (se 1 (by rfl) ⟨320732, by rfl⟩ : syracuseStep 427643 = 641465) B641465
theorem B394951 : Blo 183802 394951 := bstep (se 1 (by rfl) ⟨296213, by rfl⟩ : syracuseStep 394951 = 592427) B592427
theorem B2393945 : Blo 183802 2393945 := bstep (se 2 (by rfl) ⟨897729, by rfl⟩ : syracuseStep 2393945 = 1795459) B1795459
theorem B1181699 : Blo 183802 1181699 := bstep (se 1 (by rfl) ⟨886274, by rfl⟩ : syracuseStep 1181699 = 1772549) B1772549
theorem B624887 : Blo 183802 624887 := bstep (se 1 (by rfl) ⟨468665, by rfl⟩ : syracuseStep 624887 = 937331) B937331
theorem B5966257 : Blo 183802 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B30771683 : Blo 183802 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B625211 : Blo 183802 625211 := bstep (se 1 (by rfl) ⟨468908, by rfl⟩ : syracuseStep 625211 = 937817) B937817
theorem B625481 : Blo 183802 625481 := bstep (se 2 (by rfl) ⟨234555, by rfl⟩ : syracuseStep 625481 = 469111) B469111
theorem B4295501 : Blo 183802 4295501 := bstep (se 3 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 4295501 = 1610813) B1610813
theorem B887735 : Blo 183802 887735 := bstep (se 1 (by rfl) ⟨665801, by rfl⟩ : syracuseStep 887735 = 1331603) B1331603
theorem B462071 : Blo 183802 462071 := bstep (se 1 (by rfl) ⟨346553, by rfl⟩ : syracuseStep 462071 = 693107) B693107
theorem B298423 : Blo 183802 298423 := bstep (se 1 (by rfl) ⟨223817, by rfl⟩ : syracuseStep 298423 = 447635) B447635
theorem B855539 : Blo 183802 855539 := bstep (se 1 (by rfl) ⟨641654, by rfl⟩ : syracuseStep 855539 = 1283309) B1283309
theorem B396839 : Blo 183802 396839 := bstep (se 1 (by rfl) ⟨297629, by rfl⟩ : syracuseStep 396839 = 595259) B595259
theorem B397163 : Blo 183802 397163 := bstep (se 1 (by rfl) ⟨297872, by rfl⟩ : syracuseStep 397163 = 595745) B595745
theorem B626615 : Blo 183802 626615 := bstep (se 1 (by rfl) ⟨469961, by rfl⟩ : syracuseStep 626615 = 939923) B939923
theorem B1773899 : Blo 183802 1773899 := bstep (se 1 (by rfl) ⟨1330424, by rfl⟩ : syracuseStep 1773899 = 2660849) B2660849
theorem B627209 : Blo 183802 627209 := bstep (se 2 (by rfl) ⟨235203, by rfl⟩ : syracuseStep 627209 = 470407) B470407
theorem B5083955 : Blo 183802 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B889775 : Blo 183802 889775 := bstep (se 1 (by rfl) ⟨667331, by rfl⟩ : syracuseStep 889775 = 1334663) B1334663
theorem B595001 : Blo 183802 595001 := bstep (se 2 (by rfl) ⟨223125, by rfl⟩ : syracuseStep 595001 = 446251) B446251
theorem B1348901 : Blo 183802 1348901 := bstep (se 4 (by rfl) ⟨126459, by rfl⟩ : syracuseStep 1348901 = 252919) B252919
theorem B333161 : Blo 183802 333161 := bstep (se 2 (by rfl) ⟨124935, by rfl⟩ : syracuseStep 333161 = 249871) B249871
theorem B628073 : Blo 183802 628073 := bstep (se 2 (by rfl) ⟨235527, by rfl⟩ : syracuseStep 628073 = 471055) B471055
theorem B1119653 : Blo 183802 1119653 := bstep (se 4 (by rfl) ⟨104967, by rfl⟩ : syracuseStep 1119653 = 209935) B209935
theorem B562697 : Blo 183802 562697 := bstep (se 2 (by rfl) ⟨211011, by rfl⟩ : syracuseStep 562697 = 422023) B422023
theorem B2135969 : Blo 183802 2135969 := bstep (se 2 (by rfl) ⟨800988, by rfl⟩ : syracuseStep 2135969 = 1601977) B1601977
theorem B628667 : Blo 183802 628667 := bstep (se 1 (by rfl) ⟨471500, by rfl⟩ : syracuseStep 628667 = 943001) B943001
theorem B1185799 : Blo 183802 1185799 := bstep (se 1 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 1185799 = 1778699) B1778699
theorem B1054727 : Blo 183802 1054727 := bstep (se 1 (by rfl) ⟨791045, by rfl⟩ : syracuseStep 1054727 = 1582091) B1582091
theorem B399367 : Blo 183802 399367 := bstep (se 1 (by rfl) ⟨299525, by rfl⟩ : syracuseStep 399367 = 599051) B599051
theorem B334343 : Blo 183802 334343 := bstep (se 1 (by rfl) ⟨250757, by rfl⟩ : syracuseStep 334343 = 501515) B501515
theorem B793097 : Blo 183802 793097 := bstep (se 2 (by rfl) ⟨297411, by rfl⟩ : syracuseStep 793097 = 594823) B594823
theorem B891425 : Blo 183802 891425 := bstep (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) B668569
theorem B334415 : Blo 183802 334415 := bstep (se 1 (by rfl) ⟨250811, by rfl⟩ : syracuseStep 334415 = 501623) B501623
theorem B465547 : Blo 183802 465547 := bstep (se 1 (by rfl) ⟨349160, by rfl⟩ : syracuseStep 465547 = 698321) B698321
theorem B465851 : Blo 183802 465851 := bstep (se 1 (by rfl) ⟨349388, by rfl⟩ : syracuseStep 465851 = 698777) B698777
theorem B400555 : Blo 183802 400555 := bstep (se 1 (by rfl) ⟨300416, by rfl⟩ : syracuseStep 400555 = 600833) B600833
theorem B400631 : Blo 183802 400631 := bstep (se 1 (by rfl) ⟨300473, by rfl⟩ : syracuseStep 400631 = 600947) B600947
theorem B4300121 : Blo 183802 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B302599 : Blo 183802 302599 := bstep (se 1 (by rfl) ⟨226949, by rfl⟩ : syracuseStep 302599 = 453899) B453899
theorem B663065 : Blo 183802 663065 := bstep (se 2 (by rfl) ⟨248649, by rfl⟩ : syracuseStep 663065 = 497299) B497299
theorem B597563 : Blo 183802 597563 := bstep (se 1 (by rfl) ⟨448172, by rfl⟩ : syracuseStep 597563 = 896345) B896345
theorem B630395 : Blo 183802 630395 := bstep (se 1 (by rfl) ⟨472796, by rfl⟩ : syracuseStep 630395 = 945593) B945593
theorem B466631 : Blo 183802 466631 := bstep (se 1 (by rfl) ⟨349973, by rfl⟩ : syracuseStep 466631 = 699947) B699947
theorem B597719 : Blo 183802 597719 := bstep (se 1 (by rfl) ⟨448289, by rfl⟩ : syracuseStep 597719 = 896579) B896579
theorem B466681 : Blo 183802 466681 := bstep (se 2 (by rfl) ⟨175005, by rfl⟩ : syracuseStep 466681 = 350011) B350011
theorem B630557 : Blo 183802 630557 := bstep (se 3 (by rfl) ⟨118229, by rfl⟩ : syracuseStep 630557 = 236459) B236459
theorem B237487 : Blo 183802 237487 := bstep (se 1 (by rfl) ⟨178115, by rfl⟩ : syracuseStep 237487 = 356231) B356231
theorem B335929 : Blo 183802 335929 := bstep (se 2 (by rfl) ⟨125973, by rfl⟩ : syracuseStep 335929 = 251947) B251947
theorem B631145 : Blo 183802 631145 := bstep (se 2 (by rfl) ⟨236679, by rfl⟩ : syracuseStep 631145 = 473359) B473359
theorem B467329 : Blo 183802 467329 := bstep (se 2 (by rfl) ⟨175248, by rfl⟩ : syracuseStep 467329 = 350497) B350497
theorem B631259 : Blo 183802 631259 := bstep (se 1 (by rfl) ⟨473444, by rfl⟩ : syracuseStep 631259 = 946889) B946889
theorem B1188361 : Blo 183802 1188361 := bstep (se 2 (by rfl) ⟨445635, by rfl⟩ : syracuseStep 1188361 = 891271) B891271
theorem B565883 : Blo 183802 565883 := bstep (se 1 (by rfl) ⟨424412, by rfl⟩ : syracuseStep 565883 = 848825) B848825
theorem B1352477 : Blo 183802 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B1057643 : Blo 183802 1057643 := bstep (se 1 (by rfl) ⟨793232, by rfl⟩ : syracuseStep 1057643 = 1586465) B1586465
theorem B336953 : Blo 183802 336953 := bstep (se 2 (by rfl) ⟨126357, by rfl⟩ : syracuseStep 336953 = 252715) B252715
theorem B631961 : Blo 183802 631961 := bstep (se 2 (by rfl) ⟨236985, by rfl⟩ : syracuseStep 631961 = 473971) B473971
theorem B468139 : Blo 183802 468139 := bstep (se 1 (by rfl) ⟨351104, by rfl⟩ : syracuseStep 468139 = 702209) B702209
theorem B468443 : Blo 183802 468443 := bstep (se 1 (by rfl) ⟨351332, by rfl⟩ : syracuseStep 468443 = 702665) B702665
theorem B1189363 : Blo 183802 1189363 := bstep (se 1 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 1189363 = 1784045) B1784045
theorem B698003 : Blo 183802 698003 := bstep (se 1 (by rfl) ⟨523502, by rfl⟩ : syracuseStep 698003 = 1047005) B1047005
theorem B1582841 : Blo 183802 1582841 := bstep (se 2 (by rfl) ⟨593565, by rfl⟩ : syracuseStep 1582841 = 1187131) B1187131
theorem B1058669 : Blo 183802 1058669 := bstep (se 3 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 1058669 = 397001) B397001
theorem B206887 : Blo 183802 206887 := bstep (se 1 (by rfl) ⟨155165, by rfl⟩ : syracuseStep 206887 = 310331) B310331
theorem B796787 : Blo 183802 796787 := bstep (se 1 (by rfl) ⟨597590, by rfl⟩ : syracuseStep 796787 = 1195181) B1195181
theorem B633149 : Blo 183802 633149 := bstep (se 3 (by rfl) ⟨118715, by rfl⟩ : syracuseStep 633149 = 237431) B237431
theorem B338555 : Blo 183802 338555 := bstep (se 1 (by rfl) ⟨253916, by rfl⟩ : syracuseStep 338555 = 507833) B507833
theorem B666251 : Blo 183802 666251 := bstep (se 1 (by rfl) ⟨499688, by rfl⟩ : syracuseStep 666251 = 999377) B999377
theorem B4500299 : Blo 183802 4500299 := bstep (se 1 (by rfl) ⟨3375224, by rfl⟩ : syracuseStep 4500299 = 6750449) B6750449
theorem B469921 : Blo 183802 469921 := bstep (se 2 (by rfl) ⟨176220, by rfl⟩ : syracuseStep 469921 = 352441) B352441
theorem B208507 : Blo 183802 208507 := bstep (se 1 (by rfl) ⟨156380, by rfl⟩ : syracuseStep 208507 = 312761) B312761
theorem B1421243 : Blo 183802 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B3158027 : Blo 183802 3158027 := bstep (se 1 (by rfl) ⟨2368520, by rfl⟩ : syracuseStep 3158027 = 4737041) B4737041
theorem B208975 : Blo 183802 208975 := bstep (se 1 (by rfl) ⟨156731, by rfl⟩ : syracuseStep 208975 = 313463) B313463
theorem B799105 : Blo 183802 799105 := bstep (se 2 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 799105 = 599329) B599329
theorem B209371 : Blo 183802 209371 := bstep (se 1 (by rfl) ⟨157028, by rfl⟩ : syracuseStep 209371 = 314057) B314057
theorem B1061585 : Blo 183802 1061585 := bstep (se 2 (by rfl) ⟨398094, by rfl⟩ : syracuseStep 1061585 = 796189) B796189
theorem B1422035 : Blo 183802 1422035 := bstep (se 1 (by rfl) ⟨1066526, by rfl⟩ : syracuseStep 1422035 = 2133053) B2133053
theorem B897821 : Blo 183802 897821 := bstep (se 3 (by rfl) ⟨168341, by rfl⟩ : syracuseStep 897821 = 336683) B336683
theorem B504737 : Blo 183802 504737 := bstep (se 2 (by rfl) ⟨189276, by rfl⟩ : syracuseStep 504737 = 378553) B378553
theorem B209839 : Blo 183802 209839 := bstep (se 1 (by rfl) ⟨157379, by rfl⟩ : syracuseStep 209839 = 314759) B314759
theorem B275705 : Blo 183802 275705 := bstep (se 2 (by rfl) ⟨103389, by rfl⟩ : syracuseStep 275705 = 206779) B206779
theorem B275807 : Blo 183802 275807 := bstep (se 1 (by rfl) ⟨206855, by rfl⟩ : syracuseStep 275807 = 413711) B413711
theorem B210271 : Blo 183802 210271 := bstep (se 1 (by rfl) ⟨157703, by rfl⟩ : syracuseStep 210271 = 315407) B315407
theorem B275819 : Blo 183802 275819 := bstep (se 1 (by rfl) ⟨206864, by rfl⟩ : syracuseStep 275819 = 413729) B413729
theorem B472463 : Blo 183802 472463 := bstep (se 1 (by rfl) ⟨354347, by rfl⟩ : syracuseStep 472463 = 708695) B708695
theorem B276047 : Blo 183802 276047 := bstep (se 1 (by rfl) ⟨207035, by rfl⟩ : syracuseStep 276047 = 414071) B414071
theorem B276167 : Blo 183802 276167 := bstep (se 1 (by rfl) ⟨207125, by rfl⟩ : syracuseStep 276167 = 414251) B414251
theorem B210631 : Blo 183802 210631 := bstep (se 1 (by rfl) ⟨157973, by rfl⟩ : syracuseStep 210631 = 315947) B315947
theorem B472787 : Blo 183802 472787 := bstep (se 1 (by rfl) ⟨354590, by rfl⟩ : syracuseStep 472787 = 709181) B709181
theorem B800579 : Blo 183802 800579 := bstep (se 1 (by rfl) ⟨600434, by rfl⟩ : syracuseStep 800579 = 1200869) B1200869
theorem B276329 : Blo 183802 276329 := bstep (se 2 (by rfl) ⟨103623, by rfl⟩ : syracuseStep 276329 = 207247) B207247
theorem B276407 : Blo 183802 276407 := bstep (se 1 (by rfl) ⟨207305, by rfl⟩ : syracuseStep 276407 = 414611) B414611
theorem B702391 : Blo 183802 702391 := bstep (se 1 (by rfl) ⟨526793, by rfl⟩ : syracuseStep 702391 = 1053587) B1053587
theorem B538555 : Blo 183802 538555 := bstep (se 1 (by rfl) ⟨403916, by rfl⟩ : syracuseStep 538555 = 807833) B807833
theorem B276443 : Blo 183802 276443 := bstep (se 1 (by rfl) ⟨207332, by rfl⟩ : syracuseStep 276443 = 414665) B414665
theorem B2046053 : Blo 183802 2046053 := bstep (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) B383635
theorem B702863 : Blo 183802 702863 := bstep (se 1 (by rfl) ⟨527147, by rfl⟩ : syracuseStep 702863 = 1054295) B1054295
theorem B276911 : Blo 183802 276911 := bstep (se 1 (by rfl) ⟨207683, by rfl⟩ : syracuseStep 276911 = 415367) B415367
theorem B375227 : Blo 183802 375227 := bstep (se 1 (by rfl) ⟨281420, by rfl⟩ : syracuseStep 375227 = 562841) B562841
theorem B277001 : Blo 183802 277001 := bstep (se 2 (by rfl) ⟨103875, by rfl⟩ : syracuseStep 277001 = 207751) B207751
theorem B277031 : Blo 183802 277031 := bstep (se 1 (by rfl) ⟨207773, by rfl⟩ : syracuseStep 277031 = 415547) B415547
theorem B277115 : Blo 183802 277115 := bstep (se 1 (by rfl) ⟨207836, by rfl⟩ : syracuseStep 277115 = 415673) B415673
theorem B277241 : Blo 183802 277241 := bstep (se 2 (by rfl) ⟨103965, by rfl⟩ : syracuseStep 277241 = 207931) B207931
theorem B277343 : Blo 183802 277343 := bstep (se 1 (by rfl) ⟨208007, by rfl⟩ : syracuseStep 277343 = 416015) B416015
theorem B473951 : Blo 183802 473951 := bstep (se 1 (by rfl) ⟨355463, by rfl⟩ : syracuseStep 473951 = 710927) B710927
theorem B277355 : Blo 183802 277355 := bstep (se 1 (by rfl) ⟨208016, by rfl⟩ : syracuseStep 277355 = 416033) B416033
theorem B310351 : Blo 183802 310351 := bstep (se 1 (by rfl) ⟨232763, by rfl⟩ : syracuseStep 310351 = 465527) B465527
theorem B277583 : Blo 183802 277583 := bstep (se 1 (by rfl) ⟨208187, by rfl⟩ : syracuseStep 277583 = 416375) B416375
theorem B277703 : Blo 183802 277703 := bstep (se 1 (by rfl) ⟨208277, by rfl⟩ : syracuseStep 277703 = 416555) B416555
theorem B310601 : Blo 183802 310601 := bstep (se 2 (by rfl) ⟨116475, by rfl⟩ : syracuseStep 310601 = 232951) B232951
theorem B277865 : Blo 183802 277865 := bstep (se 2 (by rfl) ⟨104199, by rfl⟩ : syracuseStep 277865 = 208399) B208399
theorem B703849 : Blo 183802 703849 := bstep (se 2 (by rfl) ⟨263943, by rfl⟩ : syracuseStep 703849 = 527887) B527887
theorem B2243965 : Blo 183802 2243965 := bstep (se 3 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 2243965 = 841487) B841487
theorem B277943 : Blo 183802 277943 := bstep (se 1 (by rfl) ⟨208457, by rfl⟩ : syracuseStep 277943 = 416915) B416915
theorem B277979 : Blo 183802 277979 := bstep (se 1 (by rfl) ⟨208484, by rfl⟩ : syracuseStep 277979 = 416969) B416969
theorem B8535581 : Blo 183802 8535581 := bstep (se 3 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 8535581 = 3200843) B3200843
theorem B704123 : Blo 183802 704123 := bstep (se 1 (by rfl) ⟨528092, by rfl⟩ : syracuseStep 704123 = 1056185) B1056185
theorem B2866877 : Blo 183802 2866877 := bstep (se 3 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 2866877 = 1075079) B1075079
theorem B311033 : Blo 183802 311033 := bstep (se 2 (by rfl) ⟨116637, by rfl⟩ : syracuseStep 311033 = 233275) B233275
theorem B311215 : Blo 183802 311215 := bstep (se 1 (by rfl) ⟨233411, by rfl⟩ : syracuseStep 311215 = 466823) B466823
theorem B278447 : Blo 183802 278447 := bstep (se 1 (by rfl) ⟨208835, by rfl⟩ : syracuseStep 278447 = 417671) B417671
theorem B475055 : Blo 183802 475055 := bstep (se 1 (by rfl) ⟨356291, by rfl⟩ : syracuseStep 475055 = 712583) B712583
theorem B1196039 : Blo 183802 1196039 := bstep (se 1 (by rfl) ⟨897029, by rfl⟩ : syracuseStep 1196039 = 1794059) B1794059
theorem B311303 : Blo 183802 311303 := bstep (se 1 (by rfl) ⟨233477, by rfl⟩ : syracuseStep 311303 = 466955) B466955
theorem B278537 : Blo 183802 278537 := bstep (se 2 (by rfl) ⟨104451, by rfl⟩ : syracuseStep 278537 = 208903) B208903
theorem B1425437 : Blo 183802 1425437 := bstep (se 3 (by rfl) ⟨267269, by rfl⟩ : syracuseStep 1425437 = 534539) B534539
theorem B278567 : Blo 183802 278567 := bstep (se 1 (by rfl) ⟨208925, by rfl⟩ : syracuseStep 278567 = 417851) B417851
theorem B278651 : Blo 183802 278651 := bstep (se 1 (by rfl) ⟨208988, by rfl⟩ : syracuseStep 278651 = 417977) B417977
theorem B671915 : Blo 183802 671915 := bstep (se 1 (by rfl) ⟨503936, by rfl⟩ : syracuseStep 671915 = 1007873) B1007873
theorem B278777 : Blo 183802 278777 := bstep (se 2 (by rfl) ⟨104541, by rfl⟩ : syracuseStep 278777 = 209083) B209083
theorem B311647 : Blo 183802 311647 := bstep (se 1 (by rfl) ⟨233735, by rfl⟩ : syracuseStep 311647 = 467471) B467471
theorem B278879 : Blo 183802 278879 := bstep (se 1 (by rfl) ⟨209159, by rfl⟩ : syracuseStep 278879 = 418319) B418319
theorem B278891 : Blo 183802 278891 := bstep (se 1 (by rfl) ⟨209168, by rfl⟩ : syracuseStep 278891 = 418337) B418337
theorem B311735 : Blo 183802 311735 := bstep (se 1 (by rfl) ⟨233801, by rfl⟩ : syracuseStep 311735 = 467603) B467603
theorem B279119 : Blo 183802 279119 := bstep (se 1 (by rfl) ⟨209339, by rfl⟩ : syracuseStep 279119 = 418679) B418679
theorem B279239 : Blo 183802 279239 := bstep (se 1 (by rfl) ⟨209429, by rfl⟩ : syracuseStep 279239 = 418859) B418859
theorem B803537 : Blo 183802 803537 := bstep (se 2 (by rfl) ⟨301326, by rfl⟩ : syracuseStep 803537 = 602653) B602653
theorem B607019 : Blo 183802 607019 := bstep (se 1 (by rfl) ⟨455264, by rfl⟩ : syracuseStep 607019 = 910529) B910529
theorem B1786697 : Blo 183802 1786697 := bstep (se 2 (by rfl) ⟨670011, by rfl⟩ : syracuseStep 1786697 = 1340023) B1340023
theorem B901961 : Blo 183802 901961 := bstep (se 2 (by rfl) ⟨338235, by rfl⟩ : syracuseStep 901961 = 676471) B676471
theorem B279401 : Blo 183802 279401 := bstep (se 2 (by rfl) ⟨104775, by rfl⟩ : syracuseStep 279401 = 209551) B209551
theorem B1590191 : Blo 183802 1590191 := bstep (se 1 (by rfl) ⟨1192643, by rfl⟩ : syracuseStep 1590191 = 2385287) B2385287
theorem B279479 : Blo 183802 279479 := bstep (se 1 (by rfl) ⟨209609, by rfl⟩ : syracuseStep 279479 = 419219) B419219
theorem B279515 : Blo 183802 279515 := bstep (se 1 (by rfl) ⟨209636, by rfl⟩ : syracuseStep 279515 = 419273) B419273
theorem B312329 : Blo 183802 312329 := bstep (se 2 (by rfl) ⟨117123, by rfl⟩ : syracuseStep 312329 = 234247) B234247
theorem B312491 : Blo 183802 312491 := bstep (se 1 (by rfl) ⟨234368, by rfl⟩ : syracuseStep 312491 = 468737) B468737
theorem B279983 : Blo 183802 279983 := bstep (se 1 (by rfl) ⟨209987, by rfl⟩ : syracuseStep 279983 = 419975) B419975
theorem B1230281 : Blo 183802 1230281 := bstep (se 2 (by rfl) ⟨461355, by rfl⟩ : syracuseStep 1230281 = 922711) B922711
theorem B935387 : Blo 183802 935387 := bstep (se 1 (by rfl) ⟨701540, by rfl⟩ : syracuseStep 935387 = 1403081) B1403081
theorem B280073 : Blo 183802 280073 := bstep (se 2 (by rfl) ⟨105027, by rfl⟩ : syracuseStep 280073 = 210055) B210055
theorem B280103 : Blo 183802 280103 := bstep (se 1 (by rfl) ⟨210077, by rfl⟩ : syracuseStep 280103 = 420155) B420155
theorem B312889 : Blo 183802 312889 := bstep (se 2 (by rfl) ⟨117333, by rfl⟩ : syracuseStep 312889 = 234667) B234667
theorem B280187 : Blo 183802 280187 := bstep (se 1 (by rfl) ⟨210140, by rfl⟩ : syracuseStep 280187 = 420281) B420281
theorem B313031 : Blo 183802 313031 := bstep (se 1 (by rfl) ⟨234773, by rfl⟩ : syracuseStep 313031 = 469547) B469547
theorem B280313 : Blo 183802 280313 := bstep (se 2 (by rfl) ⟨105117, by rfl⟩ : syracuseStep 280313 = 210235) B210235
theorem B280415 : Blo 183802 280415 := bstep (se 1 (by rfl) ⟨210311, by rfl⟩ : syracuseStep 280415 = 420623) B420623
theorem B313193 : Blo 183802 313193 := bstep (se 2 (by rfl) ⟨117447, by rfl⟩ : syracuseStep 313193 = 234895) B234895
theorem B345961 : Blo 183802 345961 := bstep (se 2 (by rfl) ⟨129735, by rfl⟩ : syracuseStep 345961 = 259471) B259471
theorem B280427 : Blo 183802 280427 := bstep (se 1 (by rfl) ⟨210320, by rfl⟩ : syracuseStep 280427 = 420641) B420641
theorem B935873 : Blo 183802 935873 := bstep (se 2 (by rfl) ⟨350952, by rfl⟩ : syracuseStep 935873 = 701905) B701905
theorem B1624121 : Blo 183802 1624121 := bstep (se 2 (by rfl) ⟨609045, by rfl⟩ : syracuseStep 1624121 = 1218091) B1218091
theorem B280655 : Blo 183802 280655 := bstep (se 1 (by rfl) ⟨210491, by rfl⟩ : syracuseStep 280655 = 420983) B420983
theorem B1067165 : Blo 183802 1067165 := bstep (se 3 (by rfl) ⟨200093, by rfl⟩ : syracuseStep 1067165 = 400187) B400187
theorem B280775 : Blo 183802 280775 := bstep (se 1 (by rfl) ⟨210581, by rfl⟩ : syracuseStep 280775 = 421163) B421163
theorem B313591 : Blo 183802 313591 := bstep (se 1 (by rfl) ⟨235193, by rfl⟩ : syracuseStep 313591 = 470387) B470387
theorem B280937 : Blo 183802 280937 := bstep (se 2 (by rfl) ⟨105351, by rfl⟩ : syracuseStep 280937 = 210703) B210703
theorem B281015 : Blo 183802 281015 := bstep (se 1 (by rfl) ⟨210761, by rfl⟩ : syracuseStep 281015 = 421523) B421523
theorem B313787 : Blo 183802 313787 := bstep (se 1 (by rfl) ⟨235340, by rfl⟩ : syracuseStep 313787 = 470681) B470681
theorem B281051 : Blo 183802 281051 := bstep (se 1 (by rfl) ⟨210788, by rfl⟩ : syracuseStep 281051 = 421577) B421577
theorem B313895 : Blo 183802 313895 := bstep (se 1 (by rfl) ⟨235421, by rfl⟩ : syracuseStep 313895 = 470843) B470843
theorem B314185 : Blo 183802 314185 := bstep (se 2 (by rfl) ⟨117819, by rfl⟩ : syracuseStep 314185 = 235639) B235639
theorem B1198921 : Blo 183802 1198921 := bstep (se 2 (by rfl) ⟨449595, by rfl⟩ : syracuseStep 1198921 = 899191) B899191
theorem B1067849 : Blo 183802 1067849 := bstep (se 2 (by rfl) ⟨400443, by rfl⟩ : syracuseStep 1067849 = 800887) B800887
theorem B248681 : Blo 183802 248681 := bstep (se 2 (by rfl) ⟨93255, by rfl⟩ : syracuseStep 248681 = 186511) B186511
theorem B314219 : Blo 183802 314219 := bstep (se 1 (by rfl) ⟨235664, by rfl⟩ : syracuseStep 314219 = 471329) B471329
theorem B1362863 : Blo 183802 1362863 := bstep (se 1 (by rfl) ⟨1022147, by rfl⟩ : syracuseStep 1362863 = 2044295) B2044295
theorem B281519 : Blo 183802 281519 := bstep (se 1 (by rfl) ⟨211139, by rfl⟩ : syracuseStep 281519 = 422279) B422279
theorem B2214839 : Blo 183802 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B281609 : Blo 183802 281609 := bstep (se 2 (by rfl) ⟨105603, by rfl⟩ : syracuseStep 281609 = 211207) B211207
theorem B281639 : Blo 183802 281639 := bstep (se 1 (by rfl) ⟨211229, by rfl⟩ : syracuseStep 281639 = 422459) B422459
theorem B1395791 : Blo 183802 1395791 := bstep (se 1 (by rfl) ⟨1046843, by rfl⟩ : syracuseStep 1395791 = 2093687) B2093687
theorem B707737 : Blo 183802 707737 := bstep (se 2 (by rfl) ⟨265401, by rfl⟩ : syracuseStep 707737 = 530803) B530803
theorem B314617 : Blo 183802 314617 := bstep (se 2 (by rfl) ⟨117981, by rfl⟩ : syracuseStep 314617 = 235963) B235963
theorem B281951 : Blo 183802 281951 := bstep (se 1 (by rfl) ⟨211463, by rfl⟩ : syracuseStep 281951 = 422927) B422927
theorem B708041 : Blo 183802 708041 := bstep (se 2 (by rfl) ⟨265515, by rfl⟩ : syracuseStep 708041 = 531031) B531031
theorem B314887 : Blo 183802 314887 := bstep (se 1 (by rfl) ⟨236165, by rfl⟩ : syracuseStep 314887 = 472331) B472331
theorem B183847 : Blo 183802 183847 := bstep (se 1 (by rfl) ⟨137885, by rfl⟩ : syracuseStep 183847 = 275771) B275771
theorem B183887 : Blo 183802 183887 := bstep (se 1 (by rfl) ⟨137915, by rfl⟩ : syracuseStep 183887 = 275831) B275831
theorem B183903 : Blo 183802 183903 := bstep (se 1 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 183903 = 275855) B275855
theorem B183931 : Blo 183802 183931 := bstep (se 1 (by rfl) ⟨137948, by rfl⟩ : syracuseStep 183931 = 275897) B275897
theorem B183983 : Blo 183802 183983 := bstep (se 1 (by rfl) ⟨137987, by rfl⟩ : syracuseStep 183983 = 275975) B275975
theorem B184007 : Blo 183802 184007 := bstep (se 1 (by rfl) ⟨138005, by rfl⟩ : syracuseStep 184007 = 276011) B276011
theorem B184027 : Blo 183802 184027 := bstep (se 1 (by rfl) ⟨138020, by rfl⟩ : syracuseStep 184027 = 276041) B276041
theorem B184103 : Blo 183802 184103 := bstep (se 1 (by rfl) ⟨138077, by rfl⟩ : syracuseStep 184103 = 276155) B276155
theorem B184143 : Blo 183802 184143 := bstep (se 1 (by rfl) ⟨138107, by rfl⟩ : syracuseStep 184143 = 276215) B276215
theorem B184159 : Blo 183802 184159 := bstep (se 1 (by rfl) ⟨138119, by rfl⟩ : syracuseStep 184159 = 276239) B276239
theorem B1003373 : Blo 183802 1003373 := bstep (se 3 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 1003373 = 376265) B376265
theorem B184187 : Blo 183802 184187 := bstep (se 1 (by rfl) ⟨138140, by rfl⟩ : syracuseStep 184187 = 276281) B276281
theorem B184239 : Blo 183802 184239 := bstep (se 1 (by rfl) ⟨138179, by rfl⟩ : syracuseStep 184239 = 276359) B276359
theorem B708527 : Blo 183802 708527 := bstep (se 1 (by rfl) ⟨531395, by rfl⟩ : syracuseStep 708527 = 1062791) B1062791
theorem B315319 : Blo 183802 315319 := bstep (se 1 (by rfl) ⟨236489, by rfl⟩ : syracuseStep 315319 = 472979) B472979
theorem B184263 : Blo 183802 184263 := bstep (se 1 (by rfl) ⟨138197, by rfl⟩ : syracuseStep 184263 = 276395) B276395
theorem B184283 : Blo 183802 184283 := bstep (se 1 (by rfl) ⟨138212, by rfl⟩ : syracuseStep 184283 = 276425) B276425
theorem B9129995 : Blo 183802 9129995 := bstep (se 1 (by rfl) ⟨6847496, by rfl⟩ : syracuseStep 9129995 = 13694993) B13694993
theorem B184359 : Blo 183802 184359 := bstep (se 1 (by rfl) ⟨138269, by rfl⟩ : syracuseStep 184359 = 276539) B276539
theorem B184399 : Blo 183802 184399 := bstep (se 1 (by rfl) ⟨138299, by rfl⟩ : syracuseStep 184399 = 276599) B276599
theorem B184415 : Blo 183802 184415 := bstep (se 1 (by rfl) ⟨138311, by rfl⟩ : syracuseStep 184415 = 276623) B276623
theorem B184443 : Blo 183802 184443 := bstep (se 1 (by rfl) ⟨138332, by rfl⟩ : syracuseStep 184443 = 276665) B276665
theorem B315515 : Blo 183802 315515 := bstep (se 1 (by rfl) ⟨236636, by rfl⟩ : syracuseStep 315515 = 473273) B473273
theorem B938141 : Blo 183802 938141 := bstep (se 3 (by rfl) ⟨175901, by rfl⟩ : syracuseStep 938141 = 351803) B351803
theorem B184495 : Blo 183802 184495 := bstep (se 1 (by rfl) ⟨138371, by rfl⟩ : syracuseStep 184495 = 276743) B276743
theorem B184519 : Blo 183802 184519 := bstep (se 1 (by rfl) ⟨138389, by rfl⟩ : syracuseStep 184519 = 276779) B276779
theorem B184539 : Blo 183802 184539 := bstep (se 1 (by rfl) ⟨138404, by rfl⟩ : syracuseStep 184539 = 276809) B276809
theorem B184615 : Blo 183802 184615 := bstep (se 1 (by rfl) ⟨138461, by rfl⟩ : syracuseStep 184615 = 276923) B276923
theorem B184655 : Blo 183802 184655 := bstep (se 1 (by rfl) ⟨138491, by rfl⟩ : syracuseStep 184655 = 276983) B276983
theorem B184671 : Blo 183802 184671 := bstep (se 1 (by rfl) ⟨138503, by rfl⟩ : syracuseStep 184671 = 277007) B277007
theorem B184699 : Blo 183802 184699 := bstep (se 1 (by rfl) ⟨138524, by rfl⟩ : syracuseStep 184699 = 277049) B277049
theorem B184751 : Blo 183802 184751 := bstep (se 1 (by rfl) ⟨138563, by rfl⟩ : syracuseStep 184751 = 277127) B277127
theorem B184775 : Blo 183802 184775 := bstep (se 1 (by rfl) ⟨138581, by rfl⟩ : syracuseStep 184775 = 277163) B277163
theorem B184795 : Blo 183802 184795 := bstep (se 1 (by rfl) ⟨138596, by rfl⟩ : syracuseStep 184795 = 277193) B277193
theorem B315913 : Blo 183802 315913 := bstep (se 2 (by rfl) ⟨118467, by rfl⟩ : syracuseStep 315913 = 236935) B236935
theorem B184871 : Blo 183802 184871 := bstep (se 1 (by rfl) ⟨138653, by rfl⟩ : syracuseStep 184871 = 277307) B277307
theorem B184911 : Blo 183802 184911 := bstep (se 1 (by rfl) ⟨138683, by rfl⟩ : syracuseStep 184911 = 277367) B277367
theorem B184927 : Blo 183802 184927 := bstep (se 1 (by rfl) ⟨138695, by rfl⟩ : syracuseStep 184927 = 277391) B277391
theorem B414305 : Blo 183802 414305 := bstep (se 2 (by rfl) ⟨155364, by rfl⟩ : syracuseStep 414305 = 310729) B310729
theorem B184955 : Blo 183802 184955 := bstep (se 1 (by rfl) ⟨138716, by rfl⟩ : syracuseStep 184955 = 277433) B277433
theorem B316075 : Blo 183802 316075 := bstep (se 1 (by rfl) ⟨237056, by rfl⟩ : syracuseStep 316075 = 474113) B474113
theorem B185007 : Blo 183802 185007 := bstep (se 1 (by rfl) ⟨138755, by rfl⟩ : syracuseStep 185007 = 277511) B277511
theorem B185031 : Blo 183802 185031 := bstep (se 1 (by rfl) ⟨138773, by rfl⟩ : syracuseStep 185031 = 277547) B277547
theorem B185051 : Blo 183802 185051 := bstep (se 1 (by rfl) ⟨138788, by rfl⟩ : syracuseStep 185051 = 277577) B277577
theorem B185127 : Blo 183802 185127 := bstep (se 1 (by rfl) ⟨138845, by rfl⟩ : syracuseStep 185127 = 277691) B277691
theorem B2118473 : Blo 183802 2118473 := bstep (se 2 (by rfl) ⟨794427, by rfl⟩ : syracuseStep 2118473 = 1588855) B1588855
theorem B185167 : Blo 183802 185167 := bstep (se 1 (by rfl) ⟨138875, by rfl⟩ : syracuseStep 185167 = 277751) B277751
theorem B185183 : Blo 183802 185183 := bstep (se 1 (by rfl) ⟨138887, by rfl⟩ : syracuseStep 185183 = 277775) B277775
theorem B185211 : Blo 183802 185211 := bstep (se 1 (by rfl) ⟨138908, by rfl⟩ : syracuseStep 185211 = 277817) B277817
theorem B185263 : Blo 183802 185263 := bstep (se 1 (by rfl) ⟨138947, by rfl⟩ : syracuseStep 185263 = 277895) B277895
theorem B414647 : Blo 183802 414647 := bstep (se 1 (by rfl) ⟨310985, by rfl⟩ : syracuseStep 414647 = 621971) B621971
theorem B185287 : Blo 183802 185287 := bstep (se 1 (by rfl) ⟨138965, by rfl⟩ : syracuseStep 185287 = 277931) B277931
theorem B185307 : Blo 183802 185307 := bstep (se 1 (by rfl) ⟨138980, by rfl⟩ : syracuseStep 185307 = 277961) B277961
theorem B316379 : Blo 183802 316379 := bstep (se 1 (by rfl) ⟨237284, by rfl⟩ : syracuseStep 316379 = 474569) B474569
theorem B185383 : Blo 183802 185383 := bstep (se 1 (by rfl) ⟨139037, by rfl⟩ : syracuseStep 185383 = 278075) B278075
theorem B185423 : Blo 183802 185423 := bstep (se 1 (by rfl) ⟨139067, by rfl⟩ : syracuseStep 185423 = 278135) B278135
theorem B185439 : Blo 183802 185439 := bstep (se 1 (by rfl) ⟨139079, by rfl⟩ : syracuseStep 185439 = 278159) B278159
theorem B185467 : Blo 183802 185467 := bstep (se 1 (by rfl) ⟨139100, by rfl⟩ : syracuseStep 185467 = 278201) B278201
theorem B185519 : Blo 183802 185519 := bstep (se 1 (by rfl) ⟨139139, by rfl⟩ : syracuseStep 185519 = 278279) B278279
theorem B185543 : Blo 183802 185543 := bstep (se 1 (by rfl) ⟨139157, by rfl⟩ : syracuseStep 185543 = 278315) B278315
theorem B316615 : Blo 183802 316615 := bstep (se 1 (by rfl) ⟨237461, by rfl⟩ : syracuseStep 316615 = 474923) B474923
theorem B185563 : Blo 183802 185563 := bstep (se 1 (by rfl) ⟨139172, by rfl⟩ : syracuseStep 185563 = 278345) B278345
theorem B185639 : Blo 183802 185639 := bstep (se 1 (by rfl) ⟨139229, by rfl⟩ : syracuseStep 185639 = 278459) B278459
theorem B185679 : Blo 183802 185679 := bstep (se 1 (by rfl) ⟨139259, by rfl⟩ : syracuseStep 185679 = 278519) B278519
theorem B185695 : Blo 183802 185695 := bstep (se 1 (by rfl) ⟨139271, by rfl⟩ : syracuseStep 185695 = 278543) B278543
theorem B316777 : Blo 183802 316777 := bstep (se 2 (by rfl) ⟨118791, by rfl⟩ : syracuseStep 316777 = 237583) B237583
theorem B185723 : Blo 183802 185723 := bstep (se 1 (by rfl) ⟨139292, by rfl⟩ : syracuseStep 185723 = 278585) B278585
theorem B939437 : Blo 183802 939437 := bstep (se 3 (by rfl) ⟨176144, by rfl⟩ : syracuseStep 939437 = 352289) B352289
theorem B185775 : Blo 183802 185775 := bstep (se 1 (by rfl) ⟨139331, by rfl⟩ : syracuseStep 185775 = 278663) B278663
theorem B185799 : Blo 183802 185799 := bstep (se 1 (by rfl) ⟨139349, by rfl⟩ : syracuseStep 185799 = 278699) B278699
theorem B185819 : Blo 183802 185819 := bstep (se 1 (by rfl) ⟨139364, by rfl⟩ : syracuseStep 185819 = 278729) B278729
theorem B710153 : Blo 183802 710153 := bstep (se 2 (by rfl) ⟨266307, by rfl⟩ : syracuseStep 710153 = 532615) B532615
theorem B415241 : Blo 183802 415241 := bstep (se 2 (by rfl) ⟨155715, by rfl⟩ : syracuseStep 415241 = 311431) B311431
theorem B185895 : Blo 183802 185895 := bstep (se 1 (by rfl) ⟨139421, by rfl⟩ : syracuseStep 185895 = 278843) B278843
theorem B448039 : Blo 183802 448039 := bstep (se 1 (by rfl) ⟨336029, by rfl⟩ : syracuseStep 448039 = 672059) B672059
theorem B349753 : Blo 183802 349753 := bstep (se 2 (by rfl) ⟨131157, by rfl⟩ : syracuseStep 349753 = 262315) B262315
theorem B3200573 : Blo 183802 3200573 := bstep (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) B1200215
theorem B185935 : Blo 183802 185935 := bstep (se 1 (by rfl) ⟨139451, by rfl⟩ : syracuseStep 185935 = 278903) B278903
theorem B251471 : Blo 183802 251471 := bstep (se 1 (by rfl) ⟨188603, by rfl⟩ : syracuseStep 251471 = 377207) B377207
theorem B185951 : Blo 183802 185951 := bstep (se 1 (by rfl) ⟨139463, by rfl⟩ : syracuseStep 185951 = 278927) B278927
theorem B185979 : Blo 183802 185979 := bstep (se 1 (by rfl) ⟨139484, by rfl⟩ : syracuseStep 185979 = 278969) B278969
theorem B186031 : Blo 183802 186031 := bstep (se 1 (by rfl) ⟨139523, by rfl⟩ : syracuseStep 186031 = 279047) B279047
theorem B186055 : Blo 183802 186055 := bstep (se 1 (by rfl) ⟨139541, by rfl⟩ : syracuseStep 186055 = 279083) B279083
theorem B186075 : Blo 183802 186075 := bstep (se 1 (by rfl) ⟨139556, by rfl⟩ : syracuseStep 186075 = 279113) B279113
theorem B186151 : Blo 183802 186151 := bstep (se 1 (by rfl) ⟨139613, by rfl⟩ : syracuseStep 186151 = 279227) B279227
theorem B186191 : Blo 183802 186191 := bstep (se 1 (by rfl) ⟨139643, by rfl⟩ : syracuseStep 186191 = 279287) B279287
theorem B415583 : Blo 183802 415583 := bstep (se 1 (by rfl) ⟨311687, by rfl⟩ : syracuseStep 415583 = 623375) B623375
theorem B186207 : Blo 183802 186207 := bstep (se 1 (by rfl) ⟨139655, by rfl⟩ : syracuseStep 186207 = 279311) B279311
theorem B350057 : Blo 183802 350057 := bstep (se 2 (by rfl) ⟨131271, by rfl⟩ : syracuseStep 350057 = 262543) B262543
theorem B186235 : Blo 183802 186235 := bstep (se 1 (by rfl) ⟨139676, by rfl⟩ : syracuseStep 186235 = 279353) B279353
theorem B350095 : Blo 183802 350095 := bstep (se 1 (by rfl) ⟨262571, by rfl⟩ : syracuseStep 350095 = 525143) B525143
theorem B186287 : Blo 183802 186287 := bstep (se 1 (by rfl) ⟨139715, by rfl⟩ : syracuseStep 186287 = 279431) B279431
theorem B186311 : Blo 183802 186311 := bstep (se 1 (by rfl) ⟨139733, by rfl⟩ : syracuseStep 186311 = 279467) B279467
theorem B186331 : Blo 183802 186331 := bstep (se 1 (by rfl) ⟨139748, by rfl⟩ : syracuseStep 186331 = 279497) B279497
theorem B710657 : Blo 183802 710657 := bstep (se 2 (by rfl) ⟨266496, by rfl⟩ : syracuseStep 710657 = 532993) B532993
theorem B415763 : Blo 183802 415763 := bstep (se 1 (by rfl) ⟨311822, by rfl⟩ : syracuseStep 415763 = 623645) B623645
theorem B186407 : Blo 183802 186407 := bstep (se 1 (by rfl) ⟨139805, by rfl⟩ : syracuseStep 186407 = 279611) B279611
theorem B186447 : Blo 183802 186447 := bstep (se 1 (by rfl) ⟨139835, by rfl⟩ : syracuseStep 186447 = 279671) B279671
theorem B186463 : Blo 183802 186463 := bstep (se 1 (by rfl) ⟨139847, by rfl⟩ : syracuseStep 186463 = 279695) B279695
theorem B186491 : Blo 183802 186491 := bstep (se 1 (by rfl) ⟨139868, by rfl⟩ : syracuseStep 186491 = 279737) B279737
theorem B186543 : Blo 183802 186543 := bstep (se 1 (by rfl) ⟨139907, by rfl⟩ : syracuseStep 186543 = 279815) B279815
theorem B186567 : Blo 183802 186567 := bstep (se 1 (by rfl) ⟨139925, by rfl⟩ : syracuseStep 186567 = 279851) B279851
theorem B186587 : Blo 183802 186587 := bstep (se 1 (by rfl) ⟨139940, by rfl⟩ : syracuseStep 186587 = 279881) B279881
theorem B186663 : Blo 183802 186663 := bstep (se 1 (by rfl) ⟨139997, by rfl⟩ : syracuseStep 186663 = 279995) B279995
theorem B186703 : Blo 183802 186703 := bstep (se 1 (by rfl) ⟨140027, by rfl⟩ : syracuseStep 186703 = 280055) B280055
theorem B186719 : Blo 183802 186719 := bstep (se 1 (by rfl) ⟨140039, by rfl⟩ : syracuseStep 186719 = 280079) B280079
theorem B416105 : Blo 183802 416105 := bstep (se 2 (by rfl) ⟨156039, by rfl⟩ : syracuseStep 416105 = 312079) B312079
theorem B317803 : Blo 183802 317803 := bstep (se 1 (by rfl) ⟨238352, by rfl⟩ : syracuseStep 317803 = 476705) B476705
theorem B186747 : Blo 183802 186747 := bstep (se 1 (by rfl) ⟨140060, by rfl⟩ : syracuseStep 186747 = 280121) B280121
theorem B907649 : Blo 183802 907649 := bstep (se 2 (by rfl) ⟨340368, by rfl⟩ : syracuseStep 907649 = 680737) B680737
theorem B1399193 : Blo 183802 1399193 := bstep (se 2 (by rfl) ⟨524697, by rfl⟩ : syracuseStep 1399193 = 1049395) B1049395
theorem B186799 : Blo 183802 186799 := bstep (se 1 (by rfl) ⟨140099, by rfl⟩ : syracuseStep 186799 = 280199) B280199
theorem B186823 : Blo 183802 186823 := bstep (se 1 (by rfl) ⟨140117, by rfl⟩ : syracuseStep 186823 = 280235) B280235
theorem B186843 : Blo 183802 186843 := bstep (se 1 (by rfl) ⟨140132, by rfl⟩ : syracuseStep 186843 = 280265) B280265
theorem B186919 : Blo 183802 186919 := bstep (se 1 (by rfl) ⟨140189, by rfl⟩ : syracuseStep 186919 = 280379) B280379
theorem B3758669 : Blo 183802 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B186959 : Blo 183802 186959 := bstep (se 1 (by rfl) ⟨140219, by rfl⟩ : syracuseStep 186959 = 280439) B280439
theorem B186975 : Blo 183802 186975 := bstep (se 1 (by rfl) ⟨140231, by rfl⟩ : syracuseStep 186975 = 280463) B280463
theorem B187003 : Blo 183802 187003 := bstep (se 1 (by rfl) ⟨140252, by rfl⟩ : syracuseStep 187003 = 280505) B280505
theorem B187055 : Blo 183802 187055 := bstep (se 1 (by rfl) ⟨140291, by rfl⟩ : syracuseStep 187055 = 280583) B280583
theorem B187079 : Blo 183802 187079 := bstep (se 1 (by rfl) ⟨140309, by rfl⟩ : syracuseStep 187079 = 280619) B280619
theorem B187099 : Blo 183802 187099 := bstep (se 1 (by rfl) ⟨140324, by rfl⟩ : syracuseStep 187099 = 280649) B280649
theorem B187175 : Blo 183802 187175 := bstep (se 1 (by rfl) ⟨140381, by rfl⟩ : syracuseStep 187175 = 280763) B280763
theorem B187215 : Blo 183802 187215 := bstep (se 1 (by rfl) ⟨140411, by rfl⟩ : syracuseStep 187215 = 280823) B280823
theorem B187231 : Blo 183802 187231 := bstep (se 1 (by rfl) ⟨140423, by rfl⟩ : syracuseStep 187231 = 280847) B280847
theorem B187259 : Blo 183802 187259 := bstep (se 1 (by rfl) ⟨140444, by rfl⟩ : syracuseStep 187259 = 280889) B280889
theorem B187311 : Blo 183802 187311 := bstep (se 1 (by rfl) ⟨140483, by rfl⟩ : syracuseStep 187311 = 280967) B280967
theorem B416699 : Blo 183802 416699 := bstep (se 1 (by rfl) ⟨312524, by rfl⟩ : syracuseStep 416699 = 625049) B625049
theorem B711611 : Blo 183802 711611 := bstep (se 1 (by rfl) ⟨533708, by rfl⟩ : syracuseStep 711611 = 1067417) B1067417
theorem B187335 : Blo 183802 187335 := bstep (se 1 (by rfl) ⟨140501, by rfl⟩ : syracuseStep 187335 = 281003) B281003
theorem B187355 : Blo 183802 187355 := bstep (se 1 (by rfl) ⟨140516, by rfl⟩ : syracuseStep 187355 = 281033) B281033
theorem B941057 : Blo 183802 941057 := bstep (se 2 (by rfl) ⟨352896, by rfl⟩ : syracuseStep 941057 = 705793) B705793
theorem B187431 : Blo 183802 187431 := bstep (se 1 (by rfl) ⟨140573, by rfl⟩ : syracuseStep 187431 = 281147) B281147
theorem B416825 : Blo 183802 416825 := bstep (se 2 (by rfl) ⟨156309, by rfl⟩ : syracuseStep 416825 = 312619) B312619
theorem B187471 : Blo 183802 187471 := bstep (se 1 (by rfl) ⟨140603, by rfl⟩ : syracuseStep 187471 = 281207) B281207
theorem B187487 : Blo 183802 187487 := bstep (se 1 (by rfl) ⟨140615, by rfl⟩ : syracuseStep 187487 = 281231) B281231
theorem B187515 : Blo 183802 187515 := bstep (se 1 (by rfl) ⟨140636, by rfl⟩ : syracuseStep 187515 = 281273) B281273
theorem B187567 : Blo 183802 187567 := bstep (se 1 (by rfl) ⟨140675, by rfl⟩ : syracuseStep 187567 = 281351) B281351
theorem B187591 : Blo 183802 187591 := bstep (se 1 (by rfl) ⟨140693, by rfl⟩ : syracuseStep 187591 = 281387) B281387
theorem B187611 : Blo 183802 187611 := bstep (se 1 (by rfl) ⟨140708, by rfl⟩ : syracuseStep 187611 = 281417) B281417
theorem B187687 : Blo 183802 187687 := bstep (se 1 (by rfl) ⟨140765, by rfl⟩ : syracuseStep 187687 = 281531) B281531
theorem B187727 : Blo 183802 187727 := bstep (se 1 (by rfl) ⟨140795, by rfl⟩ : syracuseStep 187727 = 281591) B281591
theorem B187743 : Blo 183802 187743 := bstep (se 1 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 187743 = 281615) B281615
theorem B187771 : Blo 183802 187771 := bstep (se 1 (by rfl) ⟨140828, by rfl⟩ : syracuseStep 187771 = 281657) B281657
theorem B417167 : Blo 183802 417167 := bstep (se 1 (by rfl) ⟨312875, by rfl⟩ : syracuseStep 417167 = 625751) B625751
theorem B2874797 : Blo 183802 2874797 := bstep (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) B1078049
theorem B351955 : Blo 183802 351955 := bstep (se 1 (by rfl) ⟨263966, by rfl⟩ : syracuseStep 351955 = 527933) B527933
theorem B417491 : Blo 183802 417491 := bstep (se 1 (by rfl) ⟨313118, by rfl⟩ : syracuseStep 417491 = 626237) B626237
theorem B941867 : Blo 183802 941867 := bstep (se 1 (by rfl) ⟨706400, by rfl⟩ : syracuseStep 941867 = 1412801) B1412801
theorem B319339 : Blo 183802 319339 := bstep (se 1 (by rfl) ⟨239504, by rfl⟩ : syracuseStep 319339 = 479009) B479009
theorem B352183 : Blo 183802 352183 := bstep (se 1 (by rfl) ⟨264137, by rfl⟩ : syracuseStep 352183 = 528275) B528275
theorem B2285597 : Blo 183802 2285597 := bstep (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) B857099
theorem B1794163 : Blo 183802 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B1597603 : Blo 183802 1597603 := bstep (se 1 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 1597603 = 2396405) B2396405
theorem B1401137 : Blo 183802 1401137 := bstep (se 2 (by rfl) ⟨525426, by rfl⟩ : syracuseStep 1401137 = 1050853) B1050853
theorem B352775 : Blo 183802 352775 := bstep (se 1 (by rfl) ⟨264581, by rfl⟩ : syracuseStep 352775 = 529163) B529163
theorem B418427 : Blo 183802 418427 := bstep (se 1 (by rfl) ⟨313820, by rfl⟩ : syracuseStep 418427 = 627641) B627641
theorem B484039 : Blo 183802 484039 := bstep (se 1 (by rfl) ⟨363029, by rfl⟩ : syracuseStep 484039 = 726059) B726059
theorem B418553 : Blo 183802 418553 := bstep (se 2 (by rfl) ⟨156957, by rfl⟩ : syracuseStep 418553 = 313915) B313915
theorem B418823 : Blo 183802 418823 := bstep (se 1 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 418823 = 628235) B628235
theorem B418895 : Blo 183802 418895 := bstep (se 1 (by rfl) ⟨314171, by rfl⟩ : syracuseStep 418895 = 628343) B628343
theorem B353641 : Blo 183802 353641 := bstep (se 2 (by rfl) ⟨132615, by rfl⟩ : syracuseStep 353641 = 265231) B265231
theorem B1893851 : Blo 183802 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B419291 : Blo 183802 419291 := bstep (se 1 (by rfl) ⟨314468, by rfl⟩ : syracuseStep 419291 = 628937) B628937
theorem B1598939 : Blo 183802 1598939 := bstep (se 1 (by rfl) ⟨1199204, by rfl⟩ : syracuseStep 1598939 = 2398409) B2398409
theorem B353801 : Blo 183802 353801 := bstep (se 2 (by rfl) ⟨132675, by rfl⟩ : syracuseStep 353801 = 265351) B265351
theorem B222799 : Blo 183802 222799 := bstep (se 1 (by rfl) ⟨167099, by rfl⟩ : syracuseStep 222799 = 334199) B334199
theorem B419759 : Blo 183802 419759 := bstep (se 1 (by rfl) ⟨314819, by rfl⟩ : syracuseStep 419759 = 629639) B629639
theorem B1894337 : Blo 183802 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B944135 : Blo 183802 944135 := bstep (se 1 (by rfl) ⟨708101, by rfl⟩ : syracuseStep 944135 = 1416203) B1416203
theorem B420011 : Blo 183802 420011 := bstep (se 1 (by rfl) ⟨315008, by rfl⟩ : syracuseStep 420011 = 630017) B630017
theorem B944621 : Blo 183802 944621 := bstep (se 3 (by rfl) ⟨177116, by rfl⟩ : syracuseStep 944621 = 354233) B354233
theorem B420551 : Blo 183802 420551 := bstep (se 1 (by rfl) ⟨315413, by rfl⟩ : syracuseStep 420551 = 630827) B630827
theorem B355259 : Blo 183802 355259 := bstep (se 1 (by rfl) ⟨266444, by rfl⟩ : syracuseStep 355259 = 532889) B532889
theorem B945431 : Blo 183802 945431 := bstep (se 1 (by rfl) ⟨709073, by rfl⟩ : syracuseStep 945431 = 1418147) B1418147
theorem B355691 : Blo 183802 355691 := bstep (se 1 (by rfl) ⟨266768, by rfl⟩ : syracuseStep 355691 = 533537) B533537
theorem B355745 : Blo 183802 355745 := bstep (se 2 (by rfl) ⟨133404, by rfl⟩ : syracuseStep 355745 = 266809) B266809
theorem B421415 : Blo 183802 421415 := bstep (se 1 (by rfl) ⟨316061, by rfl⟩ : syracuseStep 421415 = 632123) B632123
theorem B1404539 : Blo 183802 1404539 := bstep (se 1 (by rfl) ⟨1053404, by rfl⟩ : syracuseStep 1404539 = 2106809) B2106809
theorem B356051 : Blo 183802 356051 := bstep (se 1 (by rfl) ⟨267038, by rfl⟩ : syracuseStep 356051 = 534077) B534077
theorem B421739 : Blo 183802 421739 := bstep (se 1 (by rfl) ⟨316304, by rfl⟩ : syracuseStep 421739 = 632609) B632609
theorem B421793 : Blo 183802 421793 := bstep (se 2 (by rfl) ⟨158172, by rfl⟩ : syracuseStep 421793 = 316345) B316345
theorem B1798307 : Blo 183802 1798307 := bstep (se 1 (by rfl) ⟨1348730, by rfl⟩ : syracuseStep 1798307 = 2697461) B2697461
theorem B422135 : Blo 183802 422135 := bstep (se 1 (by rfl) ⟨316601, by rfl⟩ : syracuseStep 422135 = 633203) B633203
theorem B947051 : Blo 183802 947051 := bstep (se 1 (by rfl) ⟨710288, by rfl⟩ : syracuseStep 947051 = 1420577) B1420577
theorem B2880715 : Blo 183802 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B750973 : Blo 183802 750973 := bstep (se 3 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 750973 = 281615) B281615
theorem B947699 : Blo 183802 947699 := bstep (se 1 (by rfl) ⟨710774, by rfl⟩ : syracuseStep 947699 = 1421549) B1421549
theorem B1178009 : Blo 183802 1178009 := bstep (se 2 (by rfl) ⟨441753, by rfl⟩ : syracuseStep 1178009 = 883507) B883507
theorem B1080067 : Blo 183802 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B948995 : Blo 183802 948995 := bstep (se 1 (by rfl) ⟨711746, by rfl⟩ : syracuseStep 948995 = 1423493) B1423493
theorem B621431 : Blo 183802 621431 := bstep (se 1 (by rfl) ⟨466073, by rfl⟩ : syracuseStep 621431 = 932147) B932147
theorem B1276901 : Blo 183802 1276901 := bstep (se 4 (by rfl) ⟨119709, by rfl⟩ : syracuseStep 1276901 = 239419) B239419
theorem B719891 : Blo 183802 719891 := bstep (se 1 (by rfl) ⟨539918, by rfl⟩ : syracuseStep 719891 = 1079837) B1079837
theorem B621647 : Blo 183802 621647 := bstep (se 1 (by rfl) ⟨466235, by rfl⟩ : syracuseStep 621647 = 932471) B932471
theorem B588953 : Blo 183802 588953 := bstep (se 2 (by rfl) ⟨220857, by rfl⟩ : syracuseStep 588953 = 441715) B441715
theorem B1047755 : Blo 183802 1047755 := bstep (se 1 (by rfl) ⟨785816, by rfl⟩ : syracuseStep 1047755 = 1571633) B1571633
theorem B622025 : Blo 183802 622025 := bstep (se 2 (by rfl) ⟨233259, by rfl⟩ : syracuseStep 622025 = 466519) B466519
theorem B589351 : Blo 183802 589351 := bstep (se 1 (by rfl) ⟨442013, by rfl⟩ : syracuseStep 589351 = 884027) B884027
theorem B3538565 : Blo 183802 3538565 := bstep (se 4 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 3538565 = 663481) B663481
theorem B1212043 : Blo 183802 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B1048211 : Blo 183802 1048211 := bstep (se 1 (by rfl) ⟨786158, by rfl⟩ : syracuseStep 1048211 = 1572317) B1572317
theorem B622295 : Blo 183802 622295 := bstep (se 1 (by rfl) ⟨466721, by rfl⟩ : syracuseStep 622295 = 933443) B933443
theorem B753569 : Blo 183802 753569 := bstep (se 2 (by rfl) ⟨282588, by rfl⟩ : syracuseStep 753569 = 565177) B565177
theorem B622511 : Blo 183802 622511 := bstep (se 1 (by rfl) ⟨466883, by rfl⟩ : syracuseStep 622511 = 933767) B933767
theorem B950291 : Blo 183802 950291 := bstep (se 1 (by rfl) ⟨712718, by rfl⟩ : syracuseStep 950291 = 1425437) B1425437
theorem B1048627 : Blo 183802 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B2392217 : Blo 183802 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B2130137 : Blo 183802 2130137 := bstep (se 2 (by rfl) ⟨798801, by rfl⟩ : syracuseStep 2130137 = 1597603) B1597603
theorem B623105 : Blo 183802 623105 := bstep (se 2 (by rfl) ⟨233664, by rfl⟩ : syracuseStep 623105 = 467329) B467329
theorem B524971 : Blo 183802 524971 := bstep (se 1 (by rfl) ⟨393728, by rfl⟩ : syracuseStep 524971 = 787457) B787457
theorem B394139 : Blo 183802 394139 := bstep (se 1 (by rfl) ⟨295604, by rfl⟩ : syracuseStep 394139 = 591209) B591209
theorem B820187 : Blo 183802 820187 := bstep (se 1 (by rfl) ⟨615140, by rfl⟩ : syracuseStep 820187 = 1230281) B1230281
theorem B623591 : Blo 183802 623591 := bstep (se 1 (by rfl) ⟨467693, by rfl⟩ : syracuseStep 623591 = 935387) B935387
theorem B623915 : Blo 183802 623915 := bstep (se 1 (by rfl) ⟨467936, by rfl⟩ : syracuseStep 623915 = 935873) B935873
theorem B787799 : Blo 183802 787799 := bstep (se 1 (by rfl) ⟨590849, by rfl⟩ : syracuseStep 787799 = 1181699) B1181699
theorem B1082747 : Blo 183802 1082747 := bstep (se 1 (by rfl) ⟨812060, by rfl⟩ : syracuseStep 1082747 = 1624121) B1624121
theorem B624185 : Blo 183802 624185 := bstep (se 2 (by rfl) ⟨234069, by rfl⟩ : syracuseStep 624185 = 468139) B468139
theorem B20514455 : Blo 183802 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B395113 : Blo 183802 395113 := bstep (se 2 (by rfl) ⟨148167, by rfl⟩ : syracuseStep 395113 = 296335) B296335
theorem B591823 : Blo 183802 591823 := bstep (se 1 (by rfl) ⟨443867, by rfl⟩ : syracuseStep 591823 = 887735) B887735
theorem B1476559 : Blo 183802 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B3606605 : Blo 183802 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B395369 : Blo 183802 395369 := bstep (se 2 (by rfl) ⟨148263, by rfl⟩ : syracuseStep 395369 = 296527) B296527
theorem B297065 : Blo 183802 297065 := bstep (se 2 (by rfl) ⟨111399, by rfl⟩ : syracuseStep 297065 = 222799) B222799
theorem B526601 : Blo 183802 526601 := bstep (se 2 (by rfl) ⟨197475, by rfl⟩ : syracuseStep 526601 = 394951) B394951
theorem B264559 : Blo 183802 264559 := bstep (se 1 (by rfl) ⟨198419, by rfl⟩ : syracuseStep 264559 = 396839) B396839
theorem B625427 : Blo 183802 625427 := bstep (se 1 (by rfl) ⟨469070, by rfl⟩ : syracuseStep 625427 = 938141) B938141
theorem B1182599 : Blo 183802 1182599 := bstep (se 1 (by rfl) ⟨886949, by rfl⟩ : syracuseStep 1182599 = 1773899) B1773899
theorem B1412315 : Blo 183802 1412315 := bstep (se 1 (by rfl) ⟨1059236, by rfl⟩ : syracuseStep 1412315 = 2118473) B2118473
theorem B593183 : Blo 183802 593183 := bstep (se 1 (by rfl) ⟨444887, by rfl⟩ : syracuseStep 593183 = 889775) B889775
theorem B396667 : Blo 183802 396667 := bstep (se 1 (by rfl) ⟨297500, by rfl⟩ : syracuseStep 396667 = 595001) B595001
theorem B626291 : Blo 183802 626291 := bstep (se 1 (by rfl) ⟨469718, by rfl⟩ : syracuseStep 626291 = 939437) B939437
theorem B2133715 : Blo 183802 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B626561 : Blo 183802 626561 := bstep (se 2 (by rfl) ⟨234960, by rfl⟩ : syracuseStep 626561 = 469921) B469921
theorem B233371 : Blo 183802 233371 := bstep (se 1 (by rfl) ⟨175028, by rfl⟩ : syracuseStep 233371 = 350057) B350057
theorem B528731 : Blo 183802 528731 := bstep (se 1 (by rfl) ⟨396548, by rfl⟩ : syracuseStep 528731 = 793097) B793097
theorem B627371 : Blo 183802 627371 := bstep (se 1 (by rfl) ⟨470528, by rfl⟩ : syracuseStep 627371 = 941057) B941057
theorem B398375 : Blo 183802 398375 := bstep (se 1 (by rfl) ⟨298781, by rfl⟩ : syracuseStep 398375 = 597563) B597563
theorem B398479 : Blo 183802 398479 := bstep (se 1 (by rfl) ⟨298859, by rfl⟩ : syracuseStep 398479 = 597719) B597719
theorem B627911 : Blo 183802 627911 := bstep (se 1 (by rfl) ⟨470933, by rfl⟩ : syracuseStep 627911 = 941867) B941867
theorem B235867 : Blo 183802 235867 := bstep (se 1 (by rfl) ⟨176900, by rfl⟩ : syracuseStep 235867 = 353801) B353801
theorem B465335 : Blo 183802 465335 := bstep (se 1 (by rfl) ⟨349001, by rfl⟩ : syracuseStep 465335 = 698003) B698003
theorem B1055227 : Blo 183802 1055227 := bstep (se 1 (by rfl) ⟨791420, by rfl⟩ : syracuseStep 1055227 = 1582841) B1582841
theorem B629423 : Blo 183802 629423 := bstep (se 1 (by rfl) ⟨472067, by rfl⟩ : syracuseStep 629423 = 944135) B944135
theorem B531191 : Blo 183802 531191 := bstep (se 1 (by rfl) ⟨398393, by rfl⟩ : syracuseStep 531191 = 796787) B796787
theorem B891773 : Blo 183802 891773 := bstep (se 3 (by rfl) ⟨167207, by rfl⟩ : syracuseStep 891773 = 334415) B334415
theorem B3840953 : Blo 183802 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B629747 : Blo 183802 629747 := bstep (se 1 (by rfl) ⟨472310, by rfl⟩ : syracuseStep 629747 = 944621) B944621
theorem B236839 : Blo 183802 236839 := bstep (se 1 (by rfl) ⟨177629, by rfl⟩ : syracuseStep 236839 = 355259) B355259
theorem B597385 : Blo 183802 597385 := bstep (se 2 (by rfl) ⟨224019, by rfl⟩ : syracuseStep 597385 = 448039) B448039
theorem B466337 : Blo 183802 466337 := bstep (se 2 (by rfl) ⟨174876, by rfl⟩ : syracuseStep 466337 = 349753) B349753
theorem B630287 : Blo 183802 630287 := bstep (se 1 (by rfl) ⟨472715, by rfl⟩ : syracuseStep 630287 = 945431) B945431
theorem B237163 : Blo 183802 237163 := bstep (se 1 (by rfl) ⟨177872, by rfl⟩ : syracuseStep 237163 = 355745) B355745
theorem B663149 : Blo 183802 663149 := bstep (se 3 (by rfl) ⟨124340, by rfl⟩ : syracuseStep 663149 = 248681) B248681
theorem B237367 : Blo 183802 237367 := bstep (se 1 (by rfl) ⟨178025, by rfl⟩ : syracuseStep 237367 = 356051) B356051
theorem B466793 : Blo 183802 466793 := bstep (se 2 (by rfl) ⟨175047, by rfl⟩ : syracuseStep 466793 = 350095) B350095
theorem B2105351 : Blo 183802 2105351 := bstep (se 1 (by rfl) ⟨1579013, by rfl⟩ : syracuseStep 2105351 = 3158027) B3158027
theorem B1581065 : Blo 183802 1581065 := bstep (se 2 (by rfl) ⟨592899, by rfl⟩ : syracuseStep 1581065 = 1185799) B1185799
theorem B532489 : Blo 183802 532489 := bstep (se 2 (by rfl) ⟨199683, by rfl⟩ : syracuseStep 532489 = 399367) B399367
theorem B598547 : Blo 183802 598547 := bstep (se 1 (by rfl) ⟨448910, by rfl⟩ : syracuseStep 598547 = 897821) B897821
theorem B631367 : Blo 183802 631367 := bstep (se 1 (by rfl) ⟨473525, by rfl⟩ : syracuseStep 631367 = 947051) B947051
theorem B336491 : Blo 183802 336491 := bstep (se 1 (by rfl) ⟨252368, by rfl⟩ : syracuseStep 336491 = 504737) B504737
theorem B631799 : Blo 183802 631799 := bstep (se 1 (by rfl) ⟨473849, by rfl⟩ : syracuseStep 631799 = 947699) B947699
theorem B533719 : Blo 183802 533719 := bstep (se 1 (by rfl) ⟨400289, by rfl⟩ : syracuseStep 533719 = 800579) B800579
theorem B534073 : Blo 183802 534073 := bstep (se 2 (by rfl) ⟨200277, by rfl⟩ : syracuseStep 534073 = 400555) B400555
theorem B468575 : Blo 183802 468575 := bstep (se 1 (by rfl) ⟨351431, by rfl⟩ : syracuseStep 468575 = 702863) B702863
theorem B2991953 : Blo 183802 2991953 := bstep (se 2 (by rfl) ⟨1121982, by rfl⟩ : syracuseStep 2991953 = 2243965) B2243965
theorem B632663 : Blo 183802 632663 := bstep (se 1 (by rfl) ⟨474497, by rfl⟩ : syracuseStep 632663 = 948995) B948995
theorem B1845125 : Blo 183802 1845125 := bstep (se 4 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 1845125 = 345961) B345961
theorem B403465 : Blo 183802 403465 := bstep (se 2 (by rfl) ⟨151299, by rfl⟩ : syracuseStep 403465 = 302599) B302599
theorem B698503 : Blo 183802 698503 := bstep (se 1 (by rfl) ⟨523877, by rfl⟩ : syracuseStep 698503 = 1047755) B1047755
theorem B1616057 : Blo 183802 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B207067 : Blo 183802 207067 := bstep (se 1 (by rfl) ⟨155300, by rfl⟩ : syracuseStep 207067 = 310601) B310601
theorem B469273 : Blo 183802 469273 := bstep (se 2 (by rfl) ⟨175977, by rfl⟩ : syracuseStep 469273 = 351955) B351955
theorem B1059101 : Blo 183802 1059101 := bstep (se 3 (by rfl) ⟨198581, by rfl⟩ : syracuseStep 1059101 = 397163) B397163
theorem B469415 : Blo 183802 469415 := bstep (se 1 (by rfl) ⟨352061, by rfl⟩ : syracuseStep 469415 = 704123) B704123
theorem B698807 : Blo 183802 698807 := bstep (se 1 (by rfl) ⟨524105, by rfl⟩ : syracuseStep 698807 = 1048211) B1048211
theorem B1911251 : Blo 183802 1911251 := bstep (se 1 (by rfl) ⟨1433438, by rfl⟩ : syracuseStep 1911251 = 2866877) B2866877
theorem B207355 : Blo 183802 207355 := bstep (se 1 (by rfl) ⟨155516, by rfl⟩ : syracuseStep 207355 = 311033) B311033
theorem B469577 : Blo 183802 469577 := bstep (se 2 (by rfl) ⟨176091, by rfl⟩ : syracuseStep 469577 = 352183) B352183
theorem B502379 : Blo 183802 502379 := bstep (se 1 (by rfl) ⟨376784, by rfl⟩ : syracuseStep 502379 = 753569) B753569
theorem B797359 : Blo 183802 797359 := bstep (se 1 (by rfl) ⟨598019, by rfl⟩ : syracuseStep 797359 = 1196039) B1196039
theorem B207535 : Blo 183802 207535 := bstep (se 1 (by rfl) ⟨155651, by rfl⟩ : syracuseStep 207535 = 311303) B311303
theorem B961303 : Blo 183802 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B633743 : Blo 183802 633743 := bstep (se 1 (by rfl) ⟨475307, by rfl⟩ : syracuseStep 633743 = 950615) B950615
theorem B207823 : Blo 183802 207823 := bstep (se 1 (by rfl) ⟨155867, by rfl⟩ : syracuseStep 207823 = 311735) B311735
theorem B535691 : Blo 183802 535691 := bstep (se 1 (by rfl) ⟨401768, by rfl⟩ : syracuseStep 535691 = 803537) B803537
theorem B1191131 : Blo 183802 1191131 := bstep (se 1 (by rfl) ⟨893348, by rfl⟩ : syracuseStep 1191131 = 1786697) B1786697
theorem B601307 : Blo 183802 601307 := bstep (se 1 (by rfl) ⟨450980, by rfl⟩ : syracuseStep 601307 = 901961) B901961
theorem B1060127 : Blo 183802 1060127 := bstep (se 1 (by rfl) ⟨795095, by rfl⟩ : syracuseStep 1060127 = 1590191) B1590191
theorem B208219 : Blo 183802 208219 := bstep (se 1 (by rfl) ⟨156164, by rfl⟩ : syracuseStep 208219 = 312329) B312329
theorem B1584481 : Blo 183802 1584481 := bstep (se 2 (by rfl) ⟨594180, by rfl⟩ : syracuseStep 1584481 = 1188361) B1188361
theorem B10136951 : Blo 183802 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B208327 : Blo 183802 208327 := bstep (se 1 (by rfl) ⟨156245, by rfl⟩ : syracuseStep 208327 = 312491) B312491
theorem B2272967 : Blo 183802 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B208687 : Blo 183802 208687 := bstep (se 1 (by rfl) ⟨156515, by rfl⟩ : syracuseStep 208687 = 313031) B313031
theorem B208795 : Blo 183802 208795 := bstep (se 1 (by rfl) ⟨156596, by rfl⟩ : syracuseStep 208795 = 313193) B313193
theorem B209191 : Blo 183802 209191 := bstep (se 1 (by rfl) ⟨156893, by rfl⟩ : syracuseStep 209191 = 313787) B313787
theorem B209263 : Blo 183802 209263 := bstep (se 1 (by rfl) ⟨156947, by rfl⟩ : syracuseStep 209263 = 313895) B313895
theorem B471521 : Blo 183802 471521 := bstep (se 2 (by rfl) ⟨176820, by rfl⟩ : syracuseStep 471521 = 353641) B353641
theorem B2863667 : Blo 183802 2863667 := bstep (se 1 (by rfl) ⟨2147750, by rfl⟩ : syracuseStep 2863667 = 4295501) B4295501
theorem B209479 : Blo 183802 209479 := bstep (se 1 (by rfl) ⟨157109, by rfl⟩ : syracuseStep 209479 = 314219) B314219
theorem B1585817 : Blo 183802 1585817 := bstep (se 2 (by rfl) ⟨594681, by rfl⟩ : syracuseStep 1585817 = 1189363) B1189363
theorem B930527 : Blo 183802 930527 := bstep (se 1 (by rfl) ⟨697895, by rfl⟩ : syracuseStep 930527 = 1395791) B1395791
theorem B1618717 : Blo 183802 1618717 := bstep (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) B607019
theorem B308047 : Blo 183802 308047 := bstep (se 1 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 308047 = 462071) B462071
theorem B472027 : Blo 183802 472027 := bstep (se 1 (by rfl) ⟨354020, by rfl⟩ : syracuseStep 472027 = 708041) B708041
theorem B570359 : Blo 183802 570359 := bstep (se 1 (by rfl) ⟨427769, by rfl⟩ : syracuseStep 570359 = 855539) B855539
theorem B668915 : Blo 183802 668915 := bstep (se 1 (by rfl) ⟨501686, by rfl⟩ : syracuseStep 668915 = 1003373) B1003373
theorem B472351 : Blo 183802 472351 := bstep (se 1 (by rfl) ⟨354263, by rfl⟩ : syracuseStep 472351 = 708527) B708527
theorem B275849 : Blo 183802 275849 := bstep (se 2 (by rfl) ⟨103443, by rfl⟩ : syracuseStep 275849 = 206887) B206887
theorem B210343 : Blo 183802 210343 := bstep (se 1 (by rfl) ⟨157757, by rfl⟩ : syracuseStep 210343 = 315515) B315515
theorem B276203 : Blo 183802 276203 := bstep (se 1 (by rfl) ⟨207152, by rfl⟩ : syracuseStep 276203 = 414305) B414305
theorem B3389303 : Blo 183802 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B276431 : Blo 183802 276431 := bstep (se 1 (by rfl) ⟨207323, by rfl⟩ : syracuseStep 276431 = 414647) B414647
theorem B210919 : Blo 183802 210919 := bstep (se 1 (by rfl) ⟨158189, by rfl⟩ : syracuseStep 210919 = 316379) B316379
theorem B899267 : Blo 183802 899267 := bstep (se 1 (by rfl) ⟨674450, by rfl⟩ : syracuseStep 899267 = 1348901) B1348901
theorem B276827 : Blo 183802 276827 := bstep (se 1 (by rfl) ⟨207620, by rfl⟩ : syracuseStep 276827 = 415241) B415241
theorem B375131 : Blo 183802 375131 := bstep (se 1 (by rfl) ⟨281348, by rfl⟩ : syracuseStep 375131 = 562697) B562697
theorem B473435 : Blo 183802 473435 := bstep (se 1 (by rfl) ⟨355076, by rfl⟩ : syracuseStep 473435 = 710153) B710153
theorem B277055 : Blo 183802 277055 := bstep (se 1 (by rfl) ⟨207791, by rfl⟩ : syracuseStep 277055 = 415583) B415583
theorem B1423979 : Blo 183802 1423979 := bstep (se 1 (by rfl) ⟨1067984, by rfl⟩ : syracuseStep 1423979 = 2135969) B2135969
theorem B473771 : Blo 183802 473771 := bstep (se 1 (by rfl) ⟨355328, by rfl⟩ : syracuseStep 473771 = 710657) B710657
theorem B703151 : Blo 183802 703151 := bstep (se 1 (by rfl) ⟨527363, by rfl⟩ : syracuseStep 703151 = 1054727) B1054727
theorem B277175 : Blo 183802 277175 := bstep (se 1 (by rfl) ⟨207881, by rfl⟩ : syracuseStep 277175 = 415763) B415763
theorem B670589 : Blo 183802 670589 := bstep (se 3 (by rfl) ⟨125735, by rfl⟩ : syracuseStep 670589 = 251471) B251471
theorem B277403 : Blo 183802 277403 := bstep (se 1 (by rfl) ⟨208052, by rfl⟩ : syracuseStep 277403 = 416105) B416105
theorem B605099 : Blo 183802 605099 := bstep (se 1 (by rfl) ⟨453824, by rfl⟩ : syracuseStep 605099 = 907649) B907649
theorem B932795 : Blo 183802 932795 := bstep (se 1 (by rfl) ⟨699596, by rfl⟩ : syracuseStep 932795 = 1399193) B1399193
theorem B2505779 : Blo 183802 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B310567 : Blo 183802 310567 := bstep (se 1 (by rfl) ⟨232925, by rfl⟩ : syracuseStep 310567 = 465851) B465851
theorem B277799 : Blo 183802 277799 := bstep (se 1 (by rfl) ⟨208349, by rfl⟩ : syracuseStep 277799 = 416699) B416699
theorem B474407 : Blo 183802 474407 := bstep (se 1 (by rfl) ⟨355805, by rfl⟩ : syracuseStep 474407 = 711611) B711611
theorem B277883 : Blo 183802 277883 := bstep (se 1 (by rfl) ⟨208412, by rfl⟩ : syracuseStep 277883 = 416825) B416825
theorem B278009 : Blo 183802 278009 := bstep (se 2 (by rfl) ⟨104253, by rfl⟩ : syracuseStep 278009 = 208507) B208507
theorem B2866747 : Blo 183802 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B278111 : Blo 183802 278111 := bstep (se 1 (by rfl) ⟨208583, by rfl⟩ : syracuseStep 278111 = 417167) B417167
theorem B1916531 : Blo 183802 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B442043 : Blo 183802 442043 := bstep (se 1 (by rfl) ⟨331532, by rfl⟩ : syracuseStep 442043 = 663065) B663065
theorem B311087 : Blo 183802 311087 := bstep (se 1 (by rfl) ⟨233315, by rfl⟩ : syracuseStep 311087 = 466631) B466631
theorem B278327 : Blo 183802 278327 := bstep (se 1 (by rfl) ⟨208745, by rfl⟩ : syracuseStep 278327 = 417491) B417491
theorem B1523731 : Blo 183802 1523731 := bstep (se 1 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 1523731 = 2285597) B2285597
theorem B278633 : Blo 183802 278633 := bstep (se 2 (by rfl) ⟨104487, by rfl⟩ : syracuseStep 278633 = 208975) B208975
theorem B934091 : Blo 183802 934091 := bstep (se 1 (by rfl) ⟨700568, by rfl⟩ : syracuseStep 934091 = 1401137) B1401137
theorem B278951 : Blo 183802 278951 := bstep (se 1 (by rfl) ⟨209213, by rfl⟩ : syracuseStep 278951 = 418427) B418427
theorem B377255 : Blo 183802 377255 := bstep (se 1 (by rfl) ⟨282941, by rfl⟩ : syracuseStep 377255 = 565883) B565883
theorem B279035 : Blo 183802 279035 := bstep (se 1 (by rfl) ⟨209276, by rfl⟩ : syracuseStep 279035 = 418553) B418553
theorem B1065473 : Blo 183802 1065473 := bstep (se 2 (by rfl) ⟨399552, by rfl⟩ : syracuseStep 1065473 = 799105) B799105
theorem B705095 : Blo 183802 705095 := bstep (se 1 (by rfl) ⟨528821, by rfl⟩ : syracuseStep 705095 = 1057643) B1057643
theorem B279161 : Blo 183802 279161 := bstep (se 2 (by rfl) ⟨104685, by rfl⟩ : syracuseStep 279161 = 209371) B209371
theorem B279215 : Blo 183802 279215 := bstep (se 1 (by rfl) ⟨209411, by rfl⟩ : syracuseStep 279215 = 418823) B418823
theorem B279263 : Blo 183802 279263 := bstep (se 1 (by rfl) ⟨209447, by rfl⟩ : syracuseStep 279263 = 418895) B418895
theorem B1262567 : Blo 183802 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B312295 : Blo 183802 312295 := bstep (se 1 (by rfl) ⟨234221, by rfl⟩ : syracuseStep 312295 = 468443) B468443
theorem B279527 : Blo 183802 279527 := bstep (se 1 (by rfl) ⟨209645, by rfl⟩ : syracuseStep 279527 = 419291) B419291
theorem B1065959 : Blo 183802 1065959 := bstep (se 1 (by rfl) ⟨799469, by rfl⟩ : syracuseStep 1065959 = 1598939) B1598939
theorem B279785 : Blo 183802 279785 := bstep (se 2 (by rfl) ⟨104919, by rfl⟩ : syracuseStep 279785 = 209839) B209839
theorem B705779 : Blo 183802 705779 := bstep (se 1 (by rfl) ⟨529334, by rfl⟩ : syracuseStep 705779 = 1058669) B1058669
theorem B279839 : Blo 183802 279839 := bstep (se 1 (by rfl) ⟨209879, by rfl⟩ : syracuseStep 279839 = 419759) B419759
theorem B1262891 : Blo 183802 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B2377133 : Blo 183802 2377133 := bstep (se 3 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 2377133 = 891425) B891425
theorem B280007 : Blo 183802 280007 := bstep (se 1 (by rfl) ⟨210005, by rfl⟩ : syracuseStep 280007 = 420011) B420011
theorem B444167 : Blo 183802 444167 := bstep (se 1 (by rfl) ⟨333125, by rfl⟩ : syracuseStep 444167 = 666251) B666251
theorem B280361 : Blo 183802 280361 := bstep (se 2 (by rfl) ⟨105135, by rfl⟩ : syracuseStep 280361 = 210271) B210271
theorem B280367 : Blo 183802 280367 := bstep (se 1 (by rfl) ⟨210275, by rfl⟩ : syracuseStep 280367 = 420551) B420551
theorem B1001297 : Blo 183802 1001297 := bstep (se 2 (by rfl) ⟨375486, by rfl⟩ : syracuseStep 1001297 = 750973) B750973
theorem B3000199 : Blo 183802 3000199 := bstep (se 1 (by rfl) ⟨2250149, by rfl⟩ : syracuseStep 3000199 = 4500299) B4500299
theorem B280841 : Blo 183802 280841 := bstep (se 2 (by rfl) ⟨105315, by rfl⟩ : syracuseStep 280841 = 210631) B210631
theorem B1591589 : Blo 183802 1591589 := bstep (se 4 (by rfl) ⟨149211, by rfl⟩ : syracuseStep 1591589 = 298423) B298423
theorem B280943 : Blo 183802 280943 := bstep (se 1 (by rfl) ⟨210707, by rfl⟩ : syracuseStep 280943 = 421415) B421415
theorem B936359 : Blo 183802 936359 := bstep (se 1 (by rfl) ⟨702269, by rfl⟩ : syracuseStep 936359 = 1404539) B1404539
theorem B281159 : Blo 183802 281159 := bstep (se 1 (by rfl) ⟨210869, by rfl⟩ : syracuseStep 281159 = 421739) B421739
theorem B936521 : Blo 183802 936521 := bstep (se 2 (by rfl) ⟨351195, by rfl⟩ : syracuseStep 936521 = 702391) B702391
theorem B281195 : Blo 183802 281195 := bstep (se 1 (by rfl) ⟨210896, by rfl⟩ : syracuseStep 281195 = 421793) B421793
theorem B1198871 : Blo 183802 1198871 := bstep (se 1 (by rfl) ⟨899153, by rfl⟩ : syracuseStep 1198871 = 1798307) B1798307
theorem B281423 : Blo 183802 281423 := bstep (se 1 (by rfl) ⟨211067, by rfl⟩ : syracuseStep 281423 = 422135) B422135
theorem B707723 : Blo 183802 707723 := bstep (se 1 (by rfl) ⟨530792, by rfl⟩ : syracuseStep 707723 = 1061585) B1061585
theorem B1068349 : Blo 183802 1068349 := bstep (se 3 (by rfl) ⟨200315, by rfl⟩ : syracuseStep 1068349 = 400631) B400631
theorem B183803 : Blo 183802 183803 := bstep (se 1 (by rfl) ⟨137852, by rfl⟩ : syracuseStep 183803 = 275705) B275705
theorem B183871 : Blo 183802 183871 := bstep (se 1 (by rfl) ⟨137903, by rfl⟩ : syracuseStep 183871 = 275807) B275807
theorem B183879 : Blo 183802 183879 := bstep (se 1 (by rfl) ⟨137909, by rfl⟩ : syracuseStep 183879 = 275819) B275819
theorem B314975 : Blo 183802 314975 := bstep (se 1 (by rfl) ⟨236231, by rfl⟩ : syracuseStep 314975 = 472463) B472463
theorem B184031 : Blo 183802 184031 := bstep (se 1 (by rfl) ⟨138023, by rfl⟩ : syracuseStep 184031 = 276047) B276047
theorem B184111 : Blo 183802 184111 := bstep (se 1 (by rfl) ⟨138083, by rfl⟩ : syracuseStep 184111 = 276167) B276167
theorem B315191 : Blo 183802 315191 := bstep (se 1 (by rfl) ⟨236393, by rfl⟩ : syracuseStep 315191 = 472787) B472787
theorem B184219 : Blo 183802 184219 := bstep (se 1 (by rfl) ⟨138164, by rfl⟩ : syracuseStep 184219 = 276329) B276329
theorem B184271 : Blo 183802 184271 := bstep (se 1 (by rfl) ⟨138203, by rfl⟩ : syracuseStep 184271 = 276407) B276407
theorem B184295 : Blo 183802 184295 := bstep (se 1 (by rfl) ⟨138221, by rfl⟩ : syracuseStep 184295 = 276443) B276443
theorem B1364035 : Blo 183802 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B413801 : Blo 183802 413801 := bstep (se 2 (by rfl) ⟨155175, by rfl⟩ : syracuseStep 413801 = 310351) B310351
theorem B184607 : Blo 183802 184607 := bstep (se 1 (by rfl) ⟨138455, by rfl⟩ : syracuseStep 184607 = 276911) B276911
theorem B250151 : Blo 183802 250151 := bstep (se 1 (by rfl) ⟨187613, by rfl⟩ : syracuseStep 250151 = 375227) B375227
theorem B184667 : Blo 183802 184667 := bstep (se 1 (by rfl) ⟨138500, by rfl⟩ : syracuseStep 184667 = 277001) B277001
theorem B184687 : Blo 183802 184687 := bstep (se 1 (by rfl) ⟨138515, by rfl⟩ : syracuseStep 184687 = 277031) B277031
theorem B184743 : Blo 183802 184743 := bstep (se 1 (by rfl) ⟨138557, by rfl⟩ : syracuseStep 184743 = 277115) B277115
theorem B938465 : Blo 183802 938465 := bstep (se 2 (by rfl) ⟨351924, by rfl⟩ : syracuseStep 938465 = 703849) B703849
theorem B184827 : Blo 183802 184827 := bstep (se 1 (by rfl) ⟨138620, by rfl⟩ : syracuseStep 184827 = 277241) B277241
theorem B184895 : Blo 183802 184895 := bstep (se 1 (by rfl) ⟨138671, by rfl⟩ : syracuseStep 184895 = 277343) B277343
theorem B315967 : Blo 183802 315967 := bstep (se 1 (by rfl) ⟨236975, by rfl⟩ : syracuseStep 315967 = 473951) B473951
theorem B184903 : Blo 183802 184903 := bstep (se 1 (by rfl) ⟨138677, by rfl⟩ : syracuseStep 184903 = 277355) B277355
theorem B414287 : Blo 183802 414287 := bstep (se 1 (by rfl) ⟨310715, by rfl⟩ : syracuseStep 414287 = 621431) B621431
theorem B479927 : Blo 183802 479927 := bstep (se 1 (by rfl) ⟨359945, by rfl⟩ : syracuseStep 479927 = 719891) B719891
theorem B414431 : Blo 183802 414431 := bstep (se 1 (by rfl) ⟨310823, by rfl⟩ : syracuseStep 414431 = 621647) B621647
theorem B185055 : Blo 183802 185055 := bstep (se 1 (by rfl) ⟨138791, by rfl⟩ : syracuseStep 185055 = 277583) B277583
theorem B185135 : Blo 183802 185135 := bstep (se 1 (by rfl) ⟨138851, by rfl⟩ : syracuseStep 185135 = 277703) B277703
theorem B185243 : Blo 183802 185243 := bstep (se 1 (by rfl) ⟨138932, by rfl⟩ : syracuseStep 185243 = 277865) B277865
theorem B185295 : Blo 183802 185295 := bstep (se 1 (by rfl) ⟨138971, by rfl⟩ : syracuseStep 185295 = 277943) B277943
theorem B414683 : Blo 183802 414683 := bstep (se 1 (by rfl) ⟨311012, by rfl⟩ : syracuseStep 414683 = 622025) B622025
theorem B185319 : Blo 183802 185319 := bstep (se 1 (by rfl) ⟨138989, by rfl⟩ : syracuseStep 185319 = 277979) B277979
theorem B5690387 : Blo 183802 5690387 := bstep (se 1 (by rfl) ⟨4267790, by rfl⟩ : syracuseStep 5690387 = 8535581) B8535581
theorem B414863 : Blo 183802 414863 := bstep (se 1 (by rfl) ⟨311147, by rfl⟩ : syracuseStep 414863 = 622295) B622295
theorem B414953 : Blo 183802 414953 := bstep (se 2 (by rfl) ⟨155607, by rfl⟩ : syracuseStep 414953 = 311215) B311215
theorem B316649 : Blo 183802 316649 := bstep (se 2 (by rfl) ⟨118743, by rfl⟩ : syracuseStep 316649 = 237487) B237487
theorem B415007 : Blo 183802 415007 := bstep (se 1 (by rfl) ⟨311255, by rfl⟩ : syracuseStep 415007 = 622511) B622511
theorem B185631 : Blo 183802 185631 := bstep (se 1 (by rfl) ⟨139223, by rfl⟩ : syracuseStep 185631 = 278447) B278447
theorem B316703 : Blo 183802 316703 := bstep (se 1 (by rfl) ⟨237527, by rfl⟩ : syracuseStep 316703 = 475055) B475055
theorem B185691 : Blo 183802 185691 := bstep (se 1 (by rfl) ⟨139268, by rfl⟩ : syracuseStep 185691 = 278537) B278537
theorem B185711 : Blo 183802 185711 := bstep (se 1 (by rfl) ⟨139283, by rfl⟩ : syracuseStep 185711 = 278567) B278567
theorem B447905 : Blo 183802 447905 := bstep (se 2 (by rfl) ⟨167964, by rfl⟩ : syracuseStep 447905 = 335929) B335929
theorem B185767 : Blo 183802 185767 := bstep (se 1 (by rfl) ⟨139325, by rfl⟩ : syracuseStep 185767 = 278651) B278651
theorem B447943 : Blo 183802 447943 := bstep (se 1 (by rfl) ⟨335957, by rfl⟩ : syracuseStep 447943 = 671915) B671915
theorem B185851 : Blo 183802 185851 := bstep (se 1 (by rfl) ⟨139388, by rfl⟩ : syracuseStep 185851 = 278777) B278777
theorem B185919 : Blo 183802 185919 := bstep (se 1 (by rfl) ⟨139439, by rfl⟩ : syracuseStep 185919 = 278879) B278879
theorem B185927 : Blo 183802 185927 := bstep (se 1 (by rfl) ⟨139445, by rfl⟩ : syracuseStep 185927 = 278891) B278891
theorem B186079 : Blo 183802 186079 := bstep (se 1 (by rfl) ⟨139559, by rfl⟩ : syracuseStep 186079 = 279119) B279119
theorem B415529 : Blo 183802 415529 := bstep (se 2 (by rfl) ⟨155823, by rfl⟩ : syracuseStep 415529 = 311647) B311647
theorem B186159 : Blo 183802 186159 := bstep (se 1 (by rfl) ⟨139619, by rfl⟩ : syracuseStep 186159 = 279239) B279239
theorem B186267 : Blo 183802 186267 := bstep (se 1 (by rfl) ⟨139700, by rfl⟩ : syracuseStep 186267 = 279401) B279401
theorem B186319 : Blo 183802 186319 := bstep (se 1 (by rfl) ⟨139739, by rfl⟩ : syracuseStep 186319 = 279479) B279479
theorem B186343 : Blo 183802 186343 := bstep (se 1 (by rfl) ⟨139757, by rfl⟩ : syracuseStep 186343 = 279515) B279515
theorem B1792043 : Blo 183802 1792043 := bstep (se 1 (by rfl) ⟨1344032, by rfl⟩ : syracuseStep 1792043 = 2688065) B2688065
theorem B645385 : Blo 183802 645385 := bstep (se 2 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 645385 = 484039) B484039
theorem B186655 : Blo 183802 186655 := bstep (se 1 (by rfl) ⟨139991, by rfl⟩ : syracuseStep 186655 = 279983) B279983
theorem B186715 : Blo 183802 186715 := bstep (se 1 (by rfl) ⟨140036, by rfl⟩ : syracuseStep 186715 = 280073) B280073
theorem B186735 : Blo 183802 186735 := bstep (se 1 (by rfl) ⟨140051, by rfl⟩ : syracuseStep 186735 = 280103) B280103
theorem B186791 : Blo 183802 186791 := bstep (se 1 (by rfl) ⟨140093, by rfl⟩ : syracuseStep 186791 = 280187) B280187
theorem B285095 : Blo 183802 285095 := bstep (se 1 (by rfl) ⟨213821, by rfl⟩ : syracuseStep 285095 = 427643) B427643
theorem B186875 : Blo 183802 186875 := bstep (se 1 (by rfl) ⟨140156, by rfl⟩ : syracuseStep 186875 = 280313) B280313
theorem B1595963 : Blo 183802 1595963 := bstep (se 1 (by rfl) ⟨1196972, by rfl⟩ : syracuseStep 1595963 = 2393945) B2393945
theorem B186943 : Blo 183802 186943 := bstep (se 1 (by rfl) ⟨140207, by rfl⟩ : syracuseStep 186943 = 280415) B280415
theorem B186951 : Blo 183802 186951 := bstep (se 1 (by rfl) ⟨140213, by rfl⟩ : syracuseStep 186951 = 280427) B280427
theorem B940733 : Blo 183802 940733 := bstep (se 3 (by rfl) ⟨176387, by rfl⟩ : syracuseStep 940733 = 352775) B352775
theorem B187103 : Blo 183802 187103 := bstep (se 1 (by rfl) ⟨140327, by rfl⟩ : syracuseStep 187103 = 280655) B280655
theorem B711443 : Blo 183802 711443 := bstep (se 1 (by rfl) ⟨533582, by rfl⟩ : syracuseStep 711443 = 1067165) B1067165
theorem B187183 : Blo 183802 187183 := bstep (se 1 (by rfl) ⟨140387, by rfl⟩ : syracuseStep 187183 = 280775) B280775
theorem B416591 : Blo 183802 416591 := bstep (se 1 (by rfl) ⟨312443, by rfl⟩ : syracuseStep 416591 = 624887) B624887
theorem B187291 : Blo 183802 187291 := bstep (se 1 (by rfl) ⟨140468, by rfl⟩ : syracuseStep 187291 = 280937) B280937
theorem B187343 : Blo 183802 187343 := bstep (se 1 (by rfl) ⟨140507, by rfl⟩ : syracuseStep 187343 = 281015) B281015
theorem B187367 : Blo 183802 187367 := bstep (se 1 (by rfl) ⟨140525, by rfl⟩ : syracuseStep 187367 = 281051) B281051
theorem B416807 : Blo 183802 416807 := bstep (se 1 (by rfl) ⟨312605, by rfl⟩ : syracuseStep 416807 = 625211) B625211
theorem B416987 : Blo 183802 416987 := bstep (se 1 (by rfl) ⟨312740, by rfl⟩ : syracuseStep 416987 = 625481) B625481
theorem B711899 : Blo 183802 711899 := bstep (se 1 (by rfl) ⟨533924, by rfl⟩ : syracuseStep 711899 = 1067849) B1067849
theorem B187679 : Blo 183802 187679 := bstep (se 1 (by rfl) ⟨140759, by rfl⟩ : syracuseStep 187679 = 281519) B281519
theorem B187739 : Blo 183802 187739 := bstep (se 1 (by rfl) ⟨140804, by rfl⟩ : syracuseStep 187739 = 281609) B281609
theorem B187759 : Blo 183802 187759 := bstep (se 1 (by rfl) ⟨140819, by rfl⟩ : syracuseStep 187759 = 281639) B281639
theorem B417185 : Blo 183802 417185 := bstep (se 2 (by rfl) ⟨156444, by rfl⟩ : syracuseStep 417185 = 312889) B312889
theorem B187967 : Blo 183802 187967 := bstep (se 1 (by rfl) ⟨140975, by rfl⟩ : syracuseStep 187967 = 281951) B281951
theorem B417743 : Blo 183802 417743 := bstep (se 1 (by rfl) ⟨313307, by rfl⟩ : syracuseStep 417743 = 626615) B626615
theorem B6086663 : Blo 183802 6086663 := bstep (se 1 (by rfl) ⟨4564997, by rfl⟩ : syracuseStep 6086663 = 9129995) B9129995
theorem B418121 : Blo 183802 418121 := bstep (se 2 (by rfl) ⟨156795, by rfl⟩ : syracuseStep 418121 = 313591) B313591
theorem B418139 : Blo 183802 418139 := bstep (se 1 (by rfl) ⟨313604, by rfl⟩ : syracuseStep 418139 = 627209) B627209
theorem B7955009 : Blo 183802 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B222107 : Blo 183802 222107 := bstep (se 1 (by rfl) ⟨166580, by rfl⟩ : syracuseStep 222107 = 333161) B333161
theorem B418715 : Blo 183802 418715 := bstep (se 1 (by rfl) ⟨314036, by rfl⟩ : syracuseStep 418715 = 628073) B628073
theorem B746435 : Blo 183802 746435 := bstep (se 1 (by rfl) ⟨559826, by rfl⟩ : syracuseStep 746435 = 1119653) B1119653
theorem B418913 : Blo 183802 418913 := bstep (se 2 (by rfl) ⟨157092, by rfl⟩ : syracuseStep 418913 = 314185) B314185
theorem B1598561 : Blo 183802 1598561 := bstep (se 2 (by rfl) ⟨599460, by rfl⟩ : syracuseStep 1598561 = 1198921) B1198921
theorem B419111 : Blo 183802 419111 := bstep (se 1 (by rfl) ⟨314333, by rfl⟩ : syracuseStep 419111 = 628667) B628667
theorem B943649 : Blo 183802 943649 := bstep (se 2 (by rfl) ⟨353868, by rfl⟩ : syracuseStep 943649 = 707737) B707737
theorem B419489 : Blo 183802 419489 := bstep (se 2 (by rfl) ⟨157308, by rfl⟩ : syracuseStep 419489 = 314617) B314617
theorem B222895 : Blo 183802 222895 := bstep (se 1 (by rfl) ⟨167171, by rfl⟩ : syracuseStep 222895 = 334343) B334343
theorem B419849 : Blo 183802 419849 := bstep (se 2 (by rfl) ⟨157443, by rfl⟩ : syracuseStep 419849 = 314887) B314887
theorem B420263 : Blo 183802 420263 := bstep (se 1 (by rfl) ⟨315197, by rfl⟩ : syracuseStep 420263 = 630395) B630395
theorem B420371 : Blo 183802 420371 := bstep (se 1 (by rfl) ⟨315278, by rfl⟩ : syracuseStep 420371 = 630557) B630557
theorem B420425 : Blo 183802 420425 := bstep (se 2 (by rfl) ⟨157659, by rfl⟩ : syracuseStep 420425 = 315319) B315319
theorem B420763 : Blo 183802 420763 := bstep (se 1 (by rfl) ⟨315572, by rfl⟩ : syracuseStep 420763 = 631145) B631145
theorem B420839 : Blo 183802 420839 := bstep (se 1 (by rfl) ⟨315629, by rfl⟩ : syracuseStep 420839 = 631259) B631259
theorem B421217 : Blo 183802 421217 := bstep (se 2 (by rfl) ⟨157956, by rfl⟩ : syracuseStep 421217 = 315913) B315913
theorem B224635 : Blo 183802 224635 := bstep (se 1 (by rfl) ⟨168476, by rfl⟩ : syracuseStep 224635 = 336953) B336953
theorem B421307 : Blo 183802 421307 := bstep (se 1 (by rfl) ⟨315980, by rfl⟩ : syracuseStep 421307 = 631961) B631961
theorem B421433 : Blo 183802 421433 := bstep (se 2 (by rfl) ⟨158037, by rfl⟩ : syracuseStep 421433 = 316075) B316075
theorem B422099 : Blo 183802 422099 := bstep (se 1 (by rfl) ⟨316574, by rfl⟩ : syracuseStep 422099 = 633149) B633149
theorem B422153 : Blo 183802 422153 := bstep (se 2 (by rfl) ⟨158307, by rfl⟩ : syracuseStep 422153 = 316615) B316615
theorem B225703 : Blo 183802 225703 := bstep (se 1 (by rfl) ⟨169277, by rfl⟩ : syracuseStep 225703 = 338555) B338555
theorem B422369 : Blo 183802 422369 := bstep (se 2 (by rfl) ⟨158388, by rfl⟩ : syracuseStep 422369 = 316777) B316777
theorem B3634301 : Blo 183802 3634301 := bstep (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) B1362863
theorem B718073 : Blo 183802 718073 := bstep (se 2 (by rfl) ⟨269277, by rfl⟩ : syracuseStep 718073 = 538555) B538555
theorem B947495 : Blo 183802 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B948023 : Blo 183802 948023 := bstep (se 1 (by rfl) ⟨711017, by rfl⟩ : syracuseStep 948023 = 1422035) B1422035
theorem B423737 : Blo 183802 423737 := bstep (se 2 (by rfl) ⟨158901, by rfl⟩ : syracuseStep 423737 = 317803) B317803
theorem B620729 : Blo 183802 620729 := bstep (se 2 (by rfl) ⟨232773, by rfl⟩ : syracuseStep 620729 = 465547) B465547
theorem B948509 : Blo 183802 948509 := bstep (se 3 (by rfl) ⟨177845, by rfl⟩ : syracuseStep 948509 = 355691) B355691
theorem B1440089 : Blo 183802 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B785339 : Blo 183802 785339 := bstep (se 1 (by rfl) ⟨589004, by rfl⟩ : syracuseStep 785339 = 1178009) B1178009
theorem B851267 : Blo 183802 851267 := bstep (se 1 (by rfl) ⟨638450, by rfl⟩ : syracuseStep 851267 = 1276901) B1276901
theorem B785801 : Blo 183802 785801 := bstep (se 2 (by rfl) ⟨294675, by rfl⟩ : syracuseStep 785801 = 589351) B589351
theorem B392635 : Blo 183802 392635 := bstep (se 1 (by rfl) ⟨294476, by rfl⟩ : syracuseStep 392635 = 588953) B588953
theorem B622241 : Blo 183802 622241 := bstep (se 2 (by rfl) ⟨233340, by rfl⟩ : syracuseStep 622241 = 466681) B466681
theorem B2359043 : Blo 183802 2359043 := bstep (se 1 (by rfl) ⟨1769282, by rfl⟩ : syracuseStep 2359043 = 3538565) B3538565
theorem B425785 : Blo 183802 425785 := bstep (se 2 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 425785 = 319339) B319339
theorem B2031641 : Blo 183802 2031641 := bstep (se 2 (by rfl) ⟨761865, by rfl⟩ : syracuseStep 2031641 = 1523731) B1523731
theorem B622727 : Blo 183802 622727 := bstep (se 1 (by rfl) ⟨467045, by rfl⟩ : syracuseStep 622727 = 934091) B934091
theorem B262759 : Blo 183802 262759 := bstep (se 1 (by rfl) ⟨197069, by rfl⟩ : syracuseStep 262759 = 394139) B394139
theorem B525199 : Blo 183802 525199 := bstep (se 1 (by rfl) ⟨393899, by rfl⟩ : syracuseStep 525199 = 787799) B787799
theorem B721831 : Blo 183802 721831 := bstep (se 1 (by rfl) ⟨541373, by rfl⟩ : syracuseStep 721831 = 1082747) B1082747
theorem B296111 : Blo 183802 296111 := bstep (se 1 (by rfl) ⟨222083, by rfl⟩ : syracuseStep 296111 = 444167) B444167
theorem B263579 : Blo 183802 263579 := bstep (se 1 (by rfl) ⟨197684, by rfl⟩ : syracuseStep 263579 = 395369) B395369
theorem B624239 : Blo 183802 624239 := bstep (se 1 (by rfl) ⟨468179, by rfl⟩ : syracuseStep 624239 = 936359) B936359
theorem B624347 : Blo 183802 624347 := bstep (se 1 (by rfl) ⟨468260, by rfl⟩ : syracuseStep 624347 = 936521) B936521
theorem B1279805 : Blo 183802 1279805 := bstep (se 3 (by rfl) ⟨239963, by rfl⟩ : syracuseStep 1279805 = 479927) B479927
theorem B788399 : Blo 183802 788399 := bstep (se 1 (by rfl) ⟨591299, by rfl⟩ : syracuseStep 788399 = 1182599) B1182599
theorem B395455 : Blo 183802 395455 := bstep (se 1 (by rfl) ⟨296591, by rfl⟩ : syracuseStep 395455 = 593183) B593183
theorem B297193 : Blo 183802 297193 := bstep (se 2 (by rfl) ⟨111447, by rfl⟩ : syracuseStep 297193 = 222895) B222895
theorem B592285 : Blo 183802 592285 := bstep (se 3 (by rfl) ⟨111053, by rfl⟩ : syracuseStep 592285 = 222107) B222107
theorem B526817 : Blo 183802 526817 := bstep (se 2 (by rfl) ⟨197556, by rfl⟩ : syracuseStep 526817 = 395113) B395113
theorem B4000265 : Blo 183802 4000265 := bstep (se 2 (by rfl) ⟨1500099, by rfl⟩ : syracuseStep 4000265 = 3000199) B3000199
theorem B789097 : Blo 183802 789097 := bstep (se 2 (by rfl) ⟨295911, by rfl⟩ : syracuseStep 789097 = 591823) B591823
theorem B1968745 : Blo 183802 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B625643 : Blo 183802 625643 := bstep (se 1 (by rfl) ⟨469232, by rfl⟩ : syracuseStep 625643 = 938465) B938465
theorem B625697 : Blo 183802 625697 := bstep (se 2 (by rfl) ⟨234636, by rfl⟩ : syracuseStep 625697 = 469273) B469273
theorem B265583 : Blo 183802 265583 := bstep (se 1 (by rfl) ⟨199187, by rfl⟩ : syracuseStep 265583 = 398375) B398375
theorem B2526653 : Blo 183802 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B298603 : Blo 183802 298603 := bstep (se 1 (by rfl) ⟨223952, by rfl⟩ : syracuseStep 298603 = 447905) B447905
theorem B1281737 : Blo 183802 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B561017 : Blo 183802 561017 := bstep (se 2 (by rfl) ⟨210381, by rfl⟩ : syracuseStep 561017 = 420763) B420763
theorem B627155 : Blo 183802 627155 := bstep (se 1 (by rfl) ⟨470366, by rfl⟩ : syracuseStep 627155 = 940733) B940733
theorem B299513 : Blo 183802 299513 := bstep (se 2 (by rfl) ⟨112317, by rfl⟩ : syracuseStep 299513 = 224635) B224635
theorem B594515 : Blo 183802 594515 := bstep (se 1 (by rfl) ⟨445886, by rfl⟩ : syracuseStep 594515 = 891773) B891773
theorem B1054043 : Blo 183802 1054043 := bstep (se 1 (by rfl) ⟨790532, by rfl⟩ : syracuseStep 1054043 = 1581065) B1581065
theorem B792173 : Blo 183802 792173 := bstep (se 3 (by rfl) ⟨148532, by rfl⟩ : syracuseStep 792173 = 297065) B297065
theorem B2398045 : Blo 183802 2398045 := bstep (se 3 (by rfl) ⟨449633, by rfl⟩ : syracuseStep 2398045 = 899267) B899267
theorem B300937 : Blo 183802 300937 := bstep (se 2 (by rfl) ⟨112851, by rfl⟩ : syracuseStep 300937 = 225703) B225703
theorem B497623 : Blo 183802 497623 := bstep (se 1 (by rfl) ⟨373217, by rfl⟩ : syracuseStep 497623 = 746435) B746435
theorem B629099 : Blo 183802 629099 := bstep (se 1 (by rfl) ⟨471824, by rfl⟩ : syracuseStep 629099 = 943649) B943649
theorem B629369 : Blo 183802 629369 := bstep (se 2 (by rfl) ⟨236013, by rfl⟩ : syracuseStep 629369 = 472027) B472027
theorem B531305 : Blo 183802 531305 := bstep (se 2 (by rfl) ⟨199239, by rfl⟩ : syracuseStep 531305 = 398479) B398479
theorem B465871 : Blo 183802 465871 := bstep (se 1 (by rfl) ⟨349403, by rfl⟩ : syracuseStep 465871 = 698807) B698807
theorem B629801 : Blo 183802 629801 := bstep (se 2 (by rfl) ⟨236175, by rfl⟩ : syracuseStep 629801 = 472351) B472351
theorem B334919 : Blo 183802 334919 := bstep (se 1 (by rfl) ⟨251189, by rfl⟩ : syracuseStep 334919 = 502379) B502379
theorem B597257 : Blo 183802 597257 := bstep (se 2 (by rfl) ⟨223971, by rfl⟩ : syracuseStep 597257 = 447943) B447943
theorem B794087 : Blo 183802 794087 := bstep (se 1 (by rfl) ⟨595565, by rfl⟩ : syracuseStep 794087 = 1191131) B1191131
theorem B400871 : Blo 183802 400871 := bstep (se 1 (by rfl) ⟨300653, by rfl⟩ : syracuseStep 400871 = 601307) B601307
theorem B6757967 : Blo 183802 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B1515311 : Blo 183802 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B860513 : Blo 183802 860513 := bstep (se 2 (by rfl) ⟨322692, by rfl⟩ : syracuseStep 860513 = 645385) B645385
theorem B1909111 : Blo 183802 1909111 := bstep (se 1 (by rfl) ⟨1431833, by rfl⟩ : syracuseStep 1909111 = 2863667) B2863667
theorem B1057211 : Blo 183802 1057211 := bstep (se 1 (by rfl) ⟨792908, by rfl⟩ : syracuseStep 1057211 = 1585817) B1585817
theorem B2270045 : Blo 183802 2270045 := bstep (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) B851267
theorem B632015 : Blo 183802 632015 := bstep (se 1 (by rfl) ⟨474011, by rfl⟩ : syracuseStep 632015 = 948023) B948023
theorem B501245 : Blo 183802 501245 := bstep (se 3 (by rfl) ⟨93983, by rfl⟩ : syracuseStep 501245 = 187967) B187967
theorem B632339 : Blo 183802 632339 := bstep (se 1 (by rfl) ⟨474254, by rfl⟩ : syracuseStep 632339 = 948509) B948509
theorem B960059 : Blo 183802 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B468767 : Blo 183802 468767 := bstep (se 1 (by rfl) ⟨351575, by rfl⟩ : syracuseStep 468767 = 703151) B703151
theorem B796513 : Blo 183802 796513 := bstep (se 2 (by rfl) ⟨298692, by rfl⟩ : syracuseStep 796513 = 597385) B597385
theorem B403399 : Blo 183802 403399 := bstep (se 1 (by rfl) ⟨302549, by rfl⟩ : syracuseStep 403399 = 605099) B605099
theorem B567713 : Blo 183802 567713 := bstep (se 2 (by rfl) ⟨212892, by rfl⟩ : syracuseStep 567713 = 425785) B425785
theorem B207391 : Blo 183802 207391 := bstep (se 1 (by rfl) ⟨155543, by rfl⟩ : syracuseStep 207391 = 311087) B311087
theorem B633527 : Blo 183802 633527 := bstep (se 1 (by rfl) ⟨475145, by rfl⟩ : syracuseStep 633527 = 950291) B950291
theorem B1420091 : Blo 183802 1420091 := bstep (se 1 (by rfl) ⟨1065068, by rfl⟩ : syracuseStep 1420091 = 2130137) B2130137
theorem B470063 : Blo 183802 470063 := bstep (se 1 (by rfl) ⟨352547, by rfl⟩ : syracuseStep 470063 = 705095) B705095
theorem B470519 : Blo 183802 470519 := bstep (se 1 (by rfl) ⟨352889, by rfl⟩ : syracuseStep 470519 = 705779) B705779
theorem B699961 : Blo 183802 699961 := bstep (se 2 (by rfl) ⟨262485, by rfl⟩ : syracuseStep 699961 = 524971) B524971
theorem B1584755 : Blo 183802 1584755 := bstep (se 1 (by rfl) ⟨1188566, by rfl⟩ : syracuseStep 1584755 = 2377133) B2377133
theorem B13676303 : Blo 183802 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B667531 : Blo 183802 667531 := bstep (se 1 (by rfl) ⟨500648, by rfl⟩ : syracuseStep 667531 = 1001297) B1001297
theorem B2404403 : Blo 183802 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B1061059 : Blo 183802 1061059 := bstep (se 1 (by rfl) ⟨795794, by rfl⟩ : syracuseStep 1061059 = 1591589) B1591589
theorem B799247 : Blo 183802 799247 := bstep (se 1 (by rfl) ⟨599435, by rfl⟩ : syracuseStep 799247 = 1198871) B1198871
theorem B471815 : Blo 183802 471815 := bstep (se 1 (by rfl) ⟨353861, by rfl⟩ : syracuseStep 471815 = 707723) B707723
theorem B209983 : Blo 183802 209983 := bstep (se 1 (by rfl) ⟨157487, by rfl⟩ : syracuseStep 209983 = 314975) B314975
theorem B210127 : Blo 183802 210127 := bstep (se 1 (by rfl) ⟨157595, by rfl⟩ : syracuseStep 210127 = 315191) B315191
theorem B1520957 : Blo 183802 1520957 := bstep (se 3 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 1520957 = 570359) B570359
theorem B537953 : Blo 183802 537953 := bstep (se 2 (by rfl) ⟨201732, by rfl⟩ : syracuseStep 537953 = 403465) B403465
theorem B275867 : Blo 183802 275867 := bstep (se 1 (by rfl) ⟨206900, by rfl⟩ : syracuseStep 275867 = 413801) B413801
theorem B931337 : Blo 183802 931337 := bstep (se 2 (by rfl) ⟨349251, by rfl⟩ : syracuseStep 931337 = 698503) B698503
theorem B276089 : Blo 183802 276089 := bstep (se 2 (by rfl) ⟨103533, by rfl⟩ : syracuseStep 276089 = 207067) B207067
theorem B276191 : Blo 183802 276191 := bstep (se 1 (by rfl) ⟨207143, by rfl⟩ : syracuseStep 276191 = 414287) B414287
theorem B2668277 : Blo 183802 2668277 := bstep (se 5 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 2668277 = 250151) B250151
theorem B276287 : Blo 183802 276287 := bstep (se 1 (by rfl) ⟨207215, by rfl⟩ : syracuseStep 276287 = 414431) B414431
theorem B276455 : Blo 183802 276455 := bstep (se 1 (by rfl) ⟨207341, by rfl⟩ : syracuseStep 276455 = 414683) B414683
theorem B276473 : Blo 183802 276473 := bstep (se 2 (by rfl) ⟨103677, by rfl⟩ : syracuseStep 276473 = 207355) B207355
theorem B276575 : Blo 183802 276575 := bstep (se 1 (by rfl) ⟨207431, by rfl⟩ : syracuseStep 276575 = 414863) B414863
theorem B276635 : Blo 183802 276635 := bstep (se 1 (by rfl) ⟨207476, by rfl⟩ : syracuseStep 276635 = 414953) B414953
theorem B211099 : Blo 183802 211099 := bstep (se 1 (by rfl) ⟨158324, by rfl⟩ : syracuseStep 211099 = 316649) B316649
theorem B276671 : Blo 183802 276671 := bstep (se 1 (by rfl) ⟨207503, by rfl⟩ : syracuseStep 276671 = 415007) B415007
theorem B211135 : Blo 183802 211135 := bstep (se 1 (by rfl) ⟨158351, by rfl⟩ : syracuseStep 211135 = 316703) B316703
theorem B1063145 : Blo 183802 1063145 := bstep (se 2 (by rfl) ⟨398679, by rfl⟩ : syracuseStep 1063145 = 797359) B797359
theorem B276713 : Blo 183802 276713 := bstep (se 2 (by rfl) ⟨103767, by rfl⟩ : syracuseStep 276713 = 207535) B207535
theorem B277019 : Blo 183802 277019 := bstep (se 1 (by rfl) ⟨207764, by rfl⟩ : syracuseStep 277019 = 415529) B415529
theorem B277097 : Blo 183802 277097 := bstep (se 2 (by rfl) ⟨103911, by rfl⟩ : syracuseStep 277097 = 207823) B207823
theorem B1194695 : Blo 183802 1194695 := bstep (se 1 (by rfl) ⟨896021, by rfl⟩ : syracuseStep 1194695 = 1792043) B1792043
theorem B310223 : Blo 183802 310223 := bstep (se 1 (by rfl) ⟨232667, by rfl⟩ : syracuseStep 310223 = 465335) B465335
theorem B1063975 : Blo 183802 1063975 := bstep (se 1 (by rfl) ⟨797981, by rfl⟩ : syracuseStep 1063975 = 1595963) B1595963
theorem B1424465 : Blo 183802 1424465 := bstep (se 2 (by rfl) ⟨534174, by rfl⟩ : syracuseStep 1424465 = 1068349) B1068349
theorem B277625 : Blo 183802 277625 := bstep (se 2 (by rfl) ⟨104109, by rfl⟩ : syracuseStep 277625 = 208219) B208219
theorem B2112641 : Blo 183802 2112641 := bstep (se 2 (by rfl) ⟨792240, by rfl⟩ : syracuseStep 2112641 = 1584481) B1584481
theorem B474295 : Blo 183802 474295 := bstep (se 1 (by rfl) ⟨355721, by rfl⟩ : syracuseStep 474295 = 711443) B711443
theorem B277727 : Blo 183802 277727 := bstep (se 1 (by rfl) ⟨208295, by rfl⟩ : syracuseStep 277727 = 416591) B416591
theorem B277769 : Blo 183802 277769 := bstep (se 2 (by rfl) ⟨104163, by rfl⟩ : syracuseStep 277769 = 208327) B208327
theorem B277871 : Blo 183802 277871 := bstep (se 1 (by rfl) ⟨208403, by rfl⟩ : syracuseStep 277871 = 416807) B416807
theorem B277991 : Blo 183802 277991 := bstep (se 1 (by rfl) ⟨208493, by rfl⟩ : syracuseStep 277991 = 416987) B416987
theorem B474599 : Blo 183802 474599 := bstep (se 1 (by rfl) ⟨355949, by rfl⟩ : syracuseStep 474599 = 711899) B711899
theorem B310891 : Blo 183802 310891 := bstep (se 1 (by rfl) ⟨233168, by rfl⟩ : syracuseStep 310891 = 466337) B466337
theorem B278123 : Blo 183802 278123 := bstep (se 1 (by rfl) ⟨208592, by rfl⟩ : syracuseStep 278123 = 417185) B417185
theorem B278249 : Blo 183802 278249 := bstep (se 2 (by rfl) ⟨104343, by rfl⟩ : syracuseStep 278249 = 208687) B208687
theorem B442099 : Blo 183802 442099 := bstep (se 1 (by rfl) ⟨331574, by rfl⟩ : syracuseStep 442099 = 663149) B663149
theorem B311161 : Blo 183802 311161 := bstep (se 2 (by rfl) ⟨116685, by rfl⟩ : syracuseStep 311161 = 233371) B233371
theorem B278393 : Blo 183802 278393 := bstep (se 2 (by rfl) ⟨104397, by rfl⟩ : syracuseStep 278393 = 208795) B208795
theorem B311195 : Blo 183802 311195 := bstep (se 1 (by rfl) ⟨233396, by rfl⟩ : syracuseStep 311195 = 466793) B466793
theorem B278495 : Blo 183802 278495 := bstep (se 1 (by rfl) ⟨208871, by rfl⟩ : syracuseStep 278495 = 417743) B417743
theorem B1818713 : Blo 183802 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B278747 : Blo 183802 278747 := bstep (se 1 (by rfl) ⟨209060, by rfl⟩ : syracuseStep 278747 = 418121) B418121
theorem B278759 : Blo 183802 278759 := bstep (se 1 (by rfl) ⟨209069, by rfl⟩ : syracuseStep 278759 = 418139) B418139
theorem B278921 : Blo 183802 278921 := bstep (se 2 (by rfl) ⟨104595, by rfl⟩ : syracuseStep 278921 = 209191) B209191
theorem B279017 : Blo 183802 279017 := bstep (se 2 (by rfl) ⟨104631, by rfl⟩ : syracuseStep 279017 = 209263) B209263
theorem B279143 : Blo 183802 279143 := bstep (se 1 (by rfl) ⟨209357, by rfl⟩ : syracuseStep 279143 = 418715) B418715
theorem B279275 : Blo 183802 279275 := bstep (se 1 (by rfl) ⟨209456, by rfl⟩ : syracuseStep 279275 = 418913) B418913
theorem B1065707 : Blo 183802 1065707 := bstep (se 1 (by rfl) ⟨799280, by rfl⟩ : syracuseStep 1065707 = 1598561) B1598561
theorem B279305 : Blo 183802 279305 := bstep (se 2 (by rfl) ⟨104739, by rfl⟩ : syracuseStep 279305 = 209479) B209479
theorem B279407 : Blo 183802 279407 := bstep (se 1 (by rfl) ⟨209555, by rfl⟩ : syracuseStep 279407 = 419111) B419111
theorem B1000349 : Blo 183802 1000349 := bstep (se 3 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 1000349 = 375131) B375131
theorem B312383 : Blo 183802 312383 := bstep (se 1 (by rfl) ⟨234287, by rfl⟩ : syracuseStep 312383 = 468575) B468575
theorem B410729 : Blo 183802 410729 := bstep (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) B308047
theorem B279659 : Blo 183802 279659 := bstep (se 1 (by rfl) ⟨209744, by rfl⟩ : syracuseStep 279659 = 419489) B419489
theorem B1230083 : Blo 183802 1230083 := bstep (se 1 (by rfl) ⟨922562, by rfl⟩ : syracuseStep 1230083 = 1845125) B1845125
theorem B279899 : Blo 183802 279899 := bstep (se 1 (by rfl) ⟨209924, by rfl⟩ : syracuseStep 279899 = 419849) B419849
theorem B706067 : Blo 183802 706067 := bstep (se 1 (by rfl) ⟨529550, by rfl⟩ : syracuseStep 706067 = 1059101) B1059101
theorem B312943 : Blo 183802 312943 := bstep (se 1 (by rfl) ⟨234707, by rfl⟩ : syracuseStep 312943 = 469415) B469415
theorem B280175 : Blo 183802 280175 := bstep (se 1 (by rfl) ⟨210131, by rfl⟩ : syracuseStep 280175 = 420263) B420263
theorem B280247 : Blo 183802 280247 := bstep (se 1 (by rfl) ⟨210185, by rfl⟩ : syracuseStep 280247 = 420371) B420371
theorem B313051 : Blo 183802 313051 := bstep (se 1 (by rfl) ⟨234788, by rfl⟩ : syracuseStep 313051 = 469577) B469577
theorem B280283 : Blo 183802 280283 := bstep (se 1 (by rfl) ⟨210212, by rfl⟩ : syracuseStep 280283 = 420425) B420425
theorem B280457 : Blo 183802 280457 := bstep (se 2 (by rfl) ⟨105171, by rfl⟩ : syracuseStep 280457 = 210343) B210343
theorem B2115557 : Blo 183802 2115557 := bstep (se 4 (by rfl) ⟨198333, by rfl⟩ : syracuseStep 2115557 = 396667) B396667
theorem B280559 : Blo 183802 280559 := bstep (se 1 (by rfl) ⟨210419, by rfl⟩ : syracuseStep 280559 = 420839) B420839
theorem B706751 : Blo 183802 706751 := bstep (se 1 (by rfl) ⟨530063, by rfl⟩ : syracuseStep 706751 = 1060127) B1060127
theorem B280811 : Blo 183802 280811 := bstep (se 1 (by rfl) ⟨210608, by rfl⟩ : syracuseStep 280811 = 421217) B421217
theorem B280871 : Blo 183802 280871 := bstep (se 1 (by rfl) ⟨210653, by rfl⟩ : syracuseStep 280871 = 421307) B421307
theorem B280955 : Blo 183802 280955 := bstep (se 1 (by rfl) ⟨210716, by rfl⟩ : syracuseStep 280955 = 421433) B421433
theorem B10242541 : Blo 183802 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B281225 : Blo 183802 281225 := bstep (se 2 (by rfl) ⟨105459, by rfl⟩ : syracuseStep 281225 = 210919) B210919
theorem B281399 : Blo 183802 281399 := bstep (se 1 (by rfl) ⟨211049, by rfl⟩ : syracuseStep 281399 = 422099) B422099
theorem B281435 : Blo 183802 281435 := bstep (se 1 (by rfl) ⟨211076, by rfl⟩ : syracuseStep 281435 = 422153) B422153
theorem B314347 : Blo 183802 314347 := bstep (se 1 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 314347 = 471521) B471521
theorem B281579 : Blo 183802 281579 := bstep (se 1 (by rfl) ⟨211184, by rfl⟩ : syracuseStep 281579 = 422369) B422369
theorem B1428509 : Blo 183802 1428509 := bstep (se 3 (by rfl) ⟨267845, by rfl⟩ : syracuseStep 1428509 = 535691) B535691
theorem B314489 : Blo 183802 314489 := bstep (se 2 (by rfl) ⟨117933, by rfl⟩ : syracuseStep 314489 = 235867) B235867
theorem B445943 : Blo 183802 445943 := bstep (se 1 (by rfl) ⟨334457, by rfl⟩ : syracuseStep 445943 = 668915) B668915
theorem B478715 : Blo 183802 478715 := bstep (se 1 (by rfl) ⟨359036, by rfl⟩ : syracuseStep 478715 = 718073) B718073
theorem B183899 : Blo 183802 183899 := bstep (se 1 (by rfl) ⟨137924, by rfl⟩ : syracuseStep 183899 = 275849) B275849
theorem B184135 : Blo 183802 184135 := bstep (se 1 (by rfl) ⟨138101, by rfl⟩ : syracuseStep 184135 = 276203) B276203
theorem B282491 : Blo 183802 282491 := bstep (se 1 (by rfl) ⟨211868, by rfl⟩ : syracuseStep 282491 = 423737) B423737
theorem B184287 : Blo 183802 184287 := bstep (se 1 (by rfl) ⟨138215, by rfl⟩ : syracuseStep 184287 = 276431) B276431
theorem B413819 : Blo 183802 413819 := bstep (se 1 (by rfl) ⟨310364, by rfl⟩ : syracuseStep 413819 = 620729) B620729
theorem B184551 : Blo 183802 184551 := bstep (se 1 (by rfl) ⟨138413, by rfl⟩ : syracuseStep 184551 = 276827) B276827
theorem B315623 : Blo 183802 315623 := bstep (se 1 (by rfl) ⟨236717, by rfl⟩ : syracuseStep 315623 = 473435) B473435
theorem B184703 : Blo 183802 184703 := bstep (se 1 (by rfl) ⟨138527, by rfl⟩ : syracuseStep 184703 = 277055) B277055
theorem B414089 : Blo 183802 414089 := bstep (se 2 (by rfl) ⟨155283, by rfl⟩ : syracuseStep 414089 = 310567) B310567
theorem B315785 : Blo 183802 315785 := bstep (se 2 (by rfl) ⟨118419, by rfl⟩ : syracuseStep 315785 = 236839) B236839
theorem B315847 : Blo 183802 315847 := bstep (se 1 (by rfl) ⟨236885, by rfl⟩ : syracuseStep 315847 = 473771) B473771
theorem B184783 : Blo 183802 184783 := bstep (se 1 (by rfl) ⟨138587, by rfl⟩ : syracuseStep 184783 = 277175) B277175
theorem B447059 : Blo 183802 447059 := bstep (se 1 (by rfl) ⟨335294, by rfl⟩ : syracuseStep 447059 = 670589) B670589
theorem B184935 : Blo 183802 184935 := bstep (se 1 (by rfl) ⟨138701, by rfl⟩ : syracuseStep 184935 = 277403) B277403
theorem B3822329 : Blo 183802 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B316217 : Blo 183802 316217 := bstep (se 2 (by rfl) ⟨118581, by rfl⟩ : syracuseStep 316217 = 237163) B237163
theorem B185199 : Blo 183802 185199 := bstep (se 1 (by rfl) ⟨138899, by rfl⟩ : syracuseStep 185199 = 277799) B277799
theorem B316271 : Blo 183802 316271 := bstep (se 1 (by rfl) ⟨237203, by rfl⟩ : syracuseStep 316271 = 474407) B474407
theorem B185255 : Blo 183802 185255 := bstep (se 1 (by rfl) ⟨138941, by rfl⟩ : syracuseStep 185255 = 277883) B277883
theorem B185339 : Blo 183802 185339 := bstep (se 1 (by rfl) ⟨139004, by rfl⟩ : syracuseStep 185339 = 278009) B278009
theorem B185407 : Blo 183802 185407 := bstep (se 1 (by rfl) ⟨139055, by rfl⟩ : syracuseStep 185407 = 278111) B278111
theorem B316489 : Blo 183802 316489 := bstep (se 2 (by rfl) ⟨118683, by rfl⟩ : syracuseStep 316489 = 237367) B237367
theorem B414827 : Blo 183802 414827 := bstep (se 1 (by rfl) ⟨311120, by rfl⟩ : syracuseStep 414827 = 622241) B622241
theorem B185551 : Blo 183802 185551 := bstep (se 1 (by rfl) ⟨139163, by rfl⟩ : syracuseStep 185551 = 278327) B278327
theorem B709985 : Blo 183802 709985 := bstep (se 2 (by rfl) ⟨266244, by rfl⟩ : syracuseStep 709985 = 532489) B532489
theorem B1398169 : Blo 183802 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B185755 : Blo 183802 185755 := bstep (se 1 (by rfl) ⟨139316, by rfl⟩ : syracuseStep 185755 = 278633) B278633
theorem B1594811 : Blo 183802 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B185967 : Blo 183802 185967 := bstep (se 1 (by rfl) ⟨139475, by rfl⟩ : syracuseStep 185967 = 278951) B278951
theorem B186023 : Blo 183802 186023 := bstep (se 1 (by rfl) ⟨139517, by rfl⟩ : syracuseStep 186023 = 279035) B279035
theorem B710315 : Blo 183802 710315 := bstep (se 1 (by rfl) ⟨532736, by rfl⟩ : syracuseStep 710315 = 1065473) B1065473
theorem B415403 : Blo 183802 415403 := bstep (se 1 (by rfl) ⟨311552, by rfl⟩ : syracuseStep 415403 = 623105) B623105
theorem B186107 : Blo 183802 186107 := bstep (se 1 (by rfl) ⟨139580, by rfl⟩ : syracuseStep 186107 = 279161) B279161
theorem B186143 : Blo 183802 186143 := bstep (se 1 (by rfl) ⟨139607, by rfl⟩ : syracuseStep 186143 = 279215) B279215
theorem B186175 : Blo 183802 186175 := bstep (se 1 (by rfl) ⟨139631, by rfl⟩ : syracuseStep 186175 = 279263) B279263
theorem B546791 : Blo 183802 546791 := bstep (se 1 (by rfl) ⟨410093, by rfl⟩ : syracuseStep 546791 = 820187) B820187
theorem B841711 : Blo 183802 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B415727 : Blo 183802 415727 := bstep (se 1 (by rfl) ⟨311795, by rfl⟩ : syracuseStep 415727 = 623591) B623591
theorem B186351 : Blo 183802 186351 := bstep (se 1 (by rfl) ⟨139763, by rfl⟩ : syracuseStep 186351 = 279527) B279527
theorem B710639 : Blo 183802 710639 := bstep (se 1 (by rfl) ⟨532979, by rfl⟩ : syracuseStep 710639 = 1065959) B1065959
theorem B186523 : Blo 183802 186523 := bstep (se 1 (by rfl) ⟨139892, by rfl⟩ : syracuseStep 186523 = 279785) B279785
theorem B186559 : Blo 183802 186559 := bstep (se 1 (by rfl) ⟨139919, by rfl⟩ : syracuseStep 186559 = 279839) B279839
theorem B841927 : Blo 183802 841927 := bstep (se 1 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 841927 = 1262891) B1262891
theorem B415943 : Blo 183802 415943 := bstep (se 1 (by rfl) ⟨311957, by rfl⟩ : syracuseStep 415943 = 623915) B623915
theorem B186671 : Blo 183802 186671 := bstep (se 1 (by rfl) ⟨140003, by rfl⟩ : syracuseStep 186671 = 280007) B280007
theorem B416123 : Blo 183802 416123 := bstep (se 1 (by rfl) ⟨312092, by rfl⟩ : syracuseStep 416123 = 624185) B624185
theorem B1006013 : Blo 183802 1006013 := bstep (se 3 (by rfl) ⟨188627, by rfl⟩ : syracuseStep 1006013 = 377255) B377255
theorem B186907 : Blo 183802 186907 := bstep (se 1 (by rfl) ⟨140180, by rfl⟩ : syracuseStep 186907 = 280361) B280361
theorem B186911 : Blo 183802 186911 := bstep (se 1 (by rfl) ⟨140183, by rfl⟩ : syracuseStep 186911 = 280367) B280367
theorem B416393 : Blo 183802 416393 := bstep (se 2 (by rfl) ⟨156147, by rfl⟩ : syracuseStep 416393 = 312295) B312295
theorem B1596125 : Blo 183802 1596125 := bstep (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) B598547
theorem B351067 : Blo 183802 351067 := bstep (se 1 (by rfl) ⟨263300, by rfl⟩ : syracuseStep 351067 = 526601) B526601
theorem B187227 : Blo 183802 187227 := bstep (se 1 (by rfl) ⟨140420, by rfl⟩ : syracuseStep 187227 = 280841) B280841
theorem B187295 : Blo 183802 187295 := bstep (se 1 (by rfl) ⟨140471, by rfl⟩ : syracuseStep 187295 = 280943) B280943
theorem B711625 : Blo 183802 711625 := bstep (se 2 (by rfl) ⟨266859, by rfl⟩ : syracuseStep 711625 = 533719) B533719
theorem B187439 : Blo 183802 187439 := bstep (se 1 (by rfl) ⟨140579, by rfl⟩ : syracuseStep 187439 = 281159) B281159
theorem B187463 : Blo 183802 187463 := bstep (se 1 (by rfl) ⟨140597, by rfl⟩ : syracuseStep 187463 = 281195) B281195
theorem B416951 : Blo 183802 416951 := bstep (se 1 (by rfl) ⟨312713, by rfl⟩ : syracuseStep 416951 = 625427) B625427
theorem B187615 : Blo 183802 187615 := bstep (se 1 (by rfl) ⟨140711, by rfl⟩ : syracuseStep 187615 = 281423) B281423
theorem B712097 : Blo 183802 712097 := bstep (se 2 (by rfl) ⟨267036, by rfl⟩ : syracuseStep 712097 = 534073) B534073
theorem B941543 : Blo 183802 941543 := bstep (se 1 (by rfl) ⟨706157, by rfl⟩ : syracuseStep 941543 = 1412315) B1412315
theorem B417527 : Blo 183802 417527 := bstep (se 1 (by rfl) ⟨313145, by rfl⟩ : syracuseStep 417527 = 626291) B626291
theorem B417707 : Blo 183802 417707 := bstep (se 1 (by rfl) ⟨313280, by rfl⟩ : syracuseStep 417707 = 626561) B626561
theorem B352487 : Blo 183802 352487 := bstep (se 1 (by rfl) ⟨264365, by rfl⟩ : syracuseStep 352487 = 528731) B528731
theorem B9691469 : Blo 183802 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B418247 : Blo 183802 418247 := bstep (se 1 (by rfl) ⟨313685, by rfl⟩ : syracuseStep 418247 = 627371) B627371
theorem B352745 : Blo 183802 352745 := bstep (se 2 (by rfl) ⟨132279, by rfl⟩ : syracuseStep 352745 = 264559) B264559
theorem B3793591 : Blo 183802 3793591 := bstep (se 1 (by rfl) ⟨2845193, by rfl⟩ : syracuseStep 3793591 = 5690387) B5690387
theorem B418607 : Blo 183802 418607 := bstep (se 1 (by rfl) ⟨313955, by rfl⟩ : syracuseStep 418607 = 627911) B627911
theorem B190063 : Blo 183802 190063 := bstep (se 1 (by rfl) ⟨142547, by rfl⟩ : syracuseStep 190063 = 285095) B285095
theorem B419615 : Blo 183802 419615 := bstep (se 1 (by rfl) ⟨314711, by rfl⟩ : syracuseStep 419615 = 629423) B629423
theorem B354127 : Blo 183802 354127 := bstep (se 1 (by rfl) ⟨265595, by rfl⟩ : syracuseStep 354127 = 531191) B531191
theorem B419831 : Blo 183802 419831 := bstep (se 1 (by rfl) ⟨314873, by rfl⟩ : syracuseStep 419831 = 629747) B629747
theorem B2844953 : Blo 183802 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B9038141 : Blo 183802 9038141 := bstep (se 3 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 9038141 = 3389303) B3389303
theorem B420191 : Blo 183802 420191 := bstep (se 1 (by rfl) ⟨315143, by rfl⟩ : syracuseStep 420191 = 630287) B630287
theorem B1403567 : Blo 183802 1403567 := bstep (se 1 (by rfl) ⟨1052675, by rfl⟩ : syracuseStep 1403567 = 2105351) B2105351
theorem B4057775 : Blo 183802 4057775 := bstep (se 1 (by rfl) ⟨3043331, by rfl⟩ : syracuseStep 4057775 = 6086663) B6086663
theorem B5303339 : Blo 183802 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B420911 : Blo 183802 420911 := bstep (se 1 (by rfl) ⟨315683, by rfl⟩ : syracuseStep 420911 = 631367) B631367
theorem B224327 : Blo 183802 224327 := bstep (se 1 (by rfl) ⟨168245, by rfl⟩ : syracuseStep 224327 = 336491) B336491
theorem B421199 : Blo 183802 421199 := bstep (se 1 (by rfl) ⟨315899, by rfl⟩ : syracuseStep 421199 = 631799) B631799
theorem B421289 : Blo 183802 421289 := bstep (se 2 (by rfl) ⟨157983, by rfl⟩ : syracuseStep 421289 = 315967) B315967
theorem B2158289 : Blo 183802 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B1994635 : Blo 183802 1994635 := bstep (se 1 (by rfl) ⟨1495976, by rfl⟩ : syracuseStep 1994635 = 2991953) B2991953
theorem B421775 : Blo 183802 421775 := bstep (se 1 (by rfl) ⟨316331, by rfl⟩ : syracuseStep 421775 = 632663) B632663
theorem B1077371 : Blo 183802 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B1274167 : Blo 183802 1274167 := bstep (se 1 (by rfl) ⟨955625, by rfl⟩ : syracuseStep 1274167 = 1911251) B1911251
theorem B422495 : Blo 183802 422495 := bstep (se 1 (by rfl) ⟨316871, by rfl⟩ : syracuseStep 422495 = 633743) B633743
theorem B620351 : Blo 183802 620351 := bstep (se 1 (by rfl) ⟨465263, by rfl⟩ : syracuseStep 620351 = 930527) B930527
theorem B1406969 : Blo 183802 1406969 := bstep (se 2 (by rfl) ⟨527613, by rfl⟩ : syracuseStep 1406969 = 1055227) B1055227
theorem B949319 : Blo 183802 949319 := bstep (se 1 (by rfl) ⟨711989, by rfl⟩ : syracuseStep 949319 = 1423979) B1423979
theorem B523513 : Blo 183802 523513 := bstep (se 2 (by rfl) ⟨196317, by rfl⟩ : syracuseStep 523513 = 392635) B392635
theorem B523559 : Blo 183802 523559 := bstep (se 1 (by rfl) ⟨392669, by rfl⟩ : syracuseStep 523559 = 785339) B785339
theorem B621863 : Blo 183802 621863 := bstep (se 1 (by rfl) ⟨466397, by rfl⟩ : syracuseStep 621863 = 932795) B932795
theorem B1670519 : Blo 183802 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B523867 : Blo 183802 523867 := bstep (se 1 (by rfl) ⟨392900, by rfl⟩ : syracuseStep 523867 = 785801) B785801
theorem B1277687 : Blo 183802 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B294695 : Blo 183802 294695 := bstep (se 1 (by rfl) ⟨221021, by rfl⟩ : syracuseStep 294695 = 442043) B442043
theorem B1572695 : Blo 183802 1572695 := bstep (se 1 (by rfl) ⟨1179521, by rfl⟩ : syracuseStep 1572695 = 2359043) B2359043
theorem B4849901 : Blo 183802 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B197407 : Blo 183802 197407 := bstep (se 1 (by rfl) ⟨148055, by rfl⟩ : syracuseStep 197407 = 296111) B296111
theorem B820055 : Blo 183802 820055 := bstep (se 1 (by rfl) ⟨615041, by rfl⟩ : syracuseStep 820055 = 1230083) B1230083
theorem B2294701 : Blo 183802 2294701 := bstep (se 3 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 2294701 = 860513) B860513
theorem B525599 : Blo 183802 525599 := bstep (se 1 (by rfl) ⟨394199, by rfl⟩ : syracuseStep 525599 = 788399) B788399
theorem B1410371 : Blo 183802 1410371 := bstep (se 1 (by rfl) ⟨1057778, by rfl⟩ : syracuseStep 1410371 = 2115557) B2115557
theorem B10192877 : Blo 183802 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B952339 : Blo 183802 952339 := bstep (se 1 (by rfl) ⟨714254, by rfl⟩ : syracuseStep 952339 = 1428509) B1428509
theorem B854491 : Blo 183802 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B527273 : Blo 183802 527273 := bstep (se 2 (by rfl) ⟨197727, by rfl⟩ : syracuseStep 527273 = 395455) B395455
theorem B396257 : Blo 183802 396257 := bstep (se 2 (by rfl) ⟨148596, by rfl⟩ : syracuseStep 396257 = 297193) B297193
theorem B199675 : Blo 183802 199675 := bstep (se 1 (by rfl) ⟨149756, by rfl⟩ : syracuseStep 199675 = 299513) B299513
theorem B396343 : Blo 183802 396343 := bstep (se 1 (by rfl) ⟨297257, by rfl⟩ : syracuseStep 396343 = 594515) B594515
theorem B789713 : Blo 183802 789713 := bstep (se 2 (by rfl) ⟨296142, by rfl⟩ : syracuseStep 789713 = 592285) B592285
theorem B1052129 : Blo 183802 1052129 := bstep (se 2 (by rfl) ⟨394548, by rfl⟩ : syracuseStep 1052129 = 789097) B789097
theorem B2624993 : Blo 183802 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B5738165 : Blo 183802 5738165 := bstep (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) B537953
theorem B528115 : Blo 183802 528115 := bstep (se 1 (by rfl) ⟨396086, by rfl⟩ : syracuseStep 528115 = 792173) B792173
theorem B2560157 : Blo 183802 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B398137 : Blo 183802 398137 := bstep (se 2 (by rfl) ⟨149301, by rfl⟩ : syracuseStep 398137 = 298603) B298603
theorem B3412813 : Blo 183802 3412813 := bstep (se 3 (by rfl) ⟨639902, by rfl⟩ : syracuseStep 3412813 = 1279805) B1279805
theorem B398171 : Blo 183802 398171 := bstep (se 1 (by rfl) ⟨298628, by rfl⟩ : syracuseStep 398171 = 597257) B597257
theorem B529391 : Blo 183802 529391 := bstep (se 1 (by rfl) ⟨397043, by rfl⟩ : syracuseStep 529391 = 794087) B794087
theorem B627695 : Blo 183802 627695 := bstep (se 1 (by rfl) ⟨470771, by rfl⟩ : syracuseStep 627695 = 941543) B941543
theorem B267247 : Blo 183802 267247 := bstep (se 1 (by rfl) ⟨200435, by rfl⟩ : syracuseStep 267247 = 400871) B400871
theorem B2659513 : Blo 183802 2659513 := bstep (se 2 (by rfl) ⟨997317, by rfl⟩ : syracuseStep 2659513 = 1994635) B1994635
theorem B890041 : Blo 183802 890041 := bstep (se 2 (by rfl) ⟨333765, by rfl⟩ : syracuseStep 890041 = 667531) B667531
theorem B234991 : Blo 183802 234991 := bstep (se 1 (by rfl) ⟨176243, by rfl⟩ : syracuseStep 234991 = 352487) B352487
theorem B6460979 : Blo 183802 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B1414745 : Blo 183802 1414745 := bstep (se 2 (by rfl) ⟨530529, by rfl⟩ : syracuseStep 1414745 = 1061059) B1061059
theorem B235163 : Blo 183802 235163 := bstep (se 1 (by rfl) ⟨176372, by rfl⟩ : syracuseStep 235163 = 352745) B352745
theorem B1513363 : Blo 183802 1513363 := bstep (se 1 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 1513363 = 2270045) B2270045
theorem B334163 : Blo 183802 334163 := bstep (se 1 (by rfl) ⟨250622, by rfl⟩ : syracuseStep 334163 = 501245) B501245
theorem B1056503 : Blo 183802 1056503 := bstep (se 1 (by rfl) ⟨792377, by rfl⟩ : syracuseStep 1056503 = 1584755) B1584755
theorem B9117535 : Blo 183802 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B401249 : Blo 183802 401249 := bstep (se 2 (by rfl) ⟨150468, by rfl⟩ : syracuseStep 401249 = 300937) B300937
theorem B663497 : Blo 183802 663497 := bstep (se 2 (by rfl) ⟨248811, by rfl⟩ : syracuseStep 663497 = 497623) B497623
theorem B1122281 : Blo 183802 1122281 := bstep (se 2 (by rfl) ⟨420855, by rfl⟩ : syracuseStep 1122281 = 841711) B841711
theorem B598205 : Blo 183802 598205 := bstep (se 3 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 598205 = 224327) B224327
theorem B1122569 : Blo 183802 1122569 := bstep (se 2 (by rfl) ⟨420963, by rfl⟩ : syracuseStep 1122569 = 841927) B841927
theorem B532831 : Blo 183802 532831 := bstep (se 1 (by rfl) ⟨399623, by rfl⟩ : syracuseStep 532831 = 799247) B799247
theorem B468089 : Blo 183802 468089 := bstep (se 2 (by rfl) ⟨175533, by rfl⟩ : syracuseStep 468089 = 351067) B351067
theorem B1778851 : Blo 183802 1778851 := bstep (se 1 (by rfl) ⟨1334138, by rfl⟩ : syracuseStep 1778851 = 2668277) B2668277
theorem B1189181 : Blo 183802 1189181 := bstep (se 3 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 1189181 = 445943) B445943
theorem B1418633 : Blo 183802 1418633 := bstep (se 2 (by rfl) ⟨531987, by rfl⟩ : syracuseStep 1418633 = 1063975) B1063975
theorem B632393 : Blo 183802 632393 := bstep (se 2 (by rfl) ⟨237147, by rfl⟩ : syracuseStep 632393 = 474295) B474295
theorem B698017 : Blo 183802 698017 := bstep (se 2 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 698017 = 523513) B523513
theorem B796463 : Blo 183802 796463 := bstep (se 1 (by rfl) ⟨597347, by rfl⟩ : syracuseStep 796463 = 1194695) B1194695
theorem B206815 : Blo 183802 206815 := bstep (se 1 (by rfl) ⟨155111, by rfl⟩ : syracuseStep 206815 = 310223) B310223
theorem B632879 : Blo 183802 632879 := bstep (se 1 (by rfl) ⟨474659, by rfl⟩ : syracuseStep 632879 = 949319) B949319
theorem B698489 : Blo 183802 698489 := bstep (se 2 (by rfl) ⟨261933, by rfl⟩ : syracuseStep 698489 = 523867) B523867
theorem B207463 : Blo 183802 207463 := bstep (se 1 (by rfl) ⟨155597, by rfl⟩ : syracuseStep 207463 = 311195) B311195
theorem B1354427 : Blo 183802 1354427 := bstep (se 1 (by rfl) ⟨1015820, by rfl⟩ : syracuseStep 1354427 = 2031641) B2031641
theorem B666899 : Blo 183802 666899 := bstep (se 1 (by rfl) ⟨500174, by rfl⟩ : syracuseStep 666899 = 1000349) B1000349
theorem B208255 : Blo 183802 208255 := bstep (se 1 (by rfl) ⟨156191, by rfl⟩ : syracuseStep 208255 = 312383) B312383
theorem B5058121 : Blo 183802 5058121 := bstep (se 2 (by rfl) ⟨1896795, by rfl⟩ : syracuseStep 5058121 = 3793591) B3793591
theorem B470711 : Blo 183802 470711 := bstep (se 1 (by rfl) ⟨353033, by rfl⟩ : syracuseStep 470711 = 706067) B706067
theorem B700265 : Blo 183802 700265 := bstep (se 2 (by rfl) ⟨262599, by rfl⟩ : syracuseStep 700265 = 525199) B525199
theorem B962441 : Blo 183802 962441 := bstep (se 2 (by rfl) ⟨360915, by rfl⟩ : syracuseStep 962441 = 721831) B721831
theorem B471167 : Blo 183802 471167 := bstep (se 1 (by rfl) ⟨353375, by rfl⟩ : syracuseStep 471167 = 706751) B706751
theorem B1192157 : Blo 183802 1192157 := bstep (se 3 (by rfl) ⟨223529, by rfl⟩ : syracuseStep 1192157 = 447059) B447059
theorem B2666843 : Blo 183802 2666843 := bstep (se 1 (by rfl) ⟨2000132, by rfl⟩ : syracuseStep 2666843 = 4000265) B4000265
theorem B209659 : Blo 183802 209659 := bstep (se 1 (by rfl) ⟨157244, by rfl⟩ : syracuseStep 209659 = 314489) B314489
theorem B1684435 : Blo 183802 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B472169 : Blo 183802 472169 := bstep (se 2 (by rfl) ⟨177063, by rfl⟩ : syracuseStep 472169 = 354127) B354127
theorem B1062017 : Blo 183802 1062017 := bstep (se 2 (by rfl) ⟨398256, by rfl⟩ : syracuseStep 1062017 = 796513) B796513
theorem B275879 : Blo 183802 275879 := bstep (se 1 (by rfl) ⟨206909, by rfl⟩ : syracuseStep 275879 = 413819) B413819
theorem B210415 : Blo 183802 210415 := bstep (se 1 (by rfl) ⟨157811, by rfl⟩ : syracuseStep 210415 = 315623) B315623
theorem B276059 : Blo 183802 276059 := bstep (se 1 (by rfl) ⟨207044, by rfl⟩ : syracuseStep 276059 = 414089) B414089
theorem B210523 : Blo 183802 210523 := bstep (se 1 (by rfl) ⟨157892, by rfl⟩ : syracuseStep 210523 = 315785) B315785
theorem B1095277 : Blo 183802 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B210811 : Blo 183802 210811 := bstep (se 1 (by rfl) ⟨158108, by rfl⟩ : syracuseStep 210811 = 316217) B316217
theorem B210847 : Blo 183802 210847 := bstep (se 1 (by rfl) ⟨158135, by rfl⟩ : syracuseStep 210847 = 316271) B316271
theorem B276521 : Blo 183802 276521 := bstep (se 2 (by rfl) ⟨103695, by rfl⟩ : syracuseStep 276521 = 207391) B207391
theorem B276551 : Blo 183802 276551 := bstep (se 1 (by rfl) ⟨207413, by rfl⟩ : syracuseStep 276551 = 414827) B414827
theorem B702695 : Blo 183802 702695 := bstep (se 1 (by rfl) ⟨527021, by rfl⟩ : syracuseStep 702695 = 1054043) B1054043
theorem B473323 : Blo 183802 473323 := bstep (se 1 (by rfl) ⟨354992, by rfl⟩ : syracuseStep 473323 = 709985) B709985
theorem B1063207 : Blo 183802 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B702877 : Blo 183802 702877 := bstep (se 3 (by rfl) ⟨131789, by rfl⟩ : syracuseStep 702877 = 263579) B263579
theorem B473543 : Blo 183802 473543 := bstep (se 1 (by rfl) ⟨355157, by rfl⟩ : syracuseStep 473543 = 710315) B710315
theorem B276935 : Blo 183802 276935 := bstep (se 1 (by rfl) ⟨207701, by rfl⟩ : syracuseStep 276935 = 415403) B415403
theorem B277151 : Blo 183802 277151 := bstep (se 1 (by rfl) ⟨207863, by rfl⟩ : syracuseStep 277151 = 415727) B415727
theorem B473759 : Blo 183802 473759 := bstep (se 1 (by rfl) ⟨355319, by rfl⟩ : syracuseStep 473759 = 710639) B710639
theorem B277295 : Blo 183802 277295 := bstep (se 1 (by rfl) ⟨207971, by rfl⟩ : syracuseStep 277295 = 415943) B415943
theorem B277415 : Blo 183802 277415 := bstep (se 1 (by rfl) ⟨208061, by rfl⟩ : syracuseStep 277415 = 416123) B416123
theorem B670675 : Blo 183802 670675 := bstep (se 1 (by rfl) ⟨503006, by rfl⟩ : syracuseStep 670675 = 1006013) B1006013
theorem B277595 : Blo 183802 277595 := bstep (se 1 (by rfl) ⟨208196, by rfl⟩ : syracuseStep 277595 = 416393) B416393
theorem B1064083 : Blo 183802 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B933281 : Blo 183802 933281 := bstep (se 2 (by rfl) ⟨349980, by rfl⟩ : syracuseStep 933281 = 699961) B699961
theorem B277967 : Blo 183802 277967 := bstep (se 1 (by rfl) ⟨208475, by rfl⟩ : syracuseStep 277967 = 416951) B416951
theorem B474731 : Blo 183802 474731 := bstep (se 1 (by rfl) ⟨356048, by rfl⟩ : syracuseStep 474731 = 712097) B712097
theorem B4505311 : Blo 183802 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B278351 : Blo 183802 278351 := bstep (se 1 (by rfl) ⟨208763, by rfl⟩ : syracuseStep 278351 = 417527) B417527
theorem B1458109 : Blo 183802 1458109 := bstep (se 3 (by rfl) ⟨273395, by rfl⟩ : syracuseStep 1458109 = 546791) B546791
theorem B278471 : Blo 183802 278471 := bstep (se 1 (by rfl) ⟨208853, by rfl⟩ : syracuseStep 278471 = 417707) B417707
theorem B704807 : Blo 183802 704807 := bstep (se 1 (by rfl) ⟨528605, by rfl⟩ : syracuseStep 704807 = 1057211) B1057211
theorem B278831 : Blo 183802 278831 := bstep (se 1 (by rfl) ⟨209123, by rfl⟩ : syracuseStep 278831 = 418247) B418247
theorem B279071 : Blo 183802 279071 := bstep (se 1 (by rfl) ⟨209303, by rfl⟩ : syracuseStep 279071 = 418607) B418607
theorem B312511 : Blo 183802 312511 := bstep (se 1 (by rfl) ⟨234383, by rfl⟩ : syracuseStep 312511 = 468767) B468767
theorem B279743 : Blo 183802 279743 := bstep (se 1 (by rfl) ⟨209807, by rfl⟩ : syracuseStep 279743 = 419615) B419615
theorem B279887 : Blo 183802 279887 := bstep (se 1 (by rfl) ⟨209915, by rfl⟩ : syracuseStep 279887 = 419831) B419831
theorem B279977 : Blo 183802 279977 := bstep (se 2 (by rfl) ⟨104991, by rfl⟩ : syracuseStep 279977 = 209983) B209983
theorem B280127 : Blo 183802 280127 := bstep (se 1 (by rfl) ⟨210095, by rfl⟩ : syracuseStep 280127 = 420191) B420191
theorem B280169 : Blo 183802 280169 := bstep (se 2 (by rfl) ⟨105063, by rfl⟩ : syracuseStep 280169 = 210127) B210127
theorem B378475 : Blo 183802 378475 := bstep (se 1 (by rfl) ⟨283856, by rfl⟩ : syracuseStep 378475 = 567713) B567713
theorem B935711 : Blo 183802 935711 := bstep (se 1 (by rfl) ⟨701783, by rfl⟩ : syracuseStep 935711 = 1403567) B1403567
theorem B2705183 : Blo 183802 2705183 := bstep (se 1 (by rfl) ⟨2028887, by rfl⟩ : syracuseStep 2705183 = 4057775) B4057775
theorem B313375 : Blo 183802 313375 := bstep (se 1 (by rfl) ⟨235031, by rfl⟩ : syracuseStep 313375 = 470063) B470063
theorem B280607 : Blo 183802 280607 := bstep (se 1 (by rfl) ⟨210455, by rfl⟩ : syracuseStep 280607 = 420911) B420911
theorem B280799 : Blo 183802 280799 := bstep (se 1 (by rfl) ⟨210599, by rfl⟩ : syracuseStep 280799 = 421199) B421199
theorem B280859 : Blo 183802 280859 := bstep (se 1 (by rfl) ⟨210644, by rfl⟩ : syracuseStep 280859 = 421289) B421289
theorem B313679 : Blo 183802 313679 := bstep (se 1 (by rfl) ⟨235259, by rfl⟩ : syracuseStep 313679 = 470519) B470519
theorem B3197393 : Blo 183802 3197393 := bstep (se 2 (by rfl) ⟨1199022, by rfl⟩ : syracuseStep 3197393 = 2398045) B2398045
theorem B281183 : Blo 183802 281183 := bstep (se 1 (by rfl) ⟨210887, by rfl⟩ : syracuseStep 281183 = 421775) B421775
theorem B281465 : Blo 183802 281465 := bstep (se 2 (by rfl) ⟨105549, by rfl⟩ : syracuseStep 281465 = 211099) B211099
theorem B281513 : Blo 183802 281513 := bstep (se 2 (by rfl) ⟨105567, by rfl⟩ : syracuseStep 281513 = 211135) B211135
theorem B281663 : Blo 183802 281663 := bstep (se 1 (by rfl) ⟨211247, by rfl⟩ : syracuseStep 281663 = 422495) B422495
theorem B314543 : Blo 183802 314543 := bstep (se 1 (by rfl) ⟨235907, by rfl⟩ : syracuseStep 314543 = 471815) B471815
theorem B183911 : Blo 183802 183911 := bstep (se 1 (by rfl) ⟨137933, by rfl⟩ : syracuseStep 183911 = 275867) B275867
theorem B708221 : Blo 183802 708221 := bstep (se 3 (by rfl) ⟨132791, by rfl⟩ : syracuseStep 708221 = 265583) B265583
theorem B184059 : Blo 183802 184059 := bstep (se 1 (by rfl) ⟨138044, by rfl⟩ : syracuseStep 184059 = 276089) B276089
theorem B184127 : Blo 183802 184127 := bstep (se 1 (by rfl) ⟨138095, by rfl⟩ : syracuseStep 184127 = 276191) B276191
theorem B413567 : Blo 183802 413567 := bstep (se 1 (by rfl) ⟨310175, by rfl⟩ : syracuseStep 413567 = 620351) B620351
theorem B184191 : Blo 183802 184191 := bstep (se 1 (by rfl) ⟨138143, by rfl⟩ : syracuseStep 184191 = 276287) B276287
theorem B184303 : Blo 183802 184303 := bstep (se 1 (by rfl) ⟨138227, by rfl⟩ : syracuseStep 184303 = 276455) B276455
theorem B184315 : Blo 183802 184315 := bstep (se 1 (by rfl) ⟨138236, by rfl⟩ : syracuseStep 184315 = 276473) B276473
theorem B937979 : Blo 183802 937979 := bstep (se 1 (by rfl) ⟨703484, by rfl⟩ : syracuseStep 937979 = 1406969) B1406969
theorem B184383 : Blo 183802 184383 := bstep (se 1 (by rfl) ⟨138287, by rfl⟩ : syracuseStep 184383 = 276575) B276575
theorem B184423 : Blo 183802 184423 := bstep (se 1 (by rfl) ⟨138317, by rfl⟩ : syracuseStep 184423 = 276635) B276635
theorem B184447 : Blo 183802 184447 := bstep (se 1 (by rfl) ⟨138335, by rfl⟩ : syracuseStep 184447 = 276671) B276671
theorem B708763 : Blo 183802 708763 := bstep (se 1 (by rfl) ⟨531572, by rfl⟩ : syracuseStep 708763 = 1063145) B1063145
theorem B184475 : Blo 183802 184475 := bstep (se 1 (by rfl) ⟨138356, by rfl⟩ : syracuseStep 184475 = 276713) B276713
theorem B184679 : Blo 183802 184679 := bstep (se 1 (by rfl) ⟨138509, by rfl⟩ : syracuseStep 184679 = 277019) B277019
theorem B184731 : Blo 183802 184731 := bstep (se 1 (by rfl) ⟨138548, by rfl⟩ : syracuseStep 184731 = 277097) B277097
theorem B185083 : Blo 183802 185083 := bstep (se 1 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 185083 = 277625) B277625
theorem B414521 : Blo 183802 414521 := bstep (se 2 (by rfl) ⟨155445, by rfl⟩ : syracuseStep 414521 = 310891) B310891
theorem B185151 : Blo 183802 185151 := bstep (se 1 (by rfl) ⟨138863, by rfl⟩ : syracuseStep 185151 = 277727) B277727
theorem B185179 : Blo 183802 185179 := bstep (se 1 (by rfl) ⟨138884, by rfl⟩ : syracuseStep 185179 = 277769) B277769
theorem B349039 : Blo 183802 349039 := bstep (se 1 (by rfl) ⟨261779, by rfl⟩ : syracuseStep 349039 = 523559) B523559
theorem B414575 : Blo 183802 414575 := bstep (se 1 (by rfl) ⟨310931, by rfl⟩ : syracuseStep 414575 = 621863) B621863
theorem B185247 : Blo 183802 185247 := bstep (se 1 (by rfl) ⟨138935, by rfl⟩ : syracuseStep 185247 = 277871) B277871
theorem B1496045 : Blo 183802 1496045 := bstep (se 3 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 1496045 = 561017) B561017
theorem B185327 : Blo 183802 185327 := bstep (se 1 (by rfl) ⟨138995, by rfl⟩ : syracuseStep 185327 = 277991) B277991
theorem B316399 : Blo 183802 316399 := bstep (se 1 (by rfl) ⟨237299, by rfl⟩ : syracuseStep 316399 = 474599) B474599
theorem B2151461 : Blo 183802 2151461 := bstep (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) B403399
theorem B185415 : Blo 183802 185415 := bstep (se 1 (by rfl) ⟨139061, by rfl⟩ : syracuseStep 185415 = 278123) B278123
theorem B185499 : Blo 183802 185499 := bstep (se 1 (by rfl) ⟨139124, by rfl⟩ : syracuseStep 185499 = 278249) B278249
theorem B414881 : Blo 183802 414881 := bstep (se 2 (by rfl) ⟨155580, by rfl⟩ : syracuseStep 414881 = 311161) B311161
theorem B185595 : Blo 183802 185595 := bstep (se 1 (by rfl) ⟨139196, by rfl⟩ : syracuseStep 185595 = 278393) B278393
theorem B185663 : Blo 183802 185663 := bstep (se 1 (by rfl) ⟨139247, by rfl⟩ : syracuseStep 185663 = 278495) B278495
theorem B415151 : Blo 183802 415151 := bstep (se 1 (by rfl) ⟨311363, by rfl⟩ : syracuseStep 415151 = 622727) B622727
theorem B185831 : Blo 183802 185831 := bstep (se 1 (by rfl) ⟨139373, by rfl⟩ : syracuseStep 185831 = 278747) B278747
theorem B185839 : Blo 183802 185839 := bstep (se 1 (by rfl) ⟨139379, by rfl⟩ : syracuseStep 185839 = 278759) B278759
theorem B185947 : Blo 183802 185947 := bstep (se 1 (by rfl) ⟨139460, by rfl⟩ : syracuseStep 185947 = 278921) B278921
theorem B186011 : Blo 183802 186011 := bstep (se 1 (by rfl) ⟨139508, by rfl⟩ : syracuseStep 186011 = 279017) B279017
theorem B186095 : Blo 183802 186095 := bstep (se 1 (by rfl) ⟨139571, by rfl⟩ : syracuseStep 186095 = 279143) B279143
theorem B186183 : Blo 183802 186183 := bstep (se 1 (by rfl) ⟨139637, by rfl⟩ : syracuseStep 186183 = 279275) B279275
theorem B710471 : Blo 183802 710471 := bstep (se 1 (by rfl) ⟨532853, by rfl⟩ : syracuseStep 710471 = 1065707) B1065707
theorem B2545481 : Blo 183802 2545481 := bstep (se 2 (by rfl) ⟨954555, by rfl⟩ : syracuseStep 2545481 = 1909111) B1909111
theorem B186203 : Blo 183802 186203 := bstep (se 1 (by rfl) ⟨139652, by rfl⟩ : syracuseStep 186203 = 279305) B279305
theorem B186271 : Blo 183802 186271 := bstep (se 1 (by rfl) ⟨139703, by rfl⟩ : syracuseStep 186271 = 279407) B279407
theorem B186439 : Blo 183802 186439 := bstep (se 1 (by rfl) ⟨139829, by rfl⟩ : syracuseStep 186439 = 279659) B279659
theorem B350345 : Blo 183802 350345 := bstep (se 2 (by rfl) ⟨131379, by rfl⟩ : syracuseStep 350345 = 262759) B262759
theorem B186599 : Blo 183802 186599 := bstep (se 1 (by rfl) ⟨139949, by rfl⟩ : syracuseStep 186599 = 279899) B279899
theorem B416159 : Blo 183802 416159 := bstep (se 1 (by rfl) ⟨312119, by rfl⟩ : syracuseStep 416159 = 624239) B624239
theorem B186783 : Blo 183802 186783 := bstep (se 1 (by rfl) ⟨140087, by rfl⟩ : syracuseStep 186783 = 280175) B280175
theorem B186831 : Blo 183802 186831 := bstep (se 1 (by rfl) ⟨140123, by rfl⟩ : syracuseStep 186831 = 280247) B280247
theorem B416231 : Blo 183802 416231 := bstep (se 1 (by rfl) ⟨312173, by rfl⟩ : syracuseStep 416231 = 624347) B624347
theorem B186855 : Blo 183802 186855 := bstep (se 1 (by rfl) ⟨140141, by rfl⟩ : syracuseStep 186855 = 280283) B280283
theorem B186971 : Blo 183802 186971 := bstep (se 1 (by rfl) ⟨140228, by rfl⟩ : syracuseStep 186971 = 280457) B280457
theorem B187039 : Blo 183802 187039 := bstep (se 1 (by rfl) ⟨140279, by rfl⟩ : syracuseStep 187039 = 280559) B280559
theorem B187207 : Blo 183802 187207 := bstep (se 1 (by rfl) ⟨140405, by rfl⟩ : syracuseStep 187207 = 280811) B280811
theorem B187247 : Blo 183802 187247 := bstep (se 1 (by rfl) ⟨140435, by rfl⟩ : syracuseStep 187247 = 280871) B280871
theorem B187303 : Blo 183802 187303 := bstep (se 1 (by rfl) ⟨140477, by rfl⟩ : syracuseStep 187303 = 280955) B280955
theorem B351211 : Blo 183802 351211 := bstep (se 1 (by rfl) ⟨263408, by rfl⟩ : syracuseStep 351211 = 526817) B526817
theorem B187483 : Blo 183802 187483 := bstep (se 1 (by rfl) ⟨140612, by rfl⟩ : syracuseStep 187483 = 281225) B281225
theorem B187599 : Blo 183802 187599 := bstep (se 1 (by rfl) ⟨140699, by rfl⟩ : syracuseStep 187599 = 281399) B281399
theorem B187623 : Blo 183802 187623 := bstep (se 1 (by rfl) ⟨140717, by rfl⟩ : syracuseStep 187623 = 281435) B281435
theorem B417095 : Blo 183802 417095 := bstep (se 1 (by rfl) ⟨312821, by rfl⟩ : syracuseStep 417095 = 625643) B625643
theorem B187719 : Blo 183802 187719 := bstep (se 1 (by rfl) ⟨140789, by rfl⟩ : syracuseStep 187719 = 281579) B281579
theorem B417131 : Blo 183802 417131 := bstep (se 1 (by rfl) ⟨312848, by rfl⟩ : syracuseStep 417131 = 625697) B625697
theorem B417257 : Blo 183802 417257 := bstep (se 2 (by rfl) ⟨156471, by rfl⟩ : syracuseStep 417257 = 312943) B312943
theorem B253417 : Blo 183802 253417 := bstep (se 2 (by rfl) ⟨95031, by rfl⟩ : syracuseStep 253417 = 190063) B190063
theorem B417401 : Blo 183802 417401 := bstep (se 2 (by rfl) ⟨156525, by rfl⟩ : syracuseStep 417401 = 313051) B313051
theorem B188327 : Blo 183802 188327 := bstep (se 1 (by rfl) ⟨141245, by rfl⟩ : syracuseStep 188327 = 282491) B282491
theorem B418103 : Blo 183802 418103 := bstep (se 1 (by rfl) ⟨313577, by rfl⟩ : syracuseStep 418103 = 627155) B627155
theorem B13656721 : Blo 183802 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B419129 : Blo 183802 419129 := bstep (se 2 (by rfl) ⟨157173, by rfl⟩ : syracuseStep 419129 = 314347) B314347
theorem B419399 : Blo 183802 419399 := bstep (se 1 (by rfl) ⟨314549, by rfl⟩ : syracuseStep 419399 = 629099) B629099
theorem B419579 : Blo 183802 419579 := bstep (se 1 (by rfl) ⟨314684, by rfl⟩ : syracuseStep 419579 = 629369) B629369
theorem B354203 : Blo 183802 354203 := bstep (se 1 (by rfl) ⟨265652, by rfl⟩ : syracuseStep 354203 = 531305) B531305
theorem B419867 : Blo 183802 419867 := bstep (se 1 (by rfl) ⟨314900, by rfl⟩ : syracuseStep 419867 = 629801) B629801
theorem B223279 : Blo 183802 223279 := bstep (se 1 (by rfl) ⟨167459, by rfl⟩ : syracuseStep 223279 = 334919) B334919
theorem B1010207 : Blo 183802 1010207 := bstep (se 1 (by rfl) ⟨757655, by rfl⟩ : syracuseStep 1010207 = 1515311) B1515311
theorem B1698889 : Blo 183802 1698889 := bstep (se 2 (by rfl) ⟨637083, by rfl⟩ : syracuseStep 1698889 = 1274167) B1274167
theorem B421129 : Blo 183802 421129 := bstep (se 2 (by rfl) ⟨157923, by rfl⟩ : syracuseStep 421129 = 315847) B315847
theorem B421343 : Blo 183802 421343 := bstep (se 1 (by rfl) ⟨316007, by rfl⟩ : syracuseStep 421343 = 632015) B632015
theorem B421559 : Blo 183802 421559 := bstep (se 1 (by rfl) ⟨316169, by rfl⟩ : syracuseStep 421559 = 632339) B632339
theorem B421985 : Blo 183802 421985 := bstep (se 2 (by rfl) ⟨158244, by rfl⟩ : syracuseStep 421985 = 316489) B316489
theorem B1896635 : Blo 183802 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B6025427 : Blo 183802 6025427 := bstep (se 1 (by rfl) ⟨4519070, by rfl⟩ : syracuseStep 6025427 = 9038141) B9038141
theorem B422351 : Blo 183802 422351 := bstep (se 1 (by rfl) ⟨316763, by rfl⟩ : syracuseStep 422351 = 633527) B633527
theorem B1864225 : Blo 183802 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B946727 : Blo 183802 946727 := bstep (se 1 (by rfl) ⟨710045, by rfl⟩ : syracuseStep 946727 = 1420091) B1420091
theorem B3535559 : Blo 183802 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B1438859 : Blo 183802 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B1602935 : Blo 183802 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B718247 : Blo 183802 718247 := bstep (se 1 (by rfl) ⟨538685, by rfl⟩ : syracuseStep 718247 = 1077371) B1077371
theorem B1013971 : Blo 183802 1013971 := bstep (se 1 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 1013971 = 1520957) B1520957
theorem B620891 : Blo 183802 620891 := bstep (se 1 (by rfl) ⟨465668, by rfl⟩ : syracuseStep 620891 = 931337) B931337
theorem B948833 : Blo 183802 948833 := bstep (se 2 (by rfl) ⟨355812, by rfl⟩ : syracuseStep 948833 = 711625) B711625
theorem B621161 : Blo 183802 621161 := bstep (se 2 (by rfl) ⟨232935, by rfl⟩ : syracuseStep 621161 = 465871) B465871
theorem B1276573 : Blo 183802 1276573 := bstep (se 3 (by rfl) ⟨239357, by rfl⟩ : syracuseStep 1276573 = 478715) B478715
theorem B949643 : Blo 183802 949643 := bstep (se 1 (by rfl) ⟨712232, by rfl⟩ : syracuseStep 949643 = 1424465) B1424465
theorem B1408427 : Blo 183802 1408427 := bstep (se 1 (by rfl) ⟨1056320, by rfl⟩ : syracuseStep 1408427 = 2112641) B2112641
theorem B1113679 : Blo 183802 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B589465 : Blo 183802 589465 := bstep (se 2 (by rfl) ⟨221049, by rfl⟩ : syracuseStep 589465 = 442099) B442099
theorem B851791 : Blo 183802 851791 := bstep (se 1 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 851791 = 1277687) B1277687
theorem B196463 : Blo 183802 196463 := bstep (se 1 (by rfl) ⟨147347, by rfl⟩ : syracuseStep 196463 = 294695) B294695
theorem B1048463 : Blo 183802 1048463 := bstep (se 1 (by rfl) ⟨786347, by rfl⟩ : syracuseStep 1048463 = 1572695) B1572695
theorem B623807 : Blo 183802 623807 := bstep (se 1 (by rfl) ⟨467855, by rfl⟩ : syracuseStep 623807 = 935711) B935711
theorem B1803455 : Blo 183802 1803455 := bstep (se 1 (by rfl) ⟨1352591, by rfl⟩ : syracuseStep 1803455 = 2705183) B2705183
theorem B2131595 : Blo 183802 2131595 := bstep (se 1 (by rfl) ⟨1598696, by rfl⟩ : syracuseStep 2131595 = 3197393) B3197393
theorem B526475 : Blo 183802 526475 := bstep (se 1 (by rfl) ⟨394856, by rfl⟩ : syracuseStep 526475 = 789713) B789713
theorem B625319 : Blo 183802 625319 := bstep (se 1 (by rfl) ⟨468989, by rfl⟩ : syracuseStep 625319 = 937979) B937979
theorem B1706771 : Blo 183802 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B265447 : Blo 183802 265447 := bstep (se 1 (by rfl) ⟨199085, by rfl⟩ : syracuseStep 265447 = 398171) B398171
theorem B528457 : Blo 183802 528457 := bstep (se 2 (by rfl) ⟨198171, by rfl⟩ : syracuseStep 528457 = 396343) B396343
theorem B2265185 : Blo 183802 2265185 := bstep (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) B1698889
theorem B1052837 : Blo 183802 1052837 := bstep (se 4 (by rfl) ⟨98703, by rfl⟩ : syracuseStep 1052837 = 197407) B197407
theorem B561505 : Blo 183802 561505 := bstep (se 2 (by rfl) ⟨210564, by rfl⟩ : syracuseStep 561505 = 421129) B421129
theorem B627101 : Blo 183802 627101 := bstep (se 3 (by rfl) ⟨117581, by rfl⟩ : syracuseStep 627101 = 235163) B235163
theorem B267499 : Blo 183802 267499 := bstep (se 1 (by rfl) ⟨200624, by rfl⟩ : syracuseStep 267499 = 401249) B401249
theorem B891101 : Blo 183802 891101 := bstep (se 3 (by rfl) ⟨167081, by rfl⟩ : syracuseStep 891101 = 334163) B334163
theorem B530849 : Blo 183802 530849 := bstep (se 2 (by rfl) ⟨199068, by rfl⟩ : syracuseStep 530849 = 398137) B398137
theorem B465385 : Blo 183802 465385 := bstep (se 2 (by rfl) ⟨174519, by rfl⟩ : syracuseStep 465385 = 349039) B349039
theorem B530975 : Blo 183802 530975 := bstep (se 1 (by rfl) ⟨398231, by rfl⟩ : syracuseStep 530975 = 796463) B796463
theorem B236135 : Blo 183802 236135 := bstep (se 1 (by rfl) ⟨177101, by rfl⟩ : syracuseStep 236135 = 354203) B354203
theorem B465659 : Blo 183802 465659 := bstep (se 1 (by rfl) ⟨349244, by rfl⟩ : syracuseStep 465659 = 698489) B698489
theorem B3546017 : Blo 183802 3546017 := bstep (se 2 (by rfl) ⟨1329756, by rfl⟩ : syracuseStep 3546017 = 2659513) B2659513
theorem B1186721 : Blo 183802 1186721 := bstep (se 2 (by rfl) ⟨445020, by rfl⟩ : syracuseStep 1186721 = 890041) B890041
theorem B466843 : Blo 183802 466843 := bstep (se 1 (by rfl) ⟨350132, by rfl⟩ : syracuseStep 466843 = 700265) B700265
theorem B1056685 : Blo 183802 1056685 := bstep (se 3 (by rfl) ⟨198128, by rfl⟩ : syracuseStep 1056685 = 396257) B396257
theorem B794771 : Blo 183802 794771 := bstep (se 1 (by rfl) ⟨596078, by rfl⟩ : syracuseStep 794771 = 1192157) B1192157
theorem B1777895 : Blo 183802 1777895 := bstep (se 1 (by rfl) ⟨1333421, by rfl⟩ : syracuseStep 1777895 = 2666843) B2666843
theorem B1351961 : Blo 183802 1351961 := bstep (se 2 (by rfl) ⟨506985, by rfl⟩ : syracuseStep 1351961 = 1013971) B1013971
theorem B631097 : Blo 183802 631097 := bstep (se 2 (by rfl) ⟨236661, by rfl⟩ : syracuseStep 631097 = 473323) B473323
theorem B631151 : Blo 183802 631151 := bstep (se 1 (by rfl) ⟨473363, by rfl⟩ : syracuseStep 631151 = 946727) B946727
theorem B1417609 : Blo 183802 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B959239 : Blo 183802 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B894233 : Blo 183802 894233 := bstep (se 2 (by rfl) ⟨335337, by rfl⟩ : syracuseStep 894233 = 670675) B670675
theorem B468281 : Blo 183802 468281 := bstep (se 2 (by rfl) ⟨175605, by rfl⟩ : syracuseStep 468281 = 351211) B351211
theorem B468463 : Blo 183802 468463 := bstep (se 1 (by rfl) ⟨351347, by rfl⟩ : syracuseStep 468463 = 702695) B702695
theorem B1418777 : Blo 183802 1418777 := bstep (se 2 (by rfl) ⟨532041, by rfl⟩ : syracuseStep 1418777 = 1064083) B1064083
theorem B632555 : Blo 183802 632555 := bstep (se 1 (by rfl) ⟨474416, by rfl⟩ : syracuseStep 632555 = 948833) B948833
theorem B337889 : Blo 183802 337889 := bstep (se 2 (by rfl) ⟨126708, by rfl⟩ : syracuseStep 337889 = 253417) B253417
theorem B1484905 : Blo 183802 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B633095 : Blo 183802 633095 := bstep (se 1 (by rfl) ⟨474821, by rfl⟩ : syracuseStep 633095 = 949643) B949643
theorem B6007081 : Blo 183802 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B502205 : Blo 183802 502205 := bstep (se 3 (by rfl) ⟨94163, by rfl⟩ : syracuseStep 502205 = 188327) B188327
theorem B1944145 : Blo 183802 1944145 := bstep (se 2 (by rfl) ⟨729054, by rfl⟩ : syracuseStep 1944145 = 1458109) B1458109
theorem B698975 : Blo 183802 698975 := bstep (se 1 (by rfl) ⟨524231, by rfl⟩ : syracuseStep 698975 = 1048463) B1048463
theorem B469871 : Blo 183802 469871 := bstep (se 1 (by rfl) ⟨352403, by rfl⟩ : syracuseStep 469871 = 704807) B704807
theorem B4763285 : Blo 183802 4763285 := bstep (se 6 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 4763285 = 223279) B223279
theorem B6795251 : Blo 183802 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B2371801 : Blo 183802 2371801 := bstep (se 2 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 2371801 = 1778851) B1778851
theorem B209119 : Blo 183802 209119 := bstep (se 1 (by rfl) ⟨156839, by rfl⟩ : syracuseStep 209119 = 313679) B313679
theorem B209695 : Blo 183802 209695 := bstep (se 1 (by rfl) ⟨157271, by rfl⟩ : syracuseStep 209695 = 314543) B314543
theorem B930689 : Blo 183802 930689 := bstep (se 2 (by rfl) ⟨349008, by rfl⟩ : syracuseStep 930689 = 698017) B698017
theorem B701419 : Blo 183802 701419 := bstep (se 1 (by rfl) ⟨526064, by rfl⟩ : syracuseStep 701419 = 1052129) B1052129
theorem B1749995 : Blo 183802 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B275711 : Blo 183802 275711 := bstep (se 1 (by rfl) ⟨206783, by rfl⟩ : syracuseStep 275711 = 413567) B413567
theorem B275753 : Blo 183802 275753 := bstep (se 2 (by rfl) ⟨103407, by rfl⟩ : syracuseStep 275753 = 206815) B206815
theorem B276347 : Blo 183802 276347 := bstep (se 1 (by rfl) ⟨207260, by rfl⟩ : syracuseStep 276347 = 414521) B414521
theorem B276383 : Blo 183802 276383 := bstep (se 1 (by rfl) ⟨207287, by rfl⟩ : syracuseStep 276383 = 414575) B414575
theorem B997363 : Blo 183802 997363 := bstep (se 1 (by rfl) ⟨748022, by rfl⟩ : syracuseStep 997363 = 1496045) B1496045
theorem B276587 : Blo 183802 276587 := bstep (se 1 (by rfl) ⟨207440, by rfl⟩ : syracuseStep 276587 = 414881) B414881
theorem B276617 : Blo 183802 276617 := bstep (se 2 (by rfl) ⟨103731, by rfl⟩ : syracuseStep 276617 = 207463) B207463
theorem B276767 : Blo 183802 276767 := bstep (se 1 (by rfl) ⟨207575, by rfl⟩ : syracuseStep 276767 = 415151) B415151
theorem B473647 : Blo 183802 473647 := bstep (se 1 (by rfl) ⟨355235, by rfl⟩ : syracuseStep 473647 = 710471) B710471
theorem B277439 : Blo 183802 277439 := bstep (se 1 (by rfl) ⟨208079, by rfl⟩ : syracuseStep 277439 = 416159) B416159
theorem B277487 : Blo 183802 277487 := bstep (se 1 (by rfl) ⟨208115, by rfl⟩ : syracuseStep 277487 = 416231) B416231
theorem B277673 : Blo 183802 277673 := bstep (se 2 (by rfl) ⟨104127, by rfl⟩ : syracuseStep 277673 = 208255) B208255
theorem B278063 : Blo 183802 278063 := bstep (se 1 (by rfl) ⟨208547, by rfl⟩ : syracuseStep 278063 = 417095) B417095
theorem B278087 : Blo 183802 278087 := bstep (se 1 (by rfl) ⟨208565, by rfl⟩ : syracuseStep 278087 = 417131) B417131
theorem B704153 : Blo 183802 704153 := bstep (se 2 (by rfl) ⟨264057, by rfl⟩ : syracuseStep 704153 = 528115) B528115
theorem B278171 : Blo 183802 278171 := bstep (se 1 (by rfl) ⟨208628, by rfl⟩ : syracuseStep 278171 = 417257) B417257
theorem B278267 : Blo 183802 278267 := bstep (se 1 (by rfl) ⟨208700, by rfl⟩ : syracuseStep 278267 = 417401) B417401
theorem B704335 : Blo 183802 704335 := bstep (se 1 (by rfl) ⟨528251, by rfl⟩ : syracuseStep 704335 = 1056503) B1056503
theorem B442331 : Blo 183802 442331 := bstep (se 1 (by rfl) ⟨331748, by rfl⟩ : syracuseStep 442331 = 663497) B663497
theorem B1064933 : Blo 183802 1064933 := bstep (se 4 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 1064933 = 199675) B199675
theorem B278735 : Blo 183802 278735 := bstep (se 1 (by rfl) ⟨209051, by rfl⟩ : syracuseStep 278735 = 418103) B418103
theorem B934253 : Blo 183802 934253 := bstep (se 3 (by rfl) ⟨175172, by rfl⟩ : syracuseStep 934253 = 350345) B350345
theorem B312059 : Blo 183802 312059 := bstep (se 1 (by rfl) ⟨234044, by rfl⟩ : syracuseStep 312059 = 468089) B468089
theorem B279419 : Blo 183802 279419 := bstep (se 1 (by rfl) ⟨209564, by rfl⟩ : syracuseStep 279419 = 419129) B419129
theorem B279545 : Blo 183802 279545 := bstep (se 2 (by rfl) ⟨104829, by rfl⟩ : syracuseStep 279545 = 209659) B209659
theorem B279599 : Blo 183802 279599 := bstep (se 1 (by rfl) ⟨209699, by rfl⟩ : syracuseStep 279599 = 419399) B419399
theorem B279719 : Blo 183802 279719 := bstep (se 1 (by rfl) ⟨209789, by rfl⟩ : syracuseStep 279719 = 419579) B419579
theorem B2245913 : Blo 183802 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B279911 : Blo 183802 279911 := bstep (se 1 (by rfl) ⟨209933, by rfl⟩ : syracuseStep 279911 = 419867) B419867
theorem B673471 : Blo 183802 673471 := bstep (se 1 (by rfl) ⟨505103, by rfl⟩ : syracuseStep 673471 = 1010207) B1010207
theorem B902951 : Blo 183802 902951 := bstep (se 1 (by rfl) ⟨677213, by rfl⟩ : syracuseStep 902951 = 1354427) B1354427
theorem B313321 : Blo 183802 313321 := bstep (se 2 (by rfl) ⟨117495, by rfl⟩ : syracuseStep 313321 = 234991) B234991
theorem B280553 : Blo 183802 280553 := bstep (se 2 (by rfl) ⟨105207, by rfl⟩ : syracuseStep 280553 = 210415) B210415
theorem B280697 : Blo 183802 280697 := bstep (se 2 (by rfl) ⟨105261, by rfl⟩ : syracuseStep 280697 = 210523) B210523
theorem B1460369 : Blo 183802 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B444599 : Blo 183802 444599 := bstep (se 1 (by rfl) ⟨333449, by rfl⟩ : syracuseStep 444599 = 666899) B666899
theorem B280895 : Blo 183802 280895 := bstep (se 1 (by rfl) ⟨210671, by rfl⟩ : syracuseStep 280895 = 421343) B421343
theorem B313807 : Blo 183802 313807 := bstep (se 1 (by rfl) ⟨235355, by rfl⟩ : syracuseStep 313807 = 470711) B470711
theorem B281039 : Blo 183802 281039 := bstep (se 1 (by rfl) ⟨210779, by rfl⟩ : syracuseStep 281039 = 421559) B421559
theorem B281081 : Blo 183802 281081 := bstep (se 2 (by rfl) ⟨105405, by rfl⟩ : syracuseStep 281081 = 210811) B210811
theorem B2017817 : Blo 183802 2017817 := bstep (se 2 (by rfl) ⟨756681, by rfl⟩ : syracuseStep 2017817 = 1513363) B1513363
theorem B281129 : Blo 183802 281129 := bstep (se 2 (by rfl) ⟨105423, by rfl⟩ : syracuseStep 281129 = 210847) B210847
theorem B641627 : Blo 183802 641627 := bstep (se 1 (by rfl) ⟨481220, by rfl⟩ : syracuseStep 641627 = 962441) B962441
theorem B281323 : Blo 183802 281323 := bstep (se 1 (by rfl) ⟨210992, by rfl⟩ : syracuseStep 281323 = 421985) B421985
theorem B314111 : Blo 183802 314111 := bstep (se 1 (by rfl) ⟨235583, by rfl⟩ : syracuseStep 314111 = 471167) B471167
theorem B1264423 : Blo 183802 1264423 := bstep (se 1 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 1264423 = 1896635) B1896635
theorem B4016951 : Blo 183802 4016951 := bstep (se 1 (by rfl) ⟨3012713, by rfl⟩ : syracuseStep 4016951 = 6025427) B6025427
theorem B281567 : Blo 183802 281567 := bstep (se 1 (by rfl) ⟨211175, by rfl⟩ : syracuseStep 281567 = 422351) B422351
theorem B937169 : Blo 183802 937169 := bstep (se 2 (by rfl) ⟨351438, by rfl⟩ : syracuseStep 937169 = 702877) B702877
theorem B2018533 : Blo 183802 2018533 := bstep (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) B378475
theorem B314779 : Blo 183802 314779 := bstep (se 1 (by rfl) ⟨236084, by rfl⟩ : syracuseStep 314779 = 472169) B472169
theorem B708011 : Blo 183802 708011 := bstep (se 1 (by rfl) ⟨531008, by rfl⟩ : syracuseStep 708011 = 1062017) B1062017
theorem B1068623 : Blo 183802 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B183919 : Blo 183802 183919 := bstep (se 1 (by rfl) ⟨137939, by rfl⟩ : syracuseStep 183919 = 275879) B275879
theorem B478831 : Blo 183802 478831 := bstep (se 1 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 478831 = 718247) B718247
theorem B184039 : Blo 183802 184039 := bstep (se 1 (by rfl) ⟨138029, by rfl⟩ : syracuseStep 184039 = 276059) B276059
theorem B184347 : Blo 183802 184347 := bstep (se 1 (by rfl) ⟨138260, by rfl⟩ : syracuseStep 184347 = 276521) B276521
theorem B184367 : Blo 183802 184367 := bstep (se 1 (by rfl) ⟨138275, by rfl⟩ : syracuseStep 184367 = 276551) B276551
theorem B413927 : Blo 183802 413927 := bstep (se 1 (by rfl) ⟨310445, by rfl⟩ : syracuseStep 413927 = 620891) B620891
theorem B315695 : Blo 183802 315695 := bstep (se 1 (by rfl) ⟨236771, by rfl⟩ : syracuseStep 315695 = 473543) B473543
theorem B184623 : Blo 183802 184623 := bstep (se 1 (by rfl) ⟨138467, by rfl⟩ : syracuseStep 184623 = 276935) B276935
theorem B1888589 : Blo 183802 1888589 := bstep (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) B708221
theorem B414107 : Blo 183802 414107 := bstep (se 1 (by rfl) ⟨310580, by rfl⟩ : syracuseStep 414107 = 621161) B621161
theorem B184767 : Blo 183802 184767 := bstep (se 1 (by rfl) ⟨138575, by rfl⟩ : syracuseStep 184767 = 277151) B277151
theorem B315839 : Blo 183802 315839 := bstep (se 1 (by rfl) ⟨236879, by rfl⟩ : syracuseStep 315839 = 473759) B473759
theorem B184863 : Blo 183802 184863 := bstep (se 1 (by rfl) ⟨138647, by rfl⟩ : syracuseStep 184863 = 277295) B277295
theorem B184943 : Blo 183802 184943 := bstep (se 1 (by rfl) ⟨138707, by rfl⟩ : syracuseStep 184943 = 277415) B277415
theorem B185063 : Blo 183802 185063 := bstep (se 1 (by rfl) ⟨138797, by rfl⟩ : syracuseStep 185063 = 277595) B277595
theorem B938951 : Blo 183802 938951 := bstep (se 1 (by rfl) ⟨704213, by rfl⟩ : syracuseStep 938951 = 1408427) B1408427
theorem B185311 : Blo 183802 185311 := bstep (se 1 (by rfl) ⟨138983, by rfl⟩ : syracuseStep 185311 = 277967) B277967
theorem B316487 : Blo 183802 316487 := bstep (se 1 (by rfl) ⟨237365, by rfl⟩ : syracuseStep 316487 = 474731) B474731
theorem B1135721 : Blo 183802 1135721 := bstep (se 2 (by rfl) ⟨425895, by rfl⟩ : syracuseStep 1135721 = 851791) B851791
theorem B185567 : Blo 183802 185567 := bstep (se 1 (by rfl) ⟨139175, by rfl⟩ : syracuseStep 185567 = 278351) B278351
theorem B185647 : Blo 183802 185647 := bstep (se 1 (by rfl) ⟨139235, by rfl⟩ : syracuseStep 185647 = 278471) B278471
theorem B3233267 : Blo 183802 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B185887 : Blo 183802 185887 := bstep (se 1 (by rfl) ⟨139415, by rfl⟩ : syracuseStep 185887 = 278831) B278831
theorem B186047 : Blo 183802 186047 := bstep (se 1 (by rfl) ⟨139535, by rfl⟩ : syracuseStep 186047 = 279071) B279071
theorem B710441 : Blo 183802 710441 := bstep (se 2 (by rfl) ⟨266415, by rfl⟩ : syracuseStep 710441 = 532831) B532831
theorem B1595213 : Blo 183802 1595213 := bstep (se 3 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 1595213 = 598205) B598205
theorem B186495 : Blo 183802 186495 := bstep (se 1 (by rfl) ⟨139871, by rfl⟩ : syracuseStep 186495 = 279743) B279743
theorem B350399 : Blo 183802 350399 := bstep (se 1 (by rfl) ⟨262799, by rfl⟩ : syracuseStep 350399 = 525599) B525599
theorem B18208961 : Blo 183802 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B940247 : Blo 183802 940247 := bstep (se 1 (by rfl) ⟨705185, by rfl⟩ : syracuseStep 940247 = 1410371) B1410371
theorem B186591 : Blo 183802 186591 := bstep (se 1 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 186591 = 279887) B279887
theorem B186651 : Blo 183802 186651 := bstep (se 1 (by rfl) ⟨139988, by rfl⟩ : syracuseStep 186651 = 279977) B279977
theorem B186751 : Blo 183802 186751 := bstep (se 1 (by rfl) ⟨140063, by rfl⟩ : syracuseStep 186751 = 280127) B280127
theorem B186779 : Blo 183802 186779 := bstep (se 1 (by rfl) ⟨140084, by rfl⟩ : syracuseStep 186779 = 280169) B280169
theorem B187071 : Blo 183802 187071 := bstep (se 1 (by rfl) ⟨140303, by rfl⟩ : syracuseStep 187071 = 280607) B280607
theorem B187199 : Blo 183802 187199 := bstep (se 1 (by rfl) ⟨140399, by rfl⟩ : syracuseStep 187199 = 280799) B280799
theorem B187239 : Blo 183802 187239 := bstep (se 1 (by rfl) ⟨140429, by rfl⟩ : syracuseStep 187239 = 280859) B280859
theorem B416681 : Blo 183802 416681 := bstep (se 2 (by rfl) ⟨156255, by rfl⟩ : syracuseStep 416681 = 312511) B312511
theorem B187455 : Blo 183802 187455 := bstep (se 1 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 187455 = 281183) B281183
theorem B187643 : Blo 183802 187643 := bstep (se 1 (by rfl) ⟨140732, by rfl⟩ : syracuseStep 187643 = 281465) B281465
theorem B351515 : Blo 183802 351515 := bstep (se 1 (by rfl) ⟨263636, by rfl⟩ : syracuseStep 351515 = 527273) B527273
theorem B187675 : Blo 183802 187675 := bstep (se 1 (by rfl) ⟨140756, by rfl⟩ : syracuseStep 187675 = 281513) B281513
theorem B187775 : Blo 183802 187775 := bstep (se 1 (by rfl) ⟨140831, by rfl⟩ : syracuseStep 187775 = 281663) B281663
theorem B2186813 : Blo 183802 2186813 := bstep (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) B820055
theorem B3825443 : Blo 183802 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B1269785 : Blo 183802 1269785 := bstep (se 2 (by rfl) ⟨476169, by rfl⟩ : syracuseStep 1269785 = 952339) B952339
theorem B417833 : Blo 183802 417833 := bstep (se 2 (by rfl) ⟨156687, by rfl⟩ : syracuseStep 417833 = 313375) B313375
theorem B1139321 : Blo 183802 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B352927 : Blo 183802 352927 := bstep (se 1 (by rfl) ⟨264695, by rfl⟩ : syracuseStep 352927 = 529391) B529391
theorem B418463 : Blo 183802 418463 := bstep (se 1 (by rfl) ⟨313847, by rfl⟩ : syracuseStep 418463 = 627695) B627695
theorem B1434307 : Blo 183802 1434307 := bstep (se 1 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 1434307 = 2151461) B2151461
theorem B3171149 : Blo 183802 3171149 := bstep (se 3 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 3171149 = 1189181) B1189181
theorem B943163 : Blo 183802 943163 := bstep (se 1 (by rfl) ⟨707372, by rfl⟩ : syracuseStep 943163 = 1414745) B1414745
theorem B1696987 : Blo 183802 1696987 := bstep (se 1 (by rfl) ⟨1272740, by rfl⟩ : syracuseStep 1696987 = 2545481) B2545481
theorem B17229277 : Blo 183802 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B6744161 : Blo 183802 6744161 := bstep (se 2 (by rfl) ⟨2529060, by rfl⟩ : syracuseStep 6744161 = 5058121) B5058121
theorem B748187 : Blo 183802 748187 := bstep (se 1 (by rfl) ⟨561140, by rfl⟩ : syracuseStep 748187 = 1122281) B1122281
theorem B748379 : Blo 183802 748379 := bstep (se 1 (by rfl) ⟨561284, by rfl⟩ : syracuseStep 748379 = 1122569) B1122569
theorem B945017 : Blo 183802 945017 := bstep (se 2 (by rfl) ⟨354381, by rfl⟩ : syracuseStep 945017 = 708763) B708763
theorem B2485633 : Blo 183802 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B945755 : Blo 183802 945755 := bstep (se 1 (by rfl) ⟨709316, by rfl⟩ : syracuseStep 945755 = 1418633) B1418633
theorem B421595 : Blo 183802 421595 := bstep (se 1 (by rfl) ⟨316196, by rfl⟩ : syracuseStep 421595 = 632393) B632393
theorem B4550417 : Blo 183802 4550417 := bstep (se 2 (by rfl) ⟨1706406, by rfl⟩ : syracuseStep 4550417 = 3412813) B3412813
theorem B421865 : Blo 183802 421865 := bstep (se 2 (by rfl) ⟨158199, by rfl⟩ : syracuseStep 421865 = 316399) B316399
theorem B356329 : Blo 183802 356329 := bstep (se 2 (by rfl) ⟨133623, by rfl⟩ : syracuseStep 356329 = 267247) B267247
theorem B421919 : Blo 183802 421919 := bstep (se 1 (by rfl) ⟨316439, by rfl⟩ : syracuseStep 421919 = 632879) B632879
theorem B2357039 : Blo 183802 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B1702097 : Blo 183802 1702097 := bstep (se 2 (by rfl) ⟨638286, by rfl⟩ : syracuseStep 1702097 = 1276573) B1276573
theorem B48953621 : Blo 183802 48953621 := bstep (se 6 (by rfl) ⟨1147350, by rfl⟩ : syracuseStep 48953621 = 2294701) B2294701
theorem B785953 : Blo 183802 785953 := bstep (se 2 (by rfl) ⟨294732, by rfl⟩ : syracuseStep 785953 = 589465) B589465
theorem B622187 : Blo 183802 622187 := bstep (se 1 (by rfl) ⟨466640, by rfl⟩ : syracuseStep 622187 = 933281) B933281
theorem B523901 : Blo 183802 523901 := bstep (se 3 (by rfl) ⟨98231, by rfl⟩ : syracuseStep 523901 = 196463) B196463
theorem B12156713 : Blo 183802 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B622835 : Blo 183802 622835 := bstep (se 1 (by rfl) ⟨467126, by rfl⟩ : syracuseStep 622835 = 934253) B934253
theorem B1278985 : Blo 183802 1278985 := bstep (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) B959239
theorem B296399 : Blo 183802 296399 := bstep (se 1 (by rfl) ⟨222299, by rfl⟩ : syracuseStep 296399 = 444599) B444599
theorem B2262649 : Blo 183802 2262649 := bstep (se 2 (by rfl) ⟨848493, by rfl⟩ : syracuseStep 2262649 = 1696987) B1696987
theorem B1345211 : Blo 183802 1345211 := bstep (se 1 (by rfl) ⟨1008908, by rfl⟩ : syracuseStep 1345211 = 2017817) B2017817
theorem B427751 : Blo 183802 427751 := bstep (se 1 (by rfl) ⟨320813, by rfl⟩ : syracuseStep 427751 = 641627) B641627
theorem B22972369 : Blo 183802 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B624617 : Blo 183802 624617 := bstep (se 2 (by rfl) ⟨234231, by rfl⟩ : syracuseStep 624617 = 468463) B468463
theorem B624779 : Blo 183802 624779 := bstep (se 1 (by rfl) ⟨468584, by rfl⟩ : syracuseStep 624779 = 937169) B937169
theorem B1510123 : Blo 183802 1510123 := bstep (se 1 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 1510123 = 2265185) B2265185
theorem B625967 : Blo 183802 625967 := bstep (se 1 (by rfl) ⟨469475, by rfl⟩ : syracuseStep 625967 = 938951) B938951
theorem B757147 : Blo 183802 757147 := bstep (se 1 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 757147 = 1135721) B1135721
theorem B233599 : Blo 183802 233599 := bstep (se 1 (by rfl) ⟨175199, by rfl⟩ : syracuseStep 233599 = 350399) B350399
theorem B626831 : Blo 183802 626831 := bstep (se 1 (by rfl) ⟨470123, by rfl⟩ : syracuseStep 626831 = 940247) B940247
theorem B594067 : Blo 183802 594067 := bstep (se 1 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 594067 = 891101) B891101
theorem B2691377 : Blo 183802 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B3314177 : Blo 183802 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B2364011 : Blo 183802 2364011 := bstep (se 1 (by rfl) ⟨1773008, by rfl⟩ : syracuseStep 2364011 = 3546017) B3546017
theorem B791147 : Blo 183802 791147 := bstep (se 1 (by rfl) ⟨593360, by rfl⟩ : syracuseStep 791147 = 1186721) B1186721
theorem B234343 : Blo 183802 234343 := bstep (se 1 (by rfl) ⟨175757, by rfl⟩ : syracuseStep 234343 = 351515) B351515
theorem B529847 : Blo 183802 529847 := bstep (se 1 (by rfl) ⟨397385, by rfl⟩ : syracuseStep 529847 = 794771) B794771
theorem B1185263 : Blo 183802 1185263 := bstep (se 1 (by rfl) ⟨888947, by rfl⟩ : syracuseStep 1185263 = 1777895) B1777895
theorem B759547 : Blo 183802 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B628775 : Blo 183802 628775 := bstep (se 1 (by rfl) ⟨471581, by rfl⟩ : syracuseStep 628775 = 943163) B943163
theorem B596155 : Blo 183802 596155 := bstep (se 1 (by rfl) ⟨447116, by rfl⟩ : syracuseStep 596155 = 894233) B894233
theorem B1415717 : Blo 183802 1415717 := bstep (se 4 (by rfl) ⟨132723, by rfl⟩ : syracuseStep 1415717 = 265447) B265447
theorem B4496107 : Blo 183802 4496107 := bstep (se 1 (by rfl) ⟨3372080, by rfl⟩ : syracuseStep 4496107 = 6744161) B6744161
theorem B629693 : Blo 183802 629693 := bstep (se 3 (by rfl) ⟨118067, by rfl⟩ : syracuseStep 629693 = 236135) B236135
theorem B465983 : Blo 183802 465983 := bstep (se 1 (by rfl) ⟨349487, by rfl⟩ : syracuseStep 465983 = 698975) B698975
theorem B498791 : Blo 183802 498791 := bstep (se 1 (by rfl) ⟨374093, by rfl⟩ : syracuseStep 498791 = 748187) B748187
theorem B498919 : Blo 183802 498919 := bstep (se 1 (by rfl) ⟨374189, by rfl⟩ : syracuseStep 498919 = 748379) B748379
theorem B630011 : Blo 183802 630011 := bstep (se 1 (by rfl) ⟨472508, by rfl⟩ : syracuseStep 630011 = 945017) B945017
theorem B630503 : Blo 183802 630503 := bstep (se 1 (by rfl) ⟨472877, by rfl⟩ : syracuseStep 630503 = 945755) B945755
theorem B4530167 : Blo 183802 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B631529 : Blo 183802 631529 := bstep (se 2 (by rfl) ⟨236823, by rfl⟩ : syracuseStep 631529 = 473647) B473647
theorem B469435 : Blo 183802 469435 := bstep (se 1 (by rfl) ⟨352076, by rfl⟩ : syracuseStep 469435 = 704153) B704153
theorem B8104475 : Blo 183802 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B208039 : Blo 183802 208039 := bstep (se 1 (by rfl) ⟨156029, by rfl⟩ : syracuseStep 208039 = 312059) B312059
theorem B470569 : Blo 183802 470569 := bstep (se 2 (by rfl) ⟨176463, by rfl⟩ : syracuseStep 470569 = 352927) B352927
theorem B1912409 : Blo 183802 1912409 := bstep (se 2 (by rfl) ⟨717153, by rfl⟩ : syracuseStep 1912409 = 1434307) B1434307
theorem B1421063 : Blo 183802 1421063 := bstep (se 1 (by rfl) ⟨1065797, by rfl⟩ : syracuseStep 1421063 = 2131595) B2131595
theorem B601967 : Blo 183802 601967 := bstep (se 1 (by rfl) ⟨451475, by rfl⟩ : syracuseStep 601967 = 902951) B902951
theorem B209407 : Blo 183802 209407 := bstep (se 1 (by rfl) ⟨157055, by rfl⟩ : syracuseStep 209407 = 314111) B314111
theorem B897961 : Blo 183802 897961 := bstep (se 2 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 897961 = 673471) B673471
theorem B472007 : Blo 183802 472007 := bstep (se 1 (by rfl) ⟨354005, by rfl⟩ : syracuseStep 472007 = 708011) B708011
theorem B701891 : Blo 183802 701891 := bstep (se 1 (by rfl) ⟨526418, by rfl⟩ : syracuseStep 701891 = 1052837) B1052837
theorem B1979873 : Blo 183802 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B275951 : Blo 183802 275951 := bstep (se 1 (by rfl) ⟨206963, by rfl⟩ : syracuseStep 275951 = 413927) B413927
theorem B1259059 : Blo 183802 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B276071 : Blo 183802 276071 := bstep (se 1 (by rfl) ⟨207053, by rfl⟩ : syracuseStep 276071 = 414107) B414107
theorem B210559 : Blo 183802 210559 := bstep (se 1 (by rfl) ⟨157919, by rfl⟩ : syracuseStep 210559 = 315839) B315839
theorem B8009441 : Blo 183802 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B10368773 : Blo 183802 10368773 := bstep (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) B1944145
theorem B210991 : Blo 183802 210991 := bstep (se 1 (by rfl) ⟨158243, by rfl⟩ : syracuseStep 210991 = 316487) B316487
theorem B1685897 : Blo 183802 1685897 := bstep (se 2 (by rfl) ⟨632211, by rfl⟩ : syracuseStep 1685897 = 1264423) B1264423
theorem B473627 : Blo 183802 473627 := bstep (se 1 (by rfl) ⟨355220, by rfl⟩ : syracuseStep 473627 = 710441) B710441
theorem B1063475 : Blo 183802 1063475 := bstep (se 1 (by rfl) ⟨797606, by rfl⟩ : syracuseStep 1063475 = 1595213) B1595213
theorem B12139307 : Blo 183802 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B310439 : Blo 183802 310439 := bstep (se 1 (by rfl) ⟨232829, by rfl⟩ : syracuseStep 310439 = 465659) B465659
theorem B277787 : Blo 183802 277787 := bstep (se 1 (by rfl) ⟨208340, by rfl⟩ : syracuseStep 277787 = 416681) B416681
theorem B5356853 : Blo 183802 5356853 := bstep (se 5 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 5356853 = 502205) B502205
theorem B638441 : Blo 183802 638441 := bstep (se 2 (by rfl) ⟨239415, by rfl⟩ : syracuseStep 638441 = 478831) B478831
theorem B1457875 : Blo 183802 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B901037 : Blo 183802 901037 := bstep (se 3 (by rfl) ⟨168944, by rfl⟩ : syracuseStep 901037 = 337889) B337889
theorem B475105 : Blo 183802 475105 := bstep (se 2 (by rfl) ⟨178164, by rfl⟩ : syracuseStep 475105 = 356329) B356329
theorem B278555 : Blo 183802 278555 := bstep (se 1 (by rfl) ⟨208916, by rfl⟩ : syracuseStep 278555 = 417833) B417833
theorem B704609 : Blo 183802 704609 := bstep (se 2 (by rfl) ⟨264228, by rfl⟩ : syracuseStep 704609 = 528457) B528457
theorem B901307 : Blo 183802 901307 := bstep (se 1 (by rfl) ⟨675980, by rfl⟩ : syracuseStep 901307 = 1351961) B1351961
theorem B3162401 : Blo 183802 3162401 := bstep (se 2 (by rfl) ⟨1185900, by rfl⟩ : syracuseStep 3162401 = 2371801) B2371801
theorem B278825 : Blo 183802 278825 := bstep (se 2 (by rfl) ⟨104559, by rfl⟩ : syracuseStep 278825 = 209119) B209119
theorem B278975 : Blo 183802 278975 := bstep (se 1 (by rfl) ⟨209231, by rfl⟩ : syracuseStep 278975 = 418463) B418463
theorem B2114099 : Blo 183802 2114099 := bstep (se 1 (by rfl) ⟨1585574, by rfl⟩ : syracuseStep 2114099 = 3171149) B3171149
theorem B312187 : Blo 183802 312187 := bstep (se 1 (by rfl) ⟨234140, by rfl⟩ : syracuseStep 312187 = 468281) B468281
theorem B279593 : Blo 183802 279593 := bstep (se 2 (by rfl) ⟨104847, by rfl⟩ : syracuseStep 279593 = 209695) B209695
theorem B935225 : Blo 183802 935225 := bstep (se 2 (by rfl) ⟨350709, by rfl⟩ : syracuseStep 935225 = 701419) B701419
theorem B313247 : Blo 183802 313247 := bstep (se 1 (by rfl) ⟨234935, by rfl⟩ : syracuseStep 313247 = 469871) B469871
theorem B281063 : Blo 183802 281063 := bstep (se 1 (by rfl) ⟨210797, by rfl⟩ : syracuseStep 281063 = 421595) B421595
theorem B3033611 : Blo 183802 3033611 := bstep (se 1 (by rfl) ⟨2275208, by rfl⟩ : syracuseStep 3033611 = 4550417) B4550417
theorem B1329817 : Blo 183802 1329817 := bstep (se 2 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 1329817 = 997363) B997363
theorem B281243 : Blo 183802 281243 := bstep (se 1 (by rfl) ⟨210932, by rfl⟩ : syracuseStep 281243 = 421865) B421865
theorem B281279 : Blo 183802 281279 := bstep (se 1 (by rfl) ⟨210959, by rfl⟩ : syracuseStep 281279 = 421919) B421919
theorem B1166663 : Blo 183802 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B183807 : Blo 183802 183807 := bstep (se 1 (by rfl) ⟨137855, by rfl⟩ : syracuseStep 183807 = 275711) B275711
theorem B183835 : Blo 183802 183835 := bstep (se 1 (by rfl) ⟨137876, by rfl⟩ : syracuseStep 183835 = 275753) B275753
theorem B184231 : Blo 183802 184231 := bstep (se 1 (by rfl) ⟨138173, by rfl⟩ : syracuseStep 184231 = 276347) B276347
theorem B184255 : Blo 183802 184255 := bstep (se 1 (by rfl) ⟨138191, by rfl⟩ : syracuseStep 184255 = 276383) B276383
theorem B184391 : Blo 183802 184391 := bstep (se 1 (by rfl) ⟨138293, by rfl⟩ : syracuseStep 184391 = 276587) B276587
theorem B184411 : Blo 183802 184411 := bstep (se 1 (by rfl) ⟨138308, by rfl⟩ : syracuseStep 184411 = 276617) B276617
theorem B1134731 : Blo 183802 1134731 := bstep (se 1 (by rfl) ⟨851048, by rfl⟩ : syracuseStep 1134731 = 1702097) B1702097
theorem B184511 : Blo 183802 184511 := bstep (se 1 (by rfl) ⟨138383, by rfl⟩ : syracuseStep 184511 = 276767) B276767
theorem B184959 : Blo 183802 184959 := bstep (se 1 (by rfl) ⟨138719, by rfl⟩ : syracuseStep 184959 = 277439) B277439
theorem B184991 : Blo 183802 184991 := bstep (se 1 (by rfl) ⟨138743, by rfl⟩ : syracuseStep 184991 = 277487) B277487
theorem B185115 : Blo 183802 185115 := bstep (se 1 (by rfl) ⟨138836, by rfl⟩ : syracuseStep 185115 = 277673) B277673
theorem B185375 : Blo 183802 185375 := bstep (se 1 (by rfl) ⟨139031, by rfl⟩ : syracuseStep 185375 = 278063) B278063
theorem B185391 : Blo 183802 185391 := bstep (se 1 (by rfl) ⟨139043, by rfl⟩ : syracuseStep 185391 = 278087) B278087
theorem B414791 : Blo 183802 414791 := bstep (se 1 (by rfl) ⟨311093, by rfl⟩ : syracuseStep 414791 = 622187) B622187
theorem B349267 : Blo 183802 349267 := bstep (se 1 (by rfl) ⟨261950, by rfl⟩ : syracuseStep 349267 = 523901) B523901
theorem B185447 : Blo 183802 185447 := bstep (se 1 (by rfl) ⟨139085, by rfl⟩ : syracuseStep 185447 = 278171) B278171
theorem B939113 : Blo 183802 939113 := bstep (se 2 (by rfl) ⟨352167, by rfl⟩ : syracuseStep 939113 = 704335) B704335
theorem B185511 : Blo 183802 185511 := bstep (se 1 (by rfl) ⟨139133, by rfl⟩ : syracuseStep 185511 = 278267) B278267
theorem B709955 : Blo 183802 709955 := bstep (se 1 (by rfl) ⟨532466, by rfl⟩ : syracuseStep 709955 = 1064933) B1064933
theorem B185823 : Blo 183802 185823 := bstep (se 1 (by rfl) ⟨139367, by rfl⟩ : syracuseStep 185823 = 278735) B278735
theorem B1890145 : Blo 183802 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B186279 : Blo 183802 186279 := bstep (se 1 (by rfl) ⟨139709, by rfl⟩ : syracuseStep 186279 = 279419) B279419
theorem B186363 : Blo 183802 186363 := bstep (se 1 (by rfl) ⟨139772, by rfl⟩ : syracuseStep 186363 = 279545) B279545
theorem B186399 : Blo 183802 186399 := bstep (se 1 (by rfl) ⟨139799, by rfl⟩ : syracuseStep 186399 = 279599) B279599
theorem B186479 : Blo 183802 186479 := bstep (se 1 (by rfl) ⟨139859, by rfl⟩ : syracuseStep 186479 = 279719) B279719
theorem B841853 : Blo 183802 841853 := bstep (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) B315695
theorem B415871 : Blo 183802 415871 := bstep (se 1 (by rfl) ⟨311903, by rfl⟩ : syracuseStep 415871 = 623807) B623807
theorem B1202303 : Blo 183802 1202303 := bstep (se 1 (by rfl) ⟨901727, by rfl⟩ : syracuseStep 1202303 = 1803455) B1803455
theorem B1497275 : Blo 183802 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B186607 : Blo 183802 186607 := bstep (se 1 (by rfl) ⟨139955, by rfl⟩ : syracuseStep 186607 = 279911) B279911
theorem B187035 : Blo 183802 187035 := bstep (se 1 (by rfl) ⟨140276, by rfl⟩ : syracuseStep 187035 = 280553) B280553
theorem B187131 : Blo 183802 187131 := bstep (se 1 (by rfl) ⟨140348, by rfl⟩ : syracuseStep 187131 = 280697) B280697
theorem B350983 : Blo 183802 350983 := bstep (se 1 (by rfl) ⟨263237, by rfl⟩ : syracuseStep 350983 = 526475) B526475
theorem B187263 : Blo 183802 187263 := bstep (se 1 (by rfl) ⟨140447, by rfl⟩ : syracuseStep 187263 = 280895) B280895
theorem B187359 : Blo 183802 187359 := bstep (se 1 (by rfl) ⟨140519, by rfl⟩ : syracuseStep 187359 = 281039) B281039
theorem B187387 : Blo 183802 187387 := bstep (se 1 (by rfl) ⟨140540, by rfl⟩ : syracuseStep 187387 = 281081) B281081
theorem B187419 : Blo 183802 187419 := bstep (se 1 (by rfl) ⟨140564, by rfl⟩ : syracuseStep 187419 = 281129) B281129
theorem B416879 : Blo 183802 416879 := bstep (se 1 (by rfl) ⟨312659, by rfl⟩ : syracuseStep 416879 = 625319) B625319
theorem B2677967 : Blo 183802 2677967 := bstep (se 1 (by rfl) ⟨2008475, by rfl⟩ : syracuseStep 2677967 = 4016951) B4016951
theorem B187711 : Blo 183802 187711 := bstep (se 1 (by rfl) ⟨140783, by rfl⟩ : syracuseStep 187711 = 281567) B281567
theorem B712415 : Blo 183802 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B417761 : Blo 183802 417761 := bstep (se 2 (by rfl) ⟨156660, by rfl⟩ : syracuseStep 417761 = 313321) B313321
theorem B418067 : Blo 183802 418067 := bstep (se 1 (by rfl) ⟨313550, by rfl⟩ : syracuseStep 418067 = 627101) B627101
theorem B418409 : Blo 183802 418409 := bstep (se 2 (by rfl) ⟨156903, by rfl⟩ : syracuseStep 418409 = 313807) B313807
theorem B2155511 : Blo 183802 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B1500389 : Blo 183802 1500389 := bstep (se 4 (by rfl) ⟨140661, by rfl⟩ : syracuseStep 1500389 = 281323) B281323
theorem B353899 : Blo 183802 353899 := bstep (se 1 (by rfl) ⟨265424, by rfl⟩ : syracuseStep 353899 = 530849) B530849
theorem B353983 : Blo 183802 353983 := bstep (se 1 (by rfl) ⟨265487, by rfl⟩ : syracuseStep 353983 = 530975) B530975
theorem B419705 : Blo 183802 419705 := bstep (se 2 (by rfl) ⟨157389, by rfl⟩ : syracuseStep 419705 = 314779) B314779
theorem B2550295 : Blo 183802 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B846523 : Blo 183802 846523 := bstep (se 1 (by rfl) ⟨634892, by rfl⟩ : syracuseStep 846523 = 1269785) B1269785
theorem B420731 : Blo 183802 420731 := bstep (se 1 (by rfl) ⟨315548, by rfl⟩ : syracuseStep 420731 = 631097) B631097
theorem B420767 : Blo 183802 420767 := bstep (se 1 (by rfl) ⟨315575, by rfl⟩ : syracuseStep 420767 = 631151) B631151
theorem B3894317 : Blo 183802 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B748673 : Blo 183802 748673 := bstep (se 2 (by rfl) ⟨280752, by rfl⟩ : syracuseStep 748673 = 561505) B561505
theorem B945851 : Blo 183802 945851 := bstep (se 1 (by rfl) ⟨709388, by rfl⟩ : syracuseStep 945851 = 1418777) B1418777
theorem B421703 : Blo 183802 421703 := bstep (se 1 (by rfl) ⟨316277, by rfl⟩ : syracuseStep 421703 = 632555) B632555
theorem B422063 : Blo 183802 422063 := bstep (se 1 (by rfl) ⟨316547, by rfl⟩ : syracuseStep 422063 = 633095) B633095
theorem B356665 : Blo 183802 356665 := bstep (se 2 (by rfl) ⟨133749, by rfl⟩ : syracuseStep 356665 = 267499) B267499
theorem B4551389 : Blo 183802 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B3175523 : Blo 183802 3175523 := bstep (se 1 (by rfl) ⟨2381642, by rfl⟩ : syracuseStep 3175523 = 4763285) B4763285
theorem B620459 : Blo 183802 620459 := bstep (se 1 (by rfl) ⟨465344, by rfl⟩ : syracuseStep 620459 = 930689) B930689
theorem B620513 : Blo 183802 620513 := bstep (se 2 (by rfl) ⟨232692, by rfl⟩ : syracuseStep 620513 = 465385) B465385
theorem B1571359 : Blo 183802 1571359 := bstep (se 1 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 1571359 = 2357039) B2357039
theorem B32635747 : Blo 183802 32635747 := bstep (se 1 (by rfl) ⟨24476810, by rfl⟩ : syracuseStep 32635747 = 48953621) B48953621
theorem B1047937 : Blo 183802 1047937 := bstep (se 2 (by rfl) ⟨392976, by rfl⟩ : syracuseStep 1047937 = 785953) B785953
theorem B622457 : Blo 183802 622457 := bstep (se 2 (by rfl) ⟨233421, by rfl⟩ : syracuseStep 622457 = 466843) B466843
theorem B1408913 : Blo 183802 1408913 := bstep (se 2 (by rfl) ⟨528342, by rfl⟩ : syracuseStep 1408913 = 1056685) B1056685
theorem B294887 : Blo 183802 294887 := bstep (se 1 (by rfl) ⟨221165, by rfl⟩ : syracuseStep 294887 = 442331) B442331
theorem B1409399 : Blo 183802 1409399 := bstep (se 1 (by rfl) ⟨1057049, by rfl⟩ : syracuseStep 1409399 = 2114099) B2114099
theorem B623483 : Blo 183802 623483 := bstep (se 1 (by rfl) ⟨467612, by rfl⟩ : syracuseStep 623483 = 935225) B935225
theorem B1705313 : Blo 183802 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B3016865 : Blo 183802 3016865 := bstep (se 2 (by rfl) ⟨1131324, by rfl⟩ : syracuseStep 3016865 = 2262649) B2262649
theorem B756487 : Blo 183802 756487 := bstep (se 1 (by rfl) ⟨567365, by rfl⟩ : syracuseStep 756487 = 1134731) B1134731
theorem B1576007 : Blo 183802 1576007 := bstep (se 1 (by rfl) ⟨1182005, by rfl⟩ : syracuseStep 1576007 = 2364011) B2364011
theorem B625913 : Blo 183802 625913 := bstep (se 2 (by rfl) ⟨234717, by rfl⟩ : syracuseStep 625913 = 469435) B469435
theorem B626075 : Blo 183802 626075 := bstep (se 1 (by rfl) ⟨469556, by rfl⟩ : syracuseStep 626075 = 939113) B939113
theorem B1773089 : Blo 183802 1773089 := bstep (se 2 (by rfl) ⟨664908, by rfl⟩ : syracuseStep 1773089 = 1329817) B1329817
theorem B790175 : Blo 183802 790175 := bstep (se 1 (by rfl) ⟨592631, by rfl⟩ : syracuseStep 790175 = 1185263) B1185263
theorem B790397 : Blo 183802 790397 := bstep (se 3 (by rfl) ⟨148199, by rfl⟩ : syracuseStep 790397 = 296399) B296399
theorem B627425 : Blo 183802 627425 := bstep (se 2 (by rfl) ⟨235284, by rfl⟩ : syracuseStep 627425 = 470569) B470569
theorem B332527 : Blo 183802 332527 := bstep (se 1 (by rfl) ⟨249395, by rfl⟩ : syracuseStep 332527 = 498791) B498791
theorem B3020111 : Blo 183802 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B792089 : Blo 183802 792089 := bstep (se 2 (by rfl) ⟨297033, by rfl⟩ : syracuseStep 792089 = 594067) B594067
theorem B465689 : Blo 183802 465689 := bstep (se 2 (by rfl) ⟨174633, by rfl⟩ : syracuseStep 465689 = 349267) B349267
theorem B2596211 : Blo 183802 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B1678745 : Blo 183802 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B499115 : Blo 183802 499115 := bstep (se 1 (by rfl) ⟨374336, by rfl⟩ : syracuseStep 499115 = 748673) B748673
theorem B401311 : Blo 183802 401311 := bstep (se 1 (by rfl) ⟨300983, by rfl⟩ : syracuseStep 401311 = 601967) B601967
theorem B794873 : Blo 183802 794873 := bstep (se 2 (by rfl) ⟨298077, by rfl⟩ : syracuseStep 794873 = 596155) B596155
theorem B467927 : Blo 183802 467927 := bstep (se 1 (by rfl) ⟨350945, by rfl⟩ : syracuseStep 467927 = 701891) B701891
theorem B1319915 : Blo 183802 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B467977 : Blo 183802 467977 := bstep (se 2 (by rfl) ⟨175491, by rfl⟩ : syracuseStep 467977 = 350983) B350983
theorem B1123931 : Blo 183802 1123931 := bstep (se 1 (by rfl) ⟨842948, by rfl⟩ : syracuseStep 1123931 = 1685897) B1685897
theorem B665225 : Blo 183802 665225 := bstep (se 2 (by rfl) ⟨249459, by rfl⟩ : syracuseStep 665225 = 498919) B498919
theorem B206959 : Blo 183802 206959 := bstep (se 1 (by rfl) ⟨155219, by rfl⟩ : syracuseStep 206959 = 310439) B310439
theorem B1943833 : Blo 183802 1943833 := bstep (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) B1457875
theorem B600691 : Blo 183802 600691 := bstep (se 1 (by rfl) ⟨450518, by rfl⟩ : syracuseStep 600691 = 901037) B901037
theorem B633473 : Blo 183802 633473 := bstep (se 2 (by rfl) ⟨237552, by rfl⟩ : syracuseStep 633473 = 475105) B475105
theorem B469739 : Blo 183802 469739 := bstep (se 1 (by rfl) ⟨352304, by rfl⟩ : syracuseStep 469739 = 704609) B704609
theorem B600871 : Blo 183802 600871 := bstep (se 1 (by rfl) ⟨450653, by rfl⟩ : syracuseStep 600871 = 901307) B901307
theorem B2108267 : Blo 183802 2108267 := bstep (se 1 (by rfl) ⟨1581200, by rfl⟩ : syracuseStep 2108267 = 3162401) B3162401
theorem B896807 : Blo 183802 896807 := bstep (se 1 (by rfl) ⟨672605, by rfl⟩ : syracuseStep 896807 = 1345211) B1345211
theorem B208831 : Blo 183802 208831 := bstep (se 1 (by rfl) ⟨156623, by rfl⟩ : syracuseStep 208831 = 313247) B313247
theorem B2109725 : Blo 183802 2109725 := bstep (se 3 (by rfl) ⟨395573, by rfl⟩ : syracuseStep 2109725 = 791147) B791147
theorem B471865 : Blo 183802 471865 := bstep (se 2 (by rfl) ⟨176949, by rfl⟩ : syracuseStep 471865 = 353899) B353899
theorem B471977 : Blo 183802 471977 := bstep (se 2 (by rfl) ⟨176991, by rfl⟩ : syracuseStep 471977 = 353983) B353983
theorem B5748029 : Blo 183802 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B2209451 : Blo 183802 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B276527 : Blo 183802 276527 := bstep (se 1 (by rfl) ⟨207395, by rfl⟩ : syracuseStep 276527 = 414791) B414791
theorem B473303 : Blo 183802 473303 := bstep (se 1 (by rfl) ⟨354977, by rfl⟩ : syracuseStep 473303 = 709955) B709955
theorem B1128697 : Blo 183802 1128697 := bstep (se 2 (by rfl) ⟨423261, by rfl⟩ : syracuseStep 1128697 = 846523) B846523
theorem B2013497 : Blo 183802 2013497 := bstep (se 2 (by rfl) ⟨755061, by rfl⟩ : syracuseStep 2013497 = 1510123) B1510123
theorem B277247 : Blo 183802 277247 := bstep (se 1 (by rfl) ⟨207935, by rfl⟩ : syracuseStep 277247 = 415871) B415871
theorem B998183 : Blo 183802 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B277385 : Blo 183802 277385 := bstep (se 2 (by rfl) ⟨104019, by rfl⟩ : syracuseStep 277385 = 208039) B208039
theorem B310655 : Blo 183802 310655 := bstep (se 1 (by rfl) ⟨232991, by rfl⟩ : syracuseStep 310655 = 465983) B465983
theorem B277919 : Blo 183802 277919 := bstep (se 1 (by rfl) ⟨208439, by rfl⟩ : syracuseStep 277919 = 416879) B416879
theorem B1785311 : Blo 183802 1785311 := bstep (se 1 (by rfl) ⟨1338983, by rfl⟩ : syracuseStep 1785311 = 2677967) B2677967
theorem B474943 : Blo 183802 474943 := bstep (se 1 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 474943 = 712415) B712415
theorem B278507 : Blo 183802 278507 := bstep (se 1 (by rfl) ⟨208880, by rfl⟩ : syracuseStep 278507 = 417761) B417761
theorem B311465 : Blo 183802 311465 := bstep (se 2 (by rfl) ⟨116799, by rfl⟩ : syracuseStep 311465 = 233599) B233599
theorem B278711 : Blo 183802 278711 := bstep (se 1 (by rfl) ⟨209033, by rfl⟩ : syracuseStep 278711 = 418067) B418067
theorem B2244941 : Blo 183802 2244941 := bstep (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) B841853
theorem B278939 : Blo 183802 278939 := bstep (se 1 (by rfl) ⟨209204, by rfl⟩ : syracuseStep 278939 = 418409) B418409
theorem B475553 : Blo 183802 475553 := bstep (se 2 (by rfl) ⟨178332, by rfl⟩ : syracuseStep 475553 = 356665) B356665
theorem B279209 : Blo 183802 279209 := bstep (se 2 (by rfl) ⟨104703, by rfl⟩ : syracuseStep 279209 = 209407) B209407
theorem B1000259 : Blo 183802 1000259 := bstep (se 1 (by rfl) ⟨750194, by rfl⟩ : syracuseStep 1000259 = 1500389) B1500389
theorem B312457 : Blo 183802 312457 := bstep (se 2 (by rfl) ⟨117171, by rfl⟩ : syracuseStep 312457 = 234343) B234343
theorem B1197281 : Blo 183802 1197281 := bstep (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) B897961
theorem B279803 : Blo 183802 279803 := bstep (se 1 (by rfl) ⟨209852, by rfl⟩ : syracuseStep 279803 = 419705) B419705
theorem B280487 : Blo 183802 280487 := bstep (se 1 (by rfl) ⟨210365, by rfl⟩ : syracuseStep 280487 = 420731) B420731
theorem B280511 : Blo 183802 280511 := bstep (se 1 (by rfl) ⟨210383, by rfl⟩ : syracuseStep 280511 = 420767) B420767
theorem B280745 : Blo 183802 280745 := bstep (se 2 (by rfl) ⟨105279, by rfl⟩ : syracuseStep 280745 = 210559) B210559
theorem B281135 : Blo 183802 281135 := bstep (se 1 (by rfl) ⟨210851, by rfl⟩ : syracuseStep 281135 = 421703) B421703
theorem B281321 : Blo 183802 281321 := bstep (se 2 (by rfl) ⟨105495, by rfl⟩ : syracuseStep 281321 = 210991) B210991
theorem B281375 : Blo 183802 281375 := bstep (se 1 (by rfl) ⟨211031, by rfl⟩ : syracuseStep 281375 = 422063) B422063
theorem B3034259 : Blo 183802 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B314671 : Blo 183802 314671 := bstep (se 1 (by rfl) ⟨236003, by rfl⟩ : syracuseStep 314671 = 472007) B472007
theorem B2117015 : Blo 183802 2117015 := bstep (se 1 (by rfl) ⟨1587761, by rfl⟩ : syracuseStep 2117015 = 3175523) B3175523
theorem B183967 : Blo 183802 183967 := bstep (se 1 (by rfl) ⟨137975, by rfl⟩ : syracuseStep 183967 = 275951) B275951
theorem B184047 : Blo 183802 184047 := bstep (se 1 (by rfl) ⟨138035, by rfl⟩ : syracuseStep 184047 = 276071) B276071
theorem B413639 : Blo 183802 413639 := bstep (se 1 (by rfl) ⟨310229, by rfl⟩ : syracuseStep 413639 = 620459) B620459
theorem B4050917 : Blo 183802 4050917 := bstep (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) B759547
theorem B413675 : Blo 183802 413675 := bstep (se 1 (by rfl) ⟨310256, by rfl⟩ : syracuseStep 413675 = 620513) B620513
theorem B315751 : Blo 183802 315751 := bstep (se 1 (by rfl) ⟨236813, by rfl⟩ : syracuseStep 315751 = 473627) B473627
theorem B708983 : Blo 183802 708983 := bstep (se 1 (by rfl) ⟨531737, by rfl⟩ : syracuseStep 708983 = 1063475) B1063475
theorem B1397249 : Blo 183802 1397249 := bstep (se 2 (by rfl) ⟨523968, by rfl⟩ : syracuseStep 1397249 = 1047937) B1047937
theorem B10080773 : Blo 183802 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B185191 : Blo 183802 185191 := bstep (se 1 (by rfl) ⟨138893, by rfl⟩ : syracuseStep 185191 = 277787) B277787
theorem B414971 : Blo 183802 414971 := bstep (se 1 (by rfl) ⟨311228, by rfl⟩ : syracuseStep 414971 = 622457) B622457
theorem B939275 : Blo 183802 939275 := bstep (se 1 (by rfl) ⟨704456, by rfl⟩ : syracuseStep 939275 = 1408913) B1408913
theorem B185703 : Blo 183802 185703 := bstep (se 1 (by rfl) ⟨139277, by rfl⟩ : syracuseStep 185703 = 278555) B278555
theorem B415223 : Blo 183802 415223 := bstep (se 1 (by rfl) ⟨311417, by rfl⟩ : syracuseStep 415223 = 622835) B622835
theorem B185883 : Blo 183802 185883 := bstep (se 1 (by rfl) ⟨139412, by rfl⟩ : syracuseStep 185883 = 278825) B278825
theorem B185983 : Blo 183802 185983 := bstep (se 1 (by rfl) ⟨139487, by rfl⟩ : syracuseStep 185983 = 278975) B278975
theorem B186395 : Blo 183802 186395 := bstep (se 1 (by rfl) ⟨139796, by rfl⟩ : syracuseStep 186395 = 279593) B279593
theorem B285167 : Blo 183802 285167 := bstep (se 1 (by rfl) ⟨213875, by rfl⟩ : syracuseStep 285167 = 427751) B427751
theorem B416249 : Blo 183802 416249 := bstep (se 2 (by rfl) ⟨156093, by rfl⟩ : syracuseStep 416249 = 312187) B312187
theorem B416411 : Blo 183802 416411 := bstep (se 1 (by rfl) ⟨312308, by rfl⟩ : syracuseStep 416411 = 624617) B624617
theorem B416519 : Blo 183802 416519 := bstep (se 1 (by rfl) ⟨312389, by rfl⟩ : syracuseStep 416519 = 624779) B624779
theorem B187375 : Blo 183802 187375 := bstep (se 1 (by rfl) ⟨140531, by rfl⟩ : syracuseStep 187375 = 281063) B281063
theorem B2022407 : Blo 183802 2022407 := bstep (se 1 (by rfl) ⟨1516805, by rfl⟩ : syracuseStep 2022407 = 3033611) B3033611
theorem B187495 : Blo 183802 187495 := bstep (se 1 (by rfl) ⟨140621, by rfl⟩ : syracuseStep 187495 = 281243) B281243
theorem B187519 : Blo 183802 187519 := bstep (se 1 (by rfl) ⟨140639, by rfl⟩ : syracuseStep 187519 = 281279) B281279
theorem B417311 : Blo 183802 417311 := bstep (se 1 (by rfl) ⟨312983, by rfl⟩ : syracuseStep 417311 = 625967) B625967
theorem B777775 : Blo 183802 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B30629825 : Blo 183802 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B417887 : Blo 183802 417887 := bstep (se 1 (by rfl) ⟨313415, by rfl⟩ : syracuseStep 417887 = 626831) B626831
theorem B1794251 : Blo 183802 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B3400393 : Blo 183802 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B353231 : Blo 183802 353231 := bstep (se 1 (by rfl) ⟨264923, by rfl⟩ : syracuseStep 353231 = 529847) B529847
theorem B419183 : Blo 183802 419183 := bstep (se 1 (by rfl) ⟨314387, by rfl⟩ : syracuseStep 419183 = 628775) B628775
theorem B943811 : Blo 183802 943811 := bstep (se 1 (by rfl) ⟨707858, by rfl⟩ : syracuseStep 943811 = 1415717) B1415717
theorem B1009529 : Blo 183802 1009529 := bstep (se 2 (by rfl) ⟨378573, by rfl⟩ : syracuseStep 1009529 = 757147) B757147
theorem B419795 : Blo 183802 419795 := bstep (se 1 (by rfl) ⟨314846, by rfl⟩ : syracuseStep 419795 = 629693) B629693
theorem B420007 : Blo 183802 420007 := bstep (se 1 (by rfl) ⟨315005, by rfl⟩ : syracuseStep 420007 = 630011) B630011
theorem B420335 : Blo 183802 420335 := bstep (se 1 (by rfl) ⟨315251, by rfl⟩ : syracuseStep 420335 = 630503) B630503
theorem B3206141 : Blo 183802 3206141 := bstep (se 3 (by rfl) ⟨601151, by rfl⟩ : syracuseStep 3206141 = 1202303) B1202303
theorem B421019 : Blo 183802 421019 := bstep (se 1 (by rfl) ⟨315764, by rfl⟩ : syracuseStep 421019 = 631529) B631529
theorem B5402983 : Blo 183802 5402983 := bstep (se 1 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 5402983 = 8104475) B8104475
theorem B1274939 : Blo 183802 1274939 := bstep (se 1 (by rfl) ⟨956204, by rfl⟩ : syracuseStep 1274939 = 1912409) B1912409
theorem B947375 : Blo 183802 947375 := bstep (se 1 (by rfl) ⟨710531, by rfl⟩ : syracuseStep 947375 = 1421063) B1421063
theorem B2095145 : Blo 183802 2095145 := bstep (se 2 (by rfl) ⟨785679, by rfl⟩ : syracuseStep 2095145 = 1571359) B1571359
theorem B5994809 : Blo 183802 5994809 := bstep (se 2 (by rfl) ⟨2248053, by rfl⟩ : syracuseStep 5994809 = 4496107) B4496107
theorem B43514329 : Blo 183802 43514329 := bstep (se 2 (by rfl) ⟨16317873, by rfl⟩ : syracuseStep 43514329 = 32635747) B32635747
theorem B5339627 : Blo 183802 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B6912515 : Blo 183802 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B2522269 : Blo 183802 2522269 := bstep (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) B945851
theorem B8092871 : Blo 183802 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B3571235 : Blo 183802 3571235 := bstep (se 1 (by rfl) ⟨2678426, by rfl⟩ : syracuseStep 3571235 = 5356853) B5356853
theorem B425627 : Blo 183802 425627 := bstep (se 1 (by rfl) ⟨319220, by rfl⟩ : syracuseStep 425627 = 638441) B638441
theorem B196591 : Blo 183802 196591 := bstep (se 1 (by rfl) ⟨147443, by rfl⟩ : syracuseStep 196591 = 294887) B294887
theorem B623969 : Blo 183802 623969 := bstep (se 2 (by rfl) ⟨233988, by rfl⟩ : syracuseStep 623969 = 467977) B467977
theorem B1050671 : Blo 183802 1050671 := bstep (se 1 (by rfl) ⟨788003, by rfl⟩ : syracuseStep 1050671 = 1576007) B1576007
theorem B1411343 : Blo 183802 1411343 := bstep (se 1 (by rfl) ⟨1058507, by rfl⟩ : syracuseStep 1411343 = 2117015) B2117015
theorem B1182059 : Blo 183802 1182059 := bstep (se 1 (by rfl) ⟨886544, by rfl⟩ : syracuseStep 1182059 = 1773089) B1773089
theorem B526783 : Blo 183802 526783 := bstep (se 1 (by rfl) ⟨395087, by rfl⟩ : syracuseStep 526783 = 790175) B790175
theorem B526931 : Blo 183802 526931 := bstep (se 1 (by rfl) ⟨395198, by rfl⟩ : syracuseStep 526931 = 790397) B790397
theorem B560009 : Blo 183802 560009 := bstep (se 2 (by rfl) ⟨210003, by rfl⟩ : syracuseStep 560009 = 420007) B420007
theorem B6720515 : Blo 183802 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B2591777 : Blo 183802 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B626183 : Blo 183802 626183 := bstep (se 1 (by rfl) ⟨469637, by rfl⟩ : syracuseStep 626183 = 939275) B939275
theorem B528059 : Blo 183802 528059 := bstep (se 1 (by rfl) ⟨396044, by rfl⟩ : syracuseStep 528059 = 792089) B792089
theorem B1348271 : Blo 183802 1348271 := bstep (se 1 (by rfl) ⟨1011203, by rfl⟩ : syracuseStep 1348271 = 2022407) B2022407
theorem B332743 : Blo 183802 332743 := bstep (se 1 (by rfl) ⟨249557, by rfl⟩ : syracuseStep 332743 = 499115) B499115
theorem B20419883 : Blo 183802 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B529915 : Blo 183802 529915 := bstep (se 1 (by rfl) ⟨397436, by rfl⟩ : syracuseStep 529915 = 794873) B794873
theorem B235487 : Blo 183802 235487 := bstep (se 1 (by rfl) ⟨176615, by rfl⟩ : syracuseStep 235487 = 353231) B353231
theorem B629153 : Blo 183802 629153 := bstep (se 2 (by rfl) ⟨235932, by rfl⟩ : syracuseStep 629153 = 471865) B471865
theorem B629207 : Blo 183802 629207 := bstep (se 1 (by rfl) ⟨471905, by rfl⟩ : syracuseStep 629207 = 943811) B943811
theorem B760445 : Blo 183802 760445 := bstep (se 3 (by rfl) ⟨142583, by rfl⟩ : syracuseStep 760445 = 285167) B285167
theorem B2137427 : Blo 183802 2137427 := bstep (se 1 (by rfl) ⟨1603070, by rfl⟩ : syracuseStep 2137427 = 3206141) B3206141
theorem B2661821 : Blo 183802 2661821 := bstep (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) B998183
theorem B597871 : Blo 183802 597871 := bstep (se 1 (by rfl) ⟨448403, by rfl⟩ : syracuseStep 597871 = 896807) B896807
theorem B631583 : Blo 183802 631583 := bstep (se 1 (by rfl) ⟨473687, by rfl⟩ : syracuseStep 631583 = 947375) B947375
theorem B207103 : Blo 183802 207103 := bstep (se 1 (by rfl) ⟨155327, by rfl⟩ : syracuseStep 207103 = 310655) B310655
theorem B1190207 : Blo 183802 1190207 := bstep (se 1 (by rfl) ⟨892655, by rfl⟩ : syracuseStep 1190207 = 1785311) B1785311
theorem B633257 : Blo 183802 633257 := bstep (se 2 (by rfl) ⟨237471, by rfl⟩ : syracuseStep 633257 = 474943) B474943
theorem B535081 : Blo 183802 535081 := bstep (se 2 (by rfl) ⟨200655, by rfl⟩ : syracuseStep 535081 = 401311) B401311
theorem B207643 : Blo 183802 207643 := bstep (se 1 (by rfl) ⟨155732, by rfl⟩ : syracuseStep 207643 = 311465) B311465
theorem B666839 : Blo 183802 666839 := bstep (se 1 (by rfl) ⟨500129, by rfl⟩ : syracuseStep 666839 = 1000259) B1000259
theorem B798187 : Blo 183802 798187 := bstep (se 1 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 798187 = 1197281) B1197281
theorem B4533857 : Blo 183802 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B2011243 : Blo 183802 2011243 := bstep (se 1 (by rfl) ⟨1508432, by rfl⟩ : syracuseStep 2011243 = 3016865) B3016865
theorem B3519773 : Blo 183802 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B275759 : Blo 183802 275759 := bstep (se 1 (by rfl) ⟨206819, by rfl⟩ : syracuseStep 275759 = 413639) B413639
theorem B2700611 : Blo 183802 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B275783 : Blo 183802 275783 := bstep (se 1 (by rfl) ⟨206837, by rfl⟩ : syracuseStep 275783 = 413675) B413675
theorem B275945 : Blo 183802 275945 := bstep (se 2 (by rfl) ⟨103479, by rfl⟩ : syracuseStep 275945 = 206959) B206959
theorem B472655 : Blo 183802 472655 := bstep (se 1 (by rfl) ⟨354491, by rfl⟩ : syracuseStep 472655 = 708983) B708983
theorem B931499 : Blo 183802 931499 := bstep (se 1 (by rfl) ⟨698624, by rfl⟩ : syracuseStep 931499 = 1397249) B1397249
theorem B800921 : Blo 183802 800921 := bstep (se 2 (by rfl) ⟨300345, by rfl⟩ : syracuseStep 800921 = 600691) B600691
theorem B276647 : Blo 183802 276647 := bstep (se 1 (by rfl) ⟨207485, by rfl⟩ : syracuseStep 276647 = 414971) B414971
theorem B2013407 : Blo 183802 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B276815 : Blo 183802 276815 := bstep (se 1 (by rfl) ⟨207611, by rfl⟩ : syracuseStep 276815 = 415223) B415223
theorem B801161 : Blo 183802 801161 := bstep (se 2 (by rfl) ⟨300435, by rfl⟩ : syracuseStep 801161 = 600871) B600871
theorem B277499 : Blo 183802 277499 := bstep (se 1 (by rfl) ⟨208124, by rfl⟩ : syracuseStep 277499 = 416249) B416249
theorem B277607 : Blo 183802 277607 := bstep (se 1 (by rfl) ⟨208205, by rfl⟩ : syracuseStep 277607 = 416411) B416411
theorem B277679 : Blo 183802 277679 := bstep (se 1 (by rfl) ⟨208259, by rfl⟩ : syracuseStep 277679 = 416519) B416519
theorem B310459 : Blo 183802 310459 := bstep (se 1 (by rfl) ⟨232844, by rfl⟩ : syracuseStep 310459 = 465689) B465689
theorem B278207 : Blo 183802 278207 := bstep (se 1 (by rfl) ⟨208655, by rfl⟩ : syracuseStep 278207 = 417311) B417311
theorem B278441 : Blo 183802 278441 := bstep (se 2 (by rfl) ⟨104415, by rfl⟩ : syracuseStep 278441 = 208831) B208831
theorem B278591 : Blo 183802 278591 := bstep (se 1 (by rfl) ⟨208943, by rfl⟩ : syracuseStep 278591 = 417887) B417887
theorem B1196167 : Blo 183802 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B311951 : Blo 183802 311951 := bstep (se 1 (by rfl) ⟨233963, by rfl⟩ : syracuseStep 311951 = 467927) B467927
theorem B13452101 : Blo 183802 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B279455 : Blo 183802 279455 := bstep (se 1 (by rfl) ⟨209591, by rfl⟩ : syracuseStep 279455 = 419183) B419183
theorem B443369 : Blo 183802 443369 := bstep (se 2 (by rfl) ⟨166263, by rfl⟩ : syracuseStep 443369 = 332527) B332527
theorem B443483 : Blo 183802 443483 := bstep (se 1 (by rfl) ⟨332612, by rfl⟩ : syracuseStep 443483 = 665225) B665225
theorem B673019 : Blo 183802 673019 := bstep (se 1 (by rfl) ⟨504764, by rfl⟩ : syracuseStep 673019 = 1009529) B1009529
theorem B279863 : Blo 183802 279863 := bstep (se 1 (by rfl) ⟨209897, by rfl⟩ : syracuseStep 279863 = 419795) B419795
theorem B280223 : Blo 183802 280223 := bstep (se 1 (by rfl) ⟨210167, by rfl⟩ : syracuseStep 280223 = 420335) B420335
theorem B313159 : Blo 183802 313159 := bstep (se 1 (by rfl) ⟨234869, by rfl⟩ : syracuseStep 313159 = 469739) B469739
theorem B280679 : Blo 183802 280679 := bstep (se 1 (by rfl) ⟨210509, by rfl⟩ : syracuseStep 280679 = 421019) B421019
theorem B314651 : Blo 183802 314651 := bstep (se 1 (by rfl) ⟨235988, by rfl⟩ : syracuseStep 314651 = 471977) B471977
theorem B58019105 : Blo 183802 58019105 := bstep (se 2 (by rfl) ⟨21757164, by rfl⟩ : syracuseStep 58019105 = 43514329) B43514329
theorem B4476653 : Blo 183802 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B1396763 : Blo 183802 1396763 := bstep (se 1 (by rfl) ⟨1047572, by rfl⟩ : syracuseStep 1396763 = 2095145) B2095145
theorem B184351 : Blo 183802 184351 := bstep (se 1 (by rfl) ⟨138263, by rfl⟩ : syracuseStep 184351 = 276527) B276527
theorem B315535 : Blo 183802 315535 := bstep (se 1 (by rfl) ⟨236651, by rfl⟩ : syracuseStep 315535 = 473303) B473303
theorem B3559751 : Blo 183802 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B4608343 : Blo 183802 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B184831 : Blo 183802 184831 := bstep (se 1 (by rfl) ⟨138623, by rfl⟩ : syracuseStep 184831 = 277247) B277247
theorem B184923 : Blo 183802 184923 := bstep (se 1 (by rfl) ⟨138692, by rfl⟩ : syracuseStep 184923 = 277385) B277385
theorem B1037033 : Blo 183802 1037033 := bstep (se 2 (by rfl) ⟨388887, by rfl⟩ : syracuseStep 1037033 = 777775) B777775
theorem B5395247 : Blo 183802 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B185279 : Blo 183802 185279 := bstep (se 1 (by rfl) ⟨138959, by rfl⟩ : syracuseStep 185279 = 277919) B277919
theorem B2380823 : Blo 183802 2380823 := bstep (se 1 (by rfl) ⟨1785617, by rfl⟩ : syracuseStep 2380823 = 3571235) B3571235
theorem B283751 : Blo 183802 283751 := bstep (se 1 (by rfl) ⟨212813, by rfl⟩ : syracuseStep 283751 = 425627) B425627
theorem B185671 : Blo 183802 185671 := bstep (se 1 (by rfl) ⟨139253, by rfl⟩ : syracuseStep 185671 = 278507) B278507
theorem B185807 : Blo 183802 185807 := bstep (se 1 (by rfl) ⟨139355, by rfl⟩ : syracuseStep 185807 = 278711) B278711
theorem B1496627 : Blo 183802 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B939599 : Blo 183802 939599 := bstep (se 1 (by rfl) ⟨704699, by rfl⟩ : syracuseStep 939599 = 1409399) B1409399
theorem B185959 : Blo 183802 185959 := bstep (se 1 (by rfl) ⟨139469, by rfl⟩ : syracuseStep 185959 = 278939) B278939
theorem B186139 : Blo 183802 186139 := bstep (se 1 (by rfl) ⟨139604, by rfl⟩ : syracuseStep 186139 = 279209) B279209
theorem B415655 : Blo 183802 415655 := bstep (se 1 (by rfl) ⟨311741, by rfl⟩ : syracuseStep 415655 = 623483) B623483
theorem B186535 : Blo 183802 186535 := bstep (se 1 (by rfl) ⟨139901, by rfl⟩ : syracuseStep 186535 = 279803) B279803
theorem B1136875 : Blo 183802 1136875 := bstep (se 1 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 1136875 = 1705313) B1705313
theorem B1268141 : Blo 183802 1268141 := bstep (se 3 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 1268141 = 475553) B475553
theorem B186991 : Blo 183802 186991 := bstep (se 1 (by rfl) ⟨140243, by rfl⟩ : syracuseStep 186991 = 280487) B280487
theorem B187007 : Blo 183802 187007 := bstep (se 1 (by rfl) ⟨140255, by rfl⟩ : syracuseStep 187007 = 280511) B280511
theorem B6019717 : Blo 183802 6019717 := bstep (se 4 (by rfl) ⟨564348, by rfl⟩ : syracuseStep 6019717 = 1128697) B1128697
theorem B187163 : Blo 183802 187163 := bstep (se 1 (by rfl) ⟨140372, by rfl⟩ : syracuseStep 187163 = 280745) B280745
theorem B416609 : Blo 183802 416609 := bstep (se 2 (by rfl) ⟨156228, by rfl⟩ : syracuseStep 416609 = 312457) B312457
theorem B187423 : Blo 183802 187423 := bstep (se 1 (by rfl) ⟨140567, by rfl⟩ : syracuseStep 187423 = 281135) B281135
theorem B187547 : Blo 183802 187547 := bstep (se 1 (by rfl) ⟨140660, by rfl⟩ : syracuseStep 187547 = 281321) B281321
theorem B187583 : Blo 183802 187583 := bstep (se 1 (by rfl) ⟨140687, by rfl⟩ : syracuseStep 187583 = 281375) B281375
theorem B2022839 : Blo 183802 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B417275 : Blo 183802 417275 := bstep (se 1 (by rfl) ⟨312956, by rfl⟩ : syracuseStep 417275 = 625913) B625913
theorem B417383 : Blo 183802 417383 := bstep (se 1 (by rfl) ⟨313037, by rfl⟩ : syracuseStep 417383 = 626075) B626075
theorem B418283 : Blo 183802 418283 := bstep (se 1 (by rfl) ⟨313712, by rfl⟩ : syracuseStep 418283 = 627425) B627425
theorem B1008649 : Blo 183802 1008649 := bstep (se 2 (by rfl) ⟨378243, by rfl⟩ : syracuseStep 1008649 = 756487) B756487
theorem B419561 : Blo 183802 419561 := bstep (se 2 (by rfl) ⟨157335, by rfl⟩ : syracuseStep 419561 = 314671) B314671
theorem B5891869 : Blo 183802 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B1730807 : Blo 183802 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B421001 : Blo 183802 421001 := bstep (se 2 (by rfl) ⟨157875, by rfl⟩ : syracuseStep 421001 = 315751) B315751
theorem B7203977 : Blo 183802 7203977 := bstep (se 2 (by rfl) ⟨2701491, by rfl⟩ : syracuseStep 7203977 = 5402983) B5402983
theorem B749287 : Blo 183802 749287 := bstep (se 1 (by rfl) ⟨561965, by rfl⟩ : syracuseStep 749287 = 1123931) B1123931
theorem B422315 : Blo 183802 422315 := bstep (se 1 (by rfl) ⟨316736, by rfl⟩ : syracuseStep 422315 = 633473) B633473
theorem B1405511 : Blo 183802 1405511 := bstep (se 1 (by rfl) ⟨1054133, by rfl⟩ : syracuseStep 1405511 = 2108267) B2108267
theorem B1406483 : Blo 183802 1406483 := bstep (se 1 (by rfl) ⟨1054862, by rfl⟩ : syracuseStep 1406483 = 2109725) B2109725
theorem B849959 : Blo 183802 849959 := bstep (se 1 (by rfl) ⟨637469, by rfl⟩ : syracuseStep 849959 = 1274939) B1274939
theorem B3832019 : Blo 183802 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B3996539 : Blo 183802 3996539 := bstep (se 1 (by rfl) ⟨2997404, by rfl⟩ : syracuseStep 3996539 = 5994809) B5994809
theorem B1342331 : Blo 183802 1342331 := bstep (se 1 (by rfl) ⟨1006748, by rfl⟩ : syracuseStep 1342331 = 2013497) B2013497
theorem B262121 : Blo 183802 262121 := bstep (se 2 (by rfl) ⟨98295, by rfl⟩ : syracuseStep 262121 = 196591) B196591
theorem B295579 : Blo 183802 295579 := bstep (se 1 (by rfl) ⟨221684, by rfl⟩ : syracuseStep 295579 = 443369) B443369
theorem B295655 : Blo 183802 295655 := bstep (se 1 (by rfl) ⟨221741, by rfl⟩ : syracuseStep 295655 = 443483) B443483
theorem B1344865 : Blo 183802 1344865 := bstep (se 2 (by rfl) ⟨504324, by rfl⟩ : syracuseStep 1344865 = 1008649) B1008649
theorem B788039 : Blo 183802 788039 := bstep (se 1 (by rfl) ⟨591029, by rfl⟩ : syracuseStep 788039 = 1182059) B1182059
theorem B2984435 : Blo 183802 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B691355 : Blo 183802 691355 := bstep (se 1 (by rfl) ⟨518516, by rfl⟩ : syracuseStep 691355 = 1037033) B1037033
theorem B626399 : Blo 183802 626399 := bstep (se 1 (by rfl) ⟨469799, by rfl⟩ : syracuseStep 626399 = 939599) B939599
theorem B1348559 : Blo 183802 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B1774547 : Blo 183802 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B627965 : Blo 183802 627965 := bstep (se 3 (by rfl) ⟨117743, by rfl⟩ : syracuseStep 627965 = 235487) B235487
theorem B1153871 : Blo 183802 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B793471 : Blo 183802 793471 := bstep (se 1 (by rfl) ⟨595103, by rfl⟩ : syracuseStep 793471 = 1190207) B1190207
theorem B3022571 : Blo 183802 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B1515833 : Blo 183802 1515833 := bstep (se 2 (by rfl) ⟨568437, by rfl⟩ : syracuseStep 1515833 = 1136875) B1136875
theorem B1778237 : Blo 183802 1778237 := bstep (se 3 (by rfl) ⟨333419, by rfl⟩ : syracuseStep 1778237 = 666839) B666839
theorem B566639 : Blo 183802 566639 := bstep (se 1 (by rfl) ⟨424979, by rfl⟩ : syracuseStep 566639 = 849959) B849959
theorem B533947 : Blo 183802 533947 := bstep (se 1 (by rfl) ⟨400460, by rfl⟩ : syracuseStep 533947 = 800921) B800921
theorem B534107 : Blo 183802 534107 := bstep (se 1 (by rfl) ⟨400580, by rfl⟩ : syracuseStep 534107 = 801161) B801161
theorem B3188645 : Blo 183802 3188645 := bstep (se 4 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 3188645 = 597871) B597871
theorem B2664359 : Blo 183802 2664359 := bstep (se 1 (by rfl) ⟨1998269, by rfl⟩ : syracuseStep 2664359 = 3996539) B3996539
theorem B894887 : Blo 183802 894887 := bstep (se 1 (by rfl) ⟨671165, by rfl⟩ : syracuseStep 894887 = 1342331) B1342331
theorem B698989 : Blo 183802 698989 := bstep (se 3 (by rfl) ⟨131060, by rfl⟩ : syracuseStep 698989 = 262121) B262121
theorem B207967 : Blo 183802 207967 := bstep (se 1 (by rfl) ⟨155975, by rfl⟩ : syracuseStep 207967 = 311951) B311951
theorem B700447 : Blo 183802 700447 := bstep (se 1 (by rfl) ⟨525335, by rfl⟩ : syracuseStep 700447 = 1050671) B1050671
theorem B373339 : Blo 183802 373339 := bstep (se 1 (by rfl) ⟨280004, by rfl⟩ : syracuseStep 373339 = 560009) B560009
theorem B209767 : Blo 183802 209767 := bstep (se 1 (by rfl) ⟨157325, by rfl⟩ : syracuseStep 209767 = 314651) B314651
theorem B38679403 : Blo 183802 38679403 := bstep (se 1 (by rfl) ⟨29009552, by rfl⟩ : syracuseStep 38679403 = 58019105) B58019105
theorem B931175 : Blo 183802 931175 := bstep (se 1 (by rfl) ⟨698381, by rfl⟩ : syracuseStep 931175 = 1396763) B1396763
theorem B2373167 : Blo 183802 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B276137 : Blo 183802 276137 := bstep (se 2 (by rfl) ⟨103551, by rfl⟩ : syracuseStep 276137 = 207103) B207103
theorem B898847 : Blo 183802 898847 := bstep (se 1 (by rfl) ⟨674135, by rfl⟩ : syracuseStep 898847 = 1348271) B1348271
theorem B702377 : Blo 183802 702377 := bstep (se 2 (by rfl) ⟨263391, by rfl⟩ : syracuseStep 702377 = 526783) B526783
theorem B1587215 : Blo 183802 1587215 := bstep (se 1 (by rfl) ⟨1190411, by rfl⟩ : syracuseStep 1587215 = 2380823) B2380823
theorem B13613255 : Blo 183802 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B997751 : Blo 183802 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B276857 : Blo 183802 276857 := bstep (se 2 (by rfl) ⟨103821, by rfl⟩ : syracuseStep 276857 = 207643) B207643
theorem B277103 : Blo 183802 277103 := bstep (se 1 (by rfl) ⟨207827, by rfl⟩ : syracuseStep 277103 = 415655) B415655
theorem B506963 : Blo 183802 506963 := bstep (se 1 (by rfl) ⟨380222, by rfl⟩ : syracuseStep 506963 = 760445) B760445
theorem B277739 : Blo 183802 277739 := bstep (se 1 (by rfl) ⟨208304, by rfl⟩ : syracuseStep 277739 = 416609) B416609
theorem B1064249 : Blo 183802 1064249 := bstep (se 2 (by rfl) ⟨399093, by rfl⟩ : syracuseStep 1064249 = 798187) B798187
theorem B1424951 : Blo 183802 1424951 := bstep (se 1 (by rfl) ⟨1068713, by rfl⟩ : syracuseStep 1424951 = 2137427) B2137427
theorem B999049 : Blo 183802 999049 := bstep (se 2 (by rfl) ⟨374643, by rfl⟩ : syracuseStep 999049 = 749287) B749287
theorem B278183 : Blo 183802 278183 := bstep (se 1 (by rfl) ⟨208637, by rfl⟩ : syracuseStep 278183 = 417275) B417275
theorem B278255 : Blo 183802 278255 := bstep (se 1 (by rfl) ⟨208691, by rfl⟩ : syracuseStep 278255 = 417383) B417383
theorem B278855 : Blo 183802 278855 := bstep (se 1 (by rfl) ⟨209141, by rfl⟩ : syracuseStep 278855 = 418283) B418283
theorem B6144457 : Blo 183802 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B279707 : Blo 183802 279707 := bstep (se 1 (by rfl) ⟨209780, by rfl⟩ : syracuseStep 279707 = 419561) B419561
theorem B443657 : Blo 183802 443657 := bstep (se 2 (by rfl) ⟨166371, by rfl⟩ : syracuseStep 443657 = 332743) B332743
theorem B706553 : Blo 183802 706553 := bstep (se 2 (by rfl) ⟨264957, by rfl⟩ : syracuseStep 706553 = 529915) B529915
theorem B280667 : Blo 183802 280667 := bstep (se 1 (by rfl) ⟨210500, by rfl⟩ : syracuseStep 280667 = 421001) B421001
theorem B4802651 : Blo 183802 4802651 := bstep (se 1 (by rfl) ⟨3601988, by rfl⟩ : syracuseStep 4802651 = 7203977) B7203977
theorem B281543 : Blo 183802 281543 := bstep (se 1 (by rfl) ⟨211157, by rfl⟩ : syracuseStep 281543 = 422315) B422315
theorem B937007 : Blo 183802 937007 := bstep (se 1 (by rfl) ⟨702755, by rfl⟩ : syracuseStep 937007 = 1405511) B1405511
theorem B2346515 : Blo 183802 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B183839 : Blo 183802 183839 := bstep (se 1 (by rfl) ⟨137879, by rfl⟩ : syracuseStep 183839 = 275759) B275759
theorem B183855 : Blo 183802 183855 := bstep (se 1 (by rfl) ⟨137891, by rfl⟩ : syracuseStep 183855 = 275783) B275783
theorem B183963 : Blo 183802 183963 := bstep (se 1 (by rfl) ⟨137972, by rfl⟩ : syracuseStep 183963 = 275945) B275945
theorem B937655 : Blo 183802 937655 := bstep (se 1 (by rfl) ⟨703241, by rfl⟩ : syracuseStep 937655 = 1406483) B1406483
theorem B315103 : Blo 183802 315103 := bstep (se 1 (by rfl) ⟨236327, by rfl⟩ : syracuseStep 315103 = 472655) B472655
theorem B184431 : Blo 183802 184431 := bstep (se 1 (by rfl) ⟨138323, by rfl⟩ : syracuseStep 184431 = 276647) B276647
theorem B184543 : Blo 183802 184543 := bstep (se 1 (by rfl) ⟨138407, by rfl⟩ : syracuseStep 184543 = 276815) B276815
theorem B413945 : Blo 183802 413945 := bstep (se 2 (by rfl) ⟨155229, by rfl⟩ : syracuseStep 413945 = 310459) B310459
theorem B184999 : Blo 183802 184999 := bstep (se 1 (by rfl) ⟨138749, by rfl⟩ : syracuseStep 184999 = 277499) B277499
theorem B185071 : Blo 183802 185071 := bstep (se 1 (by rfl) ⟨138803, by rfl⟩ : syracuseStep 185071 = 277607) B277607
theorem B185119 : Blo 183802 185119 := bstep (se 1 (by rfl) ⟨138839, by rfl⟩ : syracuseStep 185119 = 277679) B277679
theorem B185471 : Blo 183802 185471 := bstep (se 1 (by rfl) ⟨139103, by rfl⟩ : syracuseStep 185471 = 278207) B278207
theorem B185627 : Blo 183802 185627 := bstep (se 1 (by rfl) ⟨139220, by rfl⟩ : syracuseStep 185627 = 278441) B278441
theorem B185727 : Blo 183802 185727 := bstep (se 1 (by rfl) ⟨139295, by rfl⟩ : syracuseStep 185727 = 278591) B278591
theorem B1594889 : Blo 183802 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B8968067 : Blo 183802 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B186303 : Blo 183802 186303 := bstep (se 1 (by rfl) ⟨139727, by rfl⟩ : syracuseStep 186303 = 279455) B279455
theorem B448679 : Blo 183802 448679 := bstep (se 1 (by rfl) ⟨336509, by rfl⟩ : syracuseStep 448679 = 673019) B673019
theorem B186575 : Blo 183802 186575 := bstep (se 1 (by rfl) ⟨139931, by rfl⟩ : syracuseStep 186575 = 279863) B279863
theorem B415979 : Blo 183802 415979 := bstep (se 1 (by rfl) ⟨311984, by rfl⟩ : syracuseStep 415979 = 623969) B623969
theorem B186815 : Blo 183802 186815 := bstep (se 1 (by rfl) ⟨140111, by rfl⟩ : syracuseStep 186815 = 280223) B280223
theorem B187119 : Blo 183802 187119 := bstep (se 1 (by rfl) ⟨140339, by rfl⟩ : syracuseStep 187119 = 280679) B280679
theorem B940895 : Blo 183802 940895 := bstep (se 1 (by rfl) ⟨705671, by rfl⟩ : syracuseStep 940895 = 1411343) B1411343
theorem B351287 : Blo 183802 351287 := bstep (se 1 (by rfl) ⟨263465, by rfl⟩ : syracuseStep 351287 = 526931) B526931
theorem B4480343 : Blo 183802 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B1727851 : Blo 183802 1727851 := bstep (se 1 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 1727851 = 2591777) B2591777
theorem B417455 : Blo 183802 417455 := bstep (se 1 (by rfl) ⟨313091, by rfl⟩ : syracuseStep 417455 = 626183) B626183
theorem B7855825 : Blo 183802 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B417545 : Blo 183802 417545 := bstep (se 2 (by rfl) ⟨156579, by rfl⟩ : syracuseStep 417545 = 313159) B313159
theorem B352039 : Blo 183802 352039 := bstep (se 1 (by rfl) ⟨264029, by rfl⟩ : syracuseStep 352039 = 528059) B528059
theorem B3596831 : Blo 183802 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B713441 : Blo 183802 713441 := bstep (se 2 (by rfl) ⟨267540, by rfl⟩ : syracuseStep 713441 = 535081) B535081
theorem B189167 : Blo 183802 189167 := bstep (se 1 (by rfl) ⟨141875, by rfl⟩ : syracuseStep 189167 = 283751) B283751
theorem B419435 : Blo 183802 419435 := bstep (se 1 (by rfl) ⟨314576, by rfl⟩ : syracuseStep 419435 = 629153) B629153
theorem B419471 : Blo 183802 419471 := bstep (se 1 (by rfl) ⟨314603, by rfl⟩ : syracuseStep 419471 = 629207) B629207
theorem B13526837 : Blo 183802 13526837 := bstep (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) B1268141
theorem B2681657 : Blo 183802 2681657 := bstep (se 2 (by rfl) ⟨1005621, by rfl⟩ : syracuseStep 2681657 = 2011243) B2011243
theorem B420713 : Blo 183802 420713 := bstep (se 2 (by rfl) ⟨157767, by rfl⟩ : syracuseStep 420713 = 315535) B315535
theorem B421055 : Blo 183802 421055 := bstep (se 1 (by rfl) ⟨315791, by rfl⟩ : syracuseStep 421055 = 631583) B631583
theorem B422171 : Blo 183802 422171 := bstep (se 1 (by rfl) ⟨316628, by rfl⟩ : syracuseStep 422171 = 633257) B633257
theorem B8026289 : Blo 183802 8026289 := bstep (se 2 (by rfl) ⟨3009858, by rfl⟩ : syracuseStep 8026289 = 6019717) B6019717
theorem B1800407 : Blo 183802 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B620999 : Blo 183802 620999 := bstep (se 1 (by rfl) ⟨465749, by rfl⟩ : syracuseStep 620999 = 931499) B931499
theorem B2554679 : Blo 183802 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B1342271 : Blo 183802 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B8192609 : Blo 183802 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B394105 : Blo 183802 394105 := bstep (se 2 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 394105 = 295579) B295579
theorem B525359 : Blo 183802 525359 := bstep (se 1 (by rfl) ⟨394019, by rfl⟩ : syracuseStep 525359 = 788039) B788039
theorem B624671 : Blo 183802 624671 := bstep (se 1 (by rfl) ⟨468503, by rfl⟩ : syracuseStep 624671 = 937007) B937007
theorem B460903 : Blo 183802 460903 := bstep (se 1 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 460903 = 691355) B691355
theorem B625103 : Blo 183802 625103 := bstep (se 1 (by rfl) ⟨468827, by rfl⟩ : syracuseStep 625103 = 937655) B937655
theorem B1183031 : Blo 183802 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B1183085 : Blo 183802 1183085 := bstep (se 3 (by rfl) ⟨221828, by rfl⟩ : syracuseStep 1183085 = 443657) B443657
theorem B299119 : Blo 183802 299119 := bstep (se 1 (by rfl) ⟨224339, by rfl⟩ : syracuseStep 299119 = 448679) B448679
theorem B627263 : Blo 183802 627263 := bstep (se 1 (by rfl) ⟨470447, by rfl⟩ : syracuseStep 627263 = 940895) B940895
theorem B234191 : Blo 183802 234191 := bstep (se 1 (by rfl) ⟨175643, by rfl⟩ : syracuseStep 234191 = 351287) B351287
theorem B2986895 : Blo 183802 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B2397887 : Blo 183802 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B1185491 : Blo 183802 1185491 := bstep (se 1 (by rfl) ⟨889118, by rfl⟩ : syracuseStep 1185491 = 1778237) B1778237
theorem B9017891 : Blo 183802 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B1776239 : Blo 183802 1776239 := bstep (se 1 (by rfl) ⟨1332179, by rfl⟩ : syracuseStep 1776239 = 2664359) B2664359
theorem B596591 : Blo 183802 596591 := bstep (se 1 (by rfl) ⟨447443, by rfl⟩ : syracuseStep 596591 = 894887) B894887
theorem B3579389 : Blo 183802 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B3153653 : Blo 183802 3153653 := bstep (se 5 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 3153653 = 295655) B295655
theorem B1582111 : Blo 183802 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B1057961 : Blo 183802 1057961 := bstep (se 2 (by rfl) ⟨396735, by rfl⟩ : syracuseStep 1057961 = 793471) B793471
theorem B599231 : Blo 183802 599231 := bstep (se 1 (by rfl) ⟨449423, by rfl⟩ : syracuseStep 599231 = 898847) B898847
theorem B468251 : Blo 183802 468251 := bstep (se 1 (by rfl) ⟨351188, by rfl⟩ : syracuseStep 468251 = 702377) B702377
theorem B1058143 : Blo 183802 1058143 := bstep (se 1 (by rfl) ⟨793607, by rfl⟩ : syracuseStep 1058143 = 1587215) B1587215
theorem B5350859 : Blo 183802 5350859 := bstep (se 1 (by rfl) ⟨4013144, by rfl⟩ : syracuseStep 5350859 = 8026289) B8026289
theorem B665167 : Blo 183802 665167 := bstep (se 1 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 665167 = 997751) B997751
theorem B2303801 : Blo 183802 2303801 := bstep (se 2 (by rfl) ⟨863925, by rfl⟩ : syracuseStep 2303801 = 1727851) B1727851
theorem B337975 : Blo 183802 337975 := bstep (se 1 (by rfl) ⟨253481, by rfl⟩ : syracuseStep 337975 = 506963) B506963
theorem B469385 : Blo 183802 469385 := bstep (se 2 (by rfl) ⟨176019, by rfl⟩ : syracuseStep 469385 = 352039) B352039
theorem B471035 : Blo 183802 471035 := bstep (se 1 (by rfl) ⟨353276, by rfl⟩ : syracuseStep 471035 = 706553) B706553
theorem B275963 : Blo 183802 275963 := bstep (se 1 (by rfl) ⟨206972, by rfl⟩ : syracuseStep 275963 = 413945) B413945
theorem B899039 : Blo 183802 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B931985 : Blo 183802 931985 := bstep (se 2 (by rfl) ⟨349494, by rfl⟩ : syracuseStep 931985 = 698989) B698989
theorem B1063259 : Blo 183802 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B5978711 : Blo 183802 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B277289 : Blo 183802 277289 := bstep (se 2 (by rfl) ⟨103983, by rfl⟩ : syracuseStep 277289 = 207967) B207967
theorem B277319 : Blo 183802 277319 := bstep (se 1 (by rfl) ⟨207989, by rfl⟩ : syracuseStep 277319 = 415979) B415979
theorem B769247 : Blo 183802 769247 := bstep (se 1 (by rfl) ⟨576935, by rfl⟩ : syracuseStep 769247 = 1153871) B1153871
theorem B278303 : Blo 183802 278303 := bstep (se 1 (by rfl) ⟨208727, by rfl⟩ : syracuseStep 278303 = 417455) B417455
theorem B2015047 : Blo 183802 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B278363 : Blo 183802 278363 := bstep (se 1 (by rfl) ⟨208772, by rfl⟩ : syracuseStep 278363 = 417545) B417545
theorem B933929 : Blo 183802 933929 := bstep (se 2 (by rfl) ⟨350223, by rfl⟩ : syracuseStep 933929 = 700447) B700447
theorem B475627 : Blo 183802 475627 := bstep (se 1 (by rfl) ⟨356720, by rfl⟩ : syracuseStep 475627 = 713441) B713441
theorem B377759 : Blo 183802 377759 := bstep (se 1 (by rfl) ⟨283319, by rfl⟩ : syracuseStep 377759 = 566639) B566639
theorem B279623 : Blo 183802 279623 := bstep (se 1 (by rfl) ⟨209717, by rfl⟩ : syracuseStep 279623 = 419435) B419435
theorem B279647 : Blo 183802 279647 := bstep (se 1 (by rfl) ⟨209735, by rfl⟩ : syracuseStep 279647 = 419471) B419471
theorem B279689 : Blo 183802 279689 := bstep (se 2 (by rfl) ⟨104883, by rfl⟩ : syracuseStep 279689 = 209767) B209767
theorem B1787771 : Blo 183802 1787771 := bstep (se 1 (by rfl) ⟨1340828, by rfl⟩ : syracuseStep 1787771 = 2681657) B2681657
theorem B280475 : Blo 183802 280475 := bstep (se 1 (by rfl) ⟨210356, by rfl⟩ : syracuseStep 280475 = 420713) B420713
theorem B280703 : Blo 183802 280703 := bstep (se 1 (by rfl) ⟨210527, by rfl⟩ : syracuseStep 280703 = 421055) B421055
theorem B2017781 : Blo 183802 2017781 := bstep (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) B189167
theorem B281447 : Blo 183802 281447 := bstep (se 1 (by rfl) ⟨211085, by rfl⟩ : syracuseStep 281447 = 422171) B422171
theorem B184091 : Blo 183802 184091 := bstep (se 1 (by rfl) ⟨138068, by rfl⟩ : syracuseStep 184091 = 276137) B276137
theorem B1200271 : Blo 183802 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B184571 : Blo 183802 184571 := bstep (se 1 (by rfl) ⟨138428, by rfl⟩ : syracuseStep 184571 = 276857) B276857
theorem B413999 : Blo 183802 413999 := bstep (se 1 (by rfl) ⟨310499, by rfl⟩ : syracuseStep 413999 = 620999) B620999
theorem B184735 : Blo 183802 184735 := bstep (se 1 (by rfl) ⟨138551, by rfl⟩ : syracuseStep 184735 = 277103) B277103
theorem B185159 : Blo 183802 185159 := bstep (se 1 (by rfl) ⟨138869, by rfl⟩ : syracuseStep 185159 = 277739) B277739
theorem B1332065 : Blo 183802 1332065 := bstep (se 2 (by rfl) ⟨499524, by rfl⟩ : syracuseStep 1332065 = 999049) B999049
theorem B709499 : Blo 183802 709499 := bstep (se 1 (by rfl) ⟨532124, by rfl⟩ : syracuseStep 709499 = 1064249) B1064249
theorem B10474433 : Blo 183802 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B185455 : Blo 183802 185455 := bstep (se 1 (by rfl) ⟨139091, by rfl⟩ : syracuseStep 185455 = 278183) B278183
theorem B185503 : Blo 183802 185503 := bstep (se 1 (by rfl) ⟨139127, by rfl⟩ : syracuseStep 185503 = 278255) B278255
theorem B185903 : Blo 183802 185903 := bstep (se 1 (by rfl) ⟨139427, by rfl⟩ : syracuseStep 185903 = 278855) B278855
theorem B186471 : Blo 183802 186471 := bstep (se 1 (by rfl) ⟨139853, by rfl⟩ : syracuseStep 186471 = 279707) B279707
theorem B187111 : Blo 183802 187111 := bstep (se 1 (by rfl) ⟨140333, by rfl⟩ : syracuseStep 187111 = 280667) B280667
theorem B3201767 : Blo 183802 3201767 := bstep (se 1 (by rfl) ⟨2401325, by rfl⟩ : syracuseStep 3201767 = 4802651) B4802651
theorem B1989623 : Blo 183802 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B1793153 : Blo 183802 1793153 := bstep (se 2 (by rfl) ⟨672432, by rfl⟩ : syracuseStep 1793153 = 1344865) B1344865
theorem B711929 : Blo 183802 711929 := bstep (se 2 (by rfl) ⟨266973, by rfl⟩ : syracuseStep 711929 = 533947) B533947
theorem B187695 : Blo 183802 187695 := bstep (se 1 (by rfl) ⟨140771, by rfl⟩ : syracuseStep 187695 = 281543) B281543
theorem B1564343 : Blo 183802 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B417599 : Blo 183802 417599 := bstep (se 1 (by rfl) ⟨313199, by rfl⟩ : syracuseStep 417599 = 626399) B626399
theorem B1991141 : Blo 183802 1991141 := bstep (se 4 (by rfl) ⟨186669, by rfl⟩ : syracuseStep 1991141 = 373339) B373339
theorem B418643 : Blo 183802 418643 := bstep (se 1 (by rfl) ⟨313982, by rfl⟩ : syracuseStep 418643 = 627965) B627965
theorem B420137 : Blo 183802 420137 := bstep (se 2 (by rfl) ⟨157551, by rfl⟩ : syracuseStep 420137 = 315103) B315103
theorem B1010555 : Blo 183802 1010555 := bstep (se 1 (by rfl) ⟨757916, by rfl⟩ : syracuseStep 1010555 = 1515833) B1515833
theorem B356071 : Blo 183802 356071 := bstep (se 1 (by rfl) ⟨267053, by rfl⟩ : syracuseStep 356071 = 534107) B534107
theorem B51572537 : Blo 183802 51572537 := bstep (se 2 (by rfl) ⟨19339701, by rfl⟩ : syracuseStep 51572537 = 38679403) B38679403
theorem B2125763 : Blo 183802 2125763 := bstep (se 1 (by rfl) ⟨1594322, by rfl⟩ : syracuseStep 2125763 = 3188645) B3188645
theorem B620783 : Blo 183802 620783 := bstep (se 1 (by rfl) ⟨465587, by rfl⟩ : syracuseStep 620783 = 931175) B931175
theorem B9075503 : Blo 183802 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B1703119 : Blo 183802 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B949967 : Blo 183802 949967 := bstep (se 1 (by rfl) ⟨712475, by rfl⟩ : syracuseStep 949967 = 1424951) B1424951
theorem B622619 : Blo 183802 622619 := bstep (se 1 (by rfl) ⟨466964, by rfl⟩ : syracuseStep 622619 = 933929) B933929
theorem B1802533 : Blo 183802 1802533 := bstep (se 4 (by rfl) ⟨168987, by rfl⟩ : syracuseStep 1802533 = 337975) B337975
theorem B525473 : Blo 183802 525473 := bstep (se 2 (by rfl) ⟨197052, by rfl⟩ : syracuseStep 525473 = 394105) B394105
theorem B1345187 : Blo 183802 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B1410857 : Blo 183802 1410857 := bstep (se 2 (by rfl) ⟨529071, by rfl⟩ : syracuseStep 1410857 = 1058143) B1058143
theorem B624509 : Blo 183802 624509 := bstep (se 3 (by rfl) ⟨117095, by rfl⟩ : syracuseStep 624509 = 234191) B234191
theorem B886889 : Blo 183802 886889 := bstep (se 2 (by rfl) ⟨332583, by rfl⟩ : syracuseStep 886889 = 665167) B665167
theorem B788687 : Blo 183802 788687 := bstep (se 1 (by rfl) ⟨591515, by rfl⟩ : syracuseStep 788687 = 1183031) B1183031
theorem B788723 : Blo 183802 788723 := bstep (se 1 (by rfl) ⟨591542, by rfl⟩ : syracuseStep 788723 = 1183085) B1183085
theorem B7965053 : Blo 183802 7965053 := bstep (se 3 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 7965053 = 2986895) B2986895
theorem B888043 : Blo 183802 888043 := bstep (se 1 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 888043 = 1332065) B1332065
theorem B6982955 : Blo 183802 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B790327 : Blo 183802 790327 := bstep (se 1 (by rfl) ⟨592745, by rfl⟩ : syracuseStep 790327 = 1185491) B1185491
theorem B1184159 : Blo 183802 1184159 := bstep (se 1 (by rfl) ⟨888119, by rfl⟩ : syracuseStep 1184159 = 1776239) B1776239
theorem B397727 : Blo 183802 397727 := bstep (se 1 (by rfl) ⟨298295, by rfl⟩ : syracuseStep 397727 = 596591) B596591
theorem B2134511 : Blo 183802 2134511 := bstep (se 1 (by rfl) ⟨1600883, by rfl⟩ : syracuseStep 2134511 = 3201767) B3201767
theorem B2102435 : Blo 183802 2102435 := bstep (se 1 (by rfl) ⟨1576826, by rfl⟩ : syracuseStep 2102435 = 3153653) B3153653
theorem B398825 : Blo 183802 398825 := bstep (se 2 (by rfl) ⟨149559, by rfl⟩ : syracuseStep 398825 = 299119) B299119
theorem B399487 : Blo 183802 399487 := bstep (se 1 (by rfl) ⟨299615, by rfl⟩ : syracuseStep 399487 = 599231) B599231
theorem B34381691 : Blo 183802 34381691 := bstep (se 1 (by rfl) ⟨25786268, by rfl⟩ : syracuseStep 34381691 = 51572537) B51572537
theorem B1417175 : Blo 183802 1417175 := bstep (se 1 (by rfl) ⟨1062881, by rfl⟩ : syracuseStep 1417175 = 2125763) B2125763
theorem B599359 : Blo 183802 599359 := bstep (se 1 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 599359 = 899039) B899039
theorem B2270825 : Blo 183802 2270825 := bstep (se 2 (by rfl) ⟨851559, by rfl⟩ : syracuseStep 2270825 = 1703119) B1703119
theorem B633311 : Blo 183802 633311 := bstep (se 1 (by rfl) ⟨474983, by rfl⟩ : syracuseStep 633311 = 949967) B949967
theorem B634169 : Blo 183802 634169 := bstep (se 2 (by rfl) ⟨237813, by rfl⟩ : syracuseStep 634169 = 475627) B475627
theorem B1191847 : Blo 183802 1191847 := bstep (se 1 (by rfl) ⟨893885, by rfl⟩ : syracuseStep 1191847 = 1787771) B1787771
theorem B275999 : Blo 183802 275999 := bstep (se 1 (by rfl) ⟨206999, by rfl⟩ : syracuseStep 275999 = 413999) B413999
theorem B472999 : Blo 183802 472999 := bstep (se 1 (by rfl) ⟨354749, by rfl⟩ : syracuseStep 472999 = 709499) B709499
theorem B6011927 : Blo 183802 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B1326415 : Blo 183802 1326415 := bstep (se 1 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 1326415 = 1989623) B1989623
theorem B1195435 : Blo 183802 1195435 := bstep (se 1 (by rfl) ⟨896576, by rfl⟩ : syracuseStep 1195435 = 1793153) B1793153
theorem B474619 : Blo 183802 474619 := bstep (se 1 (by rfl) ⟨355964, by rfl⟩ : syracuseStep 474619 = 711929) B711929
theorem B474761 : Blo 183802 474761 := bstep (se 2 (by rfl) ⟨178035, by rfl⟩ : syracuseStep 474761 = 356071) B356071
theorem B278399 : Blo 183802 278399 := bstep (se 1 (by rfl) ⟨208799, by rfl⟩ : syracuseStep 278399 = 417599) B417599
theorem B8437925 : Blo 183802 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B1327427 : Blo 183802 1327427 := bstep (se 1 (by rfl) ⟨995570, by rfl⟩ : syracuseStep 1327427 = 1991141) B1991141
theorem B279095 : Blo 183802 279095 := bstep (se 1 (by rfl) ⟨209321, by rfl⟩ : syracuseStep 279095 = 418643) B418643
theorem B705307 : Blo 183802 705307 := bstep (se 1 (by rfl) ⟨528980, by rfl⟩ : syracuseStep 705307 = 1057961) B1057961
theorem B312167 : Blo 183802 312167 := bstep (se 1 (by rfl) ⟨234125, by rfl⟩ : syracuseStep 312167 = 468251) B468251
theorem B280091 : Blo 183802 280091 := bstep (se 1 (by rfl) ⟨210068, by rfl⟩ : syracuseStep 280091 = 420137) B420137
theorem B15943229 : Blo 183802 15943229 := bstep (se 3 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 15943229 = 5978711) B5978711
theorem B312923 : Blo 183802 312923 := bstep (se 1 (by rfl) ⟨234692, by rfl⟩ : syracuseStep 312923 = 469385) B469385
theorem B673703 : Blo 183802 673703 := bstep (se 1 (by rfl) ⟨505277, by rfl⟩ : syracuseStep 673703 = 1010555) B1010555
theorem B314023 : Blo 183802 314023 := bstep (se 1 (by rfl) ⟨235517, by rfl⟩ : syracuseStep 314023 = 471035) B471035
theorem B183975 : Blo 183802 183975 := bstep (se 1 (by rfl) ⟨137981, by rfl⟩ : syracuseStep 183975 = 275963) B275963
theorem B413855 : Blo 183802 413855 := bstep (se 1 (by rfl) ⟨310391, by rfl⟩ : syracuseStep 413855 = 620783) B620783
theorem B708839 : Blo 183802 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B184859 : Blo 183802 184859 := bstep (se 1 (by rfl) ⟨138644, by rfl⟩ : syracuseStep 184859 = 277289) B277289
theorem B6050335 : Blo 183802 6050335 := bstep (se 1 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 6050335 = 9075503) B9075503
theorem B184879 : Blo 183802 184879 := bstep (se 1 (by rfl) ⟨138659, by rfl⟩ : syracuseStep 184879 = 277319) B277319
theorem B512831 : Blo 183802 512831 := bstep (se 1 (by rfl) ⟨384623, by rfl⟩ : syracuseStep 512831 = 769247) B769247
theorem B185535 : Blo 183802 185535 := bstep (se 1 (by rfl) ⟨139151, by rfl⟩ : syracuseStep 185535 = 278303) B278303
theorem B185575 : Blo 183802 185575 := bstep (se 1 (by rfl) ⟨139181, by rfl⟩ : syracuseStep 185575 = 278363) B278363
theorem B5461739 : Blo 183802 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B251839 : Blo 183802 251839 := bstep (se 1 (by rfl) ⟨188879, by rfl⟩ : syracuseStep 251839 = 377759) B377759
theorem B350239 : Blo 183802 350239 := bstep (se 1 (by rfl) ⟨262679, by rfl⟩ : syracuseStep 350239 = 525359) B525359
theorem B186415 : Blo 183802 186415 := bstep (se 1 (by rfl) ⟨139811, by rfl⟩ : syracuseStep 186415 = 279623) B279623
theorem B186431 : Blo 183802 186431 := bstep (se 1 (by rfl) ⟨139823, by rfl⟩ : syracuseStep 186431 = 279647) B279647
theorem B186459 : Blo 183802 186459 := bstep (se 1 (by rfl) ⟨139844, by rfl⟩ : syracuseStep 186459 = 279689) B279689
theorem B186983 : Blo 183802 186983 := bstep (se 1 (by rfl) ⟨140237, by rfl⟩ : syracuseStep 186983 = 280475) B280475
theorem B416447 : Blo 183802 416447 := bstep (se 1 (by rfl) ⟨312335, by rfl⟩ : syracuseStep 416447 = 624671) B624671
theorem B187135 : Blo 183802 187135 := bstep (se 1 (by rfl) ⟨140351, by rfl⟩ : syracuseStep 187135 = 280703) B280703
theorem B416735 : Blo 183802 416735 := bstep (se 1 (by rfl) ⟨312551, by rfl⟩ : syracuseStep 416735 = 625103) B625103
theorem B187631 : Blo 183802 187631 := bstep (se 1 (by rfl) ⟨140723, by rfl⟩ : syracuseStep 187631 = 281447) B281447
theorem B614537 : Blo 183802 614537 := bstep (se 2 (by rfl) ⟨230451, by rfl⟩ : syracuseStep 614537 = 460903) B460903
theorem B418175 : Blo 183802 418175 := bstep (se 1 (by rfl) ⟨313631, by rfl⟩ : syracuseStep 418175 = 627263) B627263
theorem B1598591 : Blo 183802 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B2386259 : Blo 183802 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B1042895 : Blo 183802 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B1600361 : Blo 183802 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B3567239 : Blo 183802 3567239 := bstep (se 1 (by rfl) ⟨2675429, by rfl⟩ : syracuseStep 3567239 = 5350859) B5350859
theorem B1535867 : Blo 183802 1535867 := bstep (se 1 (by rfl) ⟨1151900, by rfl⟩ : syracuseStep 1535867 = 2303801) B2303801
theorem B621323 : Blo 183802 621323 := bstep (se 1 (by rfl) ⟨465992, by rfl⟩ : syracuseStep 621323 = 931985) B931985
theorem B10746917 : Blo 183802 10746917 := bstep (se 4 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 10746917 = 2015047) B2015047
theorem B884951 : Blo 183802 884951 := bstep (se 1 (by rfl) ⟨663713, by rfl⟩ : syracuseStep 884951 = 1327427) B1327427
theorem B525791 : Blo 183802 525791 := bstep (se 1 (by rfl) ⟨394343, by rfl⟩ : syracuseStep 525791 = 788687) B788687
theorem B525815 : Blo 183802 525815 := bstep (se 1 (by rfl) ⟨394361, by rfl⟩ : syracuseStep 525815 = 788723) B788723
theorem B5310035 : Blo 183802 5310035 := bstep (se 1 (by rfl) ⟨3982526, by rfl⟩ : syracuseStep 5310035 = 7965053) B7965053
theorem B4655303 : Blo 183802 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B789439 : Blo 183802 789439 := bstep (se 1 (by rfl) ⟨592079, by rfl⟩ : syracuseStep 789439 = 1184159) B1184159
theorem B265151 : Blo 183802 265151 := bstep (se 1 (by rfl) ⟨198863, by rfl⟩ : syracuseStep 265151 = 397727) B397727
theorem B265883 : Blo 183802 265883 := bstep (se 1 (by rfl) ⟨199412, by rfl⟩ : syracuseStep 265883 = 398825) B398825
theorem B3641159 : Blo 183802 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B1184057 : Blo 183802 1184057 := bstep (se 2 (by rfl) ⟨444021, by rfl⟩ : syracuseStep 1184057 = 888043) B888043
theorem B1053769 : Blo 183802 1053769 := bstep (se 2 (by rfl) ⟨395163, by rfl⟩ : syracuseStep 1053769 = 790327) B790327
theorem B2365037 : Blo 183802 2365037 := bstep (se 3 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 2365037 = 886889) B886889
theorem B8067113 : Blo 183802 8067113 := bstep (se 2 (by rfl) ⟨3025167, by rfl⟩ : syracuseStep 8067113 = 6050335) B6050335
theorem B1513883 : Blo 183802 1513883 := bstep (se 1 (by rfl) ⟨1135412, by rfl⟩ : syracuseStep 1513883 = 2270825) B2270825
theorem B630665 : Blo 183802 630665 := bstep (se 2 (by rfl) ⟨236499, by rfl⟩ : syracuseStep 630665 = 472999) B472999
theorem B1023911 : Blo 183802 1023911 := bstep (se 1 (by rfl) ⟨767933, by rfl⟩ : syracuseStep 1023911 = 1535867) B1535867
theorem B335785 : Blo 183802 335785 := bstep (se 2 (by rfl) ⟨125919, by rfl⟩ : syracuseStep 335785 = 251839) B251839
theorem B466985 : Blo 183802 466985 := bstep (se 2 (by rfl) ⟨175119, by rfl⟩ : syracuseStep 466985 = 350239) B350239
theorem B532649 : Blo 183802 532649 := bstep (se 2 (by rfl) ⟨199743, by rfl⟩ : syracuseStep 532649 = 399487) B399487
theorem B632825 : Blo 183802 632825 := bstep (se 2 (by rfl) ⟨237309, by rfl⟩ : syracuseStep 632825 = 474619) B474619
theorem B4007951 : Blo 183802 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B2403377 : Blo 183802 2403377 := bstep (se 2 (by rfl) ⟨901266, by rfl⟩ : syracuseStep 2403377 = 1802533) B1802533
theorem B208111 : Blo 183802 208111 := bstep (se 1 (by rfl) ⟨156083, by rfl⟩ : syracuseStep 208111 = 312167) B312167
theorem B10628819 : Blo 183802 10628819 := bstep (se 1 (by rfl) ⟨7971614, by rfl⟩ : syracuseStep 10628819 = 15943229) B15943229
theorem B208615 : Blo 183802 208615 := bstep (se 1 (by rfl) ⟨156461, by rfl⟩ : syracuseStep 208615 = 312923) B312923
theorem B896791 : Blo 183802 896791 := bstep (se 1 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 896791 = 1345187) B1345187
theorem B799145 : Blo 183802 799145 := bstep (se 2 (by rfl) ⟨299679, by rfl⟩ : syracuseStep 799145 = 599359) B599359
theorem B275903 : Blo 183802 275903 := bstep (se 1 (by rfl) ⟨206927, by rfl⟩ : syracuseStep 275903 = 413855) B413855
theorem B472559 : Blo 183802 472559 := bstep (se 1 (by rfl) ⟨354419, by rfl⟩ : syracuseStep 472559 = 708839) B708839
theorem B1423007 : Blo 183802 1423007 := bstep (se 1 (by rfl) ⟨1067255, by rfl⟩ : syracuseStep 1423007 = 2134511) B2134511
theorem B277631 : Blo 183802 277631 := bstep (se 1 (by rfl) ⟨208223, by rfl⟩ : syracuseStep 277631 = 416447) B416447
theorem B277823 : Blo 183802 277823 := bstep (se 1 (by rfl) ⟨208367, by rfl⟩ : syracuseStep 277823 = 416735) B416735
theorem B1589129 : Blo 183802 1589129 := bstep (se 2 (by rfl) ⟨595923, by rfl⟩ : syracuseStep 1589129 = 1191847) B1191847
theorem B22921127 : Blo 183802 22921127 := bstep (se 1 (by rfl) ⟨17190845, by rfl⟩ : syracuseStep 22921127 = 34381691) B34381691
theorem B409691 : Blo 183802 409691 := bstep (se 1 (by rfl) ⟨307268, by rfl⟩ : syracuseStep 409691 = 614537) B614537
theorem B278783 : Blo 183802 278783 := bstep (se 1 (by rfl) ⟨209087, by rfl⟩ : syracuseStep 278783 = 418175) B418175
theorem B1065727 : Blo 183802 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B1590839 : Blo 183802 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B1066907 : Blo 183802 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B2378159 : Blo 183802 2378159 := bstep (se 1 (by rfl) ⟨1783619, by rfl⟩ : syracuseStep 2378159 = 3567239) B3567239
theorem B1691117 : Blo 183802 1691117 := bstep (se 3 (by rfl) ⟨317084, by rfl⟩ : syracuseStep 1691117 = 634169) B634169
theorem B183999 : Blo 183802 183999 := bstep (se 1 (by rfl) ⟨137999, by rfl⟩ : syracuseStep 183999 = 275999) B275999
theorem B414215 : Blo 183802 414215 := bstep (se 1 (by rfl) ⟨310661, by rfl⟩ : syracuseStep 414215 = 621323) B621323
theorem B1593913 : Blo 183802 1593913 := bstep (se 2 (by rfl) ⟨597717, by rfl⟩ : syracuseStep 1593913 = 1195435) B1195435
theorem B7164611 : Blo 183802 7164611 := bstep (se 1 (by rfl) ⟨5373458, by rfl⟩ : syracuseStep 7164611 = 10746917) B10746917
theorem B316507 : Blo 183802 316507 := bstep (se 1 (by rfl) ⟨237380, by rfl⟩ : syracuseStep 316507 = 474761) B474761
theorem B185599 : Blo 183802 185599 := bstep (se 1 (by rfl) ⟨139199, by rfl⟩ : syracuseStep 185599 = 278399) B278399
theorem B415079 : Blo 183802 415079 := bstep (se 1 (by rfl) ⟨311309, by rfl⟩ : syracuseStep 415079 = 622619) B622619
theorem B5625283 : Blo 183802 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B186063 : Blo 183802 186063 := bstep (se 1 (by rfl) ⟨139547, by rfl⟩ : syracuseStep 186063 = 279095) B279095
theorem B350315 : Blo 183802 350315 := bstep (se 1 (by rfl) ⟨262736, by rfl⟩ : syracuseStep 350315 = 525473) B525473
theorem B186727 : Blo 183802 186727 := bstep (se 1 (by rfl) ⟨140045, by rfl⟩ : syracuseStep 186727 = 280091) B280091
theorem B940409 : Blo 183802 940409 := bstep (se 2 (by rfl) ⟨352653, by rfl⟩ : syracuseStep 940409 = 705307) B705307
theorem B940571 : Blo 183802 940571 := bstep (se 1 (by rfl) ⟨705428, by rfl⟩ : syracuseStep 940571 = 1410857) B1410857
theorem B416339 : Blo 183802 416339 := bstep (se 1 (by rfl) ⟨312254, by rfl⟩ : syracuseStep 416339 = 624509) B624509
theorem B449135 : Blo 183802 449135 := bstep (se 1 (by rfl) ⟨336851, by rfl⟩ : syracuseStep 449135 = 673703) B673703
theorem B1367549 : Blo 183802 1367549 := bstep (se 3 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 1367549 = 512831) B512831
theorem B1401623 : Blo 183802 1401623 := bstep (se 1 (by rfl) ⟨1051217, by rfl⟩ : syracuseStep 1401623 = 2102435) B2102435
theorem B418697 : Blo 183802 418697 := bstep (se 2 (by rfl) ⟨157011, by rfl⟩ : syracuseStep 418697 = 314023) B314023
theorem B944783 : Blo 183802 944783 := bstep (se 1 (by rfl) ⟨708587, by rfl⟩ : syracuseStep 944783 = 1417175) B1417175
theorem B2781053 : Blo 183802 2781053 := bstep (se 3 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 2781053 = 1042895) B1042895
theorem B422207 : Blo 183802 422207 := bstep (se 1 (by rfl) ⟨316655, by rfl⟩ : syracuseStep 422207 = 633311) B633311
theorem B1768553 : Blo 183802 1768553 := bstep (se 2 (by rfl) ⟨663207, by rfl⟩ : syracuseStep 1768553 = 1326415) B1326415
theorem B589967 : Blo 183802 589967 := bstep (se 1 (by rfl) ⟨442475, by rfl⟩ : syracuseStep 589967 = 884951) B884951
theorem B3540023 : Blo 183802 3540023 := bstep (se 1 (by rfl) ⟨2655017, by rfl⟩ : syracuseStep 3540023 = 5310035) B5310035
theorem B789371 : Blo 183802 789371 := bstep (se 1 (by rfl) ⟨592028, by rfl⟩ : syracuseStep 789371 = 1184057) B1184057
theorem B1576691 : Blo 183802 1576691 := bstep (se 1 (by rfl) ⟨1182518, by rfl⟩ : syracuseStep 1576691 = 2365037) B2365037
theorem B1052585 : Blo 183802 1052585 := bstep (se 2 (by rfl) ⟨394719, by rfl⟩ : syracuseStep 1052585 = 789439) B789439
theorem B5378075 : Blo 183802 5378075 := bstep (se 1 (by rfl) ⟨4033556, by rfl⟩ : syracuseStep 5378075 = 8067113) B8067113
theorem B233543 : Blo 183802 233543 := bstep (se 1 (by rfl) ⟨175157, by rfl⟩ : syracuseStep 233543 = 350315) B350315
theorem B626939 : Blo 183802 626939 := bstep (se 1 (by rfl) ⟨470204, by rfl⟩ : syracuseStep 626939 = 940409) B940409
theorem B627047 : Blo 183802 627047 := bstep (se 1 (by rfl) ⟨470285, by rfl⟩ : syracuseStep 627047 = 940571) B940571
theorem B299423 : Blo 183802 299423 := bstep (se 1 (by rfl) ⟨224567, by rfl⟩ : syracuseStep 299423 = 449135) B449135
theorem B629855 : Blo 183802 629855 := bstep (se 1 (by rfl) ⟨472391, by rfl⟩ : syracuseStep 629855 = 944783) B944783
theorem B7085879 : Blo 183802 7085879 := bstep (se 1 (by rfl) ⟨5314409, by rfl⟩ : syracuseStep 7085879 = 10628819) B10628819
theorem B532763 : Blo 183802 532763 := bstep (se 1 (by rfl) ⟨399572, by rfl⟩ : syracuseStep 532763 = 799145) B799145
theorem B9709757 : Blo 183802 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B1059419 : Blo 183802 1059419 := bstep (se 1 (by rfl) ⟨794564, by rfl⟩ : syracuseStep 1059419 = 1589129) B1589129
theorem B15280751 : Blo 183802 15280751 := bstep (se 1 (by rfl) ⟨11460563, by rfl⟩ : syracuseStep 15280751 = 22921127) B22921127
theorem B1092509 : Blo 183802 1092509 := bstep (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) B409691
theorem B1060559 : Blo 183802 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B1585439 : Blo 183802 1585439 := bstep (se 1 (by rfl) ⟨1189079, by rfl⟩ : syracuseStep 1585439 = 2378159) B2378159
theorem B1127411 : Blo 183802 1127411 := bstep (se 1 (by rfl) ⟨845558, by rfl⟩ : syracuseStep 1127411 = 1691117) B1691117
theorem B276143 : Blo 183802 276143 := bstep (se 1 (by rfl) ⟨207107, by rfl⟩ : syracuseStep 276143 = 414215) B414215
theorem B276719 : Blo 183802 276719 := bstep (se 1 (by rfl) ⟨207539, by rfl⟩ : syracuseStep 276719 = 415079) B415079
theorem B1260157 : Blo 183802 1260157 := bstep (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) B472559
theorem B5683877 : Blo 183802 5683877 := bstep (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) B1065727
theorem B277481 : Blo 183802 277481 := bstep (se 2 (by rfl) ⟨104055, by rfl⟩ : syracuseStep 277481 = 208111) B208111
theorem B277559 : Blo 183802 277559 := bstep (se 1 (by rfl) ⟨208169, by rfl⟩ : syracuseStep 277559 = 416339) B416339
theorem B278153 : Blo 183802 278153 := bstep (se 2 (by rfl) ⟨104307, by rfl⟩ : syracuseStep 278153 = 208615) B208615
theorem B1195721 : Blo 183802 1195721 := bstep (se 2 (by rfl) ⟨448395, by rfl⟩ : syracuseStep 1195721 = 896791) B896791
theorem B311323 : Blo 183802 311323 := bstep (se 1 (by rfl) ⟨233492, by rfl⟩ : syracuseStep 311323 = 466985) B466985
theorem B934415 : Blo 183802 934415 := bstep (se 1 (by rfl) ⟨700811, by rfl⟩ : syracuseStep 934415 = 1401623) B1401623
theorem B279131 : Blo 183802 279131 := bstep (se 1 (by rfl) ⟨209348, by rfl⟩ : syracuseStep 279131 = 418697) B418697
theorem B2671967 : Blo 183802 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B707069 : Blo 183802 707069 := bstep (se 3 (by rfl) ⟨132575, by rfl⟩ : syracuseStep 707069 = 265151) B265151
theorem B1854035 : Blo 183802 1854035 := bstep (se 1 (by rfl) ⟨1390526, by rfl⟩ : syracuseStep 1854035 = 2781053) B2781053
theorem B281471 : Blo 183802 281471 := bstep (se 1 (by rfl) ⟨211103, by rfl⟩ : syracuseStep 281471 = 422207) B422207
theorem B183935 : Blo 183802 183935 := bstep (se 1 (by rfl) ⟨137951, by rfl⟩ : syracuseStep 183935 = 275903) B275903
theorem B709021 : Blo 183802 709021 := bstep (se 3 (by rfl) ⟨132941, by rfl⟩ : syracuseStep 709021 = 265883) B265883
theorem B185087 : Blo 183802 185087 := bstep (se 1 (by rfl) ⟨138815, by rfl⟩ : syracuseStep 185087 = 277631) B277631
theorem B185215 : Blo 183802 185215 := bstep (se 1 (by rfl) ⟨138911, by rfl⟩ : syracuseStep 185215 = 277823) B277823
theorem B447713 : Blo 183802 447713 := bstep (se 2 (by rfl) ⟨167892, by rfl⟩ : syracuseStep 447713 = 335785) B335785
theorem B185855 : Blo 183802 185855 := bstep (se 1 (by rfl) ⟨139391, by rfl⟩ : syracuseStep 185855 = 278783) B278783
theorem B350543 : Blo 183802 350543 := bstep (se 1 (by rfl) ⟨262907, by rfl⟩ : syracuseStep 350543 = 525815) B525815
theorem B711271 : Blo 183802 711271 := bstep (se 1 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 711271 = 1066907) B1066907
theorem B3103535 : Blo 183802 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B4776407 : Blo 183802 4776407 := bstep (se 1 (by rfl) ⟨3582305, by rfl⟩ : syracuseStep 4776407 = 7164611) B7164611
theorem B1402109 : Blo 183802 1402109 := bstep (se 3 (by rfl) ⟨262895, by rfl⟩ : syracuseStep 1402109 = 525791) B525791
theorem B1009255 : Blo 183802 1009255 := bstep (se 1 (by rfl) ⟨756941, by rfl⟩ : syracuseStep 1009255 = 1513883) B1513883
theorem B911699 : Blo 183802 911699 := bstep (se 1 (by rfl) ⟨683774, by rfl⟩ : syracuseStep 911699 = 1367549) B1367549
theorem B420443 : Blo 183802 420443 := bstep (se 1 (by rfl) ⟨315332, by rfl⟩ : syracuseStep 420443 = 630665) B630665
theorem B682607 : Blo 183802 682607 := bstep (se 1 (by rfl) ⟨511955, by rfl⟩ : syracuseStep 682607 = 1023911) B1023911
theorem B355099 : Blo 183802 355099 := bstep (se 1 (by rfl) ⟨266324, by rfl⟩ : syracuseStep 355099 = 532649) B532649
theorem B2125217 : Blo 183802 2125217 := bstep (se 2 (by rfl) ⟨796956, by rfl⟩ : syracuseStep 2125217 = 1593913) B1593913
theorem B421883 : Blo 183802 421883 := bstep (se 1 (by rfl) ⟨316412, by rfl⟩ : syracuseStep 421883 = 632825) B632825
theorem B1405025 : Blo 183802 1405025 := bstep (se 2 (by rfl) ⟨526884, by rfl⟩ : syracuseStep 1405025 = 1053769) B1053769
theorem B422009 : Blo 183802 422009 := bstep (se 2 (by rfl) ⟨158253, by rfl⟩ : syracuseStep 422009 = 316507) B316507
theorem B7500377 : Blo 183802 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B1602251 : Blo 183802 1602251 := bstep (se 1 (by rfl) ⟨1201688, by rfl⟩ : syracuseStep 1602251 = 2403377) B2403377
theorem B948671 : Blo 183802 948671 := bstep (se 1 (by rfl) ⟨711503, by rfl⟩ : syracuseStep 948671 = 1423007) B1423007
theorem B1179035 : Blo 183802 1179035 := bstep (se 1 (by rfl) ⟨884276, by rfl⟩ : syracuseStep 1179035 = 1768553) B1768553
theorem B393311 : Blo 183802 393311 := bstep (se 1 (by rfl) ⟨294983, by rfl⟩ : syracuseStep 393311 = 589967) B589967
theorem B622781 : Blo 183802 622781 := bstep (se 3 (by rfl) ⟨116771, by rfl⟩ : syracuseStep 622781 = 233543) B233543
theorem B622943 : Blo 183802 622943 := bstep (se 1 (by rfl) ⟨467207, by rfl⟩ : syracuseStep 622943 = 934415) B934415
theorem B2360015 : Blo 183802 2360015 := bstep (se 1 (by rfl) ⟨1770011, by rfl⟩ : syracuseStep 2360015 = 3540023) B3540023
theorem B526247 : Blo 183802 526247 := bstep (se 1 (by rfl) ⟨394685, by rfl⟩ : syracuseStep 526247 = 789371) B789371
theorem B1345673 : Blo 183802 1345673 := bstep (se 2 (by rfl) ⟨504627, by rfl⟩ : syracuseStep 1345673 = 1009255) B1009255
theorem B1051127 : Blo 183802 1051127 := bstep (se 1 (by rfl) ⟨788345, by rfl⟩ : syracuseStep 1051127 = 1576691) B1576691
theorem B298475 : Blo 183802 298475 := bstep (se 1 (by rfl) ⟨223856, by rfl⟩ : syracuseStep 298475 = 447713) B447713
theorem B233695 : Blo 183802 233695 := bstep (se 1 (by rfl) ⟨175271, by rfl⟩ : syracuseStep 233695 = 350543) B350543
theorem B2069023 : Blo 183802 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B4723919 : Blo 183802 4723919 := bstep (se 1 (by rfl) ⟨3542939, by rfl⟩ : syracuseStep 4723919 = 7085879) B7085879
theorem B3184271 : Blo 183802 3184271 := bstep (se 1 (by rfl) ⟨2388203, by rfl⟩ : syracuseStep 3184271 = 4776407) B4776407
theorem B1416811 : Blo 183802 1416811 := bstep (se 1 (by rfl) ⟨1062608, by rfl⟩ : syracuseStep 1416811 = 2125217) B2125217
theorem B1056959 : Blo 183802 1056959 := bstep (se 1 (by rfl) ⟨792719, by rfl⟩ : syracuseStep 1056959 = 1585439) B1585439
theorem B1680209 : Blo 183802 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B632447 : Blo 183802 632447 := bstep (se 1 (by rfl) ⟨474335, by rfl⟩ : syracuseStep 632447 = 948671) B948671
theorem B797147 : Blo 183802 797147 := bstep (se 1 (by rfl) ⟨597860, by rfl⟩ : syracuseStep 797147 = 1195721) B1195721
theorem B798461 : Blo 183802 798461 := bstep (se 3 (by rfl) ⟨149711, by rfl⟩ : syracuseStep 798461 = 299423) B299423
theorem B20001005 : Blo 183802 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B471379 : Blo 183802 471379 := bstep (se 1 (by rfl) ⟨353534, by rfl⟩ : syracuseStep 471379 = 707069) B707069
theorem B701723 : Blo 183802 701723 := bstep (se 1 (by rfl) ⟨526292, by rfl⟩ : syracuseStep 701723 = 1052585) B1052585
theorem B3585383 : Blo 183802 3585383 := bstep (se 1 (by rfl) ⟨2689037, by rfl⟩ : syracuseStep 3585383 = 5378075) B5378075
theorem B7125245 : Blo 183802 7125245 := bstep (se 3 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 7125245 = 2671967) B2671967
theorem B473465 : Blo 183802 473465 := bstep (se 2 (by rfl) ⟨177549, by rfl⟩ : syracuseStep 473465 = 355099) B355099
theorem B934739 : Blo 183802 934739 := bstep (se 1 (by rfl) ⟨701054, by rfl⟩ : syracuseStep 934739 = 1402109) B1402109
theorem B46613717 : Blo 183802 46613717 := bstep (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) B1092509
theorem B6473171 : Blo 183802 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B607799 : Blo 183802 607799 := bstep (se 1 (by rfl) ⟨455849, by rfl⟩ : syracuseStep 607799 = 911699) B911699
theorem B706279 : Blo 183802 706279 := bstep (se 1 (by rfl) ⟨529709, by rfl⟩ : syracuseStep 706279 = 1059419) B1059419
theorem B280295 : Blo 183802 280295 := bstep (se 1 (by rfl) ⟨210221, by rfl⟩ : syracuseStep 280295 = 420443) B420443
theorem B707039 : Blo 183802 707039 := bstep (se 1 (by rfl) ⟨530279, by rfl⟩ : syracuseStep 707039 = 1060559) B1060559
theorem B281255 : Blo 183802 281255 := bstep (se 1 (by rfl) ⟨210941, by rfl⟩ : syracuseStep 281255 = 421883) B421883
theorem B936683 : Blo 183802 936683 := bstep (se 1 (by rfl) ⟨702512, by rfl⟩ : syracuseStep 936683 = 1405025) B1405025
theorem B281339 : Blo 183802 281339 := bstep (se 1 (by rfl) ⟨211004, by rfl⟩ : syracuseStep 281339 = 422009) B422009
theorem B1068167 : Blo 183802 1068167 := bstep (se 1 (by rfl) ⟨801125, by rfl⟩ : syracuseStep 1068167 = 1602251) B1602251
theorem B184095 : Blo 183802 184095 := bstep (se 1 (by rfl) ⟨138071, by rfl⟩ : syracuseStep 184095 = 276143) B276143
theorem B184479 : Blo 183802 184479 := bstep (se 1 (by rfl) ⟨138359, by rfl⟩ : syracuseStep 184479 = 276719) B276719
theorem B3789251 : Blo 183802 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B184987 : Blo 183802 184987 := bstep (se 1 (by rfl) ⟨138740, by rfl⟩ : syracuseStep 184987 = 277481) B277481
theorem B185039 : Blo 183802 185039 := bstep (se 1 (by rfl) ⟨138779, by rfl⟩ : syracuseStep 185039 = 277559) B277559
theorem B185435 : Blo 183802 185435 := bstep (se 1 (by rfl) ⟨139076, by rfl⟩ : syracuseStep 185435 = 278153) B278153
theorem B415097 : Blo 183802 415097 := bstep (se 2 (by rfl) ⟨155661, by rfl⟩ : syracuseStep 415097 = 311323) B311323
theorem B186087 : Blo 183802 186087 := bstep (se 1 (by rfl) ⟨139565, by rfl⟩ : syracuseStep 186087 = 279131) B279131
theorem B1236023 : Blo 183802 1236023 := bstep (se 1 (by rfl) ⟨927017, by rfl⟩ : syracuseStep 1236023 = 1854035) B1854035
theorem B187647 : Blo 183802 187647 := bstep (se 1 (by rfl) ⟨140735, by rfl⟩ : syracuseStep 187647 = 281471) B281471
theorem B417959 : Blo 183802 417959 := bstep (se 1 (by rfl) ⟨313469, by rfl⟩ : syracuseStep 417959 = 626939) B626939
theorem B418031 : Blo 183802 418031 := bstep (se 1 (by rfl) ⟨313523, by rfl⟩ : syracuseStep 418031 = 627047) B627047
theorem B419903 : Blo 183802 419903 := bstep (se 1 (by rfl) ⟨314927, by rfl⟩ : syracuseStep 419903 = 629855) B629855
theorem B355175 : Blo 183802 355175 := bstep (se 1 (by rfl) ⟨266381, by rfl⟩ : syracuseStep 355175 = 532763) B532763
theorem B945361 : Blo 183802 945361 := bstep (se 2 (by rfl) ⟨354510, by rfl⟩ : syracuseStep 945361 = 709021) B709021
theorem B10187167 : Blo 183802 10187167 := bstep (se 1 (by rfl) ⟨7640375, by rfl⟩ : syracuseStep 10187167 = 15280751) B15280751
theorem B455071 : Blo 183802 455071 := bstep (se 1 (by rfl) ⟨341303, by rfl⟩ : syracuseStep 455071 = 682607) B682607
theorem B751607 : Blo 183802 751607 := bstep (se 1 (by rfl) ⟨563705, by rfl⟩ : syracuseStep 751607 = 1127411) B1127411
theorem B948361 : Blo 183802 948361 := bstep (se 2 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 948361 = 711271) B711271
theorem B786023 : Blo 183802 786023 := bstep (se 1 (by rfl) ⟨589517, by rfl⟩ : syracuseStep 786023 = 1179035) B1179035
theorem B262207 : Blo 183802 262207 := bstep (se 1 (by rfl) ⟨196655, by rfl⟩ : syracuseStep 262207 = 393311) B393311
theorem B1573343 : Blo 183802 1573343 := bstep (se 1 (by rfl) ⟨1180007, by rfl⟩ : syracuseStep 1573343 = 2360015) B2360015
theorem B623159 : Blo 183802 623159 := bstep (se 1 (by rfl) ⟨467369, by rfl⟩ : syracuseStep 623159 = 934739) B934739
theorem B624455 : Blo 183802 624455 := bstep (se 1 (by rfl) ⟨468341, by rfl⟩ : syracuseStep 624455 = 936683) B936683
theorem B198983 : Blo 183802 198983 := bstep (se 1 (by rfl) ⟨149237, by rfl⟩ : syracuseStep 198983 = 298475) B298475
theorem B2526167 : Blo 183802 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B3149279 : Blo 183802 3149279 := bstep (se 1 (by rfl) ⟨2361959, by rfl⟩ : syracuseStep 3149279 = 4723919) B4723919
theorem B824015 : Blo 183802 824015 := bstep (se 1 (by rfl) ⟨618011, by rfl⟩ : syracuseStep 824015 = 1236023) B1236023
theorem B628505 : Blo 183802 628505 := bstep (se 2 (by rfl) ⟨235689, by rfl⟩ : syracuseStep 628505 = 471379) B471379
theorem B1120139 : Blo 183802 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B2758697 : Blo 183802 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B531431 : Blo 183802 531431 := bstep (se 1 (by rfl) ⟨398573, by rfl⟩ : syracuseStep 531431 = 797147) B797147
theorem B236783 : Blo 183802 236783 := bstep (se 1 (by rfl) ⟨177587, by rfl⟩ : syracuseStep 236783 = 355175) B355175
theorem B532307 : Blo 183802 532307 := bstep (se 1 (by rfl) ⟨399230, by rfl⟩ : syracuseStep 532307 = 798461) B798461
theorem B467815 : Blo 183802 467815 := bstep (se 1 (by rfl) ⟨350861, by rfl⟩ : syracuseStep 467815 = 701723) B701723
theorem B501071 : Blo 183802 501071 := bstep (se 1 (by rfl) ⟨375803, by rfl⟩ : syracuseStep 501071 = 751607) B751607
theorem B31075811 : Blo 183802 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B405199 : Blo 183802 405199 := bstep (se 1 (by rfl) ⟨303899, by rfl⟩ : syracuseStep 405199 = 607799) B607799
theorem B897115 : Blo 183802 897115 := bstep (se 1 (by rfl) ⟨672836, by rfl⟩ : syracuseStep 897115 = 1345673) B1345673
theorem B471359 : Blo 183802 471359 := bstep (se 1 (by rfl) ⟨353519, by rfl⟩ : syracuseStep 471359 = 707039) B707039
theorem B700751 : Blo 183802 700751 := bstep (se 1 (by rfl) ⟨525563, by rfl⟩ : syracuseStep 700751 = 1051127) B1051127
theorem B276731 : Blo 183802 276731 := bstep (se 1 (by rfl) ⟨207548, by rfl⟩ : syracuseStep 276731 = 415097) B415097
theorem B278639 : Blo 183802 278639 := bstep (se 1 (by rfl) ⟨208979, by rfl⟩ : syracuseStep 278639 = 417959) B417959
theorem B704639 : Blo 183802 704639 := bstep (se 1 (by rfl) ⟨528479, by rfl⟩ : syracuseStep 704639 = 1056959) B1056959
theorem B278687 : Blo 183802 278687 := bstep (se 1 (by rfl) ⟨209015, by rfl⟩ : syracuseStep 278687 = 418031) B418031
theorem B311593 : Blo 183802 311593 := bstep (se 2 (by rfl) ⟨116847, by rfl⟩ : syracuseStep 311593 = 233695) B233695
theorem B13582889 : Blo 183802 13582889 := bstep (se 2 (by rfl) ⟨5093583, by rfl⟩ : syracuseStep 13582889 = 10187167) B10187167
theorem B606761 : Blo 183802 606761 := bstep (se 2 (by rfl) ⟨227535, by rfl⟩ : syracuseStep 606761 = 455071) B455071
theorem B279935 : Blo 183802 279935 := bstep (se 1 (by rfl) ⟨209951, by rfl⟩ : syracuseStep 279935 = 419903) B419903
theorem B1264481 : Blo 183802 1264481 := bstep (se 2 (by rfl) ⟨474180, by rfl⟩ : syracuseStep 1264481 = 948361) B948361
theorem B315643 : Blo 183802 315643 := bstep (se 1 (by rfl) ⟨236732, by rfl⟩ : syracuseStep 315643 = 473465) B473465
theorem B1889081 : Blo 183802 1889081 := bstep (se 2 (by rfl) ⟨708405, by rfl⟩ : syracuseStep 1889081 = 1416811) B1416811
theorem B415187 : Blo 183802 415187 := bstep (se 1 (by rfl) ⟨311390, by rfl⟩ : syracuseStep 415187 = 622781) B622781
theorem B415295 : Blo 183802 415295 := bstep (se 1 (by rfl) ⟨311471, by rfl⟩ : syracuseStep 415295 = 622943) B622943
theorem B4315447 : Blo 183802 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B186863 : Blo 183802 186863 := bstep (se 1 (by rfl) ⟨140147, by rfl⟩ : syracuseStep 186863 = 280295) B280295
theorem B350831 : Blo 183802 350831 := bstep (se 1 (by rfl) ⟨263123, by rfl⟩ : syracuseStep 350831 = 526247) B526247
theorem B187503 : Blo 183802 187503 := bstep (se 1 (by rfl) ⟨140627, by rfl⟩ : syracuseStep 187503 = 281255) B281255
theorem B187559 : Blo 183802 187559 := bstep (se 1 (by rfl) ⟨140669, by rfl⟩ : syracuseStep 187559 = 281339) B281339
theorem B712111 : Blo 183802 712111 := bstep (se 1 (by rfl) ⟨534083, by rfl⟩ : syracuseStep 712111 = 1068167) B1068167
theorem B941705 : Blo 183802 941705 := bstep (se 2 (by rfl) ⟨353139, by rfl⟩ : syracuseStep 941705 = 706279) B706279
theorem B2122847 : Blo 183802 2122847 := bstep (se 1 (by rfl) ⟨1592135, by rfl⟩ : syracuseStep 2122847 = 3184271) B3184271
theorem B421631 : Blo 183802 421631 := bstep (se 1 (by rfl) ⟨316223, by rfl⟩ : syracuseStep 421631 = 632447) B632447
theorem B5041925 : Blo 183802 5041925 := bstep (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) B945361
theorem B13334003 : Blo 183802 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B2390255 : Blo 183802 2390255 := bstep (se 1 (by rfl) ⟨1792691, by rfl⟩ : syracuseStep 2390255 = 3585383) B3585383
theorem B4750163 : Blo 183802 4750163 := bstep (se 1 (by rfl) ⟨3562622, by rfl⟩ : syracuseStep 4750163 = 7125245) B7125245
theorem B524015 : Blo 183802 524015 := bstep (se 1 (by rfl) ⟨393011, by rfl⟩ : syracuseStep 524015 = 786023) B786023
theorem B1048895 : Blo 183802 1048895 := bstep (se 1 (by rfl) ⟨786671, by rfl⟩ : syracuseStep 1048895 = 1573343) B1573343
theorem B623753 : Blo 183802 623753 := bstep (se 2 (by rfl) ⟨233907, by rfl⟩ : syracuseStep 623753 = 467815) B467815
theorem B2099519 : Blo 183802 2099519 := bstep (se 1 (by rfl) ⟨1574639, by rfl⟩ : syracuseStep 2099519 = 3149279) B3149279
theorem B1839131 : Blo 183802 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B627803 : Blo 183802 627803 := bstep (se 1 (by rfl) ⟨470852, by rfl⟩ : syracuseStep 627803 = 941705) B941705
theorem B1415231 : Blo 183802 1415231 := bstep (se 1 (by rfl) ⟨1061423, by rfl⟩ : syracuseStep 1415231 = 2122847) B2122847
theorem B530621 : Blo 183802 530621 := bstep (se 3 (by rfl) ⟨99491, by rfl⟩ : syracuseStep 530621 = 198983) B198983
theorem B20717207 : Blo 183802 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B467167 : Blo 183802 467167 := bstep (se 1 (by rfl) ⟨350375, by rfl⟩ : syracuseStep 467167 = 700751) B700751
theorem B631421 : Blo 183802 631421 := bstep (se 3 (by rfl) ⟨118391, by rfl⟩ : syracuseStep 631421 = 236783) B236783
theorem B8889335 : Blo 183802 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B469759 : Blo 183802 469759 := bstep (se 1 (by rfl) ⟨352319, by rfl⟩ : syracuseStep 469759 = 704639) B704639
theorem B9055259 : Blo 183802 9055259 := bstep (se 1 (by rfl) ⟨6791444, by rfl⟩ : syracuseStep 9055259 = 13582889) B13582889
theorem B404507 : Blo 183802 404507 := bstep (se 1 (by rfl) ⟨303380, by rfl⟩ : syracuseStep 404507 = 606761) B606761
theorem B1684111 : Blo 183802 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B1259387 : Blo 183802 1259387 := bstep (se 1 (by rfl) ⟨944540, by rfl⟩ : syracuseStep 1259387 = 1889081) B1889081
theorem B276791 : Blo 183802 276791 := bstep (se 1 (by rfl) ⟨207593, by rfl⟩ : syracuseStep 276791 = 415187) B415187
theorem B276863 : Blo 183802 276863 := bstep (se 1 (by rfl) ⟨207647, by rfl⟩ : syracuseStep 276863 = 415295) B415295
theorem B540265 : Blo 183802 540265 := bstep (se 2 (by rfl) ⟨202599, by rfl⟩ : syracuseStep 540265 = 405199) B405199
theorem B1196153 : Blo 183802 1196153 := bstep (se 2 (by rfl) ⟨448557, by rfl⟩ : syracuseStep 1196153 = 897115) B897115
theorem B935549 : Blo 183802 935549 := bstep (se 3 (by rfl) ⟨175415, by rfl⟩ : syracuseStep 935549 = 350831) B350831
theorem B281087 : Blo 183802 281087 := bstep (se 1 (by rfl) ⟨210815, by rfl⟩ : syracuseStep 281087 = 421631) B421631
theorem B3361283 : Blo 183802 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B314239 : Blo 183802 314239 := bstep (se 1 (by rfl) ⟨235679, by rfl⟩ : syracuseStep 314239 = 471359) B471359
theorem B5753929 : Blo 183802 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B1593503 : Blo 183802 1593503 := bstep (se 1 (by rfl) ⟨1195127, by rfl⟩ : syracuseStep 1593503 = 2390255) B2390255
theorem B184487 : Blo 183802 184487 := bstep (se 1 (by rfl) ⟨138365, by rfl⟩ : syracuseStep 184487 = 276731) B276731
theorem B3166775 : Blo 183802 3166775 := bstep (se 1 (by rfl) ⟨2375081, by rfl⟩ : syracuseStep 3166775 = 4750163) B4750163
theorem B349343 : Blo 183802 349343 := bstep (se 1 (by rfl) ⟨262007, by rfl⟩ : syracuseStep 349343 = 524015) B524015
theorem B185759 : Blo 183802 185759 := bstep (se 1 (by rfl) ⟨139319, by rfl⟩ : syracuseStep 185759 = 278639) B278639
theorem B349609 : Blo 183802 349609 := bstep (se 2 (by rfl) ⟨131103, by rfl⟩ : syracuseStep 349609 = 262207) B262207
theorem B185791 : Blo 183802 185791 := bstep (se 1 (by rfl) ⟨139343, by rfl⟩ : syracuseStep 185791 = 278687) B278687
theorem B415439 : Blo 183802 415439 := bstep (se 1 (by rfl) ⟨311579, by rfl⟩ : syracuseStep 415439 = 623159) B623159
theorem B415457 : Blo 183802 415457 := bstep (se 2 (by rfl) ⟨155796, by rfl⟩ : syracuseStep 415457 = 311593) B311593
theorem B186623 : Blo 183802 186623 := bstep (se 1 (by rfl) ⟨139967, by rfl⟩ : syracuseStep 186623 = 279935) B279935
theorem B416303 : Blo 183802 416303 := bstep (se 1 (by rfl) ⟨312227, by rfl⟩ : syracuseStep 416303 = 624455) B624455
theorem B842987 : Blo 183802 842987 := bstep (se 1 (by rfl) ⟨632240, by rfl⟩ : syracuseStep 842987 = 1264481) B1264481
theorem B549343 : Blo 183802 549343 := bstep (se 1 (by rfl) ⟨412007, by rfl⟩ : syracuseStep 549343 = 824015) B824015
theorem B1336189 : Blo 183802 1336189 := bstep (se 3 (by rfl) ⟨250535, by rfl⟩ : syracuseStep 1336189 = 501071) B501071
theorem B419003 : Blo 183802 419003 := bstep (se 1 (by rfl) ⟨314252, by rfl⟩ : syracuseStep 419003 = 628505) B628505
theorem B746759 : Blo 183802 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B354287 : Blo 183802 354287 := bstep (se 1 (by rfl) ⟨265715, by rfl⟩ : syracuseStep 354287 = 531431) B531431
theorem B354871 : Blo 183802 354871 := bstep (se 1 (by rfl) ⟨266153, by rfl⟩ : syracuseStep 354871 = 532307) B532307
theorem B420857 : Blo 183802 420857 := bstep (se 2 (by rfl) ⟨157821, by rfl⟩ : syracuseStep 420857 = 315643) B315643
theorem B949481 : Blo 183802 949481 := bstep (se 2 (by rfl) ⟨356055, by rfl⟩ : syracuseStep 949481 = 712111) B712111
theorem B622889 : Blo 183802 622889 := bstep (se 2 (by rfl) ⟨233583, by rfl⟩ : syracuseStep 622889 = 467167) B467167
theorem B623699 : Blo 183802 623699 := bstep (se 1 (by rfl) ⟨467774, by rfl⟩ : syracuseStep 623699 = 935549) B935549
theorem B232895 : Blo 183802 232895 := bstep (se 1 (by rfl) ⟨174671, by rfl⟩ : syracuseStep 232895 = 349343) B349343
theorem B626345 : Blo 183802 626345 := bstep (se 2 (by rfl) ⟨234879, by rfl⟩ : syracuseStep 626345 = 469759) B469759
theorem B7671905 : Blo 183802 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B561991 : Blo 183802 561991 := bstep (se 1 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 561991 = 842987) B842987
theorem B497839 : Blo 183802 497839 := bstep (se 1 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 497839 = 746759) B746759
theorem B236191 : Blo 183802 236191 := bstep (se 1 (by rfl) ⟨177143, by rfl⟩ : syracuseStep 236191 = 354287) B354287
theorem B466145 : Blo 183802 466145 := bstep (se 2 (by rfl) ⟨174804, by rfl⟩ : syracuseStep 466145 = 349609) B349609
theorem B6036839 : Blo 183802 6036839 := bstep (se 1 (by rfl) ⟨4527629, by rfl⟩ : syracuseStep 6036839 = 9055259) B9055259
theorem B269671 : Blo 183802 269671 := bstep (se 1 (by rfl) ⟨202253, by rfl⟩ : syracuseStep 269671 = 404507) B404507
theorem B632987 : Blo 183802 632987 := bstep (se 1 (by rfl) ⟨474740, by rfl⟩ : syracuseStep 632987 = 949481) B949481
theorem B797435 : Blo 183802 797435 := bstep (se 1 (by rfl) ⟨598076, by rfl⟩ : syracuseStep 797435 = 1196153) B1196153
theorem B699263 : Blo 183802 699263 := bstep (se 1 (by rfl) ⟨524447, by rfl⟩ : syracuseStep 699263 = 1048895) B1048895
theorem B1781585 : Blo 183802 1781585 := bstep (se 2 (by rfl) ⟨668094, by rfl⟩ : syracuseStep 1781585 = 1336189) B1336189
theorem B2240855 : Blo 183802 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B2929829 : Blo 183802 2929829 := bstep (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) B549343
theorem B1226087 : Blo 183802 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B1062335 : Blo 183802 1062335 := bstep (se 1 (by rfl) ⟨796751, by rfl⟩ : syracuseStep 1062335 = 1593503) B1593503
theorem B2111183 : Blo 183802 2111183 := bstep (se 1 (by rfl) ⟨1583387, by rfl⟩ : syracuseStep 2111183 = 3166775) B3166775
theorem B473161 : Blo 183802 473161 := bstep (se 2 (by rfl) ⟨177435, by rfl⟩ : syracuseStep 473161 = 354871) B354871
theorem B276959 : Blo 183802 276959 := bstep (se 1 (by rfl) ⟨207719, by rfl⟩ : syracuseStep 276959 = 415439) B415439
theorem B276971 : Blo 183802 276971 := bstep (se 1 (by rfl) ⟨207728, by rfl⟩ : syracuseStep 276971 = 415457) B415457
theorem B277535 : Blo 183802 277535 := bstep (se 1 (by rfl) ⟨208151, by rfl⟩ : syracuseStep 277535 = 416303) B416303
theorem B13811471 : Blo 183802 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B279335 : Blo 183802 279335 := bstep (se 1 (by rfl) ⟨209501, by rfl⟩ : syracuseStep 279335 = 419003) B419003
theorem B2245481 : Blo 183802 2245481 := bstep (se 2 (by rfl) ⟨842055, by rfl⟩ : syracuseStep 2245481 = 1684111) B1684111
theorem B280571 : Blo 183802 280571 := bstep (se 1 (by rfl) ⟨210428, by rfl⟩ : syracuseStep 280571 = 420857) B420857
theorem B839591 : Blo 183802 839591 := bstep (se 1 (by rfl) ⟨629693, by rfl⟩ : syracuseStep 839591 = 1259387) B1259387
theorem B184527 : Blo 183802 184527 := bstep (se 1 (by rfl) ⟨138395, by rfl⟩ : syracuseStep 184527 = 276791) B276791
theorem B184575 : Blo 183802 184575 := bstep (se 1 (by rfl) ⟨138431, by rfl⟩ : syracuseStep 184575 = 276863) B276863
theorem B415835 : Blo 183802 415835 := bstep (se 1 (by rfl) ⟨311876, by rfl⟩ : syracuseStep 415835 = 623753) B623753
theorem B1399679 : Blo 183802 1399679 := bstep (se 1 (by rfl) ⟨1049759, by rfl⟩ : syracuseStep 1399679 = 2099519) B2099519
theorem B187391 : Blo 183802 187391 := bstep (se 1 (by rfl) ⟨140543, by rfl⟩ : syracuseStep 187391 = 281087) B281087
theorem B418535 : Blo 183802 418535 := bstep (se 1 (by rfl) ⟨313901, by rfl⟩ : syracuseStep 418535 = 627803) B627803
theorem B418985 : Blo 183802 418985 := bstep (se 2 (by rfl) ⟨157119, by rfl⟩ : syracuseStep 418985 = 314239) B314239
theorem B943487 : Blo 183802 943487 := bstep (se 1 (by rfl) ⟨707615, by rfl⟩ : syracuseStep 943487 = 1415231) B1415231
theorem B353747 : Blo 183802 353747 := bstep (se 1 (by rfl) ⟨265310, by rfl⟩ : syracuseStep 353747 = 530621) B530621
theorem B420947 : Blo 183802 420947 := bstep (se 1 (by rfl) ⟨315710, by rfl⟩ : syracuseStep 420947 = 631421) B631421
theorem B5926223 : Blo 183802 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B720353 : Blo 183802 720353 := bstep (se 2 (by rfl) ⟨270132, by rfl⟩ : syracuseStep 720353 = 540265) B540265
theorem B559727 : Blo 183802 559727 := bstep (se 1 (by rfl) ⟨419795, by rfl⟩ : syracuseStep 559727 = 839591) B839591
theorem B5114603 : Blo 183802 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B628991 : Blo 183802 628991 := bstep (se 1 (by rfl) ⟨471743, by rfl⟩ : syracuseStep 628991 = 943487) B943487
theorem B531623 : Blo 183802 531623 := bstep (se 1 (by rfl) ⟨398717, by rfl⟩ : syracuseStep 531623 = 797435) B797435
theorem B466175 : Blo 183802 466175 := bstep (se 1 (by rfl) ⟨349631, by rfl⟩ : syracuseStep 466175 = 699263) B699263
theorem B1187723 : Blo 183802 1187723 := bstep (se 1 (by rfl) ⟨890792, by rfl⟩ : syracuseStep 1187723 = 1781585) B1781585
theorem B630881 : Blo 183802 630881 := bstep (se 2 (by rfl) ⟨236580, by rfl⟩ : syracuseStep 630881 = 473161) B473161
theorem B663785 : Blo 183802 663785 := bstep (se 2 (by rfl) ⟨248919, by rfl⟩ : syracuseStep 663785 = 497839) B497839
theorem B7812877 : Blo 183802 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B277223 : Blo 183802 277223 := bstep (se 1 (by rfl) ⟨207917, by rfl⟩ : syracuseStep 277223 = 415835) B415835
theorem B933119 : Blo 183802 933119 := bstep (se 1 (by rfl) ⟨699839, by rfl⟩ : syracuseStep 933119 = 1399679) B1399679
theorem B310763 : Blo 183802 310763 := bstep (se 1 (by rfl) ⟨233072, by rfl⟩ : syracuseStep 310763 = 466145) B466145
theorem B279023 : Blo 183802 279023 := bstep (se 1 (by rfl) ⟨209267, by rfl⟩ : syracuseStep 279023 = 418535) B418535
theorem B279323 : Blo 183802 279323 := bstep (se 1 (by rfl) ⟨209492, by rfl⟩ : syracuseStep 279323 = 418985) B418985
theorem B280631 : Blo 183802 280631 := bstep (se 1 (by rfl) ⟨210473, by rfl⟩ : syracuseStep 280631 = 420947) B420947
theorem B3950815 : Blo 183802 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B1493903 : Blo 183802 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B314921 : Blo 183802 314921 := bstep (se 2 (by rfl) ⟨118095, by rfl⟩ : syracuseStep 314921 = 236191) B236191
theorem B708223 : Blo 183802 708223 := bstep (se 1 (by rfl) ⟨531167, by rfl⟩ : syracuseStep 708223 = 1062335) B1062335
theorem B184639 : Blo 183802 184639 := bstep (se 1 (by rfl) ⟨138479, by rfl⟩ : syracuseStep 184639 = 276959) B276959
theorem B184647 : Blo 183802 184647 := bstep (se 1 (by rfl) ⟨138485, by rfl⟩ : syracuseStep 184647 = 276971) B276971
theorem B185023 : Blo 183802 185023 := bstep (se 1 (by rfl) ⟨138767, by rfl⟩ : syracuseStep 185023 = 277535) B277535
theorem B480235 : Blo 183802 480235 := bstep (se 1 (by rfl) ⟨360176, by rfl⟩ : syracuseStep 480235 = 720353) B720353
theorem B415259 : Blo 183802 415259 := bstep (se 1 (by rfl) ⟨311444, by rfl⟩ : syracuseStep 415259 = 622889) B622889
theorem B186223 : Blo 183802 186223 := bstep (se 1 (by rfl) ⟨139667, by rfl⟩ : syracuseStep 186223 = 279335) B279335
theorem B1496987 : Blo 183802 1496987 := bstep (se 1 (by rfl) ⟨1122740, by rfl⟩ : syracuseStep 1496987 = 2245481) B2245481
theorem B415799 : Blo 183802 415799 := bstep (se 1 (by rfl) ⟨311849, by rfl⟩ : syracuseStep 415799 = 623699) B623699
theorem B187047 : Blo 183802 187047 := bstep (se 1 (by rfl) ⟨140285, by rfl⟩ : syracuseStep 187047 = 280571) B280571
theorem B417563 : Blo 183802 417563 := bstep (se 1 (by rfl) ⟨313172, by rfl⟩ : syracuseStep 417563 = 626345) B626345
theorem B943325 : Blo 183802 943325 := bstep (se 3 (by rfl) ⟨176873, by rfl⟩ : syracuseStep 943325 = 353747) B353747
theorem B4024559 : Blo 183802 4024559 := bstep (se 1 (by rfl) ⟨3018419, by rfl⟩ : syracuseStep 4024559 = 6036839) B6036839
theorem B749321 : Blo 183802 749321 := bstep (se 2 (by rfl) ⟨280995, by rfl⟩ : syracuseStep 749321 = 561991) B561991
theorem B421991 : Blo 183802 421991 := bstep (se 1 (by rfl) ⟨316493, by rfl⟩ : syracuseStep 421991 = 632987) B632987
theorem B817391 : Blo 183802 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B1407455 : Blo 183802 1407455 := bstep (se 1 (by rfl) ⟨1055591, by rfl⟩ : syracuseStep 1407455 = 2111183) B2111183
theorem B621053 : Blo 183802 621053 := bstep (se 3 (by rfl) ⟨116447, by rfl⟩ : syracuseStep 621053 = 232895) B232895
theorem B359561 : Blo 183802 359561 := bstep (se 2 (by rfl) ⟨134835, by rfl⟩ : syracuseStep 359561 = 269671) B269671
theorem B9207647 : Blo 183802 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B3409735 : Blo 183802 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B791815 : Blo 183802 791815 := bstep (se 1 (by rfl) ⟨593861, by rfl⟩ : syracuseStep 791815 = 1187723) B1187723
theorem B628883 : Blo 183802 628883 := bstep (se 1 (by rfl) ⟨471662, by rfl⟩ : syracuseStep 628883 = 943325) B943325
theorem B499547 : Blo 183802 499547 := bstep (se 1 (by rfl) ⟨374660, by rfl⟩ : syracuseStep 499547 = 749321) B749321
theorem B1417661 : Blo 183802 1417661 := bstep (se 3 (by rfl) ⟨265811, by rfl⟩ : syracuseStep 1417661 = 531623) B531623
theorem B239707 : Blo 183802 239707 := bstep (se 1 (by rfl) ⟨179780, by rfl⟩ : syracuseStep 239707 = 359561) B359561
theorem B207175 : Blo 183802 207175 := bstep (se 1 (by rfl) ⟨155381, by rfl⟩ : syracuseStep 207175 = 310763) B310763
theorem B6138431 : Blo 183802 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B373151 : Blo 183802 373151 := bstep (se 1 (by rfl) ⟨279863, by rfl⟩ : syracuseStep 373151 = 559727) B559727
theorem B995935 : Blo 183802 995935 := bstep (se 1 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 995935 = 1493903) B1493903
theorem B209947 : Blo 183802 209947 := bstep (se 1 (by rfl) ⟨157460, by rfl⟩ : syracuseStep 209947 = 314921) B314921
theorem B276839 : Blo 183802 276839 := bstep (se 1 (by rfl) ⟨207629, by rfl⟩ : syracuseStep 276839 = 415259) B415259
theorem B997991 : Blo 183802 997991 := bstep (se 1 (by rfl) ⟨748493, by rfl⟩ : syracuseStep 997991 = 1496987) B1496987
theorem B277199 : Blo 183802 277199 := bstep (se 1 (by rfl) ⟨207899, by rfl⟩ : syracuseStep 277199 = 415799) B415799
theorem B310783 : Blo 183802 310783 := bstep (se 1 (by rfl) ⟨233087, by rfl⟩ : syracuseStep 310783 = 466175) B466175
theorem B278375 : Blo 183802 278375 := bstep (se 1 (by rfl) ⟨208781, by rfl⟩ : syracuseStep 278375 = 417563) B417563
theorem B442523 : Blo 183802 442523 := bstep (se 1 (by rfl) ⟨331892, by rfl⟩ : syracuseStep 442523 = 663785) B663785
theorem B2179709 : Blo 183802 2179709 := bstep (se 3 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 2179709 = 817391) B817391
theorem B640313 : Blo 183802 640313 := bstep (se 2 (by rfl) ⟨240117, by rfl⟩ : syracuseStep 640313 = 480235) B480235
theorem B281327 : Blo 183802 281327 := bstep (se 1 (by rfl) ⟨210995, by rfl⟩ : syracuseStep 281327 = 421991) B421991
theorem B938303 : Blo 183802 938303 := bstep (se 1 (by rfl) ⟨703727, by rfl⟩ : syracuseStep 938303 = 1407455) B1407455
theorem B414035 : Blo 183802 414035 := bstep (se 1 (by rfl) ⟨310526, by rfl⟩ : syracuseStep 414035 = 621053) B621053
theorem B184815 : Blo 183802 184815 := bstep (se 1 (by rfl) ⟨138611, by rfl⟩ : syracuseStep 184815 = 277223) B277223
theorem B186015 : Blo 183802 186015 := bstep (se 1 (by rfl) ⟨139511, by rfl⟩ : syracuseStep 186015 = 279023) B279023
theorem B186215 : Blo 183802 186215 := bstep (se 1 (by rfl) ⟨139661, by rfl⟩ : syracuseStep 186215 = 279323) B279323
theorem B187087 : Blo 183802 187087 := bstep (se 1 (by rfl) ⟨140315, by rfl⟩ : syracuseStep 187087 = 280631) B280631
theorem B5267753 : Blo 183802 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B419327 : Blo 183802 419327 := bstep (se 1 (by rfl) ⟨314495, by rfl⟩ : syracuseStep 419327 = 628991) B628991
theorem B944297 : Blo 183802 944297 := bstep (se 2 (by rfl) ⟨354111, by rfl⟩ : syracuseStep 944297 = 708223) B708223
theorem B420587 : Blo 183802 420587 := bstep (se 1 (by rfl) ⟨315440, by rfl⟩ : syracuseStep 420587 = 630881) B630881
theorem B2683039 : Blo 183802 2683039 := bstep (se 1 (by rfl) ⟨2012279, by rfl⟩ : syracuseStep 2683039 = 4024559) B4024559
theorem B10417169 : Blo 183802 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B622079 : Blo 183802 622079 := bstep (se 1 (by rfl) ⟨466559, by rfl⟩ : syracuseStep 622079 = 933119) B933119
theorem B295015 : Blo 183802 295015 := bstep (se 1 (by rfl) ⟨221261, by rfl⟩ : syracuseStep 295015 = 442523) B442523
theorem B426875 : Blo 183802 426875 := bstep (se 1 (by rfl) ⟨320156, by rfl⟩ : syracuseStep 426875 = 640313) B640313
theorem B625535 : Blo 183802 625535 := bstep (se 1 (by rfl) ⟨469151, by rfl⟩ : syracuseStep 625535 = 938303) B938303
theorem B3511835 : Blo 183802 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B3577385 : Blo 183802 3577385 := bstep (se 2 (by rfl) ⟨1341519, by rfl⟩ : syracuseStep 3577385 = 2683039) B2683039
theorem B629531 : Blo 183802 629531 := bstep (se 1 (by rfl) ⟨472148, by rfl⟩ : syracuseStep 629531 = 944297) B944297
theorem B1055753 : Blo 183802 1055753 := bstep (se 2 (by rfl) ⟨395907, by rfl⟩ : syracuseStep 1055753 = 791815) B791815
theorem B665327 : Blo 183802 665327 := bstep (se 1 (by rfl) ⟨498995, by rfl⟩ : syracuseStep 665327 = 997991) B997991
theorem B1453139 : Blo 183802 1453139 := bstep (se 1 (by rfl) ⟨1089854, by rfl⟩ : syracuseStep 1453139 = 2179709) B2179709
theorem B276023 : Blo 183802 276023 := bstep (se 1 (by rfl) ⟨207017, by rfl⟩ : syracuseStep 276023 = 414035) B414035
theorem B276233 : Blo 183802 276233 := bstep (se 2 (by rfl) ⟨103587, by rfl⟩ : syracuseStep 276233 = 207175) B207175
theorem B1327913 : Blo 183802 1327913 := bstep (se 2 (by rfl) ⟨497967, by rfl⟩ : syracuseStep 1327913 = 995935) B995935
theorem B279551 : Blo 183802 279551 := bstep (se 1 (by rfl) ⟨209663, by rfl⟩ : syracuseStep 279551 = 419327) B419327
theorem B279929 : Blo 183802 279929 := bstep (se 2 (by rfl) ⟨104973, by rfl⟩ : syracuseStep 279929 = 209947) B209947
theorem B280391 : Blo 183802 280391 := bstep (se 1 (by rfl) ⟨210293, by rfl⟩ : syracuseStep 280391 = 420587) B420587
theorem B248767 : Blo 183802 248767 := bstep (se 1 (by rfl) ⟨186575, by rfl⟩ : syracuseStep 248767 = 373151) B373151
theorem B184559 : Blo 183802 184559 := bstep (se 1 (by rfl) ⟨138419, by rfl⟩ : syracuseStep 184559 = 276839) B276839
theorem B184799 : Blo 183802 184799 := bstep (se 1 (by rfl) ⟨138599, by rfl⟩ : syracuseStep 184799 = 277199) B277199
theorem B414377 : Blo 183802 414377 := bstep (se 2 (by rfl) ⟨155391, by rfl⟩ : syracuseStep 414377 = 310783) B310783
theorem B1332125 : Blo 183802 1332125 := bstep (se 3 (by rfl) ⟨249773, by rfl⟩ : syracuseStep 1332125 = 499547) B499547
theorem B414719 : Blo 183802 414719 := bstep (se 1 (by rfl) ⟨311039, by rfl⟩ : syracuseStep 414719 = 622079) B622079
theorem B185583 : Blo 183802 185583 := bstep (se 1 (by rfl) ⟨139187, by rfl⟩ : syracuseStep 185583 = 278375) B278375
theorem B187551 : Blo 183802 187551 := bstep (se 1 (by rfl) ⟨140663, by rfl⟩ : syracuseStep 187551 = 281327) B281327
theorem B4546313 : Blo 183802 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B319609 : Blo 183802 319609 := bstep (se 2 (by rfl) ⟨119853, by rfl⟩ : syracuseStep 319609 = 239707) B239707
theorem B419255 : Blo 183802 419255 := bstep (se 1 (by rfl) ⟨314441, by rfl⟩ : syracuseStep 419255 = 628883) B628883
theorem B945107 : Blo 183802 945107 := bstep (se 1 (by rfl) ⟨708830, by rfl⟩ : syracuseStep 945107 = 1417661) B1417661
theorem B4092287 : Blo 183802 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B6944779 : Blo 183802 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B393353 : Blo 183802 393353 := bstep (se 2 (by rfl) ⟨147507, by rfl⟩ : syracuseStep 393353 = 295015) B295015
theorem B426145 : Blo 183802 426145 := bstep (se 2 (by rfl) ⟨159804, by rfl⟩ : syracuseStep 426145 = 319609) B319609
theorem B885275 : Blo 183802 885275 := bstep (se 1 (by rfl) ⟨663956, by rfl⟩ : syracuseStep 885275 = 1327913) B1327913
theorem B10912765 : Blo 183802 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B888083 : Blo 183802 888083 := bstep (se 1 (by rfl) ⟨666062, by rfl⟩ : syracuseStep 888083 = 1332125) B1332125
theorem B630071 : Blo 183802 630071 := bstep (se 1 (by rfl) ⟨472553, by rfl⟩ : syracuseStep 630071 = 945107) B945107
theorem B276251 : Blo 183802 276251 := bstep (se 1 (by rfl) ⟨207188, by rfl⟩ : syracuseStep 276251 = 414377) B414377
theorem B276479 : Blo 183802 276479 := bstep (se 1 (by rfl) ⟨207359, by rfl⟩ : syracuseStep 276479 = 414719) B414719
theorem B2341223 : Blo 183802 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B703835 : Blo 183802 703835 := bstep (se 1 (by rfl) ⟨527876, by rfl⟩ : syracuseStep 703835 = 1055753) B1055753
theorem B3030875 : Blo 183802 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B279503 : Blo 183802 279503 := bstep (se 1 (by rfl) ⟨209627, by rfl⟩ : syracuseStep 279503 = 419255) B419255
theorem B443551 : Blo 183802 443551 := bstep (se 1 (by rfl) ⟨332663, by rfl⟩ : syracuseStep 443551 = 665327) B665327
theorem B968759 : Blo 183802 968759 := bstep (se 1 (by rfl) ⟨726569, by rfl⟩ : syracuseStep 968759 = 1453139) B1453139
theorem B9259705 : Blo 183802 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B184015 : Blo 183802 184015 := bstep (se 1 (by rfl) ⟨138011, by rfl⟩ : syracuseStep 184015 = 276023) B276023
theorem B184155 : Blo 183802 184155 := bstep (se 1 (by rfl) ⟨138116, by rfl⟩ : syracuseStep 184155 = 276233) B276233
theorem B186367 : Blo 183802 186367 := bstep (se 1 (by rfl) ⟨139775, by rfl⟩ : syracuseStep 186367 = 279551) B279551
theorem B186619 : Blo 183802 186619 := bstep (se 1 (by rfl) ⟨139964, by rfl⟩ : syracuseStep 186619 = 279929) B279929
theorem B186927 : Blo 183802 186927 := bstep (se 1 (by rfl) ⟨140195, by rfl⟩ : syracuseStep 186927 = 280391) B280391
theorem B417023 : Blo 183802 417023 := bstep (se 1 (by rfl) ⟨312767, by rfl⟩ : syracuseStep 417023 = 625535) B625535
theorem B2384923 : Blo 183802 2384923 := bstep (se 1 (by rfl) ⟨1788692, by rfl⟩ : syracuseStep 2384923 = 3577385) B3577385
theorem B419687 : Blo 183802 419687 := bstep (se 1 (by rfl) ⟨314765, by rfl⟩ : syracuseStep 419687 = 629531) B629531
theorem B4553333 : Blo 183802 4553333 := bstep (se 5 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 4553333 = 426875) B426875
theorem B5307029 : Blo 183802 5307029 := bstep (se 6 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 5307029 = 248767) B248767
theorem B262235 : Blo 183802 262235 := bstep (se 1 (by rfl) ⟨196676, by rfl⟩ : syracuseStep 262235 = 393353) B393353
theorem B590183 : Blo 183802 590183 := bstep (se 1 (by rfl) ⟨442637, by rfl⟩ : syracuseStep 590183 = 885275) B885275
theorem B14550353 : Blo 183802 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B3179897 : Blo 183802 3179897 := bstep (se 2 (by rfl) ⟨1192461, by rfl⟩ : syracuseStep 3179897 = 2384923) B2384923
theorem B591401 : Blo 183802 591401 := bstep (se 2 (by rfl) ⟨221775, by rfl⟩ : syracuseStep 591401 = 443551) B443551
theorem B592055 : Blo 183802 592055 := bstep (se 1 (by rfl) ⟨444041, by rfl⟩ : syracuseStep 592055 = 888083) B888083
theorem B469223 : Blo 183802 469223 := bstep (se 1 (by rfl) ⟨351917, by rfl⟩ : syracuseStep 469223 = 703835) B703835
theorem B568193 : Blo 183802 568193 := bstep (se 2 (by rfl) ⟨213072, by rfl⟩ : syracuseStep 568193 = 426145) B426145
theorem B278015 : Blo 183802 278015 := bstep (se 1 (by rfl) ⟨208511, by rfl⟩ : syracuseStep 278015 = 417023) B417023
theorem B279791 : Blo 183802 279791 := bstep (se 1 (by rfl) ⟨209843, by rfl⟩ : syracuseStep 279791 = 419687) B419687
theorem B184167 : Blo 183802 184167 := bstep (se 1 (by rfl) ⟨138125, by rfl⟩ : syracuseStep 184167 = 276251) B276251
theorem B184319 : Blo 183802 184319 := bstep (se 1 (by rfl) ⟨138239, by rfl⟩ : syracuseStep 184319 = 276479) B276479
theorem B1560815 : Blo 183802 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B3035555 : Blo 183802 3035555 := bstep (se 1 (by rfl) ⟨2276666, by rfl⟩ : syracuseStep 3035555 = 4553333) B4553333
theorem B2020583 : Blo 183802 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B186335 : Blo 183802 186335 := bstep (se 1 (by rfl) ⟨139751, by rfl⟩ : syracuseStep 186335 = 279503) B279503
theorem B645839 : Blo 183802 645839 := bstep (se 1 (by rfl) ⟨484379, by rfl⟩ : syracuseStep 645839 = 968759) B968759
theorem B12346273 : Blo 183802 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B420047 : Blo 183802 420047 := bstep (se 1 (by rfl) ⟨315035, by rfl⟩ : syracuseStep 420047 = 630071) B630071
theorem B3538019 : Blo 183802 3538019 := bstep (se 1 (by rfl) ⟨2653514, by rfl⟩ : syracuseStep 3538019 = 5307029) B5307029
theorem B393455 : Blo 183802 393455 := bstep (se 1 (by rfl) ⟨295091, by rfl⟩ : syracuseStep 393455 = 590183) B590183
theorem B9700235 : Blo 183802 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B394703 : Blo 183802 394703 := bstep (se 1 (by rfl) ⟨296027, by rfl⟩ : syracuseStep 394703 = 592055) B592055
theorem B1577069 : Blo 183802 1577069 := bstep (se 3 (by rfl) ⟨295700, by rfl⟩ : syracuseStep 1577069 = 591401) B591401
theorem B430559 : Blo 183802 430559 := bstep (se 1 (by rfl) ⟨322919, by rfl⟩ : syracuseStep 430559 = 645839) B645839
theorem B1515181 : Blo 183802 1515181 := bstep (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) B568193
theorem B699293 : Blo 183802 699293 := bstep (se 3 (by rfl) ⟨131117, by rfl⟩ : syracuseStep 699293 = 262235) B262235
theorem B5388221 : Blo 183802 5388221 := bstep (se 3 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 5388221 = 2020583) B2020583
theorem B65846789 : Blo 183802 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B280031 : Blo 183802 280031 := bstep (se 1 (by rfl) ⟨210023, by rfl⟩ : syracuseStep 280031 = 420047) B420047
theorem B312815 : Blo 183802 312815 := bstep (se 1 (by rfl) ⟨234611, by rfl⟩ : syracuseStep 312815 = 469223) B469223
theorem B185343 : Blo 183802 185343 := bstep (se 1 (by rfl) ⟨139007, by rfl⟩ : syracuseStep 185343 = 278015) B278015
theorem B186527 : Blo 183802 186527 := bstep (se 1 (by rfl) ⟨139895, by rfl⟩ : syracuseStep 186527 = 279791) B279791
theorem B2119931 : Blo 183802 2119931 := bstep (se 1 (by rfl) ⟨1589948, by rfl⟩ : syracuseStep 2119931 = 3179897) B3179897
theorem B1040543 : Blo 183802 1040543 := bstep (se 1 (by rfl) ⟨780407, by rfl⟩ : syracuseStep 1040543 = 1560815) B1560815
theorem B2023703 : Blo 183802 2023703 := bstep (se 1 (by rfl) ⟨1517777, by rfl⟩ : syracuseStep 2023703 = 3035555) B3035555
theorem B2358679 : Blo 183802 2358679 := bstep (se 1 (by rfl) ⟨1769009, by rfl⟩ : syracuseStep 2358679 = 3538019) B3538019
theorem B1049213 : Blo 183802 1049213 := bstep (se 3 (by rfl) ⟨196727, by rfl⟩ : syracuseStep 1049213 = 393455) B393455
theorem B263135 : Blo 183802 263135 := bstep (se 1 (by rfl) ⟨197351, by rfl⟩ : syracuseStep 263135 = 394703) B394703
theorem B1051379 : Blo 183802 1051379 := bstep (se 1 (by rfl) ⟨788534, by rfl⟩ : syracuseStep 1051379 = 1577069) B1577069
theorem B1413287 : Blo 183802 1413287 := bstep (se 1 (by rfl) ⟨1059965, by rfl⟩ : syracuseStep 1413287 = 2119931) B2119931
theorem B693695 : Blo 183802 693695 := bstep (se 1 (by rfl) ⟨520271, by rfl⟩ : syracuseStep 693695 = 1040543) B1040543
theorem B1349135 : Blo 183802 1349135 := bstep (se 1 (by rfl) ⟨1011851, by rfl⟩ : syracuseStep 1349135 = 2023703) B2023703
theorem B466195 : Blo 183802 466195 := bstep (se 1 (by rfl) ⟨349646, by rfl⟩ : syracuseStep 466195 = 699293) B699293
theorem B6466823 : Blo 183802 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B208543 : Blo 183802 208543 := bstep (se 1 (by rfl) ⟨156407, by rfl⟩ : syracuseStep 208543 = 312815) B312815
theorem B3592147 : Blo 183802 3592147 := bstep (se 1 (by rfl) ⟨2694110, by rfl⟩ : syracuseStep 3592147 = 5388221) B5388221
theorem B2020241 : Blo 183802 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B43897859 : Blo 183802 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B186687 : Blo 183802 186687 := bstep (se 1 (by rfl) ⟨140015, by rfl⟩ : syracuseStep 186687 = 280031) B280031
theorem B287039 : Blo 183802 287039 := bstep (se 1 (by rfl) ⟨215279, by rfl⟩ : syracuseStep 287039 = 430559) B430559
theorem B3144905 : Blo 183802 3144905 := bstep (se 2 (by rfl) ⟨1179339, by rfl⟩ : syracuseStep 3144905 = 2358679) B2358679
theorem B1346827 : Blo 183802 1346827 := bstep (se 1 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 1346827 = 2020241) B2020241
theorem B29265239 : Blo 183802 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B4789529 : Blo 183802 4789529 := bstep (se 2 (by rfl) ⟨1796073, by rfl⟩ : syracuseStep 4789529 = 3592147) B3592147
theorem B699475 : Blo 183802 699475 := bstep (se 1 (by rfl) ⟨524606, by rfl⟩ : syracuseStep 699475 = 1049213) B1049213
theorem B700919 : Blo 183802 700919 := bstep (se 1 (by rfl) ⟨525689, by rfl⟩ : syracuseStep 700919 = 1051379) B1051379
theorem B701693 : Blo 183802 701693 := bstep (se 3 (by rfl) ⟨131567, by rfl⟩ : syracuseStep 701693 = 263135) B263135
theorem B899423 : Blo 183802 899423 := bstep (se 1 (by rfl) ⟨674567, by rfl⟩ : syracuseStep 899423 = 1349135) B1349135
theorem B1849853 : Blo 183802 1849853 := bstep (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) B693695
theorem B278057 : Blo 183802 278057 := bstep (se 2 (by rfl) ⟨104271, by rfl⟩ : syracuseStep 278057 = 208543) B208543
theorem B4311215 : Blo 183802 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B942191 : Blo 183802 942191 := bstep (se 1 (by rfl) ⟨706643, by rfl⟩ : syracuseStep 942191 = 1413287) B1413287
theorem B191359 : Blo 183802 191359 := bstep (se 1 (by rfl) ⟨143519, by rfl⟩ : syracuseStep 191359 = 287039) B287039
theorem B621593 : Blo 183802 621593 := bstep (se 2 (by rfl) ⟨233097, by rfl⟩ : syracuseStep 621593 = 466195) B466195
theorem B2096603 : Blo 183802 2096603 := bstep (se 1 (by rfl) ⟨1572452, by rfl⟩ : syracuseStep 2096603 = 3144905) B3144905
theorem B628127 : Blo 183802 628127 := bstep (se 1 (by rfl) ⟨471095, by rfl⟩ : syracuseStep 628127 = 942191) B942191
theorem B467279 : Blo 183802 467279 := bstep (se 1 (by rfl) ⟨350459, by rfl⟩ : syracuseStep 467279 = 700919) B700919
theorem B467795 : Blo 183802 467795 := bstep (se 1 (by rfl) ⟨350846, by rfl⟩ : syracuseStep 467795 = 701693) B701693
theorem B599615 : Blo 183802 599615 := bstep (se 1 (by rfl) ⟨449711, by rfl⟩ : syracuseStep 599615 = 899423) B899423
theorem B19510159 : Blo 183802 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B3193019 : Blo 183802 3193019 := bstep (se 1 (by rfl) ⟨2394764, by rfl⟩ : syracuseStep 3193019 = 4789529) B4789529
theorem B932633 : Blo 183802 932633 := bstep (se 2 (by rfl) ⟨349737, by rfl⟩ : syracuseStep 932633 = 699475) B699475
theorem B1233235 : Blo 183802 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B414395 : Blo 183802 414395 := bstep (se 1 (by rfl) ⟨310796, by rfl⟩ : syracuseStep 414395 = 621593) B621593
theorem B1397735 : Blo 183802 1397735 := bstep (se 1 (by rfl) ⟨1048301, by rfl⟩ : syracuseStep 1397735 = 2096603) B2096603
theorem B185371 : Blo 183802 185371 := bstep (se 1 (by rfl) ⟨139028, by rfl⟩ : syracuseStep 185371 = 278057) B278057
theorem B2874143 : Blo 183802 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B255145 : Blo 183802 255145 := bstep (se 2 (by rfl) ⟨95679, by rfl⟩ : syracuseStep 255145 = 191359) B191359
theorem B1795769 : Blo 183802 1795769 := bstep (se 2 (by rfl) ⟨673413, by rfl⟩ : syracuseStep 1795769 = 1346827) B1346827
theorem B1644313 : Blo 183802 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B399743 : Blo 183802 399743 := bstep (se 1 (by rfl) ⟨299807, by rfl⟩ : syracuseStep 399743 = 599615) B599615
theorem B340193 : Blo 183802 340193 := bstep (se 2 (by rfl) ⟨127572, by rfl⟩ : syracuseStep 340193 = 255145) B255145
theorem B276263 : Blo 183802 276263 := bstep (se 1 (by rfl) ⟨207197, by rfl⟩ : syracuseStep 276263 = 414395) B414395
theorem B931823 : Blo 183802 931823 := bstep (se 1 (by rfl) ⟨698867, by rfl⟩ : syracuseStep 931823 = 1397735) B1397735
theorem B1916095 : Blo 183802 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B311519 : Blo 183802 311519 := bstep (se 1 (by rfl) ⟨233639, by rfl⟩ : syracuseStep 311519 = 467279) B467279
theorem B311863 : Blo 183802 311863 := bstep (se 1 (by rfl) ⟨233897, by rfl⟩ : syracuseStep 311863 = 467795) B467795
theorem B1197179 : Blo 183802 1197179 := bstep (se 1 (by rfl) ⟨897884, by rfl⟩ : syracuseStep 1197179 = 1795769) B1795769
theorem B418751 : Blo 183802 418751 := bstep (se 1 (by rfl) ⟨314063, by rfl⟩ : syracuseStep 418751 = 628127) B628127
theorem B26013545 : Blo 183802 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B2128679 : Blo 183802 2128679 := bstep (se 1 (by rfl) ⟨1596509, by rfl⟩ : syracuseStep 2128679 = 3193019) B3193019
theorem B621755 : Blo 183802 621755 := bstep (se 1 (by rfl) ⟨466316, by rfl⟩ : syracuseStep 621755 = 932633) B932633
theorem B266495 : Blo 183802 266495 := bstep (se 1 (by rfl) ⟨199871, by rfl⟩ : syracuseStep 266495 = 399743) B399743
theorem B17342363 : Blo 183802 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B1419119 : Blo 183802 1419119 := bstep (se 1 (by rfl) ⟨1064339, by rfl⟩ : syracuseStep 1419119 = 2128679) B2128679
theorem B207679 : Blo 183802 207679 := bstep (se 1 (by rfl) ⟨155759, by rfl⟩ : syracuseStep 207679 = 311519) B311519
theorem B798119 : Blo 183802 798119 := bstep (se 1 (by rfl) ⟨598589, by rfl⟩ : syracuseStep 798119 = 1197179) B1197179
theorem B279167 : Blo 183802 279167 := bstep (se 1 (by rfl) ⟨209375, by rfl⟩ : syracuseStep 279167 = 418751) B418751
theorem B184175 : Blo 183802 184175 := bstep (se 1 (by rfl) ⟨138131, by rfl⟩ : syracuseStep 184175 = 276263) B276263
theorem B414503 : Blo 183802 414503 := bstep (se 1 (by rfl) ⟨310877, by rfl⟩ : syracuseStep 414503 = 621755) B621755
theorem B415817 : Blo 183802 415817 := bstep (se 2 (by rfl) ⟨155931, by rfl⟩ : syracuseStep 415817 = 311863) B311863
theorem B2192417 : Blo 183802 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B226795 : Blo 183802 226795 := bstep (se 1 (by rfl) ⟨170096, by rfl⟩ : syracuseStep 226795 = 340193) B340193
theorem B621215 : Blo 183802 621215 := bstep (se 1 (by rfl) ⟨465911, by rfl⟩ : syracuseStep 621215 = 931823) B931823
theorem B2554793 : Blo 183802 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B302393 : Blo 183802 302393 := bstep (se 2 (by rfl) ⟨113397, by rfl⟩ : syracuseStep 302393 = 226795) B226795
theorem B532079 : Blo 183802 532079 := bstep (se 1 (by rfl) ⟨399059, by rfl⟩ : syracuseStep 532079 = 798119) B798119
theorem B276335 : Blo 183802 276335 := bstep (se 1 (by rfl) ⟨207251, by rfl⟩ : syracuseStep 276335 = 414503) B414503
theorem B276905 : Blo 183802 276905 := bstep (se 2 (by rfl) ⟨103839, by rfl⟩ : syracuseStep 276905 = 207679) B207679
theorem B277211 : Blo 183802 277211 := bstep (se 1 (by rfl) ⟨207908, by rfl⟩ : syracuseStep 277211 = 415817) B415817
theorem B1461611 : Blo 183802 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B414143 : Blo 183802 414143 := bstep (se 1 (by rfl) ⟨310607, by rfl⟩ : syracuseStep 414143 = 621215) B621215
theorem B186111 : Blo 183802 186111 := bstep (se 1 (by rfl) ⟨139583, by rfl⟩ : syracuseStep 186111 = 279167) B279167
theorem B710653 : Blo 183802 710653 := bstep (se 3 (by rfl) ⟨133247, by rfl⟩ : syracuseStep 710653 = 266495) B266495
theorem B11561575 : Blo 183802 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B946079 : Blo 183802 946079 := bstep (se 1 (by rfl) ⟨709559, by rfl⟩ : syracuseStep 946079 = 1419119) B1419119
theorem B1703195 : Blo 183802 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B630719 : Blo 183802 630719 := bstep (se 1 (by rfl) ⟨473039, by rfl⟩ : syracuseStep 630719 = 946079) B946079
theorem B276095 : Blo 183802 276095 := bstep (se 1 (by rfl) ⟨207071, by rfl⟩ : syracuseStep 276095 = 414143) B414143
theorem B15415433 : Blo 183802 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B806381 : Blo 183802 806381 := bstep (se 3 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 806381 = 302393) B302393
theorem B184223 : Blo 183802 184223 := bstep (se 1 (by rfl) ⟨138167, by rfl⟩ : syracuseStep 184223 = 276335) B276335
theorem B184603 : Blo 183802 184603 := bstep (se 1 (by rfl) ⟨138452, by rfl⟩ : syracuseStep 184603 = 276905) B276905
theorem B184807 : Blo 183802 184807 := bstep (se 1 (by rfl) ⟨138605, by rfl⟩ : syracuseStep 184807 = 277211) B277211
theorem B1135463 : Blo 183802 1135463 := bstep (se 1 (by rfl) ⟨851597, by rfl⟩ : syracuseStep 1135463 = 1703195) B1703195
theorem B354719 : Blo 183802 354719 := bstep (se 1 (by rfl) ⟨266039, by rfl⟩ : syracuseStep 354719 = 532079) B532079
theorem B947537 : Blo 183802 947537 := bstep (se 2 (by rfl) ⟨355326, by rfl⟩ : syracuseStep 947537 = 710653) B710653
theorem B3897629 : Blo 183802 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B631691 : Blo 183802 631691 := bstep (se 1 (by rfl) ⟨473768, by rfl⟩ : syracuseStep 631691 = 947537) B947537
theorem B2598419 : Blo 183802 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B3027901 : Blo 183802 3027901 := bstep (se 3 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 3027901 = 1135463) B1135463
theorem B537587 : Blo 183802 537587 := bstep (se 1 (by rfl) ⟨403190, by rfl⟩ : syracuseStep 537587 = 806381) B806381
theorem B184063 : Blo 183802 184063 := bstep (se 1 (by rfl) ⟨138047, by rfl⟩ : syracuseStep 184063 = 276095) B276095
theorem B10276955 : Blo 183802 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B420479 : Blo 183802 420479 := bstep (se 1 (by rfl) ⟨315359, by rfl⟩ : syracuseStep 420479 = 630719) B630719
theorem B945917 : Blo 183802 945917 := bstep (se 3 (by rfl) ⟨177359, by rfl⟩ : syracuseStep 945917 = 354719) B354719
theorem B6851303 : Blo 183802 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B4037201 : Blo 183802 4037201 := bstep (se 2 (by rfl) ⟨1513950, by rfl⟩ : syracuseStep 4037201 = 3027901) B3027901
theorem B630611 : Blo 183802 630611 := bstep (se 1 (by rfl) ⟨472958, by rfl⟩ : syracuseStep 630611 = 945917) B945917
theorem B280319 : Blo 183802 280319 := bstep (se 1 (by rfl) ⟨210239, by rfl⟩ : syracuseStep 280319 = 420479) B420479
theorem B421127 : Blo 183802 421127 := bstep (se 1 (by rfl) ⟨315845, by rfl⟩ : syracuseStep 421127 = 631691) B631691
theorem B1732279 : Blo 183802 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B358391 : Blo 183802 358391 := bstep (se 1 (by rfl) ⟨268793, by rfl⟩ : syracuseStep 358391 = 537587) B537587
theorem B2691467 : Blo 183802 2691467 := bstep (se 1 (by rfl) ⟨2018600, by rfl⟩ : syracuseStep 2691467 = 4037201) B4037201
theorem B955709 : Blo 183802 955709 := bstep (se 3 (by rfl) ⟨179195, by rfl⟩ : syracuseStep 955709 = 358391) B358391
theorem B4567535 : Blo 183802 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B2309705 : Blo 183802 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B280751 : Blo 183802 280751 := bstep (se 1 (by rfl) ⟨210563, by rfl⟩ : syracuseStep 280751 = 421127) B421127
theorem B186879 : Blo 183802 186879 := bstep (se 1 (by rfl) ⟨140159, by rfl⟩ : syracuseStep 186879 = 280319) B280319
theorem B420407 : Blo 183802 420407 := bstep (se 1 (by rfl) ⟨315305, by rfl⟩ : syracuseStep 420407 = 630611) B630611
theorem B637139 : Blo 183802 637139 := bstep (se 1 (by rfl) ⟨477854, by rfl⟩ : syracuseStep 637139 = 955709) B955709
theorem B280271 : Blo 183802 280271 := bstep (se 1 (by rfl) ⟨210203, by rfl⟩ : syracuseStep 280271 = 420407) B420407
theorem B187167 : Blo 183802 187167 := bstep (se 1 (by rfl) ⟨140375, by rfl⟩ : syracuseStep 187167 = 280751) B280751
theorem B1794311 : Blo 183802 1794311 := bstep (se 1 (by rfl) ⟨1345733, by rfl⟩ : syracuseStep 1794311 = 2691467) B2691467
theorem B3045023 : Blo 183802 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B1539803 : Blo 183802 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B1026535 : Blo 183802 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B1196207 : Blo 183802 1196207 := bstep (se 1 (by rfl) ⟨897155, by rfl⟩ : syracuseStep 1196207 = 1794311) B1794311
theorem B186847 : Blo 183802 186847 := bstep (se 1 (by rfl) ⟨140135, by rfl⟩ : syracuseStep 186847 = 280271) B280271
theorem B2030015 : Blo 183802 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B424759 : Blo 183802 424759 := bstep (se 1 (by rfl) ⟨318569, by rfl⟩ : syracuseStep 424759 = 637139) B637139
theorem B566345 : Blo 183802 566345 := bstep (se 2 (by rfl) ⟨212379, by rfl⟩ : syracuseStep 566345 = 424759) B424759
theorem B1353343 : Blo 183802 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B797471 : Blo 183802 797471 := bstep (se 1 (by rfl) ⟨598103, by rfl⟩ : syracuseStep 797471 = 1196207) B1196207
theorem B1368713 : Blo 183802 1368713 := bstep (se 2 (by rfl) ⟨513267, by rfl⟩ : syracuseStep 1368713 = 1026535) B1026535
theorem B1804457 : Blo 183802 1804457 := bstep (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) B1353343
theorem B531647 : Blo 183802 531647 := bstep (se 1 (by rfl) ⟨398735, by rfl⟩ : syracuseStep 531647 = 797471) B797471
theorem B377563 : Blo 183802 377563 := bstep (se 1 (by rfl) ⟨283172, by rfl⟩ : syracuseStep 377563 = 566345) B566345
theorem B912475 : Blo 183802 912475 := bstep (se 1 (by rfl) ⟨684356, by rfl⟩ : syracuseStep 912475 = 1368713) B1368713
theorem B1216633 : Blo 183802 1216633 := bstep (se 2 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 1216633 = 912475) B912475
theorem B503417 : Blo 183802 503417 := bstep (se 2 (by rfl) ⟨188781, by rfl⟩ : syracuseStep 503417 = 377563) B377563
theorem B1202971 : Blo 183802 1202971 := bstep (se 1 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 1202971 = 1804457) B1804457
theorem B354431 : Blo 183802 354431 := bstep (se 1 (by rfl) ⟨265823, by rfl⟩ : syracuseStep 354431 = 531647) B531647
theorem B236287 : Blo 183802 236287 := bstep (se 1 (by rfl) ⟨177215, by rfl⟩ : syracuseStep 236287 = 354431) B354431
theorem B335611 : Blo 183802 335611 := bstep (se 1 (by rfl) ⟨251708, by rfl⟩ : syracuseStep 335611 = 503417) B503417
theorem B1622177 : Blo 183802 1622177 := bstep (se 2 (by rfl) ⟨608316, by rfl⟩ : syracuseStep 1622177 = 1216633) B1216633
theorem B1603961 : Blo 183802 1603961 := bstep (se 2 (by rfl) ⟨601485, by rfl⟩ : syracuseStep 1603961 = 1202971) B1202971
theorem B1081451 : Blo 183802 1081451 := bstep (se 1 (by rfl) ⟨811088, by rfl⟩ : syracuseStep 1081451 = 1622177) B1622177
theorem B315049 : Blo 183802 315049 := bstep (se 2 (by rfl) ⟨118143, by rfl⟩ : syracuseStep 315049 = 236287) B236287
theorem B1069307 : Blo 183802 1069307 := bstep (se 1 (by rfl) ⟨801980, by rfl⟩ : syracuseStep 1069307 = 1603961) B1603961
theorem B447481 : Blo 183802 447481 := bstep (se 2 (by rfl) ⟨167805, by rfl⟩ : syracuseStep 447481 = 335611) B335611
theorem B2883869 : Blo 183802 2883869 := bstep (se 3 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 2883869 = 1081451) B1081451
theorem B596641 : Blo 183802 596641 := bstep (se 2 (by rfl) ⟨223740, by rfl⟩ : syracuseStep 596641 = 447481) B447481
theorem B712871 : Blo 183802 712871 := bstep (se 1 (by rfl) ⟨534653, by rfl⟩ : syracuseStep 712871 = 1069307) B1069307
theorem B420065 : Blo 183802 420065 := bstep (se 2 (by rfl) ⟨157524, by rfl⟩ : syracuseStep 420065 = 315049) B315049
theorem B795521 : Blo 183802 795521 := bstep (se 2 (by rfl) ⟨298320, by rfl⟩ : syracuseStep 795521 = 596641) B596641
theorem B475247 : Blo 183802 475247 := bstep (se 1 (by rfl) ⟨356435, by rfl⟩ : syracuseStep 475247 = 712871) B712871
theorem B280043 : Blo 183802 280043 := bstep (se 1 (by rfl) ⟨210032, by rfl⟩ : syracuseStep 280043 = 420065) B420065
theorem B1922579 : Blo 183802 1922579 := bstep (se 1 (by rfl) ⟨1441934, by rfl⟩ : syracuseStep 1922579 = 2883869) B2883869
theorem B1281719 : Blo 183802 1281719 := bstep (se 1 (by rfl) ⟨961289, by rfl⟩ : syracuseStep 1281719 = 1922579) B1922579
theorem B316831 : Blo 183802 316831 := bstep (se 1 (by rfl) ⟨237623, by rfl⟩ : syracuseStep 316831 = 475247) B475247
theorem B186695 : Blo 183802 186695 := bstep (se 1 (by rfl) ⟨140021, by rfl⟩ : syracuseStep 186695 = 280043) B280043
theorem B2121389 : Blo 183802 2121389 := bstep (se 3 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 2121389 = 795521) B795521
theorem B854479 : Blo 183802 854479 := bstep (se 1 (by rfl) ⟨640859, by rfl⟩ : syracuseStep 854479 = 1281719) B1281719
theorem B1414259 : Blo 183802 1414259 := bstep (se 1 (by rfl) ⟨1060694, by rfl⟩ : syracuseStep 1414259 = 2121389) B2121389
theorem B422441 : Blo 183802 422441 := bstep (se 2 (by rfl) ⟨158415, by rfl⟩ : syracuseStep 422441 = 316831) B316831
theorem B281627 : Blo 183802 281627 := bstep (se 1 (by rfl) ⟨211220, by rfl⟩ : syracuseStep 281627 = 422441) B422441
theorem B1139305 : Blo 183802 1139305 := bstep (se 2 (by rfl) ⟨427239, by rfl⟩ : syracuseStep 1139305 = 854479) B854479
theorem B942839 : Blo 183802 942839 := bstep (se 1 (by rfl) ⟨707129, by rfl⟩ : syracuseStep 942839 = 1414259) B1414259
theorem B628559 : Blo 183802 628559 := bstep (se 1 (by rfl) ⟨471419, by rfl⟩ : syracuseStep 628559 = 942839) B942839
theorem B1519073 : Blo 183802 1519073 := bstep (se 2 (by rfl) ⟨569652, by rfl⟩ : syracuseStep 1519073 = 1139305) B1139305
theorem B187751 : Blo 183802 187751 := bstep (se 1 (by rfl) ⟨140813, by rfl⟩ : syracuseStep 187751 = 281627) B281627
theorem B419039 : Blo 183802 419039 := bstep (se 1 (by rfl) ⟨314279, by rfl⟩ : syracuseStep 419039 = 628559) B628559
theorem B1012715 : Blo 183802 1012715 := bstep (se 1 (by rfl) ⟨759536, by rfl⟩ : syracuseStep 1012715 = 1519073) B1519073
theorem B279359 : Blo 183802 279359 := bstep (se 1 (by rfl) ⟨209519, by rfl⟩ : syracuseStep 279359 = 419039) B419039
theorem B675143 : Blo 183802 675143 := bstep (se 1 (by rfl) ⟨506357, by rfl⟩ : syracuseStep 675143 = 1012715) B1012715
theorem B186239 : Blo 183802 186239 := bstep (se 1 (by rfl) ⟨139679, by rfl⟩ : syracuseStep 186239 = 279359) B279359
theorem B450095 : Blo 183802 450095 := bstep (se 1 (by rfl) ⟨337571, by rfl⟩ : syracuseStep 450095 = 675143) B675143
theorem B1200253 : Blo 183802 1200253 := bstep (se 3 (by rfl) ⟨225047, by rfl⟩ : syracuseStep 1200253 = 450095) B450095
theorem B1600337 : Blo 183802 1600337 := bstep (se 2 (by rfl) ⟨600126, by rfl⟩ : syracuseStep 1600337 = 1200253) B1200253
theorem B1066891 : Blo 183802 1066891 := bstep (se 1 (by rfl) ⟨800168, by rfl⟩ : syracuseStep 1066891 = 1600337) B1600337
theorem B1422521 : Blo 183802 1422521 := bstep (se 2 (by rfl) ⟨533445, by rfl⟩ : syracuseStep 1422521 = 1066891) B1066891
theorem B948347 : Blo 183802 948347 := bstep (se 1 (by rfl) ⟨711260, by rfl⟩ : syracuseStep 948347 = 1422521) B1422521
theorem B632231 : Blo 183802 632231 := bstep (se 1 (by rfl) ⟨474173, by rfl⟩ : syracuseStep 632231 = 948347) B948347
theorem B421487 : Blo 183802 421487 := bstep (se 1 (by rfl) ⟨316115, by rfl⟩ : syracuseStep 421487 = 632231) B632231
theorem B280991 : Blo 183802 280991 := bstep (se 1 (by rfl) ⟨210743, by rfl⟩ : syracuseStep 280991 = 421487) B421487
theorem B187327 : Blo 183802 187327 := bstep (se 1 (by rfl) ⟨140495, by rfl⟩ : syracuseStep 187327 = 280991) B280991

theorem C0 (j : ℕ) (h1 : 45950 ≤ j) (h2 : j ≤ 46649) : Blo 183802 (4 * j + 3) := by
  interval_cases j
  · exact B183803
  · exact B183807
  · exact B183811
  · exact B183815
  · exact B183819
  · exact B183823
  · exact B183827
  · exact B183831
  · exact B183835
  · exact B183839
  · exact B183843
  · exact B183847
  · exact B183851
  · exact B183855
  · exact B183859
  · exact B183863
  · exact B183867
  · exact B183871
  · exact B183875
  · exact B183879
  · exact B183883
  · exact B183887
  · exact B183891
  · exact B183895
  · exact B183899
  · exact B183903
  · exact B183907
  · exact B183911
  · exact B183915
  · exact B183919
  · exact B183923
  · exact B183927
  · exact B183931
  · exact B183935
  · exact B183939
  · exact B183943
  · exact B183947
  · exact B183951
  · exact B183955
  · exact B183959
  · exact B183963
  · exact B183967
  · exact B183971
  · exact B183975
  · exact B183979
  · exact B183983
  · exact B183987
  · exact B183991
  · exact B183995
  · exact B183999
  · exact B184003
  · exact B184007
  · exact B184011
  · exact B184015
  · exact B184019
  · exact B184023
  · exact B184027
  · exact B184031
  · exact B184035
  · exact B184039
  · exact B184043
  · exact B184047
  · exact B184051
  · exact B184055
  · exact B184059
  · exact B184063
  · exact B184067
  · exact B184071
  · exact B184075
  · exact B184079
  · exact B184083
  · exact B184087
  · exact B184091
  · exact B184095
  · exact B184099
  · exact B184103
  · exact B184107
  · exact B184111
  · exact B184115
  · exact B184119
  · exact B184123
  · exact B184127
  · exact B184131
  · exact B184135
  · exact B184139
  · exact B184143
  · exact B184147
  · exact B184151
  · exact B184155
  · exact B184159
  · exact B184163
  · exact B184167
  · exact B184171
  · exact B184175
  · exact B184179
  · exact B184183
  · exact B184187
  · exact B184191
  · exact B184195
  · exact B184199
  · exact B184203
  · exact B184207
  · exact B184211
  · exact B184215
  · exact B184219
  · exact B184223
  · exact B184227
  · exact B184231
  · exact B184235
  · exact B184239
  · exact B184243
  · exact B184247
  · exact B184251
  · exact B184255
  · exact B184259
  · exact B184263
  · exact B184267
  · exact B184271
  · exact B184275
  · exact B184279
  · exact B184283
  · exact B184287
  · exact B184291
  · exact B184295
  · exact B184299
  · exact B184303
  · exact B184307
  · exact B184311
  · exact B184315
  · exact B184319
  · exact B184323
  · exact B184327
  · exact B184331
  · exact B184335
  · exact B184339
  · exact B184343
  · exact B184347
  · exact B184351
  · exact B184355
  · exact B184359
  · exact B184363
  · exact B184367
  · exact B184371
  · exact B184375
  · exact B184379
  · exact B184383
  · exact B184387
  · exact B184391
  · exact B184395
  · exact B184399
  · exact B184403
  · exact B184407
  · exact B184411
  · exact B184415
  · exact B184419
  · exact B184423
  · exact B184427
  · exact B184431
  · exact B184435
  · exact B184439
  · exact B184443
  · exact B184447
  · exact B184451
  · exact B184455
  · exact B184459
  · exact B184463
  · exact B184467
  · exact B184471
  · exact B184475
  · exact B184479
  · exact B184483
  · exact B184487
  · exact B184491
  · exact B184495
  · exact B184499
  · exact B184503
  · exact B184507
  · exact B184511
  · exact B184515
  · exact B184519
  · exact B184523
  · exact B184527
  · exact B184531
  · exact B184535
  · exact B184539
  · exact B184543
  · exact B184547
  · exact B184551
  · exact B184555
  · exact B184559
  · exact B184563
  · exact B184567
  · exact B184571
  · exact B184575
  · exact B184579
  · exact B184583
  · exact B184587
  · exact B184591
  · exact B184595
  · exact B184599
  · exact B184603
  · exact B184607
  · exact B184611
  · exact B184615
  · exact B184619
  · exact B184623
  · exact B184627
  · exact B184631
  · exact B184635
  · exact B184639
  · exact B184643
  · exact B184647
  · exact B184651
  · exact B184655
  · exact B184659
  · exact B184663
  · exact B184667
  · exact B184671
  · exact B184675
  · exact B184679
  · exact B184683
  · exact B184687
  · exact B184691
  · exact B184695
  · exact B184699
  · exact B184703
  · exact B184707
  · exact B184711
  · exact B184715
  · exact B184719
  · exact B184723
  · exact B184727
  · exact B184731
  · exact B184735
  · exact B184739
  · exact B184743
  · exact B184747
  · exact B184751
  · exact B184755
  · exact B184759
  · exact B184763
  · exact B184767
  · exact B184771
  · exact B184775
  · exact B184779
  · exact B184783
  · exact B184787
  · exact B184791
  · exact B184795
  · exact B184799
  · exact B184803
  · exact B184807
  · exact B184811
  · exact B184815
  · exact B184819
  · exact B184823
  · exact B184827
  · exact B184831
  · exact B184835
  · exact B184839
  · exact B184843
  · exact B184847
  · exact B184851
  · exact B184855
  · exact B184859
  · exact B184863
  · exact B184867
  · exact B184871
  · exact B184875
  · exact B184879
  · exact B184883
  · exact B184887
  · exact B184891
  · exact B184895
  · exact B184899
  · exact B184903
  · exact B184907
  · exact B184911
  · exact B184915
  · exact B184919
  · exact B184923
  · exact B184927
  · exact B184931
  · exact B184935
  · exact B184939
  · exact B184943
  · exact B184947
  · exact B184951
  · exact B184955
  · exact B184959
  · exact B184963
  · exact B184967
  · exact B184971
  · exact B184975
  · exact B184979
  · exact B184983
  · exact B184987
  · exact B184991
  · exact B184995
  · exact B184999
  · exact B185003
  · exact B185007
  · exact B185011
  · exact B185015
  · exact B185019
  · exact B185023
  · exact B185027
  · exact B185031
  · exact B185035
  · exact B185039
  · exact B185043
  · exact B185047
  · exact B185051
  · exact B185055
  · exact B185059
  · exact B185063
  · exact B185067
  · exact B185071
  · exact B185075
  · exact B185079
  · exact B185083
  · exact B185087
  · exact B185091
  · exact B185095
  · exact B185099
  · exact B185103
  · exact B185107
  · exact B185111
  · exact B185115
  · exact B185119
  · exact B185123
  · exact B185127
  · exact B185131
  · exact B185135
  · exact B185139
  · exact B185143
  · exact B185147
  · exact B185151
  · exact B185155
  · exact B185159
  · exact B185163
  · exact B185167
  · exact B185171
  · exact B185175
  · exact B185179
  · exact B185183
  · exact B185187
  · exact B185191
  · exact B185195
  · exact B185199
  · exact B185203
  · exact B185207
  · exact B185211
  · exact B185215
  · exact B185219
  · exact B185223
  · exact B185227
  · exact B185231
  · exact B185235
  · exact B185239
  · exact B185243
  · exact B185247
  · exact B185251
  · exact B185255
  · exact B185259
  · exact B185263
  · exact B185267
  · exact B185271
  · exact B185275
  · exact B185279
  · exact B185283
  · exact B185287
  · exact B185291
  · exact B185295
  · exact B185299
  · exact B185303
  · exact B185307
  · exact B185311
  · exact B185315
  · exact B185319
  · exact B185323
  · exact B185327
  · exact B185331
  · exact B185335
  · exact B185339
  · exact B185343
  · exact B185347
  · exact B185351
  · exact B185355
  · exact B185359
  · exact B185363
  · exact B185367
  · exact B185371
  · exact B185375
  · exact B185379
  · exact B185383
  · exact B185387
  · exact B185391
  · exact B185395
  · exact B185399
  · exact B185403
  · exact B185407
  · exact B185411
  · exact B185415
  · exact B185419
  · exact B185423
  · exact B185427
  · exact B185431
  · exact B185435
  · exact B185439
  · exact B185443
  · exact B185447
  · exact B185451
  · exact B185455
  · exact B185459
  · exact B185463
  · exact B185467
  · exact B185471
  · exact B185475
  · exact B185479
  · exact B185483
  · exact B185487
  · exact B185491
  · exact B185495
  · exact B185499
  · exact B185503
  · exact B185507
  · exact B185511
  · exact B185515
  · exact B185519
  · exact B185523
  · exact B185527
  · exact B185531
  · exact B185535
  · exact B185539
  · exact B185543
  · exact B185547
  · exact B185551
  · exact B185555
  · exact B185559
  · exact B185563
  · exact B185567
  · exact B185571
  · exact B185575
  · exact B185579
  · exact B185583
  · exact B185587
  · exact B185591
  · exact B185595
  · exact B185599
  · exact B185603
  · exact B185607
  · exact B185611
  · exact B185615
  · exact B185619
  · exact B185623
  · exact B185627
  · exact B185631
  · exact B185635
  · exact B185639
  · exact B185643
  · exact B185647
  · exact B185651
  · exact B185655
  · exact B185659
  · exact B185663
  · exact B185667
  · exact B185671
  · exact B185675
  · exact B185679
  · exact B185683
  · exact B185687
  · exact B185691
  · exact B185695
  · exact B185699
  · exact B185703
  · exact B185707
  · exact B185711
  · exact B185715
  · exact B185719
  · exact B185723
  · exact B185727
  · exact B185731
  · exact B185735
  · exact B185739
  · exact B185743
  · exact B185747
  · exact B185751
  · exact B185755
  · exact B185759
  · exact B185763
  · exact B185767
  · exact B185771
  · exact B185775
  · exact B185779
  · exact B185783
  · exact B185787
  · exact B185791
  · exact B185795
  · exact B185799
  · exact B185803
  · exact B185807
  · exact B185811
  · exact B185815
  · exact B185819
  · exact B185823
  · exact B185827
  · exact B185831
  · exact B185835
  · exact B185839
  · exact B185843
  · exact B185847
  · exact B185851
  · exact B185855
  · exact B185859
  · exact B185863
  · exact B185867
  · exact B185871
  · exact B185875
  · exact B185879
  · exact B185883
  · exact B185887
  · exact B185891
  · exact B185895
  · exact B185899
  · exact B185903
  · exact B185907
  · exact B185911
  · exact B185915
  · exact B185919
  · exact B185923
  · exact B185927
  · exact B185931
  · exact B185935
  · exact B185939
  · exact B185943
  · exact B185947
  · exact B185951
  · exact B185955
  · exact B185959
  · exact B185963
  · exact B185967
  · exact B185971
  · exact B185975
  · exact B185979
  · exact B185983
  · exact B185987
  · exact B185991
  · exact B185995
  · exact B185999
  · exact B186003
  · exact B186007
  · exact B186011
  · exact B186015
  · exact B186019
  · exact B186023
  · exact B186027
  · exact B186031
  · exact B186035
  · exact B186039
  · exact B186043
  · exact B186047
  · exact B186051
  · exact B186055
  · exact B186059
  · exact B186063
  · exact B186067
  · exact B186071
  · exact B186075
  · exact B186079
  · exact B186083
  · exact B186087
  · exact B186091
  · exact B186095
  · exact B186099
  · exact B186103
  · exact B186107
  · exact B186111
  · exact B186115
  · exact B186119
  · exact B186123
  · exact B186127
  · exact B186131
  · exact B186135
  · exact B186139
  · exact B186143
  · exact B186147
  · exact B186151
  · exact B186155
  · exact B186159
  · exact B186163
  · exact B186167
  · exact B186171
  · exact B186175
  · exact B186179
  · exact B186183
  · exact B186187
  · exact B186191
  · exact B186195
  · exact B186199
  · exact B186203
  · exact B186207
  · exact B186211
  · exact B186215
  · exact B186219
  · exact B186223
  · exact B186227
  · exact B186231
  · exact B186235
  · exact B186239
  · exact B186243
  · exact B186247
  · exact B186251
  · exact B186255
  · exact B186259
  · exact B186263
  · exact B186267
  · exact B186271
  · exact B186275
  · exact B186279
  · exact B186283
  · exact B186287
  · exact B186291
  · exact B186295
  · exact B186299
  · exact B186303
  · exact B186307
  · exact B186311
  · exact B186315
  · exact B186319
  · exact B186323
  · exact B186327
  · exact B186331
  · exact B186335
  · exact B186339
  · exact B186343
  · exact B186347
  · exact B186351
  · exact B186355
  · exact B186359
  · exact B186363
  · exact B186367
  · exact B186371
  · exact B186375
  · exact B186379
  · exact B186383
  · exact B186387
  · exact B186391
  · exact B186395
  · exact B186399
  · exact B186403
  · exact B186407
  · exact B186411
  · exact B186415
  · exact B186419
  · exact B186423
  · exact B186427
  · exact B186431
  · exact B186435
  · exact B186439
  · exact B186443
  · exact B186447
  · exact B186451
  · exact B186455
  · exact B186459
  · exact B186463
  · exact B186467
  · exact B186471
  · exact B186475
  · exact B186479
  · exact B186483
  · exact B186487
  · exact B186491
  · exact B186495
  · exact B186499
  · exact B186503
  · exact B186507
  · exact B186511
  · exact B186515
  · exact B186519
  · exact B186523
  · exact B186527
  · exact B186531
  · exact B186535
  · exact B186539
  · exact B186543
  · exact B186547
  · exact B186551
  · exact B186555
  · exact B186559
  · exact B186563
  · exact B186567
  · exact B186571
  · exact B186575
  · exact B186579
  · exact B186583
  · exact B186587
  · exact B186591
  · exact B186595
  · exact B186599

theorem C1 (j : ℕ) (h1 : 46650 ≤ j) (h2 : j ≤ 46949) : Blo 183802 (4 * j + 3) := by
  interval_cases j
  · exact B186603
  · exact B186607
  · exact B186611
  · exact B186615
  · exact B186619
  · exact B186623
  · exact B186627
  · exact B186631
  · exact B186635
  · exact B186639
  · exact B186643
  · exact B186647
  · exact B186651
  · exact B186655
  · exact B186659
  · exact B186663
  · exact B186667
  · exact B186671
  · exact B186675
  · exact B186679
  · exact B186683
  · exact B186687
  · exact B186691
  · exact B186695
  · exact B186699
  · exact B186703
  · exact B186707
  · exact B186711
  · exact B186715
  · exact B186719
  · exact B186723
  · exact B186727
  · exact B186731
  · exact B186735
  · exact B186739
  · exact B186743
  · exact B186747
  · exact B186751
  · exact B186755
  · exact B186759
  · exact B186763
  · exact B186767
  · exact B186771
  · exact B186775
  · exact B186779
  · exact B186783
  · exact B186787
  · exact B186791
  · exact B186795
  · exact B186799
  · exact B186803
  · exact B186807
  · exact B186811
  · exact B186815
  · exact B186819
  · exact B186823
  · exact B186827
  · exact B186831
  · exact B186835
  · exact B186839
  · exact B186843
  · exact B186847
  · exact B186851
  · exact B186855
  · exact B186859
  · exact B186863
  · exact B186867
  · exact B186871
  · exact B186875
  · exact B186879
  · exact B186883
  · exact B186887
  · exact B186891
  · exact B186895
  · exact B186899
  · exact B186903
  · exact B186907
  · exact B186911
  · exact B186915
  · exact B186919
  · exact B186923
  · exact B186927
  · exact B186931
  · exact B186935
  · exact B186939
  · exact B186943
  · exact B186947
  · exact B186951
  · exact B186955
  · exact B186959
  · exact B186963
  · exact B186967
  · exact B186971
  · exact B186975
  · exact B186979
  · exact B186983
  · exact B186987
  · exact B186991
  · exact B186995
  · exact B186999
  · exact B187003
  · exact B187007
  · exact B187011
  · exact B187015
  · exact B187019
  · exact B187023
  · exact B187027
  · exact B187031
  · exact B187035
  · exact B187039
  · exact B187043
  · exact B187047
  · exact B187051
  · exact B187055
  · exact B187059
  · exact B187063
  · exact B187067
  · exact B187071
  · exact B187075
  · exact B187079
  · exact B187083
  · exact B187087
  · exact B187091
  · exact B187095
  · exact B187099
  · exact B187103
  · exact B187107
  · exact B187111
  · exact B187115
  · exact B187119
  · exact B187123
  · exact B187127
  · exact B187131
  · exact B187135
  · exact B187139
  · exact B187143
  · exact B187147
  · exact B187151
  · exact B187155
  · exact B187159
  · exact B187163
  · exact B187167
  · exact B187171
  · exact B187175
  · exact B187179
  · exact B187183
  · exact B187187
  · exact B187191
  · exact B187195
  · exact B187199
  · exact B187203
  · exact B187207
  · exact B187211
  · exact B187215
  · exact B187219
  · exact B187223
  · exact B187227
  · exact B187231
  · exact B187235
  · exact B187239
  · exact B187243
  · exact B187247
  · exact B187251
  · exact B187255
  · exact B187259
  · exact B187263
  · exact B187267
  · exact B187271
  · exact B187275
  · exact B187279
  · exact B187283
  · exact B187287
  · exact B187291
  · exact B187295
  · exact B187299
  · exact B187303
  · exact B187307
  · exact B187311
  · exact B187315
  · exact B187319
  · exact B187323
  · exact B187327
  · exact B187331
  · exact B187335
  · exact B187339
  · exact B187343
  · exact B187347
  · exact B187351
  · exact B187355
  · exact B187359
  · exact B187363
  · exact B187367
  · exact B187371
  · exact B187375
  · exact B187379
  · exact B187383
  · exact B187387
  · exact B187391
  · exact B187395
  · exact B187399
  · exact B187403
  · exact B187407
  · exact B187411
  · exact B187415
  · exact B187419
  · exact B187423
  · exact B187427
  · exact B187431
  · exact B187435
  · exact B187439
  · exact B187443
  · exact B187447
  · exact B187451
  · exact B187455
  · exact B187459
  · exact B187463
  · exact B187467
  · exact B187471
  · exact B187475
  · exact B187479
  · exact B187483
  · exact B187487
  · exact B187491
  · exact B187495
  · exact B187499
  · exact B187503
  · exact B187507
  · exact B187511
  · exact B187515
  · exact B187519
  · exact B187523
  · exact B187527
  · exact B187531
  · exact B187535
  · exact B187539
  · exact B187543
  · exact B187547
  · exact B187551
  · exact B187555
  · exact B187559
  · exact B187563
  · exact B187567
  · exact B187571
  · exact B187575
  · exact B187579
  · exact B187583
  · exact B187587
  · exact B187591
  · exact B187595
  · exact B187599
  · exact B187603
  · exact B187607
  · exact B187611
  · exact B187615
  · exact B187619
  · exact B187623
  · exact B187627
  · exact B187631
  · exact B187635
  · exact B187639
  · exact B187643
  · exact B187647
  · exact B187651
  · exact B187655
  · exact B187659
  · exact B187663
  · exact B187667
  · exact B187671
  · exact B187675
  · exact B187679
  · exact B187683
  · exact B187687
  · exact B187691
  · exact B187695
  · exact B187699
  · exact B187703
  · exact B187707
  · exact B187711
  · exact B187715
  · exact B187719
  · exact B187723
  · exact B187727
  · exact B187731
  · exact B187735
  · exact B187739
  · exact B187743
  · exact B187747
  · exact B187751
  · exact B187755
  · exact B187759
  · exact B187763
  · exact B187767
  · exact B187771
  · exact B187775
  · exact B187779
  · exact B187783
  · exact B187787
  · exact B187791
  · exact B187795
  · exact B187799

theorem solution (m : ℕ) (hlo : 183802 ≤ m) (hhi : m ≤ 187802) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 45950 ≤ j := by omega
    have hj2 : j ≤ 46949 := by omega
    have hb : Blo 183802 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 46650 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
