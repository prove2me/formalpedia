-- Prove2me | solution 1 for syracuse_descends_range_802343_806343
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:38.152592+00:00
-- url     : https://prove2.me/submissions/855bf134-8496-473f-ae9e-68f5d01bf215

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


theorem B1015841 : Blo 802343 1015841 := bbase (se 2 (by rfl) ⟨380940, by rfl⟩ : syracuseStep 1015841 = 761881) (by norm_num)
theorem B3309605 : Blo 802343 3309605 := bbase (se 4 (by rfl) ⟨310275, by rfl⟩ : syracuseStep 3309605 = 620551) (by norm_num)
theorem B1015897 : Blo 802343 1015897 := bbase (se 2 (by rfl) ⟨380961, by rfl⟩ : syracuseStep 1015897 = 761923) (by norm_num)
theorem B917653 : Blo 802343 917653 := bbase (se 6 (by rfl) ⟨21507, by rfl⟩ : syracuseStep 917653 = 43015) (by norm_num)
theorem B2719925 : Blo 802343 2719925 := bbase (se 5 (by rfl) ⟨127496, by rfl⟩ : syracuseStep 2719925 = 254993) (by norm_num)
theorem B1015993 : Blo 802343 1015993 := bbase (se 2 (by rfl) ⟨380997, by rfl⟩ : syracuseStep 1015993 = 761995) (by norm_num)
theorem B4063445 : Blo 802343 4063445 := bbase (se 7 (by rfl) ⟨47618, by rfl⟩ : syracuseStep 4063445 = 95237) (by norm_num)
theorem B4358357 : Blo 802343 4358357 := bbase (se 7 (by rfl) ⟨51074, by rfl⟩ : syracuseStep 4358357 = 102149) (by norm_num)
theorem B2031925 : Blo 802343 2031925 := bbase (se 5 (by rfl) ⟨95246, by rfl⟩ : syracuseStep 2031925 = 190493) (by norm_num)
theorem B1933645 : Blo 802343 1933645 := bbase (se 3 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 1933645 = 725117) (by norm_num)
theorem B1147213 : Blo 802343 1147213 := bbase (se 3 (by rfl) ⟨215102, by rfl⟩ : syracuseStep 1147213 = 430205) (by norm_num)
theorem B1016165 : Blo 802343 1016165 := bbase (se 4 (by rfl) ⟨95265, by rfl⟩ : syracuseStep 1016165 = 190531) (by norm_num)
theorem B3047813 : Blo 802343 3047813 := bbase (se 4 (by rfl) ⟨285732, by rfl⟩ : syracuseStep 3047813 = 571465) (by norm_num)
theorem B2064781 : Blo 802343 2064781 := bbase (se 3 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 2064781 = 774293) (by norm_num)
theorem B1016221 : Blo 802343 1016221 := bbase (se 3 (by rfl) ⟨190541, by rfl⟩ : syracuseStep 1016221 = 381083) (by norm_num)
theorem B2032037 : Blo 802343 2032037 := bbase (se 4 (by rfl) ⟨190503, by rfl⟩ : syracuseStep 2032037 = 381007) (by norm_num)
theorem B1016317 : Blo 802343 1016317 := bbase (se 3 (by rfl) ⟨190559, by rfl⟩ : syracuseStep 1016317 = 381119) (by norm_num)
theorem B2032229 : Blo 802343 2032229 := bbase (se 4 (by rfl) ⟨190521, by rfl⟩ : syracuseStep 2032229 = 381043) (by norm_num)
theorem B2720357 : Blo 802343 2720357 := bbase (se 4 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 2720357 = 510067) (by norm_num)
theorem B1147549 : Blo 802343 1147549 := bbase (se 3 (by rfl) ⟨215165, by rfl⟩ : syracuseStep 1147549 = 430331) (by norm_num)
theorem B3048101 : Blo 802343 3048101 := bbase (se 4 (by rfl) ⟨285759, by rfl⟩ : syracuseStep 3048101 = 571519) (by norm_num)
theorem B1016489 : Blo 802343 1016489 := bbase (se 2 (by rfl) ⟨381183, by rfl⟩ : syracuseStep 1016489 = 762367) (by norm_num)
theorem B1016545 : Blo 802343 1016545 := bbase (se 2 (by rfl) ⟨381204, by rfl⟩ : syracuseStep 1016545 = 762409) (by norm_num)
theorem B918301 : Blo 802343 918301 := bbase (se 3 (by rfl) ⟨172181, by rfl⟩ : syracuseStep 918301 = 344363) (by norm_num)
theorem B1737509 : Blo 802343 1737509 := bbase (se 4 (by rfl) ⟨162891, by rfl⟩ : syracuseStep 1737509 = 325783) (by norm_num)
theorem B1016641 : Blo 802343 1016641 := bbase (se 2 (by rfl) ⟨381240, by rfl⟩ : syracuseStep 1016641 = 762481) (by norm_num)
theorem B1147765 : Blo 802343 1147765 := bbase (se 5 (by rfl) ⟨53801, by rfl⟩ : syracuseStep 1147765 = 107603) (by norm_num)
theorem B1835909 : Blo 802343 1835909 := bbase (se 4 (by rfl) ⟨172116, by rfl⟩ : syracuseStep 1835909 = 344233) (by norm_num)
theorem B2032573 : Blo 802343 2032573 := bbase (se 3 (by rfl) ⟨381107, by rfl⟩ : syracuseStep 2032573 = 762215) (by norm_num)
theorem B1016813 : Blo 802343 1016813 := bbase (se 3 (by rfl) ⟨190652, by rfl⟩ : syracuseStep 1016813 = 381305) (by norm_num)
theorem B2720789 : Blo 802343 2720789 := bbase (se 6 (by rfl) ⟨63768, by rfl⟩ : syracuseStep 2720789 = 127537) (by norm_num)
theorem B1016869 : Blo 802343 1016869 := bbase (se 4 (by rfl) ⟨95331, by rfl⟩ : syracuseStep 1016869 = 190663) (by norm_num)
theorem B2032685 : Blo 802343 2032685 := bbase (se 3 (by rfl) ⟨381128, by rfl⟩ : syracuseStep 2032685 = 762257) (by norm_num)
theorem B1016965 : Blo 802343 1016965 := bbase (se 4 (by rfl) ⟨95340, by rfl⟩ : syracuseStep 1016965 = 190681) (by norm_num)
theorem B2032877 : Blo 802343 2032877 := bbase (se 3 (by rfl) ⟨381164, by rfl⟩ : syracuseStep 2032877 = 762329) (by norm_num)
theorem B2295029 : Blo 802343 2295029 := bbase (se 5 (by rfl) ⟨107579, by rfl⟩ : syracuseStep 2295029 = 215159) (by norm_num)
theorem B918821 : Blo 802343 918821 := bbase (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) (by norm_num)
theorem B1017137 : Blo 802343 1017137 := bbase (se 2 (by rfl) ⟨381426, by rfl⟩ : syracuseStep 1017137 = 762853) (by norm_num)
theorem B1017193 : Blo 802343 1017193 := bbase (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) (by norm_num)
theorem B2721221 : Blo 802343 2721221 := bbase (se 4 (by rfl) ⟨255114, by rfl⟩ : syracuseStep 2721221 = 510229) (by norm_num)
theorem B1017289 : Blo 802343 1017289 := bbase (se 2 (by rfl) ⟨381483, by rfl⟩ : syracuseStep 1017289 = 762967) (by norm_num)
theorem B4064741 : Blo 802343 4064741 := bbase (se 4 (by rfl) ⟨381069, by rfl⟩ : syracuseStep 4064741 = 762139) (by norm_num)
theorem B2033221 : Blo 802343 2033221 := bbase (se 4 (by rfl) ⟨190614, by rfl⟩ : syracuseStep 2033221 = 381229) (by norm_num)
theorem B1017461 : Blo 802343 1017461 := bbase (se 5 (by rfl) ⟨47693, by rfl⟩ : syracuseStep 1017461 = 95387) (by norm_num)
theorem B3868325 : Blo 802343 3868325 := bbase (se 4 (by rfl) ⟨362655, by rfl⟩ : syracuseStep 3868325 = 725311) (by norm_num)
theorem B1017517 : Blo 802343 1017517 := bbase (se 3 (by rfl) ⟨190784, by rfl⟩ : syracuseStep 1017517 = 381569) (by norm_num)
theorem B2033333 : Blo 802343 2033333 := bbase (se 5 (by rfl) ⟨95312, by rfl⟩ : syracuseStep 2033333 = 190625) (by norm_num)
theorem B1935029 : Blo 802343 1935029 := bbase (se 5 (by rfl) ⟨90704, by rfl⟩ : syracuseStep 1935029 = 181409) (by norm_num)
theorem B4589237 : Blo 802343 4589237 := bbase (se 5 (by rfl) ⟨215120, by rfl⟩ : syracuseStep 4589237 = 430241) (by norm_num)
theorem B1017613 : Blo 802343 1017613 := bbase (se 3 (by rfl) ⟨190802, by rfl⟩ : syracuseStep 1017613 = 381605) (by norm_num)
theorem B10323733 : Blo 802343 10323733 := bbase (se 6 (by rfl) ⟨241962, by rfl⟩ : syracuseStep 10323733 = 483925) (by norm_num)
theorem B3049285 : Blo 802343 3049285 := bbase (se 4 (by rfl) ⟨285870, by rfl⟩ : syracuseStep 3049285 = 571741) (by norm_num)
theorem B2033525 : Blo 802343 2033525 := bbase (se 5 (by rfl) ⟨95321, by rfl⟩ : syracuseStep 2033525 = 190643) (by norm_num)
theorem B3475349 : Blo 802343 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B1017785 : Blo 802343 1017785 := bbase (se 2 (by rfl) ⟨381669, by rfl⟩ : syracuseStep 1017785 = 763339) (by norm_num)
theorem B1017841 : Blo 802343 1017841 := bbase (se 2 (by rfl) ⟨381690, by rfl⟩ : syracuseStep 1017841 = 763381) (by norm_num)
theorem B1017937 : Blo 802343 1017937 := bbase (se 2 (by rfl) ⟨381726, by rfl⟩ : syracuseStep 1017937 = 763453) (by norm_num)
theorem B1935461 : Blo 802343 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B3049589 : Blo 802343 3049589 := bbase (se 5 (by rfl) ⟨142949, by rfl⟩ : syracuseStep 3049589 = 285899) (by norm_num)
theorem B9799829 : Blo 802343 9799829 := bbase (se 6 (by rfl) ⟨229683, by rfl⟩ : syracuseStep 9799829 = 459367) (by norm_num)
theorem B2033869 : Blo 802343 2033869 := bbase (se 3 (by rfl) ⟨381350, by rfl⟩ : syracuseStep 2033869 = 762701) (by norm_num)
theorem B1018109 : Blo 802343 1018109 := bbase (se 3 (by rfl) ⟨190895, by rfl⟩ : syracuseStep 1018109 = 381791) (by norm_num)
theorem B5146901 : Blo 802343 5146901 := bbase (se 6 (by rfl) ⟨120630, by rfl⟩ : syracuseStep 5146901 = 241261) (by norm_num)
theorem B1018165 : Blo 802343 1018165 := bbase (se 5 (by rfl) ⟨47726, by rfl⟩ : syracuseStep 1018165 = 95453) (by norm_num)
theorem B2033981 : Blo 802343 2033981 := bbase (se 3 (by rfl) ⟨381371, by rfl⟩ : syracuseStep 2033981 = 762743) (by norm_num)
theorem B1837397 : Blo 802343 1837397 := bbase (se 10 (by rfl) ⟨2691, by rfl⟩ : syracuseStep 1837397 = 5383) (by norm_num)
theorem B1378669 : Blo 802343 1378669 := bbase (se 3 (by rfl) ⟨258500, by rfl⟩ : syracuseStep 1378669 = 517001) (by norm_num)
theorem B1018261 : Blo 802343 1018261 := bbase (se 6 (by rfl) ⟨23865, by rfl⟩ : syracuseStep 1018261 = 47731) (by norm_num)
theorem B2034173 : Blo 802343 2034173 := bbase (se 3 (by rfl) ⟨381407, by rfl⟩ : syracuseStep 2034173 = 762815) (by norm_num)
theorem B1018433 : Blo 802343 1018433 := bbase (se 2 (by rfl) ⟨381912, by rfl⟩ : syracuseStep 1018433 = 763825) (by norm_num)
theorem B1018489 : Blo 802343 1018489 := bbase (se 2 (by rfl) ⟨381933, by rfl⟩ : syracuseStep 1018489 = 763867) (by norm_num)
theorem B1018585 : Blo 802343 1018585 := bbase (se 2 (by rfl) ⟨381969, by rfl⟩ : syracuseStep 1018585 = 763939) (by norm_num)
theorem B4066037 : Blo 802343 4066037 := bbase (se 5 (by rfl) ⟨190595, by rfl⟩ : syracuseStep 4066037 = 381191) (by norm_num)
theorem B2034517 : Blo 802343 2034517 := bbase (se 9 (by rfl) ⟨5960, by rfl⟩ : syracuseStep 2034517 = 11921) (by norm_num)
theorem B1018757 : Blo 802343 1018757 := bbase (se 4 (by rfl) ⟨95508, by rfl⟩ : syracuseStep 1018757 = 191017) (by norm_num)
theorem B3476405 : Blo 802343 3476405 := bbase (se 5 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 3476405 = 325913) (by norm_num)
theorem B1018813 : Blo 802343 1018813 := bbase (se 3 (by rfl) ⟨191027, by rfl⟩ : syracuseStep 1018813 = 382055) (by norm_num)
theorem B2034629 : Blo 802343 2034629 := bbase (se 4 (by rfl) ⟨190746, by rfl⟩ : syracuseStep 2034629 = 381493) (by norm_num)
theorem B7736309 : Blo 802343 7736309 := bbase (se 5 (by rfl) ⟨362639, by rfl⟩ : syracuseStep 7736309 = 725279) (by norm_num)
theorem B1805309 : Blo 802343 1805309 := bbase (se 3 (by rfl) ⟨338495, by rfl⟩ : syracuseStep 1805309 = 676991) (by norm_num)
theorem B1018909 : Blo 802343 1018909 := bbase (se 3 (by rfl) ⟨191045, by rfl⟩ : syracuseStep 1018909 = 382091) (by norm_num)
theorem B1805381 : Blo 802343 1805381 := bbase (se 4 (by rfl) ⟨169254, by rfl⟩ : syracuseStep 1805381 = 338509) (by norm_num)
theorem B6261877 : Blo 802343 6261877 := bbase (se 5 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 6261877 = 587051) (by norm_num)
theorem B2034821 : Blo 802343 2034821 := bbase (se 4 (by rfl) ⟨190764, by rfl⟩ : syracuseStep 2034821 = 381529) (by norm_num)
theorem B1805453 : Blo 802343 1805453 := bbase (se 3 (by rfl) ⟨338522, by rfl⟩ : syracuseStep 1805453 = 677045) (by norm_num)
theorem B2755781 : Blo 802343 2755781 := bbase (se 4 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 2755781 = 516709) (by norm_num)
theorem B2985157 : Blo 802343 2985157 := bbase (se 4 (by rfl) ⟨279858, by rfl⟩ : syracuseStep 2985157 = 559717) (by norm_num)
theorem B1019081 : Blo 802343 1019081 := bbase (se 2 (by rfl) ⟨382155, by rfl⟩ : syracuseStep 1019081 = 764311) (by norm_num)
theorem B1805525 : Blo 802343 1805525 := bbase (se 7 (by rfl) ⟨21158, by rfl⟩ : syracuseStep 1805525 = 42317) (by norm_num)
theorem B1019137 : Blo 802343 1019137 := bbase (se 2 (by rfl) ⟨382176, by rfl⟩ : syracuseStep 1019137 = 764353) (by norm_num)
theorem B3673349 : Blo 802343 3673349 := bbase (se 4 (by rfl) ⟨344376, by rfl⟩ : syracuseStep 3673349 = 688753) (by norm_num)
theorem B1805597 : Blo 802343 1805597 := bbase (se 3 (by rfl) ⟨338549, by rfl⟩ : syracuseStep 1805597 = 677099) (by norm_num)
theorem B1019233 : Blo 802343 1019233 := bbase (se 2 (by rfl) ⟨382212, by rfl⟩ : syracuseStep 1019233 = 764425) (by norm_num)
theorem B1805669 : Blo 802343 1805669 := bbase (se 4 (by rfl) ⟨169281, by rfl⟩ : syracuseStep 1805669 = 338563) (by norm_num)
theorem B1805741 : Blo 802343 1805741 := bbase (se 3 (by rfl) ⟨338576, by rfl⟩ : syracuseStep 1805741 = 677153) (by norm_num)
theorem B1084853 : Blo 802343 1084853 := bbase (se 5 (by rfl) ⟨50852, by rfl⟩ : syracuseStep 1084853 = 101705) (by norm_num)
theorem B2035165 : Blo 802343 2035165 := bbase (se 3 (by rfl) ⟨381593, by rfl⟩ : syracuseStep 2035165 = 763187) (by norm_num)
theorem B1805813 : Blo 802343 1805813 := bbase (se 5 (by rfl) ⟨84647, by rfl⟩ : syracuseStep 1805813 = 169295) (by norm_num)
theorem B1609205 : Blo 802343 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B1019405 : Blo 802343 1019405 := bbase (se 3 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 1019405 = 382277) (by norm_num)
theorem B1805885 : Blo 802343 1805885 := bbase (se 3 (by rfl) ⟨338603, by rfl⟩ : syracuseStep 1805885 = 677207) (by norm_num)
theorem B1019461 : Blo 802343 1019461 := bbase (se 4 (by rfl) ⟨95574, by rfl⟩ : syracuseStep 1019461 = 191149) (by norm_num)
theorem B1085005 : Blo 802343 1085005 := bbase (se 3 (by rfl) ⟨203438, by rfl⟩ : syracuseStep 1085005 = 406877) (by norm_num)
theorem B2035277 : Blo 802343 2035277 := bbase (se 3 (by rfl) ⟨381614, by rfl⟩ : syracuseStep 2035277 = 763229) (by norm_num)
theorem B1805957 : Blo 802343 1805957 := bbase (se 4 (by rfl) ⟨169308, by rfl⟩ : syracuseStep 1805957 = 338617) (by norm_num)
theorem B1019557 : Blo 802343 1019557 := bbase (se 4 (by rfl) ⟨95583, by rfl⟩ : syracuseStep 1019557 = 191167) (by norm_num)
theorem B1806029 : Blo 802343 1806029 := bbase (se 3 (by rfl) ⟨338630, by rfl⟩ : syracuseStep 1806029 = 677261) (by norm_num)
theorem B1412813 : Blo 802343 1412813 := bbase (se 3 (by rfl) ⟨264902, by rfl⟩ : syracuseStep 1412813 = 529805) (by norm_num)
theorem B2035469 : Blo 802343 2035469 := bbase (se 3 (by rfl) ⟨381650, by rfl⟩ : syracuseStep 2035469 = 763301) (by norm_num)
theorem B1806101 : Blo 802343 1806101 := bbase (se 6 (by rfl) ⟨42330, by rfl⟩ : syracuseStep 1806101 = 84661) (by norm_num)
theorem B1019729 : Blo 802343 1019729 := bbase (se 2 (by rfl) ⟨382398, by rfl⟩ : syracuseStep 1019729 = 764797) (by norm_num)
theorem B1806173 : Blo 802343 1806173 := bbase (se 3 (by rfl) ⟨338657, by rfl⟩ : syracuseStep 1806173 = 677315) (by norm_num)
theorem B1019785 : Blo 802343 1019785 := bbase (se 2 (by rfl) ⟨382419, by rfl⟩ : syracuseStep 1019785 = 764839) (by norm_num)
theorem B1806245 : Blo 802343 1806245 := bbase (se 4 (by rfl) ⟨169335, by rfl⟩ : syracuseStep 1806245 = 338671) (by norm_num)
theorem B1019881 : Blo 802343 1019881 := bbase (se 2 (by rfl) ⟨382455, by rfl⟩ : syracuseStep 1019881 = 764911) (by norm_num)
theorem B1806317 : Blo 802343 1806317 := bbase (se 3 (by rfl) ⟨338684, by rfl⟩ : syracuseStep 1806317 = 677369) (by norm_num)
theorem B4067333 : Blo 802343 4067333 := bbase (se 4 (by rfl) ⟨381312, by rfl⟩ : syracuseStep 4067333 = 762625) (by norm_num)
theorem B1806389 : Blo 802343 1806389 := bbase (se 5 (by rfl) ⟨84674, by rfl⟩ : syracuseStep 1806389 = 169349) (by norm_num)
theorem B5509205 : Blo 802343 5509205 := bbase (se 8 (by rfl) ⟨32280, by rfl⟩ : syracuseStep 5509205 = 64561) (by norm_num)
theorem B2199653 : Blo 802343 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B2035813 : Blo 802343 2035813 := bbase (se 4 (by rfl) ⟨190857, by rfl⟩ : syracuseStep 2035813 = 381715) (by norm_num)
theorem B1806461 : Blo 802343 1806461 := bbase (se 3 (by rfl) ⟨338711, by rfl⟩ : syracuseStep 1806461 = 677423) (by norm_num)
theorem B1020053 : Blo 802343 1020053 := bbase (se 6 (by rfl) ⟨23907, by rfl⟩ : syracuseStep 1020053 = 47815) (by norm_num)
theorem B3051701 : Blo 802343 3051701 := bbase (se 5 (by rfl) ⟨143048, by rfl⟩ : syracuseStep 3051701 = 286097) (by norm_num)
theorem B2068661 : Blo 802343 2068661 := bbase (se 5 (by rfl) ⟨96968, by rfl⟩ : syracuseStep 2068661 = 193937) (by norm_num)
theorem B1675453 : Blo 802343 1675453 := bbase (se 3 (by rfl) ⟨314147, by rfl⟩ : syracuseStep 1675453 = 628295) (by norm_num)
theorem B1806533 : Blo 802343 1806533 := bbase (se 4 (by rfl) ⟨169362, by rfl⟩ : syracuseStep 1806533 = 338725) (by norm_num)
theorem B1020109 : Blo 802343 1020109 := bbase (se 3 (by rfl) ⟨191270, by rfl⟩ : syracuseStep 1020109 = 382541) (by norm_num)
theorem B2035925 : Blo 802343 2035925 := bbase (se 7 (by rfl) ⟨23858, by rfl⟩ : syracuseStep 2035925 = 47717) (by norm_num)
theorem B1806605 : Blo 802343 1806605 := bbase (se 3 (by rfl) ⟨338738, by rfl⟩ : syracuseStep 1806605 = 677477) (by norm_num)
theorem B12521749 : Blo 802343 12521749 := bbase (se 6 (by rfl) ⟨293478, by rfl⟩ : syracuseStep 12521749 = 586957) (by norm_num)
theorem B1020205 : Blo 802343 1020205 := bbase (se 3 (by rfl) ⟨191288, by rfl⟩ : syracuseStep 1020205 = 382577) (by norm_num)
theorem B1806677 : Blo 802343 1806677 := bbase (se 10 (by rfl) ⟨2646, by rfl⟩ : syracuseStep 1806677 = 5293) (by norm_num)
theorem B3871093 : Blo 802343 3871093 := bbase (se 5 (by rfl) ⟨181457, by rfl⟩ : syracuseStep 3871093 = 362915) (by norm_num)
theorem B2036117 : Blo 802343 2036117 := bbase (se 6 (by rfl) ⟨47721, by rfl⟩ : syracuseStep 2036117 = 95443) (by norm_num)
theorem B2068885 : Blo 802343 2068885 := bbase (se 6 (by rfl) ⟨48489, by rfl⟩ : syracuseStep 2068885 = 96979) (by norm_num)
theorem B1806749 : Blo 802343 1806749 := bbase (se 3 (by rfl) ⟨338765, by rfl⟩ : syracuseStep 1806749 = 677531) (by norm_num)
theorem B3051989 : Blo 802343 3051989 := bbase (se 7 (by rfl) ⟨35765, by rfl⟩ : syracuseStep 3051989 = 71531) (by norm_num)
theorem B1020377 : Blo 802343 1020377 := bbase (se 2 (by rfl) ⟨382641, by rfl⟩ : syracuseStep 1020377 = 765283) (by norm_num)
theorem B1806821 : Blo 802343 1806821 := bbase (se 4 (by rfl) ⟨169389, by rfl⟩ : syracuseStep 1806821 = 338779) (by norm_num)
theorem B1020433 : Blo 802343 1020433 := bbase (se 2 (by rfl) ⟨382662, by rfl⟩ : syracuseStep 1020433 = 765325) (by norm_num)
theorem B1806893 : Blo 802343 1806893 := bbase (se 3 (by rfl) ⟨338792, by rfl⟩ : syracuseStep 1806893 = 677585) (by norm_num)
theorem B1020529 : Blo 802343 1020529 := bbase (se 2 (by rfl) ⟨382698, by rfl⟩ : syracuseStep 1020529 = 765397) (by norm_num)
theorem B1806965 : Blo 802343 1806965 := bbase (se 5 (by rfl) ⟨84701, by rfl⟩ : syracuseStep 1806965 = 169403) (by norm_num)
theorem B1807037 : Blo 802343 1807037 := bbase (se 3 (by rfl) ⟨338819, by rfl⟩ : syracuseStep 1807037 = 677639) (by norm_num)
theorem B2036461 : Blo 802343 2036461 := bbase (se 3 (by rfl) ⟨381836, by rfl⟩ : syracuseStep 2036461 = 763673) (by norm_num)
theorem B1807109 : Blo 802343 1807109 := bbase (se 4 (by rfl) ⟨169416, by rfl⟩ : syracuseStep 1807109 = 338833) (by norm_num)
theorem B1676045 : Blo 802343 1676045 := bbase (se 3 (by rfl) ⟨314258, by rfl⟩ : syracuseStep 1676045 = 628517) (by norm_num)
theorem B7344917 : Blo 802343 7344917 := bbase (se 6 (by rfl) ⟨172146, by rfl⟩ : syracuseStep 7344917 = 344293) (by norm_num)
theorem B856877 : Blo 802343 856877 := bbase (se 3 (by rfl) ⟨160664, by rfl⟩ : syracuseStep 856877 = 321329) (by norm_num)
theorem B1807181 : Blo 802343 1807181 := bbase (se 3 (by rfl) ⟨338846, by rfl⟩ : syracuseStep 1807181 = 677693) (by norm_num)
theorem B2036573 : Blo 802343 2036573 := bbase (se 3 (by rfl) ⟨381857, by rfl⟩ : syracuseStep 2036573 = 763715) (by norm_num)
theorem B856937 : Blo 802343 856937 := bbase (se 2 (by rfl) ⟨321351, by rfl⟩ : syracuseStep 856937 = 642703) (by norm_num)
theorem B1807253 : Blo 802343 1807253 := bbase (se 6 (by rfl) ⟨42357, by rfl⟩ : syracuseStep 1807253 = 84715) (by norm_num)
theorem B1807325 : Blo 802343 1807325 := bbase (se 3 (by rfl) ⟨338873, by rfl⟩ : syracuseStep 1807325 = 677747) (by norm_num)
theorem B857065 : Blo 802343 857065 := bbase (se 2 (by rfl) ⟨321399, by rfl⟩ : syracuseStep 857065 = 642799) (by norm_num)
theorem B2036765 : Blo 802343 2036765 := bbase (se 3 (by rfl) ⟨381893, by rfl⟩ : syracuseStep 2036765 = 763787) (by norm_num)
theorem B1807397 : Blo 802343 1807397 := bbase (se 4 (by rfl) ⟨169443, by rfl⟩ : syracuseStep 1807397 = 338887) (by norm_num)
theorem B1446989 : Blo 802343 1446989 := bbase (se 3 (by rfl) ⟨271310, by rfl⟩ : syracuseStep 1446989 = 542621) (by norm_num)
theorem B1807469 : Blo 802343 1807469 := bbase (se 3 (by rfl) ⟨338900, by rfl⟩ : syracuseStep 1807469 = 677801) (by norm_num)
theorem B1807541 : Blo 802343 1807541 := bbase (se 5 (by rfl) ⟨84728, by rfl⟩ : syracuseStep 1807541 = 169457) (by norm_num)
theorem B1807613 : Blo 802343 1807613 := bbase (se 3 (by rfl) ⟨338927, by rfl⟩ : syracuseStep 1807613 = 677855) (by norm_num)
theorem B4068629 : Blo 802343 4068629 := bbase (se 6 (by rfl) ⟨95358, by rfl⟩ : syracuseStep 4068629 = 190717) (by norm_num)
theorem B1807685 : Blo 802343 1807685 := bbase (se 4 (by rfl) ⟨169470, by rfl⟩ : syracuseStep 1807685 = 338941) (by norm_num)
theorem B2037109 : Blo 802343 2037109 := bbase (se 5 (by rfl) ⟨95489, by rfl⟩ : syracuseStep 2037109 = 190979) (by norm_num)
theorem B1807757 : Blo 802343 1807757 := bbase (se 3 (by rfl) ⟨338954, by rfl⟩ : syracuseStep 1807757 = 677909) (by norm_num)
theorem B857509 : Blo 802343 857509 := bbase (se 4 (by rfl) ⟨80391, by rfl⟩ : syracuseStep 857509 = 160783) (by norm_num)
theorem B1807829 : Blo 802343 1807829 := bbase (se 7 (by rfl) ⟨21185, by rfl⟩ : syracuseStep 1807829 = 42371) (by norm_num)
theorem B2037221 : Blo 802343 2037221 := bbase (se 4 (by rfl) ⟨190989, by rfl⟩ : syracuseStep 2037221 = 381979) (by norm_num)
theorem B1447445 : Blo 802343 1447445 := bbase (se 6 (by rfl) ⟨33924, by rfl⟩ : syracuseStep 1447445 = 67849) (by norm_num)
theorem B857629 : Blo 802343 857629 := bbase (se 3 (by rfl) ⟨160805, by rfl⟩ : syracuseStep 857629 = 321611) (by norm_num)
theorem B1807901 : Blo 802343 1807901 := bbase (se 3 (by rfl) ⟨338981, by rfl⟩ : syracuseStep 1807901 = 677963) (by norm_num)
theorem B1742429 : Blo 802343 1742429 := bbase (se 3 (by rfl) ⟨326705, by rfl⟩ : syracuseStep 1742429 = 653411) (by norm_num)
theorem B1807973 : Blo 802343 1807973 := bbase (se 4 (by rfl) ⟨169497, by rfl⟩ : syracuseStep 1807973 = 338995) (by norm_num)
theorem B3053173 : Blo 802343 3053173 := bbase (se 5 (by rfl) ⟨143117, by rfl⟩ : syracuseStep 3053173 = 286235) (by norm_num)
theorem B2037413 : Blo 802343 2037413 := bbase (se 4 (by rfl) ⟨191007, by rfl⟩ : syracuseStep 2037413 = 382015) (by norm_num)
theorem B1808045 : Blo 802343 1808045 := bbase (se 3 (by rfl) ⟨339008, by rfl⟩ : syracuseStep 1808045 = 678017) (by norm_num)
theorem B1808117 : Blo 802343 1808117 := bbase (se 5 (by rfl) ⟨84755, by rfl⟩ : syracuseStep 1808117 = 169511) (by norm_num)
theorem B6100757 : Blo 802343 6100757 := bbase (se 6 (by rfl) ⟨142986, by rfl⟩ : syracuseStep 6100757 = 285973) (by norm_num)
theorem B857881 : Blo 802343 857881 := bbase (se 2 (by rfl) ⟨321705, by rfl⟩ : syracuseStep 857881 = 643411) (by norm_num)
theorem B857885 : Blo 802343 857885 := bbase (se 3 (by rfl) ⟨160853, by rfl⟩ : syracuseStep 857885 = 321707) (by norm_num)
theorem B1808189 : Blo 802343 1808189 := bbase (se 3 (by rfl) ⟨339035, by rfl⟩ : syracuseStep 1808189 = 678071) (by norm_num)
theorem B2201413 : Blo 802343 2201413 := bbase (se 4 (by rfl) ⟨206382, by rfl⟩ : syracuseStep 2201413 = 412765) (by norm_num)
theorem B1808261 : Blo 802343 1808261 := bbase (se 4 (by rfl) ⟨169524, by rfl⟩ : syracuseStep 1808261 = 339049) (by norm_num)
theorem B3053477 : Blo 802343 3053477 := bbase (se 4 (by rfl) ⟨286263, by rfl⟩ : syracuseStep 3053477 = 572527) (by norm_num)
theorem B1808333 : Blo 802343 1808333 := bbase (se 3 (by rfl) ⟨339062, by rfl⟩ : syracuseStep 1808333 = 678125) (by norm_num)
theorem B2037757 : Blo 802343 2037757 := bbase (se 3 (by rfl) ⟨382079, by rfl⟩ : syracuseStep 2037757 = 764159) (by norm_num)
theorem B1808405 : Blo 802343 1808405 := bbase (se 6 (by rfl) ⟨42384, by rfl⟩ : syracuseStep 1808405 = 84769) (by norm_num)
theorem B1808477 : Blo 802343 1808477 := bbase (se 3 (by rfl) ⟨339089, by rfl⟩ : syracuseStep 1808477 = 678179) (by norm_num)
theorem B2037869 : Blo 802343 2037869 := bbase (se 3 (by rfl) ⟨382100, by rfl⟩ : syracuseStep 2037869 = 764201) (by norm_num)
theorem B1808549 : Blo 802343 1808549 := bbase (se 4 (by rfl) ⟨169551, by rfl⟩ : syracuseStep 1808549 = 339103) (by norm_num)
theorem B1808621 : Blo 802343 1808621 := bbase (se 3 (by rfl) ⟨339116, by rfl⟩ : syracuseStep 1808621 = 678233) (by norm_num)
theorem B2038061 : Blo 802343 2038061 := bbase (se 3 (by rfl) ⟨382136, by rfl⟩ : syracuseStep 2038061 = 764273) (by norm_num)
theorem B1808693 : Blo 802343 1808693 := bbase (se 5 (by rfl) ⟨84782, by rfl⟩ : syracuseStep 1808693 = 169565) (by norm_num)
theorem B858449 : Blo 802343 858449 := bbase (se 2 (by rfl) ⟨321918, by rfl⟩ : syracuseStep 858449 = 643837) (by norm_num)
theorem B1808765 : Blo 802343 1808765 := bbase (se 3 (by rfl) ⟨339143, by rfl⟩ : syracuseStep 1808765 = 678287) (by norm_num)
theorem B15702421 : Blo 802343 15702421 := bbase (se 6 (by rfl) ⟨368025, by rfl⟩ : syracuseStep 15702421 = 736051) (by norm_num)
theorem B1808837 : Blo 802343 1808837 := bbase (se 4 (by rfl) ⟨169578, by rfl⟩ : syracuseStep 1808837 = 339157) (by norm_num)
theorem B2169317 : Blo 802343 2169317 := bbase (se 4 (by rfl) ⟨203373, by rfl⟩ : syracuseStep 2169317 = 406747) (by norm_num)
theorem B1808909 : Blo 802343 1808909 := bbase (se 3 (by rfl) ⟨339170, by rfl⟩ : syracuseStep 1808909 = 678341) (by norm_num)
theorem B858637 : Blo 802343 858637 := bbase (se 3 (by rfl) ⟨160994, by rfl⟩ : syracuseStep 858637 = 321989) (by norm_num)
theorem B9148949 : Blo 802343 9148949 := bbase (se 6 (by rfl) ⟨214428, by rfl⟩ : syracuseStep 9148949 = 428857) (by norm_num)
theorem B4069925 : Blo 802343 4069925 := bbase (se 4 (by rfl) ⟨381555, by rfl⟩ : syracuseStep 4069925 = 763111) (by norm_num)
theorem B1808981 : Blo 802343 1808981 := bbase (se 8 (by rfl) ⟨10599, by rfl⟩ : syracuseStep 1808981 = 21199) (by norm_num)
theorem B2038405 : Blo 802343 2038405 := bbase (se 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) (by norm_num)
theorem B1809053 : Blo 802343 1809053 := bbase (se 3 (by rfl) ⟨339197, by rfl⟩ : syracuseStep 1809053 = 678395) (by norm_num)
theorem B3676853 : Blo 802343 3676853 := bbase (se 5 (by rfl) ⟨172352, by rfl⟩ : syracuseStep 3676853 = 344705) (by norm_num)
theorem B1809125 : Blo 802343 1809125 := bbase (se 4 (by rfl) ⟨169605, by rfl⟩ : syracuseStep 1809125 = 339211) (by norm_num)
theorem B2038517 : Blo 802343 2038517 := bbase (se 5 (by rfl) ⟨95555, by rfl⟩ : syracuseStep 2038517 = 191111) (by norm_num)
theorem B1809197 : Blo 802343 1809197 := bbase (se 3 (by rfl) ⟨339224, by rfl⟩ : syracuseStep 1809197 = 678449) (by norm_num)
theorem B1809269 : Blo 802343 1809269 := bbase (se 5 (by rfl) ⟨84809, by rfl⟩ : syracuseStep 1809269 = 169619) (by norm_num)
theorem B2038709 : Blo 802343 2038709 := bbase (se 5 (by rfl) ⟨95564, by rfl⟩ : syracuseStep 2038709 = 191129) (by norm_num)
theorem B1809341 : Blo 802343 1809341 := bbase (se 3 (by rfl) ⟨339251, by rfl⟩ : syracuseStep 1809341 = 678503) (by norm_num)
theorem B1448965 : Blo 802343 1448965 := bbase (se 4 (by rfl) ⟨135840, by rfl⟩ : syracuseStep 1448965 = 271681) (by norm_num)
theorem B1809413 : Blo 802343 1809413 := bbase (se 4 (by rfl) ⟨169632, by rfl⟩ : syracuseStep 1809413 = 339265) (by norm_num)
theorem B3873845 : Blo 802343 3873845 := bbase (se 5 (by rfl) ⟨181586, by rfl⟩ : syracuseStep 3873845 = 363173) (by norm_num)
theorem B1809485 : Blo 802343 1809485 := bbase (se 3 (by rfl) ⟨339278, by rfl⟩ : syracuseStep 1809485 = 678557) (by norm_num)
theorem B1809557 : Blo 802343 1809557 := bbase (se 6 (by rfl) ⟨42411, by rfl⟩ : syracuseStep 1809557 = 84823) (by norm_num)
theorem B1809629 : Blo 802343 1809629 := bbase (se 3 (by rfl) ⟨339305, by rfl⟩ : syracuseStep 1809629 = 678611) (by norm_num)
theorem B2039053 : Blo 802343 2039053 := bbase (se 3 (by rfl) ⟨382322, by rfl⟩ : syracuseStep 2039053 = 764645) (by norm_num)
theorem B1809701 : Blo 802343 1809701 := bbase (se 4 (by rfl) ⟨169659, by rfl⟩ : syracuseStep 1809701 = 339319) (by norm_num)
theorem B859457 : Blo 802343 859457 := bbase (se 2 (by rfl) ⟨322296, by rfl⟩ : syracuseStep 859457 = 644593) (by norm_num)
theorem B1809773 : Blo 802343 1809773 := bbase (se 3 (by rfl) ⟨339332, by rfl⟩ : syracuseStep 1809773 = 678665) (by norm_num)
theorem B2039165 : Blo 802343 2039165 := bbase (se 3 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 2039165 = 764687) (by norm_num)
theorem B1285541 : Blo 802343 1285541 := bbase (se 4 (by rfl) ⟨120519, by rfl⟩ : syracuseStep 1285541 = 241039) (by norm_num)
theorem B1809845 : Blo 802343 1809845 := bbase (se 5 (by rfl) ⟨84836, by rfl⟩ : syracuseStep 1809845 = 169673) (by norm_num)
theorem B1809917 : Blo 802343 1809917 := bbase (se 3 (by rfl) ⟨339359, by rfl⟩ : syracuseStep 1809917 = 678719) (by norm_num)
theorem B2039357 : Blo 802343 2039357 := bbase (se 3 (by rfl) ⟨382379, by rfl⟩ : syracuseStep 2039357 = 764759) (by norm_num)
theorem B1809989 : Blo 802343 1809989 := bbase (se 4 (by rfl) ⟨169686, by rfl⟩ : syracuseStep 1809989 = 339373) (by norm_num)
theorem B1810061 : Blo 802343 1810061 := bbase (se 3 (by rfl) ⟨339386, by rfl⟩ : syracuseStep 1810061 = 678773) (by norm_num)
theorem B1089221 : Blo 802343 1089221 := bbase (se 4 (by rfl) ⟨102114, by rfl⟩ : syracuseStep 1089221 = 204229) (by norm_num)
theorem B1810133 : Blo 802343 1810133 := bbase (se 7 (by rfl) ⟨21212, by rfl⟩ : syracuseStep 1810133 = 42425) (by norm_num)
theorem B859901 : Blo 802343 859901 := bbase (se 3 (by rfl) ⟨161231, by rfl⟩ : syracuseStep 859901 = 322463) (by norm_num)
theorem B1810205 : Blo 802343 1810205 := bbase (se 3 (by rfl) ⟨339413, by rfl⟩ : syracuseStep 1810205 = 678827) (by norm_num)
theorem B1449757 : Blo 802343 1449757 := bbase (se 3 (by rfl) ⟨271829, by rfl⟩ : syracuseStep 1449757 = 543659) (by norm_num)
theorem B4071221 : Blo 802343 4071221 := bbase (se 5 (by rfl) ⟨190838, by rfl⟩ : syracuseStep 4071221 = 381677) (by norm_num)
theorem B1810277 : Blo 802343 1810277 := bbase (se 4 (by rfl) ⟨169713, by rfl⟩ : syracuseStep 1810277 = 339427) (by norm_num)
theorem B2039701 : Blo 802343 2039701 := bbase (se 6 (by rfl) ⟨47805, by rfl⟩ : syracuseStep 2039701 = 95611) (by norm_num)
theorem B1810349 : Blo 802343 1810349 := bbase (se 3 (by rfl) ⟨339440, by rfl⟩ : syracuseStep 1810349 = 678881) (by norm_num)
theorem B5152693 : Blo 802343 5152693 := bbase (se 5 (by rfl) ⟨241532, by rfl⟩ : syracuseStep 5152693 = 483065) (by norm_num)
theorem B1220557 : Blo 802343 1220557 := bbase (se 3 (by rfl) ⟨228854, by rfl⟩ : syracuseStep 1220557 = 457709) (by norm_num)
theorem B3055589 : Blo 802343 3055589 := bbase (se 4 (by rfl) ⟨286461, by rfl⟩ : syracuseStep 3055589 = 572923) (by norm_num)
theorem B1810421 : Blo 802343 1810421 := bbase (se 5 (by rfl) ⟨84863, by rfl⟩ : syracuseStep 1810421 = 169727) (by norm_num)
theorem B860149 : Blo 802343 860149 := bbase (se 5 (by rfl) ⟨40319, by rfl⟩ : syracuseStep 860149 = 80639) (by norm_num)
theorem B2039813 : Blo 802343 2039813 := bbase (se 4 (by rfl) ⟨191232, by rfl⟩ : syracuseStep 2039813 = 382465) (by norm_num)
theorem B1450037 : Blo 802343 1450037 := bbase (se 5 (by rfl) ⟨67970, by rfl⟩ : syracuseStep 1450037 = 135941) (by norm_num)
theorem B1810493 : Blo 802343 1810493 := bbase (se 3 (by rfl) ⟨339467, by rfl⟩ : syracuseStep 1810493 = 678935) (by norm_num)
theorem B1810565 : Blo 802343 1810565 := bbase (se 4 (by rfl) ⟨169740, by rfl⟩ : syracuseStep 1810565 = 339481) (by norm_num)
theorem B1450133 : Blo 802343 1450133 := bbase (se 6 (by rfl) ⟨33987, by rfl⟩ : syracuseStep 1450133 = 67975) (by norm_num)
theorem B2040005 : Blo 802343 2040005 := bbase (se 4 (by rfl) ⟨191250, by rfl⟩ : syracuseStep 2040005 = 382501) (by norm_num)
theorem B1810637 : Blo 802343 1810637 := bbase (se 3 (by rfl) ⟨339494, by rfl⟩ : syracuseStep 1810637 = 678989) (by norm_num)
theorem B3055877 : Blo 802343 3055877 := bbase (se 4 (by rfl) ⟨286488, by rfl⟩ : syracuseStep 3055877 = 572977) (by norm_num)
theorem B1810709 : Blo 802343 1810709 := bbase (se 6 (by rfl) ⟨42438, by rfl⟩ : syracuseStep 1810709 = 84877) (by norm_num)
theorem B1810781 : Blo 802343 1810781 := bbase (se 3 (by rfl) ⟨339521, by rfl⟩ : syracuseStep 1810781 = 679043) (by norm_num)
theorem B2892133 : Blo 802343 2892133 := bbase (se 4 (by rfl) ⟨271137, by rfl⟩ : syracuseStep 2892133 = 542275) (by norm_num)
theorem B1286533 : Blo 802343 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B1810853 : Blo 802343 1810853 := bbase (se 4 (by rfl) ⟨169767, by rfl⟩ : syracuseStep 1810853 = 339535) (by norm_num)
theorem B860581 : Blo 802343 860581 := bbase (se 4 (by rfl) ⟨80679, by rfl⟩ : syracuseStep 860581 = 161359) (by norm_num)
theorem B1810925 : Blo 802343 1810925 := bbase (se 3 (by rfl) ⟨339548, by rfl⟩ : syracuseStep 1810925 = 679097) (by norm_num)
theorem B860653 : Blo 802343 860653 := bbase (se 3 (by rfl) ⟨161372, by rfl⟩ : syracuseStep 860653 = 322745) (by norm_num)
theorem B2040349 : Blo 802343 2040349 := bbase (se 3 (by rfl) ⟨382565, by rfl⟩ : syracuseStep 2040349 = 765131) (by norm_num)
theorem B1810997 : Blo 802343 1810997 := bbase (se 5 (by rfl) ⟨84890, by rfl⟩ : syracuseStep 1810997 = 169781) (by norm_num)
theorem B1811069 : Blo 802343 1811069 := bbase (se 3 (by rfl) ⟨339575, by rfl⟩ : syracuseStep 1811069 = 679151) (by norm_num)
theorem B2040461 : Blo 802343 2040461 := bbase (se 3 (by rfl) ⟨382586, by rfl⟩ : syracuseStep 2040461 = 765173) (by norm_num)
theorem B1548973 : Blo 802343 1548973 := bbase (se 3 (by rfl) ⟨290432, by rfl⟩ : syracuseStep 1548973 = 580865) (by norm_num)
theorem B1811141 : Blo 802343 1811141 := bbase (se 4 (by rfl) ⟨169794, by rfl⟩ : syracuseStep 1811141 = 339589) (by norm_num)
theorem B1811213 : Blo 802343 1811213 := bbase (se 3 (by rfl) ⟨339602, by rfl⟩ : syracuseStep 1811213 = 679205) (by norm_num)
theorem B2040653 : Blo 802343 2040653 := bbase (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) (by norm_num)
theorem B1811285 : Blo 802343 1811285 := bbase (se 9 (by rfl) ⟨5306, by rfl⟩ : syracuseStep 1811285 = 10613) (by norm_num)
theorem B861025 : Blo 802343 861025 := bbase (se 2 (by rfl) ⟨322884, by rfl⟩ : syracuseStep 861025 = 645769) (by norm_num)
theorem B1450853 : Blo 802343 1450853 := bbase (se 4 (by rfl) ⟨136017, by rfl⟩ : syracuseStep 1450853 = 272035) (by norm_num)
theorem B1811357 : Blo 802343 1811357 := bbase (se 3 (by rfl) ⟨339629, by rfl⟩ : syracuseStep 1811357 = 679259) (by norm_num)
theorem B1811429 : Blo 802343 1811429 := bbase (se 4 (by rfl) ⟨169821, by rfl⟩ : syracuseStep 1811429 = 339643) (by norm_num)
theorem B1287181 : Blo 802343 1287181 := bbase (se 3 (by rfl) ⟨241346, by rfl⟩ : syracuseStep 1287181 = 482693) (by norm_num)
theorem B1811501 : Blo 802343 1811501 := bbase (se 3 (by rfl) ⟨339656, by rfl⟩ : syracuseStep 1811501 = 679313) (by norm_num)
theorem B4072517 : Blo 802343 4072517 := bbase (se 4 (by rfl) ⟨381798, by rfl⟩ : syracuseStep 4072517 = 763597) (by norm_num)
theorem B4891765 : Blo 802343 4891765 := bbase (se 5 (by rfl) ⟨229301, by rfl⟩ : syracuseStep 4891765 = 458603) (by norm_num)
theorem B1811573 : Blo 802343 1811573 := bbase (se 5 (by rfl) ⟨84917, by rfl⟩ : syracuseStep 1811573 = 169835) (by norm_num)
theorem B2040997 : Blo 802343 2040997 := bbase (se 4 (by rfl) ⟨191343, by rfl⟩ : syracuseStep 2040997 = 382687) (by norm_num)
theorem B1811645 : Blo 802343 1811645 := bbase (se 3 (by rfl) ⟨339683, by rfl⟩ : syracuseStep 1811645 = 679367) (by norm_num)
theorem B1811717 : Blo 802343 1811717 := bbase (se 4 (by rfl) ⟨169848, by rfl⟩ : syracuseStep 1811717 = 339697) (by norm_num)
theorem B1811789 : Blo 802343 1811789 := bbase (se 3 (by rfl) ⟨339710, by rfl⟩ : syracuseStep 1811789 = 679421) (by norm_num)
theorem B1811861 : Blo 802343 1811861 := bbase (se 6 (by rfl) ⟨42465, by rfl⟩ : syracuseStep 1811861 = 84931) (by norm_num)
theorem B3057061 : Blo 802343 3057061 := bbase (se 4 (by rfl) ⟨286599, by rfl⟩ : syracuseStep 3057061 = 573199) (by norm_num)
theorem B1811933 : Blo 802343 1811933 := bbase (se 3 (by rfl) ⟨339737, by rfl⟩ : syracuseStep 1811933 = 679475) (by norm_num)
theorem B1812005 : Blo 802343 1812005 := bbase (se 4 (by rfl) ⟨169875, by rfl⟩ : syracuseStep 1812005 = 339751) (by norm_num)
theorem B1812077 : Blo 802343 1812077 := bbase (se 3 (by rfl) ⟨339764, by rfl⟩ : syracuseStep 1812077 = 679529) (by norm_num)
theorem B1812149 : Blo 802343 1812149 := bbase (se 5 (by rfl) ⟨84944, by rfl⟩ : syracuseStep 1812149 = 169889) (by norm_num)
theorem B3057365 : Blo 802343 3057365 := bbase (se 7 (by rfl) ⟨35828, by rfl⟩ : syracuseStep 3057365 = 71657) (by norm_num)
theorem B2041573 : Blo 802343 2041573 := bbase (se 4 (by rfl) ⟨191397, by rfl⟩ : syracuseStep 2041573 = 382795) (by norm_num)
theorem B1812221 : Blo 802343 1812221 := bbase (se 3 (by rfl) ⟨339791, by rfl⟩ : syracuseStep 1812221 = 679583) (by norm_num)
theorem B1812293 : Blo 802343 1812293 := bbase (se 4 (by rfl) ⟨169902, by rfl⟩ : syracuseStep 1812293 = 339805) (by norm_num)
theorem B1812365 : Blo 802343 1812365 := bbase (se 3 (by rfl) ⟨339818, by rfl⟩ : syracuseStep 1812365 = 679637) (by norm_num)
theorem B1288109 : Blo 802343 1288109 := bbase (se 3 (by rfl) ⟨241520, by rfl⟩ : syracuseStep 1288109 = 483041) (by norm_num)
theorem B1812437 : Blo 802343 1812437 := bbase (se 7 (by rfl) ⟨21239, by rfl⟩ : syracuseStep 1812437 = 42479) (by norm_num)
theorem B1812509 : Blo 802343 1812509 := bbase (se 3 (by rfl) ⟨339845, by rfl⟩ : syracuseStep 1812509 = 679691) (by norm_num)
theorem B1812581 : Blo 802343 1812581 := bbase (se 4 (by rfl) ⟨169929, by rfl⟩ : syracuseStep 1812581 = 339859) (by norm_num)
theorem B1714301 : Blo 802343 1714301 := bbase (se 3 (by rfl) ⟨321431, by rfl⟩ : syracuseStep 1714301 = 642863) (by norm_num)
theorem B1812653 : Blo 802343 1812653 := bbase (se 3 (by rfl) ⟨339872, by rfl⟩ : syracuseStep 1812653 = 679745) (by norm_num)
theorem B1714421 : Blo 802343 1714421 := bbase (se 5 (by rfl) ⟨80363, by rfl⟩ : syracuseStep 1714421 = 160727) (by norm_num)
theorem B1812725 : Blo 802343 1812725 := bbase (se 5 (by rfl) ⟨84971, by rfl⟩ : syracuseStep 1812725 = 169943) (by norm_num)
theorem B1353989 : Blo 802343 1353989 := bbase (se 4 (by rfl) ⟨126936, by rfl⟩ : syracuseStep 1353989 = 253873) (by norm_num)
theorem B1812797 : Blo 802343 1812797 := bbase (se 3 (by rfl) ⟨339899, by rfl⟩ : syracuseStep 1812797 = 679799) (by norm_num)
theorem B4073813 : Blo 802343 4073813 := bbase (se 10 (by rfl) ⟨5967, by rfl⟩ : syracuseStep 4073813 = 11935) (by norm_num)
theorem B1288565 : Blo 802343 1288565 := bbase (se 5 (by rfl) ⟨60401, by rfl⟩ : syracuseStep 1288565 = 120803) (by norm_num)
theorem B1354117 : Blo 802343 1354117 := bbase (se 4 (by rfl) ⟨126948, by rfl⟩ : syracuseStep 1354117 = 253897) (by norm_num)
theorem B1812869 : Blo 802343 1812869 := bbase (se 4 (by rfl) ⟨169956, by rfl⟩ : syracuseStep 1812869 = 339913) (by norm_num)
theorem B1812941 : Blo 802343 1812941 := bbase (se 3 (by rfl) ⟨339926, by rfl⟩ : syracuseStep 1812941 = 679853) (by norm_num)
theorem B1354205 : Blo 802343 1354205 := bbase (se 3 (by rfl) ⟨253913, by rfl⟩ : syracuseStep 1354205 = 507827) (by norm_num)
theorem B1813013 : Blo 802343 1813013 := bbase (se 6 (by rfl) ⟨42492, by rfl⟩ : syracuseStep 1813013 = 84985) (by norm_num)
theorem B1452613 : Blo 802343 1452613 := bbase (se 4 (by rfl) ⟨136182, by rfl⟩ : syracuseStep 1452613 = 272365) (by norm_num)
theorem B1354333 : Blo 802343 1354333 := bbase (se 3 (by rfl) ⟨253937, by rfl⟩ : syracuseStep 1354333 = 507875) (by norm_num)
theorem B1813085 : Blo 802343 1813085 := bbase (se 3 (by rfl) ⟨339953, by rfl⟩ : syracuseStep 1813085 = 679907) (by norm_num)
theorem B1813157 : Blo 802343 1813157 := bbase (se 4 (by rfl) ⟨169983, by rfl⟩ : syracuseStep 1813157 = 339967) (by norm_num)
theorem B1354421 : Blo 802343 1354421 := bbase (se 5 (by rfl) ⟨63488, by rfl⟩ : syracuseStep 1354421 = 126977) (by norm_num)
theorem B1452749 : Blo 802343 1452749 := bbase (se 3 (by rfl) ⟨272390, by rfl⟩ : syracuseStep 1452749 = 544781) (by norm_num)
theorem B1813229 : Blo 802343 1813229 := bbase (se 3 (by rfl) ⟨339980, by rfl⟩ : syracuseStep 1813229 = 679961) (by norm_num)
theorem B1452829 : Blo 802343 1452829 := bbase (se 3 (by rfl) ⟨272405, by rfl⟩ : syracuseStep 1452829 = 544811) (by norm_num)
theorem B1354549 : Blo 802343 1354549 := bbase (se 5 (by rfl) ⟨63494, by rfl⟩ : syracuseStep 1354549 = 126989) (by norm_num)
theorem B1813301 : Blo 802343 1813301 := bbase (se 5 (by rfl) ⟨84998, by rfl⟩ : syracuseStep 1813301 = 169997) (by norm_num)
theorem B1715053 : Blo 802343 1715053 := bbase (se 3 (by rfl) ⟨321572, by rfl⟩ : syracuseStep 1715053 = 643145) (by norm_num)
theorem B1813373 : Blo 802343 1813373 := bbase (se 3 (by rfl) ⟨340007, by rfl⟩ : syracuseStep 1813373 = 680015) (by norm_num)
theorem B1354637 : Blo 802343 1354637 := bbase (se 3 (by rfl) ⟨253994, by rfl⟩ : syracuseStep 1354637 = 507989) (by norm_num)
theorem B1813445 : Blo 802343 1813445 := bbase (se 4 (by rfl) ⟨170010, by rfl⟩ : syracuseStep 1813445 = 340021) (by norm_num)
theorem B1354765 : Blo 802343 1354765 := bbase (se 3 (by rfl) ⟨254018, by rfl⟩ : syracuseStep 1354765 = 508037) (by norm_num)
theorem B1813517 : Blo 802343 1813517 := bbase (se 3 (by rfl) ⟨340034, by rfl⟩ : syracuseStep 1813517 = 680069) (by norm_num)
theorem B1813589 : Blo 802343 1813589 := bbase (se 8 (by rfl) ⟨10626, by rfl⟩ : syracuseStep 1813589 = 21253) (by norm_num)
theorem B1354853 : Blo 802343 1354853 := bbase (se 4 (by rfl) ⟨127017, by rfl⟩ : syracuseStep 1354853 = 254035) (by norm_num)
theorem B1813661 : Blo 802343 1813661 := bbase (se 3 (by rfl) ⟨340061, by rfl⟩ : syracuseStep 1813661 = 680123) (by norm_num)
theorem B1354981 : Blo 802343 1354981 := bbase (se 4 (by rfl) ⟨127029, by rfl⟩ : syracuseStep 1354981 = 254059) (by norm_num)
theorem B1813733 : Blo 802343 1813733 := bbase (se 4 (by rfl) ⟨170037, by rfl⟩ : syracuseStep 1813733 = 340075) (by norm_num)
theorem B1813805 : Blo 802343 1813805 := bbase (se 3 (by rfl) ⟨340088, by rfl⟩ : syracuseStep 1813805 = 680177) (by norm_num)
theorem B1355069 : Blo 802343 1355069 := bbase (se 3 (by rfl) ⟨254075, by rfl⟩ : syracuseStep 1355069 = 508151) (by norm_num)
theorem B1813877 : Blo 802343 1813877 := bbase (se 5 (by rfl) ⟨85025, by rfl⟩ : syracuseStep 1813877 = 170051) (by norm_num)
theorem B1355197 : Blo 802343 1355197 := bbase (se 3 (by rfl) ⟨254099, by rfl⟩ : syracuseStep 1355197 = 508199) (by norm_num)
theorem B1813949 : Blo 802343 1813949 := bbase (se 3 (by rfl) ⟨340115, by rfl⟩ : syracuseStep 1813949 = 680231) (by norm_num)
theorem B1814021 : Blo 802343 1814021 := bbase (se 4 (by rfl) ⟨170064, by rfl⟩ : syracuseStep 1814021 = 340129) (by norm_num)
theorem B1355285 : Blo 802343 1355285 := bbase (se 6 (by rfl) ⟨31764, by rfl⟩ : syracuseStep 1355285 = 63529) (by norm_num)
theorem B1060417 : Blo 802343 1060417 := bbase (se 2 (by rfl) ⟨397656, by rfl⟩ : syracuseStep 1060417 = 795313) (by norm_num)
theorem B1814093 : Blo 802343 1814093 := bbase (se 3 (by rfl) ⟨340142, by rfl⟩ : syracuseStep 1814093 = 680285) (by norm_num)
theorem B4075109 : Blo 802343 4075109 := bbase (se 4 (by rfl) ⟨382041, by rfl⟩ : syracuseStep 4075109 = 764083) (by norm_num)
theorem B1355413 : Blo 802343 1355413 := bbase (se 6 (by rfl) ⟨31767, by rfl⟩ : syracuseStep 1355413 = 63535) (by norm_num)
theorem B1814165 : Blo 802343 1814165 := bbase (se 6 (by rfl) ⟨42519, by rfl⟩ : syracuseStep 1814165 = 85039) (by norm_num)
theorem B1814237 : Blo 802343 1814237 := bbase (se 3 (by rfl) ⟨340169, by rfl⟩ : syracuseStep 1814237 = 680339) (by norm_num)
theorem B1715941 : Blo 802343 1715941 := bbase (se 4 (by rfl) ⟨160869, by rfl⟩ : syracuseStep 1715941 = 321739) (by norm_num)
theorem B1355501 : Blo 802343 1355501 := bbase (se 3 (by rfl) ⟨254156, by rfl⟩ : syracuseStep 1355501 = 508313) (by norm_num)
theorem B1289981 : Blo 802343 1289981 := bbase (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) (by norm_num)
theorem B3059477 : Blo 802343 3059477 := bbase (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) (by norm_num)
theorem B1716061 : Blo 802343 1716061 := bbase (se 3 (by rfl) ⟨321761, by rfl⟩ : syracuseStep 1716061 = 643523) (by norm_num)
theorem B1355629 : Blo 802343 1355629 := bbase (se 3 (by rfl) ⟨254180, by rfl⟩ : syracuseStep 1355629 = 508361) (by norm_num)
theorem B3092357 : Blo 802343 3092357 := bbase (se 4 (by rfl) ⟨289908, by rfl⟩ : syracuseStep 3092357 = 579817) (by norm_num)
theorem B1355717 : Blo 802343 1355717 := bbase (se 4 (by rfl) ⟨127098, by rfl⟩ : syracuseStep 1355717 = 254197) (by norm_num)
theorem B1290205 : Blo 802343 1290205 := bbase (se 3 (by rfl) ⟨241913, by rfl⟩ : syracuseStep 1290205 = 483827) (by norm_num)
theorem B3059765 : Blo 802343 3059765 := bbase (se 5 (by rfl) ⟨143426, by rfl⟩ : syracuseStep 3059765 = 286853) (by norm_num)
theorem B1355845 : Blo 802343 1355845 := bbase (se 4 (by rfl) ⟨127110, by rfl⟩ : syracuseStep 1355845 = 254221) (by norm_num)
theorem B1716317 : Blo 802343 1716317 := bbase (se 3 (by rfl) ⟨321809, by rfl⟩ : syracuseStep 1716317 = 643619) (by norm_num)
theorem B1650797 : Blo 802343 1650797 := bbase (se 3 (by rfl) ⟨309524, by rfl⟩ : syracuseStep 1650797 = 619049) (by norm_num)
theorem B1355933 : Blo 802343 1355933 := bbase (se 3 (by rfl) ⟨254237, by rfl⟩ : syracuseStep 1355933 = 508475) (by norm_num)
theorem B1356061 : Blo 802343 1356061 := bbase (se 3 (by rfl) ⟨254261, by rfl⟩ : syracuseStep 1356061 = 508523) (by norm_num)
theorem B1356149 : Blo 802343 1356149 := bbase (se 5 (by rfl) ⟨63569, by rfl⟩ : syracuseStep 1356149 = 127139) (by norm_num)
theorem B1356277 : Blo 802343 1356277 := bbase (se 5 (by rfl) ⟨63575, by rfl⟩ : syracuseStep 1356277 = 127151) (by norm_num)
theorem B9777685 : Blo 802343 9777685 := bbase (se 6 (by rfl) ⟨229164, by rfl⟩ : syracuseStep 9777685 = 458329) (by norm_num)
theorem B1356365 : Blo 802343 1356365 := bbase (se 3 (by rfl) ⟨254318, by rfl⟩ : syracuseStep 1356365 = 508637) (by norm_num)
theorem B1225301 : Blo 802343 1225301 := bbase (se 8 (by rfl) ⟨7179, by rfl⟩ : syracuseStep 1225301 = 14359) (by norm_num)
theorem B1225325 : Blo 802343 1225325 := bbase (se 3 (by rfl) ⟨229748, by rfl⟩ : syracuseStep 1225325 = 459497) (by norm_num)
theorem B1356493 : Blo 802343 1356493 := bbase (se 3 (by rfl) ⟨254342, by rfl⟩ : syracuseStep 1356493 = 508685) (by norm_num)
theorem B1356581 : Blo 802343 1356581 := bbase (se 4 (by rfl) ⟨127179, by rfl⟩ : syracuseStep 1356581 = 254359) (by norm_num)
theorem B4076405 : Blo 802343 4076405 := bbase (se 5 (by rfl) ⟨191081, by rfl⟩ : syracuseStep 4076405 = 382163) (by norm_num)
theorem B1160101 : Blo 802343 1160101 := bbase (se 4 (by rfl) ⟨108759, by rfl⟩ : syracuseStep 1160101 = 217519) (by norm_num)
theorem B1356709 : Blo 802343 1356709 := bbase (se 4 (by rfl) ⟨127191, by rfl⟩ : syracuseStep 1356709 = 254383) (by norm_num)
theorem B1717205 : Blo 802343 1717205 := bbase (se 7 (by rfl) ⟨20123, by rfl⟩ : syracuseStep 1717205 = 40247) (by norm_num)
theorem B1356797 : Blo 802343 1356797 := bbase (se 3 (by rfl) ⟨254399, by rfl⟩ : syracuseStep 1356797 = 508799) (by norm_num)
theorem B1356925 : Blo 802343 1356925 := bbase (se 3 (by rfl) ⟨254423, by rfl⟩ : syracuseStep 1356925 = 508847) (by norm_num)
theorem B1717445 : Blo 802343 1717445 := bbase (se 4 (by rfl) ⟨161010, by rfl⟩ : syracuseStep 1717445 = 322021) (by norm_num)
theorem B1357013 : Blo 802343 1357013 := bbase (se 7 (by rfl) ⟨15902, by rfl⟩ : syracuseStep 1357013 = 31805) (by norm_num)
theorem B3060949 : Blo 802343 3060949 := bbase (se 7 (by rfl) ⟨35870, by rfl⟩ : syracuseStep 3060949 = 71741) (by norm_num)
theorem B1357141 : Blo 802343 1357141 := bbase (se 13 (by rfl) ⟨248, by rfl⟩ : syracuseStep 1357141 = 497) (by norm_num)
theorem B6108533 : Blo 802343 6108533 := bbase (se 5 (by rfl) ⟨286337, by rfl⟩ : syracuseStep 6108533 = 572675) (by norm_num)
theorem B1357229 : Blo 802343 1357229 := bbase (se 3 (by rfl) ⟨254480, by rfl⟩ : syracuseStep 1357229 = 508961) (by norm_num)
theorem B3061253 : Blo 802343 3061253 := bbase (se 4 (by rfl) ⟨286992, by rfl⟩ : syracuseStep 3061253 = 573985) (by norm_num)
theorem B1357357 : Blo 802343 1357357 := bbase (se 3 (by rfl) ⟨254504, by rfl⟩ : syracuseStep 1357357 = 509009) (by norm_num)
theorem B931385 : Blo 802343 931385 := bbase (se 2 (by rfl) ⟨349269, by rfl⟩ : syracuseStep 931385 = 698539) (by norm_num)
theorem B1652341 : Blo 802343 1652341 := bbase (se 5 (by rfl) ⟨77453, by rfl⟩ : syracuseStep 1652341 = 154907) (by norm_num)
theorem B1357445 : Blo 802343 1357445 := bbase (se 4 (by rfl) ⟨127260, by rfl⟩ : syracuseStep 1357445 = 254521) (by norm_num)
theorem B964237 : Blo 802343 964237 := bbase (se 3 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 964237 = 361589) (by norm_num)
theorem B1717949 : Blo 802343 1717949 := bbase (se 3 (by rfl) ⟨322115, by rfl⟩ : syracuseStep 1717949 = 644231) (by norm_num)
theorem B1717957 : Blo 802343 1717957 := bbase (se 4 (by rfl) ⟨161058, by rfl⟩ : syracuseStep 1717957 = 322117) (by norm_num)
theorem B2897669 : Blo 802343 2897669 := bbase (se 4 (by rfl) ⟨271656, by rfl⟩ : syracuseStep 2897669 = 543313) (by norm_num)
theorem B1357573 : Blo 802343 1357573 := bbase (se 4 (by rfl) ⟨127272, by rfl⟩ : syracuseStep 1357573 = 254545) (by norm_num)
theorem B3585877 : Blo 802343 3585877 := bbase (se 9 (by rfl) ⟨10505, by rfl⟩ : syracuseStep 3585877 = 21011) (by norm_num)
theorem B1357661 : Blo 802343 1357661 := bbase (se 3 (by rfl) ⟨254561, by rfl⟩ : syracuseStep 1357661 = 509123) (by norm_num)
theorem B2176885 : Blo 802343 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B1357789 : Blo 802343 1357789 := bbase (se 3 (by rfl) ⟨254585, by rfl⟩ : syracuseStep 1357789 = 509171) (by norm_num)
theorem B964621 : Blo 802343 964621 := bbase (se 3 (by rfl) ⟨180866, by rfl⟩ : syracuseStep 964621 = 361733) (by norm_num)
theorem B1357877 : Blo 802343 1357877 := bbase (se 5 (by rfl) ⟨63650, by rfl⟩ : syracuseStep 1357877 = 127301) (by norm_num)
theorem B8697941 : Blo 802343 8697941 := bbase (se 8 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 8697941 = 101929) (by norm_num)
theorem B5158997 : Blo 802343 5158997 := bbase (se 8 (by rfl) ⟨30228, by rfl⟩ : syracuseStep 5158997 = 60457) (by norm_num)
theorem B4077701 : Blo 802343 4077701 := bbase (se 4 (by rfl) ⟨382284, by rfl⟩ : syracuseStep 4077701 = 764569) (by norm_num)
theorem B1358005 : Blo 802343 1358005 := bbase (se 5 (by rfl) ⟨63656, by rfl⟩ : syracuseStep 1358005 = 127313) (by norm_num)
theorem B3258613 : Blo 802343 3258613 := bbase (se 5 (by rfl) ⟨152747, by rfl⟩ : syracuseStep 3258613 = 305495) (by norm_num)
theorem B1358093 : Blo 802343 1358093 := bbase (se 3 (by rfl) ⟨254642, by rfl⟩ : syracuseStep 1358093 = 509285) (by norm_num)
theorem B2177317 : Blo 802343 2177317 := bbase (se 4 (by rfl) ⟨204123, by rfl⟩ : syracuseStep 2177317 = 408247) (by norm_num)
theorem B1358221 : Blo 802343 1358221 := bbase (se 3 (by rfl) ⟨254666, by rfl⟩ : syracuseStep 1358221 = 509333) (by norm_num)
theorem B1358309 : Blo 802343 1358309 := bbase (se 4 (by rfl) ⟨127341, by rfl⟩ : syracuseStep 1358309 = 254683) (by norm_num)
theorem B2570773 : Blo 802343 2570773 := bbase (se 6 (by rfl) ⟨60252, by rfl⟩ : syracuseStep 2570773 = 120505) (by norm_num)
theorem B2177621 : Blo 802343 2177621 := bbase (se 8 (by rfl) ⟨12759, by rfl⟩ : syracuseStep 2177621 = 25519) (by norm_num)
theorem B1358437 : Blo 802343 1358437 := bbase (se 4 (by rfl) ⟨127353, by rfl⟩ : syracuseStep 1358437 = 254707) (by norm_num)
theorem B1358525 : Blo 802343 1358525 := bbase (se 3 (by rfl) ⟨254723, by rfl⟩ : syracuseStep 1358525 = 509447) (by norm_num)
theorem B1719085 : Blo 802343 1719085 := bbase (se 3 (by rfl) ⟨322328, by rfl⟩ : syracuseStep 1719085 = 644657) (by norm_num)
theorem B1358653 : Blo 802343 1358653 := bbase (se 3 (by rfl) ⟨254747, by rfl⟩ : syracuseStep 1358653 = 509495) (by norm_num)
theorem B965477 : Blo 802343 965477 := bbase (se 4 (by rfl) ⟨90513, by rfl⟩ : syracuseStep 965477 = 181027) (by norm_num)
theorem B1358741 : Blo 802343 1358741 := bbase (se 6 (by rfl) ⟨31845, by rfl⟩ : syracuseStep 1358741 = 63691) (by norm_num)
theorem B1031077 : Blo 802343 1031077 := bbase (se 4 (by rfl) ⟨96663, by rfl⟩ : syracuseStep 1031077 = 193327) (by norm_num)
theorem B1358869 : Blo 802343 1358869 := bbase (se 6 (by rfl) ⟨31848, by rfl⟩ : syracuseStep 1358869 = 63697) (by norm_num)
theorem B1358957 : Blo 802343 1358957 := bbase (se 3 (by rfl) ⟨254804, by rfl⟩ : syracuseStep 1358957 = 509609) (by norm_num)
theorem B965785 : Blo 802343 965785 := bbase (se 2 (by rfl) ⟨362169, by rfl⟩ : syracuseStep 965785 = 724339) (by norm_num)
theorem B1719461 : Blo 802343 1719461 := bbase (se 4 (by rfl) ⟨161199, by rfl⟩ : syracuseStep 1719461 = 322399) (by norm_num)
theorem B1359085 : Blo 802343 1359085 := bbase (se 3 (by rfl) ⟨254828, by rfl⟩ : syracuseStep 1359085 = 509657) (by norm_num)
theorem B1359173 : Blo 802343 1359173 := bbase (se 4 (by rfl) ⟨127422, by rfl⟩ : syracuseStep 1359173 = 254845) (by norm_num)
theorem B2571605 : Blo 802343 2571605 := bbase (se 11 (by rfl) ⟨1883, by rfl⟩ : syracuseStep 2571605 = 3767) (by norm_num)
theorem B966001 : Blo 802343 966001 := bbase (se 2 (by rfl) ⟨362250, by rfl⟩ : syracuseStep 966001 = 724501) (by norm_num)
theorem B4078997 : Blo 802343 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B1359301 : Blo 802343 1359301 := bbase (se 4 (by rfl) ⟨127434, by rfl⟩ : syracuseStep 1359301 = 254869) (by norm_num)
theorem B1359389 : Blo 802343 1359389 := bbase (se 3 (by rfl) ⟨254885, by rfl⟩ : syracuseStep 1359389 = 509771) (by norm_num)
theorem B1523261 : Blo 802343 1523261 := bbase (se 3 (by rfl) ⟨285611, by rfl⟩ : syracuseStep 1523261 = 571223) (by norm_num)
theorem B1031837 : Blo 802343 1031837 := bbase (se 3 (by rfl) ⟨193469, by rfl⟩ : syracuseStep 1031837 = 386939) (by norm_num)
theorem B1359517 : Blo 802343 1359517 := bbase (se 3 (by rfl) ⟨254909, by rfl⟩ : syracuseStep 1359517 = 509819) (by norm_num)
theorem B1031869 : Blo 802343 1031869 := bbase (se 3 (by rfl) ⟨193475, by rfl⟩ : syracuseStep 1031869 = 386951) (by norm_num)
theorem B1359605 : Blo 802343 1359605 := bbase (se 5 (by rfl) ⟨63731, by rfl⟩ : syracuseStep 1359605 = 127463) (by norm_num)
theorem B1523549 : Blo 802343 1523549 := bbase (se 3 (by rfl) ⟨285665, by rfl⟩ : syracuseStep 1523549 = 571331) (by norm_num)
theorem B1359733 : Blo 802343 1359733 := bbase (se 5 (by rfl) ⟨63737, by rfl⟩ : syracuseStep 1359733 = 127475) (by norm_num)
theorem B966601 : Blo 802343 966601 := bbase (se 2 (by rfl) ⟨362475, by rfl⟩ : syracuseStep 966601 = 724951) (by norm_num)
theorem B1359821 : Blo 802343 1359821 := bbase (se 3 (by rfl) ⟨254966, by rfl⟩ : syracuseStep 1359821 = 509933) (by norm_num)
theorem B1523701 : Blo 802343 1523701 := bbase (se 5 (by rfl) ⟨71423, by rfl⟩ : syracuseStep 1523701 = 142847) (by norm_num)
theorem B1359949 : Blo 802343 1359949 := bbase (se 3 (by rfl) ⟨254990, by rfl⟩ : syracuseStep 1359949 = 509981) (by norm_num)
theorem B3096677 : Blo 802343 3096677 := bbase (se 4 (by rfl) ⟨290313, by rfl⟩ : syracuseStep 3096677 = 580627) (by norm_num)
theorem B1360037 : Blo 802343 1360037 := bbase (se 4 (by rfl) ⟨127503, by rfl⟩ : syracuseStep 1360037 = 255007) (by norm_num)
theorem B1524005 : Blo 802343 1524005 := bbase (se 4 (by rfl) ⟨142875, by rfl⟩ : syracuseStep 1524005 = 285751) (by norm_num)
theorem B1360165 : Blo 802343 1360165 := bbase (se 4 (by rfl) ⟨127515, by rfl⟩ : syracuseStep 1360165 = 255031) (by norm_num)
theorem B1360253 : Blo 802343 1360253 := bbase (se 3 (by rfl) ⟨255047, by rfl⟩ : syracuseStep 1360253 = 510095) (by norm_num)
theorem B1032689 : Blo 802343 1032689 := bbase (se 2 (by rfl) ⟨387258, by rfl⟩ : syracuseStep 1032689 = 774517) (by norm_num)
theorem B1360381 : Blo 802343 1360381 := bbase (se 3 (by rfl) ⟨255071, by rfl⟩ : syracuseStep 1360381 = 510143) (by norm_num)
theorem B1360469 : Blo 802343 1360469 := bbase (se 8 (by rfl) ⟨7971, by rfl⟩ : syracuseStep 1360469 = 15943) (by norm_num)
theorem B4080293 : Blo 802343 4080293 := bbase (se 4 (by rfl) ⟨382527, by rfl⟩ : syracuseStep 4080293 = 765055) (by norm_num)
theorem B1360597 : Blo 802343 1360597 := bbase (se 7 (by rfl) ⟨15944, by rfl⟩ : syracuseStep 1360597 = 31889) (by norm_num)
theorem B1721101 : Blo 802343 1721101 := bbase (se 3 (by rfl) ⟨322706, by rfl⟩ : syracuseStep 1721101 = 645413) (by norm_num)
theorem B1360685 : Blo 802343 1360685 := bbase (se 3 (by rfl) ⟨255128, by rfl⟩ : syracuseStep 1360685 = 510257) (by norm_num)
theorem B1524757 : Blo 802343 1524757 := bbase (se 6 (by rfl) ⟨35736, by rfl⟩ : syracuseStep 1524757 = 71473) (by norm_num)
theorem B967745 : Blo 802343 967745 := bbase (se 2 (by rfl) ⟨362904, by rfl⟩ : syracuseStep 967745 = 725809) (by norm_num)
theorem B967793 : Blo 802343 967793 := bbase (se 2 (by rfl) ⟨362922, by rfl⟩ : syracuseStep 967793 = 725845) (by norm_num)
theorem B1524901 : Blo 802343 1524901 := bbase (se 4 (by rfl) ⟨142959, by rfl⟩ : syracuseStep 1524901 = 285919) (by norm_num)
theorem B2573477 : Blo 802343 2573477 := bbase (se 4 (by rfl) ⟨241263, by rfl⟩ : syracuseStep 2573477 = 482527) (by norm_num)
theorem B967889 : Blo 802343 967889 := bbase (se 2 (by rfl) ⟨362958, by rfl⟩ : syracuseStep 967889 = 725917) (by norm_num)
theorem B7718165 : Blo 802343 7718165 := bbase (se 6 (by rfl) ⟨180894, by rfl⟩ : syracuseStep 7718165 = 361789) (by norm_num)
theorem B1525061 : Blo 802343 1525061 := bbase (se 4 (by rfl) ⟨142974, by rfl⟩ : syracuseStep 1525061 = 285949) (by norm_num)
theorem B3523925 : Blo 802343 3523925 := bbase (se 12 (by rfl) ⟨1290, by rfl⟩ : syracuseStep 3523925 = 2581) (by norm_num)
theorem B968053 : Blo 802343 968053 := bbase (se 5 (by rfl) ⟨45377, by rfl⟩ : syracuseStep 968053 = 90755) (by norm_num)
theorem B1525205 : Blo 802343 1525205 := bbase (se 7 (by rfl) ⟨17873, by rfl⟩ : syracuseStep 1525205 = 35747) (by norm_num)
theorem B902641 : Blo 802343 902641 := bbase (se 2 (by rfl) ⟨338490, by rfl⟩ : syracuseStep 902641 = 676981) (by norm_num)
theorem B3261941 : Blo 802343 3261941 := bbase (se 5 (by rfl) ⟨152903, by rfl⟩ : syracuseStep 3261941 = 305807) (by norm_num)
theorem B902677 : Blo 802343 902677 := bbase (se 6 (by rfl) ⟨21156, by rfl⟩ : syracuseStep 902677 = 42313) (by norm_num)
theorem B902713 : Blo 802343 902713 := bbase (se 2 (by rfl) ⟨338517, by rfl⟩ : syracuseStep 902713 = 677035) (by norm_num)
theorem B968269 : Blo 802343 968269 := bbase (se 3 (by rfl) ⟨181550, by rfl⟩ : syracuseStep 968269 = 363101) (by norm_num)
theorem B2475605 : Blo 802343 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B902749 : Blo 802343 902749 := bbase (se 3 (by rfl) ⟨169265, by rfl⟩ : syracuseStep 902749 = 338531) (by norm_num)
theorem B902785 : Blo 802343 902785 := bbase (se 2 (by rfl) ⟨338544, by rfl⟩ : syracuseStep 902785 = 677089) (by norm_num)
theorem B1721989 : Blo 802343 1721989 := bbase (se 4 (by rfl) ⟨161436, by rfl⟩ : syracuseStep 1721989 = 322873) (by norm_num)
theorem B902821 : Blo 802343 902821 := bbase (se 4 (by rfl) ⟨84639, by rfl⟩ : syracuseStep 902821 = 169279) (by norm_num)
theorem B902857 : Blo 802343 902857 := bbase (se 2 (by rfl) ⟨338571, by rfl⟩ : syracuseStep 902857 = 677143) (by norm_num)
theorem B902893 : Blo 802343 902893 := bbase (se 3 (by rfl) ⟨169292, by rfl⟩ : syracuseStep 902893 = 338585) (by norm_num)
theorem B1525493 : Blo 802343 1525493 := bbase (se 5 (by rfl) ⟨71507, by rfl⟩ : syracuseStep 1525493 = 143015) (by norm_num)
theorem B968437 : Blo 802343 968437 := bbase (se 5 (by rfl) ⟨45395, by rfl⟩ : syracuseStep 968437 = 90791) (by norm_num)
theorem B2443013 : Blo 802343 2443013 := bbase (se 4 (by rfl) ⟨229032, by rfl⟩ : syracuseStep 2443013 = 458065) (by norm_num)
theorem B902929 : Blo 802343 902929 := bbase (se 2 (by rfl) ⟨338598, by rfl⟩ : syracuseStep 902929 = 677197) (by norm_num)
theorem B902965 : Blo 802343 902965 := bbase (se 5 (by rfl) ⟨42326, by rfl⟩ : syracuseStep 902965 = 84653) (by norm_num)
theorem B903001 : Blo 802343 903001 := bbase (se 2 (by rfl) ⟨338625, by rfl⟩ : syracuseStep 903001 = 677251) (by norm_num)
theorem B903037 : Blo 802343 903037 := bbase (se 3 (by rfl) ⟨169319, by rfl⟩ : syracuseStep 903037 = 338639) (by norm_num)
theorem B1525645 : Blo 802343 1525645 := bbase (se 3 (by rfl) ⟨286058, by rfl⟩ : syracuseStep 1525645 = 572117) (by norm_num)
theorem B903073 : Blo 802343 903073 := bbase (se 2 (by rfl) ⟨338652, by rfl⟩ : syracuseStep 903073 = 677305) (by norm_num)
theorem B4081589 : Blo 802343 4081589 := bbase (se 5 (by rfl) ⟨191324, by rfl⟩ : syracuseStep 4081589 = 382649) (by norm_num)
theorem B903109 : Blo 802343 903109 := bbase (se 4 (by rfl) ⟨84666, by rfl⟩ : syracuseStep 903109 = 169333) (by norm_num)
theorem B903145 : Blo 802343 903145 := bbase (se 2 (by rfl) ⟨338679, by rfl⟩ : syracuseStep 903145 = 677359) (by norm_num)
theorem B903181 : Blo 802343 903181 := bbase (se 3 (by rfl) ⟨169346, by rfl⟩ : syracuseStep 903181 = 338693) (by norm_num)
theorem B903217 : Blo 802343 903217 := bbase (se 2 (by rfl) ⟨338706, by rfl⟩ : syracuseStep 903217 = 677413) (by norm_num)
theorem B903253 : Blo 802343 903253 := bbase (se 8 (by rfl) ⟨5292, by rfl⟩ : syracuseStep 903253 = 10585) (by norm_num)
theorem B903289 : Blo 802343 903289 := bbase (se 2 (by rfl) ⟨338733, by rfl⟩ : syracuseStep 903289 = 677467) (by norm_num)
theorem B903325 : Blo 802343 903325 := bbase (se 3 (by rfl) ⟨169373, by rfl⟩ : syracuseStep 903325 = 338747) (by norm_num)
theorem B1525949 : Blo 802343 1525949 := bbase (se 3 (by rfl) ⟨286115, by rfl⟩ : syracuseStep 1525949 = 572231) (by norm_num)
theorem B903361 : Blo 802343 903361 := bbase (se 2 (by rfl) ⟨338760, by rfl⟩ : syracuseStep 903361 = 677521) (by norm_num)
theorem B903397 : Blo 802343 903397 := bbase (se 4 (by rfl) ⟨84693, by rfl⟩ : syracuseStep 903397 = 169387) (by norm_num)
theorem B903433 : Blo 802343 903433 := bbase (se 2 (by rfl) ⟨338787, by rfl⟩ : syracuseStep 903433 = 677575) (by norm_num)
theorem B903469 : Blo 802343 903469 := bbase (se 3 (by rfl) ⟨169400, by rfl⟩ : syracuseStep 903469 = 338801) (by norm_num)
theorem B903505 : Blo 802343 903505 := bbase (se 2 (by rfl) ⟨338814, by rfl⟩ : syracuseStep 903505 = 677629) (by norm_num)
theorem B903541 : Blo 802343 903541 := bbase (se 5 (by rfl) ⟨42353, by rfl⟩ : syracuseStep 903541 = 84707) (by norm_num)
theorem B903577 : Blo 802343 903577 := bbase (se 2 (by rfl) ⟨338841, by rfl⟩ : syracuseStep 903577 = 677683) (by norm_num)
theorem B903613 : Blo 802343 903613 := bbase (se 3 (by rfl) ⟨169427, by rfl⟩ : syracuseStep 903613 = 338855) (by norm_num)
theorem B903649 : Blo 802343 903649 := bbase (se 2 (by rfl) ⟨338868, by rfl⟩ : syracuseStep 903649 = 677737) (by norm_num)
theorem B903685 : Blo 802343 903685 := bbase (se 4 (by rfl) ⟨84720, by rfl⟩ : syracuseStep 903685 = 169441) (by norm_num)
theorem B903721 : Blo 802343 903721 := bbase (se 2 (by rfl) ⟨338895, by rfl⟩ : syracuseStep 903721 = 677791) (by norm_num)
theorem B903757 : Blo 802343 903757 := bbase (se 3 (by rfl) ⟨169454, by rfl⟩ : syracuseStep 903757 = 338909) (by norm_num)
theorem B903793 : Blo 802343 903793 := bbase (se 2 (by rfl) ⟨338922, by rfl⟩ : syracuseStep 903793 = 677845) (by norm_num)
theorem B903829 : Blo 802343 903829 := bbase (se 6 (by rfl) ⟨21183, by rfl⟩ : syracuseStep 903829 = 42367) (by norm_num)
theorem B903865 : Blo 802343 903865 := bbase (se 2 (by rfl) ⟨338949, by rfl⟩ : syracuseStep 903865 = 677899) (by norm_num)
theorem B903901 : Blo 802343 903901 := bbase (se 3 (by rfl) ⟨169481, by rfl⟩ : syracuseStep 903901 = 338963) (by norm_num)
theorem B903937 : Blo 802343 903937 := bbase (se 2 (by rfl) ⟨338976, by rfl⟩ : syracuseStep 903937 = 677953) (by norm_num)
theorem B903973 : Blo 802343 903973 := bbase (se 4 (by rfl) ⟨84747, by rfl⟩ : syracuseStep 903973 = 169495) (by norm_num)
theorem B904009 : Blo 802343 904009 := bbase (se 2 (by rfl) ⟨339003, by rfl⟩ : syracuseStep 904009 = 678007) (by norm_num)
theorem B904045 : Blo 802343 904045 := bbase (se 3 (by rfl) ⟨169508, by rfl⟩ : syracuseStep 904045 = 339017) (by norm_num)
theorem B904081 : Blo 802343 904081 := bbase (se 2 (by rfl) ⟨339030, by rfl⟩ : syracuseStep 904081 = 678061) (by norm_num)
theorem B1526701 : Blo 802343 1526701 := bbase (se 3 (by rfl) ⟨286256, by rfl⟩ : syracuseStep 1526701 = 572513) (by norm_num)
theorem B904117 : Blo 802343 904117 := bbase (se 5 (by rfl) ⟨42380, by rfl⟩ : syracuseStep 904117 = 84761) (by norm_num)
theorem B904153 : Blo 802343 904153 := bbase (se 2 (by rfl) ⟨339057, by rfl⟩ : syracuseStep 904153 = 678115) (by norm_num)
theorem B904189 : Blo 802343 904189 := bbase (se 3 (by rfl) ⟨169535, by rfl⟩ : syracuseStep 904189 = 339071) (by norm_num)
theorem B904225 : Blo 802343 904225 := bbase (se 2 (by rfl) ⟨339084, by rfl⟩ : syracuseStep 904225 = 678169) (by norm_num)
theorem B1526845 : Blo 802343 1526845 := bbase (se 3 (by rfl) ⟨286283, by rfl⟩ : syracuseStep 1526845 = 572567) (by norm_num)
theorem B904261 : Blo 802343 904261 := bbase (se 4 (by rfl) ⟨84774, by rfl⟩ : syracuseStep 904261 = 169549) (by norm_num)
theorem B904297 : Blo 802343 904297 := bbase (se 2 (by rfl) ⟨339111, by rfl⟩ : syracuseStep 904297 = 678223) (by norm_num)
theorem B904333 : Blo 802343 904333 := bbase (se 3 (by rfl) ⟨169562, by rfl⟩ : syracuseStep 904333 = 339125) (by norm_num)
theorem B904369 : Blo 802343 904369 := bbase (se 2 (by rfl) ⟨339138, by rfl⟩ : syracuseStep 904369 = 678277) (by norm_num)
theorem B904405 : Blo 802343 904405 := bbase (se 7 (by rfl) ⟨10598, by rfl⟩ : syracuseStep 904405 = 21197) (by norm_num)
theorem B1527005 : Blo 802343 1527005 := bbase (se 3 (by rfl) ⟨286313, by rfl⟩ : syracuseStep 1527005 = 572627) (by norm_num)
theorem B2608357 : Blo 802343 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B904441 : Blo 802343 904441 := bbase (se 2 (by rfl) ⟨339165, by rfl⟩ : syracuseStep 904441 = 678331) (by norm_num)
theorem B904477 : Blo 802343 904477 := bbase (se 3 (by rfl) ⟨169589, by rfl⟩ : syracuseStep 904477 = 339179) (by norm_num)
theorem B904513 : Blo 802343 904513 := bbase (se 2 (by rfl) ⟨339192, by rfl⟩ : syracuseStep 904513 = 678385) (by norm_num)
theorem B904549 : Blo 802343 904549 := bbase (se 4 (by rfl) ⟨84801, by rfl⟩ : syracuseStep 904549 = 169603) (by norm_num)
theorem B1527149 : Blo 802343 1527149 := bbase (se 3 (by rfl) ⟨286340, by rfl⟩ : syracuseStep 1527149 = 572681) (by norm_num)
theorem B904585 : Blo 802343 904585 := bbase (se 2 (by rfl) ⟨339219, by rfl⟩ : syracuseStep 904585 = 678439) (by norm_num)
theorem B904621 : Blo 802343 904621 := bbase (se 3 (by rfl) ⟨169616, by rfl⟩ : syracuseStep 904621 = 339233) (by norm_num)
theorem B904657 : Blo 802343 904657 := bbase (se 2 (by rfl) ⟨339246, by rfl⟩ : syracuseStep 904657 = 678493) (by norm_num)
theorem B904693 : Blo 802343 904693 := bbase (se 5 (by rfl) ⟨42407, by rfl⟩ : syracuseStep 904693 = 84815) (by norm_num)
theorem B904729 : Blo 802343 904729 := bbase (se 2 (by rfl) ⟨339273, by rfl⟩ : syracuseStep 904729 = 678547) (by norm_num)
theorem B904765 : Blo 802343 904765 := bbase (se 3 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 904765 = 339287) (by norm_num)
theorem B904801 : Blo 802343 904801 := bbase (se 2 (by rfl) ⟨339300, by rfl⟩ : syracuseStep 904801 = 678601) (by norm_num)
theorem B904837 : Blo 802343 904837 := bbase (se 4 (by rfl) ⟨84828, by rfl⟩ : syracuseStep 904837 = 169657) (by norm_num)
theorem B1527437 : Blo 802343 1527437 := bbase (se 3 (by rfl) ⟨286394, by rfl⟩ : syracuseStep 1527437 = 572789) (by norm_num)
theorem B904873 : Blo 802343 904873 := bbase (se 2 (by rfl) ⟨339327, by rfl⟩ : syracuseStep 904873 = 678655) (by norm_num)
theorem B3428021 : Blo 802343 3428021 := bbase (se 5 (by rfl) ⟨160688, by rfl⟩ : syracuseStep 3428021 = 321377) (by norm_num)
theorem B904909 : Blo 802343 904909 := bbase (se 3 (by rfl) ⟨169670, by rfl⟩ : syracuseStep 904909 = 339341) (by norm_num)
theorem B904945 : Blo 802343 904945 := bbase (se 2 (by rfl) ⟨339354, by rfl⟩ : syracuseStep 904945 = 678709) (by norm_num)
theorem B2903813 : Blo 802343 2903813 := bbase (se 4 (by rfl) ⟨272232, by rfl⟩ : syracuseStep 2903813 = 544465) (by norm_num)
theorem B904981 : Blo 802343 904981 := bbase (se 6 (by rfl) ⟨21210, by rfl⟩ : syracuseStep 904981 = 42421) (by norm_num)
theorem B1527589 : Blo 802343 1527589 := bbase (se 4 (by rfl) ⟨143211, by rfl⟩ : syracuseStep 1527589 = 286423) (by norm_num)
theorem B905017 : Blo 802343 905017 := bbase (se 2 (by rfl) ⟨339381, by rfl⟩ : syracuseStep 905017 = 678763) (by norm_num)
theorem B905053 : Blo 802343 905053 := bbase (se 3 (by rfl) ⟨169697, by rfl⟩ : syracuseStep 905053 = 339395) (by norm_num)
theorem B2576245 : Blo 802343 2576245 := bbase (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) (by norm_num)
theorem B905089 : Blo 802343 905089 := bbase (se 2 (by rfl) ⟨339408, by rfl⟩ : syracuseStep 905089 = 678817) (by norm_num)
theorem B2903957 : Blo 802343 2903957 := bbase (se 6 (by rfl) ⟨68061, by rfl⟩ : syracuseStep 2903957 = 136123) (by norm_num)
theorem B905125 : Blo 802343 905125 := bbase (se 4 (by rfl) ⟨84855, by rfl⟩ : syracuseStep 905125 = 169711) (by norm_num)
theorem B905161 : Blo 802343 905161 := bbase (se 2 (by rfl) ⟨339435, by rfl⟩ : syracuseStep 905161 = 678871) (by norm_num)
theorem B905197 : Blo 802343 905197 := bbase (se 3 (by rfl) ⟨169724, by rfl⟩ : syracuseStep 905197 = 339449) (by norm_num)
theorem B905233 : Blo 802343 905233 := bbase (se 2 (by rfl) ⟨339462, by rfl⟩ : syracuseStep 905233 = 678925) (by norm_num)
theorem B872465 : Blo 802343 872465 := bbase (se 2 (by rfl) ⟨327174, by rfl⟩ : syracuseStep 872465 = 654349) (by norm_num)
theorem B905269 : Blo 802343 905269 := bbase (se 5 (by rfl) ⟨42434, by rfl⟩ : syracuseStep 905269 = 84869) (by norm_num)
theorem B1527893 : Blo 802343 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B905305 : Blo 802343 905305 := bbase (se 2 (by rfl) ⟨339489, by rfl⟩ : syracuseStep 905305 = 678979) (by norm_num)
theorem B905341 : Blo 802343 905341 := bbase (se 3 (by rfl) ⟨169751, by rfl⟩ : syracuseStep 905341 = 339503) (by norm_num)
theorem B3920021 : Blo 802343 3920021 := bbase (se 6 (by rfl) ⟨91875, by rfl⟩ : syracuseStep 3920021 = 183751) (by norm_num)
theorem B905377 : Blo 802343 905377 := bbase (se 2 (by rfl) ⟨339516, by rfl⟩ : syracuseStep 905377 = 679033) (by norm_num)
theorem B905413 : Blo 802343 905413 := bbase (se 4 (by rfl) ⟨84882, by rfl⟩ : syracuseStep 905413 = 169765) (by norm_num)
theorem B905449 : Blo 802343 905449 := bbase (se 2 (by rfl) ⟨339543, by rfl⟩ : syracuseStep 905449 = 679087) (by norm_num)
theorem B905485 : Blo 802343 905485 := bbase (se 3 (by rfl) ⟨169778, by rfl⟩ : syracuseStep 905485 = 339557) (by norm_num)
theorem B905521 : Blo 802343 905521 := bbase (se 2 (by rfl) ⟨339570, by rfl⟩ : syracuseStep 905521 = 679141) (by norm_num)
theorem B905557 : Blo 802343 905557 := bbase (se 10 (by rfl) ⟨1326, by rfl⟩ : syracuseStep 905557 = 2653) (by norm_num)
theorem B905593 : Blo 802343 905593 := bbase (se 2 (by rfl) ⟨339597, by rfl⟩ : syracuseStep 905593 = 679195) (by norm_num)
theorem B905629 : Blo 802343 905629 := bbase (se 3 (by rfl) ⟨169805, by rfl⟩ : syracuseStep 905629 = 339611) (by norm_num)
theorem B905665 : Blo 802343 905665 := bbase (se 2 (by rfl) ⟨339624, by rfl⟩ : syracuseStep 905665 = 679249) (by norm_num)
theorem B905701 : Blo 802343 905701 := bbase (se 4 (by rfl) ⟨84909, by rfl⟩ : syracuseStep 905701 = 169819) (by norm_num)
theorem B905737 : Blo 802343 905737 := bbase (se 2 (by rfl) ⟨339651, by rfl⟩ : syracuseStep 905737 = 679303) (by norm_num)
theorem B905773 : Blo 802343 905773 := bbase (se 3 (by rfl) ⟨169832, by rfl⟩ : syracuseStep 905773 = 339665) (by norm_num)
theorem B4575797 : Blo 802343 4575797 := bbase (se 5 (by rfl) ⟨214490, by rfl⟩ : syracuseStep 4575797 = 428981) (by norm_num)
theorem B905809 : Blo 802343 905809 := bbase (se 2 (by rfl) ⟨339678, by rfl⟩ : syracuseStep 905809 = 679357) (by norm_num)
theorem B16536149 : Blo 802343 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B905845 : Blo 802343 905845 := bbase (se 5 (by rfl) ⟨42461, by rfl⟩ : syracuseStep 905845 = 84923) (by norm_num)
theorem B905881 : Blo 802343 905881 := bbase (se 2 (by rfl) ⟨339705, by rfl⟩ : syracuseStep 905881 = 679411) (by norm_num)
theorem B905917 : Blo 802343 905917 := bbase (se 3 (by rfl) ⟨169859, by rfl⟩ : syracuseStep 905917 = 339719) (by norm_num)
theorem B905953 : Blo 802343 905953 := bbase (se 2 (by rfl) ⟨339732, by rfl⟩ : syracuseStep 905953 = 679465) (by norm_num)
theorem B905989 : Blo 802343 905989 := bbase (se 4 (by rfl) ⟨84936, by rfl⟩ : syracuseStep 905989 = 169873) (by norm_num)
theorem B2708261 : Blo 802343 2708261 := bbase (se 4 (by rfl) ⟨253899, by rfl⟩ : syracuseStep 2708261 = 507799) (by norm_num)
theorem B906025 : Blo 802343 906025 := bbase (se 2 (by rfl) ⟨339759, by rfl⟩ : syracuseStep 906025 = 679519) (by norm_num)
theorem B1528645 : Blo 802343 1528645 := bbase (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) (by norm_num)
theorem B906061 : Blo 802343 906061 := bbase (se 3 (by rfl) ⟨169886, by rfl⟩ : syracuseStep 906061 = 339773) (by norm_num)
theorem B906097 : Blo 802343 906097 := bbase (se 2 (by rfl) ⟨339786, by rfl⟩ : syracuseStep 906097 = 679573) (by norm_num)
theorem B906133 : Blo 802343 906133 := bbase (se 6 (by rfl) ⟨21237, by rfl⟩ : syracuseStep 906133 = 42475) (by norm_num)
theorem B906169 : Blo 802343 906169 := bbase (se 2 (by rfl) ⟨339813, by rfl⟩ : syracuseStep 906169 = 679627) (by norm_num)
theorem B6116309 : Blo 802343 6116309 := bbase (se 7 (by rfl) ⟨71675, by rfl⟩ : syracuseStep 6116309 = 143351) (by norm_num)
theorem B1528789 : Blo 802343 1528789 := bbase (se 7 (by rfl) ⟨17915, by rfl⟩ : syracuseStep 1528789 = 35831) (by norm_num)
theorem B906205 : Blo 802343 906205 := bbase (se 3 (by rfl) ⟨169913, by rfl⟩ : syracuseStep 906205 = 339827) (by norm_num)
theorem B906241 : Blo 802343 906241 := bbase (se 2 (by rfl) ⟨339840, by rfl⟩ : syracuseStep 906241 = 679681) (by norm_num)
theorem B906277 : Blo 802343 906277 := bbase (se 4 (by rfl) ⟨84963, by rfl⟩ : syracuseStep 906277 = 169927) (by norm_num)
theorem B906313 : Blo 802343 906313 := bbase (se 2 (by rfl) ⟨339867, by rfl⟩ : syracuseStep 906313 = 679735) (by norm_num)
theorem B906349 : Blo 802343 906349 := bbase (se 3 (by rfl) ⟨169940, by rfl⟩ : syracuseStep 906349 = 339881) (by norm_num)
theorem B1528949 : Blo 802343 1528949 := bbase (se 5 (by rfl) ⟨71669, by rfl⟩ : syracuseStep 1528949 = 143339) (by norm_num)
theorem B906385 : Blo 802343 906385 := bbase (se 2 (by rfl) ⟨339894, by rfl⟩ : syracuseStep 906385 = 679789) (by norm_num)
theorem B5788853 : Blo 802343 5788853 := bbase (se 5 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 5788853 = 542705) (by norm_num)
theorem B906421 : Blo 802343 906421 := bbase (se 5 (by rfl) ⟨42488, by rfl⟩ : syracuseStep 906421 = 84977) (by norm_num)
theorem B2708693 : Blo 802343 2708693 := bbase (se 7 (by rfl) ⟨31742, by rfl⟩ : syracuseStep 2708693 = 63485) (by norm_num)
theorem B906457 : Blo 802343 906457 := bbase (se 2 (by rfl) ⟨339921, by rfl⟩ : syracuseStep 906457 = 679843) (by norm_num)
theorem B906493 : Blo 802343 906493 := bbase (se 3 (by rfl) ⟨169967, by rfl⟩ : syracuseStep 906493 = 339935) (by norm_num)
theorem B1529093 : Blo 802343 1529093 := bbase (se 4 (by rfl) ⟨143352, by rfl⟩ : syracuseStep 1529093 = 286705) (by norm_num)
theorem B2446613 : Blo 802343 2446613 := bbase (se 6 (by rfl) ⟨57342, by rfl⟩ : syracuseStep 2446613 = 114685) (by norm_num)
theorem B906529 : Blo 802343 906529 := bbase (se 2 (by rfl) ⟨339948, by rfl⟩ : syracuseStep 906529 = 679897) (by norm_num)
theorem B906565 : Blo 802343 906565 := bbase (se 4 (by rfl) ⟨84990, by rfl⟩ : syracuseStep 906565 = 169981) (by norm_num)
theorem B906601 : Blo 802343 906601 := bbase (se 2 (by rfl) ⟨339975, by rfl⟩ : syracuseStep 906601 = 679951) (by norm_num)
theorem B7853429 : Blo 802343 7853429 := bbase (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) (by norm_num)
theorem B906637 : Blo 802343 906637 := bbase (se 3 (by rfl) ⟨169994, by rfl⟩ : syracuseStep 906637 = 339989) (by norm_num)
theorem B906673 : Blo 802343 906673 := bbase (se 2 (by rfl) ⟨340002, by rfl⟩ : syracuseStep 906673 = 680005) (by norm_num)
theorem B906709 : Blo 802343 906709 := bbase (se 7 (by rfl) ⟨10625, by rfl⟩ : syracuseStep 906709 = 21251) (by norm_num)
theorem B906745 : Blo 802343 906745 := bbase (se 2 (by rfl) ⟨340029, by rfl⟩ : syracuseStep 906745 = 680059) (by norm_num)
theorem B906781 : Blo 802343 906781 := bbase (se 3 (by rfl) ⟨170021, by rfl⟩ : syracuseStep 906781 = 340043) (by norm_num)
theorem B1529381 : Blo 802343 1529381 := bbase (se 4 (by rfl) ⟨143379, by rfl⟩ : syracuseStep 1529381 = 286759) (by norm_num)
theorem B906817 : Blo 802343 906817 := bbase (se 2 (by rfl) ⟨340056, by rfl⟩ : syracuseStep 906817 = 680113) (by norm_num)
theorem B906853 : Blo 802343 906853 := bbase (se 4 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 906853 = 170035) (by norm_num)
theorem B2709125 : Blo 802343 2709125 := bbase (se 4 (by rfl) ⟨253980, by rfl⟩ : syracuseStep 2709125 = 507961) (by norm_num)
theorem B906889 : Blo 802343 906889 := bbase (se 2 (by rfl) ⟨340083, by rfl⟩ : syracuseStep 906889 = 680167) (by norm_num)
theorem B906925 : Blo 802343 906925 := bbase (se 3 (by rfl) ⟨170048, by rfl⟩ : syracuseStep 906925 = 340097) (by norm_num)
theorem B1529533 : Blo 802343 1529533 := bbase (se 3 (by rfl) ⟨286787, by rfl⟩ : syracuseStep 1529533 = 573575) (by norm_num)
theorem B906961 : Blo 802343 906961 := bbase (se 2 (by rfl) ⟨340110, by rfl⟩ : syracuseStep 906961 = 680221) (by norm_num)
theorem B906997 : Blo 802343 906997 := bbase (se 5 (by rfl) ⟨42515, by rfl⟩ : syracuseStep 906997 = 85031) (by norm_num)
theorem B907033 : Blo 802343 907033 := bbase (se 2 (by rfl) ⟨340137, by rfl⟩ : syracuseStep 907033 = 680275) (by norm_num)
theorem B907069 : Blo 802343 907069 := bbase (se 3 (by rfl) ⟨170075, by rfl⟩ : syracuseStep 907069 = 340151) (by norm_num)
theorem B907105 : Blo 802343 907105 := bbase (se 2 (by rfl) ⟨340164, by rfl⟩ : syracuseStep 907105 = 680329) (by norm_num)
theorem B2905973 : Blo 802343 2905973 := bbase (se 5 (by rfl) ⟨136217, by rfl⟩ : syracuseStep 2905973 = 272435) (by norm_num)
theorem B2381717 : Blo 802343 2381717 := bbase (se 6 (by rfl) ⟨55821, by rfl⟩ : syracuseStep 2381717 = 111643) (by norm_num)
theorem B7722965 : Blo 802343 7722965 := bbase (se 7 (by rfl) ⟨90503, by rfl⟩ : syracuseStep 7722965 = 181007) (by norm_num)
theorem B1529837 : Blo 802343 1529837 := bbase (se 3 (by rfl) ⟨286844, by rfl⟩ : syracuseStep 1529837 = 573689) (by norm_num)
theorem B2709557 : Blo 802343 2709557 := bbase (se 5 (by rfl) ⟨127010, by rfl⟩ : syracuseStep 2709557 = 254021) (by norm_num)
theorem B24762581 : Blo 802343 24762581 := bbase (se 7 (by rfl) ⟨290186, by rfl⟩ : syracuseStep 24762581 = 580373) (by norm_num)
theorem B3299621 : Blo 802343 3299621 := bbase (se 4 (by rfl) ⟨309339, by rfl⟩ : syracuseStep 3299621 = 618679) (by norm_num)
theorem B2709989 : Blo 802343 2709989 := bbase (se 4 (by rfl) ⟨254061, by rfl⟩ : syracuseStep 2709989 = 508123) (by norm_num)
theorem B1628765 : Blo 802343 1628765 := bbase (se 3 (by rfl) ⟨305393, by rfl⟩ : syracuseStep 1628765 = 610787) (by norm_num)
theorem B2579141 : Blo 802343 2579141 := bbase (se 4 (by rfl) ⟨241794, by rfl⟩ : syracuseStep 2579141 = 483589) (by norm_num)
theorem B1530589 : Blo 802343 1530589 := bbase (se 3 (by rfl) ⟨286985, by rfl⟩ : syracuseStep 1530589 = 573971) (by norm_num)
theorem B1530733 : Blo 802343 1530733 := bbase (se 3 (by rfl) ⟨287012, by rfl⟩ : syracuseStep 1530733 = 574025) (by norm_num)
theorem B2448245 : Blo 802343 2448245 := bbase (se 5 (by rfl) ⟨114761, by rfl⟩ : syracuseStep 2448245 = 229523) (by norm_num)
theorem B2710421 : Blo 802343 2710421 := bbase (se 6 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 2710421 = 127051) (by norm_num)
theorem B1629485 : Blo 802343 1629485 := bbase (se 3 (by rfl) ⟨305528, by rfl⟩ : syracuseStep 1629485 = 611057) (by norm_num)
theorem B2710853 : Blo 802343 2710853 := bbase (se 4 (by rfl) ⟨254142, by rfl⟩ : syracuseStep 2710853 = 508285) (by norm_num)
theorem B1203533 : Blo 802343 1203533 := bbase (se 3 (by rfl) ⟨225662, by rfl⟩ : syracuseStep 1203533 = 451325) (by norm_num)
theorem B1203557 : Blo 802343 1203557 := bbase (se 4 (by rfl) ⟨112833, by rfl⟩ : syracuseStep 1203557 = 225667) (by norm_num)
theorem B1203581 : Blo 802343 1203581 := bbase (se 3 (by rfl) ⟨225671, by rfl⟩ : syracuseStep 1203581 = 451343) (by norm_num)
theorem B2284949 : Blo 802343 2284949 := bbase (se 6 (by rfl) ⟨53553, by rfl⟩ : syracuseStep 2284949 = 107107) (by norm_num)
theorem B1203605 : Blo 802343 1203605 := bbase (se 6 (by rfl) ⟨28209, by rfl⟩ : syracuseStep 1203605 = 56419) (by norm_num)
theorem B3267989 : Blo 802343 3267989 := bbase (se 6 (by rfl) ⟨76593, by rfl⟩ : syracuseStep 3267989 = 153187) (by norm_num)
theorem B1203629 : Blo 802343 1203629 := bbase (se 3 (by rfl) ⟨225680, by rfl⟩ : syracuseStep 1203629 = 451361) (by norm_num)
theorem B1203653 : Blo 802343 1203653 := bbase (se 4 (by rfl) ⟨112842, by rfl⟩ : syracuseStep 1203653 = 225685) (by norm_num)
theorem B1203677 : Blo 802343 1203677 := bbase (se 3 (by rfl) ⟨225689, by rfl⟩ : syracuseStep 1203677 = 451379) (by norm_num)
theorem B1203701 : Blo 802343 1203701 := bbase (se 5 (by rfl) ⟨56423, by rfl⟩ : syracuseStep 1203701 = 112847) (by norm_num)
theorem B3726853 : Blo 802343 3726853 := bbase (se 4 (by rfl) ⟨349392, by rfl⟩ : syracuseStep 3726853 = 698785) (by norm_num)
theorem B1203725 : Blo 802343 1203725 := bbase (se 3 (by rfl) ⟨225698, by rfl⟩ : syracuseStep 1203725 = 451397) (by norm_num)
theorem B1203749 : Blo 802343 1203749 := bbase (se 4 (by rfl) ⟨112851, by rfl⟩ : syracuseStep 1203749 = 225703) (by norm_num)
theorem B1203773 : Blo 802343 1203773 := bbase (se 3 (by rfl) ⟨225707, by rfl⟩ : syracuseStep 1203773 = 451415) (by norm_num)
theorem B1203797 : Blo 802343 1203797 := bbase (se 8 (by rfl) ⟨7053, by rfl⟩ : syracuseStep 1203797 = 14107) (by norm_num)
theorem B3858005 : Blo 802343 3858005 := bbase (se 8 (by rfl) ⟨22605, by rfl⟩ : syracuseStep 3858005 = 45211) (by norm_num)
theorem B1203821 : Blo 802343 1203821 := bbase (se 3 (by rfl) ⟨225716, by rfl⟩ : syracuseStep 1203821 = 451433) (by norm_num)
theorem B1203845 : Blo 802343 1203845 := bbase (se 4 (by rfl) ⟨112860, by rfl⟩ : syracuseStep 1203845 = 225721) (by norm_num)
theorem B13721237 : Blo 802343 13721237 := bbase (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) (by norm_num)
theorem B2449045 : Blo 802343 2449045 := bbase (se 6 (by rfl) ⟨57399, by rfl⟩ : syracuseStep 2449045 = 114799) (by norm_num)
theorem B1203869 : Blo 802343 1203869 := bbase (se 3 (by rfl) ⟨225725, by rfl⟩ : syracuseStep 1203869 = 451451) (by norm_num)
theorem B1203893 : Blo 802343 1203893 := bbase (se 5 (by rfl) ⟨56432, by rfl⟩ : syracuseStep 1203893 = 112865) (by norm_num)
theorem B3858101 : Blo 802343 3858101 := bbase (se 5 (by rfl) ⟨180848, by rfl⟩ : syracuseStep 3858101 = 361697) (by norm_num)
theorem B1203917 : Blo 802343 1203917 := bbase (se 3 (by rfl) ⟨225734, by rfl⟩ : syracuseStep 1203917 = 451469) (by norm_num)
theorem B1203941 : Blo 802343 1203941 := bbase (se 4 (by rfl) ⟨112869, by rfl⟩ : syracuseStep 1203941 = 225739) (by norm_num)
theorem B2711285 : Blo 802343 2711285 := bbase (se 5 (by rfl) ⟨127091, by rfl⟩ : syracuseStep 2711285 = 254183) (by norm_num)
theorem B1203965 : Blo 802343 1203965 := bbase (se 3 (by rfl) ⟨225743, by rfl⟩ : syracuseStep 1203965 = 451487) (by norm_num)
theorem B1203989 : Blo 802343 1203989 := bbase (se 6 (by rfl) ⟨28218, by rfl⟩ : syracuseStep 1203989 = 56437) (by norm_num)
theorem B1204013 : Blo 802343 1204013 := bbase (se 3 (by rfl) ⟨225752, by rfl⟩ : syracuseStep 1204013 = 451505) (by norm_num)
theorem B1204037 : Blo 802343 1204037 := bbase (se 4 (by rfl) ⟨112878, by rfl⟩ : syracuseStep 1204037 = 225757) (by norm_num)
theorem B88137557 : Blo 802343 88137557 := bbase (se 9 (by rfl) ⟨258215, by rfl⟩ : syracuseStep 88137557 = 516431) (by norm_num)
theorem B1204061 : Blo 802343 1204061 := bbase (se 3 (by rfl) ⟨225761, by rfl⟩ : syracuseStep 1204061 = 451523) (by norm_num)
theorem B3432293 : Blo 802343 3432293 := bbase (se 4 (by rfl) ⟨321777, by rfl⟩ : syracuseStep 3432293 = 643555) (by norm_num)
theorem B1204085 : Blo 802343 1204085 := bbase (se 5 (by rfl) ⟨56441, by rfl⟩ : syracuseStep 1204085 = 112883) (by norm_num)
theorem B1204109 : Blo 802343 1204109 := bbase (se 3 (by rfl) ⟨225770, by rfl⟩ : syracuseStep 1204109 = 451541) (by norm_num)
theorem B1204133 : Blo 802343 1204133 := bbase (se 4 (by rfl) ⟨112887, by rfl⟩ : syracuseStep 1204133 = 225775) (by norm_num)
theorem B1204157 : Blo 802343 1204157 := bbase (se 3 (by rfl) ⟨225779, by rfl⟩ : syracuseStep 1204157 = 451559) (by norm_num)
theorem B1204181 : Blo 802343 1204181 := bbase (se 7 (by rfl) ⟨14111, by rfl⟩ : syracuseStep 1204181 = 28223) (by norm_num)
theorem B1204205 : Blo 802343 1204205 := bbase (se 3 (by rfl) ⟨225788, by rfl⟩ : syracuseStep 1204205 = 451577) (by norm_num)
theorem B1204229 : Blo 802343 1204229 := bbase (se 4 (by rfl) ⟨112896, by rfl⟩ : syracuseStep 1204229 = 225793) (by norm_num)
theorem B2416661 : Blo 802343 2416661 := bbase (se 6 (by rfl) ⟨56640, by rfl⟩ : syracuseStep 2416661 = 113281) (by norm_num)
theorem B1204253 : Blo 802343 1204253 := bbase (se 3 (by rfl) ⟨225797, by rfl⟩ : syracuseStep 1204253 = 451595) (by norm_num)
theorem B2285621 : Blo 802343 2285621 := bbase (se 5 (by rfl) ⟨107138, by rfl⟩ : syracuseStep 2285621 = 214277) (by norm_num)
theorem B1204277 : Blo 802343 1204277 := bbase (se 5 (by rfl) ⟨56450, by rfl⟩ : syracuseStep 1204277 = 112901) (by norm_num)
theorem B1204301 : Blo 802343 1204301 := bbase (se 3 (by rfl) ⟨225806, by rfl⟩ : syracuseStep 1204301 = 451613) (by norm_num)
theorem B1204325 : Blo 802343 1204325 := bbase (se 4 (by rfl) ⟨112905, by rfl⟩ : syracuseStep 1204325 = 225811) (by norm_num)
theorem B1204349 : Blo 802343 1204349 := bbase (se 3 (by rfl) ⟨225815, by rfl⟩ : syracuseStep 1204349 = 451631) (by norm_num)
theorem B1204373 : Blo 802343 1204373 := bbase (se 6 (by rfl) ⟨28227, by rfl⟩ : syracuseStep 1204373 = 56455) (by norm_num)
theorem B2711717 : Blo 802343 2711717 := bbase (se 4 (by rfl) ⟨254223, by rfl⟩ : syracuseStep 2711717 = 508447) (by norm_num)
theorem B1204397 : Blo 802343 1204397 := bbase (se 3 (by rfl) ⟨225824, by rfl⟩ : syracuseStep 1204397 = 451649) (by norm_num)
theorem B1204421 : Blo 802343 1204421 := bbase (se 4 (by rfl) ⟨112914, by rfl⟩ : syracuseStep 1204421 = 225829) (by norm_num)
theorem B1204445 : Blo 802343 1204445 := bbase (se 3 (by rfl) ⟨225833, by rfl⟩ : syracuseStep 1204445 = 451667) (by norm_num)
theorem B1204469 : Blo 802343 1204469 := bbase (se 5 (by rfl) ⟨56459, by rfl⟩ : syracuseStep 1204469 = 112919) (by norm_num)
theorem B1204493 : Blo 802343 1204493 := bbase (se 3 (by rfl) ⟨225842, by rfl⟩ : syracuseStep 1204493 = 451685) (by norm_num)
theorem B1204517 : Blo 802343 1204517 := bbase (se 4 (by rfl) ⟨112923, by rfl⟩ : syracuseStep 1204517 = 225847) (by norm_num)
theorem B1204541 : Blo 802343 1204541 := bbase (se 3 (by rfl) ⟨225851, by rfl⟩ : syracuseStep 1204541 = 451703) (by norm_num)
theorem B1204565 : Blo 802343 1204565 := bbase (se 10 (by rfl) ⟨1764, by rfl⟩ : syracuseStep 1204565 = 3529) (by norm_num)
theorem B4350293 : Blo 802343 4350293 := bbase (se 10 (by rfl) ⟨6372, by rfl⟩ : syracuseStep 4350293 = 12745) (by norm_num)
theorem B1204589 : Blo 802343 1204589 := bbase (se 3 (by rfl) ⟨225860, by rfl⟩ : syracuseStep 1204589 = 451721) (by norm_num)
theorem B1204613 : Blo 802343 1204613 := bbase (se 4 (by rfl) ⟨112932, by rfl⟩ : syracuseStep 1204613 = 225865) (by norm_num)
theorem B1204637 : Blo 802343 1204637 := bbase (se 3 (by rfl) ⟨225869, by rfl⟩ : syracuseStep 1204637 = 451739) (by norm_num)
theorem B1630621 : Blo 802343 1630621 := bbase (se 3 (by rfl) ⟨305741, by rfl⟩ : syracuseStep 1630621 = 611483) (by norm_num)
theorem B1204661 : Blo 802343 1204661 := bbase (se 5 (by rfl) ⟨56468, by rfl⟩ : syracuseStep 1204661 = 112937) (by norm_num)
theorem B1204685 : Blo 802343 1204685 := bbase (se 3 (by rfl) ⟨225878, by rfl⟩ : syracuseStep 1204685 = 451757) (by norm_num)
theorem B2286053 : Blo 802343 2286053 := bbase (se 4 (by rfl) ⟨214317, by rfl⟩ : syracuseStep 2286053 = 428635) (by norm_num)
theorem B1204709 : Blo 802343 1204709 := bbase (se 4 (by rfl) ⟨112941, by rfl⟩ : syracuseStep 1204709 = 225883) (by norm_num)
theorem B1204733 : Blo 802343 1204733 := bbase (se 3 (by rfl) ⟨225887, by rfl⟩ : syracuseStep 1204733 = 451775) (by norm_num)
theorem B1204757 : Blo 802343 1204757 := bbase (se 6 (by rfl) ⟨28236, by rfl⟩ : syracuseStep 1204757 = 56473) (by norm_num)
theorem B1204781 : Blo 802343 1204781 := bbase (se 3 (by rfl) ⟨225896, by rfl⟩ : syracuseStep 1204781 = 451793) (by norm_num)
theorem B1204805 : Blo 802343 1204805 := bbase (se 4 (by rfl) ⟨112950, by rfl⟩ : syracuseStep 1204805 = 225901) (by norm_num)
theorem B2712149 : Blo 802343 2712149 := bbase (se 8 (by rfl) ⟨15891, by rfl⟩ : syracuseStep 2712149 = 31783) (by norm_num)
theorem B1204829 : Blo 802343 1204829 := bbase (se 3 (by rfl) ⟨225905, by rfl⟩ : syracuseStep 1204829 = 451811) (by norm_num)
theorem B1204853 : Blo 802343 1204853 := bbase (se 5 (by rfl) ⟨56477, by rfl⟩ : syracuseStep 1204853 = 112955) (by norm_num)
theorem B1204877 : Blo 802343 1204877 := bbase (se 3 (by rfl) ⟨225914, by rfl⟩ : syracuseStep 1204877 = 451829) (by norm_num)
theorem B1204901 : Blo 802343 1204901 := bbase (se 4 (by rfl) ⟨112959, by rfl⟩ : syracuseStep 1204901 = 225919) (by norm_num)
theorem B1204925 : Blo 802343 1204925 := bbase (se 3 (by rfl) ⟨225923, by rfl⟩ : syracuseStep 1204925 = 451847) (by norm_num)
theorem B1204949 : Blo 802343 1204949 := bbase (se 7 (by rfl) ⟨14120, by rfl⟩ : syracuseStep 1204949 = 28241) (by norm_num)
theorem B1204973 : Blo 802343 1204973 := bbase (se 3 (by rfl) ⟨225932, by rfl⟩ : syracuseStep 1204973 = 451865) (by norm_num)
theorem B1204997 : Blo 802343 1204997 := bbase (se 4 (by rfl) ⟨112968, by rfl⟩ : syracuseStep 1204997 = 225937) (by norm_num)
theorem B1205021 : Blo 802343 1205021 := bbase (se 3 (by rfl) ⟨225941, by rfl⟩ : syracuseStep 1205021 = 451883) (by norm_num)
theorem B1205045 : Blo 802343 1205045 := bbase (se 5 (by rfl) ⟨56486, by rfl⟩ : syracuseStep 1205045 = 112973) (by norm_num)
theorem B1205069 : Blo 802343 1205069 := bbase (se 3 (by rfl) ⟨225950, by rfl⟩ : syracuseStep 1205069 = 451901) (by norm_num)
theorem B1205093 : Blo 802343 1205093 := bbase (se 4 (by rfl) ⟨112977, by rfl⟩ : syracuseStep 1205093 = 225955) (by norm_num)
theorem B1205117 : Blo 802343 1205117 := bbase (se 3 (by rfl) ⟨225959, by rfl⟩ : syracuseStep 1205117 = 451919) (by norm_num)
theorem B1205141 : Blo 802343 1205141 := bbase (se 6 (by rfl) ⟨28245, by rfl⟩ : syracuseStep 1205141 = 56491) (by norm_num)
theorem B1205165 : Blo 802343 1205165 := bbase (se 3 (by rfl) ⟨225968, by rfl⟩ : syracuseStep 1205165 = 451937) (by norm_num)
theorem B1205189 : Blo 802343 1205189 := bbase (se 4 (by rfl) ⟨112986, by rfl⟩ : syracuseStep 1205189 = 225973) (by norm_num)
theorem B1205213 : Blo 802343 1205213 := bbase (se 3 (by rfl) ⟨225977, by rfl⟩ : syracuseStep 1205213 = 451955) (by norm_num)
theorem B1205237 : Blo 802343 1205237 := bbase (se 5 (by rfl) ⟨56495, by rfl⟩ : syracuseStep 1205237 = 112991) (by norm_num)
theorem B2712581 : Blo 802343 2712581 := bbase (se 4 (by rfl) ⟨254304, by rfl⟩ : syracuseStep 2712581 = 508609) (by norm_num)
theorem B1205261 : Blo 802343 1205261 := bbase (se 3 (by rfl) ⟨225986, by rfl⟩ : syracuseStep 1205261 = 451973) (by norm_num)
theorem B1205285 : Blo 802343 1205285 := bbase (se 4 (by rfl) ⟨112995, by rfl⟩ : syracuseStep 1205285 = 225991) (by norm_num)
theorem B1205309 : Blo 802343 1205309 := bbase (se 3 (by rfl) ⟨225995, by rfl⟩ : syracuseStep 1205309 = 451991) (by norm_num)
theorem B1205333 : Blo 802343 1205333 := bbase (se 8 (by rfl) ⟨7062, by rfl⟩ : syracuseStep 1205333 = 14125) (by norm_num)
theorem B1205357 : Blo 802343 1205357 := bbase (se 3 (by rfl) ⟨226004, by rfl⟩ : syracuseStep 1205357 = 452009) (by norm_num)
theorem B1205381 : Blo 802343 1205381 := bbase (se 4 (by rfl) ⟨113004, by rfl⟩ : syracuseStep 1205381 = 226009) (by norm_num)
theorem B1205405 : Blo 802343 1205405 := bbase (se 3 (by rfl) ⟨226013, by rfl⟩ : syracuseStep 1205405 = 452027) (by norm_num)
theorem B1205429 : Blo 802343 1205429 := bbase (se 5 (by rfl) ⟨56504, by rfl⟩ : syracuseStep 1205429 = 113009) (by norm_num)
theorem B1205453 : Blo 802343 1205453 := bbase (se 3 (by rfl) ⟨226022, by rfl⟩ : syracuseStep 1205453 = 452045) (by norm_num)
theorem B2286805 : Blo 802343 2286805 := bbase (se 7 (by rfl) ⟨26798, by rfl⟩ : syracuseStep 2286805 = 53597) (by norm_num)
theorem B1205477 : Blo 802343 1205477 := bbase (se 4 (by rfl) ⟨113013, by rfl⟩ : syracuseStep 1205477 = 226027) (by norm_num)
theorem B1205501 : Blo 802343 1205501 := bbase (se 3 (by rfl) ⟨226031, by rfl⟩ : syracuseStep 1205501 = 452063) (by norm_num)
theorem B1205525 : Blo 802343 1205525 := bbase (se 6 (by rfl) ⟨28254, by rfl⟩ : syracuseStep 1205525 = 56509) (by norm_num)
theorem B1205549 : Blo 802343 1205549 := bbase (se 3 (by rfl) ⟨226040, by rfl⟩ : syracuseStep 1205549 = 452081) (by norm_num)
theorem B1205573 : Blo 802343 1205573 := bbase (se 4 (by rfl) ⟨113022, by rfl⟩ : syracuseStep 1205573 = 226045) (by norm_num)
theorem B1205597 : Blo 802343 1205597 := bbase (se 3 (by rfl) ⟨226049, by rfl⟩ : syracuseStep 1205597 = 452099) (by norm_num)
theorem B1205621 : Blo 802343 1205621 := bbase (se 5 (by rfl) ⟨56513, by rfl⟩ : syracuseStep 1205621 = 113027) (by norm_num)
theorem B1205645 : Blo 802343 1205645 := bbase (se 3 (by rfl) ⟨226058, by rfl⟩ : syracuseStep 1205645 = 452117) (by norm_num)
theorem B1205669 : Blo 802343 1205669 := bbase (se 4 (by rfl) ⟨113031, by rfl⟩ : syracuseStep 1205669 = 226063) (by norm_num)
theorem B2713013 : Blo 802343 2713013 := bbase (se 5 (by rfl) ⟨127172, by rfl⟩ : syracuseStep 2713013 = 254345) (by norm_num)
theorem B1205693 : Blo 802343 1205693 := bbase (se 3 (by rfl) ⟨226067, by rfl⟩ : syracuseStep 1205693 = 452135) (by norm_num)
theorem B1205717 : Blo 802343 1205717 := bbase (se 7 (by rfl) ⟨14129, by rfl⟩ : syracuseStep 1205717 = 28259) (by norm_num)
theorem B1205741 : Blo 802343 1205741 := bbase (se 3 (by rfl) ⟨226076, by rfl⟩ : syracuseStep 1205741 = 452153) (by norm_num)
theorem B1205765 : Blo 802343 1205765 := bbase (se 4 (by rfl) ⟨113040, by rfl⟩ : syracuseStep 1205765 = 226081) (by norm_num)
theorem B1205789 : Blo 802343 1205789 := bbase (se 3 (by rfl) ⟨226085, by rfl⟩ : syracuseStep 1205789 = 452171) (by norm_num)
theorem B3860021 : Blo 802343 3860021 := bbase (se 5 (by rfl) ⟨180938, by rfl⟩ : syracuseStep 3860021 = 361877) (by norm_num)
theorem B1205813 : Blo 802343 1205813 := bbase (se 5 (by rfl) ⟨56522, by rfl⟩ : syracuseStep 1205813 = 113045) (by norm_num)
theorem B1205837 : Blo 802343 1205837 := bbase (se 3 (by rfl) ⟨226094, by rfl⟩ : syracuseStep 1205837 = 452189) (by norm_num)
theorem B1631821 : Blo 802343 1631821 := bbase (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) (by norm_num)
theorem B3434069 : Blo 802343 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B3663461 : Blo 802343 3663461 := bbase (se 4 (by rfl) ⟨343449, by rfl⟩ : syracuseStep 3663461 = 686899) (by norm_num)
theorem B1205861 : Blo 802343 1205861 := bbase (se 4 (by rfl) ⟨113049, by rfl⟩ : syracuseStep 1205861 = 226099) (by norm_num)
theorem B1205885 : Blo 802343 1205885 := bbase (se 3 (by rfl) ⟨226103, by rfl⟩ : syracuseStep 1205885 = 452207) (by norm_num)
theorem B1205909 : Blo 802343 1205909 := bbase (se 6 (by rfl) ⟨28263, by rfl⟩ : syracuseStep 1205909 = 56527) (by norm_num)
theorem B1205933 : Blo 802343 1205933 := bbase (se 3 (by rfl) ⟨226112, by rfl⟩ : syracuseStep 1205933 = 452225) (by norm_num)
theorem B1205957 : Blo 802343 1205957 := bbase (se 4 (by rfl) ⟨113058, by rfl⟩ : syracuseStep 1205957 = 226117) (by norm_num)
theorem B1205981 : Blo 802343 1205981 := bbase (se 3 (by rfl) ⟨226121, by rfl⟩ : syracuseStep 1205981 = 452243) (by norm_num)
theorem B1206005 : Blo 802343 1206005 := bbase (se 5 (by rfl) ⟨56531, by rfl⟩ : syracuseStep 1206005 = 113063) (by norm_num)
theorem B1206029 : Blo 802343 1206029 := bbase (se 3 (by rfl) ⟨226130, by rfl⟩ : syracuseStep 1206029 = 452261) (by norm_num)
theorem B2582293 : Blo 802343 2582293 := bbase (se 6 (by rfl) ⟨60522, by rfl⟩ : syracuseStep 2582293 = 121045) (by norm_num)
theorem B1206053 : Blo 802343 1206053 := bbase (se 4 (by rfl) ⟨113067, by rfl⟩ : syracuseStep 1206053 = 226135) (by norm_num)
theorem B1206077 : Blo 802343 1206077 := bbase (se 3 (by rfl) ⟨226139, by rfl⟩ : syracuseStep 1206077 = 452279) (by norm_num)
theorem B3434309 : Blo 802343 3434309 := bbase (se 4 (by rfl) ⟨321966, by rfl⟩ : syracuseStep 3434309 = 643933) (by norm_num)
theorem B1206101 : Blo 802343 1206101 := bbase (se 9 (by rfl) ⟨3533, by rfl⟩ : syracuseStep 1206101 = 7067) (by norm_num)
theorem B2713445 : Blo 802343 2713445 := bbase (se 4 (by rfl) ⟨254385, by rfl⟩ : syracuseStep 2713445 = 508771) (by norm_num)
theorem B1206125 : Blo 802343 1206125 := bbase (se 3 (by rfl) ⟨226148, by rfl⟩ : syracuseStep 1206125 = 452297) (by norm_num)
theorem B1206149 : Blo 802343 1206149 := bbase (se 4 (by rfl) ⟨113076, by rfl⟩ : syracuseStep 1206149 = 226153) (by norm_num)
theorem B1206173 : Blo 802343 1206173 := bbase (se 3 (by rfl) ⟨226157, by rfl⟩ : syracuseStep 1206173 = 452315) (by norm_num)
theorem B1206197 : Blo 802343 1206197 := bbase (se 5 (by rfl) ⟨56540, by rfl⟩ : syracuseStep 1206197 = 113081) (by norm_num)
theorem B1206221 : Blo 802343 1206221 := bbase (se 3 (by rfl) ⟨226166, by rfl⟩ : syracuseStep 1206221 = 452333) (by norm_num)
theorem B5498837 : Blo 802343 5498837 := bbase (se 7 (by rfl) ⟨64439, by rfl⟩ : syracuseStep 5498837 = 128879) (by norm_num)
theorem B1206245 : Blo 802343 1206245 := bbase (se 4 (by rfl) ⟨113085, by rfl⟩ : syracuseStep 1206245 = 226171) (by norm_num)
theorem B1206269 : Blo 802343 1206269 := bbase (se 3 (by rfl) ⟨226175, by rfl⟩ : syracuseStep 1206269 = 452351) (by norm_num)
theorem B1206293 : Blo 802343 1206293 := bbase (se 6 (by rfl) ⟨28272, by rfl⟩ : syracuseStep 1206293 = 56545) (by norm_num)
theorem B1206317 : Blo 802343 1206317 := bbase (se 3 (by rfl) ⟨226184, by rfl⟩ : syracuseStep 1206317 = 452369) (by norm_num)
theorem B1206341 : Blo 802343 1206341 := bbase (se 4 (by rfl) ⟨113094, by rfl⟩ : syracuseStep 1206341 = 226189) (by norm_num)
theorem B1206365 : Blo 802343 1206365 := bbase (se 3 (by rfl) ⟨226193, by rfl⟩ : syracuseStep 1206365 = 452387) (by norm_num)
theorem B1206389 : Blo 802343 1206389 := bbase (se 5 (by rfl) ⟨56549, by rfl⟩ : syracuseStep 1206389 = 113099) (by norm_num)
theorem B1206413 : Blo 802343 1206413 := bbase (se 3 (by rfl) ⟨226202, by rfl⟩ : syracuseStep 1206413 = 452405) (by norm_num)
theorem B1206437 : Blo 802343 1206437 := bbase (se 4 (by rfl) ⟨113103, by rfl⟩ : syracuseStep 1206437 = 226207) (by norm_num)
theorem B1632421 : Blo 802343 1632421 := bbase (se 4 (by rfl) ⟨153039, by rfl⟩ : syracuseStep 1632421 = 306079) (by norm_num)
theorem B1304749 : Blo 802343 1304749 := bbase (se 3 (by rfl) ⟨244640, by rfl⟩ : syracuseStep 1304749 = 489281) (by norm_num)
theorem B1206461 : Blo 802343 1206461 := bbase (se 3 (by rfl) ⟨226211, by rfl⟩ : syracuseStep 1206461 = 452423) (by norm_num)
theorem B1206485 : Blo 802343 1206485 := bbase (se 7 (by rfl) ⟨14138, by rfl⟩ : syracuseStep 1206485 = 28277) (by norm_num)
theorem B1206509 : Blo 802343 1206509 := bbase (se 3 (by rfl) ⟨226220, by rfl⟩ : syracuseStep 1206509 = 452441) (by norm_num)
theorem B6875381 : Blo 802343 6875381 := bbase (se 5 (by rfl) ⟨322283, by rfl⟩ : syracuseStep 6875381 = 644567) (by norm_num)
theorem B1206533 : Blo 802343 1206533 := bbase (se 4 (by rfl) ⟨113112, by rfl⟩ : syracuseStep 1206533 = 226225) (by norm_num)
theorem B2713877 : Blo 802343 2713877 := bbase (se 6 (by rfl) ⟨63606, by rfl⟩ : syracuseStep 2713877 = 127213) (by norm_num)
theorem B1206557 : Blo 802343 1206557 := bbase (se 3 (by rfl) ⟨226229, by rfl⟩ : syracuseStep 1206557 = 452459) (by norm_num)
theorem B1206581 : Blo 802343 1206581 := bbase (se 5 (by rfl) ⟨56558, by rfl⟩ : syracuseStep 1206581 = 113117) (by norm_num)
theorem B1206605 : Blo 802343 1206605 := bbase (se 3 (by rfl) ⟨226238, by rfl⟩ : syracuseStep 1206605 = 452477) (by norm_num)
theorem B1206629 : Blo 802343 1206629 := bbase (se 4 (by rfl) ⟨113121, by rfl⟩ : syracuseStep 1206629 = 226243) (by norm_num)
theorem B1206653 : Blo 802343 1206653 := bbase (se 3 (by rfl) ⟨226247, by rfl⟩ : syracuseStep 1206653 = 452495) (by norm_num)
theorem B813445 : Blo 802343 813445 := bbase (se 4 (by rfl) ⟨76260, by rfl⟩ : syracuseStep 813445 = 152521) (by norm_num)
theorem B1206677 : Blo 802343 1206677 := bbase (se 6 (by rfl) ⟨28281, by rfl⟩ : syracuseStep 1206677 = 56563) (by norm_num)
theorem B1206701 : Blo 802343 1206701 := bbase (se 3 (by rfl) ⟨226256, by rfl⟩ : syracuseStep 1206701 = 452513) (by norm_num)
theorem B1206725 : Blo 802343 1206725 := bbase (se 4 (by rfl) ⟨113130, by rfl⟩ : syracuseStep 1206725 = 226261) (by norm_num)
theorem B5302741 : Blo 802343 5302741 := bbase (se 7 (by rfl) ⟨62141, by rfl⟩ : syracuseStep 5302741 = 124283) (by norm_num)
theorem B1206749 : Blo 802343 1206749 := bbase (se 3 (by rfl) ⟨226265, by rfl⟩ : syracuseStep 1206749 = 452531) (by norm_num)
theorem B1206773 : Blo 802343 1206773 := bbase (se 5 (by rfl) ⟨56567, by rfl⟩ : syracuseStep 1206773 = 113135) (by norm_num)
theorem B1206797 : Blo 802343 1206797 := bbase (se 3 (by rfl) ⟨226274, by rfl⟩ : syracuseStep 1206797 = 452549) (by norm_num)
theorem B1206821 : Blo 802343 1206821 := bbase (se 4 (by rfl) ⟨113139, by rfl⟩ : syracuseStep 1206821 = 226279) (by norm_num)
theorem B1206845 : Blo 802343 1206845 := bbase (se 3 (by rfl) ⟨226283, by rfl⟩ : syracuseStep 1206845 = 452567) (by norm_num)
theorem B1206869 : Blo 802343 1206869 := bbase (se 8 (by rfl) ⟨7071, by rfl⟩ : syracuseStep 1206869 = 14143) (by norm_num)
theorem B1206893 : Blo 802343 1206893 := bbase (se 3 (by rfl) ⟨226292, by rfl⟩ : syracuseStep 1206893 = 452585) (by norm_num)
theorem B1206917 : Blo 802343 1206917 := bbase (se 4 (by rfl) ⟨113148, by rfl⟩ : syracuseStep 1206917 = 226297) (by norm_num)
theorem B1206941 : Blo 802343 1206941 := bbase (se 3 (by rfl) ⟨226301, by rfl⟩ : syracuseStep 1206941 = 452603) (by norm_num)
theorem B1206965 : Blo 802343 1206965 := bbase (se 5 (by rfl) ⟨56576, by rfl⟩ : syracuseStep 1206965 = 113153) (by norm_num)
theorem B2714309 : Blo 802343 2714309 := bbase (se 4 (by rfl) ⟨254466, by rfl⟩ : syracuseStep 2714309 = 508933) (by norm_num)
theorem B1206989 : Blo 802343 1206989 := bbase (se 3 (by rfl) ⟨226310, by rfl⟩ : syracuseStep 1206989 = 452621) (by norm_num)
theorem B1305317 : Blo 802343 1305317 := bbase (se 4 (by rfl) ⟨122373, by rfl⟩ : syracuseStep 1305317 = 244747) (by norm_num)
theorem B1207013 : Blo 802343 1207013 := bbase (se 4 (by rfl) ⟨113157, by rfl⟩ : syracuseStep 1207013 = 226315) (by norm_num)
theorem B1207037 : Blo 802343 1207037 := bbase (se 3 (by rfl) ⟨226319, by rfl⟩ : syracuseStep 1207037 = 452639) (by norm_num)
theorem B1207061 : Blo 802343 1207061 := bbase (se 6 (by rfl) ⟨28290, by rfl⟩ : syracuseStep 1207061 = 56581) (by norm_num)
theorem B1567525 : Blo 802343 1567525 := bbase (se 4 (by rfl) ⟨146955, by rfl⟩ : syracuseStep 1567525 = 293911) (by norm_num)
theorem B1207085 : Blo 802343 1207085 := bbase (se 3 (by rfl) ⟨226328, by rfl⟩ : syracuseStep 1207085 = 452657) (by norm_num)
theorem B1207109 : Blo 802343 1207109 := bbase (se 4 (by rfl) ⟨113166, by rfl⟩ : syracuseStep 1207109 = 226333) (by norm_num)
theorem B1207133 : Blo 802343 1207133 := bbase (se 3 (by rfl) ⟨226337, by rfl⟩ : syracuseStep 1207133 = 452675) (by norm_num)
theorem B1207157 : Blo 802343 1207157 := bbase (se 5 (by rfl) ⟨56585, by rfl⟩ : syracuseStep 1207157 = 113171) (by norm_num)
theorem B1207181 : Blo 802343 1207181 := bbase (se 3 (by rfl) ⟨226346, by rfl⟩ : syracuseStep 1207181 = 452693) (by norm_num)
theorem B1207205 : Blo 802343 1207205 := bbase (se 4 (by rfl) ⟨113175, by rfl⟩ : syracuseStep 1207205 = 226351) (by norm_num)
theorem B813997 : Blo 802343 813997 := bbase (se 3 (by rfl) ⟨152624, by rfl⟩ : syracuseStep 813997 = 305249) (by norm_num)
theorem B1207229 : Blo 802343 1207229 := bbase (se 3 (by rfl) ⟨226355, by rfl⟩ : syracuseStep 1207229 = 452711) (by norm_num)
theorem B3861445 : Blo 802343 3861445 := bbase (se 4 (by rfl) ⟨362010, by rfl⟩ : syracuseStep 3861445 = 724021) (by norm_num)
theorem B1207253 : Blo 802343 1207253 := bbase (se 7 (by rfl) ⟨14147, by rfl⟩ : syracuseStep 1207253 = 28295) (by norm_num)
theorem B1207277 : Blo 802343 1207277 := bbase (se 3 (by rfl) ⟨226364, by rfl⟩ : syracuseStep 1207277 = 452729) (by norm_num)
theorem B1207301 : Blo 802343 1207301 := bbase (se 4 (by rfl) ⟨113184, by rfl⟩ : syracuseStep 1207301 = 226369) (by norm_num)
theorem B1207325 : Blo 802343 1207325 := bbase (se 3 (by rfl) ⟨226373, by rfl⟩ : syracuseStep 1207325 = 452747) (by norm_num)
theorem B1207349 : Blo 802343 1207349 := bbase (se 5 (by rfl) ⟨56594, by rfl⟩ : syracuseStep 1207349 = 113189) (by norm_num)
theorem B1207373 : Blo 802343 1207373 := bbase (se 3 (by rfl) ⟨226382, by rfl⟩ : syracuseStep 1207373 = 452765) (by norm_num)
theorem B1207397 : Blo 802343 1207397 := bbase (se 4 (by rfl) ⟨113193, by rfl⟩ : syracuseStep 1207397 = 226387) (by norm_num)
theorem B2714741 : Blo 802343 2714741 := bbase (se 5 (by rfl) ⟨127253, by rfl⟩ : syracuseStep 2714741 = 254507) (by norm_num)
theorem B1207421 : Blo 802343 1207421 := bbase (se 3 (by rfl) ⟨226391, by rfl⟩ : syracuseStep 1207421 = 452783) (by norm_num)
theorem B1207445 : Blo 802343 1207445 := bbase (se 6 (by rfl) ⟨28299, by rfl⟩ : syracuseStep 1207445 = 56599) (by norm_num)
theorem B1830053 : Blo 802343 1830053 := bbase (se 4 (by rfl) ⟨171567, by rfl⟩ : syracuseStep 1830053 = 343135) (by norm_num)
theorem B1207469 : Blo 802343 1207469 := bbase (se 3 (by rfl) ⟨226400, by rfl⟩ : syracuseStep 1207469 = 452801) (by norm_num)
theorem B1207493 : Blo 802343 1207493 := bbase (se 4 (by rfl) ⟨113202, by rfl⟩ : syracuseStep 1207493 = 226405) (by norm_num)
theorem B1207517 : Blo 802343 1207517 := bbase (se 3 (by rfl) ⟨226409, by rfl⟩ : syracuseStep 1207517 = 452819) (by norm_num)
theorem B1207541 : Blo 802343 1207541 := bbase (se 5 (by rfl) ⟨56603, by rfl⟩ : syracuseStep 1207541 = 113207) (by norm_num)
theorem B1207565 : Blo 802343 1207565 := bbase (se 3 (by rfl) ⟨226418, by rfl⟩ : syracuseStep 1207565 = 452837) (by norm_num)
theorem B3665173 : Blo 802343 3665173 := bbase (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) (by norm_num)
theorem B1207589 : Blo 802343 1207589 := bbase (se 4 (by rfl) ⟨113211, by rfl⟩ : syracuseStep 1207589 = 226423) (by norm_num)
theorem B1207613 : Blo 802343 1207613 := bbase (se 3 (by rfl) ⟨226427, by rfl⟩ : syracuseStep 1207613 = 452855) (by norm_num)
theorem B1207637 : Blo 802343 1207637 := bbase (se 11 (by rfl) ⟨884, by rfl⟩ : syracuseStep 1207637 = 1769) (by norm_num)
theorem B1633637 : Blo 802343 1633637 := bbase (se 4 (by rfl) ⟨153153, by rfl⟩ : syracuseStep 1633637 = 306307) (by norm_num)
theorem B1207661 : Blo 802343 1207661 := bbase (se 3 (by rfl) ⟨226436, by rfl⟩ : syracuseStep 1207661 = 452873) (by norm_num)
theorem B1207685 : Blo 802343 1207685 := bbase (se 4 (by rfl) ⟨113220, by rfl⟩ : syracuseStep 1207685 = 226441) (by norm_num)
theorem B1207709 : Blo 802343 1207709 := bbase (se 3 (by rfl) ⟨226445, by rfl⟩ : syracuseStep 1207709 = 452891) (by norm_num)
theorem B1207733 : Blo 802343 1207733 := bbase (se 5 (by rfl) ⟨56612, by rfl⟩ : syracuseStep 1207733 = 113225) (by norm_num)
theorem B1207757 : Blo 802343 1207757 := bbase (se 3 (by rfl) ⟨226454, by rfl⟩ : syracuseStep 1207757 = 452909) (by norm_num)
theorem B1207781 : Blo 802343 1207781 := bbase (se 4 (by rfl) ⟨113229, by rfl⟩ : syracuseStep 1207781 = 226459) (by norm_num)
theorem B1207805 : Blo 802343 1207805 := bbase (se 3 (by rfl) ⟨226463, by rfl⟩ : syracuseStep 1207805 = 452927) (by norm_num)
theorem B1207829 : Blo 802343 1207829 := bbase (se 6 (by rfl) ⟨28308, by rfl⟩ : syracuseStep 1207829 = 56617) (by norm_num)
theorem B2715173 : Blo 802343 2715173 := bbase (se 4 (by rfl) ⟨254547, by rfl⟩ : syracuseStep 2715173 = 509095) (by norm_num)
theorem B1207853 : Blo 802343 1207853 := bbase (se 3 (by rfl) ⟨226472, by rfl⟩ : syracuseStep 1207853 = 452945) (by norm_num)
theorem B1207877 : Blo 802343 1207877 := bbase (se 4 (by rfl) ⟨113238, by rfl⟩ : syracuseStep 1207877 = 226477) (by norm_num)
theorem B2059853 : Blo 802343 2059853 := bbase (se 3 (by rfl) ⟨386222, by rfl⟩ : syracuseStep 2059853 = 772445) (by norm_num)
theorem B12381781 : Blo 802343 12381781 := bbase (se 8 (by rfl) ⟨72549, by rfl⟩ : syracuseStep 12381781 = 145099) (by norm_num)
theorem B1207901 : Blo 802343 1207901 := bbase (se 3 (by rfl) ⟨226481, by rfl⟩ : syracuseStep 1207901 = 452963) (by norm_num)
theorem B1207925 : Blo 802343 1207925 := bbase (se 5 (by rfl) ⟨56621, by rfl⟩ : syracuseStep 1207925 = 113243) (by norm_num)
theorem B1207949 : Blo 802343 1207949 := bbase (se 3 (by rfl) ⟨226490, by rfl⟩ : syracuseStep 1207949 = 452981) (by norm_num)
theorem B1207973 : Blo 802343 1207973 := bbase (se 4 (by rfl) ⟨113247, by rfl⟩ : syracuseStep 1207973 = 226495) (by norm_num)
theorem B1207997 : Blo 802343 1207997 := bbase (se 3 (by rfl) ⟨226499, by rfl⟩ : syracuseStep 1207997 = 452999) (by norm_num)
theorem B1208021 : Blo 802343 1208021 := bbase (se 7 (by rfl) ⟨14156, by rfl⟩ : syracuseStep 1208021 = 28313) (by norm_num)
theorem B1208045 : Blo 802343 1208045 := bbase (se 3 (by rfl) ⟨226508, by rfl⟩ : syracuseStep 1208045 = 453017) (by norm_num)
theorem B1306373 : Blo 802343 1306373 := bbase (se 4 (by rfl) ⟨122472, by rfl⟩ : syracuseStep 1306373 = 244945) (by norm_num)
theorem B1208069 : Blo 802343 1208069 := bbase (se 4 (by rfl) ⟨113256, by rfl⟩ : syracuseStep 1208069 = 226513) (by norm_num)
theorem B1208093 : Blo 802343 1208093 := bbase (se 3 (by rfl) ⟨226517, by rfl⟩ : syracuseStep 1208093 = 453035) (by norm_num)
theorem B1208117 : Blo 802343 1208117 := bbase (se 5 (by rfl) ⟨56630, by rfl⟩ : syracuseStep 1208117 = 113261) (by norm_num)
theorem B1208141 : Blo 802343 1208141 := bbase (se 3 (by rfl) ⟨226526, by rfl⟩ : syracuseStep 1208141 = 453053) (by norm_num)
theorem B1208165 : Blo 802343 1208165 := bbase (se 4 (by rfl) ⟨113265, by rfl⟩ : syracuseStep 1208165 = 226531) (by norm_num)
theorem B1208189 : Blo 802343 1208189 := bbase (se 3 (by rfl) ⟨226535, by rfl⟩ : syracuseStep 1208189 = 453071) (by norm_num)
theorem B1929109 : Blo 802343 1929109 := bbase (se 6 (by rfl) ⟨45213, by rfl⟩ : syracuseStep 1929109 = 90427) (by norm_num)
theorem B1208213 : Blo 802343 1208213 := bbase (se 6 (by rfl) ⟨28317, by rfl⟩ : syracuseStep 1208213 = 56635) (by norm_num)
theorem B1208237 : Blo 802343 1208237 := bbase (se 3 (by rfl) ⟨226544, by rfl⟩ : syracuseStep 1208237 = 453089) (by norm_num)
theorem B1208261 : Blo 802343 1208261 := bbase (se 4 (by rfl) ⟨113274, by rfl⟩ : syracuseStep 1208261 = 226549) (by norm_num)
theorem B2715605 : Blo 802343 2715605 := bbase (se 7 (by rfl) ⟨31823, by rfl⟩ : syracuseStep 2715605 = 63647) (by norm_num)
theorem B1208285 : Blo 802343 1208285 := bbase (se 3 (by rfl) ⟨226553, by rfl⟩ : syracuseStep 1208285 = 453107) (by norm_num)
theorem B2289653 : Blo 802343 2289653 := bbase (se 5 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 2289653 = 214655) (by norm_num)
theorem B1208309 : Blo 802343 1208309 := bbase (se 5 (by rfl) ⟨56639, by rfl⟩ : syracuseStep 1208309 = 113279) (by norm_num)
theorem B1208333 : Blo 802343 1208333 := bbase (se 3 (by rfl) ⟨226562, by rfl⟩ : syracuseStep 1208333 = 453125) (by norm_num)
theorem B1208357 : Blo 802343 1208357 := bbase (se 4 (by rfl) ⟨113283, by rfl⟩ : syracuseStep 1208357 = 226567) (by norm_num)
theorem B3436597 : Blo 802343 3436597 := bbase (se 5 (by rfl) ⟨161090, by rfl⟩ : syracuseStep 3436597 = 322181) (by norm_num)
theorem B1208381 : Blo 802343 1208381 := bbase (se 3 (by rfl) ⟨226571, by rfl⟩ : syracuseStep 1208381 = 453143) (by norm_num)
theorem B32206933 : Blo 802343 32206933 := bbase (se 8 (by rfl) ⟨188712, by rfl⟩ : syracuseStep 32206933 = 377425) (by norm_num)
theorem B1208405 : Blo 802343 1208405 := bbase (se 8 (by rfl) ⟨7080, by rfl⟩ : syracuseStep 1208405 = 14161) (by norm_num)
theorem B1208429 : Blo 802343 1208429 := bbase (se 3 (by rfl) ⟨226580, by rfl⟩ : syracuseStep 1208429 = 453161) (by norm_num)
theorem B1863805 : Blo 802343 1863805 := bbase (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) (by norm_num)
theorem B1208453 : Blo 802343 1208453 := bbase (se 4 (by rfl) ⟨113292, by rfl⟩ : syracuseStep 1208453 = 226585) (by norm_num)
theorem B1044625 : Blo 802343 1044625 := bbase (se 2 (by rfl) ⟨391734, by rfl⟩ : syracuseStep 1044625 = 783469) (by norm_num)
theorem B1208477 : Blo 802343 1208477 := bbase (se 3 (by rfl) ⟨226589, by rfl⟩ : syracuseStep 1208477 = 453179) (by norm_num)
theorem B1208501 : Blo 802343 1208501 := bbase (se 5 (by rfl) ⟨56648, by rfl⟩ : syracuseStep 1208501 = 113297) (by norm_num)
theorem B1208525 : Blo 802343 1208525 := bbase (se 3 (by rfl) ⟨226598, by rfl⟩ : syracuseStep 1208525 = 453197) (by norm_num)
theorem B1208549 : Blo 802343 1208549 := bbase (se 4 (by rfl) ⟨113301, by rfl⟩ : syracuseStep 1208549 = 226603) (by norm_num)
theorem B1208573 : Blo 802343 1208573 := bbase (se 3 (by rfl) ⟨226607, by rfl⟩ : syracuseStep 1208573 = 453215) (by norm_num)
theorem B1208597 : Blo 802343 1208597 := bbase (se 6 (by rfl) ⟨28326, by rfl⟩ : syracuseStep 1208597 = 56653) (by norm_num)
theorem B1208621 : Blo 802343 1208621 := bbase (se 3 (by rfl) ⟨226616, by rfl⟩ : syracuseStep 1208621 = 453233) (by norm_num)
theorem B1208645 : Blo 802343 1208645 := bbase (se 4 (by rfl) ⟨113310, by rfl⟩ : syracuseStep 1208645 = 226621) (by norm_num)
theorem B1208669 : Blo 802343 1208669 := bbase (se 3 (by rfl) ⟨226625, by rfl⟩ : syracuseStep 1208669 = 453251) (by norm_num)
theorem B5140853 : Blo 802343 5140853 := bbase (se 5 (by rfl) ⟨240977, by rfl⟩ : syracuseStep 5140853 = 481955) (by norm_num)
theorem B1208693 : Blo 802343 1208693 := bbase (se 5 (by rfl) ⟨56657, by rfl⟩ : syracuseStep 1208693 = 113315) (by norm_num)
theorem B2716037 : Blo 802343 2716037 := bbase (se 4 (by rfl) ⟨254628, by rfl⟩ : syracuseStep 2716037 = 509257) (by norm_num)
theorem B1208717 : Blo 802343 1208717 := bbase (se 3 (by rfl) ⟨226634, by rfl⟩ : syracuseStep 1208717 = 453269) (by norm_num)
theorem B1208741 : Blo 802343 1208741 := bbase (se 4 (by rfl) ⟨113319, by rfl⟩ : syracuseStep 1208741 = 226639) (by norm_num)
theorem B4583861 : Blo 802343 4583861 := bbase (se 5 (by rfl) ⟨214868, by rfl⟩ : syracuseStep 4583861 = 429737) (by norm_num)
theorem B1208765 : Blo 802343 1208765 := bbase (se 3 (by rfl) ⟨226643, by rfl⟩ : syracuseStep 1208765 = 453287) (by norm_num)
theorem B1208789 : Blo 802343 1208789 := bbase (se 7 (by rfl) ⟨14165, by rfl⟩ : syracuseStep 1208789 = 28331) (by norm_num)
theorem B1208813 : Blo 802343 1208813 := bbase (se 3 (by rfl) ⟨226652, by rfl⟩ : syracuseStep 1208813 = 453305) (by norm_num)
theorem B1208837 : Blo 802343 1208837 := bbase (se 4 (by rfl) ⟨113328, by rfl⟩ : syracuseStep 1208837 = 226657) (by norm_num)
theorem B1208861 : Blo 802343 1208861 := bbase (se 3 (by rfl) ⟨226661, by rfl⟩ : syracuseStep 1208861 = 453323) (by norm_num)
theorem B1372717 : Blo 802343 1372717 := bbase (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) (by norm_num)
theorem B1208885 : Blo 802343 1208885 := bbase (se 5 (by rfl) ⟨56666, by rfl⟩ : syracuseStep 1208885 = 113333) (by norm_num)
theorem B1208909 : Blo 802343 1208909 := bbase (se 3 (by rfl) ⟨226670, by rfl⟩ : syracuseStep 1208909 = 453341) (by norm_num)
theorem B1208933 : Blo 802343 1208933 := bbase (se 4 (by rfl) ⟨113337, by rfl⟩ : syracuseStep 1208933 = 226675) (by norm_num)
theorem B1208957 : Blo 802343 1208957 := bbase (se 3 (by rfl) ⟨226679, by rfl⟩ : syracuseStep 1208957 = 453359) (by norm_num)
theorem B1208981 : Blo 802343 1208981 := bbase (se 6 (by rfl) ⟨28335, by rfl⟩ : syracuseStep 1208981 = 56671) (by norm_num)
theorem B1209005 : Blo 802343 1209005 := bbase (se 3 (by rfl) ⟨226688, by rfl⟩ : syracuseStep 1209005 = 453377) (by norm_num)
theorem B1209029 : Blo 802343 1209029 := bbase (se 4 (by rfl) ⟨113346, by rfl⟩ : syracuseStep 1209029 = 226693) (by norm_num)
theorem B1209053 : Blo 802343 1209053 := bbase (se 3 (by rfl) ⟨226697, by rfl⟩ : syracuseStep 1209053 = 453395) (by norm_num)
theorem B1209077 : Blo 802343 1209077 := bbase (se 5 (by rfl) ⟨56675, by rfl⟩ : syracuseStep 1209077 = 113351) (by norm_num)
theorem B1209101 : Blo 802343 1209101 := bbase (se 3 (by rfl) ⟨226706, by rfl⟩ : syracuseStep 1209101 = 453413) (by norm_num)
theorem B1209125 : Blo 802343 1209125 := bbase (se 4 (by rfl) ⟨113355, by rfl⟩ : syracuseStep 1209125 = 226711) (by norm_num)
theorem B2716469 : Blo 802343 2716469 := bbase (se 5 (by rfl) ⟨127334, by rfl⟩ : syracuseStep 2716469 = 254669) (by norm_num)
theorem B1209149 : Blo 802343 1209149 := bbase (se 3 (by rfl) ⟨226715, by rfl⟩ : syracuseStep 1209149 = 453431) (by norm_num)
theorem B1209173 : Blo 802343 1209173 := bbase (se 9 (by rfl) ⟨3542, by rfl⟩ : syracuseStep 1209173 = 7085) (by norm_num)
theorem B1209197 : Blo 802343 1209197 := bbase (se 3 (by rfl) ⟨226724, by rfl⟩ : syracuseStep 1209197 = 453449) (by norm_num)
theorem B1209221 : Blo 802343 1209221 := bbase (se 4 (by rfl) ⟨113364, by rfl⟩ : syracuseStep 1209221 = 226729) (by norm_num)
theorem B1209245 : Blo 802343 1209245 := bbase (se 3 (by rfl) ⟨226733, by rfl⟩ : syracuseStep 1209245 = 453467) (by norm_num)
theorem B1143733 : Blo 802343 1143733 := bbase (se 5 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 1143733 = 107225) (by norm_num)
theorem B1209269 : Blo 802343 1209269 := bbase (se 5 (by rfl) ⟨56684, by rfl⟩ : syracuseStep 1209269 = 113369) (by norm_num)
theorem B1209293 : Blo 802343 1209293 := bbase (se 3 (by rfl) ⟨226742, by rfl⟩ : syracuseStep 1209293 = 453485) (by norm_num)
theorem B1209317 : Blo 802343 1209317 := bbase (se 4 (by rfl) ⟨113373, by rfl⟩ : syracuseStep 1209317 = 226747) (by norm_num)
theorem B1209341 : Blo 802343 1209341 := bbase (se 3 (by rfl) ⟨226751, by rfl⟩ : syracuseStep 1209341 = 453503) (by norm_num)
theorem B1209365 : Blo 802343 1209365 := bbase (se 6 (by rfl) ⟨28344, by rfl⟩ : syracuseStep 1209365 = 56689) (by norm_num)
theorem B1209389 : Blo 802343 1209389 := bbase (se 3 (by rfl) ⟨226760, by rfl⟩ : syracuseStep 1209389 = 453521) (by norm_num)
theorem B1209413 : Blo 802343 1209413 := bbase (se 4 (by rfl) ⟨113382, by rfl⟩ : syracuseStep 1209413 = 226765) (by norm_num)
theorem B1209437 : Blo 802343 1209437 := bbase (se 3 (by rfl) ⟨226769, by rfl⟩ : syracuseStep 1209437 = 453539) (by norm_num)
theorem B1209461 : Blo 802343 1209461 := bbase (se 5 (by rfl) ⟨56693, by rfl⟩ : syracuseStep 1209461 = 113387) (by norm_num)
theorem B1209485 : Blo 802343 1209485 := bbase (se 3 (by rfl) ⟨226778, by rfl⟩ : syracuseStep 1209485 = 453557) (by norm_num)
theorem B2290837 : Blo 802343 2290837 := bbase (se 6 (by rfl) ⟨53691, by rfl⟩ : syracuseStep 2290837 = 107383) (by norm_num)
theorem B6878357 : Blo 802343 6878357 := bbase (se 6 (by rfl) ⟨161211, by rfl⟩ : syracuseStep 6878357 = 322423) (by norm_num)
theorem B1209509 : Blo 802343 1209509 := bbase (se 4 (by rfl) ⟨113391, by rfl⟩ : syracuseStep 1209509 = 226783) (by norm_num)
theorem B2716901 : Blo 802343 2716901 := bbase (se 4 (by rfl) ⟨254709, by rfl⟩ : syracuseStep 2716901 = 509419) (by norm_num)
theorem B1930549 : Blo 802343 1930549 := bbase (se 5 (by rfl) ⟨90494, by rfl⟩ : syracuseStep 1930549 = 180989) (by norm_num)
theorem B2290997 : Blo 802343 2290997 := bbase (se 5 (by rfl) ⟨107390, by rfl⟩ : syracuseStep 2290997 = 214781) (by norm_num)
theorem B3667349 : Blo 802343 3667349 := bbase (se 6 (by rfl) ⟨85953, by rfl⟩ : syracuseStep 3667349 = 171907) (by norm_num)
theorem B1144325 : Blo 802343 1144325 := bbase (se 4 (by rfl) ⟨107280, by rfl⟩ : syracuseStep 1144325 = 214561) (by norm_num)
theorem B3438085 : Blo 802343 3438085 := bbase (se 4 (by rfl) ⟨322320, by rfl⟩ : syracuseStep 3438085 = 644641) (by norm_num)
theorem B3438101 : Blo 802343 3438101 := bbase (se 6 (by rfl) ⟨80580, by rfl⟩ : syracuseStep 3438101 = 161161) (by norm_num)
theorem B2291237 : Blo 802343 2291237 := bbase (se 4 (by rfl) ⟨214803, by rfl⟩ : syracuseStep 2291237 = 429607) (by norm_num)
theorem B816689 : Blo 802343 816689 := bbase (se 2 (by rfl) ⟨306258, by rfl⟩ : syracuseStep 816689 = 612517) (by norm_num)
theorem B4126277 : Blo 802343 4126277 := bbase (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) (by norm_num)
theorem B1144405 : Blo 802343 1144405 := bbase (se 8 (by rfl) ⟨6705, by rfl⟩ : syracuseStep 1144405 = 13411) (by norm_num)
theorem B4585045 : Blo 802343 4585045 := bbase (se 8 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 4585045 = 53731) (by norm_num)
theorem B2717333 : Blo 802343 2717333 := bbase (se 6 (by rfl) ⟨63687, by rfl⟩ : syracuseStep 2717333 = 127375) (by norm_num)
theorem B2291381 : Blo 802343 2291381 := bbase (se 5 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 2291381 = 214817) (by norm_num)
theorem B1144525 : Blo 802343 1144525 := bbase (se 3 (by rfl) ⟨214598, by rfl⟩ : syracuseStep 1144525 = 429197) (by norm_num)
theorem B4126421 : Blo 802343 4126421 := bbase (se 7 (by rfl) ⟨48356, by rfl⟩ : syracuseStep 4126421 = 96713) (by norm_num)
theorem B2291429 : Blo 802343 2291429 := bbase (se 4 (by rfl) ⟨214821, by rfl⟩ : syracuseStep 2291429 = 429643) (by norm_num)
theorem B1144621 : Blo 802343 1144621 := bbase (se 3 (by rfl) ⟨214616, by rfl⟩ : syracuseStep 1144621 = 429233) (by norm_num)
theorem B915305 : Blo 802343 915305 := bbase (se 2 (by rfl) ⟨343239, by rfl⟩ : syracuseStep 915305 = 686479) (by norm_num)
theorem B1046405 : Blo 802343 1046405 := bbase (se 4 (by rfl) ⟨98100, by rfl⟩ : syracuseStep 1046405 = 196201) (by norm_num)
theorem B1931165 : Blo 802343 1931165 := bbase (se 3 (by rfl) ⟨362093, by rfl⟩ : syracuseStep 1931165 = 724187) (by norm_num)
theorem B2717765 : Blo 802343 2717765 := bbase (se 4 (by rfl) ⟨254790, by rfl⟩ : syracuseStep 2717765 = 509581) (by norm_num)
theorem B1931357 : Blo 802343 1931357 := bbase (se 3 (by rfl) ⟨362129, by rfl⟩ : syracuseStep 1931357 = 724259) (by norm_num)
theorem B915565 : Blo 802343 915565 := bbase (se 3 (by rfl) ⟨171668, by rfl⟩ : syracuseStep 915565 = 343337) (by norm_num)
theorem B6092981 : Blo 802343 6092981 := bbase (se 5 (by rfl) ⟨285608, by rfl⟩ : syracuseStep 6092981 = 571217) (by norm_num)
theorem B1145117 : Blo 802343 1145117 := bbase (se 3 (by rfl) ⟨214709, by rfl⟩ : syracuseStep 1145117 = 429419) (by norm_num)
theorem B1931645 : Blo 802343 1931645 := bbase (se 3 (by rfl) ⟨362183, by rfl⟩ : syracuseStep 1931645 = 724367) (by norm_num)
theorem B1374661 : Blo 802343 1374661 := bbase (se 4 (by rfl) ⟨128874, by rfl⟩ : syracuseStep 1374661 = 257749) (by norm_num)
theorem B2718197 : Blo 802343 2718197 := bbase (se 5 (by rfl) ⟨127415, by rfl⟩ : syracuseStep 2718197 = 254831) (by norm_num)
theorem B883289 : Blo 802343 883289 := bbase (se 2 (by rfl) ⟨331233, by rfl⟩ : syracuseStep 883289 = 662467) (by norm_num)
theorem B2292421 : Blo 802343 2292421 := bbase (se 4 (by rfl) ⟨214914, by rfl⟩ : syracuseStep 2292421 = 429829) (by norm_num)
theorem B1243853 : Blo 802343 1243853 := bbase (se 3 (by rfl) ⟨233222, by rfl⟩ : syracuseStep 1243853 = 466445) (by norm_num)
theorem B1145669 : Blo 802343 1145669 := bbase (se 4 (by rfl) ⟨107406, by rfl⟩ : syracuseStep 1145669 = 214813) (by norm_num)
theorem B2718629 : Blo 802343 2718629 := bbase (se 4 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 2718629 = 509743) (by norm_num)
theorem B4062149 : Blo 802343 4062149 := bbase (se 4 (by rfl) ⟨380826, by rfl⟩ : syracuseStep 4062149 = 761653) (by norm_num)
theorem B27884501 : Blo 802343 27884501 := bbase (se 7 (by rfl) ⟨326771, by rfl⟩ : syracuseStep 27884501 = 653543) (by norm_num)
theorem B916805 : Blo 802343 916805 := bbase (se 4 (by rfl) ⟨85950, by rfl⟩ : syracuseStep 916805 = 171901) (by norm_num)
theorem B2030933 : Blo 802343 2030933 := bbase (se 11 (by rfl) ⟨1487, by rfl⟩ : syracuseStep 2030933 = 2975) (by norm_num)
theorem B2719061 : Blo 802343 2719061 := bbase (se 11 (by rfl) ⟨1991, by rfl⟩ : syracuseStep 2719061 = 3983) (by norm_num)
theorem B1375645 : Blo 802343 1375645 := bbase (se 3 (by rfl) ⟨257933, by rfl⟩ : syracuseStep 1375645 = 515867) (by norm_num)
theorem B4587029 : Blo 802343 4587029 := bbase (se 6 (by rfl) ⟨107508, by rfl⟩ : syracuseStep 4587029 = 215017) (by norm_num)
theorem B1146421 : Blo 802343 1146421 := bbase (se 5 (by rfl) ⟨53738, by rfl⟩ : syracuseStep 1146421 = 107477) (by norm_num)
theorem B2031277 : Blo 802343 2031277 := bbase (se 3 (by rfl) ⟨380864, by rfl⟩ : syracuseStep 2031277 = 761729) (by norm_num)
theorem B1015517 : Blo 802343 1015517 := bbase (se 3 (by rfl) ⟨190409, by rfl⟩ : syracuseStep 1015517 = 380819) (by norm_num)
theorem B3440357 : Blo 802343 3440357 := bbase (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) (by norm_num)
theorem B2719493 : Blo 802343 2719493 := bbase (se 4 (by rfl) ⟨254952, by rfl⟩ : syracuseStep 2719493 = 509905) (by norm_num)
theorem B2293525 : Blo 802343 2293525 := bbase (se 6 (by rfl) ⟨53754, by rfl⟩ : syracuseStep 2293525 = 107509) (by norm_num)
theorem B1015573 : Blo 802343 1015573 := bbase (se 6 (by rfl) ⟨23802, by rfl⟩ : syracuseStep 1015573 = 47605) (by norm_num)
theorem B2031389 : Blo 802343 2031389 := bbase (se 3 (by rfl) ⟨380885, by rfl⟩ : syracuseStep 2031389 = 761771) (by norm_num)
theorem B1015669 : Blo 802343 1015669 := bbase (se 5 (by rfl) ⟨47609, by rfl⟩ : syracuseStep 1015669 = 95219) (by norm_num)
theorem B2031581 : Blo 802343 2031581 := bbase (se 3 (by rfl) ⟨380921, by rfl⟩ : syracuseStep 2031581 = 761843) (by norm_num)
theorem B2326573 : Blo 802343 2326573 := bstep (se 3 (by rfl) ⟨436232, by rfl⟩ : syracuseStep 2326573 = 872465) B872465
theorem B1016003 : Blo 802343 1016003 := bstep (se 1 (by rfl) ⟨762002, by rfl⟩ : syracuseStep 1016003 = 1524005) B1524005
theorem B2031875 : Blo 802343 2031875 := bstep (se 1 (by rfl) ⟨1523906, by rfl⟩ : syracuseStep 2031875 = 3047813) B3047813
theorem B8257805 : Blo 802343 8257805 := bstep (se 3 (by rfl) ⟨1548338, by rfl⟩ : syracuseStep 8257805 = 3096677) B3096677
theorem B2720141 : Blo 802343 2720141 := bstep (se 3 (by rfl) ⟨510026, by rfl⟩ : syracuseStep 2720141 = 1020053) B1020053
theorem B2032067 : Blo 802343 2032067 := bstep (se 1 (by rfl) ⟨1524050, by rfl⟩ : syracuseStep 2032067 = 3048101) B3048101
theorem B2720195 : Blo 802343 2720195 := bstep (se 1 (by rfl) ⟨2040146, by rfl⟩ : syracuseStep 2720195 = 4080293) B4080293
theorem B2753041 : Blo 802343 2753041 := bstep (se 2 (by rfl) ⟨1032390, by rfl⟩ : syracuseStep 2753041 = 2064781) B2064781
theorem B1147441 : Blo 802343 1147441 := bstep (se 2 (by rfl) ⟨430290, by rfl⟩ : syracuseStep 1147441 = 860581) B860581
theorem B1147537 : Blo 802343 1147537 := bstep (se 2 (by rfl) ⟨430326, by rfl⟩ : syracuseStep 1147537 = 860653) B860653
theorem B2720465 : Blo 802343 2720465 := bstep (se 2 (by rfl) ⟨1020174, by rfl⟩ : syracuseStep 2720465 = 2040349) B2040349
theorem B15434549 : Blo 802343 15434549 := bstep (se 5 (by rfl) ⟨723494, by rfl⟩ : syracuseStep 15434549 = 1446989) B1446989
theorem B5145443 : Blo 802343 5145443 := bstep (se 1 (by rfl) ⟨3859082, by rfl⟩ : syracuseStep 5145443 = 7718165) B7718165
theorem B1016707 : Blo 802343 1016707 := bstep (se 1 (by rfl) ⟨762530, by rfl⟩ : syracuseStep 1016707 = 1525061) B1525061
theorem B1016803 : Blo 802343 1016803 := bstep (se 1 (by rfl) ⟨762602, by rfl⟩ : syracuseStep 1016803 = 1525205) B1525205
theorem B2294801 : Blo 802343 2294801 := bstep (se 2 (by rfl) ⟨860550, by rfl⟩ : syracuseStep 2294801 = 1721101) B1721101
theorem B1148033 : Blo 802343 1148033 := bstep (se 2 (by rfl) ⟨430512, by rfl⟩ : syracuseStep 1148033 = 861025) B861025
theorem B2721005 : Blo 802343 2721005 := bstep (se 3 (by rfl) ⟨510188, by rfl⟩ : syracuseStep 2721005 = 1020377) B1020377
theorem B2721059 : Blo 802343 2721059 := bstep (se 1 (by rfl) ⟨2040794, by rfl⟩ : syracuseStep 2721059 = 4081589) B4081589
theorem B2753837 : Blo 802343 2753837 := bstep (se 3 (by rfl) ⟨516344, by rfl⟩ : syracuseStep 2753837 = 1032689) B1032689
theorem B2033009 : Blo 802343 2033009 := bstep (se 2 (by rfl) ⟨762378, by rfl⟩ : syracuseStep 2033009 = 1524757) B1524757
theorem B2033059 : Blo 802343 2033059 := bstep (se 1 (by rfl) ⟨1524794, by rfl⟩ : syracuseStep 2033059 = 3049589) B3049589
theorem B1017299 : Blo 802343 1017299 := bstep (se 1 (by rfl) ⟨762974, by rfl⟩ : syracuseStep 1017299 = 1525949) B1525949
theorem B6522353 : Blo 802343 6522353 := bstep (se 2 (by rfl) ⟨2445882, by rfl⟩ : syracuseStep 6522353 = 4891765) B4891765
theorem B2033201 : Blo 802343 2033201 := bstep (se 2 (by rfl) ⟨762450, by rfl⟩ : syracuseStep 2033201 = 1524901) B1524901
theorem B2721329 : Blo 802343 2721329 := bstep (se 2 (by rfl) ⟨1020498, by rfl⟩ : syracuseStep 2721329 = 2040997) B2040997
theorem B3049073 : Blo 802343 3049073 := bstep (se 2 (by rfl) ⟨1143402, by rfl⟩ : syracuseStep 3049073 = 2286805) B2286805
theorem B1837187 : Blo 802343 1837187 := bstep (se 1 (by rfl) ⟨1377890, by rfl⟩ : syracuseStep 1837187 = 2755781) B2755781
theorem B1018003 : Blo 802343 1018003 := bstep (se 1 (by rfl) ⟨763502, by rfl⟩ : syracuseStep 1018003 = 1527005) B1527005
theorem B1018099 : Blo 802343 1018099 := bstep (se 1 (by rfl) ⟨763574, by rfl⟩ : syracuseStep 1018099 = 1527149) B1527149
theorem B2722097 : Blo 802343 2722097 := bstep (se 2 (by rfl) ⟨1020786, by rfl⟩ : syracuseStep 2722097 = 2041573) B2041573
theorem B13764977 : Blo 802343 13764977 := bstep (se 2 (by rfl) ⟨5161866, by rfl⟩ : syracuseStep 13764977 = 10323733) B10323733
theorem B3443057 : Blo 802343 3443057 := bstep (se 2 (by rfl) ⟨1291146, by rfl⟩ : syracuseStep 3443057 = 2582293) B2582293
theorem B4065713 : Blo 802343 4065713 := bstep (se 2 (by rfl) ⟨1524642, by rfl⟩ : syracuseStep 4065713 = 3049285) B3049285
theorem B1935875 : Blo 802343 1935875 := bstep (se 1 (by rfl) ⟨1451906, by rfl⟩ : syracuseStep 1935875 = 2903813) B2903813
theorem B2034193 : Blo 802343 2034193 := bstep (se 2 (by rfl) ⟨762822, by rfl⟩ : syracuseStep 2034193 = 1525645) B1525645
theorem B1935971 : Blo 802343 1935971 := bstep (se 1 (by rfl) ⟨1451978, by rfl⟩ : syracuseStep 1935971 = 2903957) B2903957
theorem B1018595 : Blo 802343 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B3672803 : Blo 802343 3672803 := bstep (se 1 (by rfl) ⟨2754602, by rfl⟩ : syracuseStep 3672803 = 5509205) B5509205
theorem B2034467 : Blo 802343 2034467 := bstep (se 1 (by rfl) ⟨1525850, by rfl⟩ : syracuseStep 2034467 = 3051701) B3051701
theorem B1379107 : Blo 802343 1379107 := bstep (se 1 (by rfl) ⟨1034330, by rfl⟩ : syracuseStep 1379107 = 2068661) B2068661
theorem B1739665 : Blo 802343 1739665 := bstep (se 2 (by rfl) ⟨652374, by rfl⟩ : syracuseStep 1739665 = 1304749) B1304749
theorem B2034659 : Blo 802343 2034659 := bstep (se 1 (by rfl) ⟨1525994, by rfl⟩ : syracuseStep 2034659 = 3051989) B3051989
theorem B3050531 : Blo 802343 3050531 := bstep (se 1 (by rfl) ⟨2287898, by rfl⟩ : syracuseStep 3050531 = 4575797) B4575797
theorem B1838225 : Blo 802343 1838225 := bstep (se 2 (by rfl) ⟨689334, by rfl⟩ : syracuseStep 1838225 = 1378669) B1378669
theorem B1805489 : Blo 802343 1805489 := bstep (se 2 (by rfl) ⟨677058, by rfl⟩ : syracuseStep 1805489 = 1354117) B1354117
theorem B1117363 : Blo 802343 1117363 := bstep (se 1 (by rfl) ⟨838022, by rfl⟩ : syracuseStep 1117363 = 1676045) B1676045
theorem B1805507 : Blo 802343 1805507 := bstep (se 1 (by rfl) ⟨1354130, by rfl⟩ : syracuseStep 1805507 = 2708261) B2708261
theorem B1019299 : Blo 802343 1019299 := bstep (se 1 (by rfl) ⟨764474, by rfl⟩ : syracuseStep 1019299 = 1528949) B1528949
theorem B1936817 : Blo 802343 1936817 := bstep (se 2 (by rfl) ⟨726306, by rfl⟩ : syracuseStep 1936817 = 1452613) B1452613
theorem B1805777 : Blo 802343 1805777 := bstep (se 2 (by rfl) ⟨677166, by rfl⟩ : syracuseStep 1805777 = 1354333) B1354333
theorem B1805795 : Blo 802343 1805795 := bstep (se 1 (by rfl) ⟨1354346, by rfl⟩ : syracuseStep 1805795 = 2708693) B2708693
theorem B1019395 : Blo 802343 1019395 := bstep (se 1 (by rfl) ⟨764546, by rfl⟩ : syracuseStep 1019395 = 1529093) B1529093
theorem B8261189 : Blo 802343 8261189 := bstep (se 4 (by rfl) ⟨774486, by rfl⟩ : syracuseStep 8261189 = 1548973) B1548973
theorem B1937105 : Blo 802343 1937105 := bstep (se 2 (by rfl) ⟨726414, by rfl⟩ : syracuseStep 1937105 = 1452829) B1452829
theorem B1806065 : Blo 802343 1806065 := bstep (se 2 (by rfl) ⟨677274, by rfl⟩ : syracuseStep 1806065 = 1354549) B1354549
theorem B1806083 : Blo 802343 1806083 := bstep (se 1 (by rfl) ⟨1354562, by rfl⟩ : syracuseStep 1806083 = 2709125) B2709125
theorem B4067171 : Blo 802343 4067171 := bstep (se 1 (by rfl) ⟨3050378, by rfl⟩ : syracuseStep 4067171 = 6100757) B6100757
theorem B1085329 : Blo 802343 1085329 := bstep (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) B813997
theorem B2035601 : Blo 802343 2035601 := bstep (se 2 (by rfl) ⟨763350, by rfl⟩ : syracuseStep 2035601 = 1526701) B1526701
theorem B1937315 : Blo 802343 1937315 := bstep (se 1 (by rfl) ⟨1452986, by rfl⟩ : syracuseStep 1937315 = 2905973) B2905973
theorem B5148593 : Blo 802343 5148593 := bstep (se 2 (by rfl) ⟨1930722, by rfl⟩ : syracuseStep 5148593 = 3861445) B3861445
theorem B2035651 : Blo 802343 2035651 := bstep (se 1 (by rfl) ⟨1526738, by rfl⟩ : syracuseStep 2035651 = 3053477) B3053477
theorem B5148643 : Blo 802343 5148643 := bstep (se 1 (by rfl) ⟨3861482, by rfl⟩ : syracuseStep 5148643 = 7722965) B7722965
theorem B1019891 : Blo 802343 1019891 := bstep (se 1 (by rfl) ⟨764918, by rfl⟩ : syracuseStep 1019891 = 1529837) B1529837
theorem B3051533 : Blo 802343 3051533 := bstep (se 3 (by rfl) ⟨572162, by rfl⟩ : syracuseStep 3051533 = 1144325) B1144325
theorem B1806353 : Blo 802343 1806353 := bstep (se 2 (by rfl) ⟨677382, by rfl⟩ : syracuseStep 1806353 = 1354765) B1354765
theorem B1806371 : Blo 802343 1806371 := bstep (se 1 (by rfl) ⟨1354778, by rfl⟩ : syracuseStep 1806371 = 2709557) B2709557
theorem B2035793 : Blo 802343 2035793 := bstep (se 2 (by rfl) ⟨763422, by rfl⟩ : syracuseStep 2035793 = 1526845) B1526845
theorem B10293389 : Blo 802343 10293389 := bstep (se 3 (by rfl) ⟨1930010, by rfl⟩ : syracuseStep 10293389 = 3860021) B3860021
theorem B1806641 : Blo 802343 1806641 := bstep (se 2 (by rfl) ⟨677490, by rfl⟩ : syracuseStep 1806641 = 1354981) B1354981
theorem B3477809 : Blo 802343 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B1446211 : Blo 802343 1446211 := bstep (se 1 (by rfl) ⟨1084658, by rfl⟩ : syracuseStep 1446211 = 2169317) B2169317
theorem B1806659 : Blo 802343 1806659 := bstep (se 1 (by rfl) ⟨1354994, by rfl⟩ : syracuseStep 1806659 = 2709989) B2709989
theorem B6099299 : Blo 802343 6099299 := bstep (se 1 (by rfl) ⟨4574474, by rfl⟩ : syracuseStep 6099299 = 9148949) B9148949
theorem B4886897 : Blo 802343 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B1085843 : Blo 802343 1085843 := bstep (se 1 (by rfl) ⟨814382, by rfl⟩ : syracuseStep 1085843 = 1628765) B1628765
theorem B1806929 : Blo 802343 1806929 := bstep (se 2 (by rfl) ⟨677598, by rfl⟩ : syracuseStep 1806929 = 1355197) B1355197
theorem B1806947 : Blo 802343 1806947 := bstep (se 1 (by rfl) ⟨1355210, by rfl⟩ : syracuseStep 1806947 = 2710421) B2710421
theorem B4067981 : Blo 802343 4067981 := bstep (se 3 (by rfl) ⟨762746, by rfl⟩ : syracuseStep 4067981 = 1525493) B1525493
theorem B1446673 : Blo 802343 1446673 := bstep (se 2 (by rfl) ⟨542502, by rfl⟩ : syracuseStep 1446673 = 1085005) B1085005
theorem B1807217 : Blo 802343 1807217 := bstep (se 2 (by rfl) ⟨677706, by rfl⟩ : syracuseStep 1807217 = 1355413) B1355413
theorem B1086323 : Blo 802343 1086323 := bstep (se 1 (by rfl) ⟨814742, by rfl⟩ : syracuseStep 1086323 = 1629485) B1629485
theorem B1807235 : Blo 802343 1807235 := bstep (se 1 (by rfl) ⟨1355426, by rfl⟩ : syracuseStep 1807235 = 2710853) B2710853
theorem B857027 : Blo 802343 857027 := bstep (se 1 (by rfl) ⟨642770, by rfl⟩ : syracuseStep 857027 = 1285541) B1285541
theorem B2790413 : Blo 802343 2790413 := bstep (se 3 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 2790413 = 1046405) B1046405
theorem B2036785 : Blo 802343 2036785 := bstep (se 2 (by rfl) ⟨763794, by rfl⟩ : syracuseStep 2036785 = 1527589) B1527589
theorem B9147491 : Blo 802343 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B1807505 : Blo 802343 1807505 := bstep (se 2 (by rfl) ⟨677814, by rfl⟩ : syracuseStep 1807505 = 1355629) B1355629
theorem B1807523 : Blo 802343 1807523 := bstep (se 1 (by rfl) ⟨1355642, by rfl⟩ : syracuseStep 1807523 = 2711285) B2711285
theorem B58758371 : Blo 802343 58758371 := bstep (se 1 (by rfl) ⟨44068778, by rfl⟩ : syracuseStep 58758371 = 88137557) B88137557
theorem B2037059 : Blo 802343 2037059 := bstep (se 1 (by rfl) ⟨1527794, by rfl⟩ : syracuseStep 2037059 = 3055589) B3055589
theorem B1611107 : Blo 802343 1611107 := bstep (se 1 (by rfl) ⟨1208330, by rfl⟩ : syracuseStep 1611107 = 2416661) B2416661
theorem B1807793 : Blo 802343 1807793 := bstep (se 2 (by rfl) ⟨677922, by rfl⟩ : syracuseStep 1807793 = 1355845) B1355845
theorem B1807811 : Blo 802343 1807811 := bstep (se 1 (by rfl) ⟨1355858, by rfl⟩ : syracuseStep 1807811 = 2711717) B2711717
theorem B2037251 : Blo 802343 2037251 := bstep (se 1 (by rfl) ⟨1527938, by rfl⟩ : syracuseStep 2037251 = 3055877) B3055877
theorem B2233937 : Blo 802343 2233937 := bstep (se 2 (by rfl) ⟨837726, by rfl⟩ : syracuseStep 2233937 = 1675453) B1675453
theorem B1808081 : Blo 802343 1808081 := bstep (se 2 (by rfl) ⟨678030, by rfl⟩ : syracuseStep 1808081 = 1356061) B1356061
theorem B1808099 : Blo 802343 1808099 := bstep (se 1 (by rfl) ⟨1356074, by rfl⟩ : syracuseStep 1808099 = 2712149) B2712149
theorem B1808369 : Blo 802343 1808369 := bstep (se 2 (by rfl) ⟨678138, by rfl⟩ : syracuseStep 1808369 = 1356277) B1356277
theorem B1808387 : Blo 802343 1808387 := bstep (se 1 (by rfl) ⟨1356290, by rfl⟩ : syracuseStep 1808387 = 2712581) B2712581
theorem B3053645 : Blo 802343 3053645 := bstep (se 3 (by rfl) ⟨572558, by rfl⟩ : syracuseStep 3053645 = 1145117) B1145117
theorem B1808657 : Blo 802343 1808657 := bstep (se 2 (by rfl) ⟨678246, by rfl⟩ : syracuseStep 1808657 = 1356493) B1356493
theorem B1808675 : Blo 802343 1808675 := bstep (se 1 (by rfl) ⟨1356506, by rfl⟩ : syracuseStep 1808675 = 2713013) B2713013
theorem B5151053 : Blo 802343 5151053 := bstep (se 3 (by rfl) ⟨965822, by rfl⟩ : syracuseStep 5151053 = 1931645) B1931645
theorem B2038193 : Blo 802343 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B2038243 : Blo 802343 2038243 := bstep (se 1 (by rfl) ⟨1528682, by rfl⟩ : syracuseStep 2038243 = 3057365) B3057365
theorem B1808945 : Blo 802343 1808945 := bstep (se 2 (by rfl) ⟨678354, by rfl⟩ : syracuseStep 1808945 = 1356709) B1356709
theorem B1808963 : Blo 802343 1808963 := bstep (se 1 (by rfl) ⟨1356722, by rfl⟩ : syracuseStep 1808963 = 2713445) B2713445
theorem B2038385 : Blo 802343 2038385 := bstep (se 2 (by rfl) ⟨764394, by rfl⟩ : syracuseStep 2038385 = 1528789) B1528789
theorem B1809233 : Blo 802343 1809233 := bstep (se 2 (by rfl) ⟨678462, by rfl⟩ : syracuseStep 1809233 = 1356925) B1356925
theorem B1809251 : Blo 802343 1809251 := bstep (se 1 (by rfl) ⟨1356938, by rfl⟩ : syracuseStep 1809251 = 2713877) B2713877
theorem B3054449 : Blo 802343 3054449 := bstep (se 2 (by rfl) ⟨1145418, by rfl⟩ : syracuseStep 3054449 = 2290837) B2290837
theorem B859043 : Blo 802343 859043 := bstep (se 1 (by rfl) ⟨644282, by rfl⟩ : syracuseStep 859043 = 1288565) B1288565
theorem B1809521 : Blo 802343 1809521 := bstep (se 2 (by rfl) ⟨678570, by rfl⟩ : syracuseStep 1809521 = 1357141) B1357141
theorem B1809539 : Blo 802343 1809539 := bstep (se 1 (by rfl) ⟨1357154, by rfl⟩ : syracuseStep 1809539 = 2714309) B2714309
theorem B3873997 : Blo 802343 3873997 := bstep (se 3 (by rfl) ⟨726374, by rfl⟩ : syracuseStep 3873997 = 1452749) B1452749
theorem B1809809 : Blo 802343 1809809 := bstep (se 2 (by rfl) ⟨678678, by rfl⟩ : syracuseStep 1809809 = 1357357) B1357357
theorem B1809827 : Blo 802343 1809827 := bstep (se 1 (by rfl) ⟨1357370, by rfl⟩ : syracuseStep 1809827 = 2714741) B2714741
theorem B1220035 : Blo 802343 1220035 := bstep (se 1 (by rfl) ⟨915026, by rfl⟩ : syracuseStep 1220035 = 1830053) B1830053
theorem B4070897 : Blo 802343 4070897 := bstep (se 2 (by rfl) ⟨1526586, by rfl⟩ : syracuseStep 4070897 = 3053173) B3053173
theorem B3055117 : Blo 802343 3055117 := bstep (se 3 (by rfl) ⟨572834, by rfl⟩ : syracuseStep 3055117 = 1145669) B1145669
theorem B1285649 : Blo 802343 1285649 := bstep (se 2 (by rfl) ⟨482118, by rfl⟩ : syracuseStep 1285649 = 964237) B964237
theorem B1089091 : Blo 802343 1089091 := bstep (se 1 (by rfl) ⟨816818, by rfl⟩ : syracuseStep 1089091 = 1633637) B1633637
theorem B2039377 : Blo 802343 2039377 := bstep (se 2 (by rfl) ⟨764766, by rfl⟩ : syracuseStep 2039377 = 1529533) B1529533
theorem B1810097 : Blo 802343 1810097 := bstep (se 2 (by rfl) ⟨678786, by rfl⟩ : syracuseStep 1810097 = 1357573) B1357573
theorem B1810115 : Blo 802343 1810115 := bstep (se 1 (by rfl) ⟨1357586, by rfl⟩ : syracuseStep 1810115 = 2715173) B2715173
theorem B859987 : Blo 802343 859987 := bstep (se 1 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 859987 = 1289981) B1289981
theorem B2039651 : Blo 802343 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B1810385 : Blo 802343 1810385 := bstep (se 2 (by rfl) ⟨678894, by rfl⟩ : syracuseStep 1810385 = 1357789) B1357789
theorem B1810403 : Blo 802343 1810403 := bstep (se 1 (by rfl) ⟨1357802, by rfl⟩ : syracuseStep 1810403 = 2715605) B2715605
theorem B1286161 : Blo 802343 1286161 := bstep (se 2 (by rfl) ⟨482310, by rfl⟩ : syracuseStep 1286161 = 964621) B964621
theorem B2039843 : Blo 802343 2039843 := bstep (se 1 (by rfl) ⟨1529882, by rfl⟩ : syracuseStep 2039843 = 3059765) B3059765
theorem B1220753 : Blo 802343 1220753 := bstep (se 2 (by rfl) ⟨457782, by rfl⟩ : syracuseStep 1220753 = 915565) B915565
theorem B1810673 : Blo 802343 1810673 := bstep (se 2 (by rfl) ⟨679002, by rfl⟩ : syracuseStep 1810673 = 1358005) B1358005
theorem B1810691 : Blo 802343 1810691 := bstep (se 1 (by rfl) ⟨1358018, by rfl⟩ : syracuseStep 1810691 = 2716037) B2716037
theorem B3055907 : Blo 802343 3055907 := bstep (se 1 (by rfl) ⟨2291930, by rfl⟩ : syracuseStep 3055907 = 4583861) B4583861
theorem B1810961 : Blo 802343 1810961 := bstep (se 2 (by rfl) ⟨679110, by rfl⟩ : syracuseStep 1810961 = 1358221) B1358221
theorem B1810979 : Blo 802343 1810979 := bstep (se 1 (by rfl) ⟨1358234, by rfl⟩ : syracuseStep 1810979 = 2716469) B2716469
theorem B9183941 : Blo 802343 9183941 := bstep (se 4 (by rfl) ⟨860994, by rfl⟩ : syracuseStep 9183941 = 1721989) B1721989
theorem B1811249 : Blo 802343 1811249 := bstep (se 2 (by rfl) ⟨679218, by rfl⟩ : syracuseStep 1811249 = 1358437) B1358437
theorem B1811267 : Blo 802343 1811267 := bstep (se 1 (by rfl) ⟨1358450, by rfl⟩ : syracuseStep 1811267 = 2716901) B2716901
theorem B4072355 : Blo 802343 4072355 := bstep (se 1 (by rfl) ⟨3054266, by rfl⟩ : syracuseStep 4072355 = 6108533) B6108533
theorem B3056561 : Blo 802343 3056561 := bstep (se 2 (by rfl) ⟨1146210, by rfl⟩ : syracuseStep 3056561 = 2292421) B2292421
theorem B2040785 : Blo 802343 2040785 := bstep (se 2 (by rfl) ⟨765294, by rfl⟩ : syracuseStep 2040785 = 1530589) B1530589
theorem B2040835 : Blo 802343 2040835 := bstep (se 1 (by rfl) ⟨1530626, by rfl⟩ : syracuseStep 2040835 = 3061253) B3061253
theorem B1811537 : Blo 802343 1811537 := bstep (se 2 (by rfl) ⟨679326, by rfl⟩ : syracuseStep 1811537 = 1358653) B1358653
theorem B1811555 : Blo 802343 1811555 := bstep (se 1 (by rfl) ⟨1358666, by rfl⟩ : syracuseStep 1811555 = 2717333) B2717333
theorem B2892941 : Blo 802343 2892941 := bstep (se 3 (by rfl) ⟨542426, by rfl⟩ : syracuseStep 2892941 = 1084853) B1084853
theorem B2040977 : Blo 802343 2040977 := bstep (se 2 (by rfl) ⟨765366, by rfl⟩ : syracuseStep 2040977 = 1530733) B1530733
theorem B1287443 : Blo 802343 1287443 := bstep (se 1 (by rfl) ⟨965582, by rfl⟩ : syracuseStep 1287443 = 1931165) B1931165
theorem B1811825 : Blo 802343 1811825 := bstep (se 2 (by rfl) ⟨679434, by rfl⟩ : syracuseStep 1811825 = 1358869) B1358869
theorem B1811843 : Blo 802343 1811843 := bstep (se 1 (by rfl) ⟨1358882, by rfl⟩ : syracuseStep 1811843 = 2717765) B2717765
theorem B1287571 : Blo 802343 1287571 := bstep (se 1 (by rfl) ⟨965678, by rfl⟩ : syracuseStep 1287571 = 1931357) B1931357
theorem B1287713 : Blo 802343 1287713 := bstep (se 2 (by rfl) ⟨482892, by rfl⟩ : syracuseStep 1287713 = 965785) B965785
theorem B6104645 : Blo 802343 6104645 := bstep (se 4 (by rfl) ⟨572310, by rfl⟩ : syracuseStep 6104645 = 1144621) B1144621
theorem B1812113 : Blo 802343 1812113 := bstep (se 2 (by rfl) ⟨679542, by rfl⟩ : syracuseStep 1812113 = 1359085) B1359085
theorem B1812131 : Blo 802343 1812131 := bstep (se 1 (by rfl) ⟨1359098, by rfl⟩ : syracuseStep 1812131 = 2718197) B2718197
theorem B4073165 : Blo 802343 4073165 := bstep (se 3 (by rfl) ⟨763718, by rfl⟩ : syracuseStep 4073165 = 1527437) B1527437
theorem B1451747 : Blo 802343 1451747 := bstep (se 1 (by rfl) ⟨1088810, by rfl⟩ : syracuseStep 1451747 = 2177621) B2177621
theorem B829235 : Blo 802343 829235 := bstep (se 1 (by rfl) ⟨621926, by rfl⟩ : syracuseStep 829235 = 1243853) B1243853
theorem B1288001 : Blo 802343 1288001 := bstep (se 2 (by rfl) ⟨483000, by rfl⟩ : syracuseStep 1288001 = 966001) B966001
theorem B1812401 : Blo 802343 1812401 := bstep (se 2 (by rfl) ⟨679650, by rfl⟩ : syracuseStep 1812401 = 1359301) B1359301
theorem B1812419 : Blo 802343 1812419 := bstep (se 1 (by rfl) ⟨1359314, by rfl⟩ : syracuseStep 1812419 = 2718629) B2718629
theorem B11610053 : Blo 802343 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B18589667 : Blo 802343 18589667 := bstep (se 1 (by rfl) ⟨13942250, by rfl⟩ : syracuseStep 18589667 = 27884501) B27884501
theorem B3483661 : Blo 802343 3483661 := bstep (se 3 (by rfl) ⟨653186, by rfl⟩ : syracuseStep 3483661 = 1306373) B1306373
theorem B1812689 : Blo 802343 1812689 := bstep (se 2 (by rfl) ⟨679758, by rfl⟩ : syracuseStep 1812689 = 1359517) B1359517
theorem B1353955 : Blo 802343 1353955 := bstep (se 1 (by rfl) ⟨1015466, by rfl⟩ : syracuseStep 1353955 = 2030933) B2030933
theorem B1714403 : Blo 802343 1714403 := bstep (se 1 (by rfl) ⟨1285802, by rfl⟩ : syracuseStep 1714403 = 2571605) B2571605
theorem B1812707 : Blo 802343 1812707 := bstep (se 1 (by rfl) ⟨1359530, by rfl⟩ : syracuseStep 1812707 = 2719061) B2719061
theorem B3058019 : Blo 802343 3058019 := bstep (se 1 (by rfl) ⟨2293514, by rfl⟩ : syracuseStep 3058019 = 4587029) B4587029
theorem B3058033 : Blo 802343 3058033 := bstep (se 2 (by rfl) ⟨1146762, by rfl⟩ : syracuseStep 3058033 = 2293525) B2293525
theorem B1354097 : Blo 802343 1354097 := bstep (se 2 (by rfl) ⟨507786, by rfl⟩ : syracuseStep 1354097 = 1015573) B1015573
theorem B1354225 : Blo 802343 1354225 := bstep (se 2 (by rfl) ⟨507834, by rfl⟩ : syracuseStep 1354225 = 1015669) B1015669
theorem B1812977 : Blo 802343 1812977 := bstep (se 2 (by rfl) ⟨679866, by rfl⟩ : syracuseStep 1812977 = 1359733) B1359733
theorem B1812995 : Blo 802343 1812995 := bstep (se 1 (by rfl) ⟨1359746, by rfl⟩ : syracuseStep 1812995 = 2719493) B2719493
theorem B1354259 : Blo 802343 1354259 := bstep (se 1 (by rfl) ⟨1015694, by rfl⟩ : syracuseStep 1354259 = 2031389) B2031389
theorem B1288801 : Blo 802343 1288801 := bstep (se 2 (by rfl) ⟨483300, by rfl⟩ : syracuseStep 1288801 = 966601) B966601
theorem B1354387 : Blo 802343 1354387 := bstep (se 1 (by rfl) ⟨1015790, by rfl⟩ : syracuseStep 1354387 = 2031581) B2031581
theorem B2206403 : Blo 802343 2206403 := bstep (se 1 (by rfl) ⟨1654802, by rfl⟩ : syracuseStep 2206403 = 3309605) B3309605
theorem B1813265 : Blo 802343 1813265 := bstep (se 2 (by rfl) ⟨679974, by rfl⟩ : syracuseStep 1813265 = 1359949) B1359949
theorem B1354529 : Blo 802343 1354529 := bstep (se 2 (by rfl) ⟨507948, by rfl⟩ : syracuseStep 1354529 = 1015897) B1015897
theorem B1813283 : Blo 802343 1813283 := bstep (se 1 (by rfl) ⟨1359962, by rfl⟩ : syracuseStep 1813283 = 2719925) B2719925
theorem B1223537 : Blo 802343 1223537 := bstep (se 2 (by rfl) ⟨458826, by rfl⟩ : syracuseStep 1223537 = 917653) B917653
theorem B1354657 : Blo 802343 1354657 := bstep (se 2 (by rfl) ⟨507996, by rfl⟩ : syracuseStep 1354657 = 1015993) B1015993
theorem B1354691 : Blo 802343 1354691 := bstep (se 1 (by rfl) ⟨1016018, by rfl⟩ : syracuseStep 1354691 = 2032037) B2032037
theorem B1813553 : Blo 802343 1813553 := bstep (se 2 (by rfl) ⟨680082, by rfl⟩ : syracuseStep 1813553 = 1360165) B1360165
theorem B1354819 : Blo 802343 1354819 := bstep (se 1 (by rfl) ⟨1016114, by rfl⟩ : syracuseStep 1354819 = 2032229) B2032229
theorem B1813571 : Blo 802343 1813571 := bstep (se 1 (by rfl) ⟨1360178, by rfl⟩ : syracuseStep 1813571 = 2720357) B2720357
theorem B1354961 : Blo 802343 1354961 := bstep (se 2 (by rfl) ⟨508110, by rfl⟩ : syracuseStep 1354961 = 1016221) B1016221
theorem B2174161 : Blo 802343 2174161 := bstep (se 2 (by rfl) ⟨815310, by rfl⟩ : syracuseStep 2174161 = 1630621) B1630621
theorem B1223939 : Blo 802343 1223939 := bstep (se 1 (by rfl) ⟨917954, by rfl⟩ : syracuseStep 1223939 = 1835909) B1835909
theorem B1355089 : Blo 802343 1355089 := bstep (se 2 (by rfl) ⟨508158, by rfl⟩ : syracuseStep 1355089 = 1016317) B1016317
theorem B1813841 : Blo 802343 1813841 := bstep (se 2 (by rfl) ⟨680190, by rfl⟩ : syracuseStep 1813841 = 1360381) B1360381
theorem B1813859 : Blo 802343 1813859 := bstep (se 1 (by rfl) ⟨1360394, by rfl⟩ : syracuseStep 1813859 = 2720789) B2720789
theorem B1355123 : Blo 802343 1355123 := bstep (se 1 (by rfl) ⟨1016342, by rfl⟩ : syracuseStep 1355123 = 2032685) B2032685
theorem B1715651 : Blo 802343 1715651 := bstep (se 1 (by rfl) ⟨1286738, by rfl⟩ : syracuseStep 1715651 = 2573477) B2573477
theorem B1355251 : Blo 802343 1355251 := bstep (se 1 (by rfl) ⟨1016438, by rfl⟩ : syracuseStep 1355251 = 2032877) B2032877
theorem B1814129 : Blo 802343 1814129 := bstep (se 2 (by rfl) ⟨680298, by rfl⟩ : syracuseStep 1814129 = 1360597) B1360597
theorem B1355393 : Blo 802343 1355393 := bstep (se 2 (by rfl) ⟨508272, by rfl⟩ : syracuseStep 1355393 = 1016545) B1016545
theorem B1814147 : Blo 802343 1814147 := bstep (se 1 (by rfl) ⟨1360610, by rfl⟩ : syracuseStep 1814147 = 2721221) B2721221
theorem B2174627 : Blo 802343 2174627 := bstep (se 1 (by rfl) ⟨1630970, by rfl⟩ : syracuseStep 2174627 = 3261941) B3261941
theorem B1224401 : Blo 802343 1224401 := bstep (se 2 (by rfl) ⟨459150, by rfl⟩ : syracuseStep 1224401 = 918301) B918301
theorem B1650403 : Blo 802343 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B1355521 : Blo 802343 1355521 := bstep (se 2 (by rfl) ⟨508320, by rfl⟩ : syracuseStep 1355521 = 1016641) B1016641
theorem B1355555 : Blo 802343 1355555 := bstep (se 1 (by rfl) ⟨1016666, by rfl⟩ : syracuseStep 1355555 = 2033333) B2033333
theorem B1290019 : Blo 802343 1290019 := bstep (se 1 (by rfl) ⟨967514, by rfl⟩ : syracuseStep 1290019 = 1935029) B1935029
theorem B3059491 : Blo 802343 3059491 := bstep (se 1 (by rfl) ⟨2294618, by rfl⟩ : syracuseStep 3059491 = 4589237) B4589237
theorem B1355683 : Blo 802343 1355683 := bstep (se 1 (by rfl) ⟨1016762, by rfl⟩ : syracuseStep 1355683 = 2033525) B2033525
theorem B17379269 : Blo 802343 17379269 := bstep (se 4 (by rfl) ⟨1629306, by rfl⟩ : syracuseStep 17379269 = 3258613) B3258613
theorem B1716241 : Blo 802343 1716241 := bstep (se 2 (by rfl) ⟨643590, by rfl⟩ : syracuseStep 1716241 = 1287181) B1287181
theorem B1355825 : Blo 802343 1355825 := bstep (se 2 (by rfl) ⟨508434, by rfl⟩ : syracuseStep 1355825 = 1016869) B1016869
theorem B6533219 : Blo 802343 6533219 := bstep (se 1 (by rfl) ⟨4899914, by rfl⟩ : syracuseStep 6533219 = 9799829) B9799829
theorem B1355953 : Blo 802343 1355953 := bstep (se 2 (by rfl) ⟨508482, by rfl⟩ : syracuseStep 1355953 = 1016965) B1016965
theorem B1355987 : Blo 802343 1355987 := bstep (se 1 (by rfl) ⟨1016990, by rfl⟩ : syracuseStep 1355987 = 2033981) B2033981
theorem B1224931 : Blo 802343 1224931 := bstep (se 1 (by rfl) ⟨918698, by rfl⟩ : syracuseStep 1224931 = 1837397) B1837397
theorem B1356115 : Blo 802343 1356115 := bstep (se 1 (by rfl) ⟨1017086, by rfl⟩ : syracuseStep 1356115 = 2034173) B2034173
theorem B1356257 : Blo 802343 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B1290737 : Blo 802343 1290737 := bstep (se 2 (by rfl) ⟨484026, by rfl⟩ : syracuseStep 1290737 = 968053) B968053
theorem B4076081 : Blo 802343 4076081 := bstep (se 2 (by rfl) ⟨1528530, by rfl⟩ : syracuseStep 4076081 = 3057061) B3057061
theorem B1356385 : Blo 802343 1356385 := bstep (se 2 (by rfl) ⟨508644, by rfl⟩ : syracuseStep 1356385 = 1017289) B1017289
theorem B1356419 : Blo 802343 1356419 := bstep (se 1 (by rfl) ⟨1017314, by rfl⟩ : syracuseStep 1356419 = 2034629) B2034629
theorem B5157539 : Blo 802343 5157539 := bstep (se 1 (by rfl) ⟨3868154, by rfl⟩ : syracuseStep 5157539 = 7736309) B7736309
theorem B4338373 : Blo 802343 4338373 := bstep (se 4 (by rfl) ⟨406722, by rfl⟩ : syracuseStep 4338373 = 813445) B813445
theorem B6861509 : Blo 802343 6861509 := bstep (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) B1286533
theorem B1356547 : Blo 802343 1356547 := bstep (se 1 (by rfl) ⟨1017410, by rfl⟩ : syracuseStep 1356547 = 2034821) B2034821
theorem B4633357 : Blo 802343 4633357 := bstep (se 3 (by rfl) ⟨868754, by rfl⟩ : syracuseStep 4633357 = 1737509) B1737509
theorem B2175761 : Blo 802343 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B1291025 : Blo 802343 1291025 := bstep (se 2 (by rfl) ⟨484134, by rfl⟩ : syracuseStep 1291025 = 968269) B968269
theorem B1356689 : Blo 802343 1356689 := bstep (se 2 (by rfl) ⟨508758, by rfl⟩ : syracuseStep 1356689 = 1017517) B1017517
theorem B1291249 : Blo 802343 1291249 := bstep (se 2 (by rfl) ⟨484218, by rfl⟩ : syracuseStep 1291249 = 968437) B968437
theorem B1356817 : Blo 802343 1356817 := bstep (se 2 (by rfl) ⟨508806, by rfl⟩ : syracuseStep 1356817 = 1017613) B1017613
theorem B1356851 : Blo 802343 1356851 := bstep (se 1 (by rfl) ⟨1017638, by rfl⟩ : syracuseStep 1356851 = 2035277) B2035277
theorem B1356979 : Blo 802343 1356979 := bstep (se 1 (by rfl) ⟨1017734, by rfl⟩ : syracuseStep 1356979 = 2035469) B2035469
theorem B1357121 : Blo 802343 1357121 := bstep (se 2 (by rfl) ⟨508920, by rfl⟩ : syracuseStep 1357121 = 1017841) B1017841
theorem B1357249 : Blo 802343 1357249 := bstep (se 2 (by rfl) ⟨508968, by rfl⟩ : syracuseStep 1357249 = 1017937) B1017937
theorem B1357283 : Blo 802343 1357283 := bstep (se 1 (by rfl) ⟨1017962, by rfl⟩ : syracuseStep 1357283 = 2035925) B2035925
theorem B2176561 : Blo 802343 2176561 := bstep (se 2 (by rfl) ⟨816210, by rfl⟩ : syracuseStep 2176561 = 1632421) B1632421
theorem B1357411 : Blo 802343 1357411 := bstep (se 1 (by rfl) ⟨1018058, by rfl⟩ : syracuseStep 1357411 = 2036117) B2036117
theorem B11024099 : Blo 802343 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B1357553 : Blo 802343 1357553 := bstep (se 2 (by rfl) ⟨509082, by rfl⟩ : syracuseStep 1357553 = 1018165) B1018165
theorem B4896611 : Blo 802343 4896611 := bstep (se 1 (by rfl) ⟨3672458, by rfl⟩ : syracuseStep 4896611 = 7344917) B7344917
theorem B1357681 : Blo 802343 1357681 := bstep (se 2 (by rfl) ⟨509130, by rfl⟩ : syracuseStep 1357681 = 1018261) B1018261
theorem B1357715 : Blo 802343 1357715 := bstep (se 1 (by rfl) ⟨1018286, by rfl⟩ : syracuseStep 1357715 = 2036573) B2036573
theorem B4077539 : Blo 802343 4077539 := bstep (se 1 (by rfl) ⟨3058154, by rfl⟩ : syracuseStep 4077539 = 6116309) B6116309
theorem B1357843 : Blo 802343 1357843 := bstep (se 1 (by rfl) ⟨1018382, by rfl⟩ : syracuseStep 1357843 = 2036765) B2036765
theorem B1357985 : Blo 802343 1357985 := bstep (se 2 (by rfl) ⟨509244, by rfl⟩ : syracuseStep 1357985 = 1018489) B1018489
theorem B1358113 : Blo 802343 1358113 := bstep (se 2 (by rfl) ⟨509292, by rfl⟩ : syracuseStep 1358113 = 1018585) B1018585
theorem B1358147 : Blo 802343 1358147 := bstep (se 1 (by rfl) ⟨1018610, by rfl⟩ : syracuseStep 1358147 = 2037221) B2037221
theorem B964963 : Blo 802343 964963 := bstep (se 1 (by rfl) ⟨723722, by rfl⟩ : syracuseStep 964963 = 1447445) B1447445
theorem B1358275 : Blo 802343 1358275 := bstep (se 1 (by rfl) ⟨1018706, by rfl⟩ : syracuseStep 1358275 = 2037413) B2037413
theorem B1358417 : Blo 802343 1358417 := bstep (se 2 (by rfl) ⟨509406, by rfl⟩ : syracuseStep 1358417 = 1018813) B1018813
theorem B1587811 : Blo 802343 1587811 := bstep (se 1 (by rfl) ⟨1190858, by rfl⟩ : syracuseStep 1587811 = 2381717) B2381717
theorem B1358545 : Blo 802343 1358545 := bstep (se 2 (by rfl) ⟨509454, by rfl⟩ : syracuseStep 1358545 = 1018909) B1018909
theorem B1358579 : Blo 802343 1358579 := bstep (se 1 (by rfl) ⟨1018934, by rfl⟩ : syracuseStep 1358579 = 2037869) B2037869
theorem B4078349 : Blo 802343 4078349 := bstep (se 3 (by rfl) ⟨764690, by rfl⟩ : syracuseStep 4078349 = 1529381) B1529381
theorem B2177837 : Blo 802343 2177837 := bstep (se 3 (by rfl) ⟨408344, by rfl⟩ : syracuseStep 2177837 = 816689) B816689
theorem B1358707 : Blo 802343 1358707 := bstep (se 1 (by rfl) ⟨1019030, by rfl⟩ : syracuseStep 1358707 = 2038061) B2038061
theorem B3980209 : Blo 802343 3980209 := bstep (se 2 (by rfl) ⟨1492578, by rfl⟩ : syracuseStep 3980209 = 2985157) B2985157
theorem B1358849 : Blo 802343 1358849 := bstep (se 2 (by rfl) ⟨509568, by rfl⟩ : syracuseStep 1358849 = 1019137) B1019137
theorem B1358977 : Blo 802343 1358977 := bstep (se 2 (by rfl) ⟨509616, by rfl⟩ : syracuseStep 1358977 = 1019233) B1019233
theorem B1719427 : Blo 802343 1719427 := bstep (se 1 (by rfl) ⟨1289570, by rfl⟩ : syracuseStep 1719427 = 2579141) B2579141
theorem B1359011 : Blo 802343 1359011 := bstep (se 1 (by rfl) ⟨1019258, by rfl⟩ : syracuseStep 1359011 = 2038517) B2038517
theorem B6110477 : Blo 802343 6110477 := bstep (se 3 (by rfl) ⟨1145714, by rfl⟩ : syracuseStep 6110477 = 2291429) B2291429
theorem B1359139 : Blo 802343 1359139 := bstep (se 1 (by rfl) ⟨1019354, by rfl⟩ : syracuseStep 1359139 = 2038709) B2038709
theorem B1359281 : Blo 802343 1359281 := bstep (se 2 (by rfl) ⟨509730, by rfl⟩ : syracuseStep 1359281 = 1019461) B1019461
theorem B1359409 : Blo 802343 1359409 := bstep (se 2 (by rfl) ⟨509778, by rfl⟩ : syracuseStep 1359409 = 1019557) B1019557
theorem B802355 : Blo 802343 802355 := bstep (se 1 (by rfl) ⟨601766, by rfl⟩ : syracuseStep 802355 = 1203533) B1203533
theorem B802371 : Blo 802343 802371 := bstep (se 1 (by rfl) ⟨601778, by rfl⟩ : syracuseStep 802371 = 1203557) B1203557
theorem B802387 : Blo 802343 802387 := bstep (se 1 (by rfl) ⟨601790, by rfl⟩ : syracuseStep 802387 = 1203581) B1203581
theorem B1359443 : Blo 802343 1359443 := bstep (se 1 (by rfl) ⟨1019582, by rfl⟩ : syracuseStep 1359443 = 2039165) B2039165
theorem B1523299 : Blo 802343 1523299 := bstep (se 1 (by rfl) ⟨1142474, by rfl⟩ : syracuseStep 1523299 = 2284949) B2284949
theorem B802403 : Blo 802343 802403 := bstep (se 1 (by rfl) ⟨601802, by rfl⟩ : syracuseStep 802403 = 1203605) B1203605
theorem B2178659 : Blo 802343 2178659 := bstep (se 1 (by rfl) ⟨1633994, by rfl⟩ : syracuseStep 2178659 = 3267989) B3267989
theorem B2440813 : Blo 802343 2440813 := bstep (se 3 (by rfl) ⟨457652, by rfl⟩ : syracuseStep 2440813 = 915305) B915305
theorem B802419 : Blo 802343 802419 := bstep (se 1 (by rfl) ⟨601814, by rfl⟩ : syracuseStep 802419 = 1203629) B1203629
theorem B802435 : Blo 802343 802435 := bstep (se 1 (by rfl) ⟨601826, by rfl⟩ : syracuseStep 802435 = 1203653) B1203653
theorem B802451 : Blo 802343 802451 := bstep (se 1 (by rfl) ⟨601838, by rfl⟩ : syracuseStep 802451 = 1203677) B1203677
theorem B802467 : Blo 802343 802467 := bstep (se 1 (by rfl) ⟨601850, by rfl⟩ : syracuseStep 802467 = 1203701) B1203701
theorem B802483 : Blo 802343 802483 := bstep (se 1 (by rfl) ⟨601862, by rfl⟩ : syracuseStep 802483 = 1203725) B1203725
theorem B802499 : Blo 802343 802499 := bstep (se 1 (by rfl) ⟨601874, by rfl⟩ : syracuseStep 802499 = 1203749) B1203749
theorem B802515 : Blo 802343 802515 := bstep (se 1 (by rfl) ⟨601886, by rfl⟩ : syracuseStep 802515 = 1203773) B1203773
theorem B1359571 : Blo 802343 1359571 := bstep (se 1 (by rfl) ⟨1019678, by rfl⟩ : syracuseStep 1359571 = 2039357) B2039357
theorem B802531 : Blo 802343 802531 := bstep (se 1 (by rfl) ⟨601898, by rfl⟩ : syracuseStep 802531 = 1203797) B1203797
theorem B2572003 : Blo 802343 2572003 := bstep (se 1 (by rfl) ⟨1929002, by rfl⟩ : syracuseStep 2572003 = 3858005) B3858005
theorem B802547 : Blo 802343 802547 := bstep (se 1 (by rfl) ⟨601910, by rfl⟩ : syracuseStep 802547 = 1203821) B1203821
theorem B802563 : Blo 802343 802563 := bstep (se 1 (by rfl) ⟨601922, by rfl⟩ : syracuseStep 802563 = 1203845) B1203845
theorem B802579 : Blo 802343 802579 := bstep (se 1 (by rfl) ⟨601934, by rfl⟩ : syracuseStep 802579 = 1203869) B1203869
theorem B802595 : Blo 802343 802595 := bstep (se 1 (by rfl) ⟨601946, by rfl⟩ : syracuseStep 802595 = 1203893) B1203893
theorem B2572067 : Blo 802343 2572067 := bstep (se 1 (by rfl) ⟨1929050, by rfl⟩ : syracuseStep 2572067 = 3858101) B3858101
theorem B802611 : Blo 802343 802611 := bstep (se 1 (by rfl) ⟨601958, by rfl⟩ : syracuseStep 802611 = 1203917) B1203917
theorem B802627 : Blo 802343 802627 := bstep (se 1 (by rfl) ⟨601970, by rfl⟩ : syracuseStep 802627 = 1203941) B1203941
theorem B802643 : Blo 802343 802643 := bstep (se 1 (by rfl) ⟨601982, by rfl⟩ : syracuseStep 802643 = 1203965) B1203965
theorem B1359713 : Blo 802343 1359713 := bstep (se 2 (by rfl) ⟨509892, by rfl⟩ : syracuseStep 1359713 = 1019785) B1019785
theorem B802659 : Blo 802343 802659 := bstep (se 1 (by rfl) ⟨601994, by rfl⟩ : syracuseStep 802659 = 1203989) B1203989
theorem B2572145 : Blo 802343 2572145 := bstep (se 2 (by rfl) ⟨964554, by rfl⟩ : syracuseStep 2572145 = 1929109) B1929109
theorem B802675 : Blo 802343 802675 := bstep (se 1 (by rfl) ⟨602006, by rfl⟩ : syracuseStep 802675 = 1204013) B1204013
theorem B802691 : Blo 802343 802691 := bstep (se 1 (by rfl) ⟨602018, by rfl⟩ : syracuseStep 802691 = 1204037) B1204037
theorem B802707 : Blo 802343 802707 := bstep (se 1 (by rfl) ⟨602030, by rfl⟩ : syracuseStep 802707 = 1204061) B1204061
theorem B802723 : Blo 802343 802723 := bstep (se 1 (by rfl) ⟨602042, by rfl⟩ : syracuseStep 802723 = 1204085) B1204085
theorem B802739 : Blo 802343 802739 := bstep (se 1 (by rfl) ⟨602054, by rfl⟩ : syracuseStep 802739 = 1204109) B1204109
theorem B802755 : Blo 802343 802755 := bstep (se 1 (by rfl) ⟨602066, by rfl⟩ : syracuseStep 802755 = 1204133) B1204133
theorem B1720273 : Blo 802343 1720273 := bstep (se 2 (by rfl) ⟨645102, by rfl⟩ : syracuseStep 1720273 = 1290205) B1290205
theorem B802771 : Blo 802343 802771 := bstep (se 1 (by rfl) ⟨602078, by rfl⟩ : syracuseStep 802771 = 1204157) B1204157
theorem B1359841 : Blo 802343 1359841 := bstep (se 2 (by rfl) ⟨509940, by rfl⟩ : syracuseStep 1359841 = 1019881) B1019881
theorem B802787 : Blo 802343 802787 := bstep (se 1 (by rfl) ⟨602090, by rfl⟩ : syracuseStep 802787 = 1204181) B1204181
theorem B802803 : Blo 802343 802803 := bstep (se 1 (by rfl) ⟨602102, by rfl⟩ : syracuseStep 802803 = 1204205) B1204205
theorem B802819 : Blo 802343 802819 := bstep (se 1 (by rfl) ⟨602114, by rfl⟩ : syracuseStep 802819 = 1204229) B1204229
theorem B1359875 : Blo 802343 1359875 := bstep (se 1 (by rfl) ⟨1019906, by rfl⟩ : syracuseStep 1359875 = 2039813) B2039813
theorem B802835 : Blo 802343 802835 := bstep (se 1 (by rfl) ⟨602126, by rfl⟩ : syracuseStep 802835 = 1204253) B1204253
theorem B1523747 : Blo 802343 1523747 := bstep (se 1 (by rfl) ⟨1142810, by rfl⟩ : syracuseStep 1523747 = 2285621) B2285621
theorem B802851 : Blo 802343 802851 := bstep (se 1 (by rfl) ⟨602138, by rfl⟩ : syracuseStep 802851 = 1204277) B1204277
theorem B966691 : Blo 802343 966691 := bstep (se 1 (by rfl) ⟨725018, by rfl⟩ : syracuseStep 966691 = 1450037) B1450037
theorem B802867 : Blo 802343 802867 := bstep (se 1 (by rfl) ⟨602150, by rfl⟩ : syracuseStep 802867 = 1204301) B1204301
theorem B802883 : Blo 802343 802883 := bstep (se 1 (by rfl) ⟨602162, by rfl⟩ : syracuseStep 802883 = 1204325) B1204325
theorem B802899 : Blo 802343 802899 := bstep (se 1 (by rfl) ⟨602174, by rfl⟩ : syracuseStep 802899 = 1204349) B1204349
theorem B802915 : Blo 802343 802915 := bstep (se 1 (by rfl) ⟨602186, by rfl⟩ : syracuseStep 802915 = 1204373) B1204373
theorem B966755 : Blo 802343 966755 := bstep (se 1 (by rfl) ⟨725066, by rfl⟩ : syracuseStep 966755 = 1450133) B1450133
theorem B42942577 : Blo 802343 42942577 := bstep (se 2 (by rfl) ⟨16103466, by rfl⟩ : syracuseStep 42942577 = 32206933) B32206933
theorem B802931 : Blo 802343 802931 := bstep (se 1 (by rfl) ⟨602198, by rfl⟩ : syracuseStep 802931 = 1204397) B1204397
theorem B802947 : Blo 802343 802947 := bstep (se 1 (by rfl) ⟨602210, by rfl⟩ : syracuseStep 802947 = 1204421) B1204421
theorem B1360003 : Blo 802343 1360003 := bstep (se 1 (by rfl) ⟨1020002, by rfl⟩ : syracuseStep 1360003 = 2040005) B2040005
theorem B802963 : Blo 802343 802963 := bstep (se 1 (by rfl) ⟨602222, by rfl⟩ : syracuseStep 802963 = 1204445) B1204445
theorem B802979 : Blo 802343 802979 := bstep (se 1 (by rfl) ⟨602234, by rfl⟩ : syracuseStep 802979 = 1204469) B1204469
theorem B802995 : Blo 802343 802995 := bstep (se 1 (by rfl) ⟨602246, by rfl⟩ : syracuseStep 802995 = 1204493) B1204493
theorem B1392833 : Blo 802343 1392833 := bstep (se 2 (by rfl) ⟨522312, by rfl⟩ : syracuseStep 1392833 = 1044625) B1044625
theorem B803011 : Blo 802343 803011 := bstep (se 1 (by rfl) ⟨602258, by rfl⟩ : syracuseStep 803011 = 1204517) B1204517
theorem B803027 : Blo 802343 803027 := bstep (se 1 (by rfl) ⟨602270, by rfl⟩ : syracuseStep 803027 = 1204541) B1204541
theorem B803043 : Blo 802343 803043 := bstep (se 1 (by rfl) ⟨602282, by rfl⟩ : syracuseStep 803043 = 1204565) B1204565
theorem B2900195 : Blo 802343 2900195 := bstep (se 1 (by rfl) ⟨2175146, by rfl⟩ : syracuseStep 2900195 = 4350293) B4350293
theorem B803059 : Blo 802343 803059 := bstep (se 1 (by rfl) ⟨602294, by rfl⟩ : syracuseStep 803059 = 1204589) B1204589
theorem B803075 : Blo 802343 803075 := bstep (se 1 (by rfl) ⟨602306, by rfl⟩ : syracuseStep 803075 = 1204613) B1204613
theorem B5161229 : Blo 802343 5161229 := bstep (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) B1935461
theorem B1360145 : Blo 802343 1360145 := bstep (se 2 (by rfl) ⟨510054, by rfl⟩ : syracuseStep 1360145 = 1020109) B1020109
theorem B803091 : Blo 802343 803091 := bstep (se 1 (by rfl) ⟨602318, by rfl⟩ : syracuseStep 803091 = 1204637) B1204637
theorem B803107 : Blo 802343 803107 := bstep (se 1 (by rfl) ⟨602330, by rfl⟩ : syracuseStep 803107 = 1204661) B1204661
theorem B803123 : Blo 802343 803123 := bstep (se 1 (by rfl) ⟨602342, by rfl⟩ : syracuseStep 803123 = 1204685) B1204685
theorem B1524035 : Blo 802343 1524035 := bstep (se 1 (by rfl) ⟨1143026, by rfl⟩ : syracuseStep 1524035 = 2286053) B2286053
theorem B803139 : Blo 802343 803139 := bstep (se 1 (by rfl) ⟨602354, by rfl⟩ : syracuseStep 803139 = 1204709) B1204709
theorem B803155 : Blo 802343 803155 := bstep (se 1 (by rfl) ⟨602366, by rfl⟩ : syracuseStep 803155 = 1204733) B1204733
theorem B803171 : Blo 802343 803171 := bstep (se 1 (by rfl) ⟨602378, by rfl⟩ : syracuseStep 803171 = 1204757) B1204757
theorem B16695665 : Blo 802343 16695665 := bstep (se 2 (by rfl) ⟨6260874, by rfl⟩ : syracuseStep 16695665 = 12521749) B12521749
theorem B803187 : Blo 802343 803187 := bstep (se 1 (by rfl) ⟨602390, by rfl⟩ : syracuseStep 803187 = 1204781) B1204781
theorem B803203 : Blo 802343 803203 := bstep (se 1 (by rfl) ⟨602402, by rfl⟩ : syracuseStep 803203 = 1204805) B1204805
theorem B1360273 : Blo 802343 1360273 := bstep (se 2 (by rfl) ⟨510102, by rfl⟩ : syracuseStep 1360273 = 1020205) B1020205
theorem B803219 : Blo 802343 803219 := bstep (se 1 (by rfl) ⟨602414, by rfl⟩ : syracuseStep 803219 = 1204829) B1204829
theorem B803235 : Blo 802343 803235 := bstep (se 1 (by rfl) ⟨602426, by rfl⟩ : syracuseStep 803235 = 1204853) B1204853
theorem B803251 : Blo 802343 803251 := bstep (se 1 (by rfl) ⟨602438, by rfl⟩ : syracuseStep 803251 = 1204877) B1204877
theorem B1360307 : Blo 802343 1360307 := bstep (se 1 (by rfl) ⟨1020230, by rfl⟩ : syracuseStep 1360307 = 2040461) B2040461
theorem B803267 : Blo 802343 803267 := bstep (se 1 (by rfl) ⟨602450, by rfl⟩ : syracuseStep 803267 = 1204901) B1204901
theorem B803283 : Blo 802343 803283 := bstep (se 1 (by rfl) ⟨602462, by rfl⟩ : syracuseStep 803283 = 1204925) B1204925
theorem B803299 : Blo 802343 803299 := bstep (se 1 (by rfl) ⟨602474, by rfl⟩ : syracuseStep 803299 = 1204949) B1204949
theorem B5161457 : Blo 802343 5161457 := bstep (se 2 (by rfl) ⟨1935546, by rfl⟩ : syracuseStep 5161457 = 3871093) B3871093
theorem B803315 : Blo 802343 803315 := bstep (se 1 (by rfl) ⟨602486, by rfl⟩ : syracuseStep 803315 = 1204973) B1204973
theorem B803331 : Blo 802343 803331 := bstep (se 1 (by rfl) ⟨602498, by rfl⟩ : syracuseStep 803331 = 1204997) B1204997
theorem B803347 : Blo 802343 803347 := bstep (se 1 (by rfl) ⟨602510, by rfl⟩ : syracuseStep 803347 = 1205021) B1205021
theorem B803363 : Blo 802343 803363 := bstep (se 1 (by rfl) ⟨602522, by rfl⟩ : syracuseStep 803363 = 1205045) B1205045
theorem B803379 : Blo 802343 803379 := bstep (se 1 (by rfl) ⟨602534, by rfl⟩ : syracuseStep 803379 = 1205069) B1205069
theorem B1360435 : Blo 802343 1360435 := bstep (se 1 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 1360435 = 2040653) B2040653
theorem B803395 : Blo 802343 803395 := bstep (se 1 (by rfl) ⟨602546, by rfl⟩ : syracuseStep 803395 = 1205093) B1205093
theorem B967235 : Blo 802343 967235 := bstep (se 1 (by rfl) ⟨725426, by rfl⟩ : syracuseStep 967235 = 1450853) B1450853
theorem B803411 : Blo 802343 803411 := bstep (se 1 (by rfl) ⟨602558, by rfl⟩ : syracuseStep 803411 = 1205117) B1205117
theorem B803427 : Blo 802343 803427 := bstep (se 1 (by rfl) ⟨602570, by rfl⟩ : syracuseStep 803427 = 1205141) B1205141
theorem B803443 : Blo 802343 803443 := bstep (se 1 (by rfl) ⟨602582, by rfl⟩ : syracuseStep 803443 = 1205165) B1205165
theorem B803459 : Blo 802343 803459 := bstep (se 1 (by rfl) ⟨602594, by rfl⟩ : syracuseStep 803459 = 1205189) B1205189
theorem B803475 : Blo 802343 803475 := bstep (se 1 (by rfl) ⟨602606, by rfl⟩ : syracuseStep 803475 = 1205213) B1205213
theorem B803491 : Blo 802343 803491 := bstep (se 1 (by rfl) ⟨602618, by rfl⟩ : syracuseStep 803491 = 1205237) B1205237
theorem B803507 : Blo 802343 803507 := bstep (se 1 (by rfl) ⟨602630, by rfl⟩ : syracuseStep 803507 = 1205261) B1205261
theorem B1360577 : Blo 802343 1360577 := bstep (se 2 (by rfl) ⟨510216, by rfl⟩ : syracuseStep 1360577 = 1020433) B1020433
theorem B803523 : Blo 802343 803523 := bstep (se 1 (by rfl) ⟨602642, by rfl⟩ : syracuseStep 803523 = 1205285) B1205285
theorem B803539 : Blo 802343 803539 := bstep (se 1 (by rfl) ⟨602654, by rfl⟩ : syracuseStep 803539 = 1205309) B1205309
theorem B803555 : Blo 802343 803555 := bstep (se 1 (by rfl) ⟨602666, by rfl⟩ : syracuseStep 803555 = 1205333) B1205333
theorem B803571 : Blo 802343 803571 := bstep (se 1 (by rfl) ⟨602678, by rfl⟩ : syracuseStep 803571 = 1205357) B1205357
theorem B803587 : Blo 802343 803587 := bstep (se 1 (by rfl) ⟨602690, by rfl⟩ : syracuseStep 803587 = 1205381) B1205381
theorem B8798989 : Blo 802343 8798989 := bstep (se 3 (by rfl) ⟨1649810, by rfl⟩ : syracuseStep 8798989 = 3299621) B3299621
theorem B803603 : Blo 802343 803603 := bstep (se 1 (by rfl) ⟨602702, by rfl⟩ : syracuseStep 803603 = 1205405) B1205405
theorem B803619 : Blo 802343 803619 := bstep (se 1 (by rfl) ⟨602714, by rfl⟩ : syracuseStep 803619 = 1205429) B1205429
theorem B803635 : Blo 802343 803635 := bstep (se 1 (by rfl) ⟨602726, by rfl⟩ : syracuseStep 803635 = 1205453) B1205453
theorem B1360705 : Blo 802343 1360705 := bstep (se 2 (by rfl) ⟨510264, by rfl⟩ : syracuseStep 1360705 = 1020529) B1020529
theorem B803651 : Blo 802343 803651 := bstep (se 1 (by rfl) ⟨602738, by rfl⟩ : syracuseStep 803651 = 1205477) B1205477
theorem B803667 : Blo 802343 803667 := bstep (se 1 (by rfl) ⟨602750, by rfl⟩ : syracuseStep 803667 = 1205501) B1205501
theorem B803683 : Blo 802343 803683 := bstep (se 1 (by rfl) ⟨602762, by rfl⟩ : syracuseStep 803683 = 1205525) B1205525
theorem B803699 : Blo 802343 803699 := bstep (se 1 (by rfl) ⟨602774, by rfl⟩ : syracuseStep 803699 = 1205549) B1205549
theorem B803715 : Blo 802343 803715 := bstep (se 1 (by rfl) ⟨602786, by rfl⟩ : syracuseStep 803715 = 1205573) B1205573
theorem B803731 : Blo 802343 803731 := bstep (se 1 (by rfl) ⟨602798, by rfl⟩ : syracuseStep 803731 = 1205597) B1205597
theorem B803747 : Blo 802343 803747 := bstep (se 1 (by rfl) ⟨602810, by rfl⟩ : syracuseStep 803747 = 1205621) B1205621
theorem B803763 : Blo 802343 803763 := bstep (se 1 (by rfl) ⟨602822, by rfl⟩ : syracuseStep 803763 = 1205645) B1205645
theorem B803779 : Blo 802343 803779 := bstep (se 1 (by rfl) ⟨602834, by rfl⟩ : syracuseStep 803779 = 1205669) B1205669
theorem B803795 : Blo 802343 803795 := bstep (se 1 (by rfl) ⟨602846, by rfl⟩ : syracuseStep 803795 = 1205693) B1205693
theorem B803811 : Blo 802343 803811 := bstep (se 1 (by rfl) ⟨602858, by rfl⟩ : syracuseStep 803811 = 1205717) B1205717
theorem B803827 : Blo 802343 803827 := bstep (se 1 (by rfl) ⟨602870, by rfl⟩ : syracuseStep 803827 = 1205741) B1205741
theorem B803843 : Blo 802343 803843 := bstep (se 1 (by rfl) ⟨602882, by rfl⟩ : syracuseStep 803843 = 1205765) B1205765
theorem B803859 : Blo 802343 803859 := bstep (se 1 (by rfl) ⟨602894, by rfl⟩ : syracuseStep 803859 = 1205789) B1205789
theorem B803875 : Blo 802343 803875 := bstep (se 1 (by rfl) ⟨602906, by rfl⟩ : syracuseStep 803875 = 1205813) B1205813
theorem B803891 : Blo 802343 803891 := bstep (se 1 (by rfl) ⟨602918, by rfl⟩ : syracuseStep 803891 = 1205837) B1205837
theorem B2442307 : Blo 802343 2442307 := bstep (se 1 (by rfl) ⟨1831730, by rfl⟩ : syracuseStep 2442307 = 3663461) B3663461
theorem B803907 : Blo 802343 803907 := bstep (se 1 (by rfl) ⟨602930, by rfl⟩ : syracuseStep 803907 = 1205861) B1205861
theorem B803923 : Blo 802343 803923 := bstep (se 1 (by rfl) ⟨602942, by rfl⟩ : syracuseStep 803923 = 1205885) B1205885
theorem B803939 : Blo 802343 803939 := bstep (se 1 (by rfl) ⟨602954, by rfl⟩ : syracuseStep 803939 = 1205909) B1205909
theorem B803955 : Blo 802343 803955 := bstep (se 1 (by rfl) ⟨602966, by rfl⟩ : syracuseStep 803955 = 1205933) B1205933
theorem B803971 : Blo 802343 803971 := bstep (se 1 (by rfl) ⟨602978, by rfl⟩ : syracuseStep 803971 = 1205957) B1205957
theorem B803987 : Blo 802343 803987 := bstep (se 1 (by rfl) ⟨602990, by rfl⟩ : syracuseStep 803987 = 1205981) B1205981
theorem B804003 : Blo 802343 804003 := bstep (se 1 (by rfl) ⟨603002, by rfl⟩ : syracuseStep 804003 = 1206005) B1206005
theorem B804019 : Blo 802343 804019 := bstep (se 1 (by rfl) ⟨603014, by rfl⟩ : syracuseStep 804019 = 1206029) B1206029
theorem B804035 : Blo 802343 804035 := bstep (se 1 (by rfl) ⟨603026, by rfl⟩ : syracuseStep 804035 = 1206053) B1206053
theorem B804051 : Blo 802343 804051 := bstep (se 1 (by rfl) ⟨603038, by rfl⟩ : syracuseStep 804051 = 1206077) B1206077
theorem B804067 : Blo 802343 804067 := bstep (se 1 (by rfl) ⟨603050, by rfl⟩ : syracuseStep 804067 = 1206101) B1206101
theorem B1524977 : Blo 802343 1524977 := bstep (se 2 (by rfl) ⟨571866, by rfl⟩ : syracuseStep 1524977 = 1143733) B1143733
theorem B804083 : Blo 802343 804083 := bstep (se 1 (by rfl) ⟨603062, by rfl⟩ : syracuseStep 804083 = 1206125) B1206125
theorem B804099 : Blo 802343 804099 := bstep (se 1 (by rfl) ⟨603074, by rfl⟩ : syracuseStep 804099 = 1206149) B1206149
theorem B804115 : Blo 802343 804115 := bstep (se 1 (by rfl) ⟨603086, by rfl⟩ : syracuseStep 804115 = 1206173) B1206173
theorem B804131 : Blo 802343 804131 := bstep (se 1 (by rfl) ⟨603098, by rfl⟩ : syracuseStep 804131 = 1206197) B1206197
theorem B804147 : Blo 802343 804147 := bstep (se 1 (by rfl) ⟨603110, by rfl⟩ : syracuseStep 804147 = 1206221) B1206221
theorem B804163 : Blo 802343 804163 := bstep (se 1 (by rfl) ⟨603122, by rfl⟩ : syracuseStep 804163 = 1206245) B1206245
theorem B804179 : Blo 802343 804179 := bstep (se 1 (by rfl) ⟨603134, by rfl⟩ : syracuseStep 804179 = 1206269) B1206269
theorem B804195 : Blo 802343 804195 := bstep (se 1 (by rfl) ⟨603146, by rfl⟩ : syracuseStep 804195 = 1206293) B1206293
theorem B804211 : Blo 802343 804211 := bstep (se 1 (by rfl) ⟨603158, by rfl⟩ : syracuseStep 804211 = 1206317) B1206317
theorem B804227 : Blo 802343 804227 := bstep (se 1 (by rfl) ⟨603170, by rfl⟩ : syracuseStep 804227 = 1206341) B1206341
theorem B804243 : Blo 802343 804243 := bstep (se 1 (by rfl) ⟨603182, by rfl⟩ : syracuseStep 804243 = 1206365) B1206365
theorem B804259 : Blo 802343 804259 := bstep (se 1 (by rfl) ⟨603194, by rfl⟩ : syracuseStep 804259 = 1206389) B1206389
theorem B804275 : Blo 802343 804275 := bstep (se 1 (by rfl) ⟨603206, by rfl⟩ : syracuseStep 804275 = 1206413) B1206413
theorem B804291 : Blo 802343 804291 := bstep (se 1 (by rfl) ⟨603218, by rfl⟩ : syracuseStep 804291 = 1206437) B1206437
theorem B804307 : Blo 802343 804307 := bstep (se 1 (by rfl) ⟨603230, by rfl⟩ : syracuseStep 804307 = 1206461) B1206461
theorem B804323 : Blo 802343 804323 := bstep (se 1 (by rfl) ⟨603242, by rfl⟩ : syracuseStep 804323 = 1206485) B1206485
theorem B804339 : Blo 802343 804339 := bstep (se 1 (by rfl) ⟨603254, by rfl⟩ : syracuseStep 804339 = 1206509) B1206509
theorem B902659 : Blo 802343 902659 := bstep (se 1 (by rfl) ⟨676994, by rfl⟩ : syracuseStep 902659 = 1353989) B1353989
theorem B804355 : Blo 802343 804355 := bstep (se 1 (by rfl) ⟨603266, by rfl⟩ : syracuseStep 804355 = 1206533) B1206533
theorem B804371 : Blo 802343 804371 := bstep (se 1 (by rfl) ⟨603278, by rfl⟩ : syracuseStep 804371 = 1206557) B1206557
theorem B804387 : Blo 802343 804387 := bstep (se 1 (by rfl) ⟨603290, by rfl⟩ : syracuseStep 804387 = 1206581) B1206581
theorem B804403 : Blo 802343 804403 := bstep (se 1 (by rfl) ⟨603302, by rfl⟩ : syracuseStep 804403 = 1206605) B1206605
theorem B804419 : Blo 802343 804419 := bstep (se 1 (by rfl) ⟨603314, by rfl⟩ : syracuseStep 804419 = 1206629) B1206629
theorem B804435 : Blo 802343 804435 := bstep (se 1 (by rfl) ⟨603326, by rfl⟩ : syracuseStep 804435 = 1206653) B1206653
theorem B804451 : Blo 802343 804451 := bstep (se 1 (by rfl) ⟨603338, by rfl⟩ : syracuseStep 804451 = 1206677) B1206677
theorem B4081265 : Blo 802343 4081265 := bstep (se 2 (by rfl) ⟨1530474, by rfl⟩ : syracuseStep 4081265 = 3060949) B3060949
theorem B804467 : Blo 802343 804467 := bstep (se 1 (by rfl) ⟨603350, by rfl⟩ : syracuseStep 804467 = 1206701) B1206701
theorem B804483 : Blo 802343 804483 := bstep (se 1 (by rfl) ⟨603362, by rfl⟩ : syracuseStep 804483 = 1206725) B1206725
theorem B902803 : Blo 802343 902803 := bstep (se 1 (by rfl) ⟨677102, by rfl⟩ : syracuseStep 902803 = 1354205) B1354205
theorem B804499 : Blo 802343 804499 := bstep (se 1 (by rfl) ⟨603374, by rfl⟩ : syracuseStep 804499 = 1206749) B1206749
theorem B804515 : Blo 802343 804515 := bstep (se 1 (by rfl) ⟨603386, by rfl⟩ : syracuseStep 804515 = 1206773) B1206773
theorem B804531 : Blo 802343 804531 := bstep (se 1 (by rfl) ⟨603398, by rfl⟩ : syracuseStep 804531 = 1206797) B1206797
theorem B804547 : Blo 802343 804547 := bstep (se 1 (by rfl) ⟨603410, by rfl⟩ : syracuseStep 804547 = 1206821) B1206821
theorem B804563 : Blo 802343 804563 := bstep (se 1 (by rfl) ⟨603422, by rfl⟩ : syracuseStep 804563 = 1206845) B1206845
theorem B804579 : Blo 802343 804579 := bstep (se 1 (by rfl) ⟨603434, by rfl⟩ : syracuseStep 804579 = 1206869) B1206869
theorem B2574065 : Blo 802343 2574065 := bstep (se 2 (by rfl) ⟨965274, by rfl⟩ : syracuseStep 2574065 = 1930549) B1930549
theorem B804595 : Blo 802343 804595 := bstep (se 1 (by rfl) ⟨603446, by rfl⟩ : syracuseStep 804595 = 1206893) B1206893
theorem B804611 : Blo 802343 804611 := bstep (se 1 (by rfl) ⟨603458, by rfl⟩ : syracuseStep 804611 = 1206917) B1206917
theorem B804627 : Blo 802343 804627 := bstep (se 1 (by rfl) ⟨603470, by rfl⟩ : syracuseStep 804627 = 1206941) B1206941
theorem B902947 : Blo 802343 902947 := bstep (se 1 (by rfl) ⟨677210, by rfl⟩ : syracuseStep 902947 = 1354421) B1354421
theorem B804643 : Blo 802343 804643 := bstep (se 1 (by rfl) ⟨603482, by rfl⟩ : syracuseStep 804643 = 1206965) B1206965
theorem B804659 : Blo 802343 804659 := bstep (se 1 (by rfl) ⟨603494, by rfl⟩ : syracuseStep 804659 = 1206989) B1206989
theorem B870211 : Blo 802343 870211 := bstep (se 1 (by rfl) ⟨652658, by rfl⟩ : syracuseStep 870211 = 1305317) B1305317
theorem B804675 : Blo 802343 804675 := bstep (se 1 (by rfl) ⟨603506, by rfl⟩ : syracuseStep 804675 = 1207013) B1207013
theorem B804691 : Blo 802343 804691 := bstep (se 1 (by rfl) ⟨603518, by rfl⟩ : syracuseStep 804691 = 1207037) B1207037
theorem B804707 : Blo 802343 804707 := bstep (se 1 (by rfl) ⟨603530, by rfl⟩ : syracuseStep 804707 = 1207061) B1207061
theorem B804723 : Blo 802343 804723 := bstep (se 1 (by rfl) ⟨603542, by rfl⟩ : syracuseStep 804723 = 1207085) B1207085
theorem B804739 : Blo 802343 804739 := bstep (se 1 (by rfl) ⟨603554, by rfl⟩ : syracuseStep 804739 = 1207109) B1207109
theorem B804755 : Blo 802343 804755 := bstep (se 1 (by rfl) ⟨603566, by rfl⟩ : syracuseStep 804755 = 1207133) B1207133
theorem B804771 : Blo 802343 804771 := bstep (se 1 (by rfl) ⟨603578, by rfl⟩ : syracuseStep 804771 = 1207157) B1207157
theorem B903091 : Blo 802343 903091 := bstep (se 1 (by rfl) ⟨677318, by rfl⟩ : syracuseStep 903091 = 1354637) B1354637
theorem B804787 : Blo 802343 804787 := bstep (se 1 (by rfl) ⟨603590, by rfl⟩ : syracuseStep 804787 = 1207181) B1207181
theorem B804803 : Blo 802343 804803 := bstep (se 1 (by rfl) ⟨603602, by rfl⟩ : syracuseStep 804803 = 1207205) B1207205
theorem B804819 : Blo 802343 804819 := bstep (se 1 (by rfl) ⟨603614, by rfl⟩ : syracuseStep 804819 = 1207229) B1207229
theorem B804835 : Blo 802343 804835 := bstep (se 1 (by rfl) ⟨603626, by rfl⟩ : syracuseStep 804835 = 1207253) B1207253
theorem B804851 : Blo 802343 804851 := bstep (se 1 (by rfl) ⟨603638, by rfl⟩ : syracuseStep 804851 = 1207277) B1207277
theorem B804867 : Blo 802343 804867 := bstep (se 1 (by rfl) ⟨603650, by rfl⟩ : syracuseStep 804867 = 1207301) B1207301
theorem B804883 : Blo 802343 804883 := bstep (se 1 (by rfl) ⟨603662, by rfl⟩ : syracuseStep 804883 = 1207325) B1207325
theorem B804899 : Blo 802343 804899 := bstep (se 1 (by rfl) ⟨603674, by rfl⟩ : syracuseStep 804899 = 1207349) B1207349
theorem B804915 : Blo 802343 804915 := bstep (se 1 (by rfl) ⟨603686, by rfl⟩ : syracuseStep 804915 = 1207373) B1207373
theorem B903235 : Blo 802343 903235 := bstep (se 1 (by rfl) ⟨677426, by rfl⟩ : syracuseStep 903235 = 1354853) B1354853
theorem B804931 : Blo 802343 804931 := bstep (se 1 (by rfl) ⟨603698, by rfl⟩ : syracuseStep 804931 = 1207397) B1207397
theorem B804947 : Blo 802343 804947 := bstep (se 1 (by rfl) ⟨603710, by rfl⟩ : syracuseStep 804947 = 1207421) B1207421
theorem B804963 : Blo 802343 804963 := bstep (se 1 (by rfl) ⟨603722, by rfl⟩ : syracuseStep 804963 = 1207445) B1207445
theorem B1525873 : Blo 802343 1525873 := bstep (se 2 (by rfl) ⟨572202, by rfl⟩ : syracuseStep 1525873 = 1144405) B1144405
theorem B6113393 : Blo 802343 6113393 := bstep (se 2 (by rfl) ⟨2292522, by rfl⟩ : syracuseStep 6113393 = 4585045) B4585045
theorem B804979 : Blo 802343 804979 := bstep (se 1 (by rfl) ⟨603734, by rfl⟩ : syracuseStep 804979 = 1207469) B1207469
theorem B804995 : Blo 802343 804995 := bstep (se 1 (by rfl) ⟨603746, by rfl⟩ : syracuseStep 804995 = 1207493) B1207493
theorem B805011 : Blo 802343 805011 := bstep (se 1 (by rfl) ⟨603758, by rfl⟩ : syracuseStep 805011 = 1207517) B1207517
theorem B805027 : Blo 802343 805027 := bstep (se 1 (by rfl) ⟨603770, by rfl⟩ : syracuseStep 805027 = 1207541) B1207541
theorem B805043 : Blo 802343 805043 := bstep (se 1 (by rfl) ⟨603782, by rfl⟩ : syracuseStep 805043 = 1207565) B1207565
theorem B805059 : Blo 802343 805059 := bstep (se 1 (by rfl) ⟨603794, by rfl⟩ : syracuseStep 805059 = 1207589) B1207589
theorem B4573381 : Blo 802343 4573381 := bstep (se 4 (by rfl) ⟨428754, by rfl⟩ : syracuseStep 4573381 = 857509) B857509
theorem B903379 : Blo 802343 903379 := bstep (se 1 (by rfl) ⟨677534, by rfl⟩ : syracuseStep 903379 = 1355069) B1355069
theorem B805075 : Blo 802343 805075 := bstep (se 1 (by rfl) ⟨603806, by rfl⟩ : syracuseStep 805075 = 1207613) B1207613
theorem B805091 : Blo 802343 805091 := bstep (se 1 (by rfl) ⟨603818, by rfl⟩ : syracuseStep 805091 = 1207637) B1207637
theorem B805107 : Blo 802343 805107 := bstep (se 1 (by rfl) ⟨603830, by rfl⟩ : syracuseStep 805107 = 1207661) B1207661
theorem B805123 : Blo 802343 805123 := bstep (se 1 (by rfl) ⟨603842, by rfl⟩ : syracuseStep 805123 = 1207685) B1207685
theorem B2574605 : Blo 802343 2574605 := bstep (se 3 (by rfl) ⟨482738, by rfl⟩ : syracuseStep 2574605 = 965477) B965477
theorem B1526033 : Blo 802343 1526033 := bstep (se 2 (by rfl) ⟨572262, by rfl⟩ : syracuseStep 1526033 = 1144525) B1144525
theorem B805139 : Blo 802343 805139 := bstep (se 1 (by rfl) ⟨603854, by rfl⟩ : syracuseStep 805139 = 1207709) B1207709
theorem B805155 : Blo 802343 805155 := bstep (se 1 (by rfl) ⟨603866, by rfl⟩ : syracuseStep 805155 = 1207733) B1207733
theorem B805171 : Blo 802343 805171 := bstep (se 1 (by rfl) ⟨603878, by rfl⟩ : syracuseStep 805171 = 1207757) B1207757
theorem B805187 : Blo 802343 805187 := bstep (se 1 (by rfl) ⟨603890, by rfl⟩ : syracuseStep 805187 = 1207781) B1207781
theorem B805203 : Blo 802343 805203 := bstep (se 1 (by rfl) ⟨603902, by rfl⟩ : syracuseStep 805203 = 1207805) B1207805
theorem B903523 : Blo 802343 903523 := bstep (se 1 (by rfl) ⟨677642, by rfl⟩ : syracuseStep 903523 = 1355285) B1355285
theorem B805219 : Blo 802343 805219 := bstep (se 1 (by rfl) ⟨603914, by rfl⟩ : syracuseStep 805219 = 1207829) B1207829
theorem B805235 : Blo 802343 805235 := bstep (se 1 (by rfl) ⟨603926, by rfl⟩ : syracuseStep 805235 = 1207853) B1207853
theorem B805251 : Blo 802343 805251 := bstep (se 1 (by rfl) ⟨603938, by rfl⟩ : syracuseStep 805251 = 1207877) B1207877
theorem B805267 : Blo 802343 805267 := bstep (se 1 (by rfl) ⟨603950, by rfl⟩ : syracuseStep 805267 = 1207901) B1207901
theorem B805283 : Blo 802343 805283 := bstep (se 1 (by rfl) ⟨603962, by rfl⟩ : syracuseStep 805283 = 1207925) B1207925
theorem B2935217 : Blo 802343 2935217 := bstep (se 2 (by rfl) ⟨1100706, by rfl⟩ : syracuseStep 2935217 = 2201413) B2201413
theorem B805299 : Blo 802343 805299 := bstep (se 1 (by rfl) ⟨603974, by rfl⟩ : syracuseStep 805299 = 1207949) B1207949
theorem B805315 : Blo 802343 805315 := bstep (se 1 (by rfl) ⟨603986, by rfl⟩ : syracuseStep 805315 = 1207973) B1207973
theorem B805331 : Blo 802343 805331 := bstep (se 1 (by rfl) ⟨603998, by rfl⟩ : syracuseStep 805331 = 1207997) B1207997
theorem B805347 : Blo 802343 805347 := bstep (se 1 (by rfl) ⟨604010, by rfl⟩ : syracuseStep 805347 = 1208021) B1208021
theorem B903667 : Blo 802343 903667 := bstep (se 1 (by rfl) ⟨677750, by rfl⟩ : syracuseStep 903667 = 1355501) B1355501
theorem B805363 : Blo 802343 805363 := bstep (se 1 (by rfl) ⟨604022, by rfl⟩ : syracuseStep 805363 = 1208045) B1208045
theorem B805379 : Blo 802343 805379 := bstep (se 1 (by rfl) ⟨604034, by rfl⟩ : syracuseStep 805379 = 1208069) B1208069
theorem B805395 : Blo 802343 805395 := bstep (se 1 (by rfl) ⟨604046, by rfl⟩ : syracuseStep 805395 = 1208093) B1208093
theorem B805411 : Blo 802343 805411 := bstep (se 1 (by rfl) ⟨604058, by rfl⟩ : syracuseStep 805411 = 1208117) B1208117
theorem B805427 : Blo 802343 805427 := bstep (se 1 (by rfl) ⟨604070, by rfl⟩ : syracuseStep 805427 = 1208141) B1208141
theorem B805443 : Blo 802343 805443 := bstep (se 1 (by rfl) ⟨604082, by rfl⟩ : syracuseStep 805443 = 1208165) B1208165
theorem B805459 : Blo 802343 805459 := bstep (se 1 (by rfl) ⟨604094, by rfl⟩ : syracuseStep 805459 = 1208189) B1208189
theorem B805475 : Blo 802343 805475 := bstep (se 1 (by rfl) ⟨604106, by rfl⟩ : syracuseStep 805475 = 1208213) B1208213
theorem B805491 : Blo 802343 805491 := bstep (se 1 (by rfl) ⟨604118, by rfl⟩ : syracuseStep 805491 = 1208237) B1208237
theorem B903811 : Blo 802343 903811 := bstep (se 1 (by rfl) ⟨677858, by rfl⟩ : syracuseStep 903811 = 1355717) B1355717
theorem B805507 : Blo 802343 805507 := bstep (se 1 (by rfl) ⟨604130, by rfl⟩ : syracuseStep 805507 = 1208261) B1208261
theorem B805523 : Blo 802343 805523 := bstep (se 1 (by rfl) ⟨604142, by rfl⟩ : syracuseStep 805523 = 1208285) B1208285
theorem B1526435 : Blo 802343 1526435 := bstep (se 1 (by rfl) ⟨1144826, by rfl⟩ : syracuseStep 1526435 = 2289653) B2289653
theorem B805539 : Blo 802343 805539 := bstep (se 1 (by rfl) ⟨604154, by rfl⟩ : syracuseStep 805539 = 1208309) B1208309
theorem B805555 : Blo 802343 805555 := bstep (se 1 (by rfl) ⟨604166, by rfl⟩ : syracuseStep 805555 = 1208333) B1208333
theorem B805571 : Blo 802343 805571 := bstep (se 1 (by rfl) ⟨604178, by rfl⟩ : syracuseStep 805571 = 1208357) B1208357
theorem B19876549 : Blo 802343 19876549 := bstep (se 4 (by rfl) ⟨1863426, by rfl⟩ : syracuseStep 19876549 = 3726853) B3726853
theorem B805587 : Blo 802343 805587 := bstep (se 1 (by rfl) ⟨604190, by rfl⟩ : syracuseStep 805587 = 1208381) B1208381
theorem B805603 : Blo 802343 805603 := bstep (se 1 (by rfl) ⟨604202, by rfl⟩ : syracuseStep 805603 = 1208405) B1208405
theorem B1100531 : Blo 802343 1100531 := bstep (se 1 (by rfl) ⟨825398, by rfl⟩ : syracuseStep 1100531 = 1650797) B1650797
theorem B805619 : Blo 802343 805619 := bstep (se 1 (by rfl) ⟨604214, by rfl⟩ : syracuseStep 805619 = 1208429) B1208429
theorem B805635 : Blo 802343 805635 := bstep (se 1 (by rfl) ⟨604226, by rfl⟩ : syracuseStep 805635 = 1208453) B1208453
theorem B903955 : Blo 802343 903955 := bstep (se 1 (by rfl) ⟨677966, by rfl⟩ : syracuseStep 903955 = 1355933) B1355933
theorem B805651 : Blo 802343 805651 := bstep (se 1 (by rfl) ⟨604238, by rfl⟩ : syracuseStep 805651 = 1208477) B1208477
theorem B805667 : Blo 802343 805667 := bstep (se 1 (by rfl) ⟨604250, by rfl⟩ : syracuseStep 805667 = 1208501) B1208501
theorem B805683 : Blo 802343 805683 := bstep (se 1 (by rfl) ⟨604262, by rfl⟩ : syracuseStep 805683 = 1208525) B1208525
theorem B805699 : Blo 802343 805699 := bstep (se 1 (by rfl) ⟨604274, by rfl⟩ : syracuseStep 805699 = 1208549) B1208549
theorem B805715 : Blo 802343 805715 := bstep (se 1 (by rfl) ⟨604286, by rfl⟩ : syracuseStep 805715 = 1208573) B1208573
theorem B805731 : Blo 802343 805731 := bstep (se 1 (by rfl) ⟨604298, by rfl⟩ : syracuseStep 805731 = 1208597) B1208597
theorem B805747 : Blo 802343 805747 := bstep (se 1 (by rfl) ⟨604310, by rfl⟩ : syracuseStep 805747 = 1208621) B1208621
theorem B805763 : Blo 802343 805763 := bstep (se 1 (by rfl) ⟨604322, by rfl⟩ : syracuseStep 805763 = 1208645) B1208645
theorem B805779 : Blo 802343 805779 := bstep (se 1 (by rfl) ⟨604334, by rfl⟩ : syracuseStep 805779 = 1208669) B1208669
theorem B3427235 : Blo 802343 3427235 := bstep (se 1 (by rfl) ⟨2570426, by rfl⟩ : syracuseStep 3427235 = 5140853) B5140853
theorem B904099 : Blo 802343 904099 := bstep (se 1 (by rfl) ⟨678074, by rfl⟩ : syracuseStep 904099 = 1356149) B1356149
theorem B805795 : Blo 802343 805795 := bstep (se 1 (by rfl) ⟨604346, by rfl⟩ : syracuseStep 805795 = 1208693) B1208693
theorem B805811 : Blo 802343 805811 := bstep (se 1 (by rfl) ⟨604358, by rfl⟩ : syracuseStep 805811 = 1208717) B1208717
theorem B805827 : Blo 802343 805827 := bstep (se 1 (by rfl) ⟨604370, by rfl⟩ : syracuseStep 805827 = 1208741) B1208741
theorem B805843 : Blo 802343 805843 := bstep (se 1 (by rfl) ⟨604382, by rfl⟩ : syracuseStep 805843 = 1208765) B1208765
theorem B805859 : Blo 802343 805859 := bstep (se 1 (by rfl) ⟨604394, by rfl⟩ : syracuseStep 805859 = 1208789) B1208789
theorem B805875 : Blo 802343 805875 := bstep (se 1 (by rfl) ⟨604406, by rfl⟩ : syracuseStep 805875 = 1208813) B1208813
theorem B805891 : Blo 802343 805891 := bstep (se 1 (by rfl) ⟨604418, by rfl⟩ : syracuseStep 805891 = 1208837) B1208837
theorem B5655557 : Blo 802343 5655557 := bstep (se 4 (by rfl) ⟨530208, by rfl⟩ : syracuseStep 5655557 = 1060417) B1060417
theorem B805907 : Blo 802343 805907 := bstep (se 1 (by rfl) ⟨604430, by rfl⟩ : syracuseStep 805907 = 1208861) B1208861
theorem B805923 : Blo 802343 805923 := bstep (se 1 (by rfl) ⟨604442, by rfl⟩ : syracuseStep 805923 = 1208885) B1208885
theorem B2903089 : Blo 802343 2903089 := bstep (se 2 (by rfl) ⟨1088658, by rfl⟩ : syracuseStep 2903089 = 2177317) B2177317
theorem B904243 : Blo 802343 904243 := bstep (se 1 (by rfl) ⟨678182, by rfl⟩ : syracuseStep 904243 = 1356365) B1356365
theorem B805939 : Blo 802343 805939 := bstep (se 1 (by rfl) ⟨604454, by rfl⟩ : syracuseStep 805939 = 1208909) B1208909
theorem B805955 : Blo 802343 805955 := bstep (se 1 (by rfl) ⟨604466, by rfl⟩ : syracuseStep 805955 = 1208933) B1208933
theorem B805971 : Blo 802343 805971 := bstep (se 1 (by rfl) ⟨604478, by rfl⟩ : syracuseStep 805971 = 1208957) B1208957
theorem B805987 : Blo 802343 805987 := bstep (se 1 (by rfl) ⟨604490, by rfl⟩ : syracuseStep 805987 = 1208981) B1208981
theorem B806003 : Blo 802343 806003 := bstep (se 1 (by rfl) ⟨604502, by rfl⟩ : syracuseStep 806003 = 1209005) B1209005
theorem B806019 : Blo 802343 806019 := bstep (se 1 (by rfl) ⟨604514, by rfl⟩ : syracuseStep 806019 = 1209029) B1209029
theorem B806035 : Blo 802343 806035 := bstep (se 1 (by rfl) ⟨604526, by rfl⟩ : syracuseStep 806035 = 1209053) B1209053
theorem B806051 : Blo 802343 806051 := bstep (se 1 (by rfl) ⟨604538, by rfl⟩ : syracuseStep 806051 = 1209077) B1209077
theorem B806067 : Blo 802343 806067 := bstep (se 1 (by rfl) ⟨604550, by rfl⟩ : syracuseStep 806067 = 1209101) B1209101
theorem B904387 : Blo 802343 904387 := bstep (se 1 (by rfl) ⟨678290, by rfl⟩ : syracuseStep 904387 = 1356581) B1356581
theorem B806083 : Blo 802343 806083 := bstep (se 1 (by rfl) ⟨604562, by rfl⟩ : syracuseStep 806083 = 1209125) B1209125
theorem B806099 : Blo 802343 806099 := bstep (se 1 (by rfl) ⟨604574, by rfl⟩ : syracuseStep 806099 = 1209149) B1209149
theorem B806115 : Blo 802343 806115 := bstep (se 1 (by rfl) ⟨604586, by rfl⟩ : syracuseStep 806115 = 1209173) B1209173
theorem B806131 : Blo 802343 806131 := bstep (se 1 (by rfl) ⟨604598, by rfl⟩ : syracuseStep 806131 = 1209197) B1209197
theorem B806147 : Blo 802343 806147 := bstep (se 1 (by rfl) ⟨604610, by rfl⟩ : syracuseStep 806147 = 1209221) B1209221
theorem B806163 : Blo 802343 806163 := bstep (se 1 (by rfl) ⟨604622, by rfl⟩ : syracuseStep 806163 = 1209245) B1209245
theorem B806179 : Blo 802343 806179 := bstep (se 1 (by rfl) ⟨604634, by rfl⟩ : syracuseStep 806179 = 1209269) B1209269
theorem B806195 : Blo 802343 806195 := bstep (se 1 (by rfl) ⟨604646, by rfl⟩ : syracuseStep 806195 = 1209293) B1209293
theorem B806211 : Blo 802343 806211 := bstep (se 1 (by rfl) ⟨604658, by rfl⟩ : syracuseStep 806211 = 1209317) B1209317
theorem B904531 : Blo 802343 904531 := bstep (se 1 (by rfl) ⟨678398, by rfl⟩ : syracuseStep 904531 = 1356797) B1356797
theorem B806227 : Blo 802343 806227 := bstep (se 1 (by rfl) ⟨604670, by rfl⟩ : syracuseStep 806227 = 1209341) B1209341
theorem B806243 : Blo 802343 806243 := bstep (se 1 (by rfl) ⟨604682, by rfl⟩ : syracuseStep 806243 = 1209365) B1209365
theorem B3427697 : Blo 802343 3427697 := bstep (se 2 (by rfl) ⟨1285386, by rfl⟩ : syracuseStep 3427697 = 2570773) B2570773
theorem B806259 : Blo 802343 806259 := bstep (se 1 (by rfl) ⟨604694, by rfl⟩ : syracuseStep 806259 = 1209389) B1209389
theorem B806275 : Blo 802343 806275 := bstep (se 1 (by rfl) ⟨604706, by rfl⟩ : syracuseStep 806275 = 1209413) B1209413
theorem B806291 : Blo 802343 806291 := bstep (se 1 (by rfl) ⟨604718, by rfl⟩ : syracuseStep 806291 = 1209437) B1209437
theorem B806307 : Blo 802343 806307 := bstep (se 1 (by rfl) ⟨604730, by rfl⟩ : syracuseStep 806307 = 1209461) B1209461
theorem B806323 : Blo 802343 806323 := bstep (se 1 (by rfl) ⟨604742, by rfl⟩ : syracuseStep 806323 = 1209485) B1209485
theorem B806339 : Blo 802343 806339 := bstep (se 1 (by rfl) ⟨604754, by rfl⟩ : syracuseStep 806339 = 1209509) B1209509
theorem B904675 : Blo 802343 904675 := bstep (se 1 (by rfl) ⟨678506, by rfl⟩ : syracuseStep 904675 = 1357013) B1357013
theorem B2444813 : Blo 802343 2444813 := bstep (se 3 (by rfl) ⟨458402, by rfl⟩ : syracuseStep 2444813 = 916805) B916805
theorem B1527331 : Blo 802343 1527331 := bstep (se 1 (by rfl) ⟨1145498, by rfl⟩ : syracuseStep 1527331 = 2290997) B2290997
theorem B2444899 : Blo 802343 2444899 := bstep (se 1 (by rfl) ⟨1833674, by rfl⟩ : syracuseStep 2444899 = 3667349) B3667349
theorem B904819 : Blo 802343 904819 := bstep (se 1 (by rfl) ⟨678614, by rfl⟩ : syracuseStep 904819 = 1357229) B1357229
theorem B1527491 : Blo 802343 1527491 := bstep (se 1 (by rfl) ⟨1145618, by rfl⟩ : syracuseStep 1527491 = 2291237) B2291237
theorem B904963 : Blo 802343 904963 := bstep (se 1 (by rfl) ⟨678722, by rfl⟩ : syracuseStep 904963 = 1357445) B1357445
theorem B1527587 : Blo 802343 1527587 := bstep (se 1 (by rfl) ⟨1145690, by rfl⟩ : syracuseStep 1527587 = 2291381) B2291381
theorem B905107 : Blo 802343 905107 := bstep (se 1 (by rfl) ⟨678830, by rfl⟩ : syracuseStep 905107 = 1357661) B1357661
theorem B905251 : Blo 802343 905251 := bstep (se 1 (by rfl) ⟨678938, by rfl⟩ : syracuseStep 905251 = 1357877) B1357877
theorem B4575365 : Blo 802343 4575365 := bstep (se 4 (by rfl) ⟨428940, by rfl⟩ : syracuseStep 4575365 = 857881) B857881
theorem B905395 : Blo 802343 905395 := bstep (se 1 (by rfl) ⟨679046, by rfl⟩ : syracuseStep 905395 = 1358093) B1358093
theorem B5492941 : Blo 802343 5492941 := bstep (se 3 (by rfl) ⟨1029926, by rfl⟩ : syracuseStep 5492941 = 2059853) B2059853
theorem B905539 : Blo 802343 905539 := bstep (se 1 (by rfl) ⟨679154, by rfl⟩ : syracuseStep 905539 = 1358309) B1358309
theorem B19124677 : Blo 802343 19124677 := bstep (se 4 (by rfl) ⟨1792938, by rfl⟩ : syracuseStep 19124677 = 3585877) B3585877
theorem B905683 : Blo 802343 905683 := bstep (se 1 (by rfl) ⟨679262, by rfl⟩ : syracuseStep 905683 = 1358525) B1358525
theorem B2904589 : Blo 802343 2904589 := bstep (se 3 (by rfl) ⟨544610, by rfl⟩ : syracuseStep 2904589 = 1089221) B1089221
theorem B2708045 : Blo 802343 2708045 := bstep (se 3 (by rfl) ⟨507758, by rfl⟩ : syracuseStep 2708045 = 1015517) B1015517
theorem B905827 : Blo 802343 905827 := bstep (se 1 (by rfl) ⟨679370, by rfl⟩ : syracuseStep 905827 = 1358741) B1358741
theorem B2708099 : Blo 802343 2708099 := bstep (se 1 (by rfl) ⟨2031074, by rfl⟩ : syracuseStep 2708099 = 4062149) B4062149
theorem B1528561 : Blo 802343 1528561 := bstep (se 2 (by rfl) ⟨573210, by rfl⟩ : syracuseStep 1528561 = 1146421) B1146421
theorem B905971 : Blo 802343 905971 := bstep (se 1 (by rfl) ⟨679478, by rfl⟩ : syracuseStep 905971 = 1358957) B1358957
theorem B3265393 : Blo 802343 3265393 := bstep (se 2 (by rfl) ⟨1224522, by rfl⟩ : syracuseStep 3265393 = 2449045) B2449045
theorem B906115 : Blo 802343 906115 := bstep (se 1 (by rfl) ⟨679586, by rfl⟩ : syracuseStep 906115 = 1359173) B1359173
theorem B2708369 : Blo 802343 2708369 := bstep (se 2 (by rfl) ⟨1015638, by rfl⟩ : syracuseStep 2708369 = 2031277) B2031277
theorem B906259 : Blo 802343 906259 := bstep (se 1 (by rfl) ⟨679694, by rfl⟩ : syracuseStep 906259 = 1359389) B1359389
theorem B906403 : Blo 802343 906403 := bstep (se 1 (by rfl) ⟨679802, by rfl⟩ : syracuseStep 906403 = 1359605) B1359605
theorem B6870257 : Blo 802343 6870257 := bstep (se 2 (by rfl) ⟨2576346, by rfl⟩ : syracuseStep 6870257 = 5152693) B5152693
theorem B1627409 : Blo 802343 1627409 := bstep (se 2 (by rfl) ⟨610278, by rfl⟩ : syracuseStep 1627409 = 1220557) B1220557
theorem B906547 : Blo 802343 906547 := bstep (se 1 (by rfl) ⟨679910, by rfl⟩ : syracuseStep 906547 = 1359821) B1359821
theorem B2708909 : Blo 802343 2708909 := bstep (se 3 (by rfl) ⟨507920, by rfl⟩ : syracuseStep 2708909 = 1015841) B1015841
theorem B906691 : Blo 802343 906691 := bstep (se 1 (by rfl) ⟨680018, by rfl⟩ : syracuseStep 906691 = 1360037) B1360037
theorem B2708963 : Blo 802343 2708963 := bstep (se 1 (by rfl) ⟨2031722, by rfl⟩ : syracuseStep 2708963 = 4063445) B4063445
theorem B2905571 : Blo 802343 2905571 := bstep (se 1 (by rfl) ⟨2179178, by rfl⟩ : syracuseStep 2905571 = 4358357) B4358357
theorem B906835 : Blo 802343 906835 := bstep (se 1 (by rfl) ⟨680126, by rfl⟩ : syracuseStep 906835 = 1360253) B1360253
theorem B906979 : Blo 802343 906979 := bstep (se 1 (by rfl) ⟨680234, by rfl⟩ : syracuseStep 906979 = 1360469) B1360469
theorem B2709233 : Blo 802343 2709233 := bstep (se 2 (by rfl) ⟨1015962, by rfl⟩ : syracuseStep 2709233 = 2031925) B2031925
theorem B2578193 : Blo 802343 2578193 := bstep (se 2 (by rfl) ⟨966822, by rfl⟩ : syracuseStep 2578193 = 1933645) B1933645
theorem B1529617 : Blo 802343 1529617 := bstep (se 2 (by rfl) ⟨573606, by rfl⟩ : syracuseStep 1529617 = 1147213) B1147213
theorem B3856177 : Blo 802343 3856177 := bstep (se 2 (by rfl) ⟨1446066, by rfl⟩ : syracuseStep 3856177 = 2892133) B2892133
theorem B907123 : Blo 802343 907123 := bstep (se 1 (by rfl) ⟨680342, by rfl⟩ : syracuseStep 907123 = 1360685) B1360685
theorem B1530019 : Blo 802343 1530019 := bstep (se 1 (by rfl) ⟨1147514, by rfl⟩ : syracuseStep 1530019 = 2295029) B2295029
theorem B1530065 : Blo 802343 1530065 := bstep (se 2 (by rfl) ⟨573774, by rfl⟩ : syracuseStep 1530065 = 1147549) B1147549
theorem B2349283 : Blo 802343 2349283 := bstep (se 1 (by rfl) ⟨1761962, by rfl⟩ : syracuseStep 2349283 = 3523925) B3523925
theorem B2709773 : Blo 802343 2709773 := bstep (se 3 (by rfl) ⟨508082, by rfl⟩ : syracuseStep 2709773 = 1016165) B1016165
theorem B2709827 : Blo 802343 2709827 := bstep (se 1 (by rfl) ⟨2032370, by rfl⟩ : syracuseStep 2709827 = 4064741) B4064741
theorem B2578883 : Blo 802343 2578883 := bstep (se 1 (by rfl) ⟨1934162, by rfl⟩ : syracuseStep 2578883 = 3868325) B3868325
theorem B1530353 : Blo 802343 1530353 := bstep (se 2 (by rfl) ⟨573882, by rfl⟩ : syracuseStep 1530353 = 1147765) B1147765
theorem B1628675 : Blo 802343 1628675 := bstep (se 1 (by rfl) ⟨1221506, by rfl⟩ : syracuseStep 1628675 = 2443013) B2443013
theorem B2710097 : Blo 802343 2710097 := bstep (se 2 (by rfl) ⟨1016286, by rfl⟩ : syracuseStep 2710097 = 2032573) B2032573
theorem B2316899 : Blo 802343 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B3431267 : Blo 802343 3431267 := bstep (se 1 (by rfl) ⟨2573450, by rfl⟩ : syracuseStep 3431267 = 5146901) B5146901
theorem B3267469 : Blo 802343 3267469 := bstep (se 3 (by rfl) ⟨612650, by rfl⟩ : syracuseStep 3267469 = 1225301) B1225301
theorem B2710637 : Blo 802343 2710637 := bstep (se 3 (by rfl) ⟨508244, by rfl⟩ : syracuseStep 2710637 = 1016489) B1016489
theorem B2710691 : Blo 802343 2710691 := bstep (se 1 (by rfl) ⟨2033018, by rfl⟩ : syracuseStep 2710691 = 4066037) B4066037
theorem B1203521 : Blo 802343 1203521 := bstep (se 2 (by rfl) ⟨451320, by rfl⟩ : syracuseStep 1203521 = 902641) B902641
theorem B1203539 : Blo 802343 1203539 := bstep (se 1 (by rfl) ⟨902654, by rfl⟩ : syracuseStep 1203539 = 1805309) B1805309
theorem B1203569 : Blo 802343 1203569 := bstep (se 2 (by rfl) ⟨451338, by rfl⟩ : syracuseStep 1203569 = 902677) B902677
theorem B1203587 : Blo 802343 1203587 := bstep (se 1 (by rfl) ⟨902690, by rfl⟩ : syracuseStep 1203587 = 1805381) B1805381
theorem B1203617 : Blo 802343 1203617 := bstep (se 2 (by rfl) ⟨451356, by rfl⟩ : syracuseStep 1203617 = 902713) B902713
theorem B2710961 : Blo 802343 2710961 := bstep (se 2 (by rfl) ⟨1016610, by rfl⟩ : syracuseStep 2710961 = 2033221) B2033221
theorem B1203635 : Blo 802343 1203635 := bstep (se 1 (by rfl) ⟨902726, by rfl⟩ : syracuseStep 1203635 = 1805453) B1805453
theorem B11034053 : Blo 802343 11034053 := bstep (se 4 (by rfl) ⟨1034442, by rfl⟩ : syracuseStep 11034053 = 2068885) B2068885
theorem B2285005 : Blo 802343 2285005 := bstep (se 3 (by rfl) ⟨428438, by rfl⟩ : syracuseStep 2285005 = 856877) B856877
theorem B1203665 : Blo 802343 1203665 := bstep (se 2 (by rfl) ⟨451374, by rfl⟩ : syracuseStep 1203665 = 902749) B902749
theorem B1203683 : Blo 802343 1203683 := bstep (se 1 (by rfl) ⟨902762, by rfl⟩ : syracuseStep 1203683 = 1805525) B1805525
theorem B1203713 : Blo 802343 1203713 := bstep (se 2 (by rfl) ⟨451392, by rfl⟩ : syracuseStep 1203713 = 902785) B902785
theorem B2448899 : Blo 802343 2448899 := bstep (se 1 (by rfl) ⟨1836674, by rfl⟩ : syracuseStep 2448899 = 3673349) B3673349
theorem B1203731 : Blo 802343 1203731 := bstep (se 1 (by rfl) ⟨902798, by rfl⟩ : syracuseStep 1203731 = 1805597) B1805597
theorem B1203761 : Blo 802343 1203761 := bstep (se 2 (by rfl) ⟨451410, by rfl⟩ : syracuseStep 1203761 = 902821) B902821
theorem B1203779 : Blo 802343 1203779 := bstep (se 1 (by rfl) ⟨902834, by rfl⟩ : syracuseStep 1203779 = 1805669) B1805669
theorem B1203809 : Blo 802343 1203809 := bstep (se 2 (by rfl) ⟨451428, by rfl⟩ : syracuseStep 1203809 = 902857) B902857
theorem B2285165 : Blo 802343 2285165 := bstep (se 3 (by rfl) ⟨428468, by rfl⟩ : syracuseStep 2285165 = 856937) B856937
theorem B1203827 : Blo 802343 1203827 := bstep (se 1 (by rfl) ⟨902870, by rfl⟩ : syracuseStep 1203827 = 1805741) B1805741
theorem B1203857 : Blo 802343 1203857 := bstep (se 2 (by rfl) ⟨451446, by rfl⟩ : syracuseStep 1203857 = 902893) B902893
theorem B1203875 : Blo 802343 1203875 := bstep (se 1 (by rfl) ⟨902906, by rfl⟩ : syracuseStep 1203875 = 1805813) B1805813
theorem B1203905 : Blo 802343 1203905 := bstep (se 2 (by rfl) ⟨451464, by rfl⟩ : syracuseStep 1203905 = 902929) B902929
theorem B1203923 : Blo 802343 1203923 := bstep (se 1 (by rfl) ⟨902942, by rfl⟩ : syracuseStep 1203923 = 1805885) B1805885
theorem B1203953 : Blo 802343 1203953 := bstep (se 2 (by rfl) ⟨451482, by rfl⟩ : syracuseStep 1203953 = 902965) B902965
theorem B1203971 : Blo 802343 1203971 := bstep (se 1 (by rfl) ⟨902978, by rfl⟩ : syracuseStep 1203971 = 1805957) B1805957
theorem B35249941 : Blo 802343 35249941 := bstep (se 6 (by rfl) ⟨826170, by rfl⟩ : syracuseStep 35249941 = 1652341) B1652341
theorem B1204001 : Blo 802343 1204001 := bstep (se 2 (by rfl) ⟨451500, by rfl⟩ : syracuseStep 1204001 = 903001) B903001
theorem B2285347 : Blo 802343 2285347 := bstep (se 1 (by rfl) ⟨1714010, by rfl⟩ : syracuseStep 2285347 = 3428021) B3428021
theorem B1204019 : Blo 802343 1204019 := bstep (se 1 (by rfl) ⟨903014, by rfl⟩ : syracuseStep 1204019 = 1806029) B1806029
theorem B1204049 : Blo 802343 1204049 := bstep (se 2 (by rfl) ⟨451518, by rfl⟩ : syracuseStep 1204049 = 903037) B903037
theorem B1204067 : Blo 802343 1204067 := bstep (se 1 (by rfl) ⟨903050, by rfl⟩ : syracuseStep 1204067 = 1806101) B1806101
theorem B1204097 : Blo 802343 1204097 := bstep (se 2 (by rfl) ⟨451536, by rfl⟩ : syracuseStep 1204097 = 903073) B903073
theorem B4579213 : Blo 802343 4579213 := bstep (se 3 (by rfl) ⟨858602, by rfl⟩ : syracuseStep 4579213 = 1717205) B1717205
theorem B1204115 : Blo 802343 1204115 := bstep (se 1 (by rfl) ⟨903086, by rfl⟩ : syracuseStep 1204115 = 1806173) B1806173
theorem B1204145 : Blo 802343 1204145 := bstep (se 2 (by rfl) ⟨451554, by rfl⟩ : syracuseStep 1204145 = 903109) B903109
theorem B1204163 : Blo 802343 1204163 := bstep (se 1 (by rfl) ⟨903122, by rfl⟩ : syracuseStep 1204163 = 1806245) B1806245
theorem B2711501 : Blo 802343 2711501 := bstep (se 3 (by rfl) ⟨508406, by rfl⟩ : syracuseStep 2711501 = 1016813) B1016813
theorem B1204193 : Blo 802343 1204193 := bstep (se 2 (by rfl) ⟨451572, by rfl⟩ : syracuseStep 1204193 = 903145) B903145
theorem B1204211 : Blo 802343 1204211 := bstep (se 1 (by rfl) ⟨903158, by rfl⟩ : syracuseStep 1204211 = 1806317) B1806317
theorem B2711555 : Blo 802343 2711555 := bstep (se 1 (by rfl) ⟨2033666, by rfl⟩ : syracuseStep 2711555 = 4067333) B4067333
theorem B1204241 : Blo 802343 1204241 := bstep (se 2 (by rfl) ⟨451590, by rfl⟩ : syracuseStep 1204241 = 903181) B903181
theorem B1204259 : Blo 802343 1204259 := bstep (se 1 (by rfl) ⟨903194, by rfl⟩ : syracuseStep 1204259 = 1806389) B1806389
theorem B1204289 : Blo 802343 1204289 := bstep (se 2 (by rfl) ⟨451608, by rfl⟩ : syracuseStep 1204289 = 903217) B903217
theorem B1466435 : Blo 802343 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B1204307 : Blo 802343 1204307 := bstep (se 1 (by rfl) ⟨903230, by rfl⟩ : syracuseStep 1204307 = 1806461) B1806461
theorem B2613347 : Blo 802343 2613347 := bstep (se 1 (by rfl) ⟨1960010, by rfl⟩ : syracuseStep 2613347 = 3920021) B3920021
theorem B1204337 : Blo 802343 1204337 := bstep (se 2 (by rfl) ⟨451626, by rfl⟩ : syracuseStep 1204337 = 903253) B903253
theorem B1204355 : Blo 802343 1204355 := bstep (se 1 (by rfl) ⟨903266, by rfl⟩ : syracuseStep 1204355 = 1806533) B1806533
theorem B1204385 : Blo 802343 1204385 := bstep (se 2 (by rfl) ⟨451644, by rfl⟩ : syracuseStep 1204385 = 903289) B903289
theorem B2580653 : Blo 802343 2580653 := bstep (se 3 (by rfl) ⟨483872, by rfl⟩ : syracuseStep 2580653 = 967745) B967745
theorem B1204403 : Blo 802343 1204403 := bstep (se 1 (by rfl) ⟨903302, by rfl⟩ : syracuseStep 1204403 = 1806605) B1806605
theorem B1204433 : Blo 802343 1204433 := bstep (se 2 (by rfl) ⟨451662, by rfl⟩ : syracuseStep 1204433 = 903325) B903325
theorem B1204451 : Blo 802343 1204451 := bstep (se 1 (by rfl) ⟨903338, by rfl⟩ : syracuseStep 1204451 = 1806677) B1806677
theorem B1204481 : Blo 802343 1204481 := bstep (se 2 (by rfl) ⟨451680, by rfl⟩ : syracuseStep 1204481 = 903361) B903361
theorem B2711825 : Blo 802343 2711825 := bstep (se 2 (by rfl) ⟨1016934, by rfl⟩ : syracuseStep 2711825 = 2033869) B2033869
theorem B1204499 : Blo 802343 1204499 := bstep (se 1 (by rfl) ⟨903374, by rfl⟩ : syracuseStep 1204499 = 1806749) B1806749
theorem B2580781 : Blo 802343 2580781 := bstep (se 3 (by rfl) ⟨483896, by rfl⟩ : syracuseStep 2580781 = 967793) B967793
theorem B1204529 : Blo 802343 1204529 := bstep (se 2 (by rfl) ⟨451698, by rfl⟩ : syracuseStep 1204529 = 903397) B903397
theorem B1204547 : Blo 802343 1204547 := bstep (se 1 (by rfl) ⟨903410, by rfl⟩ : syracuseStep 1204547 = 1806821) B1806821
theorem B1204577 : Blo 802343 1204577 := bstep (se 2 (by rfl) ⟨451716, by rfl⟩ : syracuseStep 1204577 = 903433) B903433
theorem B1204595 : Blo 802343 1204595 := bstep (se 1 (by rfl) ⟨903446, by rfl⟩ : syracuseStep 1204595 = 1806893) B1806893
theorem B1204625 : Blo 802343 1204625 := bstep (se 2 (by rfl) ⟨451734, by rfl⟩ : syracuseStep 1204625 = 903469) B903469
theorem B1204643 : Blo 802343 1204643 := bstep (se 1 (by rfl) ⟨903482, by rfl⟩ : syracuseStep 1204643 = 1806965) B1806965
theorem B1204673 : Blo 802343 1204673 := bstep (se 2 (by rfl) ⟨451752, by rfl⟩ : syracuseStep 1204673 = 903505) B903505
theorem B1204691 : Blo 802343 1204691 := bstep (se 1 (by rfl) ⟨903518, by rfl⟩ : syracuseStep 1204691 = 1807037) B1807037
theorem B1204721 : Blo 802343 1204721 := bstep (se 2 (by rfl) ⟨451770, by rfl⟩ : syracuseStep 1204721 = 903541) B903541
theorem B1204739 : Blo 802343 1204739 := bstep (se 1 (by rfl) ⟨903554, by rfl⟩ : syracuseStep 1204739 = 1807109) B1807109
theorem B1204769 : Blo 802343 1204769 := bstep (se 2 (by rfl) ⟨451788, by rfl⟩ : syracuseStep 1204769 = 903577) B903577
theorem B2581037 : Blo 802343 2581037 := bstep (se 3 (by rfl) ⟨483944, by rfl⟩ : syracuseStep 2581037 = 967889) B967889
theorem B1204787 : Blo 802343 1204787 := bstep (se 1 (by rfl) ⟨903590, by rfl⟩ : syracuseStep 1204787 = 1807181) B1807181
theorem B1204817 : Blo 802343 1204817 := bstep (se 2 (by rfl) ⟨451806, by rfl⟩ : syracuseStep 1204817 = 903613) B903613
theorem B1204835 : Blo 802343 1204835 := bstep (se 1 (by rfl) ⟨903626, by rfl⟩ : syracuseStep 1204835 = 1807253) B1807253
theorem B7070321 : Blo 802343 7070321 := bstep (se 2 (by rfl) ⟨2651370, by rfl⟩ : syracuseStep 7070321 = 5302741) B5302741
theorem B1204865 : Blo 802343 1204865 := bstep (se 2 (by rfl) ⟨451824, by rfl⟩ : syracuseStep 1204865 = 903649) B903649
theorem B1204883 : Blo 802343 1204883 := bstep (se 1 (by rfl) ⟨903662, by rfl⟩ : syracuseStep 1204883 = 1807325) B1807325
theorem B1204913 : Blo 802343 1204913 := bstep (se 2 (by rfl) ⟨451842, by rfl⟩ : syracuseStep 1204913 = 903685) B903685
theorem B1204931 : Blo 802343 1204931 := bstep (se 1 (by rfl) ⟨903698, by rfl⟩ : syracuseStep 1204931 = 1807397) B1807397
theorem B1204961 : Blo 802343 1204961 := bstep (se 2 (by rfl) ⟨451860, by rfl⟩ : syracuseStep 1204961 = 903721) B903721
theorem B1204979 : Blo 802343 1204979 := bstep (se 1 (by rfl) ⟨903734, by rfl⟩ : syracuseStep 1204979 = 1807469) B1807469
theorem B2450189 : Blo 802343 2450189 := bstep (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) B918821
theorem B1205009 : Blo 802343 1205009 := bstep (se 2 (by rfl) ⟨451878, by rfl⟩ : syracuseStep 1205009 = 903757) B903757
theorem B3859235 : Blo 802343 3859235 := bstep (se 1 (by rfl) ⟨2894426, by rfl⟩ : syracuseStep 3859235 = 5788853) B5788853
theorem B1205027 : Blo 802343 1205027 := bstep (se 1 (by rfl) ⟨903770, by rfl⟩ : syracuseStep 1205027 = 1807541) B1807541
theorem B2712365 : Blo 802343 2712365 := bstep (se 3 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 2712365 = 1017137) B1017137
theorem B1205057 : Blo 802343 1205057 := bstep (se 2 (by rfl) ⟨451896, by rfl⟩ : syracuseStep 1205057 = 903793) B903793
theorem B1205075 : Blo 802343 1205075 := bstep (se 1 (by rfl) ⟨903806, by rfl⟩ : syracuseStep 1205075 = 1807613) B1807613
theorem B2712419 : Blo 802343 2712419 := bstep (se 1 (by rfl) ⟨2034314, by rfl⟩ : syracuseStep 2712419 = 4068629) B4068629
theorem B1631075 : Blo 802343 1631075 := bstep (se 1 (by rfl) ⟨1223306, by rfl⟩ : syracuseStep 1631075 = 2446613) B2446613
theorem B1205105 : Blo 802343 1205105 := bstep (se 2 (by rfl) ⟨451914, by rfl⟩ : syracuseStep 1205105 = 903829) B903829
theorem B1205123 : Blo 802343 1205123 := bstep (se 1 (by rfl) ⟨903842, by rfl⟩ : syracuseStep 1205123 = 1807685) B1807685
theorem B1205153 : Blo 802343 1205153 := bstep (se 2 (by rfl) ⟨451932, by rfl⟩ : syracuseStep 1205153 = 903865) B903865
theorem B5235619 : Blo 802343 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B1205171 : Blo 802343 1205171 := bstep (se 1 (by rfl) ⟨903878, by rfl⟩ : syracuseStep 1205171 = 1807757) B1807757
theorem B1205201 : Blo 802343 1205201 := bstep (se 2 (by rfl) ⟨451950, by rfl⟩ : syracuseStep 1205201 = 903901) B903901
theorem B1205219 : Blo 802343 1205219 := bstep (se 1 (by rfl) ⟨903914, by rfl⟩ : syracuseStep 1205219 = 1807829) B1807829
theorem B1205249 : Blo 802343 1205249 := bstep (se 2 (by rfl) ⟨451968, by rfl⟩ : syracuseStep 1205249 = 903937) B903937
theorem B1205267 : Blo 802343 1205267 := bstep (se 1 (by rfl) ⟨903950, by rfl⟩ : syracuseStep 1205267 = 1807901) B1807901
theorem B1205297 : Blo 802343 1205297 := bstep (se 2 (by rfl) ⟨451986, by rfl⟩ : syracuseStep 1205297 = 903973) B903973
theorem B2090033 : Blo 802343 2090033 := bstep (se 2 (by rfl) ⟨783762, by rfl⟩ : syracuseStep 2090033 = 1567525) B1567525
theorem B1205315 : Blo 802343 1205315 := bstep (se 1 (by rfl) ⟨903986, by rfl⟩ : syracuseStep 1205315 = 1807973) B1807973
theorem B1205345 : Blo 802343 1205345 := bstep (se 2 (by rfl) ⟨452004, by rfl⟩ : syracuseStep 1205345 = 904009) B904009
theorem B2712689 : Blo 802343 2712689 := bstep (se 2 (by rfl) ⟨1017258, by rfl⟩ : syracuseStep 2712689 = 2034517) B2034517
theorem B1205363 : Blo 802343 1205363 := bstep (se 1 (by rfl) ⟨904022, by rfl⟩ : syracuseStep 1205363 = 1808045) B1808045
theorem B2286737 : Blo 802343 2286737 := bstep (se 2 (by rfl) ⟨857526, by rfl⟩ : syracuseStep 2286737 = 1715053) B1715053
theorem B1205393 : Blo 802343 1205393 := bstep (se 2 (by rfl) ⟨452022, by rfl⟩ : syracuseStep 1205393 = 904045) B904045
theorem B1205411 : Blo 802343 1205411 := bstep (se 1 (by rfl) ⟨904058, by rfl⟩ : syracuseStep 1205411 = 1808117) B1808117
theorem B1205441 : Blo 802343 1205441 := bstep (se 2 (by rfl) ⟨452040, by rfl⟩ : syracuseStep 1205441 = 904081) B904081
theorem B1205459 : Blo 802343 1205459 := bstep (se 1 (by rfl) ⟨904094, by rfl⟩ : syracuseStep 1205459 = 1808189) B1808189
theorem B1205489 : Blo 802343 1205489 := bstep (se 2 (by rfl) ⟨452058, by rfl⟩ : syracuseStep 1205489 = 904117) B904117
theorem B1205507 : Blo 802343 1205507 := bstep (se 1 (by rfl) ⟨904130, by rfl⟩ : syracuseStep 1205507 = 1808261) B1808261
theorem B1205537 : Blo 802343 1205537 := bstep (se 2 (by rfl) ⟨452076, by rfl⟩ : syracuseStep 1205537 = 904153) B904153
theorem B1205555 : Blo 802343 1205555 := bstep (se 1 (by rfl) ⟨904166, by rfl⟩ : syracuseStep 1205555 = 1808333) B1808333
theorem B1205585 : Blo 802343 1205585 := bstep (se 2 (by rfl) ⟨452094, by rfl⟩ : syracuseStep 1205585 = 904189) B904189
theorem B1205603 : Blo 802343 1205603 := bstep (se 1 (by rfl) ⟨904202, by rfl⟩ : syracuseStep 1205603 = 1808405) B1808405
theorem B1205633 : Blo 802343 1205633 := bstep (se 2 (by rfl) ⟨452112, by rfl⟩ : syracuseStep 1205633 = 904225) B904225
theorem B1205651 : Blo 802343 1205651 := bstep (se 1 (by rfl) ⟨904238, by rfl⟩ : syracuseStep 1205651 = 1808477) B1808477
theorem B1205681 : Blo 802343 1205681 := bstep (se 2 (by rfl) ⟨452130, by rfl⟩ : syracuseStep 1205681 = 904261) B904261
theorem B1205699 : Blo 802343 1205699 := bstep (se 1 (by rfl) ⟨904274, by rfl⟩ : syracuseStep 1205699 = 1808549) B1808549
theorem B1205729 : Blo 802343 1205729 := bstep (se 2 (by rfl) ⟨452148, by rfl⟩ : syracuseStep 1205729 = 904297) B904297
theorem B16508387 : Blo 802343 16508387 := bstep (se 1 (by rfl) ⟨12381290, by rfl⟩ : syracuseStep 16508387 = 24762581) B24762581
theorem B2483693 : Blo 802343 2483693 := bstep (se 3 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 2483693 = 931385) B931385
theorem B8349169 : Blo 802343 8349169 := bstep (se 2 (by rfl) ⟨3130938, by rfl⟩ : syracuseStep 8349169 = 6261877) B6261877
theorem B1205747 : Blo 802343 1205747 := bstep (se 1 (by rfl) ⟨904310, by rfl⟩ : syracuseStep 1205747 = 1808621) B1808621
theorem B1205777 : Blo 802343 1205777 := bstep (se 2 (by rfl) ⟨452166, by rfl⟩ : syracuseStep 1205777 = 904333) B904333
theorem B1205795 : Blo 802343 1205795 := bstep (se 1 (by rfl) ⟨904346, by rfl⟩ : syracuseStep 1205795 = 1808693) B1808693
theorem B1205825 : Blo 802343 1205825 := bstep (se 2 (by rfl) ⟨452184, by rfl⟩ : syracuseStep 1205825 = 904369) B904369
theorem B4646477 : Blo 802343 4646477 := bstep (se 3 (by rfl) ⟨871214, by rfl⟩ : syracuseStep 4646477 = 1742429) B1742429
theorem B1205843 : Blo 802343 1205843 := bstep (se 1 (by rfl) ⟨904382, by rfl⟩ : syracuseStep 1205843 = 1808765) B1808765
theorem B1205873 : Blo 802343 1205873 := bstep (se 2 (by rfl) ⟨452202, by rfl⟩ : syracuseStep 1205873 = 904405) B904405
theorem B1205891 : Blo 802343 1205891 := bstep (se 1 (by rfl) ⟨904418, by rfl⟩ : syracuseStep 1205891 = 1808837) B1808837
theorem B2713229 : Blo 802343 2713229 := bstep (se 3 (by rfl) ⟨508730, by rfl⟩ : syracuseStep 2713229 = 1017461) B1017461
theorem B1205921 : Blo 802343 1205921 := bstep (se 2 (by rfl) ⟨452220, by rfl⟩ : syracuseStep 1205921 = 904441) B904441
theorem B1205939 : Blo 802343 1205939 := bstep (se 1 (by rfl) ⟨904454, by rfl⟩ : syracuseStep 1205939 = 1808909) B1808909
theorem B2713283 : Blo 802343 2713283 := bstep (se 1 (by rfl) ⟨2034962, by rfl⟩ : syracuseStep 2713283 = 4069925) B4069925
theorem B1205969 : Blo 802343 1205969 := bstep (se 2 (by rfl) ⟨452238, by rfl⟩ : syracuseStep 1205969 = 904477) B904477
theorem B1205987 : Blo 802343 1205987 := bstep (se 1 (by rfl) ⟨904490, by rfl⟩ : syracuseStep 1205987 = 1808981) B1808981
theorem B1206017 : Blo 802343 1206017 := bstep (se 2 (by rfl) ⟨452256, by rfl⟩ : syracuseStep 1206017 = 904513) B904513
theorem B1206035 : Blo 802343 1206035 := bstep (se 1 (by rfl) ⟨904526, by rfl⟩ : syracuseStep 1206035 = 1809053) B1809053
theorem B2451235 : Blo 802343 2451235 := bstep (se 1 (by rfl) ⟨1838426, by rfl⟩ : syracuseStep 2451235 = 3676853) B3676853
theorem B1206065 : Blo 802343 1206065 := bstep (se 2 (by rfl) ⟨452274, by rfl⟩ : syracuseStep 1206065 = 904549) B904549
theorem B1206083 : Blo 802343 1206083 := bstep (se 1 (by rfl) ⟨904562, by rfl⟩ : syracuseStep 1206083 = 1809125) B1809125
theorem B4581197 : Blo 802343 4581197 := bstep (se 3 (by rfl) ⟨858974, by rfl⟩ : syracuseStep 4581197 = 1717949) B1717949
theorem B1206113 : Blo 802343 1206113 := bstep (se 2 (by rfl) ⟨452292, by rfl⟩ : syracuseStep 1206113 = 904585) B904585
theorem B1206131 : Blo 802343 1206131 := bstep (se 1 (by rfl) ⟨904598, by rfl⟩ : syracuseStep 1206131 = 1809197) B1809197
theorem B11003789 : Blo 802343 11003789 := bstep (se 3 (by rfl) ⟨2063210, by rfl⟩ : syracuseStep 11003789 = 4126421) B4126421
theorem B1206161 : Blo 802343 1206161 := bstep (se 2 (by rfl) ⟨452310, by rfl⟩ : syracuseStep 1206161 = 904621) B904621
theorem B1206179 : Blo 802343 1206179 := bstep (se 1 (by rfl) ⟨904634, by rfl⟩ : syracuseStep 1206179 = 1809269) B1809269
theorem B1632163 : Blo 802343 1632163 := bstep (se 1 (by rfl) ⟨1224122, by rfl⟩ : syracuseStep 1632163 = 2448245) B2448245
theorem B1206209 : Blo 802343 1206209 := bstep (se 2 (by rfl) ⟨452328, by rfl⟩ : syracuseStep 1206209 = 904657) B904657
theorem B2713553 : Blo 802343 2713553 := bstep (se 2 (by rfl) ⟨1017582, by rfl⟩ : syracuseStep 2713553 = 2035165) B2035165
theorem B1206227 : Blo 802343 1206227 := bstep (se 1 (by rfl) ⟨904670, by rfl⟩ : syracuseStep 1206227 = 1809341) B1809341
theorem B1206257 : Blo 802343 1206257 := bstep (se 2 (by rfl) ⟨452346, by rfl⟩ : syracuseStep 1206257 = 904693) B904693
theorem B1206275 : Blo 802343 1206275 := bstep (se 1 (by rfl) ⟨904706, by rfl⟩ : syracuseStep 1206275 = 1809413) B1809413
theorem B1206305 : Blo 802343 1206305 := bstep (se 2 (by rfl) ⟨452364, by rfl⟩ : syracuseStep 1206305 = 904729) B904729
theorem B2582563 : Blo 802343 2582563 := bstep (se 1 (by rfl) ⟨1936922, by rfl⟩ : syracuseStep 2582563 = 3873845) B3873845
theorem B1206323 : Blo 802343 1206323 := bstep (se 1 (by rfl) ⟨904742, by rfl⟩ : syracuseStep 1206323 = 1809485) B1809485
theorem B2287693 : Blo 802343 2287693 := bstep (se 3 (by rfl) ⟨428942, by rfl⟩ : syracuseStep 2287693 = 857885) B857885
theorem B1206353 : Blo 802343 1206353 := bstep (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) B904765
theorem B1206371 : Blo 802343 1206371 := bstep (se 1 (by rfl) ⟨904778, by rfl⟩ : syracuseStep 1206371 = 1809557) B1809557
theorem B16509041 : Blo 802343 16509041 := bstep (se 2 (by rfl) ⟨6190890, by rfl⟩ : syracuseStep 16509041 = 12381781) B12381781
theorem B1206401 : Blo 802343 1206401 := bstep (se 2 (by rfl) ⟨452400, by rfl⟩ : syracuseStep 1206401 = 904801) B904801
theorem B1206419 : Blo 802343 1206419 := bstep (se 1 (by rfl) ⟨904814, by rfl⟩ : syracuseStep 1206419 = 1809629) B1809629
theorem B1206449 : Blo 802343 1206449 := bstep (se 2 (by rfl) ⟨452418, by rfl⟩ : syracuseStep 1206449 = 904837) B904837
theorem B1206467 : Blo 802343 1206467 := bstep (se 1 (by rfl) ⟨904850, by rfl⟩ : syracuseStep 1206467 = 1809701) B1809701
theorem B6187205 : Blo 802343 6187205 := bstep (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) B1160101
theorem B1206497 : Blo 802343 1206497 := bstep (se 2 (by rfl) ⟨452436, by rfl⟩ : syracuseStep 1206497 = 904873) B904873
theorem B1206515 : Blo 802343 1206515 := bstep (se 1 (by rfl) ⟨904886, by rfl⟩ : syracuseStep 1206515 = 1809773) B1809773
theorem B1206545 : Blo 802343 1206545 := bstep (se 2 (by rfl) ⟨452454, by rfl⟩ : syracuseStep 1206545 = 904909) B904909
theorem B1206563 : Blo 802343 1206563 := bstep (se 1 (by rfl) ⟨904922, by rfl⟩ : syracuseStep 1206563 = 1809845) B1809845
theorem B2287921 : Blo 802343 2287921 := bstep (se 2 (by rfl) ⟨857970, by rfl⟩ : syracuseStep 2287921 = 1715941) B1715941
theorem B1206593 : Blo 802343 1206593 := bstep (se 2 (by rfl) ⟨452472, by rfl⟩ : syracuseStep 1206593 = 904945) B904945
theorem B1206611 : Blo 802343 1206611 := bstep (se 1 (by rfl) ⟨904958, by rfl⟩ : syracuseStep 1206611 = 1809917) B1809917
theorem B1206641 : Blo 802343 1206641 := bstep (se 2 (by rfl) ⟨452490, by rfl⟩ : syracuseStep 1206641 = 904981) B904981
theorem B1206659 : Blo 802343 1206659 := bstep (se 1 (by rfl) ⟨904994, by rfl⟩ : syracuseStep 1206659 = 1809989) B1809989
theorem B1206689 : Blo 802343 1206689 := bstep (se 2 (by rfl) ⟨452508, by rfl⟩ : syracuseStep 1206689 = 905017) B905017
theorem B1206707 : Blo 802343 1206707 := bstep (se 1 (by rfl) ⟨905030, by rfl⟩ : syracuseStep 1206707 = 1810061) B1810061
theorem B3434957 : Blo 802343 3434957 := bstep (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) B1288109
theorem B2288081 : Blo 802343 2288081 := bstep (se 2 (by rfl) ⟨858030, by rfl⟩ : syracuseStep 2288081 = 1716061) B1716061
theorem B1206737 : Blo 802343 1206737 := bstep (se 2 (by rfl) ⟨452526, by rfl⟩ : syracuseStep 1206737 = 905053) B905053
theorem B1206755 : Blo 802343 1206755 := bstep (se 1 (by rfl) ⟨905066, by rfl⟩ : syracuseStep 1206755 = 1810133) B1810133
theorem B2714093 : Blo 802343 2714093 := bstep (se 3 (by rfl) ⟨508892, by rfl⟩ : syracuseStep 2714093 = 1017785) B1017785
theorem B3434993 : Blo 802343 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B1206785 : Blo 802343 1206785 := bstep (se 2 (by rfl) ⟨452544, by rfl⟩ : syracuseStep 1206785 = 905089) B905089
theorem B1206803 : Blo 802343 1206803 := bstep (se 1 (by rfl) ⟨905102, by rfl⟩ : syracuseStep 1206803 = 1810205) B1810205
theorem B2714147 : Blo 802343 2714147 := bstep (se 1 (by rfl) ⟨2035610, by rfl⟩ : syracuseStep 2714147 = 4071221) B4071221
theorem B1206833 : Blo 802343 1206833 := bstep (se 2 (by rfl) ⟨452562, by rfl⟩ : syracuseStep 1206833 = 905125) B905125
theorem B2288195 : Blo 802343 2288195 := bstep (se 1 (by rfl) ⟨1716146, by rfl⟩ : syracuseStep 2288195 = 3432293) B3432293
theorem B1206851 : Blo 802343 1206851 := bstep (se 1 (by rfl) ⟨905138, by rfl⟩ : syracuseStep 1206851 = 1810277) B1810277
theorem B1206881 : Blo 802343 1206881 := bstep (se 2 (by rfl) ⟨452580, by rfl⟩ : syracuseStep 1206881 = 905161) B905161
theorem B1206899 : Blo 802343 1206899 := bstep (se 1 (by rfl) ⟨905174, by rfl⟩ : syracuseStep 1206899 = 1810349) B1810349
theorem B1206929 : Blo 802343 1206929 := bstep (se 2 (by rfl) ⟨452598, by rfl⟩ : syracuseStep 1206929 = 905197) B905197
theorem B1206947 : Blo 802343 1206947 := bstep (se 1 (by rfl) ⟨905210, by rfl⟩ : syracuseStep 1206947 = 1810421) B1810421
theorem B1206977 : Blo 802343 1206977 := bstep (se 2 (by rfl) ⟨452616, by rfl⟩ : syracuseStep 1206977 = 905233) B905233
theorem B1206995 : Blo 802343 1206995 := bstep (se 1 (by rfl) ⟨905246, by rfl⟩ : syracuseStep 1206995 = 1810493) B1810493
theorem B4582129 : Blo 802343 4582129 := bstep (se 2 (by rfl) ⟨1718298, by rfl⟩ : syracuseStep 4582129 = 3436597) B3436597
theorem B1207025 : Blo 802343 1207025 := bstep (se 2 (by rfl) ⟨452634, by rfl⟩ : syracuseStep 1207025 = 905269) B905269
theorem B1207043 : Blo 802343 1207043 := bstep (se 1 (by rfl) ⟨905282, by rfl⟩ : syracuseStep 1207043 = 1810565) B1810565
theorem B1207073 : Blo 802343 1207073 := bstep (se 2 (by rfl) ⟨452652, by rfl⟩ : syracuseStep 1207073 = 905305) B905305
theorem B2714417 : Blo 802343 2714417 := bstep (se 2 (by rfl) ⟨1017906, by rfl⟩ : syracuseStep 2714417 = 2035813) B2035813
theorem B1207091 : Blo 802343 1207091 := bstep (se 1 (by rfl) ⟨905318, by rfl⟩ : syracuseStep 1207091 = 1810637) B1810637
theorem B1207121 : Blo 802343 1207121 := bstep (se 2 (by rfl) ⟨452670, by rfl⟩ : syracuseStep 1207121 = 905341) B905341
theorem B2485073 : Blo 802343 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B1207139 : Blo 802343 1207139 := bstep (se 1 (by rfl) ⟨905354, by rfl⟩ : syracuseStep 1207139 = 1810709) B1810709
theorem B1207169 : Blo 802343 1207169 := bstep (se 2 (by rfl) ⟨452688, by rfl⟩ : syracuseStep 1207169 = 905377) B905377
theorem B1207187 : Blo 802343 1207187 := bstep (se 1 (by rfl) ⟨905390, by rfl⟩ : syracuseStep 1207187 = 1810781) B1810781
theorem B1207217 : Blo 802343 1207217 := bstep (se 2 (by rfl) ⟨452706, by rfl⟩ : syracuseStep 1207217 = 905413) B905413
theorem B1207235 : Blo 802343 1207235 := bstep (se 1 (by rfl) ⟨905426, by rfl⟩ : syracuseStep 1207235 = 1810853) B1810853
theorem B1207265 : Blo 802343 1207265 := bstep (se 2 (by rfl) ⟨452724, by rfl⟩ : syracuseStep 1207265 = 905449) B905449
theorem B1207283 : Blo 802343 1207283 := bstep (se 1 (by rfl) ⟨905462, by rfl⟩ : syracuseStep 1207283 = 1810925) B1810925
theorem B1207313 : Blo 802343 1207313 := bstep (se 2 (by rfl) ⟨452742, by rfl⟩ : syracuseStep 1207313 = 905485) B905485
theorem B1207331 : Blo 802343 1207331 := bstep (se 1 (by rfl) ⟨905498, by rfl⟩ : syracuseStep 1207331 = 1810997) B1810997
theorem B1207361 : Blo 802343 1207361 := bstep (se 2 (by rfl) ⟨452760, by rfl⟩ : syracuseStep 1207361 = 905521) B905521
theorem B1207379 : Blo 802343 1207379 := bstep (se 1 (by rfl) ⟨905534, by rfl⟩ : syracuseStep 1207379 = 1811069) B1811069
theorem B1207409 : Blo 802343 1207409 := bstep (se 2 (by rfl) ⟨452778, by rfl⟩ : syracuseStep 1207409 = 905557) B905557
theorem B1207427 : Blo 802343 1207427 := bstep (se 1 (by rfl) ⟨905570, by rfl⟩ : syracuseStep 1207427 = 1811141) B1811141
theorem B1207457 : Blo 802343 1207457 := bstep (se 2 (by rfl) ⟨452796, by rfl⟩ : syracuseStep 1207457 = 905593) B905593
theorem B1207475 : Blo 802343 1207475 := bstep (se 1 (by rfl) ⟨905606, by rfl⟩ : syracuseStep 1207475 = 1811213) B1811213
theorem B1207505 : Blo 802343 1207505 := bstep (se 2 (by rfl) ⟨452814, by rfl⟩ : syracuseStep 1207505 = 905629) B905629
theorem B1207523 : Blo 802343 1207523 := bstep (se 1 (by rfl) ⟨905642, by rfl⟩ : syracuseStep 1207523 = 1811285) B1811285
theorem B1207553 : Blo 802343 1207553 := bstep (se 2 (by rfl) ⟨452832, by rfl⟩ : syracuseStep 1207553 = 905665) B905665
theorem B1207571 : Blo 802343 1207571 := bstep (se 1 (by rfl) ⟨905678, by rfl⟩ : syracuseStep 1207571 = 1811357) B1811357
theorem B1207601 : Blo 802343 1207601 := bstep (se 2 (by rfl) ⟨452850, by rfl⟩ : syracuseStep 1207601 = 905701) B905701
theorem B1207619 : Blo 802343 1207619 := bstep (se 1 (by rfl) ⟨905714, by rfl⟩ : syracuseStep 1207619 = 1811429) B1811429
theorem B2714957 : Blo 802343 2714957 := bstep (se 3 (by rfl) ⟨509054, by rfl⟩ : syracuseStep 2714957 = 1018109) B1018109
theorem B1207649 : Blo 802343 1207649 := bstep (se 2 (by rfl) ⟨452868, by rfl⟩ : syracuseStep 1207649 = 905737) B905737
theorem B13036913 : Blo 802343 13036913 := bstep (se 2 (by rfl) ⟨4888842, by rfl⟩ : syracuseStep 13036913 = 9777685) B9777685
theorem B1207667 : Blo 802343 1207667 := bstep (se 1 (by rfl) ⟨905750, by rfl⟩ : syracuseStep 1207667 = 1811501) B1811501
theorem B2715011 : Blo 802343 2715011 := bstep (se 1 (by rfl) ⟨2036258, by rfl⟩ : syracuseStep 2715011 = 4072517) B4072517
theorem B1830289 : Blo 802343 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B1207697 : Blo 802343 1207697 := bstep (se 2 (by rfl) ⟨452886, by rfl⟩ : syracuseStep 1207697 = 905773) B905773
theorem B1207715 : Blo 802343 1207715 := bstep (se 1 (by rfl) ⟨905786, by rfl⟩ : syracuseStep 1207715 = 1811573) B1811573
theorem B1207745 : Blo 802343 1207745 := bstep (se 2 (by rfl) ⟨452904, by rfl⟩ : syracuseStep 1207745 = 905809) B905809
theorem B1207763 : Blo 802343 1207763 := bstep (se 1 (by rfl) ⟨905822, by rfl⟩ : syracuseStep 1207763 = 1811645) B1811645
theorem B1207793 : Blo 802343 1207793 := bstep (se 2 (by rfl) ⟨452922, by rfl⟩ : syracuseStep 1207793 = 905845) B905845
theorem B1207811 : Blo 802343 1207811 := bstep (se 1 (by rfl) ⟨905858, by rfl⟩ : syracuseStep 1207811 = 1811717) B1811717
theorem B1207841 : Blo 802343 1207841 := bstep (se 2 (by rfl) ⟨452940, by rfl⟩ : syracuseStep 1207841 = 905881) B905881
theorem B2289197 : Blo 802343 2289197 := bstep (se 3 (by rfl) ⟨429224, by rfl⟩ : syracuseStep 2289197 = 858449) B858449
theorem B1207859 : Blo 802343 1207859 := bstep (se 1 (by rfl) ⟨905894, by rfl⟩ : syracuseStep 1207859 = 1811789) B1811789
theorem B1207889 : Blo 802343 1207889 := bstep (se 2 (by rfl) ⟨452958, by rfl⟩ : syracuseStep 1207889 = 905917) B905917
theorem B1207907 : Blo 802343 1207907 := bstep (se 1 (by rfl) ⟨905930, by rfl⟩ : syracuseStep 1207907 = 1811861) B1811861
theorem B1207937 : Blo 802343 1207937 := bstep (se 2 (by rfl) ⟨452976, by rfl⟩ : syracuseStep 1207937 = 905953) B905953
theorem B2715281 : Blo 802343 2715281 := bstep (se 2 (by rfl) ⟨1018230, by rfl⟩ : syracuseStep 2715281 = 2036461) B2036461
theorem B1207955 : Blo 802343 1207955 := bstep (se 1 (by rfl) ⟨905966, by rfl⟩ : syracuseStep 1207955 = 1811933) B1811933
theorem B1207985 : Blo 802343 1207985 := bstep (se 2 (by rfl) ⟨452994, by rfl⟩ : syracuseStep 1207985 = 905989) B905989
theorem B1208003 : Blo 802343 1208003 := bstep (se 1 (by rfl) ⟨906002, by rfl⟩ : syracuseStep 1208003 = 1812005) B1812005
theorem B1208033 : Blo 802343 1208033 := bstep (se 2 (by rfl) ⟨453012, by rfl⟩ : syracuseStep 1208033 = 906025) B906025
theorem B2289379 : Blo 802343 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B1208051 : Blo 802343 1208051 := bstep (se 1 (by rfl) ⟨906038, by rfl⟩ : syracuseStep 1208051 = 1812077) B1812077
theorem B1208081 : Blo 802343 1208081 := bstep (se 2 (by rfl) ⟨453030, by rfl⟩ : syracuseStep 1208081 = 906061) B906061
theorem B1208099 : Blo 802343 1208099 := bstep (se 1 (by rfl) ⟨906074, by rfl⟩ : syracuseStep 1208099 = 1812149) B1812149
theorem B1208129 : Blo 802343 1208129 := bstep (se 2 (by rfl) ⟨453048, by rfl⟩ : syracuseStep 1208129 = 906097) B906097
theorem B1208147 : Blo 802343 1208147 := bstep (se 1 (by rfl) ⟨906110, by rfl⟩ : syracuseStep 1208147 = 1812221) B1812221
theorem B1208177 : Blo 802343 1208177 := bstep (se 2 (by rfl) ⟨453066, by rfl⟩ : syracuseStep 1208177 = 906133) B906133
theorem B2289539 : Blo 802343 2289539 := bstep (se 1 (by rfl) ⟨1717154, by rfl⟩ : syracuseStep 2289539 = 3434309) B3434309
theorem B1208195 : Blo 802343 1208195 := bstep (se 1 (by rfl) ⟨906146, by rfl⟩ : syracuseStep 1208195 = 1812293) B1812293
theorem B1208225 : Blo 802343 1208225 := bstep (se 2 (by rfl) ⟨453084, by rfl⟩ : syracuseStep 1208225 = 906169) B906169
theorem B1208243 : Blo 802343 1208243 := bstep (se 1 (by rfl) ⟨906182, by rfl⟩ : syracuseStep 1208243 = 1812365) B1812365
theorem B1208273 : Blo 802343 1208273 := bstep (se 2 (by rfl) ⟨453102, by rfl⟩ : syracuseStep 1208273 = 906205) B906205
theorem B1142753 : Blo 802343 1142753 := bstep (se 2 (by rfl) ⟨428532, by rfl⟩ : syracuseStep 1142753 = 857065) B857065
theorem B3665891 : Blo 802343 3665891 := bstep (se 1 (by rfl) ⟨2749418, by rfl⟩ : syracuseStep 3665891 = 5498837) B5498837
theorem B1208291 : Blo 802343 1208291 := bstep (se 1 (by rfl) ⟨906218, by rfl⟩ : syracuseStep 1208291 = 1812437) B1812437
theorem B1208321 : Blo 802343 1208321 := bstep (se 2 (by rfl) ⟨453120, by rfl⟩ : syracuseStep 1208321 = 906241) B906241
theorem B1208339 : Blo 802343 1208339 := bstep (se 1 (by rfl) ⟨906254, by rfl⟩ : syracuseStep 1208339 = 1812509) B1812509
theorem B1208369 : Blo 802343 1208369 := bstep (se 2 (by rfl) ⟨453138, by rfl⟩ : syracuseStep 1208369 = 906277) B906277
theorem B1208387 : Blo 802343 1208387 := bstep (se 1 (by rfl) ⟨906290, by rfl⟩ : syracuseStep 1208387 = 1812581) B1812581
theorem B1142867 : Blo 802343 1142867 := bstep (se 1 (by rfl) ⟨857150, by rfl⟩ : syracuseStep 1142867 = 1714301) B1714301
theorem B1208417 : Blo 802343 1208417 := bstep (se 2 (by rfl) ⟨453156, by rfl⟩ : syracuseStep 1208417 = 906313) B906313
theorem B1208435 : Blo 802343 1208435 := bstep (se 1 (by rfl) ⟨906326, by rfl⟩ : syracuseStep 1208435 = 1812653) B1812653
theorem B1208465 : Blo 802343 1208465 := bstep (se 2 (by rfl) ⟨453174, by rfl⟩ : syracuseStep 1208465 = 906349) B906349
theorem B1142947 : Blo 802343 1142947 := bstep (se 1 (by rfl) ⟨857210, by rfl⟩ : syracuseStep 1142947 = 1714421) B1714421
theorem B4583587 : Blo 802343 4583587 := bstep (se 1 (by rfl) ⟨3437690, by rfl⟩ : syracuseStep 4583587 = 6875381) B6875381
theorem B1208483 : Blo 802343 1208483 := bstep (se 1 (by rfl) ⟨906362, by rfl⟩ : syracuseStep 1208483 = 1812725) B1812725
theorem B2715821 : Blo 802343 2715821 := bstep (se 3 (by rfl) ⟨509216, by rfl⟩ : syracuseStep 2715821 = 1018433) B1018433
theorem B1208513 : Blo 802343 1208513 := bstep (se 2 (by rfl) ⟨453192, by rfl⟩ : syracuseStep 1208513 = 906385) B906385
theorem B1208531 : Blo 802343 1208531 := bstep (se 1 (by rfl) ⟨906398, by rfl⟩ : syracuseStep 1208531 = 1812797) B1812797
theorem B2715875 : Blo 802343 2715875 := bstep (se 1 (by rfl) ⟨2036906, by rfl⟩ : syracuseStep 2715875 = 4073813) B4073813
theorem B2355437 : Blo 802343 2355437 := bstep (se 3 (by rfl) ⟨441644, by rfl⟩ : syracuseStep 2355437 = 883289) B883289
theorem B1208561 : Blo 802343 1208561 := bstep (se 2 (by rfl) ⟨453210, by rfl⟩ : syracuseStep 1208561 = 906421) B906421
theorem B1208579 : Blo 802343 1208579 := bstep (se 1 (by rfl) ⟨906434, by rfl⟩ : syracuseStep 1208579 = 1812869) B1812869
theorem B1208609 : Blo 802343 1208609 := bstep (se 2 (by rfl) ⟨453228, by rfl⟩ : syracuseStep 1208609 = 906457) B906457
theorem B1208627 : Blo 802343 1208627 := bstep (se 1 (by rfl) ⟨906470, by rfl⟩ : syracuseStep 1208627 = 1812941) B1812941
theorem B1208657 : Blo 802343 1208657 := bstep (se 2 (by rfl) ⟨453246, by rfl⟩ : syracuseStep 1208657 = 906493) B906493
theorem B1208675 : Blo 802343 1208675 := bstep (se 1 (by rfl) ⟨906506, by rfl⟩ : syracuseStep 1208675 = 1813013) B1813013
theorem B1208705 : Blo 802343 1208705 := bstep (se 2 (by rfl) ⟨453264, by rfl⟩ : syracuseStep 1208705 = 906529) B906529
theorem B1208723 : Blo 802343 1208723 := bstep (se 1 (by rfl) ⟨906542, by rfl⟩ : syracuseStep 1208723 = 1813085) B1813085
theorem B1208753 : Blo 802343 1208753 := bstep (se 2 (by rfl) ⟨453282, by rfl⟩ : syracuseStep 1208753 = 906565) B906565
theorem B1208771 : Blo 802343 1208771 := bstep (se 1 (by rfl) ⟨906578, by rfl⟩ : syracuseStep 1208771 = 1813157) B1813157
theorem B1208801 : Blo 802343 1208801 := bstep (se 2 (by rfl) ⟨453300, by rfl⟩ : syracuseStep 1208801 = 906601) B906601
theorem B2716145 : Blo 802343 2716145 := bstep (se 2 (by rfl) ⟨1018554, by rfl⟩ : syracuseStep 2716145 = 2037109) B2037109
theorem B1208819 : Blo 802343 1208819 := bstep (se 1 (by rfl) ⟨906614, by rfl⟩ : syracuseStep 1208819 = 1813229) B1813229
theorem B1208849 : Blo 802343 1208849 := bstep (se 2 (by rfl) ⟨453318, by rfl⟩ : syracuseStep 1208849 = 906637) B906637
theorem B1208867 : Blo 802343 1208867 := bstep (se 1 (by rfl) ⟨906650, by rfl⟩ : syracuseStep 1208867 = 1813301) B1813301
theorem B1208897 : Blo 802343 1208897 := bstep (se 2 (by rfl) ⟨453336, by rfl⟩ : syracuseStep 1208897 = 906673) B906673
theorem B1208915 : Blo 802343 1208915 := bstep (se 1 (by rfl) ⟨906686, by rfl⟩ : syracuseStep 1208915 = 1813373) B1813373
theorem B1208945 : Blo 802343 1208945 := bstep (se 2 (by rfl) ⟨453354, by rfl⟩ : syracuseStep 1208945 = 906709) B906709
theorem B1208963 : Blo 802343 1208963 := bstep (se 1 (by rfl) ⟨906722, by rfl⟩ : syracuseStep 1208963 = 1813445) B1813445
theorem B1208993 : Blo 802343 1208993 := bstep (se 2 (by rfl) ⟨453372, by rfl⟩ : syracuseStep 1208993 = 906745) B906745
theorem B4584113 : Blo 802343 4584113 := bstep (se 2 (by rfl) ⟨1719042, by rfl⟩ : syracuseStep 4584113 = 3438085) B3438085
theorem B1209011 : Blo 802343 1209011 := bstep (se 1 (by rfl) ⟨906758, by rfl⟩ : syracuseStep 1209011 = 1813517) B1813517
theorem B1143505 : Blo 802343 1143505 := bstep (se 2 (by rfl) ⟨428814, by rfl⟩ : syracuseStep 1143505 = 857629) B857629
theorem B1209041 : Blo 802343 1209041 := bstep (se 2 (by rfl) ⟨453390, by rfl⟩ : syracuseStep 1209041 = 906781) B906781
theorem B1209059 : Blo 802343 1209059 := bstep (se 1 (by rfl) ⟨906794, by rfl⟩ : syracuseStep 1209059 = 1813589) B1813589
theorem B1209089 : Blo 802343 1209089 := bstep (se 2 (by rfl) ⟨453408, by rfl⟩ : syracuseStep 1209089 = 906817) B906817
theorem B1209107 : Blo 802343 1209107 := bstep (se 1 (by rfl) ⟨906830, by rfl⟩ : syracuseStep 1209107 = 1813661) B1813661
theorem B1209137 : Blo 802343 1209137 := bstep (se 2 (by rfl) ⟨453426, by rfl⟩ : syracuseStep 1209137 = 906853) B906853
theorem B1209155 : Blo 802343 1209155 := bstep (se 1 (by rfl) ⟨906866, by rfl⟩ : syracuseStep 1209155 = 1813733) B1813733
theorem B1209185 : Blo 802343 1209185 := bstep (se 2 (by rfl) ⟨453444, by rfl⟩ : syracuseStep 1209185 = 906889) B906889
theorem B1209203 : Blo 802343 1209203 := bstep (se 1 (by rfl) ⟨906902, by rfl⟩ : syracuseStep 1209203 = 1813805) B1813805
theorem B1209233 : Blo 802343 1209233 := bstep (se 2 (by rfl) ⟨453462, by rfl⟩ : syracuseStep 1209233 = 906925) B906925
theorem B1209251 : Blo 802343 1209251 := bstep (se 1 (by rfl) ⟨906938, by rfl⟩ : syracuseStep 1209251 = 1813877) B1813877
theorem B2290609 : Blo 802343 2290609 := bstep (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) B1717957
theorem B1209281 : Blo 802343 1209281 := bstep (se 2 (by rfl) ⟨453480, by rfl⟩ : syracuseStep 1209281 = 906961) B906961
theorem B1209299 : Blo 802343 1209299 := bstep (se 1 (by rfl) ⟨906974, by rfl⟩ : syracuseStep 1209299 = 1813949) B1813949
theorem B1209329 : Blo 802343 1209329 := bstep (se 2 (by rfl) ⟨453498, by rfl⟩ : syracuseStep 1209329 = 906997) B906997
theorem B1209347 : Blo 802343 1209347 := bstep (se 1 (by rfl) ⟨907010, by rfl⟩ : syracuseStep 1209347 = 1814021) B1814021
theorem B2716685 : Blo 802343 2716685 := bstep (se 3 (by rfl) ⟨509378, by rfl⟩ : syracuseStep 2716685 = 1018757) B1018757
theorem B1209377 : Blo 802343 1209377 := bstep (se 2 (by rfl) ⟨453516, by rfl⟩ : syracuseStep 1209377 = 907033) B907033
theorem B1209395 : Blo 802343 1209395 := bstep (se 1 (by rfl) ⟨907046, by rfl⟩ : syracuseStep 1209395 = 1814093) B1814093
theorem B2716739 : Blo 802343 2716739 := bstep (se 1 (by rfl) ⟨2037554, by rfl⟩ : syracuseStep 2716739 = 4075109) B4075109
theorem B1209425 : Blo 802343 1209425 := bstep (se 2 (by rfl) ⟨453534, by rfl⟩ : syracuseStep 1209425 = 907069) B907069
theorem B1209443 : Blo 802343 1209443 := bstep (se 1 (by rfl) ⟨907082, by rfl⟩ : syracuseStep 1209443 = 1814165) B1814165
theorem B1209473 : Blo 802343 1209473 := bstep (se 2 (by rfl) ⟨453552, by rfl⟩ : syracuseStep 1209473 = 907105) B907105
theorem B9270413 : Blo 802343 9270413 := bstep (se 3 (by rfl) ⟨1738202, by rfl⟩ : syracuseStep 9270413 = 3476405) B3476405
theorem B1209491 : Blo 802343 1209491 := bstep (se 1 (by rfl) ⟨907118, by rfl⟩ : syracuseStep 1209491 = 1814237) B1814237
theorem B2061571 : Blo 802343 2061571 := bstep (se 1 (by rfl) ⟨1546178, by rfl⟩ : syracuseStep 2061571 = 3092357) B3092357
theorem B9172277 : Blo 802343 9172277 := bstep (se 5 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 9172277 = 859901) B859901
theorem B2717009 : Blo 802343 2717009 := bstep (se 2 (by rfl) ⟨1018878, by rfl⟩ : syracuseStep 2717009 = 2037757) B2037757
theorem B1144211 : Blo 802343 1144211 := bstep (se 1 (by rfl) ⟨858158, by rfl⟩ : syracuseStep 1144211 = 1716317) B1716317
theorem B816883 : Blo 802343 816883 := bstep (se 1 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 816883 = 1225325) B1225325
theorem B2717549 : Blo 802343 2717549 := bstep (se 3 (by rfl) ⟨509540, by rfl⟩ : syracuseStep 2717549 = 1019081) B1019081
theorem B20936561 : Blo 802343 20936561 := bstep (se 2 (by rfl) ⟨7851210, by rfl⟩ : syracuseStep 20936561 = 15702421) B15702421
theorem B2717603 : Blo 802343 2717603 := bstep (se 1 (by rfl) ⟨2038202, by rfl⟩ : syracuseStep 2717603 = 4076405) B4076405
theorem B1832881 : Blo 802343 1832881 := bstep (se 2 (by rfl) ⟨687330, by rfl⟩ : syracuseStep 1832881 = 1374661) B1374661
theorem B1144849 : Blo 802343 1144849 := bstep (se 2 (by rfl) ⟨429318, by rfl⟩ : syracuseStep 1144849 = 858637) B858637
theorem B4585571 : Blo 802343 4585571 := bstep (se 1 (by rfl) ⟨3439178, by rfl⟩ : syracuseStep 4585571 = 6878357) B6878357
theorem B1144963 : Blo 802343 1144963 := bstep (se 1 (by rfl) ⟨858722, by rfl⟩ : syracuseStep 1144963 = 1717445) B1717445
theorem B2291885 : Blo 802343 2291885 := bstep (se 3 (by rfl) ⟨429728, by rfl⟩ : syracuseStep 2291885 = 859457) B859457
theorem B2717873 : Blo 802343 2717873 := bstep (se 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) B2038405
theorem B2292067 : Blo 802343 2292067 := bstep (se 1 (by rfl) ⟨1719050, by rfl⟩ : syracuseStep 2292067 = 3438101) B3438101
theorem B2750851 : Blo 802343 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B2292113 : Blo 802343 2292113 := bstep (se 2 (by rfl) ⟨859542, by rfl⟩ : syracuseStep 2292113 = 1719085) B1719085
theorem B1931779 : Blo 802343 1931779 := bstep (se 1 (by rfl) ⟨1448834, by rfl⟩ : syracuseStep 1931779 = 2897669) B2897669
theorem B1374769 : Blo 802343 1374769 := bstep (se 2 (by rfl) ⟨515538, by rfl⟩ : syracuseStep 1374769 = 1031077) B1031077
theorem B4291213 : Blo 802343 4291213 := bstep (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) B1609205
theorem B1931953 : Blo 802343 1931953 := bstep (se 2 (by rfl) ⟨724482, by rfl⟩ : syracuseStep 1931953 = 1448965) B1448965
theorem B2718413 : Blo 802343 2718413 := bstep (se 3 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 2718413 = 1019405) B1019405
theorem B5798627 : Blo 802343 5798627 := bstep (se 1 (by rfl) ⟨4348970, by rfl⟩ : syracuseStep 5798627 = 8697941) B8697941
theorem B3439331 : Blo 802343 3439331 := bstep (se 1 (by rfl) ⟨2579498, by rfl⟩ : syracuseStep 3439331 = 5158997) B5158997
theorem B2718467 : Blo 802343 2718467 := bstep (se 1 (by rfl) ⟨2038850, by rfl⟩ : syracuseStep 2718467 = 4077701) B4077701
theorem B4061987 : Blo 802343 4061987 := bstep (se 1 (by rfl) ⟨3046490, by rfl⟩ : syracuseStep 4061987 = 6092981) B6092981
theorem B7732037 : Blo 802343 7732037 := bstep (se 4 (by rfl) ⟨724878, by rfl⟩ : syracuseStep 7732037 = 1449757) B1449757
theorem B2718737 : Blo 802343 2718737 := bstep (se 2 (by rfl) ⟨1019526, by rfl⟩ : syracuseStep 2718737 = 2039053) B2039053
theorem B2751565 : Blo 802343 2751565 := bstep (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) B1031837
theorem B3767501 : Blo 802343 3767501 := bstep (se 3 (by rfl) ⟨706406, by rfl⟩ : syracuseStep 3767501 = 1412813) B1412813
theorem B1834193 : Blo 802343 1834193 := bstep (se 2 (by rfl) ⟨687822, by rfl⟩ : syracuseStep 1834193 = 1375645) B1375645
theorem B1146307 : Blo 802343 1146307 := bstep (se 1 (by rfl) ⟨859730, by rfl⟩ : syracuseStep 1146307 = 1719461) B1719461
theorem B2719277 : Blo 802343 2719277 := bstep (se 3 (by rfl) ⟨509864, by rfl⟩ : syracuseStep 2719277 = 1019729) B1019729
theorem B4062797 : Blo 802343 4062797 := bstep (se 3 (by rfl) ⟨761774, by rfl⟩ : syracuseStep 4062797 = 1523549) B1523549
theorem B1375825 : Blo 802343 1375825 := bstep (se 2 (by rfl) ⟨515934, by rfl⟩ : syracuseStep 1375825 = 1031869) B1031869
theorem B2719331 : Blo 802343 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B1015507 : Blo 802343 1015507 := bstep (se 1 (by rfl) ⟨761630, by rfl⟩ : syracuseStep 1015507 = 1523261) B1523261
theorem B2293571 : Blo 802343 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B2719601 : Blo 802343 2719601 := bstep (se 2 (by rfl) ⟨1019850, by rfl⟩ : syracuseStep 2719601 = 2039701) B2039701
theorem B4587461 : Blo 802343 4587461 := bstep (se 4 (by rfl) ⟨430074, by rfl⟩ : syracuseStep 4587461 = 860149) B860149
theorem B2031601 : Blo 802343 2031601 := bstep (se 2 (by rfl) ⟨761850, by rfl⟩ : syracuseStep 2031601 = 1523701) B1523701
theorem B1015831 : Blo 802343 1015831 := bstep (se 1 (by rfl) ⟨761873, by rfl⟩ : syracuseStep 1015831 = 1523747) B1523747
theorem B1933463 : Blo 802343 1933463 := bstep (se 1 (by rfl) ⟨1450097, by rfl⟩ : syracuseStep 1933463 = 2900195) B2900195
theorem B5505203 : Blo 802343 5505203 := bstep (se 1 (by rfl) ⟨4128902, by rfl⟩ : syracuseStep 5505203 = 8257805) B8257805
theorem B3440819 : Blo 802343 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B3047645 : Blo 802343 3047645 := bstep (se 3 (by rfl) ⟨571433, by rfl⟩ : syracuseStep 3047645 = 1142867) B1142867
theorem B3440971 : Blo 802343 3440971 := bstep (se 1 (by rfl) ⟨2580728, by rfl⟩ : syracuseStep 3440971 = 5161457) B5161457
theorem B3441041 : Blo 802343 3441041 := bstep (se 2 (by rfl) ⟨1290390, by rfl⟩ : syracuseStep 3441041 = 2580781) B2580781
theorem B10289699 : Blo 802343 10289699 := bstep (se 1 (by rfl) ⟨7717274, by rfl⟩ : syracuseStep 10289699 = 15434549) B15434549
theorem B3670721 : Blo 802343 3670721 := bstep (se 2 (by rfl) ⟨1376520, by rfl⟩ : syracuseStep 3670721 = 2753041) B2753041
theorem B1016651 : Blo 802343 1016651 := bstep (se 1 (by rfl) ⟨762488, by rfl⟩ : syracuseStep 1016651 = 1524977) B1524977
theorem B4064093 : Blo 802343 4064093 := bstep (se 3 (by rfl) ⟨762017, by rfl⟩ : syracuseStep 4064093 = 1524035) B1524035
theorem B1835891 : Blo 802343 1835891 := bstep (se 1 (by rfl) ⟨1376918, by rfl⟩ : syracuseStep 1835891 = 2753837) B2753837
theorem B11731985 : Blo 802343 11731985 := bstep (se 2 (by rfl) ⟨4399494, by rfl⟩ : syracuseStep 11731985 = 8798989) B8798989
theorem B29295685 : Blo 802343 29295685 := bstep (se 4 (by rfl) ⟨2746470, by rfl⟩ : syracuseStep 29295685 = 5492941) B5492941
theorem B2032715 : Blo 802343 2032715 := bstep (se 1 (by rfl) ⟨1524536, by rfl⟩ : syracuseStep 2032715 = 3049073) B3049073
theorem B2720843 : Blo 802343 2720843 := bstep (se 1 (by rfl) ⟨2040632, by rfl⟩ : syracuseStep 2720843 = 4081265) B4081265
theorem B6980825 : Blo 802343 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B2721113 : Blo 802343 2721113 := bstep (se 2 (by rfl) ⟨1020417, by rfl⟩ : syracuseStep 2721113 = 2040835) B2040835
theorem B1017355 : Blo 802343 1017355 := bstep (se 1 (by rfl) ⟨763016, by rfl⟩ : syracuseStep 1017355 = 1526033) B1526033
theorem B9176651 : Blo 802343 9176651 := bstep (se 1 (by rfl) ⟨6882488, by rfl⟩ : syracuseStep 9176651 = 13764977) B13764977
theorem B2295371 : Blo 802343 2295371 := bstep (se 1 (by rfl) ⟨1721528, by rfl⟩ : syracuseStep 2295371 = 3443057) B3443057
theorem B1017623 : Blo 802343 1017623 := bstep (se 1 (by rfl) ⟨763217, by rfl⟩ : syracuseStep 1017623 = 1526435) B1526435
theorem B3770371 : Blo 802343 3770371 := bstep (se 1 (by rfl) ⟨2827778, by rfl⟩ : syracuseStep 3770371 = 5655557) B5655557
theorem B2033687 : Blo 802343 2033687 := bstep (se 1 (by rfl) ⟨1525265, by rfl⟩ : syracuseStep 2033687 = 3050531) B3050531
theorem B5802029 : Blo 802343 5802029 := bstep (se 3 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 5802029 = 2175761) B2175761
theorem B3442733 : Blo 802343 3442733 := bstep (se 3 (by rfl) ⟨645512, by rfl⟩ : syracuseStep 3442733 = 1291025) B1291025
theorem B5507459 : Blo 802343 5507459 := bstep (se 1 (by rfl) ⟨4130594, by rfl⟩ : syracuseStep 5507459 = 8261189) B8261189
theorem B1018327 : Blo 802343 1018327 := bstep (se 1 (by rfl) ⟨763745, by rfl⟩ : syracuseStep 1018327 = 1527491) B1527491
theorem B1018391 : Blo 802343 1018391 := bstep (se 1 (by rfl) ⟨763793, by rfl⟩ : syracuseStep 1018391 = 1527587) B1527587
theorem B2034355 : Blo 802343 2034355 := bstep (se 1 (by rfl) ⟨1525766, by rfl⟩ : syracuseStep 2034355 = 3051533) B3051533
theorem B3443417 : Blo 802343 3443417 := bstep (se 2 (by rfl) ⟨1291281, by rfl⟩ : syracuseStep 3443417 = 2582563) B2582563
theorem B3050243 : Blo 802343 3050243 := bstep (se 1 (by rfl) ⟨2287682, by rfl⟩ : syracuseStep 3050243 = 4575365) B4575365
theorem B3050257 : Blo 802343 3050257 := bstep (se 2 (by rfl) ⟨1143846, by rfl⟩ : syracuseStep 3050257 = 2287693) B2287693
theorem B2034497 : Blo 802343 2034497 := bstep (se 2 (by rfl) ⟨762936, by rfl⟩ : syracuseStep 2034497 = 1525873) B1525873
theorem B4066199 : Blo 802343 4066199 := bstep (se 1 (by rfl) ⟨3049649, by rfl⟩ : syracuseStep 4066199 = 6099299) B6099299
theorem B6097841 : Blo 802343 6097841 := bstep (se 2 (by rfl) ⟨2286690, by rfl⟩ : syracuseStep 6097841 = 4573381) B4573381
theorem B1805273 : Blo 802343 1805273 := bstep (se 2 (by rfl) ⟨676977, by rfl⟩ : syracuseStep 1805273 = 1353955) B1353955
theorem B1805363 : Blo 802343 1805363 := bstep (se 1 (by rfl) ⟨1354022, by rfl⟩ : syracuseStep 1805363 = 2708045) B2708045
theorem B3050561 : Blo 802343 3050561 := bstep (se 2 (by rfl) ⟨1143960, by rfl⟩ : syracuseStep 3050561 = 2287921) B2287921
theorem B1805399 : Blo 802343 1805399 := bstep (se 1 (by rfl) ⟨1354049, by rfl⟩ : syracuseStep 1805399 = 2708099) B2708099
theorem B1805579 : Blo 802343 1805579 := bstep (se 1 (by rfl) ⟨1354184, by rfl⟩ : syracuseStep 1805579 = 2708369) B2708369
theorem B1805633 : Blo 802343 1805633 := bstep (se 2 (by rfl) ⟨677112, by rfl⟩ : syracuseStep 1805633 = 1354225) B1354225
theorem B6098327 : Blo 802343 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B1805849 : Blo 802343 1805849 := bstep (se 2 (by rfl) ⟨677193, by rfl⟩ : syracuseStep 1805849 = 1354387) B1354387
theorem B1805939 : Blo 802343 1805939 := bstep (se 1 (by rfl) ⟨1354454, by rfl⟩ : syracuseStep 1805939 = 2708909) B2708909
theorem B1805975 : Blo 802343 1805975 := bstep (se 1 (by rfl) ⟨1354481, by rfl⟩ : syracuseStep 1805975 = 2708963) B2708963
theorem B1937047 : Blo 802343 1937047 := bstep (se 1 (by rfl) ⟨1452785, by rfl⟩ : syracuseStep 1937047 = 2905571) B2905571
theorem B1838809 : Blo 802343 1838809 := bstep (se 2 (by rfl) ⟨689553, by rfl⟩ : syracuseStep 1838809 = 1379107) B1379107
theorem B3051229 : Blo 802343 3051229 := bstep (se 3 (by rfl) ⟨572105, by rfl⟩ : syracuseStep 3051229 = 1144211) B1144211
theorem B1806155 : Blo 802343 1806155 := bstep (se 1 (by rfl) ⟨1354616, by rfl⟩ : syracuseStep 1806155 = 2709233) B2709233
theorem B1806209 : Blo 802343 1806209 := bstep (se 2 (by rfl) ⟨677328, by rfl⟩ : syracuseStep 1806209 = 1354657) B1354657
theorem B2035763 : Blo 802343 2035763 := bstep (se 1 (by rfl) ⟨1526822, by rfl⟩ : syracuseStep 2035763 = 3053645) B3053645
theorem B3870785 : Blo 802343 3870785 := bstep (se 2 (by rfl) ⟨1451544, by rfl⟩ : syracuseStep 3870785 = 2903089) B2903089
theorem B1806425 : Blo 802343 1806425 := bstep (se 2 (by rfl) ⟨677409, by rfl⟩ : syracuseStep 1806425 = 1354819) B1354819
theorem B1020043 : Blo 802343 1020043 := bstep (se 1 (by rfl) ⟨765032, by rfl⟩ : syracuseStep 1020043 = 1530065) B1530065
theorem B1806515 : Blo 802343 1806515 := bstep (se 1 (by rfl) ⟨1354886, by rfl⟩ : syracuseStep 1806515 = 2709773) B2709773
theorem B1806551 : Blo 802343 1806551 := bstep (se 1 (by rfl) ⟨1354913, by rfl⟩ : syracuseStep 1806551 = 2709827) B2709827
theorem B1085783 : Blo 802343 1085783 := bstep (se 1 (by rfl) ⟨814337, by rfl⟩ : syracuseStep 1085783 = 1628675) B1628675
theorem B1806731 : Blo 802343 1806731 := bstep (se 1 (by rfl) ⟨1355048, by rfl⟩ : syracuseStep 1806731 = 2710097) B2710097
theorem B1544599 : Blo 802343 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B1806785 : Blo 802343 1806785 := bstep (se 2 (by rfl) ⟨677544, by rfl⟩ : syracuseStep 1806785 = 1355089) B1355089
theorem B2036299 : Blo 802343 2036299 := bstep (se 1 (by rfl) ⟨1527224, by rfl⟩ : syracuseStep 2036299 = 3054449) B3054449
theorem B1807001 : Blo 802343 1807001 := bstep (se 2 (by rfl) ⟨677625, by rfl⟩ : syracuseStep 1807001 = 1355251) B1355251
theorem B2036441 : Blo 802343 2036441 := bstep (se 2 (by rfl) ⟨763665, by rfl⟩ : syracuseStep 2036441 = 1527331) B1527331
theorem B1807091 : Blo 802343 1807091 := bstep (se 1 (by rfl) ⟨1355318, by rfl⟩ : syracuseStep 1807091 = 2710637) B2710637
theorem B1807127 : Blo 802343 1807127 := bstep (se 1 (by rfl) ⟨1355345, by rfl⟩ : syracuseStep 1807127 = 2710691) B2710691
theorem B1807307 : Blo 802343 1807307 := bstep (se 1 (by rfl) ⟨1355480, by rfl⟩ : syracuseStep 1807307 = 2710961) B2710961
theorem B2200537 : Blo 802343 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B3052505 : Blo 802343 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B1807361 : Blo 802343 1807361 := bstep (se 2 (by rfl) ⟨677760, by rfl⟩ : syracuseStep 1807361 = 1355521) B1355521
theorem B857099 : Blo 802343 857099 := bstep (se 1 (by rfl) ⟨642824, by rfl⟩ : syracuseStep 857099 = 1285649) B1285649
theorem B1807577 : Blo 802343 1807577 := bstep (se 2 (by rfl) ⟨677841, by rfl⟩ : syracuseStep 1807577 = 1355683) B1355683
theorem B1807667 : Blo 802343 1807667 := bstep (se 1 (by rfl) ⟨1355750, by rfl⟩ : syracuseStep 1807667 = 2711501) B2711501
theorem B1807703 : Blo 802343 1807703 := bstep (se 1 (by rfl) ⟨1355777, by rfl⟩ : syracuseStep 1807703 = 2711555) B2711555
theorem B1742231 : Blo 802343 1742231 := bstep (se 1 (by rfl) ⟨1306673, by rfl⟩ : syracuseStep 1742231 = 2613347) B2613347
theorem B1807883 : Blo 802343 1807883 := bstep (se 1 (by rfl) ⟨1355912, by rfl⟩ : syracuseStep 1807883 = 2711825) B2711825
theorem B2037271 : Blo 802343 2037271 := bstep (se 1 (by rfl) ⟨1527953, by rfl⟩ : syracuseStep 2037271 = 3055907) B3055907
theorem B1807937 : Blo 802343 1807937 := bstep (se 2 (by rfl) ⟨677976, by rfl⟩ : syracuseStep 1807937 = 1355953) B1355953
theorem B1808153 : Blo 802343 1808153 := bstep (se 2 (by rfl) ⟨678057, by rfl⟩ : syracuseStep 1808153 = 1356115) B1356115
theorem B1808243 : Blo 802343 1808243 := bstep (se 1 (by rfl) ⟨1356182, by rfl⟩ : syracuseStep 1808243 = 2712365) B2712365
theorem B1808279 : Blo 802343 1808279 := bstep (se 1 (by rfl) ⟨1356209, by rfl⟩ : syracuseStep 1808279 = 2712419) B2712419
theorem B25499569 : Blo 802343 25499569 := bstep (se 2 (by rfl) ⟨9562338, by rfl⟩ : syracuseStep 25499569 = 19124677) B19124677
theorem B2037707 : Blo 802343 2037707 := bstep (se 1 (by rfl) ⟨1528280, by rfl⟩ : syracuseStep 2037707 = 3056561) B3056561
theorem B3872785 : Blo 802343 3872785 := bstep (se 2 (by rfl) ⟨1452294, by rfl⟩ : syracuseStep 3872785 = 2904589) B2904589
theorem B1808459 : Blo 802343 1808459 := bstep (se 1 (by rfl) ⟨1356344, by rfl⟩ : syracuseStep 1808459 = 2712689) B2712689
theorem B1808513 : Blo 802343 1808513 := bstep (se 2 (by rfl) ⟨678192, by rfl⟩ : syracuseStep 1808513 = 1356385) B1356385
theorem B858295 : Blo 802343 858295 := bstep (se 1 (by rfl) ⟨643721, by rfl⟩ : syracuseStep 858295 = 1287443) B1287443
theorem B2038081 : Blo 802343 2038081 := bstep (se 2 (by rfl) ⟨764280, by rfl⟩ : syracuseStep 2038081 = 1528561) B1528561
theorem B1808729 : Blo 802343 1808729 := bstep (se 2 (by rfl) ⟨678273, by rfl⟩ : syracuseStep 1808729 = 1356547) B1356547
theorem B858475 : Blo 802343 858475 := bstep (se 1 (by rfl) ⟨643856, by rfl⟩ : syracuseStep 858475 = 1287713) B1287713
theorem B4069763 : Blo 802343 4069763 := bstep (se 1 (by rfl) ⟨3052322, by rfl⟩ : syracuseStep 4069763 = 6104645) B6104645
theorem B1808819 : Blo 802343 1808819 := bstep (se 1 (by rfl) ⟨1356614, by rfl⟩ : syracuseStep 1808819 = 2713229) B2713229
theorem B1808855 : Blo 802343 1808855 := bstep (se 1 (by rfl) ⟨1356641, by rfl⟩ : syracuseStep 1808855 = 2713283) B2713283
theorem B3054131 : Blo 802343 3054131 := bstep (se 1 (by rfl) ⟨2290598, by rfl⟩ : syracuseStep 3054131 = 4581197) B4581197
theorem B3054145 : Blo 802343 3054145 := bstep (se 2 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 3054145 = 2290609) B2290609
theorem B7740035 : Blo 802343 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B1809035 : Blo 802343 1809035 := bstep (se 1 (by rfl) ⟨1356776, by rfl⟩ : syracuseStep 1809035 = 2713553) B2713553
theorem B1809089 : Blo 802343 1809089 := bstep (se 2 (by rfl) ⟨678408, by rfl⟩ : syracuseStep 1809089 = 1356817) B1356817
theorem B2038679 : Blo 802343 2038679 := bstep (se 1 (by rfl) ⟨1529009, by rfl⟩ : syracuseStep 2038679 = 3058019) B3058019
theorem B1809305 : Blo 802343 1809305 := bstep (se 2 (by rfl) ⟨678489, by rfl⟩ : syracuseStep 1809305 = 1356979) B1356979
theorem B1809395 : Blo 802343 1809395 := bstep (se 1 (by rfl) ⟨1357046, by rfl⟩ : syracuseStep 1809395 = 2714093) B2714093
theorem B1809431 : Blo 802343 1809431 := bstep (se 1 (by rfl) ⟨1357073, by rfl⟩ : syracuseStep 1809431 = 2714147) B2714147
theorem B1809611 : Blo 802343 1809611 := bstep (se 1 (by rfl) ⟨1357208, by rfl⟩ : syracuseStep 1809611 = 2714417) B2714417
theorem B1809665 : Blo 802343 1809665 := bstep (se 2 (by rfl) ⟨678624, by rfl⟩ : syracuseStep 1809665 = 1357249) B1357249
theorem B1809881 : Blo 802343 1809881 := bstep (se 2 (by rfl) ⟨678705, by rfl⟩ : syracuseStep 1809881 = 1357411) B1357411
theorem B6626861 : Blo 802343 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B1809971 : Blo 802343 1809971 := bstep (se 1 (by rfl) ⟨1357478, by rfl⟩ : syracuseStep 1809971 = 2714957) B2714957
theorem B8691275 : Blo 802343 8691275 := bstep (se 1 (by rfl) ⟨6518456, by rfl⟩ : syracuseStep 8691275 = 13036913) B13036913
theorem B1810007 : Blo 802343 1810007 := bstep (se 1 (by rfl) ⟨1357505, by rfl⟩ : syracuseStep 1810007 = 2715011) B2715011
theorem B2039489 : Blo 802343 2039489 := bstep (se 2 (by rfl) ⟨764808, by rfl⟩ : syracuseStep 2039489 = 1529617) B1529617
theorem B1810187 : Blo 802343 1810187 := bstep (se 1 (by rfl) ⟨1357640, by rfl⟩ : syracuseStep 1810187 = 2715281) B2715281
theorem B1449751 : Blo 802343 1449751 := bstep (se 1 (by rfl) ⟨1087313, by rfl⟩ : syracuseStep 1449751 = 2174627) B2174627
theorem B1810241 : Blo 802343 1810241 := bstep (se 2 (by rfl) ⟨678840, by rfl⟩ : syracuseStep 1810241 = 1357681) B1357681
theorem B1810457 : Blo 802343 1810457 := bstep (se 2 (by rfl) ⟨678921, by rfl⟩ : syracuseStep 1810457 = 1357843) B1357843
theorem B1810547 : Blo 802343 1810547 := bstep (se 1 (by rfl) ⟨1357910, by rfl⟩ : syracuseStep 1810547 = 2715821) B2715821
theorem B1810583 : Blo 802343 1810583 := bstep (se 1 (by rfl) ⟨1357937, by rfl⟩ : syracuseStep 1810583 = 2715875) B2715875
theorem B2040025 : Blo 802343 2040025 := bstep (se 2 (by rfl) ⟨765009, by rfl⟩ : syracuseStep 2040025 = 1530019) B1530019
theorem B1810763 : Blo 802343 1810763 := bstep (se 1 (by rfl) ⟨1358072, by rfl⟩ : syracuseStep 1810763 = 2716145) B2716145
theorem B860491 : Blo 802343 860491 := bstep (se 1 (by rfl) ⟨645368, by rfl⟩ : syracuseStep 860491 = 1290737) B1290737
theorem B5808485 : Blo 802343 5808485 := bstep (se 4 (by rfl) ⟨544545, by rfl⟩ : syracuseStep 5808485 = 1089091) B1089091
theorem B1810817 : Blo 802343 1810817 := bstep (se 2 (by rfl) ⟨679056, by rfl⟩ : syracuseStep 1810817 = 1358113) B1358113
theorem B3056075 : Blo 802343 3056075 := bstep (se 1 (by rfl) ⟨2292056, by rfl⟩ : syracuseStep 3056075 = 4584113) B4584113
theorem B1286617 : Blo 802343 1286617 := bstep (se 2 (by rfl) ⟨482481, by rfl⟩ : syracuseStep 1286617 = 964963) B964963
theorem B3056089 : Blo 802343 3056089 := bstep (se 2 (by rfl) ⟨1146033, by rfl⟩ : syracuseStep 3056089 = 2292067) B2292067
theorem B1811033 : Blo 802343 1811033 := bstep (se 2 (by rfl) ⟨679137, by rfl⟩ : syracuseStep 1811033 = 1358275) B1358275
theorem B1811123 : Blo 802343 1811123 := bstep (se 1 (by rfl) ⟨1358342, by rfl⟩ : syracuseStep 1811123 = 2716685) B2716685
theorem B1811159 : Blo 802343 1811159 := bstep (se 1 (by rfl) ⟨1358369, by rfl⟩ : syracuseStep 1811159 = 2716739) B2716739
theorem B1811339 : Blo 802343 1811339 := bstep (se 1 (by rfl) ⟨1358504, by rfl⟩ : syracuseStep 1811339 = 2717009) B2717009
theorem B1811393 : Blo 802343 1811393 := bstep (se 2 (by rfl) ⟨679272, by rfl⟩ : syracuseStep 1811393 = 1358545) B1358545
theorem B7349399 : Blo 802343 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B1811609 : Blo 802343 1811609 := bstep (se 2 (by rfl) ⟨679353, by rfl⟩ : syracuseStep 1811609 = 1358707) B1358707
theorem B223323317 : Blo 802343 223323317 := bstep (se 5 (by rfl) ⟨10468280, by rfl⟩ : syracuseStep 223323317 = 20936561) B20936561
theorem B1811699 : Blo 802343 1811699 := bstep (se 1 (by rfl) ⟨1358774, by rfl⟩ : syracuseStep 1811699 = 2717549) B2717549
theorem B1811735 : Blo 802343 1811735 := bstep (se 1 (by rfl) ⟨1358801, by rfl⟩ : syracuseStep 1811735 = 2717603) B2717603
theorem B3057047 : Blo 802343 3057047 := bstep (se 1 (by rfl) ⟨2292785, by rfl⟩ : syracuseStep 3057047 = 4585571) B4585571
theorem B1811915 : Blo 802343 1811915 := bstep (se 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) B2717873
theorem B1811969 : Blo 802343 1811969 := bstep (se 2 (by rfl) ⟨679488, by rfl⟩ : syracuseStep 1811969 = 1358977) B1358977
theorem B1812185 : Blo 802343 1812185 := bstep (se 2 (by rfl) ⟨679569, by rfl⟩ : syracuseStep 1812185 = 1359139) B1359139
theorem B1812275 : Blo 802343 1812275 := bstep (se 1 (by rfl) ⟨1359206, by rfl⟩ : syracuseStep 1812275 = 2718413) B2718413
theorem B1812311 : Blo 802343 1812311 := bstep (se 1 (by rfl) ⟨1359233, by rfl⟩ : syracuseStep 1812311 = 2718467) B2718467
theorem B1451891 : Blo 802343 1451891 := bstep (se 1 (by rfl) ⟨1088918, by rfl⟩ : syracuseStep 1451891 = 2177837) B2177837
theorem B5154691 : Blo 802343 5154691 := bstep (se 1 (by rfl) ⟨3866018, by rfl⟩ : syracuseStep 5154691 = 7732037) B7732037
theorem B1812491 : Blo 802343 1812491 := bstep (se 1 (by rfl) ⟨1359368, by rfl⟩ : syracuseStep 1812491 = 2718737) B2718737
theorem B4073489 : Blo 802343 4073489 := bstep (se 2 (by rfl) ⟨1527558, by rfl⟩ : syracuseStep 4073489 = 3055117) B3055117
theorem B1812545 : Blo 802343 1812545 := bstep (se 2 (by rfl) ⟨679704, by rfl⟩ : syracuseStep 1812545 = 1359409) B1359409
theorem B1222795 : Blo 802343 1222795 := bstep (se 1 (by rfl) ⟨917096, by rfl⟩ : syracuseStep 1222795 = 1834193) B1834193
theorem B3254417 : Blo 802343 3254417 := bstep (se 2 (by rfl) ⟨1220406, by rfl⟩ : syracuseStep 3254417 = 2440813) B2440813
theorem B4073651 : Blo 802343 4073651 := bstep (se 1 (by rfl) ⟨3055238, by rfl⟩ : syracuseStep 4073651 = 6110477) B6110477
theorem B1354009 : Blo 802343 1354009 := bstep (se 2 (by rfl) ⟨507753, by rfl⟩ : syracuseStep 1354009 = 1015507) B1015507
theorem B1812761 : Blo 802343 1812761 := bstep (se 2 (by rfl) ⟨679785, by rfl⟩ : syracuseStep 1812761 = 1359571) B1359571
theorem B46999921 : Blo 802343 46999921 := bstep (se 2 (by rfl) ⟨17624970, by rfl⟩ : syracuseStep 46999921 = 35249941) B35249941
theorem B1812851 : Blo 802343 1812851 := bstep (se 1 (by rfl) ⟨1359638, by rfl⟩ : syracuseStep 1812851 = 2719277) B2719277
theorem B1812887 : Blo 802343 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B1452439 : Blo 802343 1452439 := bstep (se 1 (by rfl) ⟨1089329, by rfl⟩ : syracuseStep 1452439 = 2178659) B2178659
theorem B6105617 : Blo 802343 6105617 := bstep (se 2 (by rfl) ⟨2289606, by rfl⟩ : syracuseStep 6105617 = 4579213) B4579213
theorem B1714711 : Blo 802343 1714711 := bstep (se 1 (by rfl) ⟨1286033, by rfl⟩ : syracuseStep 1714711 = 2572067) B2572067
theorem B1714763 : Blo 802343 1714763 := bstep (se 1 (by rfl) ⟨1286072, by rfl⟩ : syracuseStep 1714763 = 2572145) B2572145
theorem B1813067 : Blo 802343 1813067 := bstep (se 1 (by rfl) ⟨1359800, by rfl⟩ : syracuseStep 1813067 = 2719601) B2719601
theorem B1813121 : Blo 802343 1813121 := bstep (se 2 (by rfl) ⟨679920, by rfl⟩ : syracuseStep 1813121 = 1359841) B1359841
theorem B3058307 : Blo 802343 3058307 := bstep (se 1 (by rfl) ⟨2293730, by rfl⟩ : syracuseStep 3058307 = 4587461) B4587461
theorem B1288921 : Blo 802343 1288921 := bstep (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) B966691
theorem B6859525 : Blo 802343 6859525 := bstep (se 4 (by rfl) ⟨643080, by rfl⟩ : syracuseStep 6859525 = 1286161) B1286161
theorem B57256769 : Blo 802343 57256769 := bstep (se 2 (by rfl) ⟨21471288, by rfl⟩ : syracuseStep 57256769 = 42942577) B42942577
theorem B1354583 : Blo 802343 1354583 := bstep (se 1 (by rfl) ⟨1015937, by rfl⟩ : syracuseStep 1354583 = 2031875) B2031875
theorem B1813337 : Blo 802343 1813337 := bstep (se 2 (by rfl) ⟨680001, by rfl⟩ : syracuseStep 1813337 = 1360003) B1360003
theorem B3910493 : Blo 802343 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B1813427 : Blo 802343 1813427 := bstep (se 1 (by rfl) ⟨1360070, by rfl⟩ : syracuseStep 1813427 = 2720141) B2720141
theorem B1354711 : Blo 802343 1354711 := bstep (se 1 (by rfl) ⟨1016033, by rfl⟩ : syracuseStep 1354711 = 2032067) B2032067
theorem B1813463 : Blo 802343 1813463 := bstep (se 1 (by rfl) ⟨1360097, by rfl⟩ : syracuseStep 1813463 = 2720195) B2720195
theorem B1813643 : Blo 802343 1813643 := bstep (se 1 (by rfl) ⟨1360232, by rfl⟩ : syracuseStep 1813643 = 2720465) B2720465
theorem B3714221 : Blo 802343 3714221 := bstep (se 3 (by rfl) ⟨696416, by rfl⟩ : syracuseStep 3714221 = 1392833) B1392833
theorem B1813697 : Blo 802343 1813697 := bstep (se 2 (by rfl) ⟨680136, by rfl⟩ : syracuseStep 1813697 = 1360273) B1360273
theorem B1813913 : Blo 802343 1813913 := bstep (se 2 (by rfl) ⟨680217, by rfl⟩ : syracuseStep 1813913 = 1360435) B1360435
theorem B1814003 : Blo 802343 1814003 := bstep (se 1 (by rfl) ⟨1360502, by rfl⟩ : syracuseStep 1814003 = 2721005) B2721005
theorem B1814039 : Blo 802343 1814039 := bstep (se 1 (by rfl) ⟨1360529, by rfl⟩ : syracuseStep 1814039 = 2721059) B2721059
theorem B1355339 : Blo 802343 1355339 := bstep (se 1 (by rfl) ⟨1016504, by rfl⟩ : syracuseStep 1355339 = 2033009) B2033009
theorem B1355467 : Blo 802343 1355467 := bstep (se 1 (by rfl) ⟨1016600, by rfl⟩ : syracuseStep 1355467 = 2033201) B2033201
theorem B1814219 : Blo 802343 1814219 := bstep (se 1 (by rfl) ⟨1360664, by rfl⟩ : syracuseStep 1814219 = 2721329) B2721329
theorem B2895581 : Blo 802343 2895581 := bstep (se 3 (by rfl) ⟨542921, by rfl⟩ : syracuseStep 2895581 = 1085843) B1085843
theorem B1814273 : Blo 802343 1814273 := bstep (se 2 (by rfl) ⟨680352, by rfl⟩ : syracuseStep 1814273 = 1360705) B1360705
theorem B1355609 : Blo 802343 1355609 := bstep (se 2 (by rfl) ⟨508353, by rfl⟩ : syracuseStep 1355609 = 1016707) B1016707
theorem B1355737 : Blo 802343 1355737 := bstep (se 2 (by rfl) ⟨508401, by rfl⟩ : syracuseStep 1355737 = 1016803) B1016803
theorem B4075595 : Blo 802343 4075595 := bstep (se 1 (by rfl) ⟨3056696, by rfl⟩ : syracuseStep 4075595 = 6113393) B6113393
theorem B1224791 : Blo 802343 1224791 := bstep (se 1 (by rfl) ⟨918593, by rfl⟩ : syracuseStep 1224791 = 1837187) B1837187
theorem B3256409 : Blo 802343 3256409 := bstep (se 2 (by rfl) ⟨1221153, by rfl⟩ : syracuseStep 3256409 = 2442307) B2442307
theorem B1716403 : Blo 802343 1716403 := bstep (se 1 (by rfl) ⟨1287302, by rfl⟩ : syracuseStep 1716403 = 2574605) B2574605
theorem B1814731 : Blo 802343 1814731 := bstep (se 1 (by rfl) ⟨1361048, by rfl⟩ : syracuseStep 1814731 = 2722097) B2722097
theorem B1290583 : Blo 802343 1290583 := bstep (se 1 (by rfl) ⟨967937, by rfl⟩ : syracuseStep 1290583 = 1935875) B1935875
theorem B1290647 : Blo 802343 1290647 := bstep (se 1 (by rfl) ⟨967985, by rfl⟩ : syracuseStep 1290647 = 1935971) B1935971
theorem B1356311 : Blo 802343 1356311 := bstep (se 1 (by rfl) ⟨1017233, by rfl⟩ : syracuseStep 1356311 = 2034467) B2034467
theorem B1716761 : Blo 802343 1716761 := bstep (se 2 (by rfl) ⟨643785, by rfl⟩ : syracuseStep 1716761 = 1287571) B1287571
theorem B1356439 : Blo 802343 1356439 := bstep (se 1 (by rfl) ⟨1017329, by rfl⟩ : syracuseStep 1356439 = 2034659) B2034659
theorem B1291211 : Blo 802343 1291211 := bstep (se 1 (by rfl) ⟨968408, by rfl⟩ : syracuseStep 1291211 = 1936817) B1936817
theorem B1160281 : Blo 802343 1160281 := bstep (se 2 (by rfl) ⟨435105, by rfl⟩ : syracuseStep 1160281 = 870211) B870211
theorem B1291403 : Blo 802343 1291403 := bstep (se 1 (by rfl) ⟨968552, by rfl⟩ : syracuseStep 1291403 = 1937105) B1937105
theorem B2176217 : Blo 802343 2176217 := bstep (se 2 (by rfl) ⟨816081, by rfl⟩ : syracuseStep 2176217 = 1632163) B1632163
theorem B1357067 : Blo 802343 1357067 := bstep (se 1 (by rfl) ⟨1017800, by rfl⟩ : syracuseStep 1357067 = 2035601) B2035601
theorem B10302821 : Blo 802343 10302821 := bstep (se 4 (by rfl) ⟨965889, by rfl⟩ : syracuseStep 10302821 = 1931779) B1931779
theorem B1357195 : Blo 802343 1357195 := bstep (se 1 (by rfl) ⟨1017896, by rfl⟩ : syracuseStep 1357195 = 2035793) B2035793
theorem B6862259 : Blo 802343 6862259 := bstep (se 1 (by rfl) ⟨5146694, by rfl⟩ : syracuseStep 6862259 = 10293389) B10293389
theorem B1357337 : Blo 802343 1357337 := bstep (se 2 (by rfl) ⟨509001, by rfl⟩ : syracuseStep 1357337 = 1018003) B1018003
theorem B1357465 : Blo 802343 1357465 := bstep (se 2 (by rfl) ⟨509049, by rfl⟩ : syracuseStep 1357465 = 1018099) B1018099
theorem B3061421 : Blo 802343 3061421 := bstep (se 3 (by rfl) ⟨574016, by rfl⟩ : syracuseStep 3061421 = 1148033) B1148033
theorem B4077377 : Blo 802343 4077377 := bstep (se 2 (by rfl) ⟨1529016, by rfl⟩ : syracuseStep 4077377 = 3058033) B3058033
theorem B4339757 : Blo 802343 4339757 := bstep (se 3 (by rfl) ⟨813704, by rfl⟩ : syracuseStep 4339757 = 1627409) B1627409
theorem B39172247 : Blo 802343 39172247 := bstep (se 1 (by rfl) ⟨29379185, by rfl⟩ : syracuseStep 39172247 = 58758371) B58758371
theorem B1358039 : Blo 802343 1358039 := bstep (se 1 (by rfl) ⟨1018529, by rfl⟩ : syracuseStep 1358039 = 2037059) B2037059
theorem B6109505 : Blo 802343 6109505 := bstep (se 2 (by rfl) ⟨2291064, by rfl⟩ : syracuseStep 6109505 = 4582129) B4582129
theorem B1358167 : Blo 802343 1358167 := bstep (se 1 (by rfl) ⟨1018625, by rfl⟩ : syracuseStep 1358167 = 2037251) B2037251
theorem B1489291 : Blo 802343 1489291 := bstep (se 1 (by rfl) ⟨1116968, by rfl⟩ : syracuseStep 1489291 = 2233937) B2233937
theorem B1718795 : Blo 802343 1718795 := bstep (se 1 (by rfl) ⟨1289096, by rfl⟩ : syracuseStep 1718795 = 2578193) B2578193
theorem B44022365 : Blo 802343 44022365 := bstep (se 3 (by rfl) ⟨8254193, by rfl⟩ : syracuseStep 44022365 = 16508387) B16508387
theorem B1489817 : Blo 802343 1489817 := bstep (se 2 (by rfl) ⟨558681, by rfl⟩ : syracuseStep 1489817 = 1117363) B1117363
theorem B2898881 : Blo 802343 2898881 := bstep (se 2 (by rfl) ⟨1087080, by rfl⟩ : syracuseStep 2898881 = 2174161) B2174161
theorem B1358795 : Blo 802343 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B1358923 : Blo 802343 1358923 := bstep (se 1 (by rfl) ⟨1019192, by rfl⟩ : syracuseStep 1358923 = 2038385) B2038385
theorem B2440385 : Blo 802343 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B1359065 : Blo 802343 1359065 := bstep (se 2 (by rfl) ⟨509649, by rfl⟩ : syracuseStep 1359065 = 1019299) B1019299
theorem B6864173 : Blo 802343 6864173 := bstep (se 3 (by rfl) ⟨1287032, by rfl⟩ : syracuseStep 6864173 = 2574065) B2574065
theorem B1359193 : Blo 802343 1359193 := bstep (se 2 (by rfl) ⟨509697, by rfl⟩ : syracuseStep 1359193 = 1019395) B1019395
theorem B3259865 : Blo 802343 3259865 := bstep (se 2 (by rfl) ⟨1222449, by rfl⟩ : syracuseStep 3259865 = 2444899) B2444899
theorem B2211293 : Blo 802343 2211293 := bstep (se 3 (by rfl) ⟨414617, by rfl⟩ : syracuseStep 2211293 = 829235) B829235
theorem B802347 : Blo 802343 802347 := bstep (se 1 (by rfl) ⟨601760, by rfl⟩ : syracuseStep 802347 = 1203521) B1203521
theorem B802359 : Blo 802343 802359 := bstep (se 1 (by rfl) ⟨601769, by rfl⟩ : syracuseStep 802359 = 1203539) B1203539
theorem B802379 : Blo 802343 802379 := bstep (se 1 (by rfl) ⟨601784, by rfl⟩ : syracuseStep 802379 = 1203569) B1203569
theorem B802391 : Blo 802343 802391 := bstep (se 1 (by rfl) ⟨601793, by rfl⟩ : syracuseStep 802391 = 1203587) B1203587
theorem B802411 : Blo 802343 802411 := bstep (se 1 (by rfl) ⟨601808, by rfl⟩ : syracuseStep 802411 = 1203617) B1203617
theorem B802423 : Blo 802343 802423 := bstep (se 1 (by rfl) ⟨601817, by rfl⟩ : syracuseStep 802423 = 1203635) B1203635
theorem B7356035 : Blo 802343 7356035 := bstep (se 1 (by rfl) ⟨5517026, by rfl⟩ : syracuseStep 7356035 = 11034053) B11034053
theorem B802443 : Blo 802343 802443 := bstep (se 1 (by rfl) ⟨601832, by rfl⟩ : syracuseStep 802443 = 1203665) B1203665
theorem B802455 : Blo 802343 802455 := bstep (se 1 (by rfl) ⟨601841, by rfl⟩ : syracuseStep 802455 = 1203683) B1203683
theorem B802475 : Blo 802343 802475 := bstep (se 1 (by rfl) ⟨601856, by rfl⟩ : syracuseStep 802475 = 1203713) B1203713
theorem B802487 : Blo 802343 802487 := bstep (se 1 (by rfl) ⟨601865, by rfl⟩ : syracuseStep 802487 = 1203731) B1203731
theorem B802507 : Blo 802343 802507 := bstep (se 1 (by rfl) ⟨601880, by rfl⟩ : syracuseStep 802507 = 1203761) B1203761
theorem B802519 : Blo 802343 802519 := bstep (se 1 (by rfl) ⟨601889, by rfl⟩ : syracuseStep 802519 = 1203779) B1203779
theorem B1720025 : Blo 802343 1720025 := bstep (se 2 (by rfl) ⟨645009, by rfl⟩ : syracuseStep 1720025 = 1290019) B1290019
theorem B4079321 : Blo 802343 4079321 := bstep (se 2 (by rfl) ⟨1529745, by rfl⟩ : syracuseStep 4079321 = 3059491) B3059491
theorem B802539 : Blo 802343 802539 := bstep (se 1 (by rfl) ⟨601904, by rfl⟩ : syracuseStep 802539 = 1203809) B1203809
theorem B1523443 : Blo 802343 1523443 := bstep (se 1 (by rfl) ⟨1142582, by rfl⟩ : syracuseStep 1523443 = 2285165) B2285165
theorem B802551 : Blo 802343 802551 := bstep (se 1 (by rfl) ⟨601913, by rfl⟩ : syracuseStep 802551 = 1203827) B1203827
theorem B802571 : Blo 802343 802571 := bstep (se 1 (by rfl) ⟨601928, by rfl⟩ : syracuseStep 802571 = 1203857) B1203857
theorem B802583 : Blo 802343 802583 := bstep (se 1 (by rfl) ⟨601937, by rfl⟩ : syracuseStep 802583 = 1203875) B1203875
theorem B802603 : Blo 802343 802603 := bstep (se 1 (by rfl) ⟨601952, by rfl⟩ : syracuseStep 802603 = 1203905) B1203905
theorem B802615 : Blo 802343 802615 := bstep (se 1 (by rfl) ⟨601961, by rfl⟩ : syracuseStep 802615 = 1203923) B1203923
theorem B802635 : Blo 802343 802635 := bstep (se 1 (by rfl) ⟨601976, by rfl⟩ : syracuseStep 802635 = 1203953) B1203953
theorem B802647 : Blo 802343 802647 := bstep (se 1 (by rfl) ⟨601985, by rfl⟩ : syracuseStep 802647 = 1203971) B1203971
theorem B802667 : Blo 802343 802667 := bstep (se 1 (by rfl) ⟨602000, by rfl⟩ : syracuseStep 802667 = 1204001) B1204001
theorem B802679 : Blo 802343 802679 := bstep (se 1 (by rfl) ⟨602009, by rfl⟩ : syracuseStep 802679 = 1204019) B1204019
theorem B802699 : Blo 802343 802699 := bstep (se 1 (by rfl) ⟨602024, by rfl⟩ : syracuseStep 802699 = 1204049) B1204049
theorem B802711 : Blo 802343 802711 := bstep (se 1 (by rfl) ⟨602033, by rfl⟩ : syracuseStep 802711 = 1204067) B1204067
theorem B1359767 : Blo 802343 1359767 := bstep (se 1 (by rfl) ⟨1019825, by rfl⟩ : syracuseStep 1359767 = 2039651) B2039651
theorem B802731 : Blo 802343 802731 := bstep (se 1 (by rfl) ⟨602048, by rfl⟩ : syracuseStep 802731 = 1204097) B1204097
theorem B802743 : Blo 802343 802743 := bstep (se 1 (by rfl) ⟨602057, by rfl⟩ : syracuseStep 802743 = 1204115) B1204115
theorem B802763 : Blo 802343 802763 := bstep (se 1 (by rfl) ⟨602072, by rfl⟩ : syracuseStep 802763 = 1204145) B1204145
theorem B802775 : Blo 802343 802775 := bstep (se 1 (by rfl) ⟨602081, by rfl⟩ : syracuseStep 802775 = 1204163) B1204163
theorem B6864857 : Blo 802343 6864857 := bstep (se 2 (by rfl) ⟨2574321, by rfl⟩ : syracuseStep 6864857 = 5148643) B5148643
theorem B802795 : Blo 802343 802795 := bstep (se 1 (by rfl) ⟨602096, by rfl⟩ : syracuseStep 802795 = 1204193) B1204193
theorem B802807 : Blo 802343 802807 := bstep (se 1 (by rfl) ⟨602105, by rfl⟩ : syracuseStep 802807 = 1204211) B1204211
theorem B802827 : Blo 802343 802827 := bstep (se 1 (by rfl) ⟨602120, by rfl⟩ : syracuseStep 802827 = 1204241) B1204241
theorem B802839 : Blo 802343 802839 := bstep (se 1 (by rfl) ⟨602129, by rfl⟩ : syracuseStep 802839 = 1204259) B1204259
theorem B1359895 : Blo 802343 1359895 := bstep (se 1 (by rfl) ⟨1019921, by rfl⟩ : syracuseStep 1359895 = 2039843) B2039843
theorem B802859 : Blo 802343 802859 := bstep (se 1 (by rfl) ⟨602144, by rfl⟩ : syracuseStep 802859 = 1204289) B1204289
theorem B802871 : Blo 802343 802871 := bstep (se 1 (by rfl) ⟨602153, by rfl⟩ : syracuseStep 802871 = 1204307) B1204307
theorem B802891 : Blo 802343 802891 := bstep (se 1 (by rfl) ⟨602168, by rfl⟩ : syracuseStep 802891 = 1204337) B1204337
theorem B802903 : Blo 802343 802903 := bstep (se 1 (by rfl) ⟨602177, by rfl⟩ : syracuseStep 802903 = 1204355) B1204355
theorem B802923 : Blo 802343 802923 := bstep (se 1 (by rfl) ⟨602192, by rfl⟩ : syracuseStep 802923 = 1204385) B1204385
theorem B1720435 : Blo 802343 1720435 := bstep (se 1 (by rfl) ⟨1290326, by rfl⟩ : syracuseStep 1720435 = 2580653) B2580653
theorem B802935 : Blo 802343 802935 := bstep (se 1 (by rfl) ⟨602201, by rfl⟩ : syracuseStep 802935 = 1204403) B1204403
theorem B802955 : Blo 802343 802955 := bstep (se 1 (by rfl) ⟨602216, by rfl⟩ : syracuseStep 802955 = 1204433) B1204433
theorem B802967 : Blo 802343 802967 := bstep (se 1 (by rfl) ⟨602225, by rfl⟩ : syracuseStep 802967 = 1204451) B1204451
theorem B802987 : Blo 802343 802987 := bstep (se 1 (by rfl) ⟨602240, by rfl⟩ : syracuseStep 802987 = 1204481) B1204481
theorem B802999 : Blo 802343 802999 := bstep (se 1 (by rfl) ⟨602249, by rfl⟩ : syracuseStep 802999 = 1204499) B1204499
theorem B803019 : Blo 802343 803019 := bstep (se 1 (by rfl) ⟨602264, by rfl⟩ : syracuseStep 803019 = 1204529) B1204529
theorem B803031 : Blo 802343 803031 := bstep (se 1 (by rfl) ⟨602273, by rfl⟩ : syracuseStep 803031 = 1204547) B1204547
theorem B1523929 : Blo 802343 1523929 := bstep (se 2 (by rfl) ⟨571473, by rfl⟩ : syracuseStep 1523929 = 1142947) B1142947
theorem B6111449 : Blo 802343 6111449 := bstep (se 2 (by rfl) ⟨2291793, by rfl⟩ : syracuseStep 6111449 = 4583587) B4583587
theorem B803051 : Blo 802343 803051 := bstep (se 1 (by rfl) ⟨602288, by rfl⟩ : syracuseStep 803051 = 1204577) B1204577
theorem B803063 : Blo 802343 803063 := bstep (se 1 (by rfl) ⟨602297, by rfl⟩ : syracuseStep 803063 = 1204595) B1204595
theorem B803083 : Blo 802343 803083 := bstep (se 1 (by rfl) ⟨602312, by rfl⟩ : syracuseStep 803083 = 1204625) B1204625
theorem B803095 : Blo 802343 803095 := bstep (se 1 (by rfl) ⟨602321, by rfl⟩ : syracuseStep 803095 = 1204643) B1204643
theorem B803115 : Blo 802343 803115 := bstep (se 1 (by rfl) ⟨602336, by rfl⟩ : syracuseStep 803115 = 1204673) B1204673
theorem B803127 : Blo 802343 803127 := bstep (se 1 (by rfl) ⟨602345, by rfl⟩ : syracuseStep 803127 = 1204691) B1204691
theorem B803147 : Blo 802343 803147 := bstep (se 1 (by rfl) ⟨602360, by rfl⟩ : syracuseStep 803147 = 1204721) B1204721
theorem B803159 : Blo 802343 803159 := bstep (se 1 (by rfl) ⟨602369, by rfl⟩ : syracuseStep 803159 = 1204739) B1204739
theorem B803179 : Blo 802343 803179 := bstep (se 1 (by rfl) ⟨602384, by rfl⟩ : syracuseStep 803179 = 1204769) B1204769
theorem B1720691 : Blo 802343 1720691 := bstep (se 1 (by rfl) ⟨1290518, by rfl⟩ : syracuseStep 1720691 = 2581037) B2581037
theorem B803191 : Blo 802343 803191 := bstep (se 1 (by rfl) ⟨602393, by rfl⟩ : syracuseStep 803191 = 1204787) B1204787
theorem B803211 : Blo 802343 803211 := bstep (se 1 (by rfl) ⟨602408, by rfl⟩ : syracuseStep 803211 = 1204817) B1204817
theorem B803223 : Blo 802343 803223 := bstep (se 1 (by rfl) ⟨602417, by rfl⟩ : syracuseStep 803223 = 1204835) B1204835
theorem B803243 : Blo 802343 803243 := bstep (se 1 (by rfl) ⟨602432, by rfl⟩ : syracuseStep 803243 = 1204865) B1204865
theorem B803255 : Blo 802343 803255 := bstep (se 1 (by rfl) ⟨602441, by rfl⟩ : syracuseStep 803255 = 1204883) B1204883
theorem B803275 : Blo 802343 803275 := bstep (se 1 (by rfl) ⟨602456, by rfl⟩ : syracuseStep 803275 = 1204913) B1204913
theorem B803287 : Blo 802343 803287 := bstep (se 1 (by rfl) ⟨602465, by rfl⟩ : syracuseStep 803287 = 1204931) B1204931
theorem B803307 : Blo 802343 803307 := bstep (se 1 (by rfl) ⟨602480, by rfl⟩ : syracuseStep 803307 = 1204961) B1204961
theorem B803319 : Blo 802343 803319 := bstep (se 1 (by rfl) ⟨602489, by rfl⟩ : syracuseStep 803319 = 1204979) B1204979
theorem B803339 : Blo 802343 803339 := bstep (se 1 (by rfl) ⟨602504, by rfl⟩ : syracuseStep 803339 = 1205009) B1205009
theorem B2572823 : Blo 802343 2572823 := bstep (se 1 (by rfl) ⟨1929617, by rfl⟩ : syracuseStep 2572823 = 3859235) B3859235
theorem B803351 : Blo 802343 803351 := bstep (se 1 (by rfl) ⟨602513, by rfl⟩ : syracuseStep 803351 = 1205027) B1205027
theorem B803371 : Blo 802343 803371 := bstep (se 1 (by rfl) ⟨602528, by rfl⟩ : syracuseStep 803371 = 1205057) B1205057
theorem B803383 : Blo 802343 803383 := bstep (se 1 (by rfl) ⟨602537, by rfl⟩ : syracuseStep 803383 = 1205075) B1205075
theorem B803403 : Blo 802343 803403 := bstep (se 1 (by rfl) ⟨602552, by rfl⟩ : syracuseStep 803403 = 1205105) B1205105
theorem B803415 : Blo 802343 803415 := bstep (se 1 (by rfl) ⟨602561, by rfl⟩ : syracuseStep 803415 = 1205123) B1205123
theorem B4571741 : Blo 802343 4571741 := bstep (se 3 (by rfl) ⟨857201, by rfl⟩ : syracuseStep 4571741 = 1714403) B1714403
theorem B803435 : Blo 802343 803435 := bstep (se 1 (by rfl) ⟨602576, by rfl⟩ : syracuseStep 803435 = 1205153) B1205153
theorem B803447 : Blo 802343 803447 := bstep (se 1 (by rfl) ⟨602585, by rfl⟩ : syracuseStep 803447 = 1205171) B1205171
theorem B803467 : Blo 802343 803467 := bstep (se 1 (by rfl) ⟨602600, by rfl⟩ : syracuseStep 803467 = 1205201) B1205201
theorem B1360523 : Blo 802343 1360523 := bstep (se 1 (by rfl) ⟨1020392, by rfl⟩ : syracuseStep 1360523 = 2040785) B2040785
theorem B803479 : Blo 802343 803479 := bstep (se 1 (by rfl) ⟨602609, by rfl⟩ : syracuseStep 803479 = 1205219) B1205219
theorem B803499 : Blo 802343 803499 := bstep (se 1 (by rfl) ⟨602624, by rfl⟩ : syracuseStep 803499 = 1205249) B1205249
theorem B803511 : Blo 802343 803511 := bstep (se 1 (by rfl) ⟨602633, by rfl⟩ : syracuseStep 803511 = 1205267) B1205267
theorem B803531 : Blo 802343 803531 := bstep (se 1 (by rfl) ⟨602648, by rfl⟩ : syracuseStep 803531 = 1205297) B1205297
theorem B1393355 : Blo 802343 1393355 := bstep (se 1 (by rfl) ⟨1045016, by rfl⟩ : syracuseStep 1393355 = 2090033) B2090033
theorem B803543 : Blo 802343 803543 := bstep (se 1 (by rfl) ⟨602657, by rfl⟩ : syracuseStep 803543 = 1205315) B1205315
theorem B803563 : Blo 802343 803563 := bstep (se 1 (by rfl) ⟨602672, by rfl⟩ : syracuseStep 803563 = 1205345) B1205345
theorem B803575 : Blo 802343 803575 := bstep (se 1 (by rfl) ⟨602681, by rfl⟩ : syracuseStep 803575 = 1205363) B1205363
theorem B1524491 : Blo 802343 1524491 := bstep (se 1 (by rfl) ⟨1143368, by rfl⟩ : syracuseStep 1524491 = 2286737) B2286737
theorem B803595 : Blo 802343 803595 := bstep (se 1 (by rfl) ⟨602696, by rfl⟩ : syracuseStep 803595 = 1205393) B1205393
theorem B1360651 : Blo 802343 1360651 := bstep (se 1 (by rfl) ⟨1020488, by rfl⟩ : syracuseStep 1360651 = 2040977) B2040977
theorem B803607 : Blo 802343 803607 := bstep (se 1 (by rfl) ⟨602705, by rfl⟩ : syracuseStep 803607 = 1205411) B1205411
theorem B803627 : Blo 802343 803627 := bstep (se 1 (by rfl) ⟨602720, by rfl⟩ : syracuseStep 803627 = 1205441) B1205441
theorem B803639 : Blo 802343 803639 := bstep (se 1 (by rfl) ⟨602729, by rfl⟩ : syracuseStep 803639 = 1205459) B1205459
theorem B803659 : Blo 802343 803659 := bstep (se 1 (by rfl) ⟨602744, by rfl⟩ : syracuseStep 803659 = 1205489) B1205489
theorem B803671 : Blo 802343 803671 := bstep (se 1 (by rfl) ⟨602753, by rfl⟩ : syracuseStep 803671 = 1205507) B1205507
theorem B803691 : Blo 802343 803691 := bstep (se 1 (by rfl) ⟨602768, by rfl⟩ : syracuseStep 803691 = 1205537) B1205537
theorem B803703 : Blo 802343 803703 := bstep (se 1 (by rfl) ⟨602777, by rfl⟩ : syracuseStep 803703 = 1205555) B1205555
theorem B803723 : Blo 802343 803723 := bstep (se 1 (by rfl) ⟨602792, by rfl⟩ : syracuseStep 803723 = 1205585) B1205585
theorem B803735 : Blo 802343 803735 := bstep (se 1 (by rfl) ⟨602801, by rfl⟩ : syracuseStep 803735 = 1205603) B1205603
theorem B803755 : Blo 802343 803755 := bstep (se 1 (by rfl) ⟨602816, by rfl⟩ : syracuseStep 803755 = 1205633) B1205633
theorem B5784497 : Blo 802343 5784497 := bstep (se 2 (by rfl) ⟨2169186, by rfl⟩ : syracuseStep 5784497 = 4338373) B4338373
theorem B803767 : Blo 802343 803767 := bstep (se 1 (by rfl) ⟨602825, by rfl⟩ : syracuseStep 803767 = 1205651) B1205651
theorem B1524673 : Blo 802343 1524673 := bstep (se 2 (by rfl) ⟨571752, by rfl⟩ : syracuseStep 1524673 = 1143505) B1143505
theorem B803787 : Blo 802343 803787 := bstep (se 1 (by rfl) ⟨602840, by rfl⟩ : syracuseStep 803787 = 1205681) B1205681
theorem B803799 : Blo 802343 803799 := bstep (se 1 (by rfl) ⟨602849, by rfl⟩ : syracuseStep 803799 = 1205699) B1205699
theorem B803819 : Blo 802343 803819 := bstep (se 1 (by rfl) ⟨602864, by rfl⟩ : syracuseStep 803819 = 1205729) B1205729
theorem B1655795 : Blo 802343 1655795 := bstep (se 1 (by rfl) ⟨1241846, by rfl⟩ : syracuseStep 1655795 = 2483693) B2483693
theorem B803831 : Blo 802343 803831 := bstep (se 1 (by rfl) ⟨602873, by rfl⟩ : syracuseStep 803831 = 1205747) B1205747
theorem B803851 : Blo 802343 803851 := bstep (se 1 (by rfl) ⟨602888, by rfl⟩ : syracuseStep 803851 = 1205777) B1205777
theorem B6177809 : Blo 802343 6177809 := bstep (se 2 (by rfl) ⟨2316678, by rfl⟩ : syracuseStep 6177809 = 4633357) B4633357
theorem B803863 : Blo 802343 803863 := bstep (se 1 (by rfl) ⟨602897, by rfl⟩ : syracuseStep 803863 = 1205795) B1205795
theorem B803883 : Blo 802343 803883 := bstep (se 1 (by rfl) ⟨602912, by rfl⟩ : syracuseStep 803883 = 1205825) B1205825
theorem B3097651 : Blo 802343 3097651 := bstep (se 1 (by rfl) ⟨2323238, by rfl⟩ : syracuseStep 3097651 = 4646477) B4646477
theorem B803895 : Blo 802343 803895 := bstep (se 1 (by rfl) ⟨602921, by rfl⟩ : syracuseStep 803895 = 1205843) B1205843
theorem B803915 : Blo 802343 803915 := bstep (se 1 (by rfl) ⟨602936, by rfl⟩ : syracuseStep 803915 = 1205873) B1205873
theorem B803927 : Blo 802343 803927 := bstep (se 1 (by rfl) ⟨602945, by rfl⟩ : syracuseStep 803927 = 1205891) B1205891
theorem B803947 : Blo 802343 803947 := bstep (se 1 (by rfl) ⟨602960, by rfl⟩ : syracuseStep 803947 = 1205921) B1205921
theorem B803959 : Blo 802343 803959 := bstep (se 1 (by rfl) ⟨602969, by rfl⟩ : syracuseStep 803959 = 1205939) B1205939
theorem B803979 : Blo 802343 803979 := bstep (se 1 (by rfl) ⟨602984, by rfl⟩ : syracuseStep 803979 = 1205969) B1205969
theorem B803991 : Blo 802343 803991 := bstep (se 1 (by rfl) ⟨602993, by rfl⟩ : syracuseStep 803991 = 1205987) B1205987
theorem B967831 : Blo 802343 967831 := bstep (se 1 (by rfl) ⟨725873, by rfl⟩ : syracuseStep 967831 = 1451747) B1451747
theorem B804011 : Blo 802343 804011 := bstep (se 1 (by rfl) ⟨603008, by rfl⟩ : syracuseStep 804011 = 1206017) B1206017
theorem B804023 : Blo 802343 804023 := bstep (se 1 (by rfl) ⟨603017, by rfl⟩ : syracuseStep 804023 = 1206035) B1206035
theorem B804043 : Blo 802343 804043 := bstep (se 1 (by rfl) ⟨603032, by rfl⟩ : syracuseStep 804043 = 1206065) B1206065
theorem B804055 : Blo 802343 804055 := bstep (se 1 (by rfl) ⟨603041, by rfl⟩ : syracuseStep 804055 = 1206083) B1206083
theorem B804075 : Blo 802343 804075 := bstep (se 1 (by rfl) ⟨603056, by rfl⟩ : syracuseStep 804075 = 1206113) B1206113
theorem B804087 : Blo 802343 804087 := bstep (se 1 (by rfl) ⟨603065, by rfl⟩ : syracuseStep 804087 = 1206131) B1206131
theorem B804107 : Blo 802343 804107 := bstep (se 1 (by rfl) ⟨603080, by rfl⟩ : syracuseStep 804107 = 1206161) B1206161
theorem B804119 : Blo 802343 804119 := bstep (se 1 (by rfl) ⟨603089, by rfl⟩ : syracuseStep 804119 = 1206179) B1206179
theorem B804139 : Blo 802343 804139 := bstep (se 1 (by rfl) ⟨603104, by rfl⟩ : syracuseStep 804139 = 1206209) B1206209
theorem B4080941 : Blo 802343 4080941 := bstep (se 3 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 4080941 = 1530353) B1530353
theorem B804151 : Blo 802343 804151 := bstep (se 1 (by rfl) ⟨603113, by rfl⟩ : syracuseStep 804151 = 1206227) B1206227
theorem B1721665 : Blo 802343 1721665 := bstep (se 2 (by rfl) ⟨645624, by rfl⟩ : syracuseStep 1721665 = 1291249) B1291249
theorem B804171 : Blo 802343 804171 := bstep (se 1 (by rfl) ⟨603128, by rfl⟩ : syracuseStep 804171 = 1206257) B1206257
theorem B804183 : Blo 802343 804183 := bstep (se 1 (by rfl) ⟨603137, by rfl⟩ : syracuseStep 804183 = 1206275) B1206275
theorem B804203 : Blo 802343 804203 := bstep (se 1 (by rfl) ⟨603152, by rfl⟩ : syracuseStep 804203 = 1206305) B1206305
theorem B804215 : Blo 802343 804215 := bstep (se 1 (by rfl) ⟨603161, by rfl⟩ : syracuseStep 804215 = 1206323) B1206323
theorem B804235 : Blo 802343 804235 := bstep (se 1 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 804235 = 1206353) B1206353
theorem B804247 : Blo 802343 804247 := bstep (se 1 (by rfl) ⟨603185, by rfl⟩ : syracuseStep 804247 = 1206371) B1206371
theorem B804267 : Blo 802343 804267 := bstep (se 1 (by rfl) ⟨603200, by rfl⟩ : syracuseStep 804267 = 1206401) B1206401
theorem B804279 : Blo 802343 804279 := bstep (se 1 (by rfl) ⟨603209, by rfl⟩ : syracuseStep 804279 = 1206419) B1206419
theorem B804299 : Blo 802343 804299 := bstep (se 1 (by rfl) ⟨603224, by rfl⟩ : syracuseStep 804299 = 1206449) B1206449
theorem B804311 : Blo 802343 804311 := bstep (se 1 (by rfl) ⟨603233, by rfl⟩ : syracuseStep 804311 = 1206467) B1206467
theorem B804331 : Blo 802343 804331 := bstep (se 1 (by rfl) ⟨603248, by rfl⟩ : syracuseStep 804331 = 1206497) B1206497
theorem B804343 : Blo 802343 804343 := bstep (se 1 (by rfl) ⟨603257, by rfl⟩ : syracuseStep 804343 = 1206515) B1206515
theorem B804363 : Blo 802343 804363 := bstep (se 1 (by rfl) ⟨603272, by rfl⟩ : syracuseStep 804363 = 1206545) B1206545
theorem B804375 : Blo 802343 804375 := bstep (se 1 (by rfl) ⟨603281, by rfl⟩ : syracuseStep 804375 = 1206563) B1206563
theorem B804395 : Blo 802343 804395 := bstep (se 1 (by rfl) ⟨603296, by rfl⟩ : syracuseStep 804395 = 1206593) B1206593
theorem B804407 : Blo 802343 804407 := bstep (se 1 (by rfl) ⟨603305, by rfl⟩ : syracuseStep 804407 = 1206611) B1206611
theorem B902731 : Blo 802343 902731 := bstep (se 1 (by rfl) ⟨677048, by rfl⟩ : syracuseStep 902731 = 1354097) B1354097
theorem B804427 : Blo 802343 804427 := bstep (se 1 (by rfl) ⟨603320, by rfl⟩ : syracuseStep 804427 = 1206641) B1206641
theorem B804439 : Blo 802343 804439 := bstep (se 1 (by rfl) ⟨603329, by rfl⟩ : syracuseStep 804439 = 1206659) B1206659
theorem B804459 : Blo 802343 804459 := bstep (se 1 (by rfl) ⟨603344, by rfl⟩ : syracuseStep 804459 = 1206689) B1206689
theorem B804471 : Blo 802343 804471 := bstep (se 1 (by rfl) ⟨603353, by rfl⟩ : syracuseStep 804471 = 1206707) B1206707
theorem B1525387 : Blo 802343 1525387 := bstep (se 1 (by rfl) ⟨1144040, by rfl⟩ : syracuseStep 1525387 = 2288081) B2288081
theorem B804491 : Blo 802343 804491 := bstep (se 1 (by rfl) ⟨603368, by rfl⟩ : syracuseStep 804491 = 1206737) B1206737
theorem B804503 : Blo 802343 804503 := bstep (se 1 (by rfl) ⟨603377, by rfl⟩ : syracuseStep 804503 = 1206755) B1206755
theorem B804523 : Blo 802343 804523 := bstep (se 1 (by rfl) ⟨603392, by rfl⟩ : syracuseStep 804523 = 1206785) B1206785
theorem B902839 : Blo 802343 902839 := bstep (se 1 (by rfl) ⟨677129, by rfl⟩ : syracuseStep 902839 = 1354259) B1354259
theorem B804535 : Blo 802343 804535 := bstep (se 1 (by rfl) ⟨603401, by rfl⟩ : syracuseStep 804535 = 1206803) B1206803
theorem B804555 : Blo 802343 804555 := bstep (se 1 (by rfl) ⟨603416, by rfl⟩ : syracuseStep 804555 = 1206833) B1206833
theorem B1525463 : Blo 802343 1525463 := bstep (se 1 (by rfl) ⟨1144097, by rfl⟩ : syracuseStep 1525463 = 2288195) B2288195
theorem B804567 : Blo 802343 804567 := bstep (se 1 (by rfl) ⟨603425, by rfl⟩ : syracuseStep 804567 = 1206851) B1206851
theorem B804587 : Blo 802343 804587 := bstep (se 1 (by rfl) ⟨603440, by rfl⟩ : syracuseStep 804587 = 1206881) B1206881
theorem B804599 : Blo 802343 804599 := bstep (se 1 (by rfl) ⟨603449, by rfl⟩ : syracuseStep 804599 = 1206899) B1206899
theorem B804619 : Blo 802343 804619 := bstep (se 1 (by rfl) ⟨603464, by rfl⟩ : syracuseStep 804619 = 1206929) B1206929
theorem B804631 : Blo 802343 804631 := bstep (se 1 (by rfl) ⟨603473, by rfl⟩ : syracuseStep 804631 = 1206947) B1206947
theorem B804651 : Blo 802343 804651 := bstep (se 1 (by rfl) ⟨603488, by rfl⟩ : syracuseStep 804651 = 1206977) B1206977
theorem B804663 : Blo 802343 804663 := bstep (se 1 (by rfl) ⟨603497, by rfl⟩ : syracuseStep 804663 = 1206995) B1206995
theorem B804683 : Blo 802343 804683 := bstep (se 1 (by rfl) ⟨603512, by rfl⟩ : syracuseStep 804683 = 1207025) B1207025
theorem B804695 : Blo 802343 804695 := bstep (se 1 (by rfl) ⟨603521, by rfl⟩ : syracuseStep 804695 = 1207043) B1207043
theorem B903019 : Blo 802343 903019 := bstep (se 1 (by rfl) ⟨677264, by rfl⟩ : syracuseStep 903019 = 1354529) B1354529
theorem B804715 : Blo 802343 804715 := bstep (se 1 (by rfl) ⟨603536, by rfl⟩ : syracuseStep 804715 = 1207073) B1207073
theorem B804727 : Blo 802343 804727 := bstep (se 1 (by rfl) ⟨603545, by rfl⟩ : syracuseStep 804727 = 1207091) B1207091
theorem B804747 : Blo 802343 804747 := bstep (se 1 (by rfl) ⟨603560, by rfl⟩ : syracuseStep 804747 = 1207121) B1207121
theorem B804759 : Blo 802343 804759 := bstep (se 1 (by rfl) ⟨603569, by rfl⟩ : syracuseStep 804759 = 1207139) B1207139
theorem B804779 : Blo 802343 804779 := bstep (se 1 (by rfl) ⟨603584, by rfl⟩ : syracuseStep 804779 = 1207169) B1207169
theorem B804791 : Blo 802343 804791 := bstep (se 1 (by rfl) ⟨603593, by rfl⟩ : syracuseStep 804791 = 1207187) B1207187
theorem B804811 : Blo 802343 804811 := bstep (se 1 (by rfl) ⟨603608, by rfl⟩ : syracuseStep 804811 = 1207217) B1207217
theorem B903127 : Blo 802343 903127 := bstep (se 1 (by rfl) ⟨677345, by rfl⟩ : syracuseStep 903127 = 1354691) B1354691
theorem B804823 : Blo 802343 804823 := bstep (se 1 (by rfl) ⟨603617, by rfl⟩ : syracuseStep 804823 = 1207235) B1207235
theorem B2934749 : Blo 802343 2934749 := bstep (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) B1100531
theorem B804843 : Blo 802343 804843 := bstep (se 1 (by rfl) ⟨603632, by rfl⟩ : syracuseStep 804843 = 1207265) B1207265
theorem B804855 : Blo 802343 804855 := bstep (se 1 (by rfl) ⟨603641, by rfl⟩ : syracuseStep 804855 = 1207283) B1207283
theorem B804875 : Blo 802343 804875 := bstep (se 1 (by rfl) ⟨603656, by rfl⟩ : syracuseStep 804875 = 1207313) B1207313
theorem B804887 : Blo 802343 804887 := bstep (se 1 (by rfl) ⟨603665, by rfl⟩ : syracuseStep 804887 = 1207331) B1207331
theorem B804907 : Blo 802343 804907 := bstep (se 1 (by rfl) ⟨603680, by rfl⟩ : syracuseStep 804907 = 1207361) B1207361
theorem B804919 : Blo 802343 804919 := bstep (se 1 (by rfl) ⟨603689, by rfl⟩ : syracuseStep 804919 = 1207379) B1207379
theorem B2902081 : Blo 802343 2902081 := bstep (se 2 (by rfl) ⟨1088280, by rfl⟩ : syracuseStep 2902081 = 2176561) B2176561
theorem B804939 : Blo 802343 804939 := bstep (se 1 (by rfl) ⟨603704, by rfl⟩ : syracuseStep 804939 = 1207409) B1207409
theorem B804951 : Blo 802343 804951 := bstep (se 1 (by rfl) ⟨603713, by rfl⟩ : syracuseStep 804951 = 1207427) B1207427
theorem B804971 : Blo 802343 804971 := bstep (se 1 (by rfl) ⟨603728, by rfl⟩ : syracuseStep 804971 = 1207457) B1207457
theorem B804983 : Blo 802343 804983 := bstep (se 1 (by rfl) ⟨603737, by rfl⟩ : syracuseStep 804983 = 1207475) B1207475
theorem B903307 : Blo 802343 903307 := bstep (se 1 (by rfl) ⟨677480, by rfl⟩ : syracuseStep 903307 = 1354961) B1354961
theorem B805003 : Blo 802343 805003 := bstep (se 1 (by rfl) ⟨603752, by rfl⟩ : syracuseStep 805003 = 1207505) B1207505
theorem B805015 : Blo 802343 805015 := bstep (se 1 (by rfl) ⟨603761, by rfl⟩ : syracuseStep 805015 = 1207523) B1207523
theorem B805035 : Blo 802343 805035 := bstep (se 1 (by rfl) ⟨603776, by rfl⟩ : syracuseStep 805035 = 1207553) B1207553
theorem B805047 : Blo 802343 805047 := bstep (se 1 (by rfl) ⟨603785, by rfl⟩ : syracuseStep 805047 = 1207571) B1207571
theorem B805067 : Blo 802343 805067 := bstep (se 1 (by rfl) ⟨603800, by rfl⟩ : syracuseStep 805067 = 1207601) B1207601
theorem B805079 : Blo 802343 805079 := bstep (se 1 (by rfl) ⟨603809, by rfl⟩ : syracuseStep 805079 = 1207619) B1207619
theorem B805099 : Blo 802343 805099 := bstep (se 1 (by rfl) ⟨603824, by rfl⟩ : syracuseStep 805099 = 1207649) B1207649
theorem B903415 : Blo 802343 903415 := bstep (se 1 (by rfl) ⟨677561, by rfl⟩ : syracuseStep 903415 = 1355123) B1355123
theorem B805111 : Blo 802343 805111 := bstep (se 1 (by rfl) ⟨603833, by rfl⟩ : syracuseStep 805111 = 1207667) B1207667
theorem B805131 : Blo 802343 805131 := bstep (se 1 (by rfl) ⟨603848, by rfl⟩ : syracuseStep 805131 = 1207697) B1207697
theorem B805143 : Blo 802343 805143 := bstep (se 1 (by rfl) ⟨603857, by rfl⟩ : syracuseStep 805143 = 1207715) B1207715
theorem B805163 : Blo 802343 805163 := bstep (se 1 (by rfl) ⟨603872, by rfl⟩ : syracuseStep 805163 = 1207745) B1207745
theorem B3262765 : Blo 802343 3262765 := bstep (se 3 (by rfl) ⟨611768, by rfl⟩ : syracuseStep 3262765 = 1223537) B1223537
theorem B805175 : Blo 802343 805175 := bstep (se 1 (by rfl) ⟨603881, by rfl⟩ : syracuseStep 805175 = 1207763) B1207763
theorem B805195 : Blo 802343 805195 := bstep (se 1 (by rfl) ⟨603896, by rfl⟩ : syracuseStep 805195 = 1207793) B1207793
theorem B805207 : Blo 802343 805207 := bstep (se 1 (by rfl) ⟨603905, by rfl⟩ : syracuseStep 805207 = 1207811) B1207811
theorem B805227 : Blo 802343 805227 := bstep (se 1 (by rfl) ⟨603920, by rfl⟩ : syracuseStep 805227 = 1207841) B1207841
theorem B1526131 : Blo 802343 1526131 := bstep (se 1 (by rfl) ⟨1144598, by rfl⟩ : syracuseStep 1526131 = 2289197) B2289197
theorem B805239 : Blo 802343 805239 := bstep (se 1 (by rfl) ⟨603929, by rfl⟩ : syracuseStep 805239 = 1207859) B1207859
theorem B805259 : Blo 802343 805259 := bstep (se 1 (by rfl) ⟨603944, by rfl⟩ : syracuseStep 805259 = 1207889) B1207889
theorem B805271 : Blo 802343 805271 := bstep (se 1 (by rfl) ⟨603953, by rfl⟩ : syracuseStep 805271 = 1207907) B1207907
theorem B903595 : Blo 802343 903595 := bstep (se 1 (by rfl) ⟨677696, by rfl⟩ : syracuseStep 903595 = 1355393) B1355393
theorem B805291 : Blo 802343 805291 := bstep (se 1 (by rfl) ⟨603968, by rfl⟩ : syracuseStep 805291 = 1207937) B1207937
theorem B805303 : Blo 802343 805303 := bstep (se 1 (by rfl) ⟨603977, by rfl⟩ : syracuseStep 805303 = 1207955) B1207955
theorem B805323 : Blo 802343 805323 := bstep (se 1 (by rfl) ⟨603992, by rfl⟩ : syracuseStep 805323 = 1207985) B1207985
theorem B805335 : Blo 802343 805335 := bstep (se 1 (by rfl) ⟨604001, by rfl⟩ : syracuseStep 805335 = 1208003) B1208003
theorem B805355 : Blo 802343 805355 := bstep (se 1 (by rfl) ⟨604016, by rfl⟩ : syracuseStep 805355 = 1208033) B1208033
theorem B805367 : Blo 802343 805367 := bstep (se 1 (by rfl) ⟨604025, by rfl⟩ : syracuseStep 805367 = 1208051) B1208051
theorem B805387 : Blo 802343 805387 := bstep (se 1 (by rfl) ⟨604040, by rfl⟩ : syracuseStep 805387 = 1208081) B1208081
theorem B903703 : Blo 802343 903703 := bstep (se 1 (by rfl) ⟨677777, by rfl⟩ : syracuseStep 903703 = 1355555) B1355555
theorem B805399 : Blo 802343 805399 := bstep (se 1 (by rfl) ⟨604049, by rfl⟩ : syracuseStep 805399 = 1208099) B1208099
theorem B805419 : Blo 802343 805419 := bstep (se 1 (by rfl) ⟨604064, by rfl⟩ : syracuseStep 805419 = 1208129) B1208129
theorem B805431 : Blo 802343 805431 := bstep (se 1 (by rfl) ⟨604073, by rfl⟩ : syracuseStep 805431 = 1208147) B1208147
theorem B2443841 : Blo 802343 2443841 := bstep (se 2 (by rfl) ⟨916440, by rfl⟩ : syracuseStep 2443841 = 1832881) B1832881
theorem B805451 : Blo 802343 805451 := bstep (se 1 (by rfl) ⟨604088, by rfl⟩ : syracuseStep 805451 = 1208177) B1208177
theorem B1526359 : Blo 802343 1526359 := bstep (se 1 (by rfl) ⟨1144769, by rfl⟩ : syracuseStep 1526359 = 2289539) B2289539
theorem B805463 : Blo 802343 805463 := bstep (se 1 (by rfl) ⟨604097, by rfl⟩ : syracuseStep 805463 = 1208195) B1208195
theorem B805483 : Blo 802343 805483 := bstep (se 1 (by rfl) ⟨604112, by rfl⟩ : syracuseStep 805483 = 1208225) B1208225
theorem B805495 : Blo 802343 805495 := bstep (se 1 (by rfl) ⟨604121, by rfl⟩ : syracuseStep 805495 = 1208243) B1208243
theorem B11586179 : Blo 802343 11586179 := bstep (se 1 (by rfl) ⟨8689634, by rfl⟩ : syracuseStep 11586179 = 17379269) B17379269
theorem B805515 : Blo 802343 805515 := bstep (se 1 (by rfl) ⟨604136, by rfl⟩ : syracuseStep 805515 = 1208273) B1208273
theorem B2443927 : Blo 802343 2443927 := bstep (se 1 (by rfl) ⟨1832945, by rfl⟩ : syracuseStep 2443927 = 3665891) B3665891
theorem B805527 : Blo 802343 805527 := bstep (se 1 (by rfl) ⟨604145, by rfl⟩ : syracuseStep 805527 = 1208291) B1208291
theorem B805547 : Blo 802343 805547 := bstep (se 1 (by rfl) ⟨604160, by rfl⟩ : syracuseStep 805547 = 1208321) B1208321
theorem B805559 : Blo 802343 805559 := bstep (se 1 (by rfl) ⟨604169, by rfl⟩ : syracuseStep 805559 = 1208339) B1208339
theorem B1526465 : Blo 802343 1526465 := bstep (se 2 (by rfl) ⟨572424, by rfl⟩ : syracuseStep 1526465 = 1144849) B1144849
theorem B903883 : Blo 802343 903883 := bstep (se 1 (by rfl) ⟨677912, by rfl⟩ : syracuseStep 903883 = 1355825) B1355825
theorem B805579 : Blo 802343 805579 := bstep (se 1 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 805579 = 1208369) B1208369
theorem B805591 : Blo 802343 805591 := bstep (se 1 (by rfl) ⟨604193, by rfl⟩ : syracuseStep 805591 = 1208387) B1208387
theorem B805611 : Blo 802343 805611 := bstep (se 1 (by rfl) ⟨604208, by rfl⟩ : syracuseStep 805611 = 1208417) B1208417
theorem B805623 : Blo 802343 805623 := bstep (se 1 (by rfl) ⟨604217, by rfl⟩ : syracuseStep 805623 = 1208435) B1208435
theorem B805643 : Blo 802343 805643 := bstep (se 1 (by rfl) ⟨604232, by rfl⟩ : syracuseStep 805643 = 1208465) B1208465
theorem B805655 : Blo 802343 805655 := bstep (se 1 (by rfl) ⟨604241, by rfl⟩ : syracuseStep 805655 = 1208483) B1208483
theorem B805675 : Blo 802343 805675 := bstep (se 1 (by rfl) ⟨604256, by rfl⟩ : syracuseStep 805675 = 1208513) B1208513
theorem B903991 : Blo 802343 903991 := bstep (se 1 (by rfl) ⟨677993, by rfl⟩ : syracuseStep 903991 = 1355987) B1355987
theorem B805687 : Blo 802343 805687 := bstep (se 1 (by rfl) ⟨604265, by rfl⟩ : syracuseStep 805687 = 1208531) B1208531
theorem B805707 : Blo 802343 805707 := bstep (se 1 (by rfl) ⟨604280, by rfl⟩ : syracuseStep 805707 = 1208561) B1208561
theorem B805719 : Blo 802343 805719 := bstep (se 1 (by rfl) ⟨604289, by rfl⟩ : syracuseStep 805719 = 1208579) B1208579
theorem B1526617 : Blo 802343 1526617 := bstep (se 2 (by rfl) ⟨572481, by rfl⟩ : syracuseStep 1526617 = 1144963) B1144963
theorem B805739 : Blo 802343 805739 := bstep (se 1 (by rfl) ⟨604304, by rfl⟩ : syracuseStep 805739 = 1208609) B1208609
theorem B805751 : Blo 802343 805751 := bstep (se 1 (by rfl) ⟨604313, by rfl⟩ : syracuseStep 805751 = 1208627) B1208627
theorem B805771 : Blo 802343 805771 := bstep (se 1 (by rfl) ⟨604328, by rfl⟩ : syracuseStep 805771 = 1208657) B1208657
theorem B805783 : Blo 802343 805783 := bstep (se 1 (by rfl) ⟨604337, by rfl⟩ : syracuseStep 805783 = 1208675) B1208675
theorem B805803 : Blo 802343 805803 := bstep (se 1 (by rfl) ⟨604352, by rfl⟩ : syracuseStep 805803 = 1208705) B1208705
theorem B805815 : Blo 802343 805815 := bstep (se 1 (by rfl) ⟨604361, by rfl⟩ : syracuseStep 805815 = 1208723) B1208723
theorem B805835 : Blo 802343 805835 := bstep (se 1 (by rfl) ⟨604376, by rfl⟩ : syracuseStep 805835 = 1208753) B1208753
theorem B805847 : Blo 802343 805847 := bstep (se 1 (by rfl) ⟨604385, by rfl⟩ : syracuseStep 805847 = 1208771) B1208771
theorem B3132377 : Blo 802343 3132377 := bstep (se 2 (by rfl) ⟨1174641, by rfl⟩ : syracuseStep 3132377 = 2349283) B2349283
theorem B904171 : Blo 802343 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B805867 : Blo 802343 805867 := bstep (se 1 (by rfl) ⟨604400, by rfl⟩ : syracuseStep 805867 = 1208801) B1208801
theorem B805879 : Blo 802343 805879 := bstep (se 1 (by rfl) ⟨604409, by rfl⟩ : syracuseStep 805879 = 1208819) B1208819
theorem B805899 : Blo 802343 805899 := bstep (se 1 (by rfl) ⟨604424, by rfl⟩ : syracuseStep 805899 = 1208849) B1208849
theorem B805911 : Blo 802343 805911 := bstep (se 1 (by rfl) ⟨604433, by rfl⟩ : syracuseStep 805911 = 1208867) B1208867
theorem B805931 : Blo 802343 805931 := bstep (se 1 (by rfl) ⟨604448, by rfl⟩ : syracuseStep 805931 = 1208897) B1208897
theorem B4901933 : Blo 802343 4901933 := bstep (se 3 (by rfl) ⟨919112, by rfl⟩ : syracuseStep 4901933 = 1838225) B1838225
theorem B805943 : Blo 802343 805943 := bstep (se 1 (by rfl) ⟨604457, by rfl⟩ : syracuseStep 805943 = 1208915) B1208915
theorem B805963 : Blo 802343 805963 := bstep (se 1 (by rfl) ⟨604472, by rfl⟩ : syracuseStep 805963 = 1208945) B1208945
theorem B904279 : Blo 802343 904279 := bstep (se 1 (by rfl) ⟨678209, by rfl⟩ : syracuseStep 904279 = 1356419) B1356419
theorem B805975 : Blo 802343 805975 := bstep (se 1 (by rfl) ⟨604481, by rfl⟩ : syracuseStep 805975 = 1208963) B1208963
theorem B805995 : Blo 802343 805995 := bstep (se 1 (by rfl) ⟨604496, by rfl⟩ : syracuseStep 805995 = 1208993) B1208993
theorem B806007 : Blo 802343 806007 := bstep (se 1 (by rfl) ⟨604505, by rfl⟩ : syracuseStep 806007 = 1209011) B1209011
theorem B4574339 : Blo 802343 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B806027 : Blo 802343 806027 := bstep (se 1 (by rfl) ⟨604520, by rfl⟩ : syracuseStep 806027 = 1209041) B1209041
theorem B806039 : Blo 802343 806039 := bstep (se 1 (by rfl) ⟨604529, by rfl⟩ : syracuseStep 806039 = 1209059) B1209059
theorem B806059 : Blo 802343 806059 := bstep (se 1 (by rfl) ⟨604544, by rfl⟩ : syracuseStep 806059 = 1209089) B1209089
theorem B806071 : Blo 802343 806071 := bstep (se 1 (by rfl) ⟨604553, by rfl⟩ : syracuseStep 806071 = 1209107) B1209107
theorem B806091 : Blo 802343 806091 := bstep (se 1 (by rfl) ⟨604568, by rfl⟩ : syracuseStep 806091 = 1209137) B1209137
theorem B806103 : Blo 802343 806103 := bstep (se 1 (by rfl) ⟨604577, by rfl⟩ : syracuseStep 806103 = 1209155) B1209155
theorem B806123 : Blo 802343 806123 := bstep (se 1 (by rfl) ⟨604592, by rfl⟩ : syracuseStep 806123 = 1209185) B1209185
theorem B806135 : Blo 802343 806135 := bstep (se 1 (by rfl) ⟨604601, by rfl⟩ : syracuseStep 806135 = 1209203) B1209203
theorem B904459 : Blo 802343 904459 := bstep (se 1 (by rfl) ⟨678344, by rfl⟩ : syracuseStep 904459 = 1356689) B1356689
theorem B806155 : Blo 802343 806155 := bstep (se 1 (by rfl) ⟨604616, by rfl⟩ : syracuseStep 806155 = 1209233) B1209233
theorem B806167 : Blo 802343 806167 := bstep (se 1 (by rfl) ⟨604625, by rfl⟩ : syracuseStep 806167 = 1209251) B1209251
theorem B806187 : Blo 802343 806187 := bstep (se 1 (by rfl) ⟨604640, by rfl⟩ : syracuseStep 806187 = 1209281) B1209281
theorem B806199 : Blo 802343 806199 := bstep (se 1 (by rfl) ⟨604649, by rfl⟩ : syracuseStep 806199 = 1209299) B1209299
theorem B806219 : Blo 802343 806219 := bstep (se 1 (by rfl) ⟨604664, by rfl⟩ : syracuseStep 806219 = 1209329) B1209329
theorem B806231 : Blo 802343 806231 := bstep (se 1 (by rfl) ⟨604673, by rfl⟩ : syracuseStep 806231 = 1209347) B1209347
theorem B806251 : Blo 802343 806251 := bstep (se 1 (by rfl) ⟨604688, by rfl⟩ : syracuseStep 806251 = 1209377) B1209377
theorem B904567 : Blo 802343 904567 := bstep (se 1 (by rfl) ⟨678425, by rfl⟩ : syracuseStep 904567 = 1356851) B1356851
theorem B806263 : Blo 802343 806263 := bstep (se 1 (by rfl) ⟨604697, by rfl⟩ : syracuseStep 806263 = 1209395) B1209395
theorem B806283 : Blo 802343 806283 := bstep (se 1 (by rfl) ⟨604712, by rfl⟩ : syracuseStep 806283 = 1209425) B1209425
theorem B806295 : Blo 802343 806295 := bstep (se 1 (by rfl) ⟨604721, by rfl⟩ : syracuseStep 806295 = 1209443) B1209443
theorem B806315 : Blo 802343 806315 := bstep (se 1 (by rfl) ⟨604736, by rfl⟩ : syracuseStep 806315 = 1209473) B1209473
theorem B6180275 : Blo 802343 6180275 := bstep (se 1 (by rfl) ⟨4635206, by rfl⟩ : syracuseStep 6180275 = 9270413) B9270413
theorem B806327 : Blo 802343 806327 := bstep (se 1 (by rfl) ⟨604745, by rfl⟩ : syracuseStep 806327 = 1209491) B1209491
theorem B2117081 : Blo 802343 2117081 := bstep (se 2 (by rfl) ⟨793905, by rfl⟩ : syracuseStep 2117081 = 1587811) B1587811
theorem B5721617 : Blo 802343 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B6114851 : Blo 802343 6114851 := bstep (se 1 (by rfl) ⟨4586138, by rfl⟩ : syracuseStep 6114851 = 9172277) B9172277
theorem B904747 : Blo 802343 904747 := bstep (se 1 (by rfl) ⟨678560, by rfl⟩ : syracuseStep 904747 = 1357121) B1357121
theorem B2575937 : Blo 802343 2575937 := bstep (se 2 (by rfl) ⟨965976, by rfl⟩ : syracuseStep 2575937 = 1931953) B1931953
theorem B904855 : Blo 802343 904855 := bstep (se 1 (by rfl) ⟨678641, by rfl⟩ : syracuseStep 904855 = 1357283) B1357283
theorem B905035 : Blo 802343 905035 := bstep (se 1 (by rfl) ⟨678776, by rfl⟩ : syracuseStep 905035 = 1357553) B1357553
theorem B11587445 : Blo 802343 11587445 := bstep (se 5 (by rfl) ⟨543161, by rfl⟩ : syracuseStep 11587445 = 1086323) B1086323
theorem B3264407 : Blo 802343 3264407 := bstep (se 1 (by rfl) ⟨2448305, by rfl⟩ : syracuseStep 3264407 = 4896611) B4896611
theorem B905143 : Blo 802343 905143 := bstep (se 1 (by rfl) ⟨678857, by rfl⟩ : syracuseStep 905143 = 1357715) B1357715
theorem B905323 : Blo 802343 905323 := bstep (se 1 (by rfl) ⟨678992, by rfl⟩ : syracuseStep 905323 = 1357985) B1357985
theorem B1527923 : Blo 802343 1527923 := bstep (se 1 (by rfl) ⟨1145942, by rfl⟩ : syracuseStep 1527923 = 2291885) B2291885
theorem B905431 : Blo 802343 905431 := bstep (se 1 (by rfl) ⟨679073, by rfl⟩ : syracuseStep 905431 = 1358147) B1358147
theorem B1528075 : Blo 802343 1528075 := bstep (se 1 (by rfl) ⟨1146056, by rfl⟩ : syracuseStep 1528075 = 2292113) B2292113
theorem B5165329 : Blo 802343 5165329 := bstep (se 2 (by rfl) ⟨1936998, by rfl⟩ : syracuseStep 5165329 = 3873997) B3873997
theorem B905611 : Blo 802343 905611 := bstep (se 1 (by rfl) ⟨679208, by rfl⟩ : syracuseStep 905611 = 1358417) B1358417
theorem B905719 : Blo 802343 905719 := bstep (se 1 (by rfl) ⟨679289, by rfl⟩ : syracuseStep 905719 = 1358579) B1358579
theorem B2707991 : Blo 802343 2707991 := bstep (se 1 (by rfl) ⟨2030993, by rfl⟩ : syracuseStep 2707991 = 4061987) B4061987
theorem B3265069 : Blo 802343 3265069 := bstep (se 3 (by rfl) ⟨612200, by rfl⟩ : syracuseStep 3265069 = 1224401) B1224401
theorem B1626713 : Blo 802343 1626713 := bstep (se 2 (by rfl) ⟨610017, by rfl⟩ : syracuseStep 1626713 = 1220035) B1220035
theorem B1528409 : Blo 802343 1528409 := bstep (se 2 (by rfl) ⟨573153, by rfl⟩ : syracuseStep 1528409 = 1146307) B1146307
theorem B905899 : Blo 802343 905899 := bstep (se 1 (by rfl) ⟨679424, by rfl⟩ : syracuseStep 905899 = 1358849) B1358849
theorem B5788421 : Blo 802343 5788421 := bstep (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) B1085329
theorem B906007 : Blo 802343 906007 := bstep (se 1 (by rfl) ⟨679505, by rfl⟩ : syracuseStep 906007 = 1359011) B1359011
theorem B2511667 : Blo 802343 2511667 := bstep (se 1 (by rfl) ⟨1883750, by rfl⟩ : syracuseStep 2511667 = 3767501) B3767501
theorem B906187 : Blo 802343 906187 := bstep (se 1 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 906187 = 1359281) B1359281
theorem B3429337 : Blo 802343 3429337 := bstep (se 2 (by rfl) ⟨1286001, by rfl⟩ : syracuseStep 3429337 = 2572003) B2572003
theorem B2708531 : Blo 802343 2708531 := bstep (se 1 (by rfl) ⟨2031398, by rfl⟩ : syracuseStep 2708531 = 4062797) B4062797
theorem B906295 : Blo 802343 906295 := bstep (se 1 (by rfl) ⟨679721, by rfl⟩ : syracuseStep 906295 = 1359443) B1359443
theorem B5166173 : Blo 802343 5166173 := bstep (se 3 (by rfl) ⟨968657, by rfl⟩ : syracuseStep 5166173 = 1937315) B1937315
theorem B1529047 : Blo 802343 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B906475 : Blo 802343 906475 := bstep (se 1 (by rfl) ⟨679856, by rfl⟩ : syracuseStep 906475 = 1359713) B1359713
theorem B2708801 : Blo 802343 2708801 := bstep (se 2 (by rfl) ⟨1015800, by rfl⟩ : syracuseStep 2708801 = 2031601) B2031601
theorem B906583 : Blo 802343 906583 := bstep (se 1 (by rfl) ⟨679937, by rfl⟩ : syracuseStep 906583 = 1359875) B1359875
theorem B3102097 : Blo 802343 3102097 := bstep (se 2 (by rfl) ⟨1163286, by rfl⟩ : syracuseStep 3102097 = 2326573) B2326573
theorem B906763 : Blo 802343 906763 := bstep (se 1 (by rfl) ⟨680072, by rfl⟩ : syracuseStep 906763 = 1360145) B1360145
theorem B11130443 : Blo 802343 11130443 := bstep (se 1 (by rfl) ⟨8347832, by rfl⟩ : syracuseStep 11130443 = 16695665) B16695665
theorem B2578013 : Blo 802343 2578013 := bstep (se 3 (by rfl) ⟨483377, by rfl⟩ : syracuseStep 2578013 = 966755) B966755
theorem B906871 : Blo 802343 906871 := bstep (se 1 (by rfl) ⟨680153, by rfl⟩ : syracuseStep 906871 = 1360307) B1360307
theorem B907051 : Blo 802343 907051 := bstep (se 1 (by rfl) ⟨680288, by rfl⟩ : syracuseStep 907051 = 1360577) B1360577
theorem B2709341 : Blo 802343 2709341 := bstep (se 3 (by rfl) ⟨508001, by rfl⟩ : syracuseStep 2709341 = 1016003) B1016003
theorem B3430295 : Blo 802343 3430295 := bstep (se 1 (by rfl) ⟨2572721, by rfl⟩ : syracuseStep 3430295 = 5145443) B5145443
theorem B1529867 : Blo 802343 1529867 := bstep (se 1 (by rfl) ⟨1147400, by rfl⟩ : syracuseStep 1529867 = 2294801) B2294801
theorem B1529921 : Blo 802343 1529921 := bstep (se 2 (by rfl) ⟨573720, by rfl⟩ : syracuseStep 1529921 = 1147441) B1147441
theorem B13031725 : Blo 802343 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B4348235 : Blo 802343 4348235 := bstep (se 1 (by rfl) ⟨3261176, by rfl⟩ : syracuseStep 4348235 = 6522353) B6522353
theorem B2579293 : Blo 802343 2579293 := bstep (se 3 (by rfl) ⟨483617, by rfl⟩ : syracuseStep 2579293 = 967235) B967235
theorem B2710475 : Blo 802343 2710475 := bstep (se 1 (by rfl) ⟨2032856, by rfl⟩ : syracuseStep 2710475 = 4065713) B4065713
theorem B1956811 : Blo 802343 1956811 := bstep (se 1 (by rfl) ⟨1467608, by rfl⟩ : syracuseStep 1956811 = 2935217) B2935217
theorem B2448535 : Blo 802343 2448535 := bstep (se 1 (by rfl) ⟨1836401, by rfl⟩ : syracuseStep 2448535 = 3672803) B3672803
theorem B2710745 : Blo 802343 2710745 := bstep (se 2 (by rfl) ⟨1016529, by rfl⟩ : syracuseStep 2710745 = 2033059) B2033059
theorem B2284823 : Blo 802343 2284823 := bstep (se 1 (by rfl) ⟨1713617, by rfl⟩ : syracuseStep 2284823 = 3427235) B3427235
theorem B11132225 : Blo 802343 11132225 := bstep (se 2 (by rfl) ⟨4174584, by rfl⟩ : syracuseStep 11132225 = 8349169) B8349169
theorem B1203545 : Blo 802343 1203545 := bstep (se 2 (by rfl) ⟨451329, by rfl⟩ : syracuseStep 1203545 = 902659) B902659
theorem B1203659 : Blo 802343 1203659 := bstep (se 1 (by rfl) ⟨902744, by rfl⟩ : syracuseStep 1203659 = 1805489) B1805489
theorem B1203671 : Blo 802343 1203671 := bstep (se 1 (by rfl) ⟨902753, by rfl⟩ : syracuseStep 1203671 = 1805507) B1805507
theorem B1203737 : Blo 802343 1203737 := bstep (se 2 (by rfl) ⟨451401, by rfl⟩ : syracuseStep 1203737 = 902803) B902803
theorem B2285131 : Blo 802343 2285131 := bstep (se 1 (by rfl) ⟨1713848, by rfl⟩ : syracuseStep 2285131 = 3427697) B3427697
theorem B4349533 : Blo 802343 4349533 := bstep (se 3 (by rfl) ⟨815537, by rfl⟩ : syracuseStep 4349533 = 1631075) B1631075
theorem B1203851 : Blo 802343 1203851 := bstep (se 1 (by rfl) ⟨902888, by rfl⟩ : syracuseStep 1203851 = 1805777) B1805777
theorem B1203863 : Blo 802343 1203863 := bstep (se 1 (by rfl) ⟨902897, by rfl⟩ : syracuseStep 1203863 = 1805795) B1805795
theorem B1629875 : Blo 802343 1629875 := bstep (se 1 (by rfl) ⟨1222406, by rfl⟩ : syracuseStep 1629875 = 2444813) B2444813
theorem B1203929 : Blo 802343 1203929 := bstep (se 2 (by rfl) ⟨451473, by rfl⟩ : syracuseStep 1203929 = 902947) B902947
theorem B3268313 : Blo 802343 3268313 := bstep (se 2 (by rfl) ⟨1225617, by rfl⟩ : syracuseStep 3268313 = 2451235) B2451235
theorem B1204043 : Blo 802343 1204043 := bstep (se 1 (by rfl) ⟨903032, by rfl⟩ : syracuseStep 1204043 = 1806065) B1806065
theorem B1204055 : Blo 802343 1204055 := bstep (se 1 (by rfl) ⟨903041, by rfl⟩ : syracuseStep 1204055 = 1806083) B1806083
theorem B2285405 : Blo 802343 2285405 := bstep (se 3 (by rfl) ⟨428513, by rfl⟩ : syracuseStep 2285405 = 857027) B857027
theorem B2711447 : Blo 802343 2711447 := bstep (se 1 (by rfl) ⟨2033585, by rfl⟩ : syracuseStep 2711447 = 4067171) B4067171
theorem B1204121 : Blo 802343 1204121 := bstep (se 2 (by rfl) ⟨451545, by rfl⟩ : syracuseStep 1204121 = 903091) B903091
theorem B3432395 : Blo 802343 3432395 := bstep (se 1 (by rfl) ⟨2574296, by rfl⟩ : syracuseStep 3432395 = 5148593) B5148593
theorem B1204235 : Blo 802343 1204235 := bstep (se 1 (by rfl) ⟨903176, by rfl⟩ : syracuseStep 1204235 = 1806353) B1806353
theorem B4644881 : Blo 802343 4644881 := bstep (se 2 (by rfl) ⟨1741830, by rfl⟩ : syracuseStep 4644881 = 3483661) B3483661
theorem B1204247 : Blo 802343 1204247 := bstep (se 1 (by rfl) ⟨903185, by rfl⟩ : syracuseStep 1204247 = 1806371) B1806371
theorem B1204313 : Blo 802343 1204313 := bstep (se 2 (by rfl) ⟨451617, by rfl⟩ : syracuseStep 1204313 = 903235) B903235
theorem B1204427 : Blo 802343 1204427 := bstep (se 1 (by rfl) ⟨903320, by rfl⟩ : syracuseStep 1204427 = 1806641) B1806641
theorem B2318539 : Blo 802343 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B1204439 : Blo 802343 1204439 := bstep (se 1 (by rfl) ⟨903329, by rfl⟩ : syracuseStep 1204439 = 1806659) B1806659
theorem B1204505 : Blo 802343 1204505 := bstep (se 2 (by rfl) ⟨451689, by rfl⟩ : syracuseStep 1204505 = 903379) B903379
theorem B1204619 : Blo 802343 1204619 := bstep (se 1 (by rfl) ⟨903464, by rfl⟩ : syracuseStep 1204619 = 1806929) B1806929
theorem B1204631 : Blo 802343 1204631 := bstep (se 1 (by rfl) ⟨903473, by rfl⟩ : syracuseStep 1204631 = 1806947) B1806947
theorem B2711987 : Blo 802343 2711987 := bstep (se 1 (by rfl) ⟨2033990, by rfl⟩ : syracuseStep 2711987 = 4067981) B4067981
theorem B1204697 : Blo 802343 1204697 := bstep (se 2 (by rfl) ⟨451761, by rfl⟩ : syracuseStep 1204697 = 903523) B903523
theorem B6873605 : Blo 802343 6873605 := bstep (se 4 (by rfl) ⟨644400, by rfl⟩ : syracuseStep 6873605 = 1288801) B1288801
theorem B1204811 : Blo 802343 1204811 := bstep (se 1 (by rfl) ⟨903608, by rfl⟩ : syracuseStep 1204811 = 1807217) B1807217
theorem B1204823 : Blo 802343 1204823 := bstep (se 1 (by rfl) ⟨903617, by rfl⟩ : syracuseStep 1204823 = 1807235) B1807235
theorem B1204889 : Blo 802343 1204889 := bstep (se 2 (by rfl) ⟨451833, by rfl⟩ : syracuseStep 1204889 = 903667) B903667
theorem B1860275 : Blo 802343 1860275 := bstep (se 1 (by rfl) ⟨1395206, by rfl⟩ : syracuseStep 1860275 = 2790413) B2790413
theorem B2712257 : Blo 802343 2712257 := bstep (se 2 (by rfl) ⟨1017096, by rfl⟩ : syracuseStep 2712257 = 2034193) B2034193
theorem B6120197 : Blo 802343 6120197 := bstep (se 4 (by rfl) ⟨573768, by rfl⟩ : syracuseStep 6120197 = 1147537) B1147537
theorem B1205003 : Blo 802343 1205003 := bstep (se 1 (by rfl) ⟨903752, by rfl⟩ : syracuseStep 1205003 = 1807505) B1807505
theorem B1205015 : Blo 802343 1205015 := bstep (se 1 (by rfl) ⟨903761, by rfl⟩ : syracuseStep 1205015 = 1807523) B1807523
theorem B4580171 : Blo 802343 4580171 := bstep (se 1 (by rfl) ⟨3435128, by rfl⟩ : syracuseStep 4580171 = 6870257) B6870257
theorem B1205081 : Blo 802343 1205081 := bstep (se 2 (by rfl) ⟨451905, by rfl⟩ : syracuseStep 1205081 = 903811) B903811
theorem B1074071 : Blo 802343 1074071 := bstep (se 1 (by rfl) ⟨805553, by rfl⟩ : syracuseStep 1074071 = 1611107) B1611107
theorem B26502065 : Blo 802343 26502065 := bstep (se 2 (by rfl) ⟨9938274, by rfl⟩ : syracuseStep 26502065 = 19876549) B19876549
theorem B1205195 : Blo 802343 1205195 := bstep (se 1 (by rfl) ⟨903896, by rfl⟩ : syracuseStep 1205195 = 1807793) B1807793
theorem B1205207 : Blo 802343 1205207 := bstep (se 1 (by rfl) ⟨903905, by rfl⟩ : syracuseStep 1205207 = 1807811) B1807811
theorem B1205273 : Blo 802343 1205273 := bstep (se 2 (by rfl) ⟨451977, by rfl⟩ : syracuseStep 1205273 = 903955) B903955
theorem B1205387 : Blo 802343 1205387 := bstep (se 1 (by rfl) ⟨904040, by rfl⟩ : syracuseStep 1205387 = 1808081) B1808081
theorem B1205399 : Blo 802343 1205399 := bstep (se 1 (by rfl) ⟨904049, by rfl⟩ : syracuseStep 1205399 = 1808099) B1808099
theorem B2319553 : Blo 802343 2319553 := bstep (se 2 (by rfl) ⟨869832, by rfl⟩ : syracuseStep 2319553 = 1739665) B1739665
theorem B1205465 : Blo 802343 1205465 := bstep (se 2 (by rfl) ⟨452049, by rfl⟩ : syracuseStep 1205465 = 904099) B904099
theorem B2712797 : Blo 802343 2712797 := bstep (se 3 (by rfl) ⟨508649, by rfl⟩ : syracuseStep 2712797 = 1017299) B1017299
theorem B1205579 : Blo 802343 1205579 := bstep (se 1 (by rfl) ⟨904184, by rfl⟩ : syracuseStep 1205579 = 1808369) B1808369
theorem B1205591 : Blo 802343 1205591 := bstep (se 1 (by rfl) ⟨904193, by rfl⟩ : syracuseStep 1205591 = 1808387) B1808387
theorem B1205657 : Blo 802343 1205657 := bstep (se 2 (by rfl) ⟨452121, by rfl⟩ : syracuseStep 1205657 = 904243) B904243
theorem B1205771 : Blo 802343 1205771 := bstep (se 1 (by rfl) ⟨904328, by rfl⟩ : syracuseStep 1205771 = 1808657) B1808657
theorem B1205783 : Blo 802343 1205783 := bstep (se 1 (by rfl) ⟨904337, by rfl⟩ : syracuseStep 1205783 = 1808675) B1808675
theorem B3434035 : Blo 802343 3434035 := bstep (se 1 (by rfl) ⟨2575526, by rfl⟩ : syracuseStep 3434035 = 5151053) B5151053
theorem B1205849 : Blo 802343 1205849 := bstep (se 2 (by rfl) ⟨452193, by rfl⟩ : syracuseStep 1205849 = 904387) B904387
theorem B1205963 : Blo 802343 1205963 := bstep (se 1 (by rfl) ⟨904472, by rfl⟩ : syracuseStep 1205963 = 1808945) B1808945
theorem B1205975 : Blo 802343 1205975 := bstep (se 1 (by rfl) ⟨904481, by rfl⟩ : syracuseStep 1205975 = 1808963) B1808963
theorem B1206041 : Blo 802343 1206041 := bstep (se 2 (by rfl) ⟨452265, by rfl⟩ : syracuseStep 1206041 = 904531) B904531
theorem B1206155 : Blo 802343 1206155 := bstep (se 1 (by rfl) ⟨904616, by rfl⟩ : syracuseStep 1206155 = 1809233) B1809233
theorem B2287511 : Blo 802343 2287511 := bstep (se 1 (by rfl) ⟨1715633, by rfl⟩ : syracuseStep 2287511 = 3431267) B3431267
theorem B1206167 : Blo 802343 1206167 := bstep (se 1 (by rfl) ⟨904625, by rfl⟩ : syracuseStep 1206167 = 1809251) B1809251
theorem B1206233 : Blo 802343 1206233 := bstep (se 2 (by rfl) ⟨452337, by rfl⟩ : syracuseStep 1206233 = 904675) B904675
theorem B1206347 : Blo 802343 1206347 := bstep (se 1 (by rfl) ⟨904760, by rfl⟩ : syracuseStep 1206347 = 1809521) B1809521
theorem B1206359 : Blo 802343 1206359 := bstep (se 1 (by rfl) ⟨904769, by rfl⟩ : syracuseStep 1206359 = 1809539) B1809539
theorem B1206425 : Blo 802343 1206425 := bstep (se 2 (by rfl) ⟨452409, by rfl⟩ : syracuseStep 1206425 = 904819) B904819
theorem B3434669 : Blo 802343 3434669 := bstep (se 3 (by rfl) ⟨644000, by rfl⟩ : syracuseStep 3434669 = 1288001) B1288001
theorem B1206539 : Blo 802343 1206539 := bstep (se 1 (by rfl) ⟨904904, by rfl⟩ : syracuseStep 1206539 = 1809809) B1809809
theorem B1206551 : Blo 802343 1206551 := bstep (se 1 (by rfl) ⟨904913, by rfl⟩ : syracuseStep 1206551 = 1809827) B1809827
theorem B2713931 : Blo 802343 2713931 := bstep (se 1 (by rfl) ⟨2035448, by rfl⟩ : syracuseStep 2713931 = 4070897) B4070897
theorem B1632599 : Blo 802343 1632599 := bstep (se 1 (by rfl) ⟨1224449, by rfl⟩ : syracuseStep 1632599 = 2448899) B2448899
theorem B1206617 : Blo 802343 1206617 := bstep (se 2 (by rfl) ⟨452481, by rfl⟩ : syracuseStep 1206617 = 904963) B904963
theorem B1206731 : Blo 802343 1206731 := bstep (se 1 (by rfl) ⟨905048, by rfl⟩ : syracuseStep 1206731 = 1810097) B1810097
theorem B1206743 : Blo 802343 1206743 := bstep (se 1 (by rfl) ⟨905057, by rfl⟩ : syracuseStep 1206743 = 1810115) B1810115
theorem B1206809 : Blo 802343 1206809 := bstep (se 2 (by rfl) ⟨452553, by rfl⟩ : syracuseStep 1206809 = 905107) B905107
theorem B2714201 : Blo 802343 2714201 := bstep (se 2 (by rfl) ⟨1017825, by rfl⟩ : syracuseStep 2714201 = 2035651) B2035651
theorem B49572445 : Blo 802343 49572445 := bstep (se 3 (by rfl) ⟨9294833, by rfl⟩ : syracuseStep 49572445 = 18589667) B18589667
theorem B1206923 : Blo 802343 1206923 := bstep (se 1 (by rfl) ⟨905192, by rfl⟩ : syracuseStep 1206923 = 1810385) B1810385
theorem B1206935 : Blo 802343 1206935 := bstep (se 1 (by rfl) ⟨905201, by rfl⟩ : syracuseStep 1206935 = 1810403) B1810403
theorem B2288321 : Blo 802343 2288321 := bstep (se 2 (by rfl) ⟨858120, by rfl⟩ : syracuseStep 2288321 = 1716241) B1716241
theorem B1207001 : Blo 802343 1207001 := bstep (se 2 (by rfl) ⟨452625, by rfl⟩ : syracuseStep 1207001 = 905251) B905251
theorem B813835 : Blo 802343 813835 := bstep (se 1 (by rfl) ⟨610376, by rfl⟩ : syracuseStep 813835 = 1220753) B1220753
theorem B1207115 : Blo 802343 1207115 := bstep (se 1 (by rfl) ⟨905336, by rfl⟩ : syracuseStep 1207115 = 1810673) B1810673
theorem B1207127 : Blo 802343 1207127 := bstep (se 1 (by rfl) ⟨905345, by rfl⟩ : syracuseStep 1207127 = 1810691) B1810691
theorem B1207193 : Blo 802343 1207193 := bstep (se 2 (by rfl) ⟨452697, by rfl⟩ : syracuseStep 1207193 = 905395) B905395
theorem B1633241 : Blo 802343 1633241 := bstep (se 2 (by rfl) ⟨612465, by rfl⟩ : syracuseStep 1633241 = 1224931) B1224931
theorem B1207307 : Blo 802343 1207307 := bstep (se 1 (by rfl) ⟨905480, by rfl⟩ : syracuseStep 1207307 = 1810961) B1810961
theorem B1207319 : Blo 802343 1207319 := bstep (se 1 (by rfl) ⟨905489, by rfl⟩ : syracuseStep 1207319 = 1810979) B1810979
theorem B4713547 : Blo 802343 4713547 := bstep (se 1 (by rfl) ⟨3535160, by rfl⟩ : syracuseStep 4713547 = 7070321) B7070321
theorem B1928281 : Blo 802343 1928281 := bstep (se 2 (by rfl) ⟨723105, by rfl⟩ : syracuseStep 1928281 = 1446211) B1446211
theorem B1207385 : Blo 802343 1207385 := bstep (se 2 (by rfl) ⟨452769, by rfl⟩ : syracuseStep 1207385 = 905539) B905539
theorem B6122627 : Blo 802343 6122627 := bstep (se 1 (by rfl) ⟨4591970, by rfl⟩ : syracuseStep 6122627 = 9183941) B9183941
theorem B1633459 : Blo 802343 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B1207499 : Blo 802343 1207499 := bstep (se 1 (by rfl) ⟨905624, by rfl⟩ : syracuseStep 1207499 = 1811249) B1811249
theorem B1207511 : Blo 802343 1207511 := bstep (se 1 (by rfl) ⟨905633, by rfl⟩ : syracuseStep 1207511 = 1811267) B1811267
theorem B2714903 : Blo 802343 2714903 := bstep (se 1 (by rfl) ⟨2036177, by rfl⟩ : syracuseStep 2714903 = 4072355) B4072355
theorem B1207577 : Blo 802343 1207577 := bstep (se 2 (by rfl) ⟨452841, by rfl⟩ : syracuseStep 1207577 = 905683) B905683
theorem B1207691 : Blo 802343 1207691 := bstep (se 1 (by rfl) ⟨905768, by rfl⟩ : syracuseStep 1207691 = 1811537) B1811537
theorem B1207703 : Blo 802343 1207703 := bstep (se 1 (by rfl) ⟨905777, by rfl⟩ : syracuseStep 1207703 = 1811555) B1811555
theorem B1928627 : Blo 802343 1928627 := bstep (se 1 (by rfl) ⟨1446470, by rfl⟩ : syracuseStep 1928627 = 2892941) B2892941
theorem B1207769 : Blo 802343 1207769 := bstep (se 2 (by rfl) ⟨452913, by rfl⟩ : syracuseStep 1207769 = 905827) B905827
theorem B1207883 : Blo 802343 1207883 := bstep (se 1 (by rfl) ⟨905912, by rfl⟩ : syracuseStep 1207883 = 1811825) B1811825
theorem B1207895 : Blo 802343 1207895 := bstep (se 1 (by rfl) ⟨905921, by rfl⟩ : syracuseStep 1207895 = 1811843) B1811843
theorem B1207961 : Blo 802343 1207961 := bstep (se 2 (by rfl) ⟨452985, by rfl⟩ : syracuseStep 1207961 = 905971) B905971
theorem B1928897 : Blo 802343 1928897 := bstep (se 2 (by rfl) ⟨723336, by rfl⟩ : syracuseStep 1928897 = 1446673) B1446673
theorem B1208075 : Blo 802343 1208075 := bstep (se 1 (by rfl) ⟨906056, by rfl⟩ : syracuseStep 1208075 = 1812113) B1812113
theorem B1208087 : Blo 802343 1208087 := bstep (se 1 (by rfl) ⟨906065, by rfl⟩ : syracuseStep 1208087 = 1812131) B1812131
theorem B2715443 : Blo 802343 2715443 := bstep (se 1 (by rfl) ⟨2036582, by rfl⟩ : syracuseStep 2715443 = 4073165) B4073165
theorem B4353857 : Blo 802343 4353857 := bstep (se 2 (by rfl) ⟨1632696, by rfl⟩ : syracuseStep 4353857 = 3265393) B3265393
theorem B1208153 : Blo 802343 1208153 := bstep (se 2 (by rfl) ⟨453057, by rfl⟩ : syracuseStep 1208153 = 906115) B906115
theorem B6877021 : Blo 802343 6877021 := bstep (se 3 (by rfl) ⟨1289441, by rfl⟩ : syracuseStep 6877021 = 2578883) B2578883
theorem B7335859 : Blo 802343 7335859 := bstep (se 1 (by rfl) ⟨5501894, by rfl⟩ : syracuseStep 7335859 = 11003789) B11003789
theorem B1208267 : Blo 802343 1208267 := bstep (se 1 (by rfl) ⟨906200, by rfl⟩ : syracuseStep 1208267 = 1812401) B1812401
theorem B1208279 : Blo 802343 1208279 := bstep (se 1 (by rfl) ⟨906209, by rfl⟩ : syracuseStep 1208279 = 1812419) B1812419
theorem B1208345 : Blo 802343 1208345 := bstep (se 2 (by rfl) ⟨453129, by rfl⟩ : syracuseStep 1208345 = 906259) B906259
theorem B2715713 : Blo 802343 2715713 := bstep (se 2 (by rfl) ⟨1018392, by rfl⟩ : syracuseStep 2715713 = 2036785) B2036785
theorem B11006027 : Blo 802343 11006027 := bstep (se 1 (by rfl) ⟨8254520, by rfl⟩ : syracuseStep 11006027 = 16509041) B16509041
theorem B4124803 : Blo 802343 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B1208459 : Blo 802343 1208459 := bstep (se 1 (by rfl) ⟨906344, by rfl⟩ : syracuseStep 1208459 = 1812689) B1812689
theorem B1208471 : Blo 802343 1208471 := bstep (se 1 (by rfl) ⟨906353, by rfl⟩ : syracuseStep 1208471 = 1812707) B1812707
theorem B1208537 : Blo 802343 1208537 := bstep (se 2 (by rfl) ⟨453201, by rfl⟩ : syracuseStep 1208537 = 906403) B906403
theorem B2289971 : Blo 802343 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B2289995 : Blo 802343 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B1208651 : Blo 802343 1208651 := bstep (se 1 (by rfl) ⟨906488, by rfl⟩ : syracuseStep 1208651 = 1812977) B1812977
theorem B1208663 : Blo 802343 1208663 := bstep (se 1 (by rfl) ⟨906497, by rfl⟩ : syracuseStep 1208663 = 1812995) B1812995
theorem B2748761 : Blo 802343 2748761 := bstep (se 2 (by rfl) ⟨1030785, by rfl⟩ : syracuseStep 2748761 = 2061571) B2061571
theorem B1208729 : Blo 802343 1208729 := bstep (se 2 (by rfl) ⟨453273, by rfl⟩ : syracuseStep 1208729 = 906547) B906547
theorem B1470935 : Blo 802343 1470935 := bstep (se 1 (by rfl) ⟨1103201, by rfl⟩ : syracuseStep 1470935 = 2206403) B2206403
theorem B1208843 : Blo 802343 1208843 := bstep (se 1 (by rfl) ⟨906632, by rfl⟩ : syracuseStep 1208843 = 1813265) B1813265
theorem B1208855 : Blo 802343 1208855 := bstep (se 1 (by rfl) ⟨906641, by rfl⟩ : syracuseStep 1208855 = 1813283) B1813283
theorem B1208921 : Blo 802343 1208921 := bstep (se 2 (by rfl) ⟨453345, by rfl⟩ : syracuseStep 1208921 = 906691) B906691
theorem B2716253 : Blo 802343 2716253 := bstep (se 3 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 2716253 = 1018595) B1018595
theorem B1209035 : Blo 802343 1209035 := bstep (se 1 (by rfl) ⟨906776, by rfl⟩ : syracuseStep 1209035 = 1813553) B1813553
theorem B1209047 : Blo 802343 1209047 := bstep (se 1 (by rfl) ⟨906785, by rfl⟩ : syracuseStep 1209047 = 1813571) B1813571
theorem B1209113 : Blo 802343 1209113 := bstep (se 2 (by rfl) ⟨453417, by rfl⟩ : syracuseStep 1209113 = 906835) B906835
theorem B815959 : Blo 802343 815959 := bstep (se 1 (by rfl) ⟨611969, by rfl⟩ : syracuseStep 815959 = 1223939) B1223939
theorem B1209227 : Blo 802343 1209227 := bstep (se 1 (by rfl) ⟨906920, by rfl⟩ : syracuseStep 1209227 = 1813841) B1813841
theorem B1209239 : Blo 802343 1209239 := bstep (se 1 (by rfl) ⟨906929, by rfl⟩ : syracuseStep 1209239 = 1813859) B1813859
theorem B1143767 : Blo 802343 1143767 := bstep (se 1 (by rfl) ⟨857825, by rfl⟩ : syracuseStep 1143767 = 1715651) B1715651
theorem B1209305 : Blo 802343 1209305 := bstep (se 2 (by rfl) ⟨453489, by rfl⟩ : syracuseStep 1209305 = 906979) B906979
theorem B5141569 : Blo 802343 5141569 := bstep (se 2 (by rfl) ⟨1928088, by rfl⟩ : syracuseStep 5141569 = 3856177) B3856177
theorem B1209419 : Blo 802343 1209419 := bstep (se 1 (by rfl) ⟨907064, by rfl⟩ : syracuseStep 1209419 = 1814129) B1814129
theorem B1209431 : Blo 802343 1209431 := bstep (se 1 (by rfl) ⟨907073, by rfl⟩ : syracuseStep 1209431 = 1814147) B1814147
theorem B2290781 : Blo 802343 2290781 := bstep (se 3 (by rfl) ⟨429521, by rfl⟩ : syracuseStep 2290781 = 859043) B859043
theorem B1209497 : Blo 802343 1209497 := bstep (se 2 (by rfl) ⟨453561, by rfl⟩ : syracuseStep 1209497 = 907123) B907123
theorem B4355479 : Blo 802343 4355479 := bstep (se 1 (by rfl) ⟨3266609, by rfl⟩ : syracuseStep 4355479 = 6533219) B6533219
theorem B1570291 : Blo 802343 1570291 := bstep (se 1 (by rfl) ⟨1177718, by rfl⟩ : syracuseStep 1570291 = 2355437) B2355437
theorem B2717387 : Blo 802343 2717387 := bstep (se 1 (by rfl) ⟨2038040, by rfl⟩ : syracuseStep 2717387 = 4076081) B4076081
theorem B3438359 : Blo 802343 3438359 := bstep (se 1 (by rfl) ⟨2578769, by rfl⟩ : syracuseStep 3438359 = 5157539) B5157539
theorem B3667801 : Blo 802343 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B2717657 : Blo 802343 2717657 := bstep (se 2 (by rfl) ⟨1019121, by rfl⟩ : syracuseStep 2717657 = 2038243) B2038243
theorem B1833025 : Blo 802343 1833025 := bstep (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) B1374769
theorem B4356625 : Blo 802343 4356625 := bstep (se 2 (by rfl) ⟨1633734, by rfl⟩ : syracuseStep 4356625 = 3267469) B3267469
theorem B5306945 : Blo 802343 5306945 := bstep (se 2 (by rfl) ⟨1990104, by rfl⟩ : syracuseStep 5306945 = 3980209) B3980209
theorem B4356709 : Blo 802343 4356709 := bstep (se 4 (by rfl) ⟨408441, by rfl⟩ : syracuseStep 4356709 = 816883) B816883
theorem B2718359 : Blo 802343 2718359 := bstep (se 1 (by rfl) ⟨2038769, by rfl⟩ : syracuseStep 2718359 = 4077539) B4077539
theorem B3668753 : Blo 802343 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B2292569 : Blo 802343 2292569 := bstep (se 2 (by rfl) ⟨859713, by rfl⟩ : syracuseStep 2292569 = 1719427) B1719427
theorem B3865751 : Blo 802343 3865751 := bstep (se 1 (by rfl) ⟨2899313, by rfl⟩ : syracuseStep 3865751 = 5798627) B5798627
theorem B2292887 : Blo 802343 2292887 := bstep (se 1 (by rfl) ⟨1719665, by rfl⟩ : syracuseStep 2292887 = 3439331) B3439331
theorem B2718899 : Blo 802343 2718899 := bstep (se 1 (by rfl) ⟨2039174, by rfl⟩ : syracuseStep 2718899 = 4078349) B4078349
theorem B3046673 : Blo 802343 3046673 := bstep (se 2 (by rfl) ⟨1142502, by rfl⟩ : syracuseStep 3046673 = 2285005) B2285005
theorem B1834433 : Blo 802343 1834433 := bstep (se 2 (by rfl) ⟨687912, by rfl⟩ : syracuseStep 1834433 = 1375825) B1375825
theorem B2719169 : Blo 802343 2719169 := bstep (se 2 (by rfl) ⟨1019688, by rfl⟩ : syracuseStep 2719169 = 2039377) B2039377
theorem B2031065 : Blo 802343 2031065 := bstep (se 2 (by rfl) ⟨761649, by rfl⟩ : syracuseStep 2031065 = 1523299) B1523299
theorem B3047129 : Blo 802343 3047129 := bstep (se 2 (by rfl) ⟨1142673, by rfl⟩ : syracuseStep 3047129 = 2285347) B2285347
theorem B1146649 : Blo 802343 1146649 := bstep (se 2 (by rfl) ⟨429993, by rfl⟩ : syracuseStep 1146649 = 859987) B859987
theorem B3047341 : Blo 802343 3047341 := bstep (se 3 (by rfl) ⟨571376, by rfl⟩ : syracuseStep 3047341 = 1142753) B1142753
theorem B2293697 : Blo 802343 2293697 := bstep (se 2 (by rfl) ⟨860136, by rfl⟩ : syracuseStep 2293697 = 1720273) B1720273
theorem B2719709 : Blo 802343 2719709 := bstep (se 3 (by rfl) ⟨509945, by rfl⟩ : syracuseStep 2719709 = 1019891) B1019891
theorem B2293879 : Blo 802343 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B2031763 : Blo 802343 2031763 := bstep (se 1 (by rfl) ⟨1523822, by rfl⟩ : syracuseStep 2031763 = 3047645) B3047645
theorem B2293913 : Blo 802343 2293913 := bstep (se 2 (by rfl) ⟨860217, by rfl⟩ : syracuseStep 2293913 = 1720435) B1720435
theorem B10322093 : Blo 802343 10322093 := bstep (se 3 (by rfl) ⟨1935392, by rfl⟩ : syracuseStep 10322093 = 3870785) B3870785
theorem B8683757 : Blo 802343 8683757 := bstep (se 3 (by rfl) ⟨1628204, by rfl⟩ : syracuseStep 8683757 = 3256409) B3256409
theorem B1147127 : Blo 802343 1147127 := bstep (se 1 (by rfl) ⟨860345, by rfl⟩ : syracuseStep 1147127 = 1720691) B1720691
theorem B2294027 : Blo 802343 2294027 := bstep (se 1 (by rfl) ⟨1720520, by rfl⟩ : syracuseStep 2294027 = 3441041) B3441041
theorem B2031905 : Blo 802343 2031905 := bstep (se 2 (by rfl) ⟨761964, by rfl⟩ : syracuseStep 2031905 = 1523929) B1523929
theorem B2720033 : Blo 802343 2720033 := bstep (se 2 (by rfl) ⟨1020012, by rfl⟩ : syracuseStep 2720033 = 2040025) B2040025
theorem B3047827 : Blo 802343 3047827 := bstep (se 1 (by rfl) ⟨2285870, by rfl⟩ : syracuseStep 3047827 = 4571741) B4571741
theorem B4587961 : Blo 802343 4587961 := bstep (se 2 (by rfl) ⟨1720485, by rfl⟩ : syracuseStep 4587961 = 3440971) B3440971
theorem B1147321 : Blo 802343 1147321 := bstep (se 2 (by rfl) ⟨430245, by rfl⟩ : syracuseStep 1147321 = 860491) B860491
theorem B14680541 : Blo 802343 14680541 := bstep (se 3 (by rfl) ⟨2752601, by rfl⟩ : syracuseStep 14680541 = 5505203) B5505203
theorem B1016327 : Blo 802343 1016327 := bstep (se 1 (by rfl) ⟨762245, by rfl⟩ : syracuseStep 1016327 = 1524491) B1524491
theorem B6521573 : Blo 802343 6521573 := bstep (se 4 (by rfl) ⟨611397, by rfl⟩ : syracuseStep 6521573 = 1222795) B1222795
theorem B4653883 : Blo 802343 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B2720627 : Blo 802343 2720627 := bstep (se 1 (by rfl) ⟨2040470, by rfl⟩ : syracuseStep 2720627 = 4080941) B4080941
theorem B1016975 : Blo 802343 1016975 := bstep (se 1 (by rfl) ⟨762731, by rfl⟩ : syracuseStep 1016975 = 1525463) B1525463
theorem B2032897 : Blo 802343 2032897 := bstep (se 2 (by rfl) ⟨762336, by rfl⟩ : syracuseStep 2032897 = 1524673) B1524673
theorem B3868019 : Blo 802343 3868019 := bstep (se 1 (by rfl) ⟨2901014, by rfl⟩ : syracuseStep 3868019 = 5802029) B5802029
theorem B2295155 : Blo 802343 2295155 := bstep (se 1 (by rfl) ⟨1721366, by rfl⟩ : syracuseStep 2295155 = 3442733) B3442733
theorem B4130201 : Blo 802343 4130201 := bstep (se 2 (by rfl) ⟨1548825, by rfl⟩ : syracuseStep 4130201 = 3097651) B3097651
theorem B3671639 : Blo 802343 3671639 := bstep (se 1 (by rfl) ⟨2753729, by rfl⟩ : syracuseStep 3671639 = 5507459) B5507459
theorem B2295553 : Blo 802343 2295553 := bstep (se 2 (by rfl) ⟨860832, by rfl⟩ : syracuseStep 2295553 = 1721665) B1721665
theorem B2295611 : Blo 802343 2295611 := bstep (se 1 (by rfl) ⟨1721708, by rfl⟩ : syracuseStep 2295611 = 3443417) B3443417
theorem B2033495 : Blo 802343 2033495 := bstep (se 1 (by rfl) ⟨1525121, by rfl⟩ : syracuseStep 2033495 = 3050243) B3050243
theorem B4065227 : Blo 802343 4065227 := bstep (se 1 (by rfl) ⟨3048920, by rfl⟩ : syracuseStep 4065227 = 6097841) B6097841
theorem B2033707 : Blo 802343 2033707 := bstep (se 1 (by rfl) ⟨1525280, by rfl⟩ : syracuseStep 2033707 = 3050561) B3050561
theorem B3049559 : Blo 802343 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B2033849 : Blo 802343 2033849 := bstep (se 2 (by rfl) ⟨762693, by rfl⟩ : syracuseStep 2033849 = 1525387) B1525387
theorem B4065551 : Blo 802343 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B1411387 : Blo 802343 1411387 := bstep (se 1 (by rfl) ⟨1058540, by rfl⟩ : syracuseStep 1411387 = 2117081) B2117081
theorem B3050045 : Blo 802343 3050045 := bstep (se 3 (by rfl) ⟨571883, by rfl⟩ : syracuseStep 3050045 = 1143767) B1143767
theorem B3869441 : Blo 802343 3869441 := bstep (se 2 (by rfl) ⟨1451040, by rfl⟩ : syracuseStep 3869441 = 2902081) B2902081
theorem B1805327 : Blo 802343 1805327 := bstep (se 1 (by rfl) ⟨1353995, by rfl⟩ : syracuseStep 1805327 = 2707991) B2707991
theorem B3443741 : Blo 802343 3443741 := bstep (se 3 (by rfl) ⟨645701, by rfl⟩ : syracuseStep 3443741 = 1291403) B1291403
theorem B1805345 : Blo 802343 1805345 := bstep (se 2 (by rfl) ⟨677004, by rfl⟩ : syracuseStep 1805345 = 1354009) B1354009
theorem B1084475 : Blo 802343 1084475 := bstep (se 1 (by rfl) ⟨813356, by rfl⟩ : syracuseStep 1084475 = 1626713) B1626713
theorem B2034841 : Blo 802343 2034841 := bstep (se 2 (by rfl) ⟨763065, by rfl⟩ : syracuseStep 2034841 = 1526131) B1526131
theorem B23235781 : Blo 802343 23235781 := bstep (se 4 (by rfl) ⟨2178354, by rfl⟩ : syracuseStep 23235781 = 4356709) B4356709
theorem B1936585 : Blo 802343 1936585 := bstep (se 2 (by rfl) ⟨726219, by rfl⟩ : syracuseStep 1936585 = 1452439) B1452439
theorem B2035003 : Blo 802343 2035003 := bstep (se 1 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 2035003 = 3052505) B3052505
theorem B1805687 : Blo 802343 1805687 := bstep (se 1 (by rfl) ⟨1354265, by rfl⟩ : syracuseStep 1805687 = 2708531) B2708531
theorem B3444115 : Blo 802343 3444115 := bstep (se 1 (by rfl) ⟨2583086, by rfl⟩ : syracuseStep 3444115 = 5166173) B5166173
theorem B2035145 : Blo 802343 2035145 := bstep (se 2 (by rfl) ⟨763179, by rfl⟩ : syracuseStep 2035145 = 1526359) B1526359
theorem B66096593 : Blo 802343 66096593 := bstep (se 2 (by rfl) ⟨24786222, by rfl⟩ : syracuseStep 66096593 = 49572445) B49572445
theorem B1805867 : Blo 802343 1805867 := bstep (se 1 (by rfl) ⟨1354400, by rfl⟩ : syracuseStep 1805867 = 2708801) B2708801
theorem B9146033 : Blo 802343 9146033 := bstep (se 2 (by rfl) ⟨3429762, by rfl⟩ : syracuseStep 9146033 = 6859525) B6859525
theorem B1085113 : Blo 802343 1085113 := bstep (se 2 (by rfl) ⟨406917, by rfl⟩ : syracuseStep 1085113 = 813835) B813835
theorem B4067009 : Blo 802343 4067009 := bstep (se 2 (by rfl) ⟨1525128, by rfl⟩ : syracuseStep 4067009 = 3050257) B3050257
theorem B2035489 : Blo 802343 2035489 := bstep (se 2 (by rfl) ⟨763308, by rfl⟩ : syracuseStep 2035489 = 1526617) B1526617
theorem B1806227 : Blo 802343 1806227 := bstep (se 1 (by rfl) ⟨1354670, by rfl⟩ : syracuseStep 1806227 = 2709341) B2709341
theorem B1806281 : Blo 802343 1806281 := bstep (se 2 (by rfl) ⟨677355, by rfl⟩ : syracuseStep 1806281 = 1354711) B1354711
theorem B1019947 : Blo 802343 1019947 := bstep (se 1 (by rfl) ⟨764960, by rfl⟩ : syracuseStep 1019947 = 1529921) B1529921
theorem B2036087 : Blo 802343 2036087 := bstep (se 1 (by rfl) ⟨1527065, by rfl⟩ : syracuseStep 2036087 = 3054131) B3054131
theorem B1806983 : Blo 802343 1806983 := bstep (se 1 (by rfl) ⟨1355237, by rfl⟩ : syracuseStep 1806983 = 2710475) B2710475
theorem B1807163 : Blo 802343 1807163 := bstep (se 1 (by rfl) ⟨1355372, by rfl⟩ : syracuseStep 1807163 = 2710745) B2710745
theorem B1807289 : Blo 802343 1807289 := bstep (se 2 (by rfl) ⟨677733, by rfl⟩ : syracuseStep 1807289 = 1355467) B1355467
theorem B4068305 : Blo 802343 4068305 := bstep (se 2 (by rfl) ⟨1525614, by rfl⟩ : syracuseStep 4068305 = 3051229) B3051229
theorem B3871709 : Blo 802343 3871709 := bstep (se 3 (by rfl) ⟨725945, by rfl⟩ : syracuseStep 3871709 = 1451891) B1451891
theorem B1086583 : Blo 802343 1086583 := bstep (se 1 (by rfl) ⟨814937, by rfl⟩ : syracuseStep 1086583 = 1629875) B1629875
theorem B1807631 : Blo 802343 1807631 := bstep (se 1 (by rfl) ⟨1355723, by rfl⟩ : syracuseStep 1807631 = 2711447) B2711447
theorem B1807649 : Blo 802343 1807649 := bstep (se 2 (by rfl) ⟨677868, by rfl⟩ : syracuseStep 1807649 = 1355737) B1355737
theorem B3872323 : Blo 802343 3872323 := bstep (se 1 (by rfl) ⟨2904242, by rfl⟩ : syracuseStep 3872323 = 5808485) B5808485
theorem B1807991 : Blo 802343 1807991 := bstep (se 1 (by rfl) ⟨1355993, by rfl⟩ : syracuseStep 1807991 = 2711987) B2711987
theorem B2037383 : Blo 802343 2037383 := bstep (se 1 (by rfl) ⟨1528037, by rfl⟩ : syracuseStep 2037383 = 3056075) B3056075
theorem B2037433 : Blo 802343 2037433 := bstep (se 2 (by rfl) ⟨764037, by rfl⟩ : syracuseStep 2037433 = 1528075) B1528075
theorem B6887105 : Blo 802343 6887105 := bstep (se 2 (by rfl) ⟨2582664, by rfl⟩ : syracuseStep 6887105 = 5165329) B5165329
theorem B156243653 : Blo 802343 156243653 := bstep (se 4 (by rfl) ⟨14647842, by rfl⟩ : syracuseStep 156243653 = 29295685) B29295685
theorem B1808171 : Blo 802343 1808171 := bstep (se 1 (by rfl) ⟨1356128, by rfl⟩ : syracuseStep 1808171 = 2712257) B2712257
theorem B3053447 : Blo 802343 3053447 := bstep (se 1 (by rfl) ⟨2290085, by rfl⟩ : syracuseStep 3053447 = 4580171) B4580171
theorem B17668043 : Blo 802343 17668043 := bstep (se 1 (by rfl) ⟨13251032, by rfl⟩ : syracuseStep 17668043 = 26502065) B26502065
theorem B1808531 : Blo 802343 1808531 := bstep (se 1 (by rfl) ⟨1356398, by rfl⟩ : syracuseStep 1808531 = 2712797) B2712797
theorem B1808585 : Blo 802343 1808585 := bstep (se 2 (by rfl) ⟨678219, by rfl⟩ : syracuseStep 1808585 = 1356439) B1356439
theorem B2038031 : Blo 802343 2038031 := bstep (se 1 (by rfl) ⟨1528523, by rfl⟩ : syracuseStep 2038031 = 3057047) B3057047
theorem B6855425 : Blo 802343 6855425 := bstep (se 2 (by rfl) ⟨2570784, by rfl⟩ : syracuseStep 6855425 = 5141569) B5141569
theorem B2169611 : Blo 802343 2169611 := bstep (se 1 (by rfl) ⟨1627208, by rfl⟩ : syracuseStep 2169611 = 3254417) B3254417
theorem B1547041 : Blo 802343 1547041 := bstep (se 2 (by rfl) ⟨580140, by rfl⟩ : syracuseStep 1547041 = 1160281) B1160281
theorem B1809287 : Blo 802343 1809287 := bstep (se 1 (by rfl) ⟨1356965, by rfl⟩ : syracuseStep 1809287 = 2713931) B2713931
theorem B1088399 : Blo 802343 1088399 := bstep (se 1 (by rfl) ⟨816299, by rfl⟩ : syracuseStep 1088399 = 1632599) B1632599
theorem B2038729 : Blo 802343 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B4070411 : Blo 802343 4070411 := bstep (se 1 (by rfl) ⟨3052808, by rfl⟩ : syracuseStep 4070411 = 6105617) B6105617
theorem B1809467 : Blo 802343 1809467 := bstep (se 1 (by rfl) ⟨1357100, by rfl⟩ : syracuseStep 1809467 = 2714201) B2714201
theorem B2038871 : Blo 802343 2038871 := bstep (se 1 (by rfl) ⟨1529153, by rfl⟩ : syracuseStep 2038871 = 3058307) B3058307
theorem B4070573 : Blo 802343 4070573 := bstep (se 3 (by rfl) ⟨763232, by rfl⟩ : syracuseStep 4070573 = 1526465) B1526465
theorem B1809593 : Blo 802343 1809593 := bstep (se 2 (by rfl) ⟨678597, by rfl⟩ : syracuseStep 1809593 = 1357195) B1357195
theorem B4136129 : Blo 802343 4136129 := bstep (se 2 (by rfl) ⟨1551048, by rfl⟩ : syracuseStep 4136129 = 3102097) B3102097
theorem B5807305 : Blo 802343 5807305 := bstep (se 2 (by rfl) ⟨2177739, by rfl⟩ : syracuseStep 5807305 = 4355479) B4355479
theorem B1809935 : Blo 802343 1809935 := bstep (se 1 (by rfl) ⟨1357451, by rfl⟩ : syracuseStep 1809935 = 2714903) B2714903
theorem B1809953 : Blo 802343 1809953 := bstep (se 2 (by rfl) ⟨678732, by rfl⟩ : syracuseStep 1809953 = 1357465) B1357465
theorem B1285751 : Blo 802343 1285751 := bstep (se 1 (by rfl) ⟨964313, by rfl⟩ : syracuseStep 1285751 = 1928627) B1928627
theorem B4890401 : Blo 802343 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B1285931 : Blo 802343 1285931 := bstep (se 1 (by rfl) ⟨964448, by rfl⟩ : syracuseStep 1285931 = 1928897) B1928897
theorem B1810295 : Blo 802343 1810295 := bstep (se 1 (by rfl) ⟨1357721, by rfl⟩ : syracuseStep 1810295 = 2715443) B2715443
theorem B1810475 : Blo 802343 1810475 := bstep (se 1 (by rfl) ⟨1357856, by rfl⟩ : syracuseStep 1810475 = 2715713) B2715713
theorem B860431 : Blo 802343 860431 := bstep (se 1 (by rfl) ⟨645323, by rfl⟩ : syracuseStep 860431 = 1290647) B1290647
theorem B17375633 : Blo 802343 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B1810835 : Blo 802343 1810835 := bstep (se 1 (by rfl) ⟨1358126, by rfl⟩ : syracuseStep 1810835 = 2716253) B2716253
theorem B1810889 : Blo 802343 1810889 := bstep (se 2 (by rfl) ⟨679083, by rfl⟩ : syracuseStep 1810889 = 1358167) B1358167
theorem B9904589 : Blo 802343 9904589 := bstep (se 3 (by rfl) ⟨1857110, by rfl⟩ : syracuseStep 9904589 = 3714221) B3714221
theorem B860807 : Blo 802343 860807 := bstep (se 1 (by rfl) ⟨645605, by rfl⟩ : syracuseStep 860807 = 1291211) B1291211
theorem B5808833 : Blo 802343 5808833 := bstep (se 2 (by rfl) ⟨2178312, by rfl⟩ : syracuseStep 5808833 = 4356625) B4356625
theorem B4072193 : Blo 802343 4072193 := bstep (se 2 (by rfl) ⟨1527072, by rfl⟩ : syracuseStep 4072193 = 3054145) B3054145
theorem B1450811 : Blo 802343 1450811 := bstep (se 1 (by rfl) ⟨1088108, by rfl⟩ : syracuseStep 1450811 = 2176217) B2176217
theorem B2040947 : Blo 802343 2040947 := bstep (se 1 (by rfl) ⟨1530710, by rfl⟩ : syracuseStep 2040947 = 3061421) B3061421
theorem B1811591 : Blo 802343 1811591 := bstep (se 1 (by rfl) ⟨1358693, by rfl⟩ : syracuseStep 1811591 = 2717387) B2717387
theorem B1811771 : Blo 802343 1811771 := bstep (se 1 (by rfl) ⟨1358828, by rfl⟩ : syracuseStep 1811771 = 2717657) B2717657
theorem B2893171 : Blo 802343 2893171 := bstep (se 1 (by rfl) ⟨2169878, by rfl⟩ : syracuseStep 2893171 = 4339757) B4339757
theorem B1811897 : Blo 802343 1811897 := bstep (se 2 (by rfl) ⟨679461, by rfl⟩ : syracuseStep 1811897 = 1358923) B1358923
theorem B4073003 : Blo 802343 4073003 := bstep (se 1 (by rfl) ⟨3054752, by rfl⟩ : syracuseStep 4073003 = 6109505) B6109505
theorem B1812239 : Blo 802343 1812239 := bstep (se 1 (by rfl) ⟨1359179, by rfl⟩ : syracuseStep 1812239 = 2718359) B2718359
theorem B1812257 : Blo 802343 1812257 := bstep (se 2 (by rfl) ⟨679596, by rfl⟩ : syracuseStep 1812257 = 1359193) B1359193
theorem B993211 : Blo 802343 993211 := bstep (se 1 (by rfl) ⟨744908, by rfl⟩ : syracuseStep 993211 = 1489817) B1489817
theorem B1812599 : Blo 802343 1812599 := bstep (se 1 (by rfl) ⟨1359449, by rfl⟩ : syracuseStep 1812599 = 2718899) B2718899
theorem B1222955 : Blo 802343 1222955 := bstep (se 1 (by rfl) ⟨917216, by rfl⟩ : syracuseStep 1222955 = 1834433) B1834433
theorem B1812779 : Blo 802343 1812779 := bstep (se 1 (by rfl) ⟨1359584, by rfl⟩ : syracuseStep 1812779 = 2719169) B2719169
theorem B1354043 : Blo 802343 1354043 := bstep (se 1 (by rfl) ⟨1015532, by rfl⟩ : syracuseStep 1354043 = 2031065) B2031065
theorem B2173243 : Blo 802343 2173243 := bstep (se 1 (by rfl) ⟨1629932, by rfl⟩ : syracuseStep 2173243 = 3259865) B3259865
theorem B33499541 : Blo 802343 33499541 := bstep (se 6 (by rfl) ⟨785145, by rfl⟩ : syracuseStep 33499541 = 1570291) B1570291
theorem B1813139 : Blo 802343 1813139 := bstep (se 1 (by rfl) ⟨1359854, by rfl⟩ : syracuseStep 1813139 = 2719709) B2719709
theorem B1354441 : Blo 802343 1354441 := bstep (se 2 (by rfl) ⟨507915, by rfl⟩ : syracuseStep 1354441 = 1015831) B1015831
theorem B1813193 : Blo 802343 1813193 := bstep (se 2 (by rfl) ⟨679947, by rfl⟩ : syracuseStep 1813193 = 1359895) B1359895
theorem B1288975 : Blo 802343 1288975 := bstep (se 1 (by rfl) ⟨966731, by rfl⟩ : syracuseStep 1288975 = 1933463) B1933463
theorem B4074299 : Blo 802343 4074299 := bstep (se 1 (by rfl) ⟨3055724, by rfl⟩ : syracuseStep 4074299 = 6111449) B6111449
theorem B3091385 : Blo 802343 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B4074461 : Blo 802343 4074461 := bstep (se 3 (by rfl) ⟨763961, by rfl⟩ : syracuseStep 4074461 = 1527923) B1527923
theorem B6859799 : Blo 802343 6859799 := bstep (se 1 (by rfl) ⟨5144849, by rfl⟩ : syracuseStep 6859799 = 10289699) B10289699
theorem B928903 : Blo 802343 928903 := bstep (se 1 (by rfl) ⟨696677, by rfl⟩ : syracuseStep 928903 = 1393355) B1393355
theorem B1223927 : Blo 802343 1223927 := bstep (se 1 (by rfl) ⟨917945, by rfl⟩ : syracuseStep 1223927 = 1835891) B1835891
theorem B1715489 : Blo 802343 1715489 := bstep (se 2 (by rfl) ⟨643308, by rfl⟩ : syracuseStep 1715489 = 1286617) B1286617
theorem B4074785 : Blo 802343 4074785 := bstep (se 2 (by rfl) ⟨1528044, by rfl⟩ : syracuseStep 4074785 = 3056089) B3056089
theorem B1355143 : Blo 802343 1355143 := bstep (se 1 (by rfl) ⟨1016357, by rfl⟩ : syracuseStep 1355143 = 2032715) B2032715
theorem B1813895 : Blo 802343 1813895 := bstep (se 1 (by rfl) ⟨1360421, by rfl⟩ : syracuseStep 1813895 = 2720843) B2720843
theorem B6106589 : Blo 802343 6106589 := bstep (se 3 (by rfl) ⟨1144985, by rfl⟩ : syracuseStep 6106589 = 2289971) B2289971
theorem B1814075 : Blo 802343 1814075 := bstep (se 1 (by rfl) ⟨1360556, by rfl⟩ : syracuseStep 1814075 = 2721113) B2721113
theorem B2895421 : Blo 802343 2895421 := bstep (se 3 (by rfl) ⟨542891, by rfl⟩ : syracuseStep 2895421 = 1085783) B1085783
theorem B1814201 : Blo 802343 1814201 := bstep (se 2 (by rfl) ⟨680325, by rfl⟩ : syracuseStep 1814201 = 1360651) B1360651
theorem B9678565 : Blo 802343 9678565 := bstep (se 4 (by rfl) ⟨907365, by rfl⟩ : syracuseStep 9678565 = 1814731) B1814731
theorem B1355791 : Blo 802343 1355791 := bstep (se 1 (by rfl) ⟨1016843, by rfl⟩ : syracuseStep 1355791 = 2033687) B2033687
theorem B6860861 : Blo 802343 6860861 := bstep (se 3 (by rfl) ⟨1286411, by rfl⟩ : syracuseStep 6860861 = 2572823) B2572823
theorem B4075757 : Blo 802343 4075757 := bstep (se 3 (by rfl) ⟨764204, by rfl⟩ : syracuseStep 4075757 = 1528409) B1528409
theorem B3092737 : Blo 802343 3092737 := bstep (se 2 (by rfl) ⟨1159776, by rfl⟩ : syracuseStep 3092737 = 2319553) B2319553
theorem B1356331 : Blo 802343 1356331 := bstep (se 1 (by rfl) ⟨1017248, by rfl⟩ : syracuseStep 1356331 = 2034497) B2034497
theorem B1356473 : Blo 802343 1356473 := bstep (se 2 (by rfl) ⟨508677, by rfl⟩ : syracuseStep 1356473 = 1017355) B1017355
theorem B3814411 : Blo 802343 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B4076567 : Blo 802343 4076567 := bstep (se 1 (by rfl) ⟨3057425, by rfl⟩ : syracuseStep 4076567 = 6114851) B6114851
theorem B1717291 : Blo 802343 1717291 := bstep (se 1 (by rfl) ⟨1287968, by rfl⟩ : syracuseStep 1717291 = 2575937) B2575937
theorem B2864189 : Blo 802343 2864189 := bstep (se 3 (by rfl) ⟨537035, by rfl⟩ : syracuseStep 2864189 = 1074071) B1074071
theorem B2176271 : Blo 802343 2176271 := bstep (se 1 (by rfl) ⟨1632203, by rfl⟩ : syracuseStep 2176271 = 3264407) B3264407
theorem B1357175 : Blo 802343 1357175 := bstep (se 1 (by rfl) ⟨1017881, by rfl⟩ : syracuseStep 1357175 = 2035763) B2035763
theorem B1357627 : Blo 802343 1357627 := bstep (se 1 (by rfl) ⟨1018220, by rfl⟩ : syracuseStep 1357627 = 2036441) B2036441
theorem B62666561 : Blo 802343 62666561 := bstep (se 2 (by rfl) ⟨23499960, by rfl⟩ : syracuseStep 62666561 = 46999921) B46999921
theorem B1357769 : Blo 802343 1357769 := bstep (se 2 (by rfl) ⟨509163, by rfl⟩ : syracuseStep 1357769 = 1018327) B1018327
theorem B3258569 : Blo 802343 3258569 := bstep (se 2 (by rfl) ⟨1221963, by rfl⟩ : syracuseStep 3258569 = 2443927) B2443927
theorem B1161487 : Blo 802343 1161487 := bstep (se 1 (by rfl) ⟨871115, by rfl⟩ : syracuseStep 1161487 = 1742231) B1742231
theorem B1718561 : Blo 802343 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B7420295 : Blo 802343 7420295 := bstep (se 1 (by rfl) ⟨5565221, by rfl⟩ : syracuseStep 7420295 = 11130443) B11130443
theorem B1718675 : Blo 802343 1718675 := bstep (se 1 (by rfl) ⟨1289006, by rfl⟩ : syracuseStep 1718675 = 2578013) B2578013
theorem B1358471 : Blo 802343 1358471 := bstep (se 1 (by rfl) ⟨1018853, by rfl⟩ : syracuseStep 1358471 = 2037707) B2037707
theorem B2571041 : Blo 802343 2571041 := bstep (se 2 (by rfl) ⟨964140, by rfl⟩ : syracuseStep 2571041 = 1928281) B1928281
theorem B2898823 : Blo 802343 2898823 := bstep (se 1 (by rfl) ⟨2174117, by rfl⟩ : syracuseStep 2898823 = 4348235) B4348235
theorem B2177945 : Blo 802343 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B5160023 : Blo 802343 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B1359119 : Blo 802343 1359119 := bstep (se 1 (by rfl) ⟨1019339, by rfl⟩ : syracuseStep 1359119 = 2038679) B2038679
theorem B1523215 : Blo 802343 1523215 := bstep (se 1 (by rfl) ⟨1142411, by rfl⟩ : syracuseStep 1523215 = 2284823) B2284823
theorem B7421483 : Blo 802343 7421483 := bstep (se 1 (by rfl) ⟨5566112, by rfl⟩ : syracuseStep 7421483 = 11132225) B11132225
theorem B802363 : Blo 802343 802363 := bstep (se 1 (by rfl) ⟨601772, by rfl⟩ : syracuseStep 802363 = 1203545) B1203545
theorem B802439 : Blo 802343 802439 := bstep (se 1 (by rfl) ⟨601829, by rfl⟩ : syracuseStep 802439 = 1203659) B1203659
theorem B802447 : Blo 802343 802447 := bstep (se 1 (by rfl) ⟨601835, by rfl⟩ : syracuseStep 802447 = 1203671) B1203671
theorem B802491 : Blo 802343 802491 := bstep (se 1 (by rfl) ⟨601868, by rfl⟩ : syracuseStep 802491 = 1203737) B1203737
theorem B802567 : Blo 802343 802567 := bstep (se 1 (by rfl) ⟨601925, by rfl⟩ : syracuseStep 802567 = 1203851) B1203851
theorem B802575 : Blo 802343 802575 := bstep (se 1 (by rfl) ⟨601931, by rfl⟩ : syracuseStep 802575 = 1203863) B1203863
theorem B1359659 : Blo 802343 1359659 := bstep (se 1 (by rfl) ⟨1019744, by rfl⟩ : syracuseStep 1359659 = 2039489) B2039489
theorem B802619 : Blo 802343 802619 := bstep (se 1 (by rfl) ⟨601964, by rfl⟩ : syracuseStep 802619 = 1203929) B1203929
theorem B2178875 : Blo 802343 2178875 := bstep (se 1 (by rfl) ⟨1634156, by rfl⟩ : syracuseStep 2178875 = 3268313) B3268313
theorem B802695 : Blo 802343 802695 := bstep (se 1 (by rfl) ⟨602021, by rfl⟩ : syracuseStep 802695 = 1204043) B1204043
theorem B802703 : Blo 802343 802703 := bstep (se 1 (by rfl) ⟨602027, by rfl⟩ : syracuseStep 802703 = 1204055) B1204055
theorem B1523603 : Blo 802343 1523603 := bstep (se 1 (by rfl) ⟨1142702, by rfl⟩ : syracuseStep 1523603 = 2285405) B2285405
theorem B9781145 : Blo 802343 9781145 := bstep (se 2 (by rfl) ⟨3667929, by rfl⟩ : syracuseStep 9781145 = 7335859) B7335859
theorem B802747 : Blo 802343 802747 := bstep (se 1 (by rfl) ⟨602060, by rfl⟩ : syracuseStep 802747 = 1204121) B1204121
theorem B802823 : Blo 802343 802823 := bstep (se 1 (by rfl) ⟨602117, by rfl⟩ : syracuseStep 802823 = 1204235) B1204235
theorem B3096587 : Blo 802343 3096587 := bstep (se 1 (by rfl) ⟨2322440, by rfl⟩ : syracuseStep 3096587 = 4644881) B4644881
theorem B802831 : Blo 802343 802831 := bstep (se 1 (by rfl) ⟨602123, by rfl⟩ : syracuseStep 802831 = 1204247) B1204247
theorem B4079645 : Blo 802343 4079645 := bstep (se 3 (by rfl) ⟨764933, by rfl⟩ : syracuseStep 4079645 = 1529867) B1529867
theorem B802875 : Blo 802343 802875 := bstep (se 1 (by rfl) ⟨602156, by rfl⟩ : syracuseStep 802875 = 1204313) B1204313
theorem B802951 : Blo 802343 802951 := bstep (se 1 (by rfl) ⟨602213, by rfl⟩ : syracuseStep 802951 = 1204427) B1204427
theorem B802959 : Blo 802343 802959 := bstep (se 1 (by rfl) ⟨602219, by rfl⟩ : syracuseStep 802959 = 1204439) B1204439
theorem B1360057 : Blo 802343 1360057 := bstep (se 2 (by rfl) ⟨510021, by rfl⟩ : syracuseStep 1360057 = 1020043) B1020043
theorem B803003 : Blo 802343 803003 := bstep (se 1 (by rfl) ⟨602252, by rfl⟩ : syracuseStep 803003 = 1204505) B1204505
theorem B803079 : Blo 802343 803079 := bstep (se 1 (by rfl) ⟨602309, by rfl⟩ : syracuseStep 803079 = 1204619) B1204619
theorem B803087 : Blo 802343 803087 := bstep (se 1 (by rfl) ⟨602315, by rfl⟩ : syracuseStep 803087 = 1204631) B1204631
theorem B803131 : Blo 802343 803131 := bstep (se 1 (by rfl) ⟨602348, by rfl⟩ : syracuseStep 803131 = 1204697) B1204697
theorem B803207 : Blo 802343 803207 := bstep (se 1 (by rfl) ⟨602405, by rfl⟩ : syracuseStep 803207 = 1204811) B1204811
theorem B803215 : Blo 802343 803215 := bstep (se 1 (by rfl) ⟨602411, by rfl⟩ : syracuseStep 803215 = 1204823) B1204823
theorem B803259 : Blo 802343 803259 := bstep (se 1 (by rfl) ⟨602444, by rfl⟩ : syracuseStep 803259 = 1204889) B1204889
theorem B1720777 : Blo 802343 1720777 := bstep (se 2 (by rfl) ⟨645291, by rfl⟩ : syracuseStep 1720777 = 1290583) B1290583
theorem B4080131 : Blo 802343 4080131 := bstep (se 1 (by rfl) ⟨3060098, by rfl⟩ : syracuseStep 4080131 = 6120197) B6120197
theorem B803335 : Blo 802343 803335 := bstep (se 1 (by rfl) ⟨602501, by rfl⟩ : syracuseStep 803335 = 1205003) B1205003
theorem B803343 : Blo 802343 803343 := bstep (se 1 (by rfl) ⟨602507, by rfl⟩ : syracuseStep 803343 = 1205015) B1205015
theorem B803387 : Blo 802343 803387 := bstep (se 1 (by rfl) ⟨602540, by rfl⟩ : syracuseStep 803387 = 1205081) B1205081
theorem B803463 : Blo 802343 803463 := bstep (se 1 (by rfl) ⟨602597, by rfl⟩ : syracuseStep 803463 = 1205195) B1205195
theorem B803471 : Blo 802343 803471 := bstep (se 1 (by rfl) ⟨602603, by rfl⟩ : syracuseStep 803471 = 1205207) B1205207
theorem B803515 : Blo 802343 803515 := bstep (se 1 (by rfl) ⟨602636, by rfl⟩ : syracuseStep 803515 = 1205273) B1205273
theorem B803591 : Blo 802343 803591 := bstep (se 1 (by rfl) ⟨602693, by rfl⟩ : syracuseStep 803591 = 1205387) B1205387
theorem B803599 : Blo 802343 803599 := bstep (se 1 (by rfl) ⟨602699, by rfl⟩ : syracuseStep 803599 = 1205399) B1205399
theorem B4899599 : Blo 802343 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B148882211 : Blo 802343 148882211 := bstep (se 1 (by rfl) ⟨111661658, by rfl⟩ : syracuseStep 148882211 = 223323317) B223323317
theorem B5161765 : Blo 802343 5161765 := bstep (se 4 (by rfl) ⟨483915, by rfl⟩ : syracuseStep 5161765 = 967831) B967831
theorem B803643 : Blo 802343 803643 := bstep (se 1 (by rfl) ⟨602732, by rfl⟩ : syracuseStep 803643 = 1205465) B1205465
theorem B803719 : Blo 802343 803719 := bstep (se 1 (by rfl) ⟨602789, by rfl⟩ : syracuseStep 803719 = 1205579) B1205579
theorem B803727 : Blo 802343 803727 := bstep (se 1 (by rfl) ⟨602795, by rfl⟩ : syracuseStep 803727 = 1205591) B1205591
theorem B803771 : Blo 802343 803771 := bstep (se 1 (by rfl) ⟨602828, by rfl⟩ : syracuseStep 803771 = 1205657) B1205657
theorem B803847 : Blo 802343 803847 := bstep (se 1 (by rfl) ⟨602885, by rfl⟩ : syracuseStep 803847 = 1205771) B1205771
theorem B803855 : Blo 802343 803855 := bstep (se 1 (by rfl) ⟨602891, by rfl⟩ : syracuseStep 803855 = 1205783) B1205783
theorem B803899 : Blo 802343 803899 := bstep (se 1 (by rfl) ⟨602924, by rfl⟩ : syracuseStep 803899 = 1205849) B1205849
theorem B803975 : Blo 802343 803975 := bstep (se 1 (by rfl) ⟨602981, by rfl⟩ : syracuseStep 803975 = 1205963) B1205963
theorem B803983 : Blo 802343 803983 := bstep (se 1 (by rfl) ⟨602987, by rfl⟩ : syracuseStep 803983 = 1205975) B1205975
theorem B804027 : Blo 802343 804027 := bstep (se 1 (by rfl) ⟨603020, by rfl⟩ : syracuseStep 804027 = 1206041) B1206041
theorem B804103 : Blo 802343 804103 := bstep (se 1 (by rfl) ⟨603077, by rfl⟩ : syracuseStep 804103 = 1206155) B1206155
theorem B1525007 : Blo 802343 1525007 := bstep (se 1 (by rfl) ⟨1143755, by rfl⟩ : syracuseStep 1525007 = 2287511) B2287511
theorem B804111 : Blo 802343 804111 := bstep (se 1 (by rfl) ⟨603083, by rfl⟩ : syracuseStep 804111 = 1206167) B1206167
theorem B4572449 : Blo 802343 4572449 := bstep (se 2 (by rfl) ⟨1714668, by rfl⟩ : syracuseStep 4572449 = 3429337) B3429337
theorem B2934049 : Blo 802343 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B804155 : Blo 802343 804155 := bstep (se 1 (by rfl) ⟨603116, by rfl⟩ : syracuseStep 804155 = 1206233) B1206233
theorem B804231 : Blo 802343 804231 := bstep (se 1 (by rfl) ⟨603173, by rfl⟩ : syracuseStep 804231 = 1206347) B1206347
theorem B804239 : Blo 802343 804239 := bstep (se 1 (by rfl) ⟨603179, by rfl⟩ : syracuseStep 804239 = 1206359) B1206359
theorem B804283 : Blo 802343 804283 := bstep (se 1 (by rfl) ⟨603212, by rfl⟩ : syracuseStep 804283 = 1206425) B1206425
theorem B804359 : Blo 802343 804359 := bstep (se 1 (by rfl) ⟨603269, by rfl⟩ : syracuseStep 804359 = 1206539) B1206539
theorem B804367 : Blo 802343 804367 := bstep (se 1 (by rfl) ⟨603275, by rfl⟩ : syracuseStep 804367 = 1206551) B1206551
theorem B804411 : Blo 802343 804411 := bstep (se 1 (by rfl) ⟨603308, by rfl⟩ : syracuseStep 804411 = 1206617) B1206617
theorem B804487 : Blo 802343 804487 := bstep (se 1 (by rfl) ⟨603365, by rfl⟩ : syracuseStep 804487 = 1206731) B1206731
theorem B804495 : Blo 802343 804495 := bstep (se 1 (by rfl) ⟨603371, by rfl⟩ : syracuseStep 804495 = 1206743) B1206743
theorem B804539 : Blo 802343 804539 := bstep (se 1 (by rfl) ⟨603404, by rfl⟩ : syracuseStep 804539 = 1206809) B1206809
theorem B804615 : Blo 802343 804615 := bstep (se 1 (by rfl) ⟨603461, by rfl⟩ : syracuseStep 804615 = 1206923) B1206923
theorem B804623 : Blo 802343 804623 := bstep (se 1 (by rfl) ⟨603467, by rfl⟩ : syracuseStep 804623 = 1206935) B1206935
theorem B1525547 : Blo 802343 1525547 := bstep (se 1 (by rfl) ⟨1144160, by rfl⟩ : syracuseStep 1525547 = 2288321) B2288321
theorem B804667 : Blo 802343 804667 := bstep (se 1 (by rfl) ⟨603500, by rfl⟩ : syracuseStep 804667 = 1207001) B1207001
theorem B804743 : Blo 802343 804743 := bstep (se 1 (by rfl) ⟨603557, by rfl⟩ : syracuseStep 804743 = 1207115) B1207115
theorem B903055 : Blo 802343 903055 := bstep (se 1 (by rfl) ⟨677291, by rfl⟩ : syracuseStep 903055 = 1354583) B1354583
theorem B804751 : Blo 802343 804751 := bstep (se 1 (by rfl) ⟨603563, by rfl⟩ : syracuseStep 804751 = 1207127) B1207127
theorem B2606995 : Blo 802343 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B804795 : Blo 802343 804795 := bstep (se 1 (by rfl) ⟨603596, by rfl⟩ : syracuseStep 804795 = 1207193) B1207193
theorem B804871 : Blo 802343 804871 := bstep (se 1 (by rfl) ⟨603653, by rfl⟩ : syracuseStep 804871 = 1207307) B1207307
theorem B804879 : Blo 802343 804879 := bstep (se 1 (by rfl) ⟨603659, by rfl⟩ : syracuseStep 804879 = 1207319) B1207319
theorem B9783341 : Blo 802343 9783341 := bstep (se 3 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 9783341 = 3668753) B3668753
theorem B804923 : Blo 802343 804923 := bstep (se 1 (by rfl) ⟨603692, by rfl⟩ : syracuseStep 804923 = 1207385) B1207385
theorem B4081751 : Blo 802343 4081751 := bstep (se 1 (by rfl) ⟨3061313, by rfl⟩ : syracuseStep 4081751 = 6122627) B6122627
theorem B804999 : Blo 802343 804999 := bstep (se 1 (by rfl) ⟨603749, by rfl⟩ : syracuseStep 804999 = 1207499) B1207499
theorem B805007 : Blo 802343 805007 := bstep (se 1 (by rfl) ⟨603755, by rfl⟩ : syracuseStep 805007 = 1207511) B1207511
theorem B805051 : Blo 802343 805051 := bstep (se 1 (by rfl) ⟨603788, by rfl⟩ : syracuseStep 805051 = 1207577) B1207577
theorem B805127 : Blo 802343 805127 := bstep (se 1 (by rfl) ⟨603845, by rfl⟩ : syracuseStep 805127 = 1207691) B1207691
theorem B805135 : Blo 802343 805135 := bstep (se 1 (by rfl) ⟨603851, by rfl⟩ : syracuseStep 805135 = 1207703) B1207703
theorem B805179 : Blo 802343 805179 := bstep (se 1 (by rfl) ⟨603884, by rfl⟩ : syracuseStep 805179 = 1207769) B1207769
theorem B903559 : Blo 802343 903559 := bstep (se 1 (by rfl) ⟨677669, by rfl⟩ : syracuseStep 903559 = 1355339) B1355339
theorem B805255 : Blo 802343 805255 := bstep (se 1 (by rfl) ⟨603941, by rfl⟩ : syracuseStep 805255 = 1207883) B1207883
theorem B805263 : Blo 802343 805263 := bstep (se 1 (by rfl) ⟨603947, by rfl⟩ : syracuseStep 805263 = 1207895) B1207895
theorem B805307 : Blo 802343 805307 := bstep (se 1 (by rfl) ⟨603980, by rfl⟩ : syracuseStep 805307 = 1207961) B1207961
theorem B805383 : Blo 802343 805383 := bstep (se 1 (by rfl) ⟨604037, by rfl⟩ : syracuseStep 805383 = 1208075) B1208075
theorem B805391 : Blo 802343 805391 := bstep (se 1 (by rfl) ⟨604043, by rfl⟩ : syracuseStep 805391 = 1208087) B1208087
theorem B2902571 : Blo 802343 2902571 := bstep (se 1 (by rfl) ⟨2176928, by rfl⟩ : syracuseStep 2902571 = 4353857) B4353857
theorem B903739 : Blo 802343 903739 := bstep (se 1 (by rfl) ⟨677804, by rfl⟩ : syracuseStep 903739 = 1355609) B1355609
theorem B805435 : Blo 802343 805435 := bstep (se 1 (by rfl) ⟨604076, by rfl⟩ : syracuseStep 805435 = 1208153) B1208153
theorem B33999425 : Blo 802343 33999425 := bstep (se 2 (by rfl) ⟨12749784, by rfl⟩ : syracuseStep 33999425 = 25499569) B25499569
theorem B805511 : Blo 802343 805511 := bstep (se 1 (by rfl) ⟨604133, by rfl⟩ : syracuseStep 805511 = 1208267) B1208267
theorem B805519 : Blo 802343 805519 := bstep (se 1 (by rfl) ⟨604139, by rfl⟩ : syracuseStep 805519 = 1208279) B1208279
theorem B805563 : Blo 802343 805563 := bstep (se 1 (by rfl) ⟨604172, by rfl⟩ : syracuseStep 805563 = 1208345) B1208345
theorem B5163713 : Blo 802343 5163713 := bstep (se 2 (by rfl) ⟨1936392, by rfl⟩ : syracuseStep 5163713 = 3872785) B3872785
theorem B2444033 : Blo 802343 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B805639 : Blo 802343 805639 := bstep (se 1 (by rfl) ⟨604229, by rfl⟩ : syracuseStep 805639 = 1208459) B1208459
theorem B805647 : Blo 802343 805647 := bstep (se 1 (by rfl) ⟨604235, by rfl⟩ : syracuseStep 805647 = 1208471) B1208471
theorem B805691 : Blo 802343 805691 := bstep (se 1 (by rfl) ⟨604268, by rfl⟩ : syracuseStep 805691 = 1208537) B1208537
theorem B1526663 : Blo 802343 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B805767 : Blo 802343 805767 := bstep (se 1 (by rfl) ⟨604325, by rfl⟩ : syracuseStep 805767 = 1208651) B1208651
theorem B805775 : Blo 802343 805775 := bstep (se 1 (by rfl) ⟨604331, by rfl⟩ : syracuseStep 805775 = 1208663) B1208663
theorem B31771541 : Blo 802343 31771541 := bstep (se 6 (by rfl) ⟨744645, by rfl⟩ : syracuseStep 31771541 = 1489291) B1489291
theorem B805819 : Blo 802343 805819 := bstep (se 1 (by rfl) ⟨604364, by rfl⟩ : syracuseStep 805819 = 1208729) B1208729
theorem B805895 : Blo 802343 805895 := bstep (se 1 (by rfl) ⟨604421, by rfl⟩ : syracuseStep 805895 = 1208843) B1208843
theorem B904207 : Blo 802343 904207 := bstep (se 1 (by rfl) ⟨678155, by rfl⟩ : syracuseStep 904207 = 1356311) B1356311
theorem B805903 : Blo 802343 805903 := bstep (se 1 (by rfl) ⟨604427, by rfl⟩ : syracuseStep 805903 = 1208855) B1208855
theorem B805947 : Blo 802343 805947 := bstep (se 1 (by rfl) ⟨604460, by rfl⟩ : syracuseStep 805947 = 1208921) B1208921
theorem B6114365 : Blo 802343 6114365 := bstep (se 3 (by rfl) ⟨1146443, by rfl⟩ : syracuseStep 6114365 = 2292887) B2292887
theorem B806023 : Blo 802343 806023 := bstep (se 1 (by rfl) ⟨604517, by rfl⟩ : syracuseStep 806023 = 1209035) B1209035
theorem B806031 : Blo 802343 806031 := bstep (se 1 (by rfl) ⟨604523, by rfl⟩ : syracuseStep 806031 = 1209047) B1209047
theorem B806075 : Blo 802343 806075 := bstep (se 1 (by rfl) ⟨604556, by rfl⟩ : syracuseStep 806075 = 1209113) B1209113
theorem B806151 : Blo 802343 806151 := bstep (se 1 (by rfl) ⟨604613, by rfl⟩ : syracuseStep 806151 = 1209227) B1209227
theorem B806159 : Blo 802343 806159 := bstep (se 1 (by rfl) ⟨604619, by rfl⟩ : syracuseStep 806159 = 1209239) B1209239
theorem B806203 : Blo 802343 806203 := bstep (se 1 (by rfl) ⟨604652, by rfl⟩ : syracuseStep 806203 = 1209305) B1209305
theorem B806279 : Blo 802343 806279 := bstep (se 1 (by rfl) ⟨604709, by rfl⟩ : syracuseStep 806279 = 1209419) B1209419
theorem B806287 : Blo 802343 806287 := bstep (se 1 (by rfl) ⟨604715, by rfl⟩ : syracuseStep 806287 = 1209431) B1209431
theorem B1527187 : Blo 802343 1527187 := bstep (se 1 (by rfl) ⟨1145390, by rfl⟩ : syracuseStep 1527187 = 2290781) B2290781
theorem B806331 : Blo 802343 806331 := bstep (se 1 (by rfl) ⟨604748, by rfl⟩ : syracuseStep 806331 = 1209497) B1209497
theorem B904711 : Blo 802343 904711 := bstep (se 1 (by rfl) ⟨678533, by rfl⟩ : syracuseStep 904711 = 1357067) B1357067
theorem B6868547 : Blo 802343 6868547 := bstep (se 1 (by rfl) ⟨5151410, by rfl⟩ : syracuseStep 6868547 = 10302821) B10302821
theorem B4574839 : Blo 802343 4574839 := bstep (se 1 (by rfl) ⟨3431129, by rfl⟩ : syracuseStep 4574839 = 6862259) B6862259
theorem B904891 : Blo 802343 904891 := bstep (se 1 (by rfl) ⟨678668, by rfl⟩ : syracuseStep 904891 = 1357337) B1357337
theorem B2609081 : Blo 802343 2609081 := bstep (se 2 (by rfl) ⟨978405, by rfl⟩ : syracuseStep 2609081 = 1956811) B1956811
theorem B905359 : Blo 802343 905359 := bstep (se 1 (by rfl) ⟨679019, by rfl⟩ : syracuseStep 905359 = 1358039) B1358039
theorem B3264713 : Blo 802343 3264713 := bstep (se 2 (by rfl) ⟨1224267, by rfl⟩ : syracuseStep 3264713 = 2448535) B2448535
theorem B19616093 : Blo 802343 19616093 := bstep (se 3 (by rfl) ⟨3678017, by rfl⟩ : syracuseStep 19616093 = 7356035) B7356035
theorem B29348243 : Blo 802343 29348243 := bstep (se 1 (by rfl) ⟨22011182, by rfl⟩ : syracuseStep 29348243 = 44022365) B44022365
theorem B1528379 : Blo 802343 1528379 := bstep (se 1 (by rfl) ⟨1146284, by rfl⟩ : syracuseStep 1528379 = 2292569) B2292569
theorem B905863 : Blo 802343 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B2577167 : Blo 802343 2577167 := bstep (se 1 (by rfl) ⟨1932875, by rfl⟩ : syracuseStep 2577167 = 3865751) B3865751
theorem B1626923 : Blo 802343 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B906043 : Blo 802343 906043 := bstep (se 1 (by rfl) ⟨679532, by rfl⟩ : syracuseStep 906043 = 1359065) B1359065
theorem B4576115 : Blo 802343 4576115 := bstep (se 1 (by rfl) ⟨3432086, by rfl⟩ : syracuseStep 4576115 = 6864173) B6864173
theorem B1528865 : Blo 802343 1528865 := bstep (se 2 (by rfl) ⟨573324, by rfl⟩ : syracuseStep 1528865 = 1146649) B1146649
theorem B906511 : Blo 802343 906511 := bstep (se 1 (by rfl) ⟨679883, by rfl⟩ : syracuseStep 906511 = 1359767) B1359767
theorem B1529131 : Blo 802343 1529131 := bstep (se 1 (by rfl) ⟨1146848, by rfl⟩ : syracuseStep 1529131 = 2293697) B2293697
theorem B4576571 : Blo 802343 4576571 := bstep (se 1 (by rfl) ⟨3432428, by rfl⟩ : syracuseStep 4576571 = 6864857) B6864857
theorem B20108645 : Blo 802343 20108645 := bstep (se 4 (by rfl) ⟨1885185, by rfl⟩ : syracuseStep 20108645 = 3770371) B3770371
theorem B907015 : Blo 802343 907015 := bstep (se 1 (by rfl) ⟨680261, by rfl⟩ : syracuseStep 907015 = 1360523) B1360523
theorem B2447147 : Blo 802343 2447147 := bstep (se 1 (by rfl) ⟨1835360, by rfl⟩ : syracuseStep 2447147 = 3670721) B3670721
theorem B2709395 : Blo 802343 2709395 := bstep (se 1 (by rfl) ⟨2032046, by rfl⟩ : syracuseStep 2709395 = 4064093) B4064093
theorem B3856331 : Blo 802343 3856331 := bstep (se 1 (by rfl) ⟨2892248, by rfl⟩ : syracuseStep 3856331 = 5784497) B5784497
theorem B1103863 : Blo 802343 1103863 := bstep (se 1 (by rfl) ⟨827897, by rfl⟩ : syracuseStep 1103863 = 1655795) B1655795
theorem B4118539 : Blo 802343 4118539 := bstep (se 1 (by rfl) ⟨3088904, by rfl⟩ : syracuseStep 4118539 = 6177809) B6177809
theorem B7821323 : Blo 802343 7821323 := bstep (se 1 (by rfl) ⟨5865992, by rfl⟩ : syracuseStep 7821323 = 11731985) B11731985
theorem B4577573 : Blo 802343 4577573 := bstep (se 4 (by rfl) ⟨429147, by rfl⟩ : syracuseStep 4577573 = 858295) B858295
theorem B6117767 : Blo 802343 6117767 := bstep (se 1 (by rfl) ⟨4588325, by rfl⟩ : syracuseStep 6117767 = 9176651) B9176651
theorem B1530247 : Blo 802343 1530247 := bstep (se 1 (by rfl) ⟨1147685, by rfl⟩ : syracuseStep 1530247 = 2295371) B2295371
theorem B4578029 : Blo 802343 4578029 := bstep (se 3 (by rfl) ⟨858380, by rfl⟩ : syracuseStep 4578029 = 1716761) B1716761
theorem B1629227 : Blo 802343 1629227 := bstep (se 1 (by rfl) ⟨1221920, by rfl⟩ : syracuseStep 1629227 = 2443841) B2443841
theorem B7724119 : Blo 802343 7724119 := bstep (se 1 (by rfl) ⟨5793089, by rfl⟩ : syracuseStep 7724119 = 11586179) B11586179
theorem B2710799 : Blo 802343 2710799 := bstep (se 1 (by rfl) ⟨2033099, by rfl⟩ : syracuseStep 2710799 = 4066199) B4066199
theorem B1203515 : Blo 802343 1203515 := bstep (se 1 (by rfl) ⟨902636, by rfl⟩ : syracuseStep 1203515 = 1805273) B1805273
theorem B2088251 : Blo 802343 2088251 := bstep (se 1 (by rfl) ⟨1566188, by rfl⟩ : syracuseStep 2088251 = 3132377) B3132377
theorem B3267955 : Blo 802343 3267955 := bstep (se 1 (by rfl) ⟨2450966, by rfl⟩ : syracuseStep 3267955 = 4901933) B4901933
theorem B1203575 : Blo 802343 1203575 := bstep (se 1 (by rfl) ⟨902681, by rfl⟩ : syracuseStep 1203575 = 1805363) B1805363
theorem B1203599 : Blo 802343 1203599 := bstep (se 1 (by rfl) ⟨902699, by rfl⟩ : syracuseStep 1203599 = 1805399) B1805399
theorem B4578713 : Blo 802343 4578713 := bstep (se 2 (by rfl) ⟨1717017, by rfl⟩ : syracuseStep 4578713 = 3434035) B3434035
theorem B1203641 : Blo 802343 1203641 := bstep (se 2 (by rfl) ⟨451365, by rfl⟩ : syracuseStep 1203641 = 902731) B902731
theorem B1203719 : Blo 802343 1203719 := bstep (se 1 (by rfl) ⟨902789, by rfl⟩ : syracuseStep 1203719 = 1805579) B1805579
theorem B2711069 : Blo 802343 2711069 := bstep (se 3 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 2711069 = 1016651) B1016651
theorem B1203755 : Blo 802343 1203755 := bstep (se 1 (by rfl) ⟨902816, by rfl⟩ : syracuseStep 1203755 = 1805633) B1805633
theorem B1203785 : Blo 802343 1203785 := bstep (se 2 (by rfl) ⟨451419, by rfl⟩ : syracuseStep 1203785 = 902839) B902839
theorem B4120183 : Blo 802343 4120183 := bstep (se 1 (by rfl) ⟨3090137, by rfl⟩ : syracuseStep 4120183 = 6180275) B6180275
theorem B1203899 : Blo 802343 1203899 := bstep (se 1 (by rfl) ⟨902924, by rfl⟩ : syracuseStep 1203899 = 1805849) B1805849
theorem B1203959 : Blo 802343 1203959 := bstep (se 1 (by rfl) ⟨902969, by rfl⟩ : syracuseStep 1203959 = 1805939) B1805939
theorem B1203983 : Blo 802343 1203983 := bstep (se 1 (by rfl) ⟨902987, by rfl⟩ : syracuseStep 1203983 = 1805975) B1805975
theorem B1204025 : Blo 802343 1204025 := bstep (se 2 (by rfl) ⟨451509, by rfl⟩ : syracuseStep 1204025 = 903019) B903019
theorem B6872921 : Blo 802343 6872921 := bstep (se 2 (by rfl) ⟨2577345, by rfl⟩ : syracuseStep 6872921 = 5154691) B5154691
theorem B1204103 : Blo 802343 1204103 := bstep (se 1 (by rfl) ⟨903077, by rfl⟩ : syracuseStep 1204103 = 1806155) B1806155
theorem B7724963 : Blo 802343 7724963 := bstep (se 1 (by rfl) ⟨5793722, by rfl⟩ : syracuseStep 7724963 = 11587445) B11587445
theorem B1204139 : Blo 802343 1204139 := bstep (se 1 (by rfl) ⟨903104, by rfl⟩ : syracuseStep 1204139 = 1806209) B1806209
theorem B1204169 : Blo 802343 1204169 := bstep (se 2 (by rfl) ⟨451563, by rfl⟩ : syracuseStep 1204169 = 903127) B903127
theorem B2285597 : Blo 802343 2285597 := bstep (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) B857099
theorem B1204283 : Blo 802343 1204283 := bstep (se 1 (by rfl) ⟨903212, by rfl⟩ : syracuseStep 1204283 = 1806425) B1806425
theorem B1204343 : Blo 802343 1204343 := bstep (se 1 (by rfl) ⟨903257, by rfl⟩ : syracuseStep 1204343 = 1806515) B1806515
theorem B1204367 : Blo 802343 1204367 := bstep (se 1 (by rfl) ⟨903275, by rfl⟩ : syracuseStep 1204367 = 1806551) B1806551
theorem B1204409 : Blo 802343 1204409 := bstep (se 2 (by rfl) ⟨451653, by rfl⟩ : syracuseStep 1204409 = 903307) B903307
theorem B1204487 : Blo 802343 1204487 := bstep (se 1 (by rfl) ⟨903365, by rfl⟩ : syracuseStep 1204487 = 1806731) B1806731
theorem B1204523 : Blo 802343 1204523 := bstep (se 1 (by rfl) ⟨903392, by rfl⟩ : syracuseStep 1204523 = 1806785) B1806785
theorem B1204553 : Blo 802343 1204553 := bstep (se 2 (by rfl) ⟨451707, by rfl⟩ : syracuseStep 1204553 = 903415) B903415
theorem B4350353 : Blo 802343 4350353 := bstep (se 2 (by rfl) ⟨1631382, by rfl⟩ : syracuseStep 4350353 = 3262765) B3262765
theorem B1204667 : Blo 802343 1204667 := bstep (se 1 (by rfl) ⟨903500, by rfl⟩ : syracuseStep 1204667 = 1807001) B1807001
theorem B1204727 : Blo 802343 1204727 := bstep (se 1 (by rfl) ⟨903545, by rfl⟩ : syracuseStep 1204727 = 1807091) B1807091
theorem B3858947 : Blo 802343 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B1204751 : Blo 802343 1204751 := bstep (se 1 (by rfl) ⟨903563, by rfl⟩ : syracuseStep 1204751 = 1807127) B1807127
theorem B1204793 : Blo 802343 1204793 := bstep (se 2 (by rfl) ⟨451797, by rfl⟩ : syracuseStep 1204793 = 903595) B903595
theorem B1204871 : Blo 802343 1204871 := bstep (se 1 (by rfl) ⟨903653, by rfl⟩ : syracuseStep 1204871 = 1807307) B1807307
theorem B1204907 : Blo 802343 1204907 := bstep (se 1 (by rfl) ⟨903680, by rfl⟩ : syracuseStep 1204907 = 1807361) B1807361
theorem B2286281 : Blo 802343 2286281 := bstep (se 2 (by rfl) ⟨857355, by rfl⟩ : syracuseStep 2286281 = 1714711) B1714711
theorem B1204937 : Blo 802343 1204937 := bstep (se 2 (by rfl) ⟨451851, by rfl⟩ : syracuseStep 1204937 = 903703) B903703
theorem B1205051 : Blo 802343 1205051 := bstep (se 1 (by rfl) ⟨903788, by rfl⟩ : syracuseStep 1205051 = 1807577) B1807577
theorem B1205111 : Blo 802343 1205111 := bstep (se 1 (by rfl) ⟨903833, by rfl⟩ : syracuseStep 1205111 = 1807667) B1807667
theorem B1205135 : Blo 802343 1205135 := bstep (se 1 (by rfl) ⟨903851, by rfl⟩ : syracuseStep 1205135 = 1807703) B1807703
theorem B2712473 : Blo 802343 2712473 := bstep (se 2 (by rfl) ⟨1017177, by rfl⟩ : syracuseStep 2712473 = 2034355) B2034355
theorem B1205177 : Blo 802343 1205177 := bstep (se 2 (by rfl) ⟨451941, by rfl⟩ : syracuseStep 1205177 = 903883) B903883
theorem B1205255 : Blo 802343 1205255 := bstep (se 1 (by rfl) ⟨903941, by rfl⟩ : syracuseStep 1205255 = 1807883) B1807883
theorem B1205291 : Blo 802343 1205291 := bstep (se 1 (by rfl) ⟨903968, by rfl⟩ : syracuseStep 1205291 = 1807937) B1807937
theorem B1205321 : Blo 802343 1205321 := bstep (se 2 (by rfl) ⟨451995, by rfl⟩ : syracuseStep 1205321 = 903991) B903991
theorem B1205435 : Blo 802343 1205435 := bstep (se 1 (by rfl) ⟨904076, by rfl⟩ : syracuseStep 1205435 = 1808153) B1808153
theorem B1205495 : Blo 802343 1205495 := bstep (se 1 (by rfl) ⟨904121, by rfl⟩ : syracuseStep 1205495 = 1808243) B1808243
theorem B2286863 : Blo 802343 2286863 := bstep (se 1 (by rfl) ⟨1715147, by rfl⟩ : syracuseStep 2286863 = 3430295) B3430295
theorem B1205519 : Blo 802343 1205519 := bstep (se 1 (by rfl) ⟨904139, by rfl⟩ : syracuseStep 1205519 = 1808279) B1808279
theorem B1205561 : Blo 802343 1205561 := bstep (se 2 (by rfl) ⟨452085, by rfl⟩ : syracuseStep 1205561 = 904171) B904171
theorem B1205639 : Blo 802343 1205639 := bstep (se 1 (by rfl) ⟨904229, by rfl⟩ : syracuseStep 1205639 = 1808459) B1808459
theorem B1205675 : Blo 802343 1205675 := bstep (se 1 (by rfl) ⟨904256, by rfl⟩ : syracuseStep 1205675 = 1808513) B1808513
theorem B6284729 : Blo 802343 6284729 := bstep (se 2 (by rfl) ⟨2356773, by rfl⟩ : syracuseStep 6284729 = 4713547) B4713547
theorem B1205705 : Blo 802343 1205705 := bstep (se 2 (by rfl) ⟨452139, by rfl⟩ : syracuseStep 1205705 = 904279) B904279
theorem B1205819 : Blo 802343 1205819 := bstep (se 1 (by rfl) ⟨904364, by rfl⟩ : syracuseStep 1205819 = 1808729) B1808729
theorem B2713175 : Blo 802343 2713175 := bstep (se 1 (by rfl) ⟨2034881, by rfl⟩ : syracuseStep 2713175 = 4069763) B4069763
theorem B13395557 : Blo 802343 13395557 := bstep (se 4 (by rfl) ⟨1255833, by rfl⟩ : syracuseStep 13395557 = 2511667) B2511667
theorem B1205879 : Blo 802343 1205879 := bstep (se 1 (by rfl) ⟨904409, by rfl⟩ : syracuseStep 1205879 = 1808819) B1808819
theorem B1205903 : Blo 802343 1205903 := bstep (se 1 (by rfl) ⟨904427, by rfl⟩ : syracuseStep 1205903 = 1808855) B1808855
theorem B1205945 : Blo 802343 1205945 := bstep (se 2 (by rfl) ⟨452229, by rfl⟩ : syracuseStep 1205945 = 904459) B904459
theorem B1206023 : Blo 802343 1206023 := bstep (se 1 (by rfl) ⟨904517, by rfl⟩ : syracuseStep 1206023 = 1809035) B1809035
theorem B4351781 : Blo 802343 4351781 := bstep (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) B815959
theorem B1206059 : Blo 802343 1206059 := bstep (se 1 (by rfl) ⟨904544, by rfl⟩ : syracuseStep 1206059 = 1809089) B1809089
theorem B13756229 : Blo 802343 13756229 := bstep (se 4 (by rfl) ⟨1289646, by rfl⟩ : syracuseStep 13756229 = 2579293) B2579293
theorem B1206089 : Blo 802343 1206089 := bstep (se 2 (by rfl) ⟨452283, by rfl⟩ : syracuseStep 1206089 = 904567) B904567
theorem B1206203 : Blo 802343 1206203 := bstep (se 1 (by rfl) ⟨904652, by rfl⟩ : syracuseStep 1206203 = 1809305) B1809305
theorem B1206263 : Blo 802343 1206263 := bstep (se 1 (by rfl) ⟨904697, by rfl⟩ : syracuseStep 1206263 = 1809395) B1809395
theorem B1206287 : Blo 802343 1206287 := bstep (se 1 (by rfl) ⟨904715, by rfl⟩ : syracuseStep 1206287 = 1809431) B1809431
theorem B1206329 : Blo 802343 1206329 := bstep (se 2 (by rfl) ⟨452373, by rfl⟩ : syracuseStep 1206329 = 904747) B904747
theorem B2713661 : Blo 802343 2713661 := bstep (se 3 (by rfl) ⟨508811, by rfl⟩ : syracuseStep 2713661 = 1017623) B1017623
theorem B1206407 : Blo 802343 1206407 := bstep (se 1 (by rfl) ⟨904805, by rfl⟩ : syracuseStep 1206407 = 1809611) B1809611
theorem B1206443 : Blo 802343 1206443 := bstep (se 1 (by rfl) ⟨904832, by rfl⟩ : syracuseStep 1206443 = 1809665) B1809665
theorem B1206473 : Blo 802343 1206473 := bstep (se 2 (by rfl) ⟨452427, by rfl⟩ : syracuseStep 1206473 = 904855) B904855
theorem B2582729 : Blo 802343 2582729 := bstep (se 2 (by rfl) ⟨968523, by rfl⟩ : syracuseStep 2582729 = 1937047) B1937047
theorem B2451745 : Blo 802343 2451745 := bstep (se 2 (by rfl) ⟨919404, by rfl⟩ : syracuseStep 2451745 = 1838809) B1838809
theorem B1206587 : Blo 802343 1206587 := bstep (se 1 (by rfl) ⟨904940, by rfl⟩ : syracuseStep 1206587 = 1809881) B1809881
theorem B4417907 : Blo 802343 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B1206647 : Blo 802343 1206647 := bstep (se 1 (by rfl) ⟨904985, by rfl⟩ : syracuseStep 1206647 = 1809971) B1809971
theorem B5794183 : Blo 802343 5794183 := bstep (se 1 (by rfl) ⟨4345637, by rfl⟩ : syracuseStep 5794183 = 8691275) B8691275
theorem B1206671 : Blo 802343 1206671 := bstep (se 1 (by rfl) ⟨905003, by rfl⟩ : syracuseStep 1206671 = 1810007) B1810007
theorem B1206713 : Blo 802343 1206713 := bstep (se 2 (by rfl) ⟨452517, by rfl⟩ : syracuseStep 1206713 = 905035) B905035
theorem B9169361 : Blo 802343 9169361 := bstep (se 2 (by rfl) ⟨3438510, by rfl⟩ : syracuseStep 9169361 = 6877021) B6877021
theorem B1206791 : Blo 802343 1206791 := bstep (se 1 (by rfl) ⟨905093, by rfl⟩ : syracuseStep 1206791 = 1810187) B1810187
theorem B1206827 : Blo 802343 1206827 := bstep (se 1 (by rfl) ⟨905120, by rfl⟩ : syracuseStep 1206827 = 1810241) B1810241
theorem B1206857 : Blo 802343 1206857 := bstep (se 2 (by rfl) ⟨452571, by rfl⟩ : syracuseStep 1206857 = 905143) B905143
theorem B7825997 : Blo 802343 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B2288263 : Blo 802343 2288263 := bstep (se 1 (by rfl) ⟨1716197, by rfl⟩ : syracuseStep 2288263 = 3432395) B3432395
theorem B1206971 : Blo 802343 1206971 := bstep (se 1 (by rfl) ⟨905228, by rfl⟩ : syracuseStep 1206971 = 1810457) B1810457
theorem B1207031 : Blo 802343 1207031 := bstep (se 1 (by rfl) ⟨905273, by rfl⟩ : syracuseStep 1207031 = 1810547) B1810547
theorem B1207055 : Blo 802343 1207055 := bstep (se 1 (by rfl) ⟨905291, by rfl⟩ : syracuseStep 1207055 = 1810583) B1810583
theorem B1207097 : Blo 802343 1207097 := bstep (se 2 (by rfl) ⟨452661, by rfl⟩ : syracuseStep 1207097 = 905323) B905323
theorem B5499737 : Blo 802343 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B1207175 : Blo 802343 1207175 := bstep (se 1 (by rfl) ⟨905381, by rfl⟩ : syracuseStep 1207175 = 1810763) B1810763
theorem B2288537 : Blo 802343 2288537 := bstep (se 2 (by rfl) ⟨858201, by rfl⟩ : syracuseStep 2288537 = 1716403) B1716403
theorem B1207211 : Blo 802343 1207211 := bstep (se 1 (by rfl) ⟨905408, by rfl⟩ : syracuseStep 1207211 = 1810817) B1810817
theorem B1207241 : Blo 802343 1207241 := bstep (se 2 (by rfl) ⟨452715, by rfl⟩ : syracuseStep 1207241 = 905431) B905431
theorem B4582403 : Blo 802343 4582403 := bstep (se 1 (by rfl) ⟨3436802, by rfl⟩ : syracuseStep 4582403 = 6873605) B6873605
theorem B1207355 : Blo 802343 1207355 := bstep (se 1 (by rfl) ⟨905516, by rfl⟩ : syracuseStep 1207355 = 1811033) B1811033
theorem B1240183 : Blo 802343 1240183 := bstep (se 1 (by rfl) ⟨930137, by rfl⟩ : syracuseStep 1240183 = 1860275) B1860275
theorem B1207415 : Blo 802343 1207415 := bstep (se 1 (by rfl) ⟨905561, by rfl⟩ : syracuseStep 1207415 = 1811123) B1811123
theorem B1207439 : Blo 802343 1207439 := bstep (se 1 (by rfl) ⟨905579, by rfl⟩ : syracuseStep 1207439 = 1811159) B1811159
theorem B1207481 : Blo 802343 1207481 := bstep (se 2 (by rfl) ⟨452805, by rfl⟩ : syracuseStep 1207481 = 905611) B905611
theorem B2059465 : Blo 802343 2059465 := bstep (se 2 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 2059465 = 1544599) B1544599
theorem B1207559 : Blo 802343 1207559 := bstep (se 1 (by rfl) ⟨905669, by rfl⟩ : syracuseStep 1207559 = 1811339) B1811339
theorem B1207595 : Blo 802343 1207595 := bstep (se 1 (by rfl) ⟨905696, by rfl⟩ : syracuseStep 1207595 = 1811393) B1811393
theorem B1207625 : Blo 802343 1207625 := bstep (se 2 (by rfl) ⟨452859, by rfl⟩ : syracuseStep 1207625 = 905719) B905719
theorem B4353425 : Blo 802343 4353425 := bstep (se 2 (by rfl) ⟨1632534, by rfl⟩ : syracuseStep 4353425 = 3265069) B3265069
theorem B2715065 : Blo 802343 2715065 := bstep (se 2 (by rfl) ⟨1018149, by rfl⟩ : syracuseStep 2715065 = 2036299) B2036299
theorem B1207739 : Blo 802343 1207739 := bstep (se 1 (by rfl) ⟨905804, by rfl⟩ : syracuseStep 1207739 = 1811609) B1811609
theorem B1207799 : Blo 802343 1207799 := bstep (se 1 (by rfl) ⟨905849, by rfl⟩ : syracuseStep 1207799 = 1811699) B1811699
theorem B1207823 : Blo 802343 1207823 := bstep (se 1 (by rfl) ⟨905867, by rfl⟩ : syracuseStep 1207823 = 1811735) B1811735
theorem B1207865 : Blo 802343 1207865 := bstep (se 2 (by rfl) ⟨452949, by rfl⟩ : syracuseStep 1207865 = 905899) B905899
theorem B1207943 : Blo 802343 1207943 := bstep (se 1 (by rfl) ⟨905957, by rfl⟩ : syracuseStep 1207943 = 1811915) B1811915
theorem B1207979 : Blo 802343 1207979 := bstep (se 1 (by rfl) ⟨905984, by rfl⟩ : syracuseStep 1207979 = 1811969) B1811969
theorem B1208009 : Blo 802343 1208009 := bstep (se 2 (by rfl) ⟨453003, by rfl⟩ : syracuseStep 1208009 = 906007) B906007
theorem B1208123 : Blo 802343 1208123 := bstep (se 1 (by rfl) ⟨906092, by rfl⟩ : syracuseStep 1208123 = 1812185) B1812185
theorem B1208183 : Blo 802343 1208183 := bstep (se 1 (by rfl) ⟨906137, by rfl⟩ : syracuseStep 1208183 = 1812275) B1812275
theorem B1208207 : Blo 802343 1208207 := bstep (se 1 (by rfl) ⟨906155, by rfl⟩ : syracuseStep 1208207 = 1812311) B1812311
theorem B1208249 : Blo 802343 1208249 := bstep (se 2 (by rfl) ⟨453093, by rfl⟩ : syracuseStep 1208249 = 906187) B906187
theorem B1208327 : Blo 802343 1208327 := bstep (se 1 (by rfl) ⟨906245, by rfl⟩ : syracuseStep 1208327 = 1812491) B1812491
theorem B2715659 : Blo 802343 2715659 := bstep (se 1 (by rfl) ⟨2036744, by rfl⟩ : syracuseStep 2715659 = 4073489) B4073489
theorem B1208363 : Blo 802343 1208363 := bstep (se 1 (by rfl) ⟨906272, by rfl⟩ : syracuseStep 1208363 = 1812545) B1812545
theorem B2715709 : Blo 802343 2715709 := bstep (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) B1018391
theorem B1208393 : Blo 802343 1208393 := bstep (se 2 (by rfl) ⟨453147, by rfl⟩ : syracuseStep 1208393 = 906295) B906295
theorem B2289779 : Blo 802343 2289779 := bstep (se 1 (by rfl) ⟨1717334, by rfl⟩ : syracuseStep 2289779 = 3434669) B3434669
theorem B2715767 : Blo 802343 2715767 := bstep (se 1 (by rfl) ⟨2036825, by rfl⟩ : syracuseStep 2715767 = 4073651) B4073651
theorem B14151853 : Blo 802343 14151853 := bstep (se 3 (by rfl) ⟨2653472, by rfl⟩ : syracuseStep 14151853 = 5306945) B5306945
theorem B1208507 : Blo 802343 1208507 := bstep (se 1 (by rfl) ⟨906380, by rfl⟩ : syracuseStep 1208507 = 1812761) B1812761
theorem B1208567 : Blo 802343 1208567 := bstep (se 1 (by rfl) ⟨906425, by rfl⟩ : syracuseStep 1208567 = 1812851) B1812851
theorem B1208591 : Blo 802343 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B1208633 : Blo 802343 1208633 := bstep (se 2 (by rfl) ⟨453237, by rfl⟩ : syracuseStep 1208633 = 906475) B906475
theorem B1143175 : Blo 802343 1143175 := bstep (se 1 (by rfl) ⟨857381, by rfl⟩ : syracuseStep 1143175 = 1714763) B1714763
theorem B1208711 : Blo 802343 1208711 := bstep (se 1 (by rfl) ⟨906533, by rfl⟩ : syracuseStep 1208711 = 1813067) B1813067
theorem B1208747 : Blo 802343 1208747 := bstep (se 1 (by rfl) ⟨906560, by rfl⟩ : syracuseStep 1208747 = 1813121) B1813121
theorem B1208777 : Blo 802343 1208777 := bstep (se 2 (by rfl) ⟨453291, by rfl⟩ : syracuseStep 1208777 = 906583) B906583
theorem B38171179 : Blo 802343 38171179 := bstep (se 1 (by rfl) ⟨28628384, by rfl⟩ : syracuseStep 38171179 = 57256769) B57256769
theorem B1208891 : Blo 802343 1208891 := bstep (se 1 (by rfl) ⟨906668, by rfl⟩ : syracuseStep 1208891 = 1813337) B1813337
theorem B1208951 : Blo 802343 1208951 := bstep (se 1 (by rfl) ⟨906713, by rfl⟩ : syracuseStep 1208951 = 1813427) B1813427
theorem B1208975 : Blo 802343 1208975 := bstep (se 1 (by rfl) ⟨906731, by rfl⟩ : syracuseStep 1208975 = 1813463) B1813463
theorem B1209017 : Blo 802343 1209017 := bstep (se 2 (by rfl) ⟨453381, by rfl⟩ : syracuseStep 1209017 = 906763) B906763
theorem B2716361 : Blo 802343 2716361 := bstep (se 2 (by rfl) ⟨1018635, by rfl⟩ : syracuseStep 2716361 = 2037271) B2037271
theorem B1209095 : Blo 802343 1209095 := bstep (se 1 (by rfl) ⟨906821, by rfl⟩ : syracuseStep 1209095 = 1813643) B1813643
theorem B1209131 : Blo 802343 1209131 := bstep (se 1 (by rfl) ⟨906848, by rfl⟩ : syracuseStep 1209131 = 1813697) B1813697
theorem B1209161 : Blo 802343 1209161 := bstep (se 2 (by rfl) ⟨453435, by rfl⟩ : syracuseStep 1209161 = 906871) B906871
theorem B1209275 : Blo 802343 1209275 := bstep (se 1 (by rfl) ⟨906956, by rfl⟩ : syracuseStep 1209275 = 1813913) B1813913
theorem B1209335 : Blo 802343 1209335 := bstep (se 1 (by rfl) ⟨907001, by rfl⟩ : syracuseStep 1209335 = 1814003) B1814003
theorem B1209359 : Blo 802343 1209359 := bstep (se 1 (by rfl) ⟨907019, by rfl⟩ : syracuseStep 1209359 = 1814039) B1814039
theorem B1209401 : Blo 802343 1209401 := bstep (se 2 (by rfl) ⟨453525, by rfl⟩ : syracuseStep 1209401 = 907051) B907051
theorem B1209479 : Blo 802343 1209479 := bstep (se 1 (by rfl) ⟨907109, by rfl⟩ : syracuseStep 1209479 = 1814219) B1814219
theorem B1930387 : Blo 802343 1930387 := bstep (se 1 (by rfl) ⟨1447790, by rfl⟩ : syracuseStep 1930387 = 2895581) B2895581
theorem B1209515 : Blo 802343 1209515 := bstep (se 1 (by rfl) ⟨907136, by rfl⟩ : syracuseStep 1209515 = 1814273) B1814273
theorem B4355309 : Blo 802343 4355309 := bstep (se 3 (by rfl) ⟨816620, by rfl⟩ : syracuseStep 4355309 = 1633241) B1633241
theorem B7337351 : Blo 802343 7337351 := bstep (se 1 (by rfl) ⟨5503013, by rfl⟩ : syracuseStep 7337351 = 11006027) B11006027
theorem B2717063 : Blo 802343 2717063 := bstep (se 1 (by rfl) ⟨2037797, by rfl⟩ : syracuseStep 2717063 = 4075595) B4075595
theorem B816527 : Blo 802343 816527 := bstep (se 1 (by rfl) ⟨612395, by rfl⟩ : syracuseStep 816527 = 1224791) B1224791
theorem B1832507 : Blo 802343 1832507 := bstep (se 1 (by rfl) ⟨1374380, by rfl⟩ : syracuseStep 1832507 = 2748761) B2748761
theorem B980623 : Blo 802343 980623 := bstep (se 1 (by rfl) ⟨735467, by rfl⟩ : syracuseStep 980623 = 1470935) B1470935
theorem B2717441 : Blo 802343 2717441 := bstep (se 2 (by rfl) ⟨1019040, by rfl⟩ : syracuseStep 2717441 = 2038081) B2038081
theorem B1144633 : Blo 802343 1144633 := bstep (se 2 (by rfl) ⟨429237, by rfl⟩ : syracuseStep 1144633 = 858475) B858475
theorem B2292239 : Blo 802343 2292239 := bstep (se 1 (by rfl) ⟨1719179, by rfl⟩ : syracuseStep 2292239 = 3438359) B3438359
theorem B2718251 : Blo 802343 2718251 := bstep (se 1 (by rfl) ⟨2038688, by rfl⟩ : syracuseStep 2718251 = 4077377) B4077377
theorem B26114831 : Blo 802343 26114831 := bstep (se 1 (by rfl) ⟨19586123, by rfl⟩ : syracuseStep 26114831 = 39172247) B39172247
theorem B1145863 : Blo 802343 1145863 := bstep (se 1 (by rfl) ⟨859397, by rfl⟩ : syracuseStep 1145863 = 1718795) B1718795
theorem B1932587 : Blo 802343 1932587 := bstep (se 1 (by rfl) ⟨1449440, by rfl⟩ : syracuseStep 1932587 = 2898881) B2898881
theorem B3046841 : Blo 802343 3046841 := bstep (se 2 (by rfl) ⟨1142565, by rfl⟩ : syracuseStep 3046841 = 2285131) B2285131
theorem B5799377 : Blo 802343 5799377 := bstep (se 2 (by rfl) ⟨2174766, by rfl⟩ : syracuseStep 5799377 = 4349533) B4349533
theorem B2031115 : Blo 802343 2031115 := bstep (se 1 (by rfl) ⟨1523336, by rfl⟩ : syracuseStep 2031115 = 3046673) B3046673
theorem B1474195 : Blo 802343 1474195 := bstep (se 1 (by rfl) ⟨1105646, by rfl⟩ : syracuseStep 1474195 = 2211293) B2211293
theorem B2031257 : Blo 802343 2031257 := bstep (se 2 (by rfl) ⟨761721, by rfl⟩ : syracuseStep 2031257 = 1523443) B1523443
theorem B1933001 : Blo 802343 1933001 := bstep (se 2 (by rfl) ⟨724875, by rfl⟩ : syracuseStep 1933001 = 1449751) B1449751
theorem B2031419 : Blo 802343 2031419 := bstep (se 1 (by rfl) ⟨1523564, by rfl⟩ : syracuseStep 2031419 = 3047129) B3047129
theorem B1146683 : Blo 802343 1146683 := bstep (se 1 (by rfl) ⟨860012, by rfl⟩ : syracuseStep 1146683 = 1720025) B1720025
theorem B2719547 : Blo 802343 2719547 := bstep (se 1 (by rfl) ⟨2039660, by rfl⟩ : syracuseStep 2719547 = 4079321) B4079321
theorem B4063121 : Blo 802343 4063121 := bstep (se 2 (by rfl) ⟨1523670, by rfl⟩ : syracuseStep 4063121 = 3047341) B3047341
theorem B2719763 : Blo 802343 2719763 := bstep (se 1 (by rfl) ⟨2039822, by rfl⟩ : syracuseStep 2719763 = 4079645) B4079645
theorem B8257565 : Blo 802343 8257565 := bstep (se 3 (by rfl) ⟨1548293, by rfl⟩ : syracuseStep 8257565 = 3096587) B3096587
theorem B6094925 : Blo 802343 6094925 := bstep (se 3 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 6094925 = 2285597) B2285597
theorem B6881395 : Blo 802343 6881395 := bstep (se 1 (by rfl) ⟨5161046, by rfl⟩ : syracuseStep 6881395 = 10322093) B10322093
theorem B2720087 : Blo 802343 2720087 := bstep (se 1 (by rfl) ⟨2040065, by rfl⟩ : syracuseStep 2720087 = 4080131) B4080131
theorem B1147241 : Blo 802343 1147241 := bstep (se 2 (by rfl) ⟨430215, by rfl⟩ : syracuseStep 1147241 = 860431) B860431
theorem B99254807 : Blo 802343 99254807 := bstep (se 1 (by rfl) ⟨74441105, by rfl⟩ : syracuseStep 99254807 = 148882211) B148882211
theorem B4063769 : Blo 802343 4063769 := bstep (se 2 (by rfl) ⟨1523913, by rfl⟩ : syracuseStep 4063769 = 3047827) B3047827
theorem B2294369 : Blo 802343 2294369 := bstep (se 2 (by rfl) ⟨860388, by rfl⟩ : syracuseStep 2294369 = 1720777) B1720777
theorem B3048299 : Blo 802343 3048299 := bstep (se 1 (by rfl) ⟨2286224, by rfl⟩ : syracuseStep 3048299 = 4572449) B4572449
theorem B11600941 : Blo 802343 11600941 := bstep (se 3 (by rfl) ⟨2175176, by rfl⟩ : syracuseStep 11600941 = 4350353) B4350353
theorem B6882353 : Blo 802343 6882353 := bstep (se 2 (by rfl) ⟨2580882, by rfl⟩ : syracuseStep 6882353 = 5161765) B5161765
theorem B1017031 : Blo 802343 1017031 := bstep (se 1 (by rfl) ⟨762773, by rfl⟩ : syracuseStep 1017031 = 1525547) B1525547
theorem B6522227 : Blo 802343 6522227 := bstep (se 1 (by rfl) ⟨4891670, by rfl⟩ : syracuseStep 6522227 = 9783341) B9783341
theorem B2033039 : Blo 802343 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B2721167 : Blo 802343 2721167 := bstep (se 1 (by rfl) ⟨2040875, by rfl⟩ : syracuseStep 2721167 = 4081751) B4081751
theorem B2295485 : Blo 802343 2295485 := bstep (se 3 (by rfl) ⟨430403, by rfl⟩ : syracuseStep 2295485 = 860807) B860807
theorem B1935047 : Blo 802343 1935047 := bstep (se 1 (by rfl) ⟨1451285, by rfl⟩ : syracuseStep 1935047 = 2902571) B2902571
theorem B2033363 : Blo 802343 2033363 := bstep (se 1 (by rfl) ⟨1525022, by rfl⟩ : syracuseStep 2033363 = 3050045) B3050045
theorem B3442475 : Blo 802343 3442475 := bstep (se 1 (by rfl) ⟨2581856, by rfl⟩ : syracuseStep 3442475 = 5163713) B5163713
theorem B1017775 : Blo 802343 1017775 := bstep (se 1 (by rfl) ⟨763331, by rfl⟩ : syracuseStep 1017775 = 1526663) B1526663
theorem B2295827 : Blo 802343 2295827 := bstep (se 1 (by rfl) ⟨1721870, by rfl⟩ : syracuseStep 2295827 = 3443741) B3443741
theorem B30902309 : Blo 802343 30902309 := bstep (se 4 (by rfl) ⟨2897091, by rfl⟩ : syracuseStep 30902309 = 5794183) B5794183
theorem B6097355 : Blo 802343 6097355 := bstep (se 1 (by rfl) ⟨4573016, by rfl⟩ : syracuseStep 6097355 = 9146033) B9146033
theorem B3475993 : Blo 802343 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B1739387 : Blo 802343 1739387 := bstep (se 1 (by rfl) ⟨1304540, by rfl⟩ : syracuseStep 1739387 = 2609081) B2609081
theorem B13077395 : Blo 802343 13077395 := bstep (se 1 (by rfl) ⟨9808046, by rfl⟩ : syracuseStep 13077395 = 19616093) B19616093
theorem B19565495 : Blo 802343 19565495 := bstep (se 1 (by rfl) ⟨14674121, by rfl⟩ : syracuseStep 19565495 = 29348243) B29348243
theorem B1018919 : Blo 802343 1018919 := bstep (se 1 (by rfl) ⟨764189, by rfl⟩ : syracuseStep 1018919 = 1528379) B1528379
theorem B3050743 : Blo 802343 3050743 := bstep (se 1 (by rfl) ⟨2288057, by rfl⟩ : syracuseStep 3050743 = 4576115) B4576115
theorem B1019243 : Blo 802343 1019243 := bstep (se 1 (by rfl) ⟨764432, by rfl⟩ : syracuseStep 1019243 = 1528865) B1528865
theorem B4066685 : Blo 802343 4066685 := bstep (se 3 (by rfl) ⟨762503, by rfl⟩ : syracuseStep 4066685 = 1525007) B1525007
theorem B3051017 : Blo 802343 3051017 := bstep (se 2 (by rfl) ⟨1144131, by rfl⟩ : syracuseStep 3051017 = 2288263) B2288263
theorem B3051047 : Blo 802343 3051047 := bstep (se 1 (by rfl) ⟨2288285, by rfl⟩ : syracuseStep 3051047 = 4576571) B4576571
theorem B13405763 : Blo 802343 13405763 := bstep (se 1 (by rfl) ⟨10054322, by rfl⟩ : syracuseStep 13405763 = 20108645) B20108645
theorem B1805921 : Blo 802343 1805921 := bstep (se 2 (by rfl) ⟨677220, by rfl⟩ : syracuseStep 1805921 = 1354441) B1354441
theorem B19566269 : Blo 802343 19566269 := bstep (se 3 (by rfl) ⟨3668675, by rfl⟩ : syracuseStep 19566269 = 7337351) B7337351
theorem B11013869 : Blo 802343 11013869 := bstep (se 3 (by rfl) ⟨2065100, by rfl⟩ : syracuseStep 11013869 = 4130201) B4130201
theorem B4591403 : Blo 802343 4591403 := bstep (se 1 (by rfl) ⟨3443552, by rfl⟩ : syracuseStep 4591403 = 6887105) B6887105
theorem B2035631 : Blo 802343 2035631 := bstep (se 1 (by rfl) ⟨1526723, by rfl⟩ : syracuseStep 2035631 = 3053447) B3053447
theorem B1806263 : Blo 802343 1806263 := bstep (se 1 (by rfl) ⟨1354697, by rfl⟩ : syracuseStep 1806263 = 2709395) B2709395
theorem B5214215 : Blo 802343 5214215 := bstep (se 1 (by rfl) ⟨3910661, by rfl⟩ : syracuseStep 5214215 = 7821323) B7821323
theorem B3051715 : Blo 802343 3051715 := bstep (se 1 (by rfl) ⟨2288786, by rfl⟩ : syracuseStep 3051715 = 4577573) B4577573
theorem B3052019 : Blo 802343 3052019 := bstep (se 1 (by rfl) ⟨2289014, by rfl⟩ : syracuseStep 3052019 = 4578029) B4578029
theorem B1446407 : Blo 802343 1446407 := bstep (se 1 (by rfl) ⟨1084805, by rfl⟩ : syracuseStep 1446407 = 2169611) B2169611
theorem B1806857 : Blo 802343 1806857 := bstep (se 2 (by rfl) ⟨677571, by rfl⟩ : syracuseStep 1806857 = 1355143) B1355143
theorem B2036249 : Blo 802343 2036249 := bstep (se 2 (by rfl) ⟨763593, by rfl⟩ : syracuseStep 2036249 = 1527187) B1527187
theorem B4592153 : Blo 802343 4592153 := bstep (se 2 (by rfl) ⟨1722057, by rfl⟩ : syracuseStep 4592153 = 3444115) B3444115
theorem B1086151 : Blo 802343 1086151 := bstep (se 1 (by rfl) ⟨814613, by rfl⟩ : syracuseStep 1086151 = 1629227) B1629227
theorem B2757419 : Blo 802343 2757419 := bstep (se 1 (by rfl) ⟨2068064, by rfl⟩ : syracuseStep 2757419 = 4136129) B4136129
theorem B6099785 : Blo 802343 6099785 := bstep (se 2 (by rfl) ⟨2287419, by rfl⟩ : syracuseStep 6099785 = 4574839) B4574839
theorem B1807199 : Blo 802343 1807199 := bstep (se 1 (by rfl) ⟨1355399, by rfl⟩ : syracuseStep 1807199 = 2710799) B2710799
theorem B1446817 : Blo 802343 1446817 := bstep (se 2 (by rfl) ⟨542556, by rfl⟩ : syracuseStep 1446817 = 1085113) B1085113
theorem B3052475 : Blo 802343 3052475 := bstep (se 1 (by rfl) ⟨2289356, by rfl⟩ : syracuseStep 3052475 = 4578713) B4578713
theorem B1807379 : Blo 802343 1807379 := bstep (se 1 (by rfl) ⟨1355534, by rfl⟩ : syracuseStep 1807379 = 2711069) B2711069
theorem B857287 : Blo 802343 857287 := bstep (se 1 (by rfl) ⟨642965, by rfl⟩ : syracuseStep 857287 = 1285931) B1285931
theorem B5149975 : Blo 802343 5149975 := bstep (se 1 (by rfl) ⟨3862481, by rfl⟩ : syracuseStep 5149975 = 7724963) B7724963
theorem B1807721 : Blo 802343 1807721 := bstep (se 2 (by rfl) ⟨677895, by rfl⟩ : syracuseStep 1807721 = 1355791) B1355791
theorem B3872555 : Blo 802343 3872555 := bstep (se 1 (by rfl) ⟨2904416, by rfl⟩ : syracuseStep 3872555 = 5808833) B5808833
theorem B1808315 : Blo 802343 1808315 := bstep (se 1 (by rfl) ⟨1356236, by rfl⟩ : syracuseStep 1808315 = 2712473) B2712473
theorem B1808441 : Blo 802343 1808441 := bstep (se 2 (by rfl) ⟨678165, by rfl⟩ : syracuseStep 1808441 = 1356331) B1356331
theorem B50894905 : Blo 802343 50894905 := bstep (se 2 (by rfl) ⟨19085589, by rfl⟩ : syracuseStep 50894905 = 38171179) B38171179
theorem B89332109 : Blo 802343 89332109 := bstep (se 3 (by rfl) ⟨16749770, by rfl⟩ : syracuseStep 89332109 = 33499541) B33499541
theorem B1808783 : Blo 802343 1808783 := bstep (se 1 (by rfl) ⟨1356587, by rfl⟩ : syracuseStep 1808783 = 2713175) B2713175
theorem B5085881 : Blo 802343 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B1809107 : Blo 802343 1809107 := bstep (se 1 (by rfl) ⟨1356830, by rfl⟩ : syracuseStep 1809107 = 2713661) B2713661
theorem B1448777 : Blo 802343 1448777 := bstep (se 2 (by rfl) ⟨543291, by rfl⟩ : syracuseStep 1448777 = 1086583) B1086583
theorem B5217331 : Blo 802343 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B2038841 : Blo 802343 2038841 := bstep (se 2 (by rfl) ⟨764565, by rfl⟩ : syracuseStep 2038841 = 1529131) B1529131
theorem B3054935 : Blo 802343 3054935 := bstep (se 1 (by rfl) ⟨2291201, by rfl⟩ : syracuseStep 3054935 = 4582403) B4582403
theorem B6856109 : Blo 802343 6856109 := bstep (se 3 (by rfl) ⟨1285520, by rfl⟩ : syracuseStep 6856109 = 2571041) B2571041
theorem B1810043 : Blo 802343 1810043 := bstep (se 1 (by rfl) ⟨1357532, by rfl⟩ : syracuseStep 1810043 = 2715065) B2715065
theorem B4071059 : Blo 802343 4071059 := bstep (se 1 (by rfl) ⟨3053294, by rfl⟩ : syracuseStep 4071059 = 6106589) B6106589
theorem B1810169 : Blo 802343 1810169 := bstep (se 2 (by rfl) ⟨678813, by rfl⟩ : syracuseStep 1810169 = 1357627) B1357627
theorem B1810439 : Blo 802343 1810439 := bstep (se 1 (by rfl) ⟨1357829, by rfl⟩ : syracuseStep 1810439 = 2715659) B2715659
theorem B1810511 : Blo 802343 1810511 := bstep (se 1 (by rfl) ⟨1357883, by rfl⟩ : syracuseStep 1810511 = 2715767) B2715767
theorem B2891933 : Blo 802343 2891933 := bstep (se 3 (by rfl) ⟨542237, by rfl⟩ : syracuseStep 2891933 = 1084475) B1084475
theorem B1548649 : Blo 802343 1548649 := bstep (se 2 (by rfl) ⟨580743, by rfl⟩ : syracuseStep 1548649 = 1161487) B1161487
theorem B1810907 : Blo 802343 1810907 := bstep (se 1 (by rfl) ⟨1358180, by rfl⟩ : syracuseStep 1810907 = 2716361) B2716361
theorem B2040329 : Blo 802343 2040329 := bstep (se 2 (by rfl) ⟨765123, by rfl⟩ : syracuseStep 2040329 = 1530247) B1530247
theorem B1909459 : Blo 802343 1909459 := bstep (se 1 (by rfl) ⟨1432094, by rfl⟩ : syracuseStep 1909459 = 2864189) B2864189
theorem B1450847 : Blo 802343 1450847 := bstep (se 1 (by rfl) ⟨1088135, by rfl⟩ : syracuseStep 1450847 = 2176271) B2176271
theorem B1811375 : Blo 802343 1811375 := bstep (se 1 (by rfl) ⟨1358531, by rfl⟩ : syracuseStep 1811375 = 2717063) B2717063
theorem B1221671 : Blo 802343 1221671 := bstep (se 1 (by rfl) ⟨916253, by rfl⟩ : syracuseStep 1221671 = 1832507) B1832507
theorem B1811627 : Blo 802343 1811627 := bstep (se 1 (by rfl) ⟨1358720, by rfl⟩ : syracuseStep 1811627 = 2717441) B2717441
theorem B10298825 : Blo 802343 10298825 := bstep (se 2 (by rfl) ⟨3862059, by rfl⟩ : syracuseStep 10298825 = 7724119) B7724119
theorem B2172379 : Blo 802343 2172379 := bstep (se 1 (by rfl) ⟨1629284, by rfl⟩ : syracuseStep 2172379 = 3258569) B3258569
theorem B7743073 : Blo 802343 7743073 := bstep (se 2 (by rfl) ⟨2903652, by rfl⟩ : syracuseStep 7743073 = 5807305) B5807305
theorem B1812167 : Blo 802343 1812167 := bstep (se 1 (by rfl) ⟨1359125, by rfl⟩ : syracuseStep 1812167 = 2718251) B2718251
theorem B17409887 : Blo 802343 17409887 := bstep (se 1 (by rfl) ⟨13057415, by rfl⟩ : syracuseStep 17409887 = 26114831) B26114831
theorem B1451963 : Blo 802343 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B3057821 : Blo 802343 3057821 := bstep (se 3 (by rfl) ⟨573341, by rfl⟩ : syracuseStep 3057821 = 1146683) B1146683
theorem B1288391 : Blo 802343 1288391 := bstep (se 1 (by rfl) ⟨966293, by rfl⟩ : syracuseStep 1288391 = 1932587) B1932587
theorem B1354171 : Blo 802343 1354171 := bstep (se 1 (by rfl) ⟨1015628, by rfl⟩ : syracuseStep 1354171 = 2031257) B2031257
theorem B1288667 : Blo 802343 1288667 := bstep (se 1 (by rfl) ⟨966500, by rfl⟩ : syracuseStep 1288667 = 1933001) B1933001
theorem B1354279 : Blo 802343 1354279 := bstep (se 1 (by rfl) ⟨1015709, by rfl⟩ : syracuseStep 1354279 = 2031419) B2031419
theorem B1813031 : Blo 802343 1813031 := bstep (se 1 (by rfl) ⟨1359773, by rfl⟩ : syracuseStep 1813031 = 2719547) B2719547
theorem B1452583 : Blo 802343 1452583 := bstep (se 1 (by rfl) ⟨1089437, by rfl⟩ : syracuseStep 1452583 = 2178875) B2178875
theorem B3058505 : Blo 802343 3058505 := bstep (se 2 (by rfl) ⟨1146939, by rfl⟩ : syracuseStep 3058505 = 2293879) B2293879
theorem B1354603 : Blo 802343 1354603 := bstep (se 1 (by rfl) ⟨1015952, by rfl⟩ : syracuseStep 1354603 = 2031905) B2031905
theorem B1813355 : Blo 802343 1813355 := bstep (se 1 (by rfl) ⟨1360016, by rfl⟩ : syracuseStep 1813355 = 2720033) B2720033
theorem B1813409 : Blo 802343 1813409 := bstep (se 2 (by rfl) ⟨680028, by rfl⟩ : syracuseStep 1813409 = 1360057) B1360057
theorem B1813751 : Blo 802343 1813751 := bstep (se 1 (by rfl) ⟨1360313, by rfl⟩ : syracuseStep 1813751 = 2720627) B2720627
theorem B3059005 : Blo 802343 3059005 := bstep (se 3 (by rfl) ⟨573563, by rfl⟩ : syracuseStep 3059005 = 1147127) B1147127
theorem B75476549 : Blo 802343 75476549 := bstep (se 4 (by rfl) ⟨7075926, by rfl⟩ : syracuseStep 75476549 = 14151853) B14151853
theorem B6205177 : Blo 802343 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B1355663 : Blo 802343 1355663 := bstep (se 1 (by rfl) ⟨1016747, by rfl⟩ : syracuseStep 1355663 = 2033495) B2033495
theorem B1355899 : Blo 802343 1355899 := bstep (se 1 (by rfl) ⟨1016924, by rfl⟩ : syracuseStep 1355899 = 2033849) B2033849
theorem B3912065 : Blo 802343 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B21181027 : Blo 802343 21181027 := bstep (se 1 (by rfl) ⟨15885770, by rfl⟩ : syracuseStep 21181027 = 31771541) B31771541
theorem B4076243 : Blo 802343 4076243 := bstep (se 1 (by rfl) ⟨3057182, by rfl⟩ : syracuseStep 4076243 = 6114365) B6114365
theorem B4338461 : Blo 802343 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B1356763 : Blo 802343 1356763 := bstep (se 1 (by rfl) ⟨1017572, by rfl⟩ : syracuseStep 1356763 = 2035145) B2035145
theorem B3060737 : Blo 802343 3060737 := bstep (se 2 (by rfl) ⟨1147776, by rfl⟩ : syracuseStep 3060737 = 2295553) B2295553
theorem B2176475 : Blo 802343 2176475 := bstep (se 1 (by rfl) ⟨1632356, by rfl⟩ : syracuseStep 2176475 = 3264713) B3264713
theorem B1357391 : Blo 802343 1357391 := bstep (se 1 (by rfl) ⟨1018043, by rfl⟩ : syracuseStep 1357391 = 2036087) B2036087
theorem B2897657 : Blo 802343 2897657 := bstep (se 2 (by rfl) ⟨1086621, by rfl⟩ : syracuseStep 2897657 = 2173243) B2173243
theorem B1718111 : Blo 802343 1718111 := bstep (se 1 (by rfl) ⟨1288583, by rfl⟩ : syracuseStep 1718111 = 2577167) B2577167
theorem B1718633 : Blo 802343 1718633 := bstep (se 2 (by rfl) ⟨644487, by rfl⟩ : syracuseStep 1718633 = 1288975) B1288975
theorem B2177405 : Blo 802343 2177405 := bstep (se 3 (by rfl) ⟨408263, by rfl⟩ : syracuseStep 2177405 = 816527) B816527
theorem B1358255 : Blo 802343 1358255 := bstep (se 1 (by rfl) ⟨1018691, by rfl⟩ : syracuseStep 1358255 = 2037383) B2037383
theorem B2570887 : Blo 802343 2570887 := bstep (se 1 (by rfl) ⟨1928165, by rfl⟩ : syracuseStep 2570887 = 3856331) B3856331
theorem B11778695 : Blo 802343 11778695 := bstep (se 1 (by rfl) ⟨8834021, by rfl⟩ : syracuseStep 11778695 = 17668043) B17668043
theorem B1653577 : Blo 802343 1653577 := bstep (se 2 (by rfl) ⟨620091, by rfl⟩ : syracuseStep 1653577 = 1240183) B1240183
theorem B1358687 : Blo 802343 1358687 := bstep (se 1 (by rfl) ⟨1019015, by rfl⟩ : syracuseStep 1358687 = 2038031) B2038031
theorem B4078511 : Blo 802343 4078511 := bstep (se 1 (by rfl) ⟨3058883, by rfl⟩ : syracuseStep 4078511 = 6117767) B6117767
theorem B30981041 : Blo 802343 30981041 := bstep (se 2 (by rfl) ⟨11617890, by rfl⟩ : syracuseStep 30981041 = 23235781) B23235781
theorem B4570283 : Blo 802343 4570283 := bstep (se 1 (by rfl) ⟨3427712, by rfl⟩ : syracuseStep 4570283 = 6855425) B6855425
theorem B1359247 : Blo 802343 1359247 := bstep (se 1 (by rfl) ⟨1019435, by rfl⟩ : syracuseStep 1359247 = 2038871) B2038871
theorem B802343 : Blo 802343 802343 := bstep (se 1 (by rfl) ⟨601757, by rfl⟩ : syracuseStep 802343 = 1203515) B1203515
theorem B1392167 : Blo 802343 1392167 := bstep (se 1 (by rfl) ⟨1044125, by rfl⟩ : syracuseStep 1392167 = 2088251) B2088251
theorem B802383 : Blo 802343 802383 := bstep (se 1 (by rfl) ⟨601787, by rfl⟩ : syracuseStep 802383 = 1203575) B1203575
theorem B802399 : Blo 802343 802399 := bstep (se 1 (by rfl) ⟨601799, by rfl⟩ : syracuseStep 802399 = 1203599) B1203599
theorem B802427 : Blo 802343 802427 := bstep (se 1 (by rfl) ⟨601820, by rfl⟩ : syracuseStep 802427 = 1203641) B1203641
theorem B802479 : Blo 802343 802479 := bstep (se 1 (by rfl) ⟨601859, by rfl⟩ : syracuseStep 802479 = 1203719) B1203719
theorem B802503 : Blo 802343 802503 := bstep (se 1 (by rfl) ⟨601877, by rfl⟩ : syracuseStep 802503 = 1203755) B1203755
theorem B802523 : Blo 802343 802523 := bstep (se 1 (by rfl) ⟨601892, by rfl⟩ : syracuseStep 802523 = 1203785) B1203785
theorem B802599 : Blo 802343 802599 := bstep (se 1 (by rfl) ⟨601949, by rfl⟩ : syracuseStep 802599 = 1203899) B1203899
theorem B802639 : Blo 802343 802639 := bstep (se 1 (by rfl) ⟨601979, by rfl⟩ : syracuseStep 802639 = 1203959) B1203959
theorem B802655 : Blo 802343 802655 := bstep (se 1 (by rfl) ⟨601991, by rfl⟩ : syracuseStep 802655 = 1203983) B1203983
theorem B3260267 : Blo 802343 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B802683 : Blo 802343 802683 := bstep (se 1 (by rfl) ⟨602012, by rfl⟩ : syracuseStep 802683 = 1204025) B1204025
theorem B802735 : Blo 802343 802735 := bstep (se 1 (by rfl) ⟨602051, by rfl⟩ : syracuseStep 802735 = 1204103) B1204103
theorem B802759 : Blo 802343 802759 := bstep (se 1 (by rfl) ⟨602069, by rfl⟩ : syracuseStep 802759 = 1204139) B1204139
theorem B802779 : Blo 802343 802779 := bstep (se 1 (by rfl) ⟨602084, by rfl⟩ : syracuseStep 802779 = 1204169) B1204169
theorem B802855 : Blo 802343 802855 := bstep (se 1 (by rfl) ⟨602141, by rfl⟩ : syracuseStep 802855 = 1204283) B1204283
theorem B1359929 : Blo 802343 1359929 := bstep (se 2 (by rfl) ⟨509973, by rfl⟩ : syracuseStep 1359929 = 1019947) B1019947
theorem B802895 : Blo 802343 802895 := bstep (se 1 (by rfl) ⟨602171, by rfl⟩ : syracuseStep 802895 = 1204343) B1204343
theorem B3620945 : Blo 802343 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B802911 : Blo 802343 802911 := bstep (se 1 (by rfl) ⟨602183, by rfl⟩ : syracuseStep 802911 = 1204367) B1204367
theorem B802939 : Blo 802343 802939 := bstep (se 1 (by rfl) ⟨602204, by rfl⟩ : syracuseStep 802939 = 1204409) B1204409
theorem B802991 : Blo 802343 802991 := bstep (se 1 (by rfl) ⟨602243, by rfl⟩ : syracuseStep 802991 = 1204487) B1204487
theorem B803015 : Blo 802343 803015 := bstep (se 1 (by rfl) ⟨602261, by rfl⟩ : syracuseStep 803015 = 1204523) B1204523
theorem B803035 : Blo 802343 803035 := bstep (se 1 (by rfl) ⟨602276, by rfl⟩ : syracuseStep 803035 = 1204553) B1204553
theorem B11583755 : Blo 802343 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B803111 : Blo 802343 803111 := bstep (se 1 (by rfl) ⟨602333, by rfl⟩ : syracuseStep 803111 = 1204667) B1204667
theorem B6603059 : Blo 802343 6603059 := bstep (se 1 (by rfl) ⟨4952294, by rfl⟩ : syracuseStep 6603059 = 9904589) B9904589
theorem B803151 : Blo 802343 803151 := bstep (se 1 (by rfl) ⟨602363, by rfl⟩ : syracuseStep 803151 = 1204727) B1204727
theorem B2572631 : Blo 802343 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B803167 : Blo 802343 803167 := bstep (se 1 (by rfl) ⟨602375, by rfl⟩ : syracuseStep 803167 = 1204751) B1204751
theorem B803195 : Blo 802343 803195 := bstep (se 1 (by rfl) ⟨602396, by rfl⟩ : syracuseStep 803195 = 1204793) B1204793
theorem B803247 : Blo 802343 803247 := bstep (se 1 (by rfl) ⟨602435, by rfl⟩ : syracuseStep 803247 = 1204871) B1204871
theorem B803271 : Blo 802343 803271 := bstep (se 1 (by rfl) ⟨602453, by rfl⟩ : syracuseStep 803271 = 1204907) B1204907
theorem B1524187 : Blo 802343 1524187 := bstep (se 1 (by rfl) ⟨1143140, by rfl⟩ : syracuseStep 1524187 = 2286281) B2286281
theorem B803291 : Blo 802343 803291 := bstep (se 1 (by rfl) ⟨602468, by rfl⟩ : syracuseStep 803291 = 1204937) B1204937
theorem B1524233 : Blo 802343 1524233 := bstep (se 2 (by rfl) ⟨571587, by rfl⟩ : syracuseStep 1524233 = 1143175) B1143175
theorem B803367 : Blo 802343 803367 := bstep (se 1 (by rfl) ⟨602525, by rfl⟩ : syracuseStep 803367 = 1205051) B1205051
theorem B967207 : Blo 802343 967207 := bstep (se 1 (by rfl) ⟨725405, by rfl⟩ : syracuseStep 967207 = 1450811) B1450811
theorem B803407 : Blo 802343 803407 := bstep (se 1 (by rfl) ⟨602555, by rfl⟩ : syracuseStep 803407 = 1205111) B1205111
theorem B803423 : Blo 802343 803423 := bstep (se 1 (by rfl) ⟨602567, by rfl⟩ : syracuseStep 803423 = 1205135) B1205135
theorem B803451 : Blo 802343 803451 := bstep (se 1 (by rfl) ⟨602588, by rfl⟩ : syracuseStep 803451 = 1205177) B1205177
theorem B803503 : Blo 802343 803503 := bstep (se 1 (by rfl) ⟨602627, by rfl⟩ : syracuseStep 803503 = 1205255) B1205255
theorem B803527 : Blo 802343 803527 := bstep (se 1 (by rfl) ⟨602645, by rfl⟩ : syracuseStep 803527 = 1205291) B1205291
theorem B803547 : Blo 802343 803547 := bstep (se 1 (by rfl) ⟨602660, by rfl⟩ : syracuseStep 803547 = 1205321) B1205321
theorem B1360631 : Blo 802343 1360631 := bstep (se 1 (by rfl) ⟨1020473, by rfl⟩ : syracuseStep 1360631 = 2040947) B2040947
theorem B803623 : Blo 802343 803623 := bstep (se 1 (by rfl) ⟨602717, by rfl⟩ : syracuseStep 803623 = 1205435) B1205435
theorem B803663 : Blo 802343 803663 := bstep (se 1 (by rfl) ⟨602747, by rfl⟩ : syracuseStep 803663 = 1205495) B1205495
theorem B1524575 : Blo 802343 1524575 := bstep (se 1 (by rfl) ⟨1143431, by rfl⟩ : syracuseStep 1524575 = 2286863) B2286863
theorem B803679 : Blo 802343 803679 := bstep (se 1 (by rfl) ⟨602759, by rfl⟩ : syracuseStep 803679 = 1205519) B1205519
theorem B803707 : Blo 802343 803707 := bstep (se 1 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 803707 = 1205561) B1205561
theorem B803759 : Blo 802343 803759 := bstep (se 1 (by rfl) ⟨602819, by rfl⟩ : syracuseStep 803759 = 1205639) B1205639
theorem B803783 : Blo 802343 803783 := bstep (se 1 (by rfl) ⟨602837, by rfl⟩ : syracuseStep 803783 = 1205675) B1205675
theorem B803803 : Blo 802343 803803 := bstep (se 1 (by rfl) ⟨602852, by rfl⟩ : syracuseStep 803803 = 1205705) B1205705
theorem B11781085 : Blo 802343 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B803879 : Blo 802343 803879 := bstep (se 1 (by rfl) ⟨602909, by rfl⟩ : syracuseStep 803879 = 1205819) B1205819
theorem B8930371 : Blo 802343 8930371 := bstep (se 1 (by rfl) ⟨6697778, by rfl⟩ : syracuseStep 8930371 = 13395557) B13395557
theorem B803919 : Blo 802343 803919 := bstep (se 1 (by rfl) ⟨602939, by rfl⟩ : syracuseStep 803919 = 1205879) B1205879
theorem B803935 : Blo 802343 803935 := bstep (se 1 (by rfl) ⟨602951, by rfl⟩ : syracuseStep 803935 = 1205903) B1205903
theorem B803963 : Blo 802343 803963 := bstep (se 1 (by rfl) ⟨602972, by rfl⟩ : syracuseStep 803963 = 1205945) B1205945
theorem B804015 : Blo 802343 804015 := bstep (se 1 (by rfl) ⟨603011, by rfl⟩ : syracuseStep 804015 = 1206023) B1206023
theorem B2901187 : Blo 802343 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B804039 : Blo 802343 804039 := bstep (se 1 (by rfl) ⟨603029, by rfl⟩ : syracuseStep 804039 = 1206059) B1206059
theorem B804059 : Blo 802343 804059 := bstep (se 1 (by rfl) ⟨603044, by rfl⟩ : syracuseStep 804059 = 1206089) B1206089
theorem B804135 : Blo 802343 804135 := bstep (se 1 (by rfl) ⟨603101, by rfl⟩ : syracuseStep 804135 = 1206203) B1206203
theorem B804175 : Blo 802343 804175 := bstep (se 1 (by rfl) ⟨603131, by rfl⟩ : syracuseStep 804175 = 1206263) B1206263
theorem B804191 : Blo 802343 804191 := bstep (se 1 (by rfl) ⟨603143, by rfl⟩ : syracuseStep 804191 = 1206287) B1206287
theorem B804219 : Blo 802343 804219 := bstep (se 1 (by rfl) ⟨603164, by rfl⟩ : syracuseStep 804219 = 1206329) B1206329
theorem B804271 : Blo 802343 804271 := bstep (se 1 (by rfl) ⟨603203, by rfl⟩ : syracuseStep 804271 = 1206407) B1206407
theorem B804295 : Blo 802343 804295 := bstep (se 1 (by rfl) ⟨603221, by rfl⟩ : syracuseStep 804295 = 1206443) B1206443
theorem B804315 : Blo 802343 804315 := bstep (se 1 (by rfl) ⟨603236, by rfl⟩ : syracuseStep 804315 = 1206473) B1206473
theorem B1721819 : Blo 802343 1721819 := bstep (se 1 (by rfl) ⟨1291364, by rfl⟩ : syracuseStep 1721819 = 2582729) B2582729
theorem B2573849 : Blo 802343 2573849 := bstep (se 2 (by rfl) ⟨965193, by rfl⟩ : syracuseStep 2573849 = 1930387) B1930387
theorem B902695 : Blo 802343 902695 := bstep (se 1 (by rfl) ⟨677021, by rfl⟩ : syracuseStep 902695 = 1354043) B1354043
theorem B804391 : Blo 802343 804391 := bstep (se 1 (by rfl) ⟨603293, by rfl⟩ : syracuseStep 804391 = 1206587) B1206587
theorem B804431 : Blo 802343 804431 := bstep (se 1 (by rfl) ⟨603323, by rfl⟩ : syracuseStep 804431 = 1206647) B1206647
theorem B804447 : Blo 802343 804447 := bstep (se 1 (by rfl) ⟨603335, by rfl⟩ : syracuseStep 804447 = 1206671) B1206671
theorem B804475 : Blo 802343 804475 := bstep (se 1 (by rfl) ⟨603356, by rfl⟩ : syracuseStep 804475 = 1206713) B1206713
theorem B6112907 : Blo 802343 6112907 := bstep (se 1 (by rfl) ⟨4584680, by rfl⟩ : syracuseStep 6112907 = 9169361) B9169361
theorem B804527 : Blo 802343 804527 := bstep (se 1 (by rfl) ⟨603395, by rfl⟩ : syracuseStep 804527 = 1206791) B1206791
theorem B804551 : Blo 802343 804551 := bstep (se 1 (by rfl) ⟨603413, by rfl⟩ : syracuseStep 804551 = 1206827) B1206827
theorem B804571 : Blo 802343 804571 := bstep (se 1 (by rfl) ⟨603428, by rfl⟩ : syracuseStep 804571 = 1206857) B1206857
theorem B804647 : Blo 802343 804647 := bstep (se 1 (by rfl) ⟨603485, by rfl⟩ : syracuseStep 804647 = 1206971) B1206971
theorem B804687 : Blo 802343 804687 := bstep (se 1 (by rfl) ⟨603515, by rfl⟩ : syracuseStep 804687 = 1207031) B1207031
theorem B804703 : Blo 802343 804703 := bstep (se 1 (by rfl) ⟨603527, by rfl⟩ : syracuseStep 804703 = 1207055) B1207055
theorem B804731 : Blo 802343 804731 := bstep (se 1 (by rfl) ⟨603548, by rfl⟩ : syracuseStep 804731 = 1207097) B1207097
theorem B804783 : Blo 802343 804783 := bstep (se 1 (by rfl) ⟨603587, by rfl⟩ : syracuseStep 804783 = 1207175) B1207175
theorem B1525691 : Blo 802343 1525691 := bstep (se 1 (by rfl) ⟨1144268, by rfl⟩ : syracuseStep 1525691 = 2288537) B2288537
theorem B804807 : Blo 802343 804807 := bstep (se 1 (by rfl) ⟨603605, by rfl⟩ : syracuseStep 804807 = 1207211) B1207211
theorem B804827 : Blo 802343 804827 := bstep (se 1 (by rfl) ⟨603620, by rfl⟩ : syracuseStep 804827 = 1207241) B1207241
theorem B4573199 : Blo 802343 4573199 := bstep (se 1 (by rfl) ⟨3429899, by rfl⟩ : syracuseStep 4573199 = 6859799) B6859799
theorem B804903 : Blo 802343 804903 := bstep (se 1 (by rfl) ⟨603677, by rfl⟩ : syracuseStep 804903 = 1207355) B1207355
theorem B804943 : Blo 802343 804943 := bstep (se 1 (by rfl) ⟨603707, by rfl⟩ : syracuseStep 804943 = 1207415) B1207415
theorem B5163097 : Blo 802343 5163097 := bstep (se 2 (by rfl) ⟨1936161, by rfl⟩ : syracuseStep 5163097 = 3872323) B3872323
theorem B804959 : Blo 802343 804959 := bstep (se 1 (by rfl) ⟨603719, by rfl⟩ : syracuseStep 804959 = 1207439) B1207439
theorem B804987 : Blo 802343 804987 := bstep (se 1 (by rfl) ⟨603740, by rfl⟩ : syracuseStep 804987 = 1207481) B1207481
theorem B805039 : Blo 802343 805039 := bstep (se 1 (by rfl) ⟨603779, by rfl⟩ : syracuseStep 805039 = 1207559) B1207559
theorem B805063 : Blo 802343 805063 := bstep (se 1 (by rfl) ⟨603797, by rfl⟩ : syracuseStep 805063 = 1207595) B1207595
theorem B805083 : Blo 802343 805083 := bstep (se 1 (by rfl) ⟨603812, by rfl⟩ : syracuseStep 805083 = 1207625) B1207625
theorem B2902283 : Blo 802343 2902283 := bstep (se 1 (by rfl) ⟨2176712, by rfl⟩ : syracuseStep 2902283 = 4353425) B4353425
theorem B805159 : Blo 802343 805159 := bstep (se 1 (by rfl) ⟨603869, by rfl⟩ : syracuseStep 805159 = 1207739) B1207739
theorem B805199 : Blo 802343 805199 := bstep (se 1 (by rfl) ⟨603899, by rfl⟩ : syracuseStep 805199 = 1207799) B1207799
theorem B805215 : Blo 802343 805215 := bstep (se 1 (by rfl) ⟨603911, by rfl⟩ : syracuseStep 805215 = 1207823) B1207823
theorem B805243 : Blo 802343 805243 := bstep (se 1 (by rfl) ⟨603932, by rfl⟩ : syracuseStep 805243 = 1207865) B1207865
theorem B2902397 : Blo 802343 2902397 := bstep (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) B1088399
theorem B1526177 : Blo 802343 1526177 := bstep (se 2 (by rfl) ⟨572316, by rfl⟩ : syracuseStep 1526177 = 1144633) B1144633
theorem B805295 : Blo 802343 805295 := bstep (se 1 (by rfl) ⟨603971, by rfl⟩ : syracuseStep 805295 = 1207943) B1207943
theorem B805319 : Blo 802343 805319 := bstep (se 1 (by rfl) ⟨603989, by rfl⟩ : syracuseStep 805319 = 1207979) B1207979
theorem B805339 : Blo 802343 805339 := bstep (se 1 (by rfl) ⟨604004, by rfl⟩ : syracuseStep 805339 = 1208009) B1208009
theorem B8243693 : Blo 802343 8243693 := bstep (se 3 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 8243693 = 3091385) B3091385
theorem B805415 : Blo 802343 805415 := bstep (se 1 (by rfl) ⟨604061, by rfl⟩ : syracuseStep 805415 = 1208123) B1208123
theorem B805455 : Blo 802343 805455 := bstep (se 1 (by rfl) ⟨604091, by rfl⟩ : syracuseStep 805455 = 1208183) B1208183
theorem B805471 : Blo 802343 805471 := bstep (se 1 (by rfl) ⟨604103, by rfl⟩ : syracuseStep 805471 = 1208207) B1208207
theorem B805499 : Blo 802343 805499 := bstep (se 1 (by rfl) ⟨604124, by rfl⟩ : syracuseStep 805499 = 1208249) B1208249
theorem B805551 : Blo 802343 805551 := bstep (se 1 (by rfl) ⟨604163, by rfl⟩ : syracuseStep 805551 = 1208327) B1208327
theorem B5491385 : Blo 802343 5491385 := bstep (se 2 (by rfl) ⟨2059269, by rfl⟩ : syracuseStep 5491385 = 4118539) B4118539
theorem B805575 : Blo 802343 805575 := bstep (se 1 (by rfl) ⟨604181, by rfl⟩ : syracuseStep 805575 = 1208363) B1208363
theorem B4573907 : Blo 802343 4573907 := bstep (se 1 (by rfl) ⟨3430430, by rfl⟩ : syracuseStep 4573907 = 6860861) B6860861
theorem B805595 : Blo 802343 805595 := bstep (se 1 (by rfl) ⟨604196, by rfl⟩ : syracuseStep 805595 = 1208393) B1208393
theorem B1526519 : Blo 802343 1526519 := bstep (se 1 (by rfl) ⟨1144889, by rfl⟩ : syracuseStep 1526519 = 2289779) B2289779
theorem B805671 : Blo 802343 805671 := bstep (se 1 (by rfl) ⟨604253, by rfl⟩ : syracuseStep 805671 = 1208507) B1208507
theorem B805711 : Blo 802343 805711 := bstep (se 1 (by rfl) ⟨604283, by rfl⟩ : syracuseStep 805711 = 1208567) B1208567
theorem B805727 : Blo 802343 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B805755 : Blo 802343 805755 := bstep (se 1 (by rfl) ⟨604316, by rfl⟩ : syracuseStep 805755 = 1208633) B1208633
theorem B805807 : Blo 802343 805807 := bstep (se 1 (by rfl) ⟨604355, by rfl⟩ : syracuseStep 805807 = 1208711) B1208711
theorem B805831 : Blo 802343 805831 := bstep (se 1 (by rfl) ⟨604373, by rfl⟩ : syracuseStep 805831 = 1208747) B1208747
theorem B805851 : Blo 802343 805851 := bstep (se 1 (by rfl) ⟨604388, by rfl⟩ : syracuseStep 805851 = 1208777) B1208777
theorem B805927 : Blo 802343 805927 := bstep (se 1 (by rfl) ⟨604445, by rfl⟩ : syracuseStep 805927 = 1208891) B1208891
theorem B805967 : Blo 802343 805967 := bstep (se 1 (by rfl) ⟨604475, by rfl⟩ : syracuseStep 805967 = 1208951) B1208951
theorem B805983 : Blo 802343 805983 := bstep (se 1 (by rfl) ⟨604487, by rfl⟩ : syracuseStep 805983 = 1208975) B1208975
theorem B904315 : Blo 802343 904315 := bstep (se 1 (by rfl) ⟨678236, by rfl⟩ : syracuseStep 904315 = 1356473) B1356473
theorem B806011 : Blo 802343 806011 := bstep (se 1 (by rfl) ⟨604508, by rfl⟩ : syracuseStep 806011 = 1209017) B1209017
theorem B806063 : Blo 802343 806063 := bstep (se 1 (by rfl) ⟨604547, by rfl⟩ : syracuseStep 806063 = 1209095) B1209095
theorem B806087 : Blo 802343 806087 := bstep (se 1 (by rfl) ⟨604565, by rfl⟩ : syracuseStep 806087 = 1209131) B1209131
theorem B806107 : Blo 802343 806107 := bstep (se 1 (by rfl) ⟨604580, by rfl⟩ : syracuseStep 806107 = 1209161) B1209161
theorem B806183 : Blo 802343 806183 := bstep (se 1 (by rfl) ⟨604637, by rfl⟩ : syracuseStep 806183 = 1209275) B1209275
theorem B806223 : Blo 802343 806223 := bstep (se 1 (by rfl) ⟨604667, by rfl⟩ : syracuseStep 806223 = 1209335) B1209335
theorem B806239 : Blo 802343 806239 := bstep (se 1 (by rfl) ⟨604679, by rfl⟩ : syracuseStep 806239 = 1209359) B1209359
theorem B806267 : Blo 802343 806267 := bstep (se 1 (by rfl) ⟨604700, by rfl⟩ : syracuseStep 806267 = 1209401) B1209401
theorem B5229989 : Blo 802343 5229989 := bstep (se 4 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 5229989 = 980623) B980623
theorem B806319 : Blo 802343 806319 := bstep (se 1 (by rfl) ⟨604739, by rfl⟩ : syracuseStep 806319 = 1209479) B1209479
theorem B806343 : Blo 802343 806343 := bstep (se 1 (by rfl) ⟨604757, by rfl⟩ : syracuseStep 806343 = 1209515) B1209515
theorem B2903539 : Blo 802343 2903539 := bstep (se 1 (by rfl) ⟨2177654, by rfl⟩ : syracuseStep 2903539 = 4355309) B4355309
theorem B904783 : Blo 802343 904783 := bstep (se 1 (by rfl) ⟨678587, by rfl⟩ : syracuseStep 904783 = 1357175) B1357175
theorem B905179 : Blo 802343 905179 := bstep (se 1 (by rfl) ⟨678884, by rfl⟩ : syracuseStep 905179 = 1357769) B1357769
theorem B1527817 : Blo 802343 1527817 := bstep (se 2 (by rfl) ⟨572931, by rfl⟩ : syracuseStep 1527817 = 1145863) B1145863
theorem B3428669 : Blo 802343 3428669 := bstep (se 3 (by rfl) ⟨642875, by rfl⟩ : syracuseStep 3428669 = 1285751) B1285751
theorem B1528159 : Blo 802343 1528159 := bstep (se 1 (by rfl) ⟨1146119, by rfl⟩ : syracuseStep 1528159 = 2292239) B2292239
theorem B905647 : Blo 802343 905647 := bstep (se 1 (by rfl) ⟨679235, by rfl⟩ : syracuseStep 905647 = 1358471) B1358471
theorem B2708153 : Blo 802343 2708153 := bstep (se 2 (by rfl) ⟨1015557, by rfl⟩ : syracuseStep 2708153 = 2031115) B2031115
theorem B5493577 : Blo 802343 5493577 := bstep (se 2 (by rfl) ⟨2060091, by rfl⟩ : syracuseStep 5493577 = 4120183) B4120183
theorem B906079 : Blo 802343 906079 := bstep (se 1 (by rfl) ⟨679559, by rfl⟩ : syracuseStep 906079 = 1359119) B1359119
theorem B5297125 : Blo 802343 5297125 := bstep (se 4 (by rfl) ⟨496605, by rfl⟩ : syracuseStep 5297125 = 993211) B993211
theorem B906439 : Blo 802343 906439 := bstep (se 1 (by rfl) ⟨679829, by rfl⟩ : syracuseStep 906439 = 1359659) B1359659
theorem B2708747 : Blo 802343 2708747 := bstep (se 1 (by rfl) ⟨2031560, by rfl⟩ : syracuseStep 2708747 = 4063121) B4063121
theorem B1529275 : Blo 802343 1529275 := bstep (se 1 (by rfl) ⟨1146956, by rfl⟩ : syracuseStep 1529275 = 2293913) B2293913
theorem B5789171 : Blo 802343 5789171 := bstep (se 1 (by rfl) ⟨4341878, by rfl⟩ : syracuseStep 5789171 = 8683757) B8683757
theorem B1529351 : Blo 802343 1529351 := bstep (se 1 (by rfl) ⟨1147013, by rfl⟩ : syracuseStep 1529351 = 2294027) B2294027
theorem B2709017 : Blo 802343 2709017 := bstep (se 2 (by rfl) ⟨1015881, by rfl⟩ : syracuseStep 2709017 = 2031763) B2031763
theorem B9787027 : Blo 802343 9787027 := bstep (se 1 (by rfl) ⟨7340270, by rfl⟩ : syracuseStep 9787027 = 14680541) B14680541
theorem B4347715 : Blo 802343 4347715 := bstep (se 1 (by rfl) ⟨3260786, by rfl⟩ : syracuseStep 4347715 = 6521573) B6521573
theorem B3266399 : Blo 802343 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B6117281 : Blo 802343 6117281 := bstep (se 2 (by rfl) ⟨2293980, by rfl⟩ : syracuseStep 6117281 = 4587961) B4587961
theorem B1529761 : Blo 802343 1529761 := bstep (se 2 (by rfl) ⟨573660, by rfl⟩ : syracuseStep 1529761 = 1147321) B1147321
theorem B2578679 : Blo 802343 2578679 := bstep (se 1 (by rfl) ⟨1934009, by rfl⟩ : syracuseStep 2578679 = 3868019) B3868019
theorem B1530103 : Blo 802343 1530103 := bstep (se 1 (by rfl) ⟨1147577, by rfl⟩ : syracuseStep 1530103 = 2295155) B2295155
theorem B2447759 : Blo 802343 2447759 := bstep (se 1 (by rfl) ⟨1835819, by rfl⟩ : syracuseStep 2447759 = 3671639) B3671639
theorem B1530407 : Blo 802343 1530407 := bstep (se 1 (by rfl) ⟨1147805, by rfl⟩ : syracuseStep 1530407 = 2295611) B2295611
theorem B2710151 : Blo 802343 2710151 := bstep (se 1 (by rfl) ⟨2032613, by rfl⟩ : syracuseStep 2710151 = 4065227) B4065227
theorem B2710205 : Blo 802343 2710205 := bstep (se 3 (by rfl) ⟨508163, by rfl⟩ : syracuseStep 2710205 = 1016327) B1016327
theorem B2710367 : Blo 802343 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B7527397 : Blo 802343 7527397 := bstep (se 4 (by rfl) ⟨705693, by rfl⟩ : syracuseStep 7527397 = 1411387) B1411387
theorem B2710529 : Blo 802343 2710529 := bstep (se 2 (by rfl) ⟨1016448, by rfl⟩ : syracuseStep 2710529 = 2032897) B2032897
theorem B22666283 : Blo 802343 22666283 := bstep (se 1 (by rfl) ⟨16999712, by rfl⟩ : syracuseStep 22666283 = 33999425) B33999425
theorem B3857561 : Blo 802343 3857561 := bstep (se 2 (by rfl) ⟨1446585, by rfl⟩ : syracuseStep 3857561 = 2893171) B2893171
theorem B2579627 : Blo 802343 2579627 := bstep (se 1 (by rfl) ⟨1934720, by rfl⟩ : syracuseStep 2579627 = 3869441) B3869441
theorem B1203551 : Blo 802343 1203551 := bstep (se 1 (by rfl) ⟨902663, by rfl⟩ : syracuseStep 1203551 = 1805327) B1805327
theorem B1203563 : Blo 802343 1203563 := bstep (se 1 (by rfl) ⟨902672, by rfl⟩ : syracuseStep 1203563 = 1805345) B1805345
theorem B1203791 : Blo 802343 1203791 := bstep (se 1 (by rfl) ⟨902843, by rfl⟩ : syracuseStep 1203791 = 1805687) B1805687
theorem B44064395 : Blo 802343 44064395 := bstep (se 1 (by rfl) ⟨33048296, by rfl⟩ : syracuseStep 44064395 = 66096593) B66096593
theorem B1203911 : Blo 802343 1203911 := bstep (se 1 (by rfl) ⟨902933, by rfl⟩ : syracuseStep 1203911 = 1805867) B1805867
theorem B4579031 : Blo 802343 4579031 := bstep (se 1 (by rfl) ⟨3434273, by rfl⟩ : syracuseStep 4579031 = 6868547) B6868547
theorem B2711339 : Blo 802343 2711339 := bstep (se 1 (by rfl) ⟨2033504, by rfl⟩ : syracuseStep 2711339 = 4067009) B4067009
theorem B1204073 : Blo 802343 1204073 := bstep (se 2 (by rfl) ⟨451527, by rfl⟩ : syracuseStep 1204073 = 903055) B903055
theorem B1204151 : Blo 802343 1204151 := bstep (se 1 (by rfl) ⟨903113, by rfl⟩ : syracuseStep 1204151 = 1806227) B1806227
theorem B1204187 : Blo 802343 1204187 := bstep (se 1 (by rfl) ⟨903140, by rfl⟩ : syracuseStep 1204187 = 1806281) B1806281
theorem B2711609 : Blo 802343 2711609 := bstep (se 2 (by rfl) ⟨1016853, by rfl⟩ : syracuseStep 2711609 = 2033707) B2033707
theorem B2711933 : Blo 802343 2711933 := bstep (se 3 (by rfl) ⟨508487, by rfl⟩ : syracuseStep 2711933 = 1016975) B1016975
theorem B3268993 : Blo 802343 3268993 := bstep (se 2 (by rfl) ⟨1225872, by rfl⟩ : syracuseStep 3268993 = 2451745) B2451745
theorem B1204655 : Blo 802343 1204655 := bstep (se 1 (by rfl) ⟨903491, by rfl⟩ : syracuseStep 1204655 = 1806983) B1806983
theorem B1204745 : Blo 802343 1204745 := bstep (se 2 (by rfl) ⟨451779, by rfl⟩ : syracuseStep 1204745 = 903559) B903559
theorem B1204775 : Blo 802343 1204775 := bstep (se 1 (by rfl) ⟨903581, by rfl⟩ : syracuseStep 1204775 = 1807163) B1807163
theorem B1204859 : Blo 802343 1204859 := bstep (se 1 (by rfl) ⟨903644, by rfl⟩ : syracuseStep 1204859 = 1807289) B1807289
theorem B2712203 : Blo 802343 2712203 := bstep (se 1 (by rfl) ⟨2034152, by rfl⟩ : syracuseStep 2712203 = 4068305) B4068305
theorem B2581139 : Blo 802343 2581139 := bstep (se 1 (by rfl) ⟨1935854, by rfl⟩ : syracuseStep 2581139 = 3871709) B3871709
theorem B1204985 : Blo 802343 1204985 := bstep (se 2 (by rfl) ⟨451869, by rfl⟩ : syracuseStep 1204985 = 903739) B903739
theorem B1205087 : Blo 802343 1205087 := bstep (se 1 (by rfl) ⟨903815, by rfl⟩ : syracuseStep 1205087 = 1807631) B1807631
theorem B1205099 : Blo 802343 1205099 := bstep (se 1 (by rfl) ⟨903824, by rfl⟩ : syracuseStep 1205099 = 1807649) B1807649
theorem B1205327 : Blo 802343 1205327 := bstep (se 1 (by rfl) ⟨903995, by rfl⟩ : syracuseStep 1205327 = 1807991) B1807991
theorem B104162435 : Blo 802343 104162435 := bstep (se 1 (by rfl) ⟨78121826, by rfl⟩ : syracuseStep 104162435 = 156243653) B156243653
theorem B1205447 : Blo 802343 1205447 := bstep (se 1 (by rfl) ⟨904085, by rfl⟩ : syracuseStep 1205447 = 1808171) B1808171
theorem B1631431 : Blo 802343 1631431 := bstep (se 1 (by rfl) ⟨1223573, by rfl⟩ : syracuseStep 1631431 = 2447147) B2447147
theorem B1205609 : Blo 802343 1205609 := bstep (se 2 (by rfl) ⟨452103, by rfl⟩ : syracuseStep 1205609 = 904207) B904207
theorem B1205687 : Blo 802343 1205687 := bstep (se 1 (by rfl) ⟨904265, by rfl⟩ : syracuseStep 1205687 = 1808531) B1808531
theorem B1205723 : Blo 802343 1205723 := bstep (se 1 (by rfl) ⟨904292, by rfl⟩ : syracuseStep 1205723 = 1808585) B1808585
theorem B1238537 : Blo 802343 1238537 := bstep (se 2 (by rfl) ⟨464451, by rfl⟩ : syracuseStep 1238537 = 928903) B928903
theorem B2713121 : Blo 802343 2713121 := bstep (se 2 (by rfl) ⟨1017420, by rfl⟩ : syracuseStep 2713121 = 2034841) B2034841
theorem B2745953 : Blo 802343 2745953 := bstep (se 2 (by rfl) ⟨1029732, by rfl⟩ : syracuseStep 2745953 = 2059465) B2059465
theorem B2582113 : Blo 802343 2582113 := bstep (se 2 (by rfl) ⟨968292, by rfl⟩ : syracuseStep 2582113 = 1936585) B1936585
theorem B2713337 : Blo 802343 2713337 := bstep (se 2 (by rfl) ⟨1017501, by rfl⟩ : syracuseStep 2713337 = 2035003) B2035003
theorem B1206191 : Blo 802343 1206191 := bstep (se 1 (by rfl) ⟨904643, by rfl⟩ : syracuseStep 1206191 = 1809287) B1809287
theorem B2713607 : Blo 802343 2713607 := bstep (se 1 (by rfl) ⟨2035205, by rfl⟩ : syracuseStep 2713607 = 4070411) B4070411
theorem B1206281 : Blo 802343 1206281 := bstep (se 2 (by rfl) ⟨452355, by rfl⟩ : syracuseStep 1206281 = 904711) B904711
theorem B1206311 : Blo 802343 1206311 := bstep (se 1 (by rfl) ⟨904733, by rfl⟩ : syracuseStep 1206311 = 1809467) B1809467
theorem B3860561 : Blo 802343 3860561 := bstep (se 2 (by rfl) ⟨1447710, by rfl⟩ : syracuseStep 3860561 = 2895421) B2895421
theorem B2713715 : Blo 802343 2713715 := bstep (se 1 (by rfl) ⟨2035286, by rfl⟩ : syracuseStep 2713715 = 4070573) B4070573
theorem B1206395 : Blo 802343 1206395 := bstep (se 1 (by rfl) ⟨904796, by rfl⟩ : syracuseStep 1206395 = 1809593) B1809593
theorem B1206521 : Blo 802343 1206521 := bstep (se 2 (by rfl) ⟨452445, by rfl⟩ : syracuseStep 1206521 = 904891) B904891
theorem B12904753 : Blo 802343 12904753 := bstep (se 2 (by rfl) ⟨4839282, by rfl⟩ : syracuseStep 12904753 = 9678565) B9678565
theorem B1206623 : Blo 802343 1206623 := bstep (se 1 (by rfl) ⟨904967, by rfl⟩ : syracuseStep 1206623 = 1809935) B1809935
theorem B1206635 : Blo 802343 1206635 := bstep (se 1 (by rfl) ⟨904976, by rfl⟩ : syracuseStep 1206635 = 1809953) B1809953
theorem B2713985 : Blo 802343 2713985 := bstep (se 2 (by rfl) ⟨1017744, by rfl⟩ : syracuseStep 2713985 = 2035489) B2035489
theorem B4581947 : Blo 802343 4581947 := bstep (se 1 (by rfl) ⟨3436460, by rfl⟩ : syracuseStep 4581947 = 6872921) B6872921
theorem B1206863 : Blo 802343 1206863 := bstep (se 1 (by rfl) ⟨905147, by rfl⟩ : syracuseStep 1206863 = 1810295) B1810295
theorem B1206983 : Blo 802343 1206983 := bstep (se 1 (by rfl) ⟨905237, by rfl⟩ : syracuseStep 1206983 = 1810475) B1810475
theorem B1207145 : Blo 802343 1207145 := bstep (se 2 (by rfl) ⟨452679, by rfl⟩ : syracuseStep 1207145 = 905359) B905359
theorem B1207223 : Blo 802343 1207223 := bstep (se 1 (by rfl) ⟨905417, by rfl⟩ : syracuseStep 1207223 = 1810835) B1810835
theorem B1207259 : Blo 802343 1207259 := bstep (se 1 (by rfl) ⟨905444, by rfl⟩ : syracuseStep 1207259 = 1810889) B1810889
theorem B4123649 : Blo 802343 4123649 := bstep (se 2 (by rfl) ⟨1546368, by rfl⟩ : syracuseStep 4123649 = 3092737) B3092737
theorem B2714795 : Blo 802343 2714795 := bstep (se 1 (by rfl) ⟨2036096, by rfl⟩ : syracuseStep 2714795 = 4072193) B4072193
theorem B1207727 : Blo 802343 1207727 := bstep (se 1 (by rfl) ⟨905795, by rfl⟩ : syracuseStep 1207727 = 1811591) B1811591
theorem B1207817 : Blo 802343 1207817 := bstep (se 2 (by rfl) ⟨452931, by rfl⟩ : syracuseStep 1207817 = 905863) B905863
theorem B1207847 : Blo 802343 1207847 := bstep (se 1 (by rfl) ⟨905885, by rfl⟩ : syracuseStep 1207847 = 1811771) B1811771
theorem B1207931 : Blo 802343 1207931 := bstep (se 1 (by rfl) ⟨905948, by rfl⟩ : syracuseStep 1207931 = 1811897) B1811897
theorem B4189819 : Blo 802343 4189819 := bstep (se 1 (by rfl) ⟨3142364, by rfl⟩ : syracuseStep 4189819 = 6284729) B6284729
theorem B19787453 : Blo 802343 19787453 := bstep (se 3 (by rfl) ⟨3710147, by rfl⟩ : syracuseStep 19787453 = 7420295) B7420295
theorem B2715335 : Blo 802343 2715335 := bstep (se 1 (by rfl) ⟨2036501, by rfl⟩ : syracuseStep 2715335 = 4073003) B4073003
theorem B1208057 : Blo 802343 1208057 := bstep (se 2 (by rfl) ⟨453021, by rfl⟩ : syracuseStep 1208057 = 906043) B906043
theorem B1208159 : Blo 802343 1208159 := bstep (se 1 (by rfl) ⟨906119, by rfl⟩ : syracuseStep 1208159 = 1812239) B1812239
theorem B1208171 : Blo 802343 1208171 := bstep (se 1 (by rfl) ⟨906128, by rfl⟩ : syracuseStep 1208171 = 1812257) B1812257
theorem B9170819 : Blo 802343 9170819 := bstep (se 1 (by rfl) ⟨6878114, by rfl⟩ : syracuseStep 9170819 = 13756229) B13756229
theorem B2289721 : Blo 802343 2289721 := bstep (se 2 (by rfl) ⟨858645, by rfl⟩ : syracuseStep 2289721 = 1717291) B1717291
theorem B1208399 : Blo 802343 1208399 := bstep (se 1 (by rfl) ⟨906299, by rfl⟩ : syracuseStep 1208399 = 1812599) B1812599
theorem B815303 : Blo 802343 815303 := bstep (se 1 (by rfl) ⟨611477, by rfl⟩ : syracuseStep 815303 = 1222955) B1222955
theorem B1208519 : Blo 802343 1208519 := bstep (se 1 (by rfl) ⟨906389, by rfl⟩ : syracuseStep 1208519 = 1812779) B1812779
theorem B1208681 : Blo 802343 1208681 := bstep (se 2 (by rfl) ⟨453255, by rfl⟩ : syracuseStep 1208681 = 906511) B906511
theorem B1208759 : Blo 802343 1208759 := bstep (se 1 (by rfl) ⟨906569, by rfl⟩ : syracuseStep 1208759 = 1813139) B1813139
theorem B1208795 : Blo 802343 1208795 := bstep (se 1 (by rfl) ⟨906596, by rfl⟩ : syracuseStep 1208795 = 1813193) B1813193
theorem B2716199 : Blo 802343 2716199 := bstep (se 1 (by rfl) ⟨2037149, by rfl⟩ : syracuseStep 2716199 = 4074299) B4074299
theorem B3666491 : Blo 802343 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B17429093 : Blo 802343 17429093 := bstep (se 4 (by rfl) ⟨1633977, by rfl⟩ : syracuseStep 17429093 = 3267955) B3267955
theorem B2716307 : Blo 802343 2716307 := bstep (se 1 (by rfl) ⟨2037230, by rfl⟩ : syracuseStep 2716307 = 4074461) B4074461
theorem B6517421 : Blo 802343 6517421 := bstep (se 3 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 6517421 = 2444033) B2444033
theorem B815951 : Blo 802343 815951 := bstep (se 1 (by rfl) ⟨611963, by rfl⟩ : syracuseStep 815951 = 1223927) B1223927
theorem B1143659 : Blo 802343 1143659 := bstep (se 1 (by rfl) ⟨857744, by rfl⟩ : syracuseStep 1143659 = 1715489) B1715489
theorem B2716523 : Blo 802343 2716523 := bstep (se 1 (by rfl) ⟨2037392, by rfl⟩ : syracuseStep 2716523 = 4074785) B4074785
theorem B2716577 : Blo 802343 2716577 := bstep (se 2 (by rfl) ⟨1018716, by rfl⟩ : syracuseStep 2716577 = 2037433) B2037433
theorem B1209263 : Blo 802343 1209263 := bstep (se 1 (by rfl) ⟨906947, by rfl⟩ : syracuseStep 1209263 = 1813895) B1813895
theorem B1209353 : Blo 802343 1209353 := bstep (se 2 (by rfl) ⟨453507, by rfl⟩ : syracuseStep 1209353 = 907015) B907015
theorem B1209383 : Blo 802343 1209383 := bstep (se 1 (by rfl) ⟨907037, by rfl⟩ : syracuseStep 1209383 = 1814075) B1814075
theorem B1209467 : Blo 802343 1209467 := bstep (se 1 (by rfl) ⟨907100, by rfl⟩ : syracuseStep 1209467 = 1814201) B1814201
theorem B1471817 : Blo 802343 1471817 := bstep (se 2 (by rfl) ⟨551931, by rfl⟩ : syracuseStep 1471817 = 1103863) B1103863
theorem B2717171 : Blo 802343 2717171 := bstep (se 1 (by rfl) ⟨2037878, by rfl⟩ : syracuseStep 2717171 = 4075757) B4075757
theorem B2717711 : Blo 802343 2717711 := bstep (se 1 (by rfl) ⟨2038283, by rfl⟩ : syracuseStep 2717711 = 4076567) B4076567
theorem B2062721 : Blo 802343 2062721 := bstep (se 2 (by rfl) ⟨773520, by rfl⟩ : syracuseStep 2062721 = 1547041) B1547041
theorem B3865097 : Blo 802343 3865097 := bstep (se 2 (by rfl) ⟨1449411, by rfl⟩ : syracuseStep 3865097 = 2898823) B2898823
theorem B41777707 : Blo 802343 41777707 := bstep (se 1 (by rfl) ⟨31333280, by rfl⟩ : syracuseStep 41777707 = 62666561) B62666561
theorem B2718305 : Blo 802343 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B1145707 : Blo 802343 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B1145783 : Blo 802343 1145783 := bstep (se 1 (by rfl) ⟨859337, by rfl⟩ : syracuseStep 1145783 = 1718675) B1718675
theorem B2030953 : Blo 802343 2030953 := bstep (se 2 (by rfl) ⟨761607, by rfl⟩ : syracuseStep 2030953 = 1523215) B1523215
theorem B3440015 : Blo 802343 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B1965593 : Blo 802343 1965593 := bstep (se 2 (by rfl) ⟨737097, by rfl⟩ : syracuseStep 1965593 = 1474195) B1474195
theorem B2031227 : Blo 802343 2031227 := bstep (se 1 (by rfl) ⟨1523420, by rfl⟩ : syracuseStep 2031227 = 3046841) B3046841
theorem B3866251 : Blo 802343 3866251 := bstep (se 1 (by rfl) ⟨2899688, by rfl⟩ : syracuseStep 3866251 = 5799377) B5799377
theorem B4947655 : Blo 802343 4947655 := bstep (se 1 (by rfl) ⟨3710741, by rfl⟩ : syracuseStep 4947655 = 7421483) B7421483
theorem B1015735 : Blo 802343 1015735 := bstep (se 1 (by rfl) ⟨761801, by rfl⟩ : syracuseStep 1015735 = 1523603) B1523603
theorem B6520763 : Blo 802343 6520763 := bstep (se 1 (by rfl) ⟨4890572, by rfl⟩ : syracuseStep 6520763 = 9781145) B9781145
theorem B4063283 : Blo 802343 4063283 := bstep (se 1 (by rfl) ⟨3047462, by rfl⟩ : syracuseStep 4063283 = 6094925) B6094925
theorem B22020173 : Blo 802343 22020173 := bstep (se 3 (by rfl) ⟨4128782, by rfl⟩ : syracuseStep 22020173 = 8257565) B8257565
theorem B9175193 : Blo 802343 9175193 := bstep (se 2 (by rfl) ⟨3440697, by rfl⟩ : syracuseStep 9175193 = 6881395) B6881395
theorem B1016155 : Blo 802343 1016155 := bstep (se 1 (by rfl) ⟨762116, by rfl⟩ : syracuseStep 1016155 = 1524233) B1524233
theorem B2064865 : Blo 802343 2064865 := bstep (se 2 (by rfl) ⟨774324, by rfl⟩ : syracuseStep 2064865 = 1548649) B1548649
theorem B4358657 : Blo 802343 4358657 := bstep (se 2 (by rfl) ⟨1634496, by rfl⟩ : syracuseStep 4358657 = 3268993) B3268993
theorem B1016383 : Blo 802343 1016383 := bstep (se 1 (by rfl) ⟨762287, by rfl⟩ : syracuseStep 1016383 = 1524575) B1524575
theorem B2032199 : Blo 802343 2032199 := bstep (se 1 (by rfl) ⟨1524149, by rfl⟩ : syracuseStep 2032199 = 3048299) B3048299
theorem B2032249 : Blo 802343 2032249 := bstep (se 2 (by rfl) ⟨762093, by rfl⟩ : syracuseStep 2032249 = 1524187) B1524187
theorem B4588235 : Blo 802343 4588235 := bstep (se 1 (by rfl) ⟨3441176, by rfl⟩ : syracuseStep 4588235 = 6882353) B6882353
theorem B9143117 : Blo 802343 9143117 := bstep (se 3 (by rfl) ⟨1714334, by rfl⟩ : syracuseStep 9143117 = 3428669) B3428669
theorem B1147879 : Blo 802343 1147879 := bstep (se 1 (by rfl) ⟨860909, by rfl⟩ : syracuseStep 1147879 = 1721819) B1721819
theorem B2294983 : Blo 802343 2294983 := bstep (se 1 (by rfl) ⟨1721237, by rfl⟩ : syracuseStep 2294983 = 3442475) B3442475
theorem B1017127 : Blo 802343 1017127 := bstep (se 1 (by rfl) ⟨762845, by rfl⟩ : syracuseStep 1017127 = 1525691) B1525691
theorem B3048799 : Blo 802343 3048799 := bstep (se 1 (by rfl) ⟨2286599, by rfl⟩ : syracuseStep 3048799 = 4573199) B4573199
theorem B15467921 : Blo 802343 15467921 := bstep (se 2 (by rfl) ⟨5800470, by rfl⟩ : syracuseStep 15467921 = 11600941) B11600941
theorem B1934855 : Blo 802343 1934855 := bstep (se 1 (by rfl) ⟨1451141, by rfl⟩ : syracuseStep 1934855 = 2902283) B2902283
theorem B3868249 : Blo 802343 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B1017451 : Blo 802343 1017451 := bstep (se 1 (by rfl) ⟨763088, by rfl⟩ : syracuseStep 1017451 = 1526177) B1526177
theorem B4064903 : Blo 802343 4064903 := bstep (se 1 (by rfl) ⟨3048677, by rfl⟩ : syracuseStep 4064903 = 6097355) B6097355
theorem B3049271 : Blo 802343 3049271 := bstep (se 1 (by rfl) ⟨2286953, by rfl⟩ : syracuseStep 3049271 = 4573907) B4573907
theorem B1017679 : Blo 802343 1017679 := bstep (se 1 (by rfl) ⟨763259, by rfl⟩ : syracuseStep 1017679 = 1526519) B1526519
theorem B8718263 : Blo 802343 8718263 := bstep (se 1 (by rfl) ⟨6538697, by rfl⟩ : syracuseStep 8718263 = 13077395) B13077395
theorem B13043663 : Blo 802343 13043663 := bstep (se 1 (by rfl) ⟨9782747, by rfl⟩ : syracuseStep 13043663 = 19565495) B19565495
theorem B11569229 : Blo 802343 11569229 := bstep (se 3 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 11569229 = 4338461) B4338461
theorem B10324097 : Blo 802343 10324097 := bstep (se 2 (by rfl) ⟨3871536, by rfl⟩ : syracuseStep 10324097 = 7743073) B7743073
theorem B3442817 : Blo 802343 3442817 := bstep (se 2 (by rfl) ⟨1291056, by rfl⟩ : syracuseStep 3442817 = 2582113) B2582113
theorem B3049757 : Blo 802343 3049757 := bstep (se 3 (by rfl) ⟨571829, by rfl⟩ : syracuseStep 3049757 = 1143659) B1143659
theorem B2034011 : Blo 802343 2034011 := bstep (se 1 (by rfl) ⟨1525508, by rfl⟩ : syracuseStep 2034011 = 3051017) B3051017
theorem B2034031 : Blo 802343 2034031 := bstep (se 1 (by rfl) ⟨1525523, by rfl⟩ : syracuseStep 2034031 = 3051047) B3051047
theorem B13044179 : Blo 802343 13044179 := bstep (se 1 (by rfl) ⟨9783134, by rfl⟩ : syracuseStep 13044179 = 19566269) B19566269
theorem B7342579 : Blo 802343 7342579 := bstep (se 1 (by rfl) ⟨5506934, by rfl⟩ : syracuseStep 7342579 = 11013869) B11013869
theorem B3476143 : Blo 802343 3476143 := bstep (se 1 (by rfl) ⟨2607107, by rfl⟩ : syracuseStep 3476143 = 5214215) B5214215
theorem B6884129 : Blo 802343 6884129 := bstep (se 2 (by rfl) ⟨2581548, by rfl⟩ : syracuseStep 6884129 = 5163097) B5163097
theorem B2034679 : Blo 802343 2034679 := bstep (se 1 (by rfl) ⟨1526009, by rfl⟩ : syracuseStep 2034679 = 3052019) B3052019
theorem B17206337 : Blo 802343 17206337 := bstep (se 2 (by rfl) ⟨6452376, by rfl⟩ : syracuseStep 17206337 = 12904753) B12904753
theorem B1805435 : Blo 802343 1805435 := bstep (se 1 (by rfl) ⟨1354076, by rfl⟩ : syracuseStep 1805435 = 2708153) B2708153
theorem B1838279 : Blo 802343 1838279 := bstep (se 1 (by rfl) ⟨1378709, by rfl⟩ : syracuseStep 1838279 = 2757419) B2757419
theorem B4066523 : Blo 802343 4066523 := bstep (se 1 (by rfl) ⟨3049892, by rfl⟩ : syracuseStep 4066523 = 6099785) B6099785
theorem B1805561 : Blo 802343 1805561 := bstep (se 2 (by rfl) ⟨677085, by rfl⟩ : syracuseStep 1805561 = 1354171) B1354171
theorem B2034983 : Blo 802343 2034983 := bstep (se 1 (by rfl) ⟨1526237, by rfl⟩ : syracuseStep 2034983 = 3052475) B3052475
theorem B1805705 : Blo 802343 1805705 := bstep (se 2 (by rfl) ⟨677139, by rfl⟩ : syracuseStep 1805705 = 1354279) B1354279
theorem B1936777 : Blo 802343 1936777 := bstep (se 2 (by rfl) ⟨726291, by rfl⟩ : syracuseStep 1936777 = 1452583) B1452583
theorem B1805831 : Blo 802343 1805831 := bstep (se 1 (by rfl) ⟨1354373, by rfl⟩ : syracuseStep 1805831 = 2708747) B2708747
theorem B1019567 : Blo 802343 1019567 := bstep (se 1 (by rfl) ⟨764675, by rfl⟩ : syracuseStep 1019567 = 1529351) B1529351
theorem B1806011 : Blo 802343 1806011 := bstep (se 1 (by rfl) ⟨1354508, by rfl⟩ : syracuseStep 1806011 = 2709017) B2709017
theorem B1806137 : Blo 802343 1806137 := bstep (se 2 (by rfl) ⟨677301, by rfl⟩ : syracuseStep 1806137 = 1354603) B1354603
theorem B5803933 : Blo 802343 5803933 := bstep (se 3 (by rfl) ⟨1088237, by rfl⟩ : syracuseStep 5803933 = 2176475) B2176475
theorem B4067657 : Blo 802343 4067657 := bstep (se 2 (by rfl) ⟨1525371, by rfl⟩ : syracuseStep 4067657 = 3050743) B3050743
theorem B1020271 : Blo 802343 1020271 := bstep (se 1 (by rfl) ⟨765203, by rfl⟩ : syracuseStep 1020271 = 1530407) B1530407
theorem B1806767 : Blo 802343 1806767 := bstep (se 1 (by rfl) ⟨1355075, by rfl⟩ : syracuseStep 1806767 = 2710151) B2710151
theorem B1806803 : Blo 802343 1806803 := bstep (se 1 (by rfl) ⟨1355102, by rfl⟩ : syracuseStep 1806803 = 2710205) B2710205
theorem B1806911 : Blo 802343 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B3871385 : Blo 802343 3871385 := bstep (se 2 (by rfl) ⟨1451769, by rfl⟩ : syracuseStep 3871385 = 2903539) B2903539
theorem B1807019 : Blo 802343 1807019 := bstep (se 1 (by rfl) ⟨1355264, by rfl⟩ : syracuseStep 1807019 = 2710529) B2710529
theorem B15110855 : Blo 802343 15110855 := bstep (se 1 (by rfl) ⟨11333141, by rfl⟩ : syracuseStep 15110855 = 22666283) B22666283
theorem B2036623 : Blo 802343 2036623 := bstep (se 1 (by rfl) ⟨1527467, by rfl⟩ : syracuseStep 2036623 = 3054935) B3054935
theorem B3052687 : Blo 802343 3052687 := bstep (se 1 (by rfl) ⟨2289515, by rfl⟩ : syracuseStep 3052687 = 4579031) B4579031
theorem B3871901 : Blo 802343 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B1807559 : Blo 802343 1807559 := bstep (se 1 (by rfl) ⟨1355669, by rfl⟩ : syracuseStep 1807559 = 2711339) B2711339
theorem B2037089 : Blo 802343 2037089 := bstep (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) B1527817
theorem B1807739 : Blo 802343 1807739 := bstep (se 1 (by rfl) ⟨1355804, by rfl⟩ : syracuseStep 1807739 = 2711609) B2711609
theorem B3052961 : Blo 802343 3052961 := bstep (se 2 (by rfl) ⟨1144860, by rfl⟩ : syracuseStep 3052961 = 2289721) B2289721
theorem B1807865 : Blo 802343 1807865 := bstep (se 2 (by rfl) ⟨677949, by rfl⟩ : syracuseStep 1807865 = 1355899) B1355899
theorem B1807955 : Blo 802343 1807955 := bstep (se 1 (by rfl) ⟨1355966, by rfl⟩ : syracuseStep 1807955 = 2711933) B2711933
theorem B4068953 : Blo 802343 4068953 := bstep (se 2 (by rfl) ⟨1525857, by rfl⟩ : syracuseStep 4068953 = 3051715) B3051715
theorem B1808135 : Blo 802343 1808135 := bstep (se 1 (by rfl) ⟨1356101, by rfl⟩ : syracuseStep 1808135 = 2712203) B2712203
theorem B2037545 : Blo 802343 2037545 := bstep (se 2 (by rfl) ⟨764079, by rfl⟩ : syracuseStep 2037545 = 1528159) B1528159
theorem B69441623 : Blo 802343 69441623 := bstep (se 1 (by rfl) ⟨52081217, by rfl⟩ : syracuseStep 69441623 = 104162435) B104162435
theorem B1448201 : Blo 802343 1448201 := bstep (se 2 (by rfl) ⟨543075, by rfl⟩ : syracuseStep 1448201 = 1086151) B1086151
theorem B7739725 : Blo 802343 7739725 := bstep (se 3 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 7739725 = 2902397) B2902397
theorem B1808747 : Blo 802343 1808747 := bstep (se 1 (by rfl) ⟨1356560, by rfl⟩ : syracuseStep 1808747 = 2713121) B2713121
theorem B1808891 : Blo 802343 1808891 := bstep (se 1 (by rfl) ⟨1356668, by rfl⟩ : syracuseStep 1808891 = 2713337) B2713337
theorem B11606591 : Blo 802343 11606591 := bstep (se 1 (by rfl) ⟨8704943, by rfl⟩ : syracuseStep 11606591 = 17409887) B17409887
theorem B1809017 : Blo 802343 1809017 := bstep (se 2 (by rfl) ⟨678381, by rfl⟩ : syracuseStep 1809017 = 1356763) B1356763
theorem B1809071 : Blo 802343 1809071 := bstep (se 1 (by rfl) ⟨1356803, by rfl⟩ : syracuseStep 1809071 = 2713607) B2713607
theorem B1809143 : Blo 802343 1809143 := bstep (se 1 (by rfl) ⟨1356857, by rfl⟩ : syracuseStep 1809143 = 2713715) B2713715
theorem B2038547 : Blo 802343 2038547 := bstep (se 1 (by rfl) ⟨1528910, by rfl⟩ : syracuseStep 2038547 = 3057821) B3057821
theorem B1809323 : Blo 802343 1809323 := bstep (se 1 (by rfl) ⟨1356992, by rfl⟩ : syracuseStep 1809323 = 2713985) B2713985
theorem B3054631 : Blo 802343 3054631 := bstep (se 1 (by rfl) ⟨2290973, by rfl⟩ : syracuseStep 3054631 = 4581947) B4581947
theorem B2039003 : Blo 802343 2039003 := bstep (se 1 (by rfl) ⟨1529252, by rfl⟩ : syracuseStep 2039003 = 3058505) B3058505
theorem B2039033 : Blo 802343 2039033 := bstep (se 2 (by rfl) ⟨764637, by rfl⟩ : syracuseStep 2039033 = 1529275) B1529275
theorem B1809863 : Blo 802343 1809863 := bstep (se 1 (by rfl) ⟨1357397, by rfl⟩ : syracuseStep 1809863 = 2714795) B2714795
theorem B13049369 : Blo 802343 13049369 := bstep (se 2 (by rfl) ⟨4893513, by rfl⟩ : syracuseStep 13049369 = 9787027) B9787027
theorem B1810223 : Blo 802343 1810223 := bstep (se 1 (by rfl) ⟨1357667, by rfl⟩ : syracuseStep 1810223 = 2715335) B2715335
theorem B3055421 : Blo 802343 3055421 := bstep (se 3 (by rfl) ⟨572891, by rfl⟩ : syracuseStep 3055421 = 1145783) B1145783
theorem B2039681 : Blo 802343 2039681 := bstep (se 2 (by rfl) ⟨764880, by rfl⟩ : syracuseStep 2039681 = 1529761) B1529761
theorem B2040137 : Blo 802343 2040137 := bstep (se 2 (by rfl) ⟨765051, by rfl⟩ : syracuseStep 2040137 = 1530103) B1530103
theorem B1810799 : Blo 802343 1810799 := bstep (se 1 (by rfl) ⟨1358099, by rfl⟩ : syracuseStep 1810799 = 2716199) B2716199
theorem B1810871 : Blo 802343 1810871 := bstep (se 1 (by rfl) ⟨1358153, by rfl⟩ : syracuseStep 1810871 = 2716307) B2716307
theorem B1811015 : Blo 802343 1811015 := bstep (se 1 (by rfl) ⟨1358261, by rfl⟩ : syracuseStep 1811015 = 2716523) B2716523
theorem B1811051 : Blo 802343 1811051 := bstep (se 1 (by rfl) ⟨1358288, by rfl⟩ : syracuseStep 1811051 = 2716577) B2716577
theorem B2040491 : Blo 802343 2040491 := bstep (se 1 (by rfl) ⟨1530368, by rfl⟩ : syracuseStep 2040491 = 3060737) B3060737
theorem B1811447 : Blo 802343 1811447 := bstep (se 1 (by rfl) ⟨1358585, by rfl⟩ : syracuseStep 1811447 = 2717171) B2717171
theorem B10036529 : Blo 802343 10036529 := bstep (se 2 (by rfl) ⟨3763698, by rfl⟩ : syracuseStep 10036529 = 7527397) B7527397
theorem B1811807 : Blo 802343 1811807 := bstep (se 1 (by rfl) ⟨1358855, by rfl⟩ : syracuseStep 1811807 = 2717711) B2717711
theorem B6956441 : Blo 802343 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B3712445 : Blo 802343 3712445 := bstep (se 3 (by rfl) ⟨696083, by rfl⟩ : syracuseStep 3712445 = 1392167) B1392167
theorem B1451603 : Blo 802343 1451603 := bstep (se 1 (by rfl) ⟨1088702, by rfl⟩ : syracuseStep 1451603 = 2177405) B2177405
theorem B1812203 : Blo 802343 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B1812329 : Blo 802343 1812329 := bstep (se 2 (by rfl) ⟨679623, by rfl⟩ : syracuseStep 1812329 = 1359247) B1359247
theorem B20654027 : Blo 802343 20654027 := bstep (se 1 (by rfl) ⟨15490520, by rfl⟩ : syracuseStep 20654027 = 30981041) B30981041
theorem B5155001 : Blo 802343 5155001 := bstep (se 2 (by rfl) ⟨1933125, by rfl⟩ : syracuseStep 5155001 = 3866251) B3866251
theorem B6596873 : Blo 802343 6596873 := bstep (se 2 (by rfl) ⟨2473827, by rfl⟩ : syracuseStep 6596873 = 4947655) B4947655
theorem B1354151 : Blo 802343 1354151 := bstep (se 1 (by rfl) ⟨1015613, by rfl⟩ : syracuseStep 1354151 = 2031227) B2031227
theorem B2173511 : Blo 802343 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B1354313 : Blo 802343 1354313 := bstep (se 2 (by rfl) ⟨507867, by rfl⟩ : syracuseStep 1354313 = 1015735) B1015735
theorem B1813175 : Blo 802343 1813175 := bstep (se 1 (by rfl) ⟨1359881, by rfl⟩ : syracuseStep 1813175 = 2719763) B2719763
theorem B4402039 : Blo 802343 4402039 := bstep (se 1 (by rfl) ⟨3301529, by rfl⟩ : syracuseStep 4402039 = 6603059) B6603059
theorem B1715087 : Blo 802343 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B1813391 : Blo 802343 1813391 := bstep (se 1 (by rfl) ⟨1360043, by rfl⟩ : syracuseStep 1813391 = 2720087) B2720087
theorem B66169871 : Blo 802343 66169871 := bstep (se 1 (by rfl) ⟨49627403, by rfl⟩ : syracuseStep 66169871 = 99254807) B99254807
theorem B2174141 : Blo 802343 2174141 := bstep (se 3 (by rfl) ⟨407651, by rfl⟩ : syracuseStep 2174141 = 815303) B815303
theorem B1289609 : Blo 802343 1289609 := bstep (se 2 (by rfl) ⟨483603, by rfl⟩ : syracuseStep 1289609 = 967207) B967207
theorem B1355359 : Blo 802343 1355359 := bstep (se 1 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 1355359 = 2033039) B2033039
theorem B1814111 : Blo 802343 1814111 := bstep (se 1 (by rfl) ⟨1360583, by rfl⟩ : syracuseStep 1814111 = 2721167) B2721167
theorem B3059309 : Blo 802343 3059309 := bstep (se 3 (by rfl) ⟨573620, by rfl⟩ : syracuseStep 3059309 = 1147241) B1147241
theorem B1715899 : Blo 802343 1715899 := bstep (se 1 (by rfl) ⟨1286924, by rfl⟩ : syracuseStep 1715899 = 2573849) B2573849
theorem B4075271 : Blo 802343 4075271 := bstep (se 1 (by rfl) ⟨3056453, by rfl⟩ : syracuseStep 4075271 = 6112907) B6112907
theorem B1355575 : Blo 802343 1355575 := bstep (se 1 (by rfl) ⟨1016681, by rfl⟩ : syracuseStep 1355575 = 2033363) B2033363
theorem B15708113 : Blo 802343 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B11907161 : Blo 802343 11907161 := bstep (se 2 (by rfl) ⟨4465185, by rfl⟩ : syracuseStep 11907161 = 8930371) B8930371
theorem B1356041 : Blo 802343 1356041 := bstep (se 2 (by rfl) ⟨508515, by rfl⟩ : syracuseStep 1356041 = 1017031) B1017031
theorem B2896505 : Blo 802343 2896505 := bstep (se 2 (by rfl) ⟨1086189, by rfl⟩ : syracuseStep 2896505 = 2172379) B2172379
theorem B2175869 : Blo 802343 2175869 := bstep (se 3 (by rfl) ⟨407975, by rfl⟩ : syracuseStep 2175869 = 815951) B815951
theorem B3486659 : Blo 802343 3486659 := bstep (se 1 (by rfl) ⟨2614994, by rfl⟩ : syracuseStep 3486659 = 5229989) B5229989
theorem B3060935 : Blo 802343 3060935 := bstep (se 1 (by rfl) ⟨2295701, by rfl⟩ : syracuseStep 3060935 = 4591403) B4591403
theorem B1357033 : Blo 802343 1357033 := bstep (se 2 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 1357033 = 1017775) B1017775
theorem B1357087 : Blo 802343 1357087 := bstep (se 1 (by rfl) ⟨1017815, by rfl⟩ : syracuseStep 1357087 = 2035631) B2035631
theorem B964271 : Blo 802343 964271 := bstep (se 1 (by rfl) ⟨723203, by rfl⟩ : syracuseStep 964271 = 1446407) B1446407
theorem B1357499 : Blo 802343 1357499 := bstep (se 1 (by rfl) ⟨1018124, by rfl⟩ : syracuseStep 1357499 = 2036249) B2036249
theorem B3061435 : Blo 802343 3061435 := bstep (se 1 (by rfl) ⟨2296076, by rfl⟩ : syracuseStep 3061435 = 4592153) B4592153
theorem B4634657 : Blo 802343 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B2177599 : Blo 802343 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B4078187 : Blo 802343 4078187 := bstep (se 1 (by rfl) ⟨3058640, by rfl⟩ : syracuseStep 4078187 = 6117281) B6117281
theorem B1719119 : Blo 802343 1719119 := bstep (se 1 (by rfl) ⟨1289339, by rfl⟩ : syracuseStep 1719119 = 2578679) B2578679
theorem B59554739 : Blo 802343 59554739 := bstep (se 1 (by rfl) ⟨44666054, by rfl⟩ : syracuseStep 59554739 = 89332109) B89332109
theorem B4078673 : Blo 802343 4078673 := bstep (se 2 (by rfl) ⟨1529502, by rfl⟩ : syracuseStep 4078673 = 3059005) B3059005
theorem B3390587 : Blo 802343 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B5160125 : Blo 802343 5160125 := bstep (se 3 (by rfl) ⟨967523, by rfl⟩ : syracuseStep 5160125 = 1935047) B1935047
theorem B965851 : Blo 802343 965851 := bstep (se 1 (by rfl) ⟨724388, by rfl⟩ : syracuseStep 965851 = 1448777) B1448777
theorem B6110437 : Blo 802343 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B1359227 : Blo 802343 1359227 := bstep (se 1 (by rfl) ⟨1019420, by rfl⟩ : syracuseStep 1359227 = 2038841) B2038841
theorem B2571707 : Blo 802343 2571707 := bstep (se 1 (by rfl) ⟨1928780, by rfl⟩ : syracuseStep 2571707 = 3857561) B3857561
theorem B5586425 : Blo 802343 5586425 := bstep (se 2 (by rfl) ⟨2094909, by rfl⟩ : syracuseStep 5586425 = 4189819) B4189819
theorem B802367 : Blo 802343 802367 := bstep (se 1 (by rfl) ⟨601775, by rfl⟩ : syracuseStep 802367 = 1203551) B1203551
theorem B802375 : Blo 802343 802375 := bstep (se 1 (by rfl) ⟨601781, by rfl⟩ : syracuseStep 802375 = 1203563) B1203563
theorem B4570739 : Blo 802343 4570739 := bstep (se 1 (by rfl) ⟨3428054, by rfl⟩ : syracuseStep 4570739 = 6856109) B6856109
theorem B802527 : Blo 802343 802527 := bstep (se 1 (by rfl) ⟨601895, by rfl⟩ : syracuseStep 802527 = 1203791) B1203791
theorem B29376263 : Blo 802343 29376263 := bstep (se 1 (by rfl) ⟨22032197, by rfl⟩ : syracuseStep 29376263 = 44064395) B44064395
theorem B802607 : Blo 802343 802607 := bstep (se 1 (by rfl) ⟨601955, by rfl⟩ : syracuseStep 802607 = 1203911) B1203911
theorem B802715 : Blo 802343 802715 := bstep (se 1 (by rfl) ⟨602036, by rfl⟩ : syracuseStep 802715 = 1204073) B1204073
theorem B802767 : Blo 802343 802767 := bstep (se 1 (by rfl) ⟨602075, by rfl⟩ : syracuseStep 802767 = 1204151) B1204151
theorem B802791 : Blo 802343 802791 := bstep (se 1 (by rfl) ⟨602093, by rfl⟩ : syracuseStep 802791 = 1204187) B1204187
theorem B803103 : Blo 802343 803103 := bstep (se 1 (by rfl) ⟨602327, by rfl⟩ : syracuseStep 803103 = 1204655) B1204655
theorem B803163 : Blo 802343 803163 := bstep (se 1 (by rfl) ⟨602372, by rfl⟩ : syracuseStep 803163 = 1204745) B1204745
theorem B1360219 : Blo 802343 1360219 := bstep (se 1 (by rfl) ⟨1020164, by rfl⟩ : syracuseStep 1360219 = 2040329) B2040329
theorem B803183 : Blo 802343 803183 := bstep (se 1 (by rfl) ⟨602387, by rfl⟩ : syracuseStep 803183 = 1204775) B1204775
theorem B803239 : Blo 802343 803239 := bstep (se 1 (by rfl) ⟨602429, by rfl⟩ : syracuseStep 803239 = 1204859) B1204859
theorem B1720759 : Blo 802343 1720759 := bstep (se 1 (by rfl) ⟨1290569, by rfl⟩ : syracuseStep 1720759 = 2581139) B2581139
theorem B803323 : Blo 802343 803323 := bstep (se 1 (by rfl) ⟨602492, by rfl⟩ : syracuseStep 803323 = 1204985) B1204985
theorem B803391 : Blo 802343 803391 := bstep (se 1 (by rfl) ⟨602543, by rfl⟩ : syracuseStep 803391 = 1205087) B1205087
theorem B967231 : Blo 802343 967231 := bstep (se 1 (by rfl) ⟨725423, by rfl⟩ : syracuseStep 967231 = 1450847) B1450847
theorem B803399 : Blo 802343 803399 := bstep (se 1 (by rfl) ⟨602549, by rfl⟩ : syracuseStep 803399 = 1205099) B1205099
theorem B803551 : Blo 802343 803551 := bstep (se 1 (by rfl) ⟨602663, by rfl⟩ : syracuseStep 803551 = 1205327) B1205327
theorem B803631 : Blo 802343 803631 := bstep (se 1 (by rfl) ⟨602723, by rfl⟩ : syracuseStep 803631 = 1205447) B1205447
theorem B803739 : Blo 802343 803739 := bstep (se 1 (by rfl) ⟨602804, by rfl⟩ : syracuseStep 803739 = 1205609) B1205609
theorem B803791 : Blo 802343 803791 := bstep (se 1 (by rfl) ⟨602843, by rfl⟩ : syracuseStep 803791 = 1205687) B1205687
theorem B6865883 : Blo 802343 6865883 := bstep (se 1 (by rfl) ⟨5149412, by rfl⟩ : syracuseStep 6865883 = 10298825) B10298825
theorem B803815 : Blo 802343 803815 := bstep (se 1 (by rfl) ⟨602861, by rfl⟩ : syracuseStep 803815 = 1205723) B1205723
theorem B4572197 : Blo 802343 4572197 := bstep (se 4 (by rfl) ⟨428643, by rfl⟩ : syracuseStep 4572197 = 857287) B857287
theorem B8700965 : Blo 802343 8700965 := bstep (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) B1631431
theorem B7324769 : Blo 802343 7324769 := bstep (se 2 (by rfl) ⟨2746788, by rfl⟩ : syracuseStep 7324769 = 5493577) B5493577
theorem B804127 : Blo 802343 804127 := bstep (se 1 (by rfl) ⟨603095, by rfl⟩ : syracuseStep 804127 = 1206191) B1206191
theorem B7062833 : Blo 802343 7062833 := bstep (se 2 (by rfl) ⟨2648562, by rfl⟩ : syracuseStep 7062833 = 5297125) B5297125
theorem B804187 : Blo 802343 804187 := bstep (se 1 (by rfl) ⟨603140, by rfl⟩ : syracuseStep 804187 = 1206281) B1206281
theorem B804207 : Blo 802343 804207 := bstep (se 1 (by rfl) ⟨603155, by rfl⟩ : syracuseStep 804207 = 1206311) B1206311
theorem B2573707 : Blo 802343 2573707 := bstep (se 1 (by rfl) ⟨1930280, by rfl⟩ : syracuseStep 2573707 = 3860561) B3860561
theorem B804263 : Blo 802343 804263 := bstep (se 1 (by rfl) ⟨603197, by rfl⟩ : syracuseStep 804263 = 1206395) B1206395
theorem B804347 : Blo 802343 804347 := bstep (se 1 (by rfl) ⟨603260, by rfl⟩ : syracuseStep 804347 = 1206521) B1206521
theorem B35276309 : Blo 802343 35276309 := bstep (se 6 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 35276309 = 1653577) B1653577
theorem B804415 : Blo 802343 804415 := bstep (se 1 (by rfl) ⟨603311, by rfl⟩ : syracuseStep 804415 = 1206623) B1206623
theorem B804423 : Blo 802343 804423 := bstep (se 1 (by rfl) ⟨603317, by rfl⟩ : syracuseStep 804423 = 1206635) B1206635
theorem B4638365 : Blo 802343 4638365 := bstep (se 3 (by rfl) ⟨869693, by rfl⟩ : syracuseStep 4638365 = 1739387) B1739387
theorem B6866633 : Blo 802343 6866633 := bstep (se 2 (by rfl) ⟨2574987, by rfl⟩ : syracuseStep 6866633 = 5149975) B5149975
theorem B804575 : Blo 802343 804575 := bstep (se 1 (by rfl) ⟨603431, by rfl⟩ : syracuseStep 804575 = 1206863) B1206863
theorem B804655 : Blo 802343 804655 := bstep (se 1 (by rfl) ⟨603491, by rfl⟩ : syracuseStep 804655 = 1206983) B1206983
theorem B804763 : Blo 802343 804763 := bstep (se 1 (by rfl) ⟨603572, by rfl⟩ : syracuseStep 804763 = 1207145) B1207145
theorem B804815 : Blo 802343 804815 := bstep (se 1 (by rfl) ⟨603611, by rfl⟩ : syracuseStep 804815 = 1207223) B1207223
theorem B804839 : Blo 802343 804839 := bstep (se 1 (by rfl) ⟨603629, by rfl⟩ : syracuseStep 804839 = 1207259) B1207259
theorem B805151 : Blo 802343 805151 := bstep (se 1 (by rfl) ⟨603863, by rfl⟩ : syracuseStep 805151 = 1207727) B1207727
theorem B805211 : Blo 802343 805211 := bstep (se 1 (by rfl) ⟨603908, by rfl⟩ : syracuseStep 805211 = 1207817) B1207817
theorem B805231 : Blo 802343 805231 := bstep (se 1 (by rfl) ⟨603923, by rfl⟩ : syracuseStep 805231 = 1207847) B1207847
theorem B50317699 : Blo 802343 50317699 := bstep (se 1 (by rfl) ⟨37738274, by rfl⟩ : syracuseStep 50317699 = 75476549) B75476549
theorem B805287 : Blo 802343 805287 := bstep (se 1 (by rfl) ⟨603965, by rfl⟩ : syracuseStep 805287 = 1207931) B1207931
theorem B13191635 : Blo 802343 13191635 := bstep (se 1 (by rfl) ⟨9893726, by rfl⟩ : syracuseStep 13191635 = 19787453) B19787453
theorem B805371 : Blo 802343 805371 := bstep (se 1 (by rfl) ⟨604028, by rfl⟩ : syracuseStep 805371 = 1208057) B1208057
theorem B805439 : Blo 802343 805439 := bstep (se 1 (by rfl) ⟨604079, by rfl⟩ : syracuseStep 805439 = 1208159) B1208159
theorem B805447 : Blo 802343 805447 := bstep (se 1 (by rfl) ⟨604085, by rfl⟩ : syracuseStep 805447 = 1208171) B1208171
theorem B6113879 : Blo 802343 6113879 := bstep (se 1 (by rfl) ⟨4585409, by rfl⟩ : syracuseStep 6113879 = 9170819) B9170819
theorem B903775 : Blo 802343 903775 := bstep (se 1 (by rfl) ⟨677831, by rfl⟩ : syracuseStep 903775 = 1355663) B1355663
theorem B10996397 : Blo 802343 10996397 := bstep (se 3 (by rfl) ⟨2061824, by rfl⟩ : syracuseStep 10996397 = 4123649) B4123649
theorem B805599 : Blo 802343 805599 := bstep (se 1 (by rfl) ⟨604199, by rfl⟩ : syracuseStep 805599 = 1208399) B1208399
theorem B805679 : Blo 802343 805679 := bstep (se 1 (by rfl) ⟨604259, by rfl⟩ : syracuseStep 805679 = 1208519) B1208519
theorem B805787 : Blo 802343 805787 := bstep (se 1 (by rfl) ⟨604340, by rfl⟩ : syracuseStep 805787 = 1208681) B1208681
theorem B2608043 : Blo 802343 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B805839 : Blo 802343 805839 := bstep (se 1 (by rfl) ⟨604379, by rfl⟩ : syracuseStep 805839 = 1208759) B1208759
theorem B805863 : Blo 802343 805863 := bstep (se 1 (by rfl) ⟨604397, by rfl⟩ : syracuseStep 805863 = 1208795) B1208795
theorem B2444327 : Blo 802343 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B11619395 : Blo 802343 11619395 := bstep (se 1 (by rfl) ⟨8714546, by rfl⟩ : syracuseStep 11619395 = 17429093) B17429093
theorem B4344947 : Blo 802343 4344947 := bstep (se 1 (by rfl) ⟨3258710, by rfl⟩ : syracuseStep 4344947 = 6517421) B6517421
theorem B806175 : Blo 802343 806175 := bstep (se 1 (by rfl) ⟨604631, by rfl⟩ : syracuseStep 806175 = 1209263) B1209263
theorem B806235 : Blo 802343 806235 := bstep (se 1 (by rfl) ⟨604676, by rfl⟩ : syracuseStep 806235 = 1209353) B1209353
theorem B806255 : Blo 802343 806255 := bstep (se 1 (by rfl) ⟨604691, by rfl⟩ : syracuseStep 806255 = 1209383) B1209383
theorem B806311 : Blo 802343 806311 := bstep (se 1 (by rfl) ⟨604733, by rfl⟩ : syracuseStep 806311 = 1209467) B1209467
theorem B3427849 : Blo 802343 3427849 := bstep (se 2 (by rfl) ⟨1285443, by rfl⟩ : syracuseStep 3427849 = 2570887) B2570887
theorem B904927 : Blo 802343 904927 := bstep (se 1 (by rfl) ⟨678695, by rfl⟩ : syracuseStep 904927 = 1357391) B1357391
theorem B905503 : Blo 802343 905503 := bstep (se 1 (by rfl) ⟨679127, by rfl⟩ : syracuseStep 905503 = 1358255) B1358255
theorem B2576731 : Blo 802343 2576731 := bstep (se 1 (by rfl) ⟨1932548, by rfl⟩ : syracuseStep 2576731 = 3865097) B3865097
theorem B7852463 : Blo 802343 7852463 := bstep (se 1 (by rfl) ⟨5889347, by rfl⟩ : syracuseStep 7852463 = 11778695) B11778695
theorem B2707937 : Blo 802343 2707937 := bstep (se 2 (by rfl) ⟨1015476, by rfl⟩ : syracuseStep 2707937 = 2030953) B2030953
theorem B905791 : Blo 802343 905791 := bstep (se 1 (by rfl) ⟨679343, by rfl⟩ : syracuseStep 905791 = 1358687) B1358687
theorem B17388701 : Blo 802343 17388701 := bstep (se 3 (by rfl) ⟨3260381, by rfl⟩ : syracuseStep 17388701 = 6520763) B6520763
theorem B906619 : Blo 802343 906619 := bstep (se 1 (by rfl) ⟨679964, by rfl⟩ : syracuseStep 906619 = 1359929) B1359929
theorem B7722503 : Blo 802343 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B9655853 : Blo 802343 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B2709179 : Blo 802343 2709179 := bstep (se 1 (by rfl) ⟨2031884, by rfl⟩ : syracuseStep 2709179 = 4063769) B4063769
theorem B1529579 : Blo 802343 1529579 := bstep (se 1 (by rfl) ⟨1147184, by rfl⟩ : syracuseStep 1529579 = 2294369) B2294369
theorem B907087 : Blo 802343 907087 := bstep (se 1 (by rfl) ⟨680315, by rfl⟩ : syracuseStep 907087 = 1360631) B1360631
theorem B4348151 : Blo 802343 4348151 := bstep (se 1 (by rfl) ⟨3261113, by rfl⟩ : syracuseStep 4348151 = 6522227) B6522227
theorem B1530323 : Blo 802343 1530323 := bstep (se 1 (by rfl) ⟨1147742, by rfl⟩ : syracuseStep 1530323 = 2295485) B2295485
theorem B1530551 : Blo 802343 1530551 := bstep (se 1 (by rfl) ⟨1147913, by rfl⟩ : syracuseStep 1530551 = 2295827) B2295827
theorem B20601539 : Blo 802343 20601539 := bstep (se 1 (by rfl) ⟨15451154, by rfl⟩ : syracuseStep 20601539 = 30902309) B30902309
theorem B5495795 : Blo 802343 5495795 := bstep (se 1 (by rfl) ⟨4121846, by rfl⟩ : syracuseStep 5495795 = 8243693) B8243693
theorem B3660923 : Blo 802343 3660923 := bstep (se 1 (by rfl) ⟨2745692, by rfl⟩ : syracuseStep 3660923 = 5491385) B5491385
theorem B1203593 : Blo 802343 1203593 := bstep (se 2 (by rfl) ⟨451347, by rfl⟩ : syracuseStep 1203593 = 902695) B902695
theorem B2711123 : Blo 802343 2711123 := bstep (se 1 (by rfl) ⟨2033342, by rfl⟩ : syracuseStep 2711123 = 4066685) B4066685
theorem B8937175 : Blo 802343 8937175 := bstep (se 1 (by rfl) ⟨6702881, by rfl⟩ : syracuseStep 8937175 = 13405763) B13405763
theorem B1203947 : Blo 802343 1203947 := bstep (se 1 (by rfl) ⟨902960, by rfl⟩ : syracuseStep 1203947 = 1805921) B1805921
theorem B1204175 : Blo 802343 1204175 := bstep (se 1 (by rfl) ⟨903131, by rfl⟩ : syracuseStep 1204175 = 1806263) B1806263
theorem B1204571 : Blo 802343 1204571 := bstep (se 1 (by rfl) ⟨903428, by rfl⟩ : syracuseStep 1204571 = 1806857) B1806857
theorem B1204799 : Blo 802343 1204799 := bstep (se 1 (by rfl) ⟨903599, by rfl⟩ : syracuseStep 1204799 = 1807199) B1807199
theorem B1204919 : Blo 802343 1204919 := bstep (se 1 (by rfl) ⟨903689, by rfl⟩ : syracuseStep 1204919 = 1807379) B1807379
theorem B3924845 : Blo 802343 3924845 := bstep (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) B1471817
theorem B1205147 : Blo 802343 1205147 := bstep (se 1 (by rfl) ⟨903860, by rfl⟩ : syracuseStep 1205147 = 1807721) B1807721
theorem B3859447 : Blo 802343 3859447 := bstep (se 1 (by rfl) ⟨2894585, by rfl⟩ : syracuseStep 3859447 = 5789171) B5789171
theorem B10183781 : Blo 802343 10183781 := bstep (se 4 (by rfl) ⟨954729, by rfl⟩ : syracuseStep 10183781 = 1909459) B1909459
theorem B2581703 : Blo 802343 2581703 := bstep (se 1 (by rfl) ⟨1936277, by rfl⟩ : syracuseStep 2581703 = 3872555) B3872555
theorem B1205543 : Blo 802343 1205543 := bstep (se 1 (by rfl) ⟨904157, by rfl⟩ : syracuseStep 1205543 = 1808315) B1808315
theorem B3302765 : Blo 802343 3302765 := bstep (se 3 (by rfl) ⟨619268, by rfl⟩ : syracuseStep 3302765 = 1238537) B1238537
theorem B1205627 : Blo 802343 1205627 := bstep (se 1 (by rfl) ⟨904220, by rfl⟩ : syracuseStep 1205627 = 1808441) B1808441
theorem B1205753 : Blo 802343 1205753 := bstep (se 2 (by rfl) ⟨452157, by rfl⟩ : syracuseStep 1205753 = 904315) B904315
theorem B1205855 : Blo 802343 1205855 := bstep (se 1 (by rfl) ⟨904391, by rfl⟩ : syracuseStep 1205855 = 1808783) B1808783
theorem B1631839 : Blo 802343 1631839 := bstep (se 1 (by rfl) ⟨1223879, by rfl⟩ : syracuseStep 1631839 = 2447759) B2447759
theorem B1206071 : Blo 802343 1206071 := bstep (se 1 (by rfl) ⟨904553, by rfl⟩ : syracuseStep 1206071 = 1809107) B1809107
theorem B1206377 : Blo 802343 1206377 := bstep (se 2 (by rfl) ⟨452391, by rfl⟩ : syracuseStep 1206377 = 904783) B904783
theorem B4581629 : Blo 802343 4581629 := bstep (se 3 (by rfl) ⟨859055, by rfl⟩ : syracuseStep 4581629 = 1718111) B1718111
theorem B1206695 : Blo 802343 1206695 := bstep (se 1 (by rfl) ⟨905021, by rfl⟩ : syracuseStep 1206695 = 1810043) B1810043
theorem B2714039 : Blo 802343 2714039 := bstep (se 1 (by rfl) ⟨2035529, by rfl⟩ : syracuseStep 2714039 = 4071059) B4071059
theorem B1206779 : Blo 802343 1206779 := bstep (se 1 (by rfl) ⟨905084, by rfl⟩ : syracuseStep 1206779 = 1810169) B1810169
theorem B1206905 : Blo 802343 1206905 := bstep (se 2 (by rfl) ⟨452589, by rfl⟩ : syracuseStep 1206905 = 905179) B905179
theorem B1206959 : Blo 802343 1206959 := bstep (se 1 (by rfl) ⟨905219, by rfl⟩ : syracuseStep 1206959 = 1810439) B1810439
theorem B1207007 : Blo 802343 1207007 := bstep (se 1 (by rfl) ⟨905255, by rfl⟩ : syracuseStep 1207007 = 1810511) B1810511
theorem B1927955 : Blo 802343 1927955 := bstep (se 1 (by rfl) ⟨1445966, by rfl⟩ : syracuseStep 1927955 = 2891933) B2891933
theorem B1207271 : Blo 802343 1207271 := bstep (se 1 (by rfl) ⟨905453, by rfl⟩ : syracuseStep 1207271 = 1810907) B1810907
theorem B3435709 : Blo 802343 3435709 := bstep (se 3 (by rfl) ⟨644195, by rfl⟩ : syracuseStep 3435709 = 1288391) B1288391
theorem B1207529 : Blo 802343 1207529 := bstep (se 2 (by rfl) ⟨452823, by rfl⟩ : syracuseStep 1207529 = 905647) B905647
theorem B1207583 : Blo 802343 1207583 := bstep (se 1 (by rfl) ⟨905687, by rfl⟩ : syracuseStep 1207583 = 1811375) B1811375
theorem B814447 : Blo 802343 814447 := bstep (se 1 (by rfl) ⟨610835, by rfl⟩ : syracuseStep 814447 = 1221671) B1221671
theorem B1207751 : Blo 802343 1207751 := bstep (se 1 (by rfl) ⟨905813, by rfl⟩ : syracuseStep 1207751 = 1811627) B1811627
theorem B28241369 : Blo 802343 28241369 := bstep (se 2 (by rfl) ⟨10590513, by rfl⟩ : syracuseStep 28241369 = 21181027) B21181027
theorem B1830635 : Blo 802343 1830635 := bstep (se 1 (by rfl) ⟨1372976, by rfl⟩ : syracuseStep 1830635 = 2745953) B2745953
theorem B1208105 : Blo 802343 1208105 := bstep (se 2 (by rfl) ⟨453039, by rfl⟩ : syracuseStep 1208105 = 906079) B906079
theorem B1208111 : Blo 802343 1208111 := bstep (se 1 (by rfl) ⟨906083, by rfl⟩ : syracuseStep 1208111 = 1812167) B1812167
theorem B1929089 : Blo 802343 1929089 := bstep (se 2 (by rfl) ⟨723408, by rfl⟩ : syracuseStep 1929089 = 1446817) B1446817
theorem B3436445 : Blo 802343 3436445 := bstep (se 3 (by rfl) ⟨644333, by rfl⟩ : syracuseStep 3436445 = 1288667) B1288667
theorem B1208585 : Blo 802343 1208585 := bstep (se 2 (by rfl) ⟨453219, by rfl⟩ : syracuseStep 1208585 = 906439) B906439
theorem B1208687 : Blo 802343 1208687 := bstep (se 1 (by rfl) ⟨906515, by rfl⟩ : syracuseStep 1208687 = 1813031) B1813031
theorem B1208903 : Blo 802343 1208903 := bstep (se 1 (by rfl) ⟨906677, by rfl⟩ : syracuseStep 1208903 = 1813355) B1813355
theorem B1208939 : Blo 802343 1208939 := bstep (se 1 (by rfl) ⟨906704, by rfl⟩ : syracuseStep 1208939 = 1813409) B1813409
theorem B1209167 : Blo 802343 1209167 := bstep (se 1 (by rfl) ⟨906875, by rfl⟩ : syracuseStep 1209167 = 1813751) B1813751
theorem B5796953 : Blo 802343 5796953 := bstep (se 2 (by rfl) ⟨2173857, by rfl⟩ : syracuseStep 5796953 = 4347715) B4347715
theorem B67859873 : Blo 802343 67859873 := bstep (se 2 (by rfl) ⟨25447452, by rfl⟩ : syracuseStep 67859873 = 50894905) B50894905
theorem B2717117 : Blo 802343 2717117 := bstep (se 3 (by rfl) ⟨509459, by rfl⟩ : syracuseStep 2717117 = 1018919) B1018919
theorem B6879005 : Blo 802343 6879005 := bstep (se 3 (by rfl) ⟨1289813, by rfl⟩ : syracuseStep 6879005 = 2579627) B2579627
theorem B2717495 : Blo 802343 2717495 := bstep (se 1 (by rfl) ⟨2038121, by rfl⟩ : syracuseStep 2717495 = 4076243) B4076243
theorem B55703609 : Blo 802343 55703609 := bstep (se 2 (by rfl) ⟨20888853, by rfl⟩ : syracuseStep 55703609 = 41777707) B41777707
theorem B2717981 : Blo 802343 2717981 := bstep (se 3 (by rfl) ⟨509621, by rfl⟩ : syracuseStep 2717981 = 1019243) B1019243
theorem B1931771 : Blo 802343 1931771 := bstep (se 1 (by rfl) ⟨1448828, by rfl⟩ : syracuseStep 1931771 = 2897657) B2897657
theorem B33094277 : Blo 802343 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B5241581 : Blo 802343 5241581 := bstep (se 3 (by rfl) ⟨982796, by rfl⟩ : syracuseStep 5241581 = 1965593) B1965593
theorem B1145755 : Blo 802343 1145755 := bstep (se 1 (by rfl) ⟨859316, by rfl⟩ : syracuseStep 1145755 = 1718633) B1718633
theorem B1375147 : Blo 802343 1375147 := bstep (se 1 (by rfl) ⟨1031360, by rfl⟩ : syracuseStep 1375147 = 2062721) B2062721
theorem B2719007 : Blo 802343 2719007 := bstep (se 1 (by rfl) ⟨2039255, by rfl⟩ : syracuseStep 2719007 = 4078511) B4078511
theorem B3046855 : Blo 802343 3046855 := bstep (se 1 (by rfl) ⟨2285141, by rfl⟩ : syracuseStep 3046855 = 4570283) B4570283
theorem B2293343 : Blo 802343 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B14680115 : Blo 802343 14680115 := bstep (se 1 (by rfl) ⟨11010086, by rfl⟩ : syracuseStep 14680115 = 22020173) B22020173
theorem B6095411 : Blo 802343 6095411 := bstep (se 1 (by rfl) ⟨4571558, by rfl⟩ : syracuseStep 6095411 = 9143117) B9143117
theorem B2294345 : Blo 802343 2294345 := bstep (se 2 (by rfl) ⟨860379, by rfl⟩ : syracuseStep 2294345 = 1720759) B1720759
theorem B2753153 : Blo 802343 2753153 := bstep (se 2 (by rfl) ⟨1032432, by rfl⟩ : syracuseStep 2753153 = 2064865) B2064865
theorem B3048131 : Blo 802343 3048131 := bstep (se 1 (by rfl) ⟨2286098, by rfl⟩ : syracuseStep 3048131 = 4572197) B4572197
theorem B5800643 : Blo 802343 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B4883179 : Blo 802343 4883179 := bstep (se 1 (by rfl) ⟨3662384, by rfl⟩ : syracuseStep 4883179 = 7324769) B7324769
theorem B2032847 : Blo 802343 2032847 := bstep (se 1 (by rfl) ⟨1524635, by rfl⟩ : syracuseStep 2032847 = 3049271) B3049271
theorem B5145929 : Blo 802343 5145929 := bstep (se 2 (by rfl) ⟨1929723, by rfl⟩ : syracuseStep 5145929 = 3859447) B3859447
theorem B6882731 : Blo 802343 6882731 := bstep (se 1 (by rfl) ⟨5162048, by rfl⟩ : syracuseStep 6882731 = 10324097) B10324097
theorem B2295211 : Blo 802343 2295211 := bstep (se 1 (by rfl) ⟨1721408, by rfl⟩ : syracuseStep 2295211 = 3442817) B3442817
theorem B2033171 : Blo 802343 2033171 := bstep (se 1 (by rfl) ⟨1524878, by rfl⟩ : syracuseStep 2033171 = 3049757) B3049757
theorem B4065065 : Blo 802343 4065065 := bstep (se 2 (by rfl) ⟨1524399, by rfl⟩ : syracuseStep 4065065 = 3048799) B3048799
theorem B4589419 : Blo 802343 4589419 := bstep (se 1 (by rfl) ⟨3442064, by rfl⟩ : syracuseStep 4589419 = 6884129) B6884129
theorem B11470891 : Blo 802343 11470891 := bstep (se 1 (by rfl) ⟨8603168, by rfl⟩ : syracuseStep 11470891 = 17206337) B17206337
theorem B5802317 : Blo 802343 5802317 := bstep (se 3 (by rfl) ⟨1087934, by rfl⟩ : syracuseStep 5802317 = 2175869) B2175869
theorem B1805291 : Blo 802343 1805291 := bstep (se 1 (by rfl) ⟨1353968, by rfl⟩ : syracuseStep 1805291 = 2707937) B2707937
theorem B10325069 : Blo 802343 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B2035307 : Blo 802343 2035307 := bstep (se 1 (by rfl) ⟨1526480, by rfl⟩ : syracuseStep 2035307 = 3052961) B3052961
theorem B5148335 : Blo 802343 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B1806119 : Blo 802343 1806119 := bstep (se 1 (by rfl) ⟨1354589, by rfl⟩ : syracuseStep 1806119 = 2709179) B2709179
theorem B1019719 : Blo 802343 1019719 := bstep (se 1 (by rfl) ⟨764789, by rfl⟩ : syracuseStep 1019719 = 1529579) B1529579
theorem B5869385 : Blo 802343 5869385 := bstep (se 2 (by rfl) ⟨2201019, by rfl⟩ : syracuseStep 5869385 = 4402039) B4402039
theorem B1020215 : Blo 802343 1020215 := bstep (se 1 (by rfl) ⟨765161, by rfl⟩ : syracuseStep 1020215 = 1530323) B1530323
theorem B7737727 : Blo 802343 7737727 := bstep (se 1 (by rfl) ⟨5803295, by rfl⟩ : syracuseStep 7737727 = 11606591) B11606591
theorem B1020367 : Blo 802343 1020367 := bstep (se 1 (by rfl) ⟨765275, by rfl⟩ : syracuseStep 1020367 = 1530551) B1530551
theorem B13734359 : Blo 802343 13734359 := bstep (se 1 (by rfl) ⟨10300769, by rfl⟩ : syracuseStep 13734359 = 20601539) B20601539
theorem B1085929 : Blo 802343 1085929 := bstep (se 2 (by rfl) ⟨407223, by rfl⟩ : syracuseStep 1085929 = 814447) B814447
theorem B1807145 : Blo 802343 1807145 := bstep (se 2 (by rfl) ⟨677679, by rfl⟩ : syracuseStep 1807145 = 1355359) B1355359
theorem B1807415 : Blo 802343 1807415 := bstep (se 1 (by rfl) ⟨1355561, by rfl⟩ : syracuseStep 1807415 = 2711123) B2711123
theorem B1807433 : Blo 802343 1807433 := bstep (se 2 (by rfl) ⟨677787, by rfl⟩ : syracuseStep 1807433 = 1355575) B1355575
theorem B7738577 : Blo 802343 7738577 := bstep (se 2 (by rfl) ⟨2901966, by rfl⟩ : syracuseStep 7738577 = 5803933) B5803933
theorem B2036947 : Blo 802343 2036947 := bstep (se 1 (by rfl) ⟨1527710, by rfl⟩ : syracuseStep 2036947 = 3055421) B3055421
theorem B6789187 : Blo 802343 6789187 := bstep (se 1 (by rfl) ⟨5091890, by rfl⟩ : syracuseStep 6789187 = 10183781) B10183781
theorem B6691019 : Blo 802343 6691019 := bstep (se 1 (by rfl) ⟨5018264, by rfl⟩ : syracuseStep 6691019 = 10036529) B10036529
theorem B2201843 : Blo 802343 2201843 := bstep (se 1 (by rfl) ⟨1651382, by rfl⟩ : syracuseStep 2201843 = 3302765) B3302765
theorem B5151205 : Blo 802343 5151205 := bstep (se 4 (by rfl) ⟨482925, by rfl⟩ : syracuseStep 5151205 = 965851) B965851
theorem B13769351 : Blo 802343 13769351 := bstep (se 1 (by rfl) ⟨10327013, by rfl⟩ : syracuseStep 13769351 = 20654027) B20654027
theorem B3054419 : Blo 802343 3054419 := bstep (se 1 (by rfl) ⟨2290814, by rfl⟩ : syracuseStep 3054419 = 4581629) B4581629
theorem B4397915 : Blo 802343 4397915 := bstep (se 1 (by rfl) ⟨3298436, by rfl⟩ : syracuseStep 4397915 = 6596873) B6596873
theorem B4070249 : Blo 802343 4070249 := bstep (se 2 (by rfl) ⟨1526343, by rfl⟩ : syracuseStep 4070249 = 3052687) B3052687
theorem B1809359 : Blo 802343 1809359 := bstep (se 1 (by rfl) ⟨1357019, by rfl⟩ : syracuseStep 1809359 = 2714039) B2714039
theorem B1809377 : Blo 802343 1809377 := bstep (se 2 (by rfl) ⟨678516, by rfl⟩ : syracuseStep 1809377 = 1357033) B1357033
theorem B1809449 : Blo 802343 1809449 := bstep (se 2 (by rfl) ⟨678543, by rfl⟩ : syracuseStep 1809449 = 1357087) B1357087
theorem B1285303 : Blo 802343 1285303 := bstep (se 1 (by rfl) ⟨963977, by rfl⟩ : syracuseStep 1285303 = 1927955) B1927955
theorem B44113247 : Blo 802343 44113247 := bstep (se 1 (by rfl) ⟨33084935, by rfl⟩ : syracuseStep 44113247 = 66169871) B66169871
theorem B1449427 : Blo 802343 1449427 := bstep (se 1 (by rfl) ⟨1087070, by rfl⟩ : syracuseStep 1449427 = 2174141) B2174141
theorem B859739 : Blo 802343 859739 := bstep (se 1 (by rfl) ⟨644804, by rfl⟩ : syracuseStep 859739 = 1289609) B1289609
theorem B2039539 : Blo 802343 2039539 := bstep (se 1 (by rfl) ⟨1529654, by rfl⟩ : syracuseStep 2039539 = 3059309) B3059309
theorem B6954781 : Blo 802343 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B1220423 : Blo 802343 1220423 := bstep (se 1 (by rfl) ⟨915317, by rfl⟩ : syracuseStep 1220423 = 1830635) B1830635
theorem B1286059 : Blo 802343 1286059 := bstep (se 1 (by rfl) ⟨964544, by rfl⟩ : syracuseStep 1286059 = 1929089) B1929089
theorem B7938107 : Blo 802343 7938107 := bstep (se 1 (by rfl) ⟨5953580, by rfl⟩ : syracuseStep 7938107 = 11907161) B11907161
theorem B2040623 : Blo 802343 2040623 := bstep (se 1 (by rfl) ⟨1530467, by rfl⟩ : syracuseStep 2040623 = 3060935) B3060935
theorem B1811411 : Blo 802343 1811411 := bstep (se 1 (by rfl) ⟨1358558, by rfl⟩ : syracuseStep 1811411 = 2717117) B2717117
theorem B6857885 : Blo 802343 6857885 := bstep (se 3 (by rfl) ⟨1285853, by rfl⟩ : syracuseStep 6857885 = 2571707) B2571707
theorem B1811663 : Blo 802343 1811663 := bstep (se 1 (by rfl) ⟨1358747, by rfl⟩ : syracuseStep 1811663 = 2717495) B2717495
theorem B3089771 : Blo 802343 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B37135739 : Blo 802343 37135739 := bstep (se 1 (by rfl) ⟨27851804, by rfl⟩ : syracuseStep 37135739 = 55703609) B55703609
theorem B4072841 : Blo 802343 4072841 := bstep (se 2 (by rfl) ⟨1527315, by rfl⟩ : syracuseStep 4072841 = 3054631) B3054631
theorem B1811987 : Blo 802343 1811987 := bstep (se 1 (by rfl) ⟨1358990, by rfl⟩ : syracuseStep 1811987 = 2717981) B2717981
theorem B1287847 : Blo 802343 1287847 := bstep (se 1 (by rfl) ⟨965885, by rfl⟩ : syracuseStep 1287847 = 1931771) B1931771
theorem B22062851 : Blo 802343 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B1812671 : Blo 802343 1812671 := bstep (se 1 (by rfl) ⟨1359503, by rfl⟩ : syracuseStep 1812671 = 2719007) B2719007
theorem B1354799 : Blo 802343 1354799 := bstep (se 1 (by rfl) ⟨1016099, by rfl⟩ : syracuseStep 1354799 = 2032199) B2032199
theorem B1354873 : Blo 802343 1354873 := bstep (se 2 (by rfl) ⟨508077, by rfl⟩ : syracuseStep 1354873 = 1016155) B1016155
theorem B1813625 : Blo 802343 1813625 := bstep (se 2 (by rfl) ⟨680109, by rfl⟩ : syracuseStep 1813625 = 1360219) B1360219
theorem B3058823 : Blo 802343 3058823 := bstep (se 1 (by rfl) ⟨2294117, by rfl⟩ : syracuseStep 3058823 = 4588235) B4588235
theorem B1355177 : Blo 802343 1355177 := bstep (se 2 (by rfl) ⟨508191, by rfl⟩ : syracuseStep 1355177 = 1016383) B1016383
theorem B1289903 : Blo 802343 1289903 := bstep (se 1 (by rfl) ⟨967427, by rfl⟩ : syracuseStep 1289903 = 1934855) B1934855
theorem B3092243 : Blo 802343 3092243 := bstep (se 1 (by rfl) ⟨2319182, by rfl⟩ : syracuseStep 3092243 = 4638365) B4638365
theorem B5812175 : Blo 802343 5812175 := bstep (se 1 (by rfl) ⟨4359131, by rfl⟩ : syracuseStep 5812175 = 8718263) B8718263
theorem B8695775 : Blo 802343 8695775 := bstep (se 1 (by rfl) ⟨6521831, by rfl⟩ : syracuseStep 8695775 = 13043663) B13043663
theorem B7712819 : Blo 802343 7712819 := bstep (se 1 (by rfl) ⟨5784614, by rfl⟩ : syracuseStep 7712819 = 11569229) B11569229
theorem B1356007 : Blo 802343 1356007 := bstep (se 1 (by rfl) ⟨1017005, by rfl⟩ : syracuseStep 1356007 = 2034011) B2034011
theorem B3059977 : Blo 802343 3059977 := bstep (se 2 (by rfl) ⟨1147491, by rfl⟩ : syracuseStep 3059977 = 2294983) B2294983
theorem B8794423 : Blo 802343 8794423 := bstep (se 1 (by rfl) ⟨6595817, by rfl⟩ : syracuseStep 8794423 = 13191635) B13191635
theorem B1356169 : Blo 802343 1356169 := bstep (se 2 (by rfl) ⟨508563, by rfl⟩ : syracuseStep 1356169 = 1017127) B1017127
theorem B4075919 : Blo 802343 4075919 := bstep (se 1 (by rfl) ⟨3056939, by rfl⟩ : syracuseStep 4075919 = 6113879) B6113879
theorem B7746263 : Blo 802343 7746263 := bstep (se 1 (by rfl) ⟨5809697, by rfl⟩ : syracuseStep 7746263 = 11619395) B11619395
theorem B2896631 : Blo 802343 2896631 := bstep (se 1 (by rfl) ⟨2172473, by rfl⟩ : syracuseStep 2896631 = 4344947) B4344947
theorem B5157665 : Blo 802343 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B2175785 : Blo 802343 2175785 := bstep (se 2 (by rfl) ⟨815919, by rfl⟩ : syracuseStep 2175785 = 1631839) B1631839
theorem B1356601 : Blo 802343 1356601 := bstep (se 2 (by rfl) ⟨508725, by rfl⟩ : syracuseStep 1356601 = 1017451) B1017451
theorem B1356655 : Blo 802343 1356655 := bstep (se 1 (by rfl) ⟨1017491, by rfl⟩ : syracuseStep 1356655 = 2034983) B2034983
theorem B1356905 : Blo 802343 1356905 := bstep (se 2 (by rfl) ⟨508839, by rfl⟩ : syracuseStep 1356905 = 1017679) B1017679
theorem B5158565 : Blo 802343 5158565 := bstep (se 4 (by rfl) ⟨483615, by rfl⟩ : syracuseStep 5158565 = 967231) B967231
theorem B10073903 : Blo 802343 10073903 := bstep (se 1 (by rfl) ⟨7555427, by rfl⟩ : syracuseStep 10073903 = 15110855) B15110855
theorem B67090265 : Blo 802343 67090265 := bstep (se 2 (by rfl) ⟨25158849, by rfl⟩ : syracuseStep 67090265 = 50317699) B50317699
theorem B4634857 : Blo 802343 4634857 := bstep (se 2 (by rfl) ⟨1738071, by rfl⟩ : syracuseStep 4634857 = 3476143) B3476143
theorem B1358059 : Blo 802343 1358059 := bstep (se 1 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 1358059 = 2037089) B2037089
theorem B1358363 : Blo 802343 1358363 := bstep (se 1 (by rfl) ⟨1018772, by rfl⟩ : syracuseStep 1358363 = 2037545) B2037545
theorem B2898767 : Blo 802343 2898767 := bstep (se 1 (by rfl) ⟨2174075, by rfl⟩ : syracuseStep 2898767 = 4348151) B4348151
theorem B965467 : Blo 802343 965467 := bstep (se 1 (by rfl) ⟨724100, by rfl⟩ : syracuseStep 965467 = 1448201) B1448201
theorem B2571389 : Blo 802343 2571389 := bstep (se 3 (by rfl) ⟨482135, by rfl⟩ : syracuseStep 2571389 = 964271) B964271
theorem B1359031 : Blo 802343 1359031 := bstep (se 1 (by rfl) ⟨1019273, by rfl⟩ : syracuseStep 1359031 = 2038547) B2038547
theorem B4570465 : Blo 802343 4570465 := bstep (se 2 (by rfl) ⟨1713924, by rfl⟩ : syracuseStep 4570465 = 3427849) B3427849
theorem B1359335 : Blo 802343 1359335 := bstep (se 1 (by rfl) ⟨1019501, by rfl⟩ : syracuseStep 1359335 = 2039003) B2039003
theorem B1359355 : Blo 802343 1359355 := bstep (se 1 (by rfl) ⟨1019516, by rfl⟩ : syracuseStep 1359355 = 2039033) B2039033
theorem B802395 : Blo 802343 802395 := bstep (se 1 (by rfl) ⟨601796, by rfl⟩ : syracuseStep 802395 = 1203593) B1203593
theorem B8699579 : Blo 802343 8699579 := bstep (se 1 (by rfl) ⟨6524684, by rfl⟩ : syracuseStep 8699579 = 13049369) B13049369
theorem B802631 : Blo 802343 802631 := bstep (se 1 (by rfl) ⟨601973, by rfl⟩ : syracuseStep 802631 = 1203947) B1203947
theorem B1359787 : Blo 802343 1359787 := bstep (se 1 (by rfl) ⟨1019840, by rfl⟩ : syracuseStep 1359787 = 2039681) B2039681
theorem B802783 : Blo 802343 802783 := bstep (se 1 (by rfl) ⟨602087, by rfl⟩ : syracuseStep 802783 = 1204175) B1204175
theorem B1360091 : Blo 802343 1360091 := bstep (se 1 (by rfl) ⟨1020068, by rfl⟩ : syracuseStep 1360091 = 2040137) B2040137
theorem B803047 : Blo 802343 803047 := bstep (se 1 (by rfl) ⟨602285, by rfl⟩ : syracuseStep 803047 = 1204571) B1204571
theorem B803199 : Blo 802343 803199 := bstep (se 1 (by rfl) ⟨602399, by rfl⟩ : syracuseStep 803199 = 1204799) B1204799
theorem B1360327 : Blo 802343 1360327 := bstep (se 1 (by rfl) ⟨1020245, by rfl⟩ : syracuseStep 1360327 = 2040491) B2040491
theorem B803279 : Blo 802343 803279 := bstep (se 1 (by rfl) ⟨602459, by rfl⟩ : syracuseStep 803279 = 1204919) B1204919
theorem B1360361 : Blo 802343 1360361 := bstep (se 2 (by rfl) ⟨510135, by rfl⟩ : syracuseStep 1360361 = 1020271) B1020271
theorem B803431 : Blo 802343 803431 := bstep (se 1 (by rfl) ⟨602573, by rfl⟩ : syracuseStep 803431 = 1205147) B1205147
theorem B1721135 : Blo 802343 1721135 := bstep (se 1 (by rfl) ⟨1290851, by rfl⟩ : syracuseStep 1721135 = 2581703) B2581703
theorem B803695 : Blo 802343 803695 := bstep (se 1 (by rfl) ⟨602771, by rfl⟩ : syracuseStep 803695 = 1205543) B1205543
theorem B803751 : Blo 802343 803751 := bstep (se 1 (by rfl) ⟨602813, by rfl⟩ : syracuseStep 803751 = 1205627) B1205627
theorem B4637627 : Blo 802343 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B2474963 : Blo 802343 2474963 := bstep (se 1 (by rfl) ⟨1856222, by rfl⟩ : syracuseStep 2474963 = 3712445) B3712445
theorem B803835 : Blo 802343 803835 := bstep (se 1 (by rfl) ⟨602876, by rfl⟩ : syracuseStep 803835 = 1205753) B1205753
theorem B967735 : Blo 802343 967735 := bstep (se 1 (by rfl) ⟨725801, by rfl⟩ : syracuseStep 967735 = 1451603) B1451603
theorem B803903 : Blo 802343 803903 := bstep (se 1 (by rfl) ⟨602927, by rfl⟩ : syracuseStep 803903 = 1205855) B1205855
theorem B804047 : Blo 802343 804047 := bstep (se 1 (by rfl) ⟨603035, by rfl⟩ : syracuseStep 804047 = 1206071) B1206071
theorem B34784477 : Blo 802343 34784477 := bstep (se 3 (by rfl) ⟨6522089, by rfl⟩ : syracuseStep 34784477 = 13044179) B13044179
theorem B804251 : Blo 802343 804251 := bstep (se 1 (by rfl) ⟨603188, by rfl⟩ : syracuseStep 804251 = 1206377) B1206377
theorem B902767 : Blo 802343 902767 := bstep (se 1 (by rfl) ⟨677075, by rfl⟩ : syracuseStep 902767 = 1354151) B1354151
theorem B804463 : Blo 802343 804463 := bstep (se 1 (by rfl) ⟨603347, by rfl⟩ : syracuseStep 804463 = 1206695) B1206695
theorem B804519 : Blo 802343 804519 := bstep (se 1 (by rfl) ⟨603389, by rfl⟩ : syracuseStep 804519 = 1206779) B1206779
theorem B902875 : Blo 802343 902875 := bstep (se 1 (by rfl) ⟨677156, by rfl⟩ : syracuseStep 902875 = 1354313) B1354313
theorem B804603 : Blo 802343 804603 := bstep (se 1 (by rfl) ⟨603452, by rfl⟩ : syracuseStep 804603 = 1206905) B1206905
theorem B804639 : Blo 802343 804639 := bstep (se 1 (by rfl) ⟨603479, by rfl⟩ : syracuseStep 804639 = 1206959) B1206959
theorem B804671 : Blo 802343 804671 := bstep (se 1 (by rfl) ⟨603503, by rfl⟩ : syracuseStep 804671 = 1207007) B1207007
theorem B804847 : Blo 802343 804847 := bstep (se 1 (by rfl) ⟨603635, by rfl⟩ : syracuseStep 804847 = 1207271) B1207271
theorem B805019 : Blo 802343 805019 := bstep (se 1 (by rfl) ⟨603764, by rfl⟩ : syracuseStep 805019 = 1207529) B1207529
theorem B805055 : Blo 802343 805055 := bstep (se 1 (by rfl) ⟨603791, by rfl⟩ : syracuseStep 805055 = 1207583) B1207583
theorem B4081913 : Blo 802343 4081913 := bstep (se 2 (by rfl) ⟨1530717, by rfl⟩ : syracuseStep 4081913 = 3061435) B3061435
theorem B805167 : Blo 802343 805167 := bstep (se 1 (by rfl) ⟨603875, by rfl⟩ : syracuseStep 805167 = 1207751) B1207751
theorem B18827579 : Blo 802343 18827579 := bstep (se 1 (by rfl) ⟨14120684, by rfl⟩ : syracuseStep 18827579 = 28241369) B28241369
theorem B805403 : Blo 802343 805403 := bstep (se 1 (by rfl) ⟨604052, by rfl⟩ : syracuseStep 805403 = 1208105) B1208105
theorem B805407 : Blo 802343 805407 := bstep (se 1 (by rfl) ⟨604055, by rfl⟩ : syracuseStep 805407 = 1208111) B1208111
theorem B10472075 : Blo 802343 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B904027 : Blo 802343 904027 := bstep (se 1 (by rfl) ⟨678020, by rfl⟩ : syracuseStep 904027 = 1356041) B1356041
theorem B805723 : Blo 802343 805723 := bstep (se 1 (by rfl) ⟨604292, by rfl⟩ : syracuseStep 805723 = 1208585) B1208585
theorem B805791 : Blo 802343 805791 := bstep (se 1 (by rfl) ⟨604343, by rfl⟩ : syracuseStep 805791 = 1208687) B1208687
theorem B805935 : Blo 802343 805935 := bstep (se 1 (by rfl) ⟨604451, by rfl⟩ : syracuseStep 805935 = 1208903) B1208903
theorem B805959 : Blo 802343 805959 := bstep (se 1 (by rfl) ⟨604469, by rfl⟩ : syracuseStep 805959 = 1208939) B1208939
theorem B4902077 : Blo 802343 4902077 := bstep (se 3 (by rfl) ⟨919139, by rfl⟩ : syracuseStep 4902077 = 1838279) B1838279
theorem B806111 : Blo 802343 806111 := bstep (se 1 (by rfl) ⟨604583, by rfl⟩ : syracuseStep 806111 = 1209167) B1209167
theorem B2903465 : Blo 802343 2903465 := bstep (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) B2177599
theorem B45239915 : Blo 802343 45239915 := bstep (se 1 (by rfl) ⟨33929936, by rfl⟩ : syracuseStep 45239915 = 67859873) B67859873
theorem B904999 : Blo 802343 904999 := bstep (se 1 (by rfl) ⟨678749, by rfl⟩ : syracuseStep 904999 = 1357499) B1357499
theorem B1527673 : Blo 802343 1527673 := bstep (se 2 (by rfl) ⟨572877, by rfl⟩ : syracuseStep 1527673 = 1145755) B1145755
theorem B8147249 : Blo 802343 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B3494387 : Blo 802343 3494387 := bstep (se 1 (by rfl) ⟨2620790, by rfl⟩ : syracuseStep 3494387 = 5241581) B5241581
theorem B39703159 : Blo 802343 39703159 := bstep (se 1 (by rfl) ⟨29777369, by rfl⟩ : syracuseStep 39703159 = 59554739) B59554739
theorem B906151 : Blo 802343 906151 := bstep (se 1 (by rfl) ⟨679613, by rfl⟩ : syracuseStep 906151 = 1359227) B1359227
theorem B11916233 : Blo 802343 11916233 := bstep (se 2 (by rfl) ⟨4468587, by rfl⟩ : syracuseStep 11916233 = 8937175) B8937175
theorem B3724283 : Blo 802343 3724283 := bstep (se 1 (by rfl) ⟨2793212, by rfl⟩ : syracuseStep 3724283 = 5586425) B5586425
theorem B1528895 : Blo 802343 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B19584175 : Blo 802343 19584175 := bstep (se 1 (by rfl) ⟨14688131, by rfl⟩ : syracuseStep 19584175 = 29376263) B29376263
theorem B2708855 : Blo 802343 2708855 := bstep (se 1 (by rfl) ⟨2031641, by rfl⟩ : syracuseStep 2708855 = 4063283) B4063283
theorem B6116795 : Blo 802343 6116795 := bstep (se 1 (by rfl) ⟨4587596, by rfl⟩ : syracuseStep 6116795 = 9175193) B9175193
theorem B4577255 : Blo 802343 4577255 := bstep (se 1 (by rfl) ⟨3432941, by rfl⟩ : syracuseStep 4577255 = 6865883) B6865883
theorem B2709665 : Blo 802343 2709665 := bstep (se 2 (by rfl) ⟨1016124, by rfl⟩ : syracuseStep 2709665 = 2032249) B2032249
theorem B10311947 : Blo 802343 10311947 := bstep (se 1 (by rfl) ⟨7733960, by rfl⟩ : syracuseStep 10311947 = 15467921) B15467921
theorem B23517539 : Blo 802343 23517539 := bstep (se 1 (by rfl) ⟨17638154, by rfl⟩ : syracuseStep 23517539 = 35276309) B35276309
theorem B2709935 : Blo 802343 2709935 := bstep (se 1 (by rfl) ⟨2032451, by rfl⟩ : syracuseStep 2709935 = 4064903) B4064903
theorem B4577755 : Blo 802343 4577755 := bstep (se 1 (by rfl) ⟨3433316, by rfl⟩ : syracuseStep 4577755 = 6866633) B6866633
theorem B1530505 : Blo 802343 1530505 := bstep (se 2 (by rfl) ⟨573939, by rfl⟩ : syracuseStep 1530505 = 1147879) B1147879
theorem B11623085 : Blo 802343 11623085 := bstep (se 3 (by rfl) ⟨2179328, by rfl⟩ : syracuseStep 11623085 = 4358657) B4358657
theorem B7330931 : Blo 802343 7330931 := bstep (se 1 (by rfl) ⟨5498198, by rfl⟩ : syracuseStep 7330931 = 10996397) B10996397
theorem B3431609 : Blo 802343 3431609 := bstep (se 2 (by rfl) ⟨1286853, by rfl⟩ : syracuseStep 3431609 = 2573707) B2573707
theorem B1629551 : Blo 802343 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B1203623 : Blo 802343 1203623 := bstep (se 1 (by rfl) ⟨902717, by rfl⟩ : syracuseStep 1203623 = 1805435) B1805435
theorem B2711015 : Blo 802343 2711015 := bstep (se 1 (by rfl) ⟨2033261, by rfl⟩ : syracuseStep 2711015 = 4066523) B4066523
theorem B1203707 : Blo 802343 1203707 := bstep (se 1 (by rfl) ⟨902780, by rfl⟩ : syracuseStep 1203707 = 1805561) B1805561
theorem B1203803 : Blo 802343 1203803 := bstep (se 1 (by rfl) ⟨902852, by rfl⟩ : syracuseStep 1203803 = 1805705) B1805705
theorem B1203887 : Blo 802343 1203887 := bstep (se 1 (by rfl) ⟨902915, by rfl⟩ : syracuseStep 1203887 = 1805831) B1805831
theorem B1204007 : Blo 802343 1204007 := bstep (se 1 (by rfl) ⟨903005, by rfl⟩ : syracuseStep 1204007 = 1806011) B1806011
theorem B9297757 : Blo 802343 9297757 := bstep (se 3 (by rfl) ⟨1743329, by rfl⟩ : syracuseStep 9297757 = 3486659) B3486659
theorem B1204091 : Blo 802343 1204091 := bstep (se 1 (by rfl) ⟨903068, by rfl⟩ : syracuseStep 1204091 = 1806137) B1806137
theorem B2711771 : Blo 802343 2711771 := bstep (se 1 (by rfl) ⟨2033828, by rfl⟩ : syracuseStep 2711771 = 4067657) B4067657
theorem B1204511 : Blo 802343 1204511 := bstep (se 1 (by rfl) ⟨903383, by rfl⟩ : syracuseStep 1204511 = 1806767) B1806767
theorem B5234975 : Blo 802343 5234975 := bstep (se 1 (by rfl) ⟨3926231, by rfl⟩ : syracuseStep 5234975 = 7852463) B7852463
theorem B1204535 : Blo 802343 1204535 := bstep (se 1 (by rfl) ⟨903401, by rfl⟩ : syracuseStep 1204535 = 1806803) B1806803
theorem B1204607 : Blo 802343 1204607 := bstep (se 1 (by rfl) ⟨903455, by rfl⟩ : syracuseStep 1204607 = 1806911) B1806911
theorem B2580923 : Blo 802343 2580923 := bstep (se 1 (by rfl) ⟨1935692, by rfl⟩ : syracuseStep 2580923 = 3871385) B3871385
theorem B1204679 : Blo 802343 1204679 := bstep (se 1 (by rfl) ⟨903509, by rfl⟩ : syracuseStep 1204679 = 1807019) B1807019
theorem B2712041 : Blo 802343 2712041 := bstep (se 2 (by rfl) ⟨1017015, by rfl⟩ : syracuseStep 2712041 = 2034031) B2034031
theorem B9790105 : Blo 802343 9790105 := bstep (se 2 (by rfl) ⟨3671289, by rfl⟩ : syracuseStep 9790105 = 7342579) B7342579
theorem B11592467 : Blo 802343 11592467 := bstep (se 1 (by rfl) ⟨8694350, by rfl⟩ : syracuseStep 11592467 = 17388701) B17388701
theorem B1205033 : Blo 802343 1205033 := bstep (se 2 (by rfl) ⟨451887, by rfl⟩ : syracuseStep 1205033 = 903775) B903775
theorem B18834221 : Blo 802343 18834221 := bstep (se 3 (by rfl) ⟨3531416, by rfl⟩ : syracuseStep 18834221 = 7062833) B7062833
theorem B1205039 : Blo 802343 1205039 := bstep (se 1 (by rfl) ⟨903779, by rfl⟩ : syracuseStep 1205039 = 1807559) B1807559
theorem B1205159 : Blo 802343 1205159 := bstep (se 1 (by rfl) ⟨903869, by rfl⟩ : syracuseStep 1205159 = 1807739) B1807739
theorem B1205243 : Blo 802343 1205243 := bstep (se 1 (by rfl) ⟨903932, by rfl⟩ : syracuseStep 1205243 = 1807865) B1807865
theorem B1205303 : Blo 802343 1205303 := bstep (se 1 (by rfl) ⟨903977, by rfl⟩ : syracuseStep 1205303 = 1807955) B1807955
theorem B2712635 : Blo 802343 2712635 := bstep (se 1 (by rfl) ⟨2034476, by rfl⟩ : syracuseStep 2712635 = 4068953) B4068953
theorem B1205423 : Blo 802343 1205423 := bstep (se 1 (by rfl) ⟨904067, by rfl⟩ : syracuseStep 1205423 = 1808135) B1808135
theorem B2712905 : Blo 802343 2712905 := bstep (se 2 (by rfl) ⟨1017339, by rfl⟩ : syracuseStep 2712905 = 2034679) B2034679
theorem B46294415 : Blo 802343 46294415 := bstep (se 1 (by rfl) ⟨34720811, by rfl⟩ : syracuseStep 46294415 = 69441623) B69441623
theorem B25748941 : Blo 802343 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B1205831 : Blo 802343 1205831 := bstep (se 1 (by rfl) ⟨904373, by rfl⟩ : syracuseStep 1205831 = 1808747) B1808747
theorem B4580945 : Blo 802343 4580945 := bstep (se 2 (by rfl) ⟨1717854, by rfl⟩ : syracuseStep 4580945 = 3435709) B3435709
theorem B1205927 : Blo 802343 1205927 := bstep (se 1 (by rfl) ⟨904445, by rfl⟩ : syracuseStep 1205927 = 1808891) B1808891
theorem B1206011 : Blo 802343 1206011 := bstep (se 1 (by rfl) ⟨904508, by rfl⟩ : syracuseStep 1206011 = 1809017) B1809017
theorem B1206047 : Blo 802343 1206047 := bstep (se 1 (by rfl) ⟨904535, by rfl⟩ : syracuseStep 1206047 = 1809071) B1809071
theorem B1206095 : Blo 802343 1206095 := bstep (se 1 (by rfl) ⟨904571, by rfl⟩ : syracuseStep 1206095 = 1809143) B1809143
theorem B2582369 : Blo 802343 2582369 := bstep (se 2 (by rfl) ⟨968388, by rfl⟩ : syracuseStep 2582369 = 1936777) B1936777
theorem B1206215 : Blo 802343 1206215 := bstep (se 1 (by rfl) ⟨904661, by rfl⟩ : syracuseStep 1206215 = 1809323) B1809323
theorem B3663863 : Blo 802343 3663863 := bstep (se 1 (by rfl) ⟨2747897, by rfl⟩ : syracuseStep 3663863 = 5495795) B5495795
theorem B2287865 : Blo 802343 2287865 := bstep (se 2 (by rfl) ⟨857949, by rfl⟩ : syracuseStep 2287865 = 1715899) B1715899
theorem B1206569 : Blo 802343 1206569 := bstep (se 2 (by rfl) ⟨452463, by rfl⟩ : syracuseStep 1206569 = 904927) B904927
theorem B1206575 : Blo 802343 1206575 := bstep (se 1 (by rfl) ⟨904931, by rfl⟩ : syracuseStep 1206575 = 1809863) B1809863
theorem B1206815 : Blo 802343 1206815 := bstep (se 1 (by rfl) ⟨905111, by rfl⟩ : syracuseStep 1206815 = 1810223) B1810223
theorem B1207199 : Blo 802343 1207199 := bstep (se 1 (by rfl) ⟨905399, by rfl⟩ : syracuseStep 1207199 = 1810799) B1810799
theorem B1207247 : Blo 802343 1207247 := bstep (se 1 (by rfl) ⟨905435, by rfl⟩ : syracuseStep 1207247 = 1810871) B1810871
theorem B1207337 : Blo 802343 1207337 := bstep (se 2 (by rfl) ⟨452751, by rfl⟩ : syracuseStep 1207337 = 905503) B905503
theorem B1207343 : Blo 802343 1207343 := bstep (se 1 (by rfl) ⟨905507, by rfl⟩ : syracuseStep 1207343 = 1811015) B1811015
theorem B1207367 : Blo 802343 1207367 := bstep (se 1 (by rfl) ⟨905525, by rfl⟩ : syracuseStep 1207367 = 1811051) B1811051
theorem B3435641 : Blo 802343 3435641 := bstep (se 2 (by rfl) ⟨1288365, by rfl⟩ : syracuseStep 3435641 = 2576731) B2576731
theorem B2616563 : Blo 802343 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B1207631 : Blo 802343 1207631 := bstep (se 1 (by rfl) ⟨905723, by rfl⟩ : syracuseStep 1207631 = 1811447) B1811447
theorem B1207721 : Blo 802343 1207721 := bstep (se 2 (by rfl) ⟨452895, by rfl⟩ : syracuseStep 1207721 = 905791) B905791
theorem B1207871 : Blo 802343 1207871 := bstep (se 1 (by rfl) ⟨905903, by rfl⟩ : syracuseStep 1207871 = 1811807) B1811807
theorem B1208135 : Blo 802343 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B2715497 : Blo 802343 2715497 := bstep (se 2 (by rfl) ⟨1018311, by rfl⟩ : syracuseStep 2715497 = 2036623) B2036623
theorem B1208219 : Blo 802343 1208219 := bstep (se 1 (by rfl) ⟨906164, by rfl⟩ : syracuseStep 1208219 = 1812329) B1812329
theorem B3436667 : Blo 802343 3436667 := bstep (se 1 (by rfl) ⟨2577500, by rfl⟩ : syracuseStep 3436667 = 5155001) B5155001
theorem B5796029 : Blo 802343 5796029 := bstep (se 3 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 5796029 = 2173511) B2173511
theorem B1208783 : Blo 802343 1208783 := bstep (se 1 (by rfl) ⟨906587, by rfl⟩ : syracuseStep 1208783 = 1813175) B1813175
theorem B1208825 : Blo 802343 1208825 := bstep (se 2 (by rfl) ⟨453309, by rfl⟩ : syracuseStep 1208825 = 906619) B906619
theorem B1143391 : Blo 802343 1143391 := bstep (se 1 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 1143391 = 1715087) B1715087
theorem B1208927 : Blo 802343 1208927 := bstep (se 1 (by rfl) ⟨906695, by rfl⟩ : syracuseStep 1208927 = 1813391) B1813391
theorem B1209407 : Blo 802343 1209407 := bstep (se 1 (by rfl) ⟨907055, by rfl⟩ : syracuseStep 1209407 = 1814111) B1814111
theorem B1209449 : Blo 802343 1209449 := bstep (se 2 (by rfl) ⟨453543, by rfl⟩ : syracuseStep 1209449 = 907087) B907087
theorem B2716847 : Blo 802343 2716847 := bstep (se 1 (by rfl) ⟨2037635, by rfl⟩ : syracuseStep 2716847 = 4075271) B4075271
theorem B2290963 : Blo 802343 2290963 := bstep (se 1 (by rfl) ⟨1718222, by rfl⟩ : syracuseStep 2290963 = 3436445) B3436445
theorem B9762461 : Blo 802343 9762461 := bstep (se 3 (by rfl) ⟨1830461, by rfl⟩ : syracuseStep 9762461 = 3660923) B3660923
theorem B1931003 : Blo 802343 1931003 := bstep (se 1 (by rfl) ⟨1448252, by rfl⟩ : syracuseStep 1931003 = 2896505) B2896505
theorem B10319633 : Blo 802343 10319633 := bstep (se 2 (by rfl) ⟨3869862, by rfl⟩ : syracuseStep 10319633 = 7739725) B7739725
theorem B3864635 : Blo 802343 3864635 := bstep (se 1 (by rfl) ⟨2898476, by rfl⟩ : syracuseStep 3864635 = 5796953) B5796953
theorem B4586003 : Blo 802343 4586003 := bstep (se 1 (by rfl) ⟨3439502, by rfl⟩ : syracuseStep 4586003 = 6879005) B6879005
theorem B1833529 : Blo 802343 1833529 := bstep (se 2 (by rfl) ⟨687573, by rfl⟩ : syracuseStep 1833529 = 1375147) B1375147
theorem B2718791 : Blo 802343 2718791 := bstep (se 1 (by rfl) ⟨2039093, by rfl⟩ : syracuseStep 2718791 = 4078187) B4078187
theorem B2718845 : Blo 802343 2718845 := bstep (se 3 (by rfl) ⟨509783, by rfl⟩ : syracuseStep 2718845 = 1019567) B1019567
theorem B1146079 : Blo 802343 1146079 := bstep (se 1 (by rfl) ⟨859559, by rfl⟩ : syracuseStep 1146079 = 1719119) B1719119
theorem B4062473 : Blo 802343 4062473 := bstep (se 2 (by rfl) ⟨1523427, by rfl⟩ : syracuseStep 4062473 = 3046855) B3046855
theorem B2719115 : Blo 802343 2719115 := bstep (se 1 (by rfl) ⟨2039336, by rfl⟩ : syracuseStep 2719115 = 4078673) B4078673
theorem B2260391 : Blo 802343 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B3440083 : Blo 802343 3440083 := bstep (se 1 (by rfl) ⟨2580062, by rfl⟩ : syracuseStep 3440083 = 5160125) B5160125
theorem B3047159 : Blo 802343 3047159 := bstep (se 1 (by rfl) ⟨2285369, by rfl⟩ : syracuseStep 3047159 = 4570739) B4570739
theorem B4063607 : Blo 802343 4063607 := bstep (se 1 (by rfl) ⟨3047705, by rfl⟩ : syracuseStep 4063607 = 6095411) B6095411
theorem B1835435 : Blo 802343 1835435 := bstep (se 1 (by rfl) ⟨1376576, by rfl⟩ : syracuseStep 1835435 = 2753153) B2753153
theorem B2032087 : Blo 802343 2032087 := bstep (se 1 (by rfl) ⟨1524065, by rfl⟩ : syracuseStep 2032087 = 3048131) B3048131
theorem B3867095 : Blo 802343 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B2720573 : Blo 802343 2720573 := bstep (se 3 (by rfl) ⟨510107, by rfl⟩ : syracuseStep 2720573 = 1020215) B1020215
theorem B4588487 : Blo 802343 4588487 := bstep (se 1 (by rfl) ⟨3441365, by rfl⟩ : syracuseStep 4588487 = 6882731) B6882731
theorem B2721275 : Blo 802343 2721275 := bstep (se 1 (by rfl) ⟨2040956, by rfl⟩ : syracuseStep 2721275 = 4081913) B4081913
theorem B3868211 : Blo 802343 3868211 := bstep (se 1 (by rfl) ⟨2901158, by rfl⟩ : syracuseStep 3868211 = 5802317) B5802317
theorem B6981383 : Blo 802343 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B6883379 : Blo 802343 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B4589693 : Blo 802343 4589693 := bstep (se 3 (by rfl) ⟨860567, by rfl⟩ : syracuseStep 4589693 = 1721135) B1721135
theorem B2329591 : Blo 802343 2329591 := bstep (se 1 (by rfl) ⟨1747193, by rfl⟩ : syracuseStep 2329591 = 3494387) B3494387
theorem B1805903 : Blo 802343 1805903 := bstep (se 1 (by rfl) ⟨1354427, by rfl⟩ : syracuseStep 1805903 = 2708855) B2708855
theorem B3051503 : Blo 802343 3051503 := bstep (se 1 (by rfl) ⟨2288627, by rfl⟩ : syracuseStep 3051503 = 4577255) B4577255
theorem B1806443 : Blo 802343 1806443 := bstep (se 1 (by rfl) ⟨1354832, by rfl⟩ : syracuseStep 1806443 = 2709665) B2709665
theorem B1806497 : Blo 802343 1806497 := bstep (se 2 (by rfl) ⟨677436, by rfl⟩ : syracuseStep 1806497 = 1354873) B1354873
theorem B1806623 : Blo 802343 1806623 := bstep (se 1 (by rfl) ⟨1354967, by rfl⟩ : syracuseStep 1806623 = 2709935) B2709935
theorem B9179567 : Blo 802343 9179567 := bstep (se 1 (by rfl) ⟨6884675, by rfl⟩ : syracuseStep 9179567 = 13769351) B13769351
theorem B2036279 : Blo 802343 2036279 := bstep (se 1 (by rfl) ⟨1527209, by rfl⟩ : syracuseStep 2036279 = 3054419) B3054419
theorem B4887287 : Blo 802343 4887287 := bstep (se 1 (by rfl) ⟨3665465, by rfl⟩ : syracuseStep 4887287 = 7330931) B7330931
theorem B1086367 : Blo 802343 1086367 := bstep (se 1 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 1086367 = 1629551) B1629551
theorem B1807343 : Blo 802343 1807343 := bstep (se 1 (by rfl) ⟨1355507, by rfl⟩ : syracuseStep 1807343 = 2711015) B2711015
theorem B2036897 : Blo 802343 2036897 := bstep (se 2 (by rfl) ⟨763836, by rfl⟩ : syracuseStep 2036897 = 1527673) B1527673
theorem B1807847 : Blo 802343 1807847 := bstep (se 1 (by rfl) ⟨1355885, by rfl⟩ : syracuseStep 1807847 = 2711771) B2711771
theorem B1808009 : Blo 802343 1808009 := bstep (se 2 (by rfl) ⟨678003, by rfl⟩ : syracuseStep 1808009 = 1356007) B1356007
theorem B1808027 : Blo 802343 1808027 := bstep (se 1 (by rfl) ⟨1356020, by rfl⟩ : syracuseStep 1808027 = 2712041) B2712041
theorem B1808225 : Blo 802343 1808225 := bstep (se 2 (by rfl) ⟨678084, by rfl⟩ : syracuseStep 1808225 = 1356169) B1356169
theorem B12556147 : Blo 802343 12556147 := bstep (se 1 (by rfl) ⟨9417110, by rfl⟩ : syracuseStep 12556147 = 18834221) B18834221
theorem B1808423 : Blo 802343 1808423 := bstep (se 1 (by rfl) ⟨1356317, by rfl⟩ : syracuseStep 1808423 = 2712635) B2712635
theorem B50206877 : Blo 802343 50206877 := bstep (se 3 (by rfl) ⟨9413789, by rfl⟩ : syracuseStep 50206877 = 18827579) B18827579
theorem B1808603 : Blo 802343 1808603 := bstep (se 1 (by rfl) ⟨1356452, by rfl⟩ : syracuseStep 1808603 = 2712905) B2712905
theorem B3053963 : Blo 802343 3053963 := bstep (se 1 (by rfl) ⟨2290472, by rfl⟩ : syracuseStep 3053963 = 4580945) B4580945
theorem B1808801 : Blo 802343 1808801 := bstep (se 2 (by rfl) ⟨678300, by rfl⟩ : syracuseStep 1808801 = 1356601) B1356601
theorem B1808873 : Blo 802343 1808873 := bstep (se 2 (by rfl) ⟨678327, by rfl⟩ : syracuseStep 1808873 = 1356655) B1356655
theorem B3054617 : Blo 802343 3054617 := bstep (se 2 (by rfl) ⟨1145481, by rfl⟩ : syracuseStep 3054617 = 2290963) B2290963
theorem B2039215 : Blo 802343 2039215 := bstep (se 1 (by rfl) ⟨1529411, by rfl⟩ : syracuseStep 2039215 = 3058823) B3058823
theorem B1810331 : Blo 802343 1810331 := bstep (se 1 (by rfl) ⟨1357748, by rfl⟩ : syracuseStep 1810331 = 2715497) B2715497
theorem B9052249 : Blo 802343 9052249 := bstep (se 2 (by rfl) ⟨3394593, by rfl⟩ : syracuseStep 9052249 = 6789187) B6789187
theorem B1810745 : Blo 802343 1810745 := bstep (se 2 (by rfl) ⟨679029, by rfl⟩ : syracuseStep 1810745 = 1358059) B1358059
theorem B1450523 : Blo 802343 1450523 := bstep (se 1 (by rfl) ⟨1087892, by rfl⟩ : syracuseStep 1450523 = 2175785) B2175785
theorem B6103673 : Blo 802343 6103673 := bstep (se 2 (by rfl) ⟨2288877, by rfl⟩ : syracuseStep 6103673 = 4577755) B4577755
theorem B1811231 : Blo 802343 1811231 := bstep (se 1 (by rfl) ⟨1358423, by rfl⟩ : syracuseStep 1811231 = 2716847) B2716847
theorem B2040673 : Blo 802343 2040673 := bstep (se 2 (by rfl) ⟨765252, by rfl⟩ : syracuseStep 2040673 = 1530505) B1530505
theorem B7742573 : Blo 802343 7742573 := bstep (se 3 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 7742573 = 2903465) B2903465
theorem B1287289 : Blo 802343 1287289 := bstep (se 2 (by rfl) ⟨482733, by rfl⟩ : syracuseStep 1287289 = 965467) B965467
theorem B1287335 : Blo 802343 1287335 := bstep (se 1 (by rfl) ⟨965501, by rfl⟩ : syracuseStep 1287335 = 1931003) B1931003
theorem B1713737 : Blo 802343 1713737 := bstep (se 2 (by rfl) ⟨642651, by rfl⟩ : syracuseStep 1713737 = 1285303) B1285303
theorem B1812041 : Blo 802343 1812041 := bstep (se 2 (by rfl) ⟨679515, by rfl⟩ : syracuseStep 1812041 = 1359031) B1359031
theorem B3057335 : Blo 802343 3057335 := bstep (se 1 (by rfl) ⟨2293001, by rfl⟩ : syracuseStep 3057335 = 4586003) B4586003
theorem B1812473 : Blo 802343 1812473 := bstep (se 2 (by rfl) ⟨679677, by rfl⟩ : syracuseStep 1812473 = 1359355) B1359355
theorem B1812527 : Blo 802343 1812527 := bstep (se 1 (by rfl) ⟨1359395, by rfl⟩ : syracuseStep 1812527 = 2718791) B2718791
theorem B1714259 : Blo 802343 1714259 := bstep (se 1 (by rfl) ⟨1285694, by rfl⟩ : syracuseStep 1714259 = 2571389) B2571389
theorem B1812563 : Blo 802343 1812563 := bstep (se 1 (by rfl) ⟨1359422, by rfl⟩ : syracuseStep 1812563 = 2718845) B2718845
theorem B3254461 : Blo 802343 3254461 := bstep (se 3 (by rfl) ⟨610211, by rfl⟩ : syracuseStep 3254461 = 1220423) B1220423
theorem B1812743 : Blo 802343 1812743 := bstep (se 1 (by rfl) ⟨1359557, by rfl⟩ : syracuseStep 1812743 = 2719115) B2719115
theorem B12397009 : Blo 802343 12397009 := bstep (se 2 (by rfl) ⟨4648878, by rfl⟩ : syracuseStep 12397009 = 9297757) B9297757
theorem B1714745 : Blo 802343 1714745 := bstep (se 2 (by rfl) ⟨643029, by rfl⟩ : syracuseStep 1714745 = 1286059) B1286059
theorem B1813049 : Blo 802343 1813049 := bstep (se 2 (by rfl) ⟨679893, by rfl⟩ : syracuseStep 1813049 = 1359787) B1359787
theorem B1813769 : Blo 802343 1813769 := bstep (se 2 (by rfl) ⟨680163, by rfl⟩ : syracuseStep 1813769 = 1360327) B1360327
theorem B3091751 : Blo 802343 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B1649975 : Blo 802343 1649975 := bstep (se 1 (by rfl) ⟨1237481, by rfl⟩ : syracuseStep 1649975 = 2474963) B2474963
theorem B1355231 : Blo 802343 1355231 := bstep (se 1 (by rfl) ⟨1016423, by rfl⟩ : syracuseStep 1355231 = 2032847) B2032847
theorem B13053473 : Blo 802343 13053473 := bstep (se 2 (by rfl) ⟨4895052, by rfl⟩ : syracuseStep 13053473 = 9790105) B9790105
theorem B1355447 : Blo 802343 1355447 := bstep (se 1 (by rfl) ⟨1016585, by rfl⟩ : syracuseStep 1355447 = 2033171) B2033171
theorem B1290313 : Blo 802343 1290313 := bstep (se 2 (by rfl) ⟨483867, by rfl⟩ : syracuseStep 1290313 = 967735) B967735
theorem B3060281 : Blo 802343 3060281 := bstep (se 2 (by rfl) ⟨1147605, by rfl⟩ : syracuseStep 3060281 = 2295211) B2295211
theorem B1717129 : Blo 802343 1717129 := bstep (se 2 (by rfl) ⟨643923, by rfl⟩ : syracuseStep 1717129 = 1287847) B1287847
theorem B1356871 : Blo 802343 1356871 := bstep (se 1 (by rfl) ⟨1017653, by rfl⟩ : syracuseStep 1356871 = 2035307) B2035307
theorem B3912923 : Blo 802343 3912923 := bstep (se 1 (by rfl) ⟨2934692, by rfl⟩ : syracuseStep 3912923 = 5869385) B5869385
theorem B4077053 : Blo 802343 4077053 := bstep (se 3 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 4077053 = 1528895) B1528895
theorem B9156239 : Blo 802343 9156239 := bstep (se 1 (by rfl) ⟨6867179, by rfl⟩ : syracuseStep 9156239 = 13734359) B13734359
theorem B7944155 : Blo 802343 7944155 := bstep (se 1 (by rfl) ⟨5958116, by rfl⟩ : syracuseStep 7944155 = 11916233) B11916233
theorem B5159051 : Blo 802343 5159051 := bstep (se 1 (by rfl) ⟨3869288, by rfl⟩ : syracuseStep 5159051 = 7738577) B7738577
theorem B4077863 : Blo 802343 4077863 := bstep (se 1 (by rfl) ⟨3058397, by rfl⟩ : syracuseStep 4077863 = 6116795) B6116795
theorem B15678359 : Blo 802343 15678359 := bstep (se 1 (by rfl) ⟨11758769, by rfl⟩ : syracuseStep 15678359 = 23517539) B23517539
theorem B7748723 : Blo 802343 7748723 := bstep (se 1 (by rfl) ⟨5811542, by rfl⟩ : syracuseStep 7748723 = 11623085) B11623085
theorem B29408831 : Blo 802343 29408831 := bstep (se 1 (by rfl) ⟨22056623, by rfl⟩ : syracuseStep 29408831 = 44113247) B44113247
theorem B802415 : Blo 802343 802415 := bstep (se 1 (by rfl) ⟨601811, by rfl⟩ : syracuseStep 802415 = 1203623) B1203623
theorem B802471 : Blo 802343 802471 := bstep (se 1 (by rfl) ⟨601853, by rfl⟩ : syracuseStep 802471 = 1203707) B1203707
theorem B802535 : Blo 802343 802535 := bstep (se 1 (by rfl) ⟨601901, by rfl⟩ : syracuseStep 802535 = 1203803) B1203803
theorem B1359625 : Blo 802343 1359625 := bstep (se 2 (by rfl) ⟨509859, by rfl⟩ : syracuseStep 1359625 = 1019719) B1019719
theorem B802591 : Blo 802343 802591 := bstep (se 1 (by rfl) ⟨601943, by rfl⟩ : syracuseStep 802591 = 1203887) B1203887
theorem B802671 : Blo 802343 802671 := bstep (se 1 (by rfl) ⟨602003, by rfl⟩ : syracuseStep 802671 = 1204007) B1204007
theorem B802727 : Blo 802343 802727 := bstep (se 1 (by rfl) ⟨602045, by rfl⟩ : syracuseStep 802727 = 1204091) B1204091
theorem B5292071 : Blo 802343 5292071 := bstep (se 1 (by rfl) ⟨3969053, by rfl⟩ : syracuseStep 5292071 = 7938107) B7938107
theorem B803007 : Blo 802343 803007 := bstep (se 1 (by rfl) ⟨602255, by rfl⟩ : syracuseStep 803007 = 1204511) B1204511
theorem B3489983 : Blo 802343 3489983 := bstep (se 1 (by rfl) ⟨2617487, by rfl⟩ : syracuseStep 3489983 = 5234975) B5234975
theorem B803023 : Blo 802343 803023 := bstep (se 1 (by rfl) ⟨602267, by rfl⟩ : syracuseStep 803023 = 1204535) B1204535
theorem B803071 : Blo 802343 803071 := bstep (se 1 (by rfl) ⟨602303, by rfl⟩ : syracuseStep 803071 = 1204607) B1204607
theorem B1720615 : Blo 802343 1720615 := bstep (se 1 (by rfl) ⟨1290461, by rfl⟩ : syracuseStep 1720615 = 2580923) B2580923
theorem B803119 : Blo 802343 803119 := bstep (se 1 (by rfl) ⟨602339, by rfl⟩ : syracuseStep 803119 = 1204679) B1204679
theorem B4079969 : Blo 802343 4079969 := bstep (se 2 (by rfl) ⟨1529988, by rfl⟩ : syracuseStep 4079969 = 3059977) B3059977
theorem B803355 : Blo 802343 803355 := bstep (se 1 (by rfl) ⟨602516, by rfl⟩ : syracuseStep 803355 = 1205033) B1205033
theorem B17842717 : Blo 802343 17842717 := bstep (se 3 (by rfl) ⟨3345509, by rfl⟩ : syracuseStep 17842717 = 6691019) B6691019
theorem B803359 : Blo 802343 803359 := bstep (se 1 (by rfl) ⟨602519, by rfl⟩ : syracuseStep 803359 = 1205039) B1205039
theorem B1360415 : Blo 802343 1360415 := bstep (se 1 (by rfl) ⟨1020311, by rfl⟩ : syracuseStep 1360415 = 2040623) B2040623
theorem B1360489 : Blo 802343 1360489 := bstep (se 2 (by rfl) ⟨510183, by rfl⟩ : syracuseStep 1360489 = 1020367) B1020367
theorem B803439 : Blo 802343 803439 := bstep (se 1 (by rfl) ⟨602579, by rfl⟩ : syracuseStep 803439 = 1205159) B1205159
theorem B803495 : Blo 802343 803495 := bstep (se 1 (by rfl) ⟨602621, by rfl⟩ : syracuseStep 803495 = 1205243) B1205243
theorem B803535 : Blo 802343 803535 := bstep (se 1 (by rfl) ⟨602651, by rfl⟩ : syracuseStep 803535 = 1205303) B1205303
theorem B4571923 : Blo 802343 4571923 := bstep (se 1 (by rfl) ⟨3428942, by rfl⟩ : syracuseStep 4571923 = 6857885) B6857885
theorem B803615 : Blo 802343 803615 := bstep (se 1 (by rfl) ⟨602711, by rfl⟩ : syracuseStep 803615 = 1205423) B1205423
theorem B1524521 : Blo 802343 1524521 := bstep (se 2 (by rfl) ⟨571695, by rfl⟩ : syracuseStep 1524521 = 1143391) B1143391
theorem B52937545 : Blo 802343 52937545 := bstep (se 2 (by rfl) ⟨19851579, by rfl⟩ : syracuseStep 52937545 = 39703159) B39703159
theorem B24757159 : Blo 802343 24757159 := bstep (se 1 (by rfl) ⟨18567869, by rfl⟩ : syracuseStep 24757159 = 37135739) B37135739
theorem B803887 : Blo 802343 803887 := bstep (se 1 (by rfl) ⟨602915, by rfl⟩ : syracuseStep 803887 = 1205831) B1205831
theorem B803951 : Blo 802343 803951 := bstep (se 1 (by rfl) ⟨602963, by rfl⟩ : syracuseStep 803951 = 1205927) B1205927
theorem B804007 : Blo 802343 804007 := bstep (se 1 (by rfl) ⟨603005, by rfl⟩ : syracuseStep 804007 = 1206011) B1206011
theorem B6112421 : Blo 802343 6112421 := bstep (se 4 (by rfl) ⟨573039, by rfl⟩ : syracuseStep 6112421 = 1146079) B1146079
theorem B804031 : Blo 802343 804031 := bstep (se 1 (by rfl) ⟨603023, by rfl⟩ : syracuseStep 804031 = 1206047) B1206047
theorem B804063 : Blo 802343 804063 := bstep (se 1 (by rfl) ⟨603047, by rfl⟩ : syracuseStep 804063 = 1206095) B1206095
theorem B1721579 : Blo 802343 1721579 := bstep (se 1 (by rfl) ⟨1291184, by rfl⟩ : syracuseStep 1721579 = 2582369) B2582369
theorem B804143 : Blo 802343 804143 := bstep (se 1 (by rfl) ⟨603107, by rfl⟩ : syracuseStep 804143 = 1206215) B1206215
theorem B2442575 : Blo 802343 2442575 := bstep (se 1 (by rfl) ⟨1831931, by rfl⟩ : syracuseStep 2442575 = 3663863) B3663863
theorem B1525243 : Blo 802343 1525243 := bstep (se 1 (by rfl) ⟨1143932, by rfl⟩ : syracuseStep 1525243 = 2287865) B2287865
theorem B804379 : Blo 802343 804379 := bstep (se 1 (by rfl) ⟨603284, by rfl⟩ : syracuseStep 804379 = 1206569) B1206569
theorem B804383 : Blo 802343 804383 := bstep (se 1 (by rfl) ⟨603287, by rfl⟩ : syracuseStep 804383 = 1206575) B1206575
theorem B804543 : Blo 802343 804543 := bstep (se 1 (by rfl) ⟨603407, by rfl⟩ : syracuseStep 804543 = 1206815) B1206815
theorem B804799 : Blo 802343 804799 := bstep (se 1 (by rfl) ⟨603599, by rfl⟩ : syracuseStep 804799 = 1207199) B1207199
theorem B804831 : Blo 802343 804831 := bstep (se 1 (by rfl) ⟨603623, by rfl⟩ : syracuseStep 804831 = 1207247) B1207247
theorem B804891 : Blo 802343 804891 := bstep (se 1 (by rfl) ⟨603668, by rfl⟩ : syracuseStep 804891 = 1207337) B1207337
theorem B903199 : Blo 802343 903199 := bstep (se 1 (by rfl) ⟨677399, by rfl⟩ : syracuseStep 903199 = 1354799) B1354799
theorem B804895 : Blo 802343 804895 := bstep (se 1 (by rfl) ⟨603671, by rfl⟩ : syracuseStep 804895 = 1207343) B1207343
theorem B804911 : Blo 802343 804911 := bstep (se 1 (by rfl) ⟨603683, by rfl⟩ : syracuseStep 804911 = 1207367) B1207367
theorem B805087 : Blo 802343 805087 := bstep (se 1 (by rfl) ⟨603815, by rfl⟩ : syracuseStep 805087 = 1207631) B1207631
theorem B903451 : Blo 802343 903451 := bstep (se 1 (by rfl) ⟨677588, by rfl⟩ : syracuseStep 903451 = 1355177) B1355177
theorem B805147 : Blo 802343 805147 := bstep (se 1 (by rfl) ⟨603860, by rfl⟩ : syracuseStep 805147 = 1207721) B1207721
theorem B805247 : Blo 802343 805247 := bstep (se 1 (by rfl) ⟨603935, by rfl⟩ : syracuseStep 805247 = 1207871) B1207871
theorem B805423 : Blo 802343 805423 := bstep (se 1 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 805423 = 1208135) B1208135
theorem B805479 : Blo 802343 805479 := bstep (se 1 (by rfl) ⟨604109, by rfl⟩ : syracuseStep 805479 = 1208219) B1208219
theorem B805855 : Blo 802343 805855 := bstep (se 1 (by rfl) ⟨604391, by rfl⟩ : syracuseStep 805855 = 1208783) B1208783
theorem B6179809 : Blo 802343 6179809 := bstep (se 2 (by rfl) ⟨2317428, by rfl⟩ : syracuseStep 6179809 = 4634857) B4634857
theorem B805883 : Blo 802343 805883 := bstep (se 1 (by rfl) ⟨604412, by rfl⟩ : syracuseStep 805883 = 1208825) B1208825
theorem B805951 : Blo 802343 805951 := bstep (se 1 (by rfl) ⟨604463, by rfl⟩ : syracuseStep 805951 = 1208927) B1208927
theorem B5164175 : Blo 802343 5164175 := bstep (se 1 (by rfl) ⟨3873131, by rfl⟩ : syracuseStep 5164175 = 7746263) B7746263
theorem B6868273 : Blo 802343 6868273 := bstep (se 2 (by rfl) ⟨2575602, by rfl⟩ : syracuseStep 6868273 = 5151205) B5151205
theorem B806271 : Blo 802343 806271 := bstep (se 1 (by rfl) ⟨604703, by rfl⟩ : syracuseStep 806271 = 1209407) B1209407
theorem B904603 : Blo 802343 904603 := bstep (se 1 (by rfl) ⟨678452, by rfl⟩ : syracuseStep 904603 = 1356905) B1356905
theorem B806299 : Blo 802343 806299 := bstep (se 1 (by rfl) ⟨604724, by rfl⟩ : syracuseStep 806299 = 1209449) B1209449
theorem B2444705 : Blo 802343 2444705 := bstep (se 2 (by rfl) ⟨916764, by rfl⟩ : syracuseStep 2444705 = 1833529) B1833529
theorem B6508307 : Blo 802343 6508307 := bstep (se 1 (by rfl) ⟨4881230, by rfl⟩ : syracuseStep 6508307 = 9762461) B9762461
theorem B2576423 : Blo 802343 2576423 := bstep (se 1 (by rfl) ⟨1932317, by rfl⟩ : syracuseStep 2576423 = 3864635) B3864635
theorem B120639773 : Blo 802343 120639773 := bstep (se 3 (by rfl) ⟨22619957, by rfl⟩ : syracuseStep 120639773 = 45239915) B45239915
theorem B905575 : Blo 802343 905575 := bstep (se 1 (by rfl) ⟨679181, by rfl⟩ : syracuseStep 905575 = 1358363) B1358363
theorem B8245981 : Blo 802343 8245981 := bstep (se 3 (by rfl) ⟨1546121, by rfl⟩ : syracuseStep 8245981 = 3092243) B3092243
theorem B2708315 : Blo 802343 2708315 := bstep (se 1 (by rfl) ⟨2031236, by rfl⟩ : syracuseStep 2708315 = 4062473) B4062473
theorem B906223 : Blo 802343 906223 := bstep (se 1 (by rfl) ⟨679667, by rfl⟩ : syracuseStep 906223 = 1359335) B1359335
theorem B9786743 : Blo 802343 9786743 := bstep (se 1 (by rfl) ⟨7340057, by rfl⟩ : syracuseStep 9786743 = 14680115) B14680115
theorem B906727 : Blo 802343 906727 := bstep (se 1 (by rfl) ⟨680045, by rfl⟩ : syracuseStep 906727 = 1360091) B1360091
theorem B906907 : Blo 802343 906907 := bstep (se 1 (by rfl) ⟨680180, by rfl⟩ : syracuseStep 906907 = 1360361) B1360361
theorem B23189651 : Blo 802343 23189651 := bstep (se 1 (by rfl) ⟨17392238, by rfl⟩ : syracuseStep 23189651 = 34784477) B34784477
theorem B3430619 : Blo 802343 3430619 := bstep (se 1 (by rfl) ⟨2572964, by rfl⟩ : syracuseStep 3430619 = 5145929) B5145929
theorem B6510905 : Blo 802343 6510905 := bstep (se 2 (by rfl) ⟨2441589, by rfl⟩ : syracuseStep 6510905 = 4883179) B4883179
theorem B2710043 : Blo 802343 2710043 := bstep (se 1 (by rfl) ⟨2032532, by rfl⟩ : syracuseStep 2710043 = 4065065) B4065065
theorem B6118253 : Blo 802343 6118253 := bstep (se 3 (by rfl) ⟨1147172, by rfl⟩ : syracuseStep 6118253 = 2294345) B2294345
theorem B34331921 : Blo 802343 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B1203527 : Blo 802343 1203527 := bstep (se 1 (by rfl) ⟨902645, by rfl⟩ : syracuseStep 1203527 = 1805291) B1805291
theorem B1203689 : Blo 802343 1203689 := bstep (se 2 (by rfl) ⟨451383, by rfl⟩ : syracuseStep 1203689 = 902767) B902767
theorem B1203833 : Blo 802343 1203833 := bstep (se 2 (by rfl) ⟨451437, by rfl⟩ : syracuseStep 1203833 = 902875) B902875
theorem B3432223 : Blo 802343 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B6119225 : Blo 802343 6119225 := bstep (se 2 (by rfl) ⟨2294709, by rfl⟩ : syracuseStep 6119225 = 4589419) B4589419
theorem B1204079 : Blo 802343 1204079 := bstep (se 1 (by rfl) ⟨903059, by rfl⟩ : syracuseStep 1204079 = 1806119) B1806119
theorem B5791621 : Blo 802343 5791621 := bstep (se 4 (by rfl) ⟨542964, by rfl⟩ : syracuseStep 5791621 = 1085929) B1085929
theorem B15294521 : Blo 802343 15294521 := bstep (se 2 (by rfl) ⟨5735445, by rfl⟩ : syracuseStep 15294521 = 11470891) B11470891
theorem B5431499 : Blo 802343 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B1204763 : Blo 802343 1204763 := bstep (se 1 (by rfl) ⟨903572, by rfl⟩ : syracuseStep 1204763 = 1807145) B1807145
theorem B2482855 : Blo 802343 2482855 := bstep (se 1 (by rfl) ⟨1862141, by rfl⟩ : syracuseStep 2482855 = 3724283) B3724283
theorem B1204943 : Blo 802343 1204943 := bstep (se 1 (by rfl) ⟨903707, by rfl⟩ : syracuseStep 1204943 = 1807415) B1807415
theorem B1204955 : Blo 802343 1204955 := bstep (se 1 (by rfl) ⟨903716, by rfl⟩ : syracuseStep 1204955 = 1807433) B1807433
theorem B1205369 : Blo 802343 1205369 := bstep (se 2 (by rfl) ⟨452013, by rfl⟩ : syracuseStep 1205369 = 904027) B904027
theorem B1467895 : Blo 802343 1467895 := bstep (se 1 (by rfl) ⟨1100921, by rfl⟩ : syracuseStep 1467895 = 2201843) B2201843
theorem B6874631 : Blo 802343 6874631 := bstep (se 1 (by rfl) ⟨5155973, by rfl⟩ : syracuseStep 6874631 = 10311947) B10311947
theorem B2713499 : Blo 802343 2713499 := bstep (se 1 (by rfl) ⟨2035124, by rfl⟩ : syracuseStep 2713499 = 4070249) B4070249
theorem B1206239 : Blo 802343 1206239 := bstep (se 1 (by rfl) ⟨904679, by rfl⟩ : syracuseStep 1206239 = 1809359) B1809359
theorem B1206251 : Blo 802343 1206251 := bstep (se 1 (by rfl) ⟨904688, by rfl⟩ : syracuseStep 1206251 = 1809377) B1809377
theorem B1206299 : Blo 802343 1206299 := bstep (se 1 (by rfl) ⟨904724, by rfl⟩ : syracuseStep 1206299 = 1809449) B1809449
theorem B2287739 : Blo 802343 2287739 := bstep (se 1 (by rfl) ⟨1715804, by rfl⟩ : syracuseStep 2287739 = 3431609) B3431609
theorem B26863741 : Blo 802343 26863741 := bstep (se 3 (by rfl) ⟨5036951, by rfl⟩ : syracuseStep 26863741 = 10073903) B10073903
theorem B1206665 : Blo 802343 1206665 := bstep (se 2 (by rfl) ⟨452499, by rfl⟩ : syracuseStep 1206665 = 904999) B904999
theorem B11725897 : Blo 802343 11725897 := bstep (se 2 (by rfl) ⟨4397211, by rfl⟩ : syracuseStep 11725897 = 8794423) B8794423
theorem B10316969 : Blo 802343 10316969 := bstep (se 2 (by rfl) ⟨3868863, by rfl⟩ : syracuseStep 10316969 = 7737727) B7737727
theorem B7728311 : Blo 802343 7728311 := bstep (se 1 (by rfl) ⟨5796233, by rfl⟩ : syracuseStep 7728311 = 11592467) B11592467
theorem B1207607 : Blo 802343 1207607 := bstep (se 1 (by rfl) ⟨905705, by rfl⟩ : syracuseStep 1207607 = 1811411) B1811411
theorem B1207775 : Blo 802343 1207775 := bstep (se 1 (by rfl) ⟨905831, by rfl⟩ : syracuseStep 1207775 = 1811663) B1811663
theorem B2059847 : Blo 802343 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B2715227 : Blo 802343 2715227 := bstep (se 1 (by rfl) ⟨2036420, by rfl⟩ : syracuseStep 2715227 = 4072841) B4072841
theorem B30862943 : Blo 802343 30862943 := bstep (se 1 (by rfl) ⟨23147207, by rfl⟩ : syracuseStep 30862943 = 46294415) B46294415
theorem B1207991 : Blo 802343 1207991 := bstep (se 1 (by rfl) ⟨905993, by rfl⟩ : syracuseStep 1207991 = 1811987) B1811987
theorem B14708567 : Blo 802343 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B1208201 : Blo 802343 1208201 := bstep (se 2 (by rfl) ⟨453075, by rfl⟩ : syracuseStep 1208201 = 906151) B906151
theorem B1208447 : Blo 802343 1208447 := bstep (se 1 (by rfl) ⟨906335, by rfl⟩ : syracuseStep 1208447 = 1812671) B1812671
theorem B26112233 : Blo 802343 26112233 := bstep (se 2 (by rfl) ⟨9792087, by rfl⟩ : syracuseStep 26112233 = 19584175) B19584175
theorem B2715929 : Blo 802343 2715929 := bstep (se 2 (by rfl) ⟨1018473, by rfl⟩ : syracuseStep 2715929 = 2036947) B2036947
theorem B2290427 : Blo 802343 2290427 := bstep (se 1 (by rfl) ⟨1717820, by rfl⟩ : syracuseStep 2290427 = 3435641) B3435641
theorem B1209083 : Blo 802343 1209083 := bstep (se 1 (by rfl) ⟨906812, by rfl⟩ : syracuseStep 1209083 = 1813625) B1813625
theorem B11727773 : Blo 802343 11727773 := bstep (se 3 (by rfl) ⟨2198957, by rfl⟩ : syracuseStep 11727773 = 4397915) B4397915
theorem B5797183 : Blo 802343 5797183 := bstep (se 1 (by rfl) ⟨4347887, by rfl⟩ : syracuseStep 5797183 = 8695775) B8695775
theorem B5141879 : Blo 802343 5141879 := bstep (se 1 (by rfl) ⟨3856409, by rfl⟩ : syracuseStep 5141879 = 7712819) B7712819
theorem B2291111 : Blo 802343 2291111 := bstep (se 1 (by rfl) ⟨1718333, by rfl⟩ : syracuseStep 2291111 = 3436667) B3436667
theorem B3864019 : Blo 802343 3864019 := bstep (se 1 (by rfl) ⟨2898014, by rfl⟩ : syracuseStep 3864019 = 5796029) B5796029
theorem B2717279 : Blo 802343 2717279 := bstep (se 1 (by rfl) ⟨2037959, by rfl⟩ : syracuseStep 2717279 = 4075919) B4075919
theorem B13072205 : Blo 802343 13072205 := bstep (se 3 (by rfl) ⟨2451038, by rfl⟩ : syracuseStep 13072205 = 4902077) B4902077
theorem B1931087 : Blo 802343 1931087 := bstep (se 1 (by rfl) ⟨1448315, by rfl⟩ : syracuseStep 1931087 = 2896631) B2896631
theorem B3438443 : Blo 802343 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B6977501 : Blo 802343 6977501 := bstep (se 3 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 6977501 = 2616563) B2616563
theorem B6027709 : Blo 802343 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B3439043 : Blo 802343 3439043 := bstep (se 1 (by rfl) ⟨2579282, by rfl⟩ : syracuseStep 3439043 = 5158565) B5158565
theorem B6879755 : Blo 802343 6879755 := bstep (se 1 (by rfl) ⟨5159816, by rfl⟩ : syracuseStep 6879755 = 10319633) B10319633
theorem B44726843 : Blo 802343 44726843 := bstep (se 1 (by rfl) ⟨33545132, by rfl⟩ : syracuseStep 44726843 = 67090265) B67090265
theorem B2292637 : Blo 802343 2292637 := bstep (se 3 (by rfl) ⟨429869, by rfl⟩ : syracuseStep 2292637 = 859739) B859739
theorem B3439741 : Blo 802343 3439741 := bstep (se 3 (by rfl) ⟨644951, by rfl⟩ : syracuseStep 3439741 = 1289903) B1289903
theorem B6093953 : Blo 802343 6093953 := bstep (se 2 (by rfl) ⟨2285232, by rfl⟩ : syracuseStep 6093953 = 4570465) B4570465
theorem B1932511 : Blo 802343 1932511 := bstep (se 1 (by rfl) ⟨1449383, by rfl⟩ : syracuseStep 1932511 = 2898767) B2898767
theorem B1932569 : Blo 802343 1932569 := bstep (se 2 (by rfl) ⟨724713, by rfl⟩ : syracuseStep 1932569 = 1449427) B1449427
theorem B4586777 : Blo 802343 4586777 := bstep (se 2 (by rfl) ⟨1720041, by rfl⟩ : syracuseStep 4586777 = 3440083) B3440083
theorem B2719385 : Blo 802343 2719385 := bstep (se 2 (by rfl) ⟨1019769, by rfl⟩ : syracuseStep 2719385 = 2039539) B2039539
theorem B9273041 : Blo 802343 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B5799719 : Blo 802343 5799719 := bstep (se 1 (by rfl) ⟨4349789, by rfl⟩ : syracuseStep 5799719 = 8699579) B8699579
theorem B2031439 : Blo 802343 2031439 := bstep (se 1 (by rfl) ⟨1523579, by rfl⟩ : syracuseStep 2031439 = 3047159) B3047159
theorem B15499133 : Blo 802343 15499133 := bstep (se 3 (by rfl) ⟨2906087, by rfl⟩ : syracuseStep 15499133 = 5812175) B5812175
theorem B2326655 : Blo 802343 2326655 := bstep (se 1 (by rfl) ⟨1744991, by rfl⟩ : syracuseStep 2326655 = 3489983) B3489983
theorem B2719979 : Blo 802343 2719979 := bstep (se 1 (by rfl) ⟨2039984, by rfl⟩ : syracuseStep 2719979 = 4079969) B4079969
theorem B6881669 : Blo 802343 6881669 := bstep (se 4 (by rfl) ⟨645156, by rfl⟩ : syracuseStep 6881669 = 1290313) B1290313
theorem B2294153 : Blo 802343 2294153 := bstep (se 2 (by rfl) ⟨860307, by rfl⟩ : syracuseStep 2294153 = 1720615) B1720615
theorem B23790289 : Blo 802343 23790289 := bstep (se 2 (by rfl) ⟨8921358, by rfl⟩ : syracuseStep 23790289 = 17842717) B17842717
theorem B6095897 : Blo 802343 6095897 := bstep (se 2 (by rfl) ⟨2285961, by rfl⟩ : syracuseStep 6095897 = 4571923) B4571923
theorem B70583393 : Blo 802343 70583393 := bstep (se 2 (by rfl) ⟨26468772, by rfl⟩ : syracuseStep 70583393 = 52937545) B52937545
theorem B2720897 : Blo 802343 2720897 := bstep (se 2 (by rfl) ⟨1020336, by rfl⟩ : syracuseStep 2720897 = 2040673) B2040673
theorem B4654255 : Blo 802343 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B4588919 : Blo 802343 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B2033657 : Blo 802343 2033657 := bstep (se 2 (by rfl) ⟨762621, by rfl⟩ : syracuseStep 2033657 = 1525243) B1525243
theorem B3442783 : Blo 802343 3442783 := bstep (se 1 (by rfl) ⟨2582087, by rfl⟩ : syracuseStep 3442783 = 5164175) B5164175
theorem B4065389 : Blo 802343 4065389 := bstep (se 3 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 4065389 = 1524521) B1524521
theorem B2034335 : Blo 802343 2034335 := bstep (se 1 (by rfl) ⟨1525751, by rfl⟩ : syracuseStep 2034335 = 3051503) B3051503
theorem B35818321 : Blo 802343 35818321 := bstep (se 2 (by rfl) ⟨13431870, by rfl⟩ : syracuseStep 35818321 = 26863741) B26863741
theorem B1805543 : Blo 802343 1805543 := bstep (se 1 (by rfl) ⟨1354157, by rfl⟩ : syracuseStep 1805543 = 2708315) B2708315
theorem B4590877 : Blo 802343 4590877 := bstep (se 3 (by rfl) ⟨860789, by rfl⟩ : syracuseStep 4590877 = 1721579) B1721579
theorem B13241893 : Blo 802343 13241893 := bstep (se 4 (by rfl) ⟨1241427, by rfl⟩ : syracuseStep 13241893 = 2482855) B2482855
theorem B6524495 : Blo 802343 6524495 := bstep (se 1 (by rfl) ⟨4893371, by rfl⟩ : syracuseStep 6524495 = 9786743) B9786743
theorem B43978565 : Blo 802343 43978565 := bstep (se 4 (by rfl) ⟨4122990, by rfl⟩ : syracuseStep 43978565 = 8245981) B8245981
theorem B15634529 : Blo 802343 15634529 := bstep (se 2 (by rfl) ⟨5862948, by rfl⟩ : syracuseStep 15634529 = 11725897) B11725897
theorem B2035975 : Blo 802343 2035975 := bstep (se 1 (by rfl) ⟨1526981, by rfl⟩ : syracuseStep 2035975 = 3053963) B3053963
theorem B1806695 : Blo 802343 1806695 := bstep (se 1 (by rfl) ⟨1355021, by rfl⟩ : syracuseStep 1806695 = 2710043) B2710043
theorem B2036411 : Blo 802343 2036411 := bstep (se 1 (by rfl) ⟨1527308, by rfl⟩ : syracuseStep 2036411 = 3054617) B3054617
theorem B5149565 : Blo 802343 5149565 := bstep (se 3 (by rfl) ⟨965543, by rfl⟩ : syracuseStep 5149565 = 1931087) B1931087
theorem B10196347 : Blo 802343 10196347 := bstep (se 1 (by rfl) ⟨7647260, by rfl⟩ : syracuseStep 10196347 = 15294521) B15294521
theorem B4069115 : Blo 802343 4069115 := bstep (se 1 (by rfl) ⟨3051836, by rfl⟩ : syracuseStep 4069115 = 6103673) B6103673
theorem B858223 : Blo 802343 858223 := bstep (se 1 (by rfl) ⟨643667, by rfl⟩ : syracuseStep 858223 = 1287335) B1287335
theorem B2038223 : Blo 802343 2038223 := bstep (se 1 (by rfl) ⟨1528667, by rfl⟩ : syracuseStep 2038223 = 3057335) B3057335
theorem B1448489 : Blo 802343 1448489 := bstep (se 2 (by rfl) ⟨543183, by rfl⟩ : syracuseStep 1448489 = 1086367) B1086367
theorem B1808999 : Blo 802343 1808999 := bstep (se 1 (by rfl) ⟨1356749, by rfl⟩ : syracuseStep 1808999 = 2713499) B2713499
theorem B1809161 : Blo 802343 1809161 := bstep (se 2 (by rfl) ⟨678435, by rfl⟩ : syracuseStep 1809161 = 1356871) B1356871
theorem B5152025 : Blo 802343 5152025 := bstep (se 2 (by rfl) ⟨1932009, by rfl⟩ : syracuseStep 5152025 = 3864019) B3864019
theorem B5152207 : Blo 802343 5152207 := bstep (se 1 (by rfl) ⟨3864155, by rfl⟩ : syracuseStep 5152207 = 7728311) B7728311
theorem B1810151 : Blo 802343 1810151 := bstep (se 1 (by rfl) ⟨1357613, by rfl⟩ : syracuseStep 1810151 = 2715227) B2715227
theorem B9805711 : Blo 802343 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B17408155 : Blo 802343 17408155 := bstep (se 1 (by rfl) ⟨13056116, by rfl⟩ : syracuseStep 17408155 = 26112233) B26112233
theorem B1810619 : Blo 802343 1810619 := bstep (se 1 (by rfl) ⟨1357964, by rfl⟩ : syracuseStep 1810619 = 2715929) B2715929
theorem B2040187 : Blo 802343 2040187 := bstep (se 1 (by rfl) ⟨1530140, by rfl⟩ : syracuseStep 2040187 = 3060281) B3060281
theorem B8036945 : Blo 802343 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B4399933 : Blo 802343 4399933 := bstep (se 3 (by rfl) ⟨824987, by rfl⟩ : syracuseStep 4399933 = 1649975) B1649975
theorem B1811519 : Blo 802343 1811519 := bstep (se 1 (by rfl) ⟨1358639, by rfl⟩ : syracuseStep 1811519 = 2717279) B2717279
theorem B6104159 : Blo 802343 6104159 := bstep (se 1 (by rfl) ⟨4578119, by rfl⟩ : syracuseStep 6104159 = 9156239) B9156239
theorem B3056849 : Blo 802343 3056849 := bstep (se 2 (by rfl) ⟨1146318, by rfl⟩ : syracuseStep 3056849 = 2292637) B2292637
theorem B3057851 : Blo 802343 3057851 := bstep (se 1 (by rfl) ⟨2293388, by rfl⟩ : syracuseStep 3057851 = 4586777) B4586777
theorem B1288379 : Blo 802343 1288379 := bstep (se 1 (by rfl) ⟨966284, by rfl⟩ : syracuseStep 1288379 = 1932569) B1932569
theorem B1812833 : Blo 802343 1812833 := bstep (se 2 (by rfl) ⟨679812, by rfl⟩ : syracuseStep 1812833 = 1359625) B1359625
theorem B19605887 : Blo 802343 19605887 := bstep (se 1 (by rfl) ⟨14704415, by rfl⟩ : syracuseStep 19605887 = 29408831) B29408831
theorem B1812923 : Blo 802343 1812923 := bstep (se 1 (by rfl) ⟨1359692, by rfl⟩ : syracuseStep 1812923 = 2719385) B2719385
theorem B10332755 : Blo 802343 10332755 := bstep (se 1 (by rfl) ⟨7749566, by rfl⟩ : syracuseStep 10332755 = 15499133) B15499133
theorem B12069665 : Blo 802343 12069665 := bstep (se 2 (by rfl) ⟨4526124, by rfl⟩ : syracuseStep 12069665 = 9052249) B9052249
theorem B1223623 : Blo 802343 1223623 := bstep (se 1 (by rfl) ⟨917717, by rfl⟩ : syracuseStep 1223623 = 1835435) B1835435
theorem B1813715 : Blo 802343 1813715 := bstep (se 1 (by rfl) ⟨1360286, by rfl⟩ : syracuseStep 1813715 = 2720573) B2720573
theorem B3058991 : Blo 802343 3058991 := bstep (se 1 (by rfl) ⟨2294243, by rfl⟩ : syracuseStep 3058991 = 4588487) B4588487
theorem B4074947 : Blo 802343 4074947 := bstep (se 1 (by rfl) ⟨3056210, by rfl⟩ : syracuseStep 4074947 = 6112421) B6112421
theorem B1813985 : Blo 802343 1813985 := bstep (se 2 (by rfl) ⟨680244, by rfl⟩ : syracuseStep 1813985 = 1360489) B1360489
theorem B1814183 : Blo 802343 1814183 := bstep (se 1 (by rfl) ⟨1360637, by rfl⟩ : syracuseStep 1814183 = 2721275) B2721275
theorem B33009545 : Blo 802343 33009545 := bstep (se 2 (by rfl) ⟨12378579, by rfl⟩ : syracuseStep 33009545 = 24757159) B24757159
theorem B3059795 : Blo 802343 3059795 := bstep (se 1 (by rfl) ⟨2294846, by rfl⟩ : syracuseStep 3059795 = 4589693) B4589693
theorem B1716385 : Blo 802343 1716385 := bstep (se 2 (by rfl) ⟨643644, by rfl⟩ : syracuseStep 1716385 = 1287289) B1287289
theorem B1717615 : Blo 802343 1717615 := bstep (se 1 (by rfl) ⟨1288211, by rfl⟩ : syracuseStep 1717615 = 2576423) B2576423
theorem B80426515 : Blo 802343 80426515 := bstep (se 1 (by rfl) ⟨60319886, by rfl⟩ : syracuseStep 80426515 = 120639773) B120639773
theorem B1357519 : Blo 802343 1357519 := bstep (se 1 (by rfl) ⟨1018139, by rfl⟩ : syracuseStep 1357519 = 2036279) B2036279
theorem B3258191 : Blo 802343 3258191 := bstep (se 1 (by rfl) ⟨2443643, by rfl⟩ : syracuseStep 3258191 = 4887287) B4887287
theorem B16529345 : Blo 802343 16529345 := bstep (se 2 (by rfl) ⟨6198504, by rfl⟩ : syracuseStep 16529345 = 12397009) B12397009
theorem B1357931 : Blo 802343 1357931 := bstep (se 1 (by rfl) ⟨1018448, by rfl⟩ : syracuseStep 1357931 = 2036897) B2036897
theorem B8239745 : Blo 802343 8239745 := bstep (se 2 (by rfl) ⟨3089904, by rfl⟩ : syracuseStep 8239745 = 6179809) B6179809
theorem B33471251 : Blo 802343 33471251 := bstep (se 1 (by rfl) ⟨25103438, by rfl⟩ : syracuseStep 33471251 = 50206877) B50206877
theorem B4569965 : Blo 802343 4569965 := bstep (se 3 (by rfl) ⟨856868, by rfl⟩ : syracuseStep 4569965 = 1713737) B1713737
theorem B4340603 : Blo 802343 4340603 := bstep (se 1 (by rfl) ⟨3255452, by rfl⟩ : syracuseStep 4340603 = 6510905) B6510905
theorem B9157697 : Blo 802343 9157697 := bstep (se 2 (by rfl) ⟨3434136, by rfl⟩ : syracuseStep 9157697 = 6868273) B6868273
theorem B4078835 : Blo 802343 4078835 := bstep (se 1 (by rfl) ⟨3059126, by rfl⟩ : syracuseStep 4078835 = 6118253) B6118253
theorem B22887947 : Blo 802343 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B802351 : Blo 802343 802351 := bstep (se 1 (by rfl) ⟨601763, by rfl⟩ : syracuseStep 802351 = 1203527) B1203527
theorem B802459 : Blo 802343 802459 := bstep (se 1 (by rfl) ⟨601844, by rfl⟩ : syracuseStep 802459 = 1203689) B1203689
theorem B802555 : Blo 802343 802555 := bstep (se 1 (by rfl) ⟨601916, by rfl⟩ : syracuseStep 802555 = 1203833) B1203833
theorem B4079483 : Blo 802343 4079483 := bstep (se 1 (by rfl) ⟨3059612, by rfl⟩ : syracuseStep 4079483 = 6119225) B6119225
theorem B802719 : Blo 802343 802719 := bstep (se 1 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 802719 = 1204079) B1204079
theorem B3620999 : Blo 802343 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B803175 : Blo 802343 803175 := bstep (se 1 (by rfl) ⟨602381, by rfl⟩ : syracuseStep 803175 = 1204763) B1204763
theorem B967015 : Blo 802343 967015 := bstep (se 1 (by rfl) ⟨725261, by rfl⟩ : syracuseStep 967015 = 1450523) B1450523
theorem B803295 : Blo 802343 803295 := bstep (se 1 (by rfl) ⟨602471, by rfl⟩ : syracuseStep 803295 = 1204943) B1204943
theorem B803303 : Blo 802343 803303 := bstep (se 1 (by rfl) ⟨602477, by rfl⟩ : syracuseStep 803303 = 1204955) B1204955
theorem B5161715 : Blo 802343 5161715 := bstep (se 1 (by rfl) ⟨3871286, by rfl⟩ : syracuseStep 5161715 = 7742573) B7742573
theorem B803579 : Blo 802343 803579 := bstep (se 1 (by rfl) ⟨602684, by rfl⟩ : syracuseStep 803579 = 1205369) B1205369
theorem B804159 : Blo 802343 804159 := bstep (se 1 (by rfl) ⟨603119, by rfl⟩ : syracuseStep 804159 = 1206239) B1206239
theorem B804167 : Blo 802343 804167 := bstep (se 1 (by rfl) ⟨603125, by rfl⟩ : syracuseStep 804167 = 1206251) B1206251
theorem B804199 : Blo 802343 804199 := bstep (se 1 (by rfl) ⟨603149, by rfl⟩ : syracuseStep 804199 = 1206299) B1206299
theorem B1525159 : Blo 802343 1525159 := bstep (se 1 (by rfl) ⟨1143869, by rfl⟩ : syracuseStep 1525159 = 2287739) B2287739
theorem B804443 : Blo 802343 804443 := bstep (se 1 (by rfl) ⟨603332, by rfl⟩ : syracuseStep 804443 = 1206665) B1206665
theorem B805071 : Blo 802343 805071 := bstep (se 1 (by rfl) ⟨603803, by rfl⟩ : syracuseStep 805071 = 1207607) B1207607
theorem B903487 : Blo 802343 903487 := bstep (se 1 (by rfl) ⟨677615, by rfl⟩ : syracuseStep 903487 = 1355231) B1355231
theorem B805183 : Blo 802343 805183 := bstep (se 1 (by rfl) ⟨603887, by rfl⟩ : syracuseStep 805183 = 1207775) B1207775
theorem B8702315 : Blo 802343 8702315 := bstep (se 1 (by rfl) ⟨6526736, by rfl⟩ : syracuseStep 8702315 = 13053473) B13053473
theorem B903631 : Blo 802343 903631 := bstep (se 1 (by rfl) ⟨677723, by rfl⟩ : syracuseStep 903631 = 1355447) B1355447
theorem B805327 : Blo 802343 805327 := bstep (se 1 (by rfl) ⟨603995, by rfl⟩ : syracuseStep 805327 = 1207991) B1207991
theorem B805467 : Blo 802343 805467 := bstep (se 1 (by rfl) ⟨604100, by rfl⟩ : syracuseStep 805467 = 1208201) B1208201
theorem B805631 : Blo 802343 805631 := bstep (se 1 (by rfl) ⟨604223, by rfl⟩ : syracuseStep 805631 = 1208447) B1208447
theorem B1526951 : Blo 802343 1526951 := bstep (se 1 (by rfl) ⟨1145213, by rfl⟩ : syracuseStep 1526951 = 2290427) B2290427
theorem B806055 : Blo 802343 806055 := bstep (se 1 (by rfl) ⟨604541, by rfl⟩ : syracuseStep 806055 = 1209083) B1209083
theorem B7818515 : Blo 802343 7818515 := bstep (se 1 (by rfl) ⟨5863886, by rfl⟩ : syracuseStep 7818515 = 11727773) B11727773
theorem B2608615 : Blo 802343 2608615 := bstep (se 1 (by rfl) ⟨1956461, by rfl⟩ : syracuseStep 2608615 = 3912923) B3912923
theorem B3427919 : Blo 802343 3427919 := bstep (se 1 (by rfl) ⟨2570939, by rfl⟩ : syracuseStep 3427919 = 5141879) B5141879
theorem B1527407 : Blo 802343 1527407 := bstep (se 1 (by rfl) ⟨1145555, by rfl⟩ : syracuseStep 1527407 = 2291111) B2291111
theorem B5296103 : Blo 802343 5296103 := bstep (se 1 (by rfl) ⟨3972077, by rfl⟩ : syracuseStep 5296103 = 7944155) B7944155
theorem B2576681 : Blo 802343 2576681 := bstep (se 2 (by rfl) ⟨966255, by rfl⟩ : syracuseStep 2576681 = 1932511) B1932511
theorem B17355485 : Blo 802343 17355485 := bstep (se 3 (by rfl) ⟨3254153, by rfl⟩ : syracuseStep 17355485 = 6508307) B6508307
theorem B5165815 : Blo 802343 5165815 := bstep (se 1 (by rfl) ⟨3874361, by rfl⟩ : syracuseStep 5165815 = 7748723) B7748723
theorem B4576297 : Blo 802343 4576297 := bstep (se 2 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 4576297 = 3432223) B3432223
theorem B2708585 : Blo 802343 2708585 := bstep (se 2 (by rfl) ⟨1015719, by rfl⟩ : syracuseStep 2708585 = 2031439) B2031439
theorem B6182027 : Blo 802343 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B7722161 : Blo 802343 7722161 := bstep (se 2 (by rfl) ⟨2895810, by rfl⟩ : syracuseStep 7722161 = 5791621) B5791621
theorem B3528047 : Blo 802343 3528047 := bstep (se 1 (by rfl) ⟨2646035, by rfl⟩ : syracuseStep 3528047 = 5292071) B5292071
theorem B2709071 : Blo 802343 2709071 := bstep (se 1 (by rfl) ⟨2031803, by rfl⟩ : syracuseStep 2709071 = 4063607) B4063607
theorem B2578063 : Blo 802343 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B906943 : Blo 802343 906943 := bstep (se 1 (by rfl) ⟨680207, by rfl⟩ : syracuseStep 906943 = 1360415) B1360415
theorem B2709449 : Blo 802343 2709449 := bstep (se 2 (by rfl) ⟨1016043, by rfl⟩ : syracuseStep 2709449 = 2032087) B2032087
theorem B1628383 : Blo 802343 1628383 := bstep (se 1 (by rfl) ⟨1221287, by rfl⟩ : syracuseStep 1628383 = 2442575) B2442575
theorem B17357125 : Blo 802343 17357125 := bstep (se 4 (by rfl) ⟨1627230, by rfl⟩ : syracuseStep 17357125 = 3254461) B3254461
theorem B2578807 : Blo 802343 2578807 := bstep (se 1 (by rfl) ⟨1934105, by rfl⟩ : syracuseStep 2578807 = 3868211) B3868211
theorem B1957193 : Blo 802343 1957193 := bstep (se 2 (by rfl) ⟨733947, by rfl⟩ : syracuseStep 1957193 = 1467895) B1467895
theorem B1629803 : Blo 802343 1629803 := bstep (se 1 (by rfl) ⟨1222352, by rfl⟩ : syracuseStep 1629803 = 2444705) B2444705
theorem B1203935 : Blo 802343 1203935 := bstep (se 1 (by rfl) ⟨902951, by rfl⟩ : syracuseStep 1203935 = 1805903) B1805903
theorem B1204265 : Blo 802343 1204265 := bstep (se 2 (by rfl) ⟨451599, by rfl⟩ : syracuseStep 1204265 = 903199) B903199
theorem B1204295 : Blo 802343 1204295 := bstep (se 1 (by rfl) ⟨903221, by rfl⟩ : syracuseStep 1204295 = 1806443) B1806443
theorem B1204331 : Blo 802343 1204331 := bstep (se 1 (by rfl) ⟨903248, by rfl⟩ : syracuseStep 1204331 = 1806497) B1806497
theorem B1204415 : Blo 802343 1204415 := bstep (se 1 (by rfl) ⟨903311, by rfl⟩ : syracuseStep 1204415 = 1806623) B1806623
theorem B6119711 : Blo 802343 6119711 := bstep (se 1 (by rfl) ⟨4589783, by rfl⟩ : syracuseStep 6119711 = 9179567) B9179567
theorem B1204601 : Blo 802343 1204601 := bstep (se 2 (by rfl) ⟨451725, by rfl⟩ : syracuseStep 1204601 = 903451) B903451
theorem B1204895 : Blo 802343 1204895 := bstep (se 1 (by rfl) ⟨903671, by rfl⟩ : syracuseStep 1204895 = 1807343) B1807343
theorem B1205231 : Blo 802343 1205231 := bstep (se 1 (by rfl) ⟨903923, by rfl⟩ : syracuseStep 1205231 = 1807847) B1807847
theorem B1205339 : Blo 802343 1205339 := bstep (se 1 (by rfl) ⟨904004, by rfl⟩ : syracuseStep 1205339 = 1808009) B1808009
theorem B1205351 : Blo 802343 1205351 := bstep (se 1 (by rfl) ⟨904013, by rfl⟩ : syracuseStep 1205351 = 1808027) B1808027
theorem B1205483 : Blo 802343 1205483 := bstep (se 1 (by rfl) ⟨904112, by rfl⟩ : syracuseStep 1205483 = 1808225) B1808225
theorem B3106121 : Blo 802343 3106121 := bstep (se 2 (by rfl) ⟨1164795, by rfl⟩ : syracuseStep 3106121 = 2329591) B2329591
theorem B1205615 : Blo 802343 1205615 := bstep (se 1 (by rfl) ⟨904211, by rfl⟩ : syracuseStep 1205615 = 1808423) B1808423
theorem B15459767 : Blo 802343 15459767 := bstep (se 1 (by rfl) ⟨11594825, by rfl⟩ : syracuseStep 15459767 = 23189651) B23189651
theorem B2287079 : Blo 802343 2287079 := bstep (se 1 (by rfl) ⟨1715309, by rfl⟩ : syracuseStep 2287079 = 3430619) B3430619
theorem B1205735 : Blo 802343 1205735 := bstep (se 1 (by rfl) ⟨904301, by rfl⟩ : syracuseStep 1205735 = 1808603) B1808603
theorem B1205867 : Blo 802343 1205867 := bstep (se 1 (by rfl) ⟨904400, by rfl⟩ : syracuseStep 1205867 = 1808801) B1808801
theorem B1205915 : Blo 802343 1205915 := bstep (se 1 (by rfl) ⟨904436, by rfl⟩ : syracuseStep 1205915 = 1808873) B1808873
theorem B1206137 : Blo 802343 1206137 := bstep (se 2 (by rfl) ⟨452301, by rfl⟩ : syracuseStep 1206137 = 904603) B904603
theorem B1206887 : Blo 802343 1206887 := bstep (se 1 (by rfl) ⟨905165, by rfl⟩ : syracuseStep 1206887 = 1810331) B1810331
theorem B1207163 : Blo 802343 1207163 := bstep (se 1 (by rfl) ⟨905372, by rfl⟩ : syracuseStep 1207163 = 1810745) B1810745
theorem B1207433 : Blo 802343 1207433 := bstep (se 2 (by rfl) ⟨452787, by rfl⟩ : syracuseStep 1207433 = 905575) B905575
theorem B1207487 : Blo 802343 1207487 := bstep (se 1 (by rfl) ⟨905615, by rfl⟩ : syracuseStep 1207487 = 1811231) B1811231
theorem B4583087 : Blo 802343 4583087 := bstep (se 1 (by rfl) ⟨3437315, by rfl⟩ : syracuseStep 4583087 = 6874631) B6874631
theorem B1208027 : Blo 802343 1208027 := bstep (se 1 (by rfl) ⟨906020, by rfl⟩ : syracuseStep 1208027 = 1812041) B1812041
theorem B2289505 : Blo 802343 2289505 := bstep (se 2 (by rfl) ⟨858564, by rfl⟩ : syracuseStep 2289505 = 1717129) B1717129
theorem B1208297 : Blo 802343 1208297 := bstep (se 2 (by rfl) ⟨453111, by rfl⟩ : syracuseStep 1208297 = 906223) B906223
theorem B1208315 : Blo 802343 1208315 := bstep (se 1 (by rfl) ⟨906236, by rfl⟩ : syracuseStep 1208315 = 1812473) B1812473
theorem B1208351 : Blo 802343 1208351 := bstep (se 1 (by rfl) ⟨906263, by rfl⟩ : syracuseStep 1208351 = 1812527) B1812527
theorem B1142839 : Blo 802343 1142839 := bstep (se 1 (by rfl) ⟨857129, by rfl⟩ : syracuseStep 1142839 = 1714259) B1714259
theorem B1208375 : Blo 802343 1208375 := bstep (se 1 (by rfl) ⟨906281, by rfl⟩ : syracuseStep 1208375 = 1812563) B1812563
theorem B1208495 : Blo 802343 1208495 := bstep (se 1 (by rfl) ⟨906371, by rfl⟩ : syracuseStep 1208495 = 1812743) B1812743
theorem B1143163 : Blo 802343 1143163 := bstep (se 1 (by rfl) ⟨857372, by rfl⟩ : syracuseStep 1143163 = 1714745) B1714745
theorem B1208699 : Blo 802343 1208699 := bstep (se 1 (by rfl) ⟨906524, by rfl⟩ : syracuseStep 1208699 = 1813049) B1813049
theorem B7729577 : Blo 802343 7729577 := bstep (se 2 (by rfl) ⟨2898591, by rfl⟩ : syracuseStep 7729577 = 5797183) B5797183
theorem B1208969 : Blo 802343 1208969 := bstep (se 2 (by rfl) ⟨453363, by rfl⟩ : syracuseStep 1208969 = 906727) B906727
theorem B6877979 : Blo 802343 6877979 := bstep (se 1 (by rfl) ⟨5158484, by rfl⟩ : syracuseStep 6877979 = 10316969) B10316969
theorem B1209179 : Blo 802343 1209179 := bstep (se 1 (by rfl) ⟨906884, by rfl⟩ : syracuseStep 1209179 = 1813769) B1813769
theorem B2061167 : Blo 802343 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B1209209 : Blo 802343 1209209 := bstep (se 2 (by rfl) ⟨453453, by rfl⟩ : syracuseStep 1209209 = 906907) B906907
theorem B1373231 : Blo 802343 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B20575295 : Blo 802343 20575295 := bstep (se 1 (by rfl) ⟨15431471, by rfl⟩ : syracuseStep 20575295 = 30862943) B30862943
theorem B16741529 : Blo 802343 16741529 := bstep (se 2 (by rfl) ⟨6278073, by rfl⟩ : syracuseStep 16741529 = 12556147) B12556147
theorem B2718035 : Blo 802343 2718035 := bstep (se 1 (by rfl) ⟨2038526, by rfl⟩ : syracuseStep 2718035 = 4077053) B4077053
theorem B8714803 : Blo 802343 8714803 := bstep (se 1 (by rfl) ⟨6536102, by rfl⟩ : syracuseStep 8714803 = 13072205) B13072205
theorem B2292295 : Blo 802343 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B4651667 : Blo 802343 4651667 := bstep (se 1 (by rfl) ⟨3488750, by rfl⟩ : syracuseStep 4651667 = 6977501) B6977501
theorem B3439367 : Blo 802343 3439367 := bstep (se 1 (by rfl) ⟨2579525, by rfl⟩ : syracuseStep 3439367 = 5159051) B5159051
theorem B4586321 : Blo 802343 4586321 := bstep (se 2 (by rfl) ⟨1719870, by rfl⟩ : syracuseStep 4586321 = 3439741) B3439741
theorem B2718575 : Blo 802343 2718575 := bstep (se 1 (by rfl) ⟨2038931, by rfl⟩ : syracuseStep 2718575 = 4077863) B4077863
theorem B2292695 : Blo 802343 2292695 := bstep (se 1 (by rfl) ⟨1719521, by rfl⟩ : syracuseStep 2292695 = 3439043) B3439043
theorem B4586503 : Blo 802343 4586503 := bstep (se 1 (by rfl) ⟨3439877, by rfl⟩ : syracuseStep 4586503 = 6879755) B6879755
theorem B29817895 : Blo 802343 29817895 := bstep (se 1 (by rfl) ⟨22363421, by rfl⟩ : syracuseStep 29817895 = 44726843) B44726843
theorem B2718953 : Blo 802343 2718953 := bstep (se 2 (by rfl) ⟨1019607, by rfl⟩ : syracuseStep 2718953 = 2039215) B2039215
theorem B10452239 : Blo 802343 10452239 := bstep (se 1 (by rfl) ⟨7839179, by rfl⟩ : syracuseStep 10452239 = 15678359) B15678359
theorem B4062635 : Blo 802343 4062635 := bstep (se 1 (by rfl) ⟨3046976, by rfl⟩ : syracuseStep 4062635 = 6093953) B6093953
theorem B15465917 : Blo 802343 15465917 := bstep (se 3 (by rfl) ⟨2899859, by rfl⟩ : syracuseStep 15465917 = 5799719) B5799719
theorem B4587779 : Blo 802343 4587779 := bstep (se 1 (by rfl) ⟨3440834, by rfl⟩ : syracuseStep 4587779 = 6881669) B6881669
theorem B3441143 : Blo 802343 3441143 := bstep (se 1 (by rfl) ⟨2580857, by rfl⟩ : syracuseStep 3441143 = 5161715) B5161715
theorem B2720249 : Blo 802343 2720249 := bstep (se 2 (by rfl) ⟨1020093, by rfl⟩ : syracuseStep 2720249 = 2040187) B2040187
theorem B4063931 : Blo 802343 4063931 := bstep (se 1 (by rfl) ⟨3047948, by rfl⟩ : syracuseStep 4063931 = 6095897) B6095897
theorem B47055595 : Blo 802343 47055595 := bstep (se 1 (by rfl) ⟨35291696, by rfl⟩ : syracuseStep 47055595 = 70583393) B70583393
theorem B31720385 : Blo 802343 31720385 := bstep (se 2 (by rfl) ⟨11895144, by rfl⟩ : syracuseStep 31720385 = 23790289) B23790289
theorem B5866577 : Blo 802343 5866577 := bstep (se 2 (by rfl) ⟨2199966, by rfl⟩ : syracuseStep 5866577 = 4399933) B4399933
theorem B5801543 : Blo 802343 5801543 := bstep (se 1 (by rfl) ⟨4351157, by rfl⟩ : syracuseStep 5801543 = 8702315) B8702315
theorem B2033545 : Blo 802343 2033545 := bstep (se 2 (by rfl) ⟨762579, by rfl⟩ : syracuseStep 2033545 = 1525159) B1525159
theorem B6096869 : Blo 802343 6096869 := bstep (se 4 (by rfl) ⟨571581, by rfl⟩ : syracuseStep 6096869 = 1143163) B1143163
theorem B5212343 : Blo 802343 5212343 := bstep (se 1 (by rfl) ⟨3909257, by rfl⟩ : syracuseStep 5212343 = 7818515) B7818515
theorem B1018271 : Blo 802343 1018271 := bstep (se 1 (by rfl) ⟨763703, by rfl⟩ : syracuseStep 1018271 = 1527407) B1527407
theorem B10423019 : Blo 802343 10423019 := bstep (se 1 (by rfl) ⟨7817264, by rfl⟩ : syracuseStep 10423019 = 15634529) B15634529
theorem B4590377 : Blo 802343 4590377 := bstep (se 2 (by rfl) ⟨1721391, by rfl⟩ : syracuseStep 4590377 = 3442783) B3442783
theorem B11570323 : Blo 802343 11570323 := bstep (se 1 (by rfl) ⟨8677742, by rfl⟩ : syracuseStep 11570323 = 17355485) B17355485
theorem B1805723 : Blo 802343 1805723 := bstep (se 1 (by rfl) ⟨1354292, by rfl⟩ : syracuseStep 1805723 = 2708585) B2708585
theorem B5148107 : Blo 802343 5148107 := bstep (se 1 (by rfl) ⟨3861080, by rfl⟩ : syracuseStep 5148107 = 7722161) B7722161
theorem B9408125 : Blo 802343 9408125 := bstep (se 3 (by rfl) ⟨1764023, by rfl⟩ : syracuseStep 9408125 = 3528047) B3528047
theorem B1806047 : Blo 802343 1806047 := bstep (se 1 (by rfl) ⟨1354535, by rfl⟩ : syracuseStep 1806047 = 2709071) B2709071
theorem B1806299 : Blo 802343 1806299 := bstep (se 1 (by rfl) ⟨1354724, by rfl⟩ : syracuseStep 1806299 = 2709449) B2709449
theorem B3478153 : Blo 802343 3478153 := bstep (se 2 (by rfl) ⟨1304307, by rfl⟩ : syracuseStep 3478153 = 2608615) B2608615
theorem B1086535 : Blo 802343 1086535 := bstep (se 1 (by rfl) ⟨814901, by rfl⟩ : syracuseStep 1086535 = 1629803) B1629803
theorem B3052673 : Blo 802343 3052673 := bstep (se 2 (by rfl) ⟨1144752, by rfl⟩ : syracuseStep 3052673 = 2289505) B2289505
theorem B4069439 : Blo 802343 4069439 := bstep (se 1 (by rfl) ⟨3052079, by rfl⟩ : syracuseStep 4069439 = 6104159) B6104159
theorem B2037899 : Blo 802343 2037899 := bstep (se 1 (by rfl) ⟨1528424, by rfl⟩ : syracuseStep 2037899 = 3056849) B3056849
theorem B6887753 : Blo 802343 6887753 := bstep (se 2 (by rfl) ⟨2582907, by rfl⟩ : syracuseStep 6887753 = 5165815) B5165815
theorem B6101729 : Blo 802343 6101729 := bstep (se 2 (by rfl) ⟨2288148, by rfl⟩ : syracuseStep 6101729 = 4576297) B4576297
theorem B858919 : Blo 802343 858919 := bstep (se 1 (by rfl) ⟨644189, by rfl⟩ : syracuseStep 858919 = 1288379) B1288379
theorem B2038567 : Blo 802343 2038567 := bstep (se 1 (by rfl) ⟨1528925, by rfl⟩ : syracuseStep 2038567 = 3057851) B3057851
theorem B6888503 : Blo 802343 6888503 := bstep (se 1 (by rfl) ⟨5166377, by rfl⟩ : syracuseStep 6888503 = 10332755) B10332755
theorem B2039327 : Blo 802343 2039327 := bstep (se 1 (by rfl) ⟨1529495, by rfl⟩ : syracuseStep 2039327 = 3058991) B3058991
theorem B1810025 : Blo 802343 1810025 := bstep (se 2 (by rfl) ⟨678759, by rfl⟩ : syracuseStep 1810025 = 1357519) B1357519
theorem B3055391 : Blo 802343 3055391 := bstep (se 1 (by rfl) ⟨2291543, by rfl⟩ : syracuseStep 3055391 = 4583087) B4583087
theorem B2039863 : Blo 802343 2039863 := bstep (se 1 (by rfl) ⟨1529897, by rfl⟩ : syracuseStep 2039863 = 3059795) B3059795
theorem B5153051 : Blo 802343 5153051 := bstep (se 1 (by rfl) ⟨3864788, by rfl⟩ : syracuseStep 5153051 = 7729577) B7729577
theorem B2171177 : Blo 802343 2171177 := bstep (se 2 (by rfl) ⟨814191, by rfl⟩ : syracuseStep 2171177 = 1628383) B1628383
theorem B23142833 : Blo 802343 23142833 := bstep (se 2 (by rfl) ⟨8678562, by rfl⟩ : syracuseStep 23142833 = 17357125) B17357125
theorem B4071869 : Blo 802343 4071869 := bstep (se 3 (by rfl) ⟨763475, by rfl⟩ : syracuseStep 4071869 = 1526951) B1526951
theorem B13738733 : Blo 802343 13738733 := bstep (se 3 (by rfl) ⟨2576012, by rfl⟩ : syracuseStep 13738733 = 5152025) B5152025
theorem B3056393 : Blo 802343 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B2172127 : Blo 802343 2172127 := bstep (se 1 (by rfl) ⟨1629095, by rfl⟩ : syracuseStep 2172127 = 3258191) B3258191
theorem B11019563 : Blo 802343 11019563 := bstep (se 1 (by rfl) ⟨8264672, by rfl⟩ : syracuseStep 11019563 = 16529345) B16529345
theorem B39757193 : Blo 802343 39757193 := bstep (se 2 (by rfl) ⟨14908947, by rfl⟩ : syracuseStep 39757193 = 29817895) B29817895
theorem B1812023 : Blo 802343 1812023 := bstep (se 1 (by rfl) ⟨1359017, by rfl⟩ : syracuseStep 1812023 = 2718035) B2718035
theorem B3057547 : Blo 802343 3057547 := bstep (se 1 (by rfl) ⟨2293160, by rfl⟩ : syracuseStep 3057547 = 4586321) B4586321
theorem B1812383 : Blo 802343 1812383 := bstep (se 1 (by rfl) ⟨1359287, by rfl⟩ : syracuseStep 1812383 = 2718575) B2718575
theorem B2893735 : Blo 802343 2893735 := bstep (se 1 (by rfl) ⟨2170301, by rfl⟩ : syracuseStep 2893735 = 4340603) B4340603
theorem B6105131 : Blo 802343 6105131 := bstep (se 1 (by rfl) ⟨4578848, by rfl⟩ : syracuseStep 6105131 = 9157697) B9157697
theorem B1812635 : Blo 802343 1812635 := bstep (se 1 (by rfl) ⟨1359476, by rfl⟩ : syracuseStep 1812635 = 2718953) B2718953
theorem B88025453 : Blo 802343 88025453 := bstep (se 3 (by rfl) ⟨16504772, by rfl⟩ : syracuseStep 88025453 = 33009545) B33009545
theorem B1813319 : Blo 802343 1813319 := bstep (se 1 (by rfl) ⟨1359989, by rfl⟩ : syracuseStep 1813319 = 2719979) B2719979
theorem B23210873 : Blo 802343 23210873 := bstep (se 2 (by rfl) ⟨8704077, by rfl⟩ : syracuseStep 23210873 = 17408155) B17408155
theorem B6204413 : Blo 802343 6204413 := bstep (se 3 (by rfl) ⟨1163327, by rfl⟩ : syracuseStep 6204413 = 2326655) B2326655
theorem B1289353 : Blo 802343 1289353 := bstep (se 2 (by rfl) ⟨483507, by rfl⟩ : syracuseStep 1289353 = 967015) B967015
theorem B1813931 : Blo 802343 1813931 := bstep (se 1 (by rfl) ⟨1360448, by rfl⟩ : syracuseStep 1813931 = 2720897) B2720897
theorem B3059279 : Blo 802343 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B1355771 : Blo 802343 1355771 := bstep (se 1 (by rfl) ⟨1016828, by rfl⟩ : syracuseStep 1355771 = 2033657) B2033657
theorem B6205673 : Blo 802343 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B1356223 : Blo 802343 1356223 := bstep (se 1 (by rfl) ⟨1017167, by rfl⟩ : syracuseStep 1356223 = 2034335) B2034335
theorem B1717787 : Blo 802343 1717787 := bstep (se 1 (by rfl) ⟨1288340, by rfl⟩ : syracuseStep 1717787 = 2576681) B2576681
theorem B1357607 : Blo 802343 1357607 := bstep (se 1 (by rfl) ⟨1018205, by rfl⟩ : syracuseStep 1357607 = 2036411) B2036411
theorem B47757761 : Blo 802343 47757761 := bstep (se 2 (by rfl) ⟨17909160, by rfl⟩ : syracuseStep 47757761 = 35818321) B35818321
theorem B1358815 : Blo 802343 1358815 := bstep (se 1 (by rfl) ⟨1019111, by rfl⟩ : syracuseStep 1358815 = 2038223) B2038223
theorem B802623 : Blo 802343 802623 := bstep (se 1 (by rfl) ⟨601967, by rfl⟩ : syracuseStep 802623 = 1203935) B1203935
theorem B802843 : Blo 802343 802843 := bstep (se 1 (by rfl) ⟨602132, by rfl⟩ : syracuseStep 802843 = 1204265) B1204265
theorem B802863 : Blo 802343 802863 := bstep (se 1 (by rfl) ⟨602147, by rfl⟩ : syracuseStep 802863 = 1204295) B1204295
theorem B802887 : Blo 802343 802887 := bstep (se 1 (by rfl) ⟨602165, by rfl⟩ : syracuseStep 802887 = 1204331) B1204331
theorem B1523785 : Blo 802343 1523785 := bstep (se 2 (by rfl) ⟨571419, by rfl⟩ : syracuseStep 1523785 = 1142839) B1142839
theorem B802943 : Blo 802343 802943 := bstep (se 1 (by rfl) ⟨602207, by rfl⟩ : syracuseStep 802943 = 1204415) B1204415
theorem B4079807 : Blo 802343 4079807 := bstep (se 1 (by rfl) ⟨3059855, by rfl⟩ : syracuseStep 4079807 = 6119711) B6119711
theorem B803067 : Blo 802343 803067 := bstep (se 1 (by rfl) ⟨602300, by rfl⟩ : syracuseStep 803067 = 1204601) B1204601
theorem B5357963 : Blo 802343 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B803263 : Blo 802343 803263 := bstep (se 1 (by rfl) ⟨602447, by rfl⟩ : syracuseStep 803263 = 1204895) B1204895
theorem B803487 : Blo 802343 803487 := bstep (se 1 (by rfl) ⟨602615, by rfl⟩ : syracuseStep 803487 = 1205231) B1205231
theorem B803559 : Blo 802343 803559 := bstep (se 1 (by rfl) ⟨602669, by rfl⟩ : syracuseStep 803559 = 1205339) B1205339
theorem B803567 : Blo 802343 803567 := bstep (se 1 (by rfl) ⟨602675, by rfl⟩ : syracuseStep 803567 = 1205351) B1205351
theorem B803655 : Blo 802343 803655 := bstep (se 1 (by rfl) ⟨602741, by rfl⟩ : syracuseStep 803655 = 1205483) B1205483
theorem B803743 : Blo 802343 803743 := bstep (se 1 (by rfl) ⟨602807, by rfl⟩ : syracuseStep 803743 = 1205615) B1205615
theorem B10306511 : Blo 802343 10306511 := bstep (se 1 (by rfl) ⟨7729883, by rfl⟩ : syracuseStep 10306511 = 15459767) B15459767
theorem B1524719 : Blo 802343 1524719 := bstep (se 1 (by rfl) ⟨1143539, by rfl⟩ : syracuseStep 1524719 = 2287079) B2287079
theorem B803823 : Blo 802343 803823 := bstep (se 1 (by rfl) ⟨602867, by rfl⟩ : syracuseStep 803823 = 1205735) B1205735
theorem B803911 : Blo 802343 803911 := bstep (se 1 (by rfl) ⟨602933, by rfl⟩ : syracuseStep 803911 = 1205867) B1205867
theorem B803943 : Blo 802343 803943 := bstep (se 1 (by rfl) ⟨602957, by rfl⟩ : syracuseStep 803943 = 1205915) B1205915
theorem B804091 : Blo 802343 804091 := bstep (se 1 (by rfl) ⟨603068, by rfl⟩ : syracuseStep 804091 = 1206137) B1206137
theorem B21972653 : Blo 802343 21972653 := bstep (se 3 (by rfl) ⟨4119872, by rfl⟩ : syracuseStep 21972653 = 8239745) B8239745
theorem B804591 : Blo 802343 804591 := bstep (se 1 (by rfl) ⟨603443, by rfl⟩ : syracuseStep 804591 = 1206887) B1206887
theorem B8046443 : Blo 802343 8046443 := bstep (se 1 (by rfl) ⟨6034832, by rfl⟩ : syracuseStep 8046443 = 12069665) B12069665
theorem B9160613 : Blo 802343 9160613 := bstep (se 4 (by rfl) ⟨858807, by rfl⟩ : syracuseStep 9160613 = 1717615) B1717615
theorem B804775 : Blo 802343 804775 := bstep (se 1 (by rfl) ⟨603581, by rfl⟩ : syracuseStep 804775 = 1207163) B1207163
theorem B107235353 : Blo 802343 107235353 := bstep (se 2 (by rfl) ⟨40213257, by rfl⟩ : syracuseStep 107235353 = 80426515) B80426515
theorem B804955 : Blo 802343 804955 := bstep (se 1 (by rfl) ⟨603716, by rfl⟩ : syracuseStep 804955 = 1207433) B1207433
theorem B804991 : Blo 802343 804991 := bstep (se 1 (by rfl) ⟨603743, by rfl⟩ : syracuseStep 804991 = 1207487) B1207487
theorem B805351 : Blo 802343 805351 := bstep (se 1 (by rfl) ⟨604013, by rfl⟩ : syracuseStep 805351 = 1208027) B1208027
theorem B805531 : Blo 802343 805531 := bstep (se 1 (by rfl) ⟨604148, by rfl⟩ : syracuseStep 805531 = 1208297) B1208297
theorem B805543 : Blo 802343 805543 := bstep (se 1 (by rfl) ⟨604157, by rfl⟩ : syracuseStep 805543 = 1208315) B1208315
theorem B805567 : Blo 802343 805567 := bstep (se 1 (by rfl) ⟨604175, by rfl⟩ : syracuseStep 805567 = 1208351) B1208351
theorem B805583 : Blo 802343 805583 := bstep (se 1 (by rfl) ⟨604187, by rfl⟩ : syracuseStep 805583 = 1208375) B1208375
theorem B805663 : Blo 802343 805663 := bstep (se 1 (by rfl) ⟨604247, by rfl⟩ : syracuseStep 805663 = 1208495) B1208495
theorem B805799 : Blo 802343 805799 := bstep (se 1 (by rfl) ⟨604349, by rfl⟩ : syracuseStep 805799 = 1208699) B1208699
theorem B805979 : Blo 802343 805979 := bstep (se 1 (by rfl) ⟨604484, by rfl⟩ : syracuseStep 805979 = 1208969) B1208969
theorem B806119 : Blo 802343 806119 := bstep (se 1 (by rfl) ⟨604589, by rfl⟩ : syracuseStep 806119 = 1209179) B1209179
theorem B806139 : Blo 802343 806139 := bstep (se 1 (by rfl) ⟨604604, by rfl⟩ : syracuseStep 806139 = 1209209) B1209209
theorem B13716863 : Blo 802343 13716863 := bstep (se 1 (by rfl) ⟨10287647, by rfl⟩ : syracuseStep 13716863 = 20575295) B20575295
theorem B11619737 : Blo 802343 11619737 := bstep (se 2 (by rfl) ⟨4357401, by rfl⟩ : syracuseStep 11619737 = 8714803) B8714803
theorem B11161019 : Blo 802343 11161019 := bstep (se 1 (by rfl) ⟨8370764, by rfl⟩ : syracuseStep 11161019 = 16741529) B16741529
theorem B6115337 : Blo 802343 6115337 := bstep (se 2 (by rfl) ⟨2293251, by rfl⟩ : syracuseStep 6115337 = 4586503) B4586503
theorem B905287 : Blo 802343 905287 := bstep (se 1 (by rfl) ⟨678965, by rfl⟩ : syracuseStep 905287 = 1357931) B1357931
theorem B3101111 : Blo 802343 3101111 := bstep (se 1 (by rfl) ⟨2325833, by rfl⟩ : syracuseStep 3101111 = 4651667) B4651667
theorem B6869609 : Blo 802343 6869609 := bstep (se 2 (by rfl) ⟨2576103, by rfl⟩ : syracuseStep 6869609 = 5152207) B5152207
theorem B1528463 : Blo 802343 1528463 := bstep (se 1 (by rfl) ⟨1146347, by rfl⟩ : syracuseStep 1528463 = 2292695) B2292695
theorem B6968159 : Blo 802343 6968159 := bstep (se 1 (by rfl) ⟨5226119, by rfl⟩ : syracuseStep 6968159 = 10452239) B10452239
theorem B2708423 : Blo 802343 2708423 := bstep (se 1 (by rfl) ⟨2031317, by rfl⟩ : syracuseStep 2708423 = 4062635) B4062635
theorem B10310611 : Blo 802343 10310611 := bstep (se 1 (by rfl) ⟨7732958, by rfl⟩ : syracuseStep 10310611 = 15465917) B15465917
theorem B15258631 : Blo 802343 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B2413999 : Blo 802343 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B1529435 : Blo 802343 1529435 := bstep (se 1 (by rfl) ⟨1147076, by rfl⟩ : syracuseStep 1529435 = 2294153) B2294153
theorem B2710259 : Blo 802343 2710259 := bstep (se 1 (by rfl) ⟨2032694, by rfl⟩ : syracuseStep 2710259 = 4065389) B4065389
theorem B1203695 : Blo 802343 1203695 := bstep (se 1 (by rfl) ⟨902771, by rfl⟩ : syracuseStep 1203695 = 1805543) B1805543
theorem B5496445 : Blo 802343 5496445 := bstep (se 3 (by rfl) ⟨1030583, by rfl⟩ : syracuseStep 5496445 = 2061167) B2061167
theorem B2285279 : Blo 802343 2285279 := bstep (se 1 (by rfl) ⟨1713959, by rfl⟩ : syracuseStep 2285279 = 3427919) B3427919
theorem B4349663 : Blo 802343 4349663 := bstep (se 1 (by rfl) ⟨3262247, by rfl⟩ : syracuseStep 4349663 = 6524495) B6524495
theorem B29319043 : Blo 802343 29319043 := bstep (se 1 (by rfl) ⟨21989282, by rfl⟩ : syracuseStep 29319043 = 43978565) B43978565
theorem B3530735 : Blo 802343 3530735 := bstep (se 1 (by rfl) ⟨2648051, by rfl⟩ : syracuseStep 3530735 = 5296103) B5296103
theorem B3661949 : Blo 802343 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B1204463 : Blo 802343 1204463 := bstep (se 1 (by rfl) ⟨903347, by rfl⟩ : syracuseStep 1204463 = 1806695) B1806695
theorem B1204649 : Blo 802343 1204649 := bstep (se 2 (by rfl) ⟨451743, by rfl⟩ : syracuseStep 1204649 = 903487) B903487
theorem B3433043 : Blo 802343 3433043 := bstep (se 1 (by rfl) ⟨2574782, by rfl⟩ : syracuseStep 3433043 = 5149565) B5149565
theorem B1204841 : Blo 802343 1204841 := bstep (se 2 (by rfl) ⟨451815, by rfl⟩ : syracuseStep 1204841 = 903631) B903631
theorem B4121351 : Blo 802343 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B8282989 : Blo 802343 8282989 := bstep (se 3 (by rfl) ⟨1553060, by rfl⟩ : syracuseStep 8282989 = 3106121) B3106121
theorem B2712743 : Blo 802343 2712743 := bstep (se 1 (by rfl) ⟨2034557, by rfl⟩ : syracuseStep 2712743 = 4069115) B4069115
theorem B1631497 : Blo 802343 1631497 := bstep (se 2 (by rfl) ⟨611811, by rfl⟩ : syracuseStep 1631497 = 1223623) B1223623
theorem B6121169 : Blo 802343 6121169 := bstep (se 2 (by rfl) ⟨2295438, by rfl⟩ : syracuseStep 6121169 = 4590877) B4590877
theorem B1205999 : Blo 802343 1205999 := bstep (se 1 (by rfl) ⟨904499, by rfl⟩ : syracuseStep 1205999 = 1808999) B1808999
theorem B1206107 : Blo 802343 1206107 := bstep (se 1 (by rfl) ⟨904580, by rfl⟩ : syracuseStep 1206107 = 1809161) B1809161
theorem B17655857 : Blo 802343 17655857 := bstep (se 2 (by rfl) ⟨6620946, by rfl⟩ : syracuseStep 17655857 = 13241893) B13241893
theorem B1304795 : Blo 802343 1304795 := bstep (se 1 (by rfl) ⟨978596, by rfl⟩ : syracuseStep 1304795 = 1957193) B1957193
theorem B1206767 : Blo 802343 1206767 := bstep (se 1 (by rfl) ⟨905075, by rfl⟩ : syracuseStep 1206767 = 1810151) B1810151
theorem B1207079 : Blo 802343 1207079 := bstep (se 1 (by rfl) ⟨905309, by rfl⟩ : syracuseStep 1207079 = 1810619) B1810619
theorem B2288513 : Blo 802343 2288513 := bstep (se 2 (by rfl) ⟨858192, by rfl⟩ : syracuseStep 2288513 = 1716385) B1716385
theorem B2714633 : Blo 802343 2714633 := bstep (se 2 (by rfl) ⟨1017987, by rfl⟩ : syracuseStep 2714633 = 2035975) B2035975
theorem B1207679 : Blo 802343 1207679 := bstep (se 1 (by rfl) ⟨905759, by rfl⟩ : syracuseStep 1207679 = 1811519) B1811519
theorem B3862637 : Blo 802343 3862637 := bstep (se 3 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 3862637 = 1448489) B1448489
theorem B1208555 : Blo 802343 1208555 := bstep (se 1 (by rfl) ⟨906416, by rfl⟩ : syracuseStep 1208555 = 1812833) B1812833
theorem B13070591 : Blo 802343 13070591 := bstep (se 1 (by rfl) ⟨9802943, by rfl⟩ : syracuseStep 13070591 = 19605887) B19605887
theorem B1208615 : Blo 802343 1208615 := bstep (se 1 (by rfl) ⟨906461, by rfl⟩ : syracuseStep 1208615 = 1812923) B1812923
theorem B13595129 : Blo 802343 13595129 := bstep (se 2 (by rfl) ⟨5098173, by rfl⟩ : syracuseStep 13595129 = 10196347) B10196347
theorem B1209143 : Blo 802343 1209143 := bstep (se 1 (by rfl) ⟨906857, by rfl⟩ : syracuseStep 1209143 = 1813715) B1813715
theorem B3437417 : Blo 802343 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B1209257 : Blo 802343 1209257 := bstep (se 2 (by rfl) ⟨453471, by rfl⟩ : syracuseStep 1209257 = 906943) B906943
theorem B2716631 : Blo 802343 2716631 := bstep (se 1 (by rfl) ⟨2037473, by rfl⟩ : syracuseStep 2716631 = 4074947) B4074947
theorem B1209323 : Blo 802343 1209323 := bstep (se 1 (by rfl) ⟨906992, by rfl⟩ : syracuseStep 1209323 = 1813985) B1813985
theorem B1209455 : Blo 802343 1209455 := bstep (se 1 (by rfl) ⟨907091, by rfl⟩ : syracuseStep 1209455 = 1814183) B1814183
theorem B1144297 : Blo 802343 1144297 := bstep (se 2 (by rfl) ⟨429111, by rfl⟩ : syracuseStep 1144297 = 858223) B858223
theorem B3438409 : Blo 802343 3438409 := bstep (se 2 (by rfl) ⟨1289403, by rfl⟩ : syracuseStep 3438409 = 2578807) B2578807
theorem B4585319 : Blo 802343 4585319 := bstep (se 1 (by rfl) ⟨3438989, by rfl⟩ : syracuseStep 4585319 = 6877979) B6877979
theorem B2292911 : Blo 802343 2292911 := bstep (se 1 (by rfl) ⟨1719683, by rfl⟩ : syracuseStep 2292911 = 3439367) B3439367
theorem B22314167 : Blo 802343 22314167 := bstep (se 1 (by rfl) ⟨16735625, by rfl⟩ : syracuseStep 22314167 = 33471251) B33471251
theorem B3046643 : Blo 802343 3046643 := bstep (se 1 (by rfl) ⟨2284982, by rfl⟩ : syracuseStep 3046643 = 4569965) B4569965
theorem B2719223 : Blo 802343 2719223 := bstep (se 1 (by rfl) ⟨2039417, by rfl⟩ : syracuseStep 2719223 = 4078835) B4078835
theorem B13074281 : Blo 802343 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B2719655 : Blo 802343 2719655 := bstep (se 1 (by rfl) ⟨2039741, by rfl⟩ : syracuseStep 2719655 = 4079483) B4079483
theorem B2719817 : Blo 802343 2719817 := bstep (se 2 (by rfl) ⟨1019931, by rfl⟩ : syracuseStep 2719817 = 2039863) B2039863
theorem B2031713 : Blo 802343 2031713 := bstep (se 2 (by rfl) ⟨761892, by rfl⟩ : syracuseStep 2031713 = 1523785) B1523785
theorem B2719871 : Blo 802343 2719871 := bstep (se 1 (by rfl) ⟨2039903, by rfl⟩ : syracuseStep 2719871 = 4079807) B4079807
theorem B3571975 : Blo 802343 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B9765197 : Blo 802343 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B2294095 : Blo 802343 2294095 := bstep (se 1 (by rfl) ⟨1720571, by rfl⟩ : syracuseStep 2294095 = 3441143) B3441143
theorem B16548461 : Blo 802343 16548461 := bstep (se 3 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 16548461 = 6205673) B6205673
theorem B1016479 : Blo 802343 1016479 := bstep (se 1 (by rfl) ⟨762359, by rfl⟩ : syracuseStep 1016479 = 1524719) B1524719
theorem B3867695 : Blo 802343 3867695 := bstep (se 1 (by rfl) ⟨2900771, by rfl⟩ : syracuseStep 3867695 = 5801543) B5801543
theorem B14648435 : Blo 802343 14648435 := bstep (se 1 (by rfl) ⟨10986326, by rfl⟩ : syracuseStep 14648435 = 21972653) B21972653
theorem B11043985 : Blo 802343 11043985 := bstep (se 2 (by rfl) ⟨4141494, by rfl⟩ : syracuseStep 11043985 = 8282989) B8282989
theorem B4064579 : Blo 802343 4064579 := bstep (se 1 (by rfl) ⟨3048434, by rfl⟩ : syracuseStep 4064579 = 6096869) B6096869
theorem B3474895 : Blo 802343 3474895 := bstep (se 1 (by rfl) ⟨2606171, by rfl⟩ : syracuseStep 3474895 = 5212343) B5212343
theorem B9144575 : Blo 802343 9144575 := bstep (se 1 (by rfl) ⟨6858431, by rfl⟩ : syracuseStep 9144575 = 13716863) B13716863
theorem B7440679 : Blo 802343 7440679 := bstep (se 1 (by rfl) ⟨5580509, by rfl⟩ : syracuseStep 7440679 = 11161019) B11161019
theorem B2067407 : Blo 802343 2067407 := bstep (se 1 (by rfl) ⟨1550555, by rfl⟩ : syracuseStep 2067407 = 3101111) B3101111
theorem B1018975 : Blo 802343 1018975 := bstep (se 1 (by rfl) ⟨764231, by rfl⟩ : syracuseStep 1018975 = 1528463) B1528463
theorem B1805615 : Blo 802343 1805615 := bstep (se 1 (by rfl) ⟨1354211, by rfl⟩ : syracuseStep 1805615 = 2708423) B2708423
theorem B2035115 : Blo 802343 2035115 := bstep (se 1 (by rfl) ⟨1526336, by rfl⟩ : syracuseStep 2035115 = 3052673) B3052673
theorem B1019623 : Blo 802343 1019623 := bstep (se 1 (by rfl) ⟨764717, by rfl⟩ : syracuseStep 1019623 = 1529435) B1529435
theorem B4591835 : Blo 802343 4591835 := bstep (se 1 (by rfl) ⟨3443876, by rfl⟩ : syracuseStep 4591835 = 6887753) B6887753
theorem B4067819 : Blo 802343 4067819 := bstep (se 1 (by rfl) ⟨3050864, by rfl⟩ : syracuseStep 4067819 = 6101729) B6101729
theorem B1806839 : Blo 802343 1806839 := bstep (se 1 (by rfl) ⟨1355129, by rfl⟩ : syracuseStep 1806839 = 2710259) B2710259
theorem B4592335 : Blo 802343 4592335 := bstep (se 1 (by rfl) ⟨3444251, by rfl⟩ : syracuseStep 4592335 = 6888503) B6888503
theorem B2036927 : Blo 802343 2036927 := bstep (se 1 (by rfl) ⟨1527695, by rfl⟩ : syracuseStep 2036927 = 3055391) B3055391
theorem B1447451 : Blo 802343 1447451 := bstep (se 1 (by rfl) ⟨1085588, by rfl⟩ : syracuseStep 1447451 = 2171177) B2171177
theorem B2037595 : Blo 802343 2037595 := bstep (se 1 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 2037595 = 3056393) B3056393
theorem B1808297 : Blo 802343 1808297 := bstep (se 2 (by rfl) ⟨678111, by rfl⟩ : syracuseStep 1808297 = 1356223) B1356223
theorem B1808495 : Blo 802343 1808495 := bstep (se 1 (by rfl) ⟨1356371, by rfl⟩ : syracuseStep 1808495 = 2712743) B2712743
theorem B7346375 : Blo 802343 7346375 := bstep (se 1 (by rfl) ⟨5509781, by rfl⟩ : syracuseStep 7346375 = 11019563) B11019563
theorem B4070087 : Blo 802343 4070087 := bstep (se 1 (by rfl) ⟨3052565, by rfl⟩ : syracuseStep 4070087 = 6105131) B6105131
theorem B11770571 : Blo 802343 11770571 := bstep (se 1 (by rfl) ⟨8827928, by rfl⟩ : syracuseStep 11770571 = 17655857) B17655857
theorem B1448713 : Blo 802343 1448713 := bstep (se 2 (by rfl) ⟨543267, by rfl⟩ : syracuseStep 1448713 = 1086535) B1086535
theorem B3218665 : Blo 802343 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B15473915 : Blo 802343 15473915 := bstep (se 1 (by rfl) ⟨11605436, by rfl⟩ : syracuseStep 15473915 = 23210873) B23210873
theorem B27794717 : Blo 802343 27794717 := bstep (se 3 (by rfl) ⟨5211509, by rfl⟩ : syracuseStep 27794717 = 10423019) B10423019
theorem B4136275 : Blo 802343 4136275 := bstep (se 1 (by rfl) ⟨3102206, by rfl⟩ : syracuseStep 4136275 = 6204413) B6204413
theorem B1809755 : Blo 802343 1809755 := bstep (se 1 (by rfl) ⟨1357316, by rfl⟩ : syracuseStep 1809755 = 2714633) B2714633
theorem B6102701 : Blo 802343 6102701 := bstep (se 3 (by rfl) ⟨1144256, by rfl⟩ : syracuseStep 6102701 = 2288513) B2288513
theorem B2039519 : Blo 802343 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B1811087 : Blo 802343 1811087 := bstep (se 1 (by rfl) ⟨1358315, by rfl⟩ : syracuseStep 1811087 = 2716631) B2716631
theorem B3056879 : Blo 802343 3056879 := bstep (se 1 (by rfl) ⟨2292659, by rfl⟩ : syracuseStep 3056879 = 4585319) B4585319
theorem B1811753 : Blo 802343 1811753 := bstep (se 2 (by rfl) ⟨679407, by rfl⟩ : syracuseStep 1811753 = 1358815) B1358815
theorem B1812815 : Blo 802343 1812815 := bstep (se 1 (by rfl) ⟨1359611, by rfl⟩ : syracuseStep 1812815 = 2719223) B2719223
theorem B1813103 : Blo 802343 1813103 := bstep (se 1 (by rfl) ⟨1359827, by rfl⟩ : syracuseStep 1813103 = 2719655) B2719655
theorem B3058519 : Blo 802343 3058519 := bstep (se 1 (by rfl) ⟨2293889, by rfl⟩ : syracuseStep 3058519 = 4587779) B4587779
theorem B1813499 : Blo 802343 1813499 := bstep (se 1 (by rfl) ⟨1360124, by rfl⟩ : syracuseStep 1813499 = 2720249) B2720249
theorem B21146923 : Blo 802343 21146923 := bstep (se 1 (by rfl) ⟨15860192, by rfl⟩ : syracuseStep 21146923 = 31720385) B31720385
theorem B3911051 : Blo 802343 3911051 := bstep (se 1 (by rfl) ⟨2933288, by rfl⟩ : syracuseStep 3911051 = 5866577) B5866577
theorem B6107075 : Blo 802343 6107075 := bstep (se 1 (by rfl) ⟨4580306, by rfl⟩ : syracuseStep 6107075 = 9160613) B9160613
theorem B9154781 : Blo 802343 9154781 := bstep (se 3 (by rfl) ⟨1716521, by rfl⟩ : syracuseStep 9154781 = 3433043) B3433043
theorem B2896169 : Blo 802343 2896169 := bstep (se 2 (by rfl) ⟨1086063, by rfl⟩ : syracuseStep 2896169 = 2172127) B2172127
theorem B2175329 : Blo 802343 2175329 := bstep (se 2 (by rfl) ⟨815748, by rfl⟩ : syracuseStep 2175329 = 1631497) B1631497
theorem B3060251 : Blo 802343 3060251 := bstep (se 1 (by rfl) ⟨2295188, by rfl⟩ : syracuseStep 3060251 = 4590377) B4590377
theorem B7746491 : Blo 802343 7746491 := bstep (se 1 (by rfl) ⟨5809868, by rfl⟩ : syracuseStep 7746491 = 11619737) B11619737
theorem B6272083 : Blo 802343 6272083 := bstep (se 1 (by rfl) ⟨4704062, by rfl⟩ : syracuseStep 6272083 = 9408125) B9408125
theorem B4076729 : Blo 802343 4076729 := bstep (se 2 (by rfl) ⟨1528773, by rfl⟩ : syracuseStep 4076729 = 3057547) B3057547
theorem B4076891 : Blo 802343 4076891 := bstep (se 1 (by rfl) ⟨3057668, by rfl⟩ : syracuseStep 4076891 = 6115337) B6115337
theorem B1358599 : Blo 802343 1358599 := bstep (se 1 (by rfl) ⟨1018949, by rfl⟩ : syracuseStep 1358599 = 2037899) B2037899
theorem B1719137 : Blo 802343 1719137 := bstep (se 2 (by rfl) ⟨644676, by rfl⟩ : syracuseStep 1719137 = 1289353) B1289353
theorem B802463 : Blo 802343 802463 := bstep (se 1 (by rfl) ⟨601847, by rfl⟩ : syracuseStep 802463 = 1203695) B1203695
theorem B1359551 : Blo 802343 1359551 := bstep (se 1 (by rfl) ⟨1019663, by rfl⟩ : syracuseStep 1359551 = 2039327) B2039327
theorem B1523519 : Blo 802343 1523519 := bstep (se 1 (by rfl) ⟨1142639, by rfl⟩ : syracuseStep 1523519 = 2285279) B2285279
theorem B2899775 : Blo 802343 2899775 := bstep (se 1 (by rfl) ⟨2174831, by rfl⟩ : syracuseStep 2899775 = 4349663) B4349663
theorem B802975 : Blo 802343 802975 := bstep (se 1 (by rfl) ⟨602231, by rfl⟩ : syracuseStep 802975 = 1204463) B1204463
theorem B803099 : Blo 802343 803099 := bstep (se 1 (by rfl) ⟨602324, by rfl⟩ : syracuseStep 803099 = 1204649) B1204649
theorem B803227 : Blo 802343 803227 := bstep (se 1 (by rfl) ⟨602420, by rfl⟩ : syracuseStep 803227 = 1204841) B1204841
theorem B9159155 : Blo 802343 9159155 := bstep (se 1 (by rfl) ⟨6869366, by rfl⟩ : syracuseStep 9159155 = 13738733) B13738733
theorem B4637537 : Blo 802343 4637537 := bstep (se 2 (by rfl) ⟨1739076, by rfl⟩ : syracuseStep 4637537 = 3478153) B3478153
theorem B4080779 : Blo 802343 4080779 := bstep (se 1 (by rfl) ⟨3060584, by rfl⟩ : syracuseStep 4080779 = 6121169) B6121169
theorem B803999 : Blo 802343 803999 := bstep (se 1 (by rfl) ⟨602999, by rfl⟩ : syracuseStep 803999 = 1205999) B1205999
theorem B804071 : Blo 802343 804071 := bstep (se 1 (by rfl) ⟨603053, by rfl⟩ : syracuseStep 804071 = 1206107) B1206107
theorem B13747481 : Blo 802343 13747481 := bstep (se 2 (by rfl) ⟨5155305, by rfl⟩ : syracuseStep 13747481 = 10310611) B10310611
theorem B869863 : Blo 802343 869863 := bstep (se 1 (by rfl) ⟨652397, by rfl⟩ : syracuseStep 869863 = 1304795) B1304795
theorem B804511 : Blo 802343 804511 := bstep (se 1 (by rfl) ⟨603383, by rfl⟩ : syracuseStep 804511 = 1206767) B1206767
theorem B804719 : Blo 802343 804719 := bstep (se 1 (by rfl) ⟨603539, by rfl⟩ : syracuseStep 804719 = 1207079) B1207079
theorem B1525729 : Blo 802343 1525729 := bstep (se 2 (by rfl) ⟨572148, by rfl⟩ : syracuseStep 1525729 = 1144297) B1144297
theorem B805119 : Blo 802343 805119 := bstep (se 1 (by rfl) ⟨603839, by rfl⟩ : syracuseStep 805119 = 1207679) B1207679
theorem B903847 : Blo 802343 903847 := bstep (se 1 (by rfl) ⟨677885, by rfl⟩ : syracuseStep 903847 = 1355771) B1355771
theorem B2575091 : Blo 802343 2575091 := bstep (se 1 (by rfl) ⟨1931318, by rfl⟩ : syracuseStep 2575091 = 3862637) B3862637
theorem B805703 : Blo 802343 805703 := bstep (se 1 (by rfl) ⟨604277, by rfl⟩ : syracuseStep 805703 = 1208555) B1208555
theorem B805743 : Blo 802343 805743 := bstep (se 1 (by rfl) ⟨604307, by rfl⟩ : syracuseStep 805743 = 1208615) B1208615
theorem B9063419 : Blo 802343 9063419 := bstep (se 1 (by rfl) ⟨6797564, by rfl⟩ : syracuseStep 9063419 = 13595129) B13595129
theorem B806095 : Blo 802343 806095 := bstep (se 1 (by rfl) ⟨604571, by rfl⟩ : syracuseStep 806095 = 1209143) B1209143
theorem B806171 : Blo 802343 806171 := bstep (se 1 (by rfl) ⟨604628, by rfl⟩ : syracuseStep 806171 = 1209257) B1209257
theorem B806215 : Blo 802343 806215 := bstep (se 1 (by rfl) ⟨604661, by rfl⟩ : syracuseStep 806215 = 1209323) B1209323
theorem B806303 : Blo 802343 806303 := bstep (se 1 (by rfl) ⟨604727, by rfl⟩ : syracuseStep 806303 = 1209455) B1209455
theorem B905071 : Blo 802343 905071 := bstep (se 1 (by rfl) ⟨678803, by rfl⟩ : syracuseStep 905071 = 1357607) B1357607
theorem B31838507 : Blo 802343 31838507 := bstep (se 1 (by rfl) ⟨23878880, by rfl⟩ : syracuseStep 31838507 = 47757761) B47757761
theorem B1528607 : Blo 802343 1528607 := bstep (se 1 (by rfl) ⟨1146455, by rfl⟩ : syracuseStep 1528607 = 2292911) B2292911
theorem B7328593 : Blo 802343 7328593 := bstep (se 2 (by rfl) ⟨2748222, by rfl⟩ : syracuseStep 7328593 = 5496445) B5496445
theorem B2709287 : Blo 802343 2709287 := bstep (se 1 (by rfl) ⟨2031965, by rfl⟩ : syracuseStep 2709287 = 4063931) B4063931
theorem B6871007 : Blo 802343 6871007 := bstep (se 1 (by rfl) ⟨5153255, by rfl⟩ : syracuseStep 6871007 = 10306511) B10306511
theorem B62740793 : Blo 802343 62740793 := bstep (se 2 (by rfl) ⟨23527797, by rfl⟩ : syracuseStep 62740793 = 47055595) B47055595
theorem B71490235 : Blo 802343 71490235 := bstep (se 1 (by rfl) ⟨53617676, by rfl⟩ : syracuseStep 71490235 = 107235353) B107235353
theorem B1203815 : Blo 802343 1203815 := bstep (se 1 (by rfl) ⟨902861, by rfl⟩ : syracuseStep 1203815 = 1805723) B1805723
theorem B9166445 : Blo 802343 9166445 := bstep (se 3 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 9166445 = 3437417) B3437417
theorem B3432071 : Blo 802343 3432071 := bstep (se 1 (by rfl) ⟨2574053, by rfl⟩ : syracuseStep 3432071 = 5148107) B5148107
theorem B1204031 : Blo 802343 1204031 := bstep (se 1 (by rfl) ⟨903023, by rfl⟩ : syracuseStep 1204031 = 1806047) B1806047
theorem B2711393 : Blo 802343 2711393 := bstep (se 2 (by rfl) ⟨1016772, by rfl⟩ : syracuseStep 2711393 = 2033545) B2033545
theorem B3858313 : Blo 802343 3858313 := bstep (se 2 (by rfl) ⟨1446867, by rfl⟩ : syracuseStep 3858313 = 2893735) B2893735
theorem B1204199 : Blo 802343 1204199 := bstep (se 1 (by rfl) ⟨903149, by rfl⟩ : syracuseStep 1204199 = 1806299) B1806299
theorem B4579739 : Blo 802343 4579739 := bstep (se 1 (by rfl) ⟨3434804, by rfl⟩ : syracuseStep 4579739 = 6869609) B6869609
theorem B4645439 : Blo 802343 4645439 := bstep (se 1 (by rfl) ⟨3484079, by rfl⟩ : syracuseStep 4645439 = 6968159) B6968159
theorem B2712959 : Blo 802343 2712959 := bstep (se 1 (by rfl) ⟨2034719, by rfl⟩ : syracuseStep 2712959 = 4069439) B4069439
theorem B15427097 : Blo 802343 15427097 := bstep (se 2 (by rfl) ⟨5785161, by rfl⟩ : syracuseStep 15427097 = 11570323) B11570323
theorem B21457181 : Blo 802343 21457181 := bstep (se 3 (by rfl) ⟨4023221, by rfl⟩ : syracuseStep 21457181 = 8046443) B8046443
theorem B1206683 : Blo 802343 1206683 := bstep (se 1 (by rfl) ⟨905012, by rfl⟩ : syracuseStep 1206683 = 1810025) B1810025
theorem B2353823 : Blo 802343 2353823 := bstep (se 1 (by rfl) ⟨1765367, by rfl⟩ : syracuseStep 2353823 = 3530735) B3530735
theorem B1207049 : Blo 802343 1207049 := bstep (se 2 (by rfl) ⟨452643, by rfl⟩ : syracuseStep 1207049 = 905287) B905287
theorem B3435367 : Blo 802343 3435367 := bstep (se 1 (by rfl) ⟨2576525, by rfl⟩ : syracuseStep 3435367 = 5153051) B5153051
theorem B15428555 : Blo 802343 15428555 := bstep (se 1 (by rfl) ⟨11571416, by rfl⟩ : syracuseStep 15428555 = 23142833) B23142833
theorem B2714579 : Blo 802343 2714579 := bstep (se 1 (by rfl) ⟨2035934, by rfl⟩ : syracuseStep 2714579 = 4071869) B4071869
theorem B2747567 : Blo 802343 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B26504795 : Blo 802343 26504795 := bstep (se 1 (by rfl) ⟨19878596, by rfl⟩ : syracuseStep 26504795 = 39757193) B39757193
theorem B1208015 : Blo 802343 1208015 := bstep (se 1 (by rfl) ⟨906011, by rfl⟩ : syracuseStep 1208015 = 1812023) B1812023
theorem B2715389 : Blo 802343 2715389 := bstep (se 3 (by rfl) ⟨509135, by rfl⟩ : syracuseStep 2715389 = 1018271) B1018271
theorem B1208255 : Blo 802343 1208255 := bstep (se 1 (by rfl) ⟨906191, by rfl⟩ : syracuseStep 1208255 = 1812383) B1812383
theorem B20344841 : Blo 802343 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B1208423 : Blo 802343 1208423 := bstep (se 1 (by rfl) ⟨906317, by rfl⟩ : syracuseStep 1208423 = 1812635) B1812635
theorem B58683635 : Blo 802343 58683635 := bstep (se 1 (by rfl) ⟨44012726, by rfl⟩ : syracuseStep 58683635 = 88025453) B88025453
theorem B1208879 : Blo 802343 1208879 := bstep (se 1 (by rfl) ⟨906659, by rfl⟩ : syracuseStep 1208879 = 1813319) B1813319
theorem B1209287 : Blo 802343 1209287 := bstep (se 1 (by rfl) ⟨906965, by rfl⟩ : syracuseStep 1209287 = 1813931) B1813931
theorem B4584545 : Blo 802343 4584545 := bstep (se 2 (by rfl) ⟨1719204, by rfl⟩ : syracuseStep 4584545 = 3438409) B3438409
theorem B8713727 : Blo 802343 8713727 := bstep (se 1 (by rfl) ⟨6535295, by rfl⟩ : syracuseStep 8713727 = 13070591) B13070591
theorem B1145191 : Blo 802343 1145191 := bstep (se 1 (by rfl) ⟨858893, by rfl⟩ : syracuseStep 1145191 = 1717787) B1717787
theorem B2718089 : Blo 802343 2718089 := bstep (se 2 (by rfl) ⟨1019283, by rfl⟩ : syracuseStep 2718089 = 2038567) B2038567
theorem B1145225 : Blo 802343 1145225 := bstep (se 2 (by rfl) ⟨429459, by rfl⟩ : syracuseStep 1145225 = 858919) B858919
theorem B14876111 : Blo 802343 14876111 := bstep (se 1 (by rfl) ⟨11157083, by rfl⟩ : syracuseStep 14876111 = 22314167) B22314167
theorem B2031095 : Blo 802343 2031095 := bstep (se 1 (by rfl) ⟨1523321, by rfl⟩ : syracuseStep 2031095 = 3046643) B3046643
theorem B39092057 : Blo 802343 39092057 := bstep (se 2 (by rfl) ⟨14659521, by rfl⟩ : syracuseStep 39092057 = 29319043) B29319043
theorem B8716187 : Blo 802343 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B9765623 : Blo 802343 9765623 := bstep (se 1 (by rfl) ⟨7324217, by rfl⟩ : syracuseStep 9765623 = 14648435) B14648435
theorem B2720519 : Blo 802343 2720519 := bstep (se 1 (by rfl) ⟨2040389, by rfl⟩ : syracuseStep 2720519 = 4080779) B4080779
theorem B6096383 : Blo 802343 6096383 := bstep (se 1 (by rfl) ⟨4572287, by rfl⟩ : syracuseStep 6096383 = 9144575) B9144575
theorem B39683621 : Blo 802343 39683621 := bstep (se 4 (by rfl) ⟨3720339, by rfl⟩ : syracuseStep 39683621 = 7440679) B7440679
theorem B2034305 : Blo 802343 2034305 := bstep (se 2 (by rfl) ⟨762864, by rfl⟩ : syracuseStep 2034305 = 1525729) B1525729
theorem B1019071 : Blo 802343 1019071 := bstep (se 1 (by rfl) ⟨764303, by rfl⟩ : syracuseStep 1019071 = 1528607) B1528607
theorem B1806191 : Blo 802343 1806191 := bstep (se 1 (by rfl) ⟨1354643, by rfl⟩ : syracuseStep 1806191 = 2709287) B2709287
theorem B4068467 : Blo 802343 4068467 := bstep (se 1 (by rfl) ⟨3051350, by rfl⟩ : syracuseStep 4068467 = 6102701) B6102701
theorem B1807595 : Blo 802343 1807595 := bstep (se 1 (by rfl) ⟨1355696, by rfl⟩ : syracuseStep 1807595 = 2711393) B2711393
theorem B3053159 : Blo 802343 3053159 := bstep (se 1 (by rfl) ⟨2289869, by rfl⟩ : syracuseStep 3053159 = 4579739) B4579739
theorem B57219149 : Blo 802343 57219149 := bstep (se 3 (by rfl) ⟨10728590, by rfl⟩ : syracuseStep 57219149 = 21457181) B21457181
theorem B2037919 : Blo 802343 2037919 := bstep (se 1 (by rfl) ⟨1528439, by rfl⟩ : syracuseStep 2037919 = 3056879) B3056879
theorem B1808639 : Blo 802343 1808639 := bstep (se 1 (by rfl) ⟨1356479, by rfl⟩ : syracuseStep 1808639 = 2712959) B2712959
theorem B3053933 : Blo 802343 3053933 := bstep (se 3 (by rfl) ⟨572612, by rfl⟩ : syracuseStep 3053933 = 1145225) B1145225
theorem B9771457 : Blo 802343 9771457 := bstep (se 2 (by rfl) ⟨3664296, by rfl⟩ : syracuseStep 9771457 = 7328593) B7328593
theorem B8362777 : Blo 802343 8362777 := bstep (se 2 (by rfl) ⟨3136041, by rfl⟩ : syracuseStep 8362777 = 6272083) B6272083
theorem B22060133 : Blo 802343 22060133 := bstep (se 4 (by rfl) ⟨2068137, by rfl⟩ : syracuseStep 22060133 = 4136275) B4136275
theorem B1809719 : Blo 802343 1809719 := bstep (se 1 (by rfl) ⟨1357289, by rfl⟩ : syracuseStep 1809719 = 2714579) B2714579
theorem B17669863 : Blo 802343 17669863 := bstep (se 1 (by rfl) ⟨13252397, by rfl⟩ : syracuseStep 17669863 = 26504795) B26504795
theorem B1810259 : Blo 802343 1810259 := bstep (se 1 (by rfl) ⟨1357694, by rfl⟩ : syracuseStep 1810259 = 2715389) B2715389
theorem B4071383 : Blo 802343 4071383 := bstep (se 1 (by rfl) ⟨3053537, by rfl⟩ : syracuseStep 4071383 = 6107075) B6107075
theorem B6103187 : Blo 802343 6103187 := bstep (se 1 (by rfl) ⟨4577390, by rfl⟩ : syracuseStep 6103187 = 9154781) B9154781
theorem B1450219 : Blo 802343 1450219 := bstep (se 1 (by rfl) ⟨1087664, by rfl⟩ : syracuseStep 1450219 = 2175329) B2175329
theorem B2040167 : Blo 802343 2040167 := bstep (se 1 (by rfl) ⟨1530125, by rfl⟩ : syracuseStep 2040167 = 3060251) B3060251
theorem B3056363 : Blo 802343 3056363 := bstep (se 1 (by rfl) ⟨2292272, by rfl⟩ : syracuseStep 3056363 = 4584545) B4584545
theorem B5809151 : Blo 802343 5809151 := bstep (se 1 (by rfl) ⟨4356863, by rfl⟩ : syracuseStep 5809151 = 8713727) B8713727
theorem B1811465 : Blo 802343 1811465 := bstep (se 2 (by rfl) ⟨679299, by rfl⟩ : syracuseStep 1811465 = 1358599) B1358599
theorem B10429469 : Blo 802343 10429469 := bstep (se 3 (by rfl) ⟨1955525, by rfl⟩ : syracuseStep 10429469 = 3911051) B3911051
theorem B1812059 : Blo 802343 1812059 := bstep (se 1 (by rfl) ⟨1359044, by rfl⟩ : syracuseStep 1812059 = 2718089) B2718089
theorem B1354063 : Blo 802343 1354063 := bstep (se 1 (by rfl) ⟨1015547, by rfl⟩ : syracuseStep 1354063 = 2031095) B2031095
theorem B26061371 : Blo 802343 26061371 := bstep (se 1 (by rfl) ⟨19546028, by rfl⟩ : syracuseStep 26061371 = 39092057) B39092057
theorem B5810791 : Blo 802343 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B1813211 : Blo 802343 1813211 := bstep (se 1 (by rfl) ⟨1359908, by rfl⟩ : syracuseStep 1813211 = 2719817) B2719817
theorem B1354475 : Blo 802343 1354475 := bstep (se 1 (by rfl) ⟨1015856, by rfl⟩ : syracuseStep 1354475 = 2031713) B2031713
theorem B1813247 : Blo 802343 1813247 := bstep (se 1 (by rfl) ⟨1359935, by rfl⟩ : syracuseStep 1813247 = 2719871) B2719871
theorem B6106103 : Blo 802343 6106103 := bstep (se 1 (by rfl) ⟨4579577, by rfl⟩ : syracuseStep 6106103 = 9159155) B9159155
theorem B4762633 : Blo 802343 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B3058793 : Blo 802343 3058793 := bstep (se 2 (by rfl) ⟨1147047, by rfl⟩ : syracuseStep 3058793 = 2294095) B2294095
theorem B3091691 : Blo 802343 3091691 := bstep (se 1 (by rfl) ⟨2318768, by rfl⟩ : syracuseStep 3091691 = 4637537) B4637537
theorem B1355305 : Blo 802343 1355305 := bstep (se 2 (by rfl) ⟨508239, by rfl⟩ : syracuseStep 1355305 = 1016479) B1016479
theorem B14725313 : Blo 802343 14725313 := bstep (se 2 (by rfl) ⟨5521992, by rfl⟩ : syracuseStep 14725313 = 11043985) B11043985
theorem B1716727 : Blo 802343 1716727 := bstep (se 1 (by rfl) ⟨1287545, by rfl⟩ : syracuseStep 1716727 = 2575091) B2575091
theorem B4633193 : Blo 802343 4633193 := bstep (se 2 (by rfl) ⟨1737447, by rfl⟩ : syracuseStep 4633193 = 3474895) B3474895
theorem B1159817 : Blo 802343 1159817 := bstep (se 2 (by rfl) ⟨434931, by rfl⟩ : syracuseStep 1159817 = 869863) B869863
theorem B1356743 : Blo 802343 1356743 := bstep (se 1 (by rfl) ⟨1017557, by rfl⟩ : syracuseStep 1356743 = 2035115) B2035115
theorem B3061223 : Blo 802343 3061223 := bstep (se 1 (by rfl) ⟨2295917, by rfl⟩ : syracuseStep 3061223 = 4591835) B4591835
theorem B1357951 : Blo 802343 1357951 := bstep (se 1 (by rfl) ⟨1018463, by rfl⟩ : syracuseStep 1357951 = 2036927) B2036927
theorem B964967 : Blo 802343 964967 := bstep (se 1 (by rfl) ⟨723725, by rfl⟩ : syracuseStep 964967 = 1447451) B1447451
theorem B4078025 : Blo 802343 4078025 := bstep (se 2 (by rfl) ⟨1529259, by rfl⟩ : syracuseStep 4078025 = 3058519) B3058519
theorem B1358633 : Blo 802343 1358633 := bstep (se 2 (by rfl) ⟨509487, by rfl⟩ : syracuseStep 1358633 = 1018975) B1018975
theorem B4897583 : Blo 802343 4897583 := bstep (se 1 (by rfl) ⟨3673187, by rfl⟩ : syracuseStep 4897583 = 7346375) B7346375
theorem B41827195 : Blo 802343 41827195 := bstep (se 1 (by rfl) ⟨31370396, by rfl⟩ : syracuseStep 41827195 = 62740793) B62740793
theorem B7847047 : Blo 802343 7847047 := bstep (se 1 (by rfl) ⟨5885285, by rfl⟩ : syracuseStep 7847047 = 11770571) B11770571
theorem B18529811 : Blo 802343 18529811 := bstep (se 1 (by rfl) ⟨13897358, by rfl⟩ : syracuseStep 18529811 = 27794717) B27794717
theorem B1359497 : Blo 802343 1359497 := bstep (se 2 (by rfl) ⟨509811, by rfl⟩ : syracuseStep 1359497 = 1019623) B1019623
theorem B802543 : Blo 802343 802543 := bstep (se 1 (by rfl) ⟨601907, by rfl⟩ : syracuseStep 802543 = 1203815) B1203815
theorem B6110963 : Blo 802343 6110963 := bstep (se 1 (by rfl) ⟨4583222, by rfl⟩ : syracuseStep 6110963 = 9166445) B9166445
theorem B1359679 : Blo 802343 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B802687 : Blo 802343 802687 := bstep (se 1 (by rfl) ⟨602015, by rfl⟩ : syracuseStep 802687 = 1204031) B1204031
theorem B802799 : Blo 802343 802799 := bstep (se 1 (by rfl) ⟨602099, by rfl⟩ : syracuseStep 802799 = 1204199) B1204199
theorem B3096959 : Blo 802343 3096959 := bstep (se 1 (by rfl) ⟨2322719, by rfl⟩ : syracuseStep 3096959 = 4645439) B4645439
theorem B804455 : Blo 802343 804455 := bstep (se 1 (by rfl) ⟨603341, by rfl⟩ : syracuseStep 804455 = 1206683) B1206683
theorem B804699 : Blo 802343 804699 := bstep (se 1 (by rfl) ⟨603524, by rfl⟩ : syracuseStep 804699 = 1207049) B1207049
theorem B805343 : Blo 802343 805343 := bstep (se 1 (by rfl) ⟨604007, by rfl⟩ : syracuseStep 805343 = 1208015) B1208015
theorem B805503 : Blo 802343 805503 := bstep (se 1 (by rfl) ⟨604127, by rfl⟩ : syracuseStep 805503 = 1208255) B1208255
theorem B24169117 : Blo 802343 24169117 := bstep (se 3 (by rfl) ⟨4531709, by rfl⟩ : syracuseStep 24169117 = 9063419) B9063419
theorem B805615 : Blo 802343 805615 := bstep (se 1 (by rfl) ⟨604211, by rfl⟩ : syracuseStep 805615 = 1208423) B1208423
theorem B805919 : Blo 802343 805919 := bstep (se 1 (by rfl) ⟨604439, by rfl⟩ : syracuseStep 805919 = 1208879) B1208879
theorem B7326845 : Blo 802343 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B1526921 : Blo 802343 1526921 := bstep (se 2 (by rfl) ⟨572595, by rfl⟩ : syracuseStep 1526921 = 1145191) B1145191
theorem B5164327 : Blo 802343 5164327 := bstep (se 1 (by rfl) ⟨3873245, by rfl⟩ : syracuseStep 5164327 = 7746491) B7746491
theorem B806191 : Blo 802343 806191 := bstep (se 1 (by rfl) ⟨604643, by rfl⟩ : syracuseStep 806191 = 1209287) B1209287
theorem B9917407 : Blo 802343 9917407 := bstep (se 1 (by rfl) ⟨7438055, by rfl⟩ : syracuseStep 9917407 = 14876111) B14876111
theorem B906367 : Blo 802343 906367 := bstep (se 1 (by rfl) ⟨679775, by rfl⟩ : syracuseStep 906367 = 1359551) B1359551
theorem B6510131 : Blo 802343 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B11032307 : Blo 802343 11032307 := bstep (se 1 (by rfl) ⟨8274230, by rfl⟩ : syracuseStep 11032307 = 16548461) B16548461
theorem B2578463 : Blo 802343 2578463 := bstep (se 1 (by rfl) ⟨1933847, by rfl⟩ : syracuseStep 2578463 = 3867695) B3867695
theorem B7723117 : Blo 802343 7723117 := bstep (se 3 (by rfl) ⟨1448084, by rfl⟩ : syracuseStep 7723117 = 2896169) B2896169
theorem B9164987 : Blo 802343 9164987 := bstep (se 1 (by rfl) ⟨6873740, by rfl⟩ : syracuseStep 9164987 = 13747481) B13747481
theorem B2709719 : Blo 802343 2709719 := bstep (se 1 (by rfl) ⟨2032289, by rfl⟩ : syracuseStep 2709719 = 4064579) B4064579
theorem B1203743 : Blo 802343 1203743 := bstep (se 1 (by rfl) ⟨902807, by rfl⟩ : syracuseStep 1203743 = 1805615) B1805615
theorem B21225671 : Blo 802343 21225671 := bstep (se 1 (by rfl) ⟨15919253, by rfl⟩ : syracuseStep 21225671 = 31838507) B31838507
theorem B2711879 : Blo 802343 2711879 := bstep (se 1 (by rfl) ⟨2033909, by rfl⟩ : syracuseStep 2711879 = 4067819) B4067819
theorem B1204559 : Blo 802343 1204559 := bstep (se 1 (by rfl) ⟨903419, by rfl⟩ : syracuseStep 1204559 = 1806839) B1806839
theorem B1205129 : Blo 802343 1205129 := bstep (se 2 (by rfl) ⟨451923, by rfl⟩ : syracuseStep 1205129 = 903847) B903847
theorem B4580489 : Blo 802343 4580489 := bstep (se 2 (by rfl) ⟨1717683, by rfl⟩ : syracuseStep 4580489 = 3435367) B3435367
theorem B1205531 : Blo 802343 1205531 := bstep (se 1 (by rfl) ⟨904148, by rfl⟩ : syracuseStep 1205531 = 1808297) B1808297
theorem B4580671 : Blo 802343 4580671 := bstep (se 1 (by rfl) ⟨3435503, by rfl⟩ : syracuseStep 4580671 = 6871007) B6871007
theorem B1205663 : Blo 802343 1205663 := bstep (se 1 (by rfl) ⟨904247, by rfl⟩ : syracuseStep 1205663 = 1808495) B1808495
theorem B2713391 : Blo 802343 2713391 := bstep (se 1 (by rfl) ⟨2035043, by rfl⟩ : syracuseStep 2713391 = 4070087) B4070087
theorem B10315943 : Blo 802343 10315943 := bstep (se 1 (by rfl) ⟨7736957, by rfl⟩ : syracuseStep 10315943 = 15473915) B15473915
theorem B1206503 : Blo 802343 1206503 := bstep (se 1 (by rfl) ⟨904877, by rfl⟩ : syracuseStep 1206503 = 1809755) B1809755
theorem B2288047 : Blo 802343 2288047 := bstep (se 1 (by rfl) ⟨1716035, by rfl⟩ : syracuseStep 2288047 = 3432071) B3432071
theorem B1206761 : Blo 802343 1206761 := bstep (se 2 (by rfl) ⟨452535, by rfl⟩ : syracuseStep 1206761 = 905071) B905071
theorem B1207391 : Blo 802343 1207391 := bstep (se 1 (by rfl) ⟨905543, by rfl⟩ : syracuseStep 1207391 = 1811087) B1811087
theorem B1207835 : Blo 802343 1207835 := bstep (se 1 (by rfl) ⟨905876, by rfl⟩ : syracuseStep 1207835 = 1811753) B1811753
theorem B6123113 : Blo 802343 6123113 := bstep (se 2 (by rfl) ⟨2296167, by rfl⟩ : syracuseStep 6123113 = 4592335) B4592335
theorem B10284731 : Blo 802343 10284731 := bstep (se 1 (by rfl) ⟨7713548, by rfl⟩ : syracuseStep 10284731 = 15427097) B15427097
theorem B1208543 : Blo 802343 1208543 := bstep (se 1 (by rfl) ⟨906407, by rfl⟩ : syracuseStep 1208543 = 1812815) B1812815
theorem B112783589 : Blo 802343 112783589 := bstep (se 4 (by rfl) ⟨10573461, by rfl⟩ : syracuseStep 112783589 = 21146923) B21146923
theorem B1208735 : Blo 802343 1208735 := bstep (se 1 (by rfl) ⟨906551, by rfl⟩ : syracuseStep 1208735 = 1813103) B1813103
theorem B1569215 : Blo 802343 1569215 := bstep (se 1 (by rfl) ⟨1176911, by rfl⟩ : syracuseStep 1569215 = 2353823) B2353823
theorem B10285703 : Blo 802343 10285703 := bstep (se 1 (by rfl) ⟨7714277, by rfl⟩ : syracuseStep 10285703 = 15428555) B15428555
theorem B1208999 : Blo 802343 1208999 := bstep (se 1 (by rfl) ⟨906749, by rfl⟩ : syracuseStep 1208999 = 1813499) B1813499
theorem B2716793 : Blo 802343 2716793 := bstep (se 2 (by rfl) ⟨1018797, by rfl⟩ : syracuseStep 2716793 = 2037595) B2037595
theorem B13563227 : Blo 802343 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B39122423 : Blo 802343 39122423 := bstep (se 1 (by rfl) ⟨29341817, by rfl⟩ : syracuseStep 39122423 = 58683635) B58683635
theorem B2717819 : Blo 802343 2717819 := bstep (se 1 (by rfl) ⟨2038364, by rfl⟩ : syracuseStep 2717819 = 4076729) B4076729
theorem B2717927 : Blo 802343 2717927 := bstep (se 1 (by rfl) ⟨2038445, by rfl⟩ : syracuseStep 2717927 = 4076891) B4076891
theorem B95320313 : Blo 802343 95320313 := bstep (se 2 (by rfl) ⟨35745117, by rfl⟩ : syracuseStep 95320313 = 71490235) B71490235
theorem B1931617 : Blo 802343 1931617 := bstep (se 2 (by rfl) ⟨724356, by rfl⟩ : syracuseStep 1931617 = 1448713) B1448713
theorem B4291553 : Blo 802343 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B1146091 : Blo 802343 1146091 := bstep (se 1 (by rfl) ⟨859568, by rfl⟩ : syracuseStep 1146091 = 1719137) B1719137
theorem B22052341 : Blo 802343 22052341 := bstep (se 5 (by rfl) ⟨1033703, by rfl⟩ : syracuseStep 22052341 = 2067407) B2067407
theorem B5144417 : Blo 802343 5144417 := bstep (se 2 (by rfl) ⟨1929156, by rfl⟩ : syracuseStep 5144417 = 3858313) B3858313
theorem B1015679 : Blo 802343 1015679 := bstep (se 1 (by rfl) ⟨761759, by rfl⟩ : syracuseStep 1015679 = 1523519) B1523519
theorem B1933183 : Blo 802343 1933183 := bstep (se 1 (by rfl) ⟨1449887, by rfl⟩ : syracuseStep 1933183 = 2899775) B2899775
theorem B1933625 : Blo 802343 1933625 := bstep (se 2 (by rfl) ⟨725109, by rfl⟩ : syracuseStep 1933625 = 1450219) B1450219
theorem B8258557 : Blo 802343 8258557 := bstep (se 3 (by rfl) ⟨1548479, by rfl⟩ : syracuseStep 8258557 = 3096959) B3096959
theorem B4064255 : Blo 802343 4064255 := bstep (se 1 (by rfl) ⟨3048191, by rfl⟩ : syracuseStep 4064255 = 6096383) B6096383
theorem B4884563 : Blo 802343 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B1017947 : Blo 802343 1017947 := bstep (se 1 (by rfl) ⟨763460, by rfl⟩ : syracuseStep 1017947 = 1526921) B1526921
theorem B1805417 : Blo 802343 1805417 := bstep (se 2 (by rfl) ⟨677031, by rfl⟩ : syracuseStep 1805417 = 1354063) B1354063
theorem B3050729 : Blo 802343 3050729 := bstep (se 2 (by rfl) ⟨1144023, by rfl⟩ : syracuseStep 3050729 = 2288047) B2288047
theorem B2035439 : Blo 802343 2035439 := bstep (se 1 (by rfl) ⟨1526579, by rfl⟩ : syracuseStep 2035439 = 3053159) B3053159
theorem B1806479 : Blo 802343 1806479 := bstep (se 1 (by rfl) ⟨1354859, by rfl⟩ : syracuseStep 1806479 = 2709719) B2709719
theorem B2035955 : Blo 802343 2035955 := bstep (se 1 (by rfl) ⟨1526966, by rfl⟩ : syracuseStep 2035955 = 3053933) B3053933
theorem B6885769 : Blo 802343 6885769 := bstep (se 2 (by rfl) ⟨2582163, by rfl⟩ : syracuseStep 6885769 = 5164327) B5164327
theorem B1807073 : Blo 802343 1807073 := bstep (se 2 (by rfl) ⟨677652, by rfl⟩ : syracuseStep 1807073 = 1355305) B1355305
theorem B52892837 : Blo 802343 52892837 := bstep (se 4 (by rfl) ⟨4958703, by rfl⟩ : syracuseStep 52892837 = 9917407) B9917407
theorem B4068791 : Blo 802343 4068791 := bstep (se 1 (by rfl) ⟨3051593, by rfl⟩ : syracuseStep 4068791 = 6103187) B6103187
theorem B1807919 : Blo 802343 1807919 := bstep (se 1 (by rfl) ⟨1355939, by rfl⟩ : syracuseStep 1807919 = 2711879) B2711879
theorem B2037575 : Blo 802343 2037575 := bstep (se 1 (by rfl) ⟨1528181, by rfl⟩ : syracuseStep 2037575 = 3056363) B3056363
theorem B3872767 : Blo 802343 3872767 := bstep (se 1 (by rfl) ⟨2904575, by rfl⟩ : syracuseStep 3872767 = 5809151) B5809151
theorem B6952979 : Blo 802343 6952979 := bstep (se 1 (by rfl) ⟨5214734, by rfl⟩ : syracuseStep 6952979 = 10429469) B10429469
theorem B3053659 : Blo 802343 3053659 := bstep (se 1 (by rfl) ⟨2290244, by rfl⟩ : syracuseStep 3053659 = 4580489) B4580489
theorem B1808927 : Blo 802343 1808927 := bstep (se 1 (by rfl) ⟨1356695, by rfl⟩ : syracuseStep 1808927 = 2713391) B2713391
theorem B17374247 : Blo 802343 17374247 := bstep (se 1 (by rfl) ⟨13030685, by rfl⟩ : syracuseStep 17374247 = 26061371) B26061371
theorem B4070735 : Blo 802343 4070735 := bstep (se 1 (by rfl) ⟨3053051, by rfl⟩ : syracuseStep 4070735 = 6106103) B6106103
theorem B2039195 : Blo 802343 2039195 := bstep (se 1 (by rfl) ⟨1529396, by rfl⟩ : syracuseStep 2039195 = 3058793) B3058793
theorem B6856487 : Blo 802343 6856487 := bstep (se 1 (by rfl) ⟨5142365, by rfl⟩ : syracuseStep 6856487 = 10284731) B10284731
theorem B11444141 : Blo 802343 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B10297489 : Blo 802343 10297489 := bstep (se 2 (by rfl) ⟨3861558, by rfl⟩ : syracuseStep 10297489 = 7723117) B7723117
theorem B1810601 : Blo 802343 1810601 := bstep (se 2 (by rfl) ⟨678975, by rfl⟩ : syracuseStep 1810601 = 1357951) B1357951
theorem B3088795 : Blo 802343 3088795 := bstep (se 1 (by rfl) ⟨2316596, by rfl⟩ : syracuseStep 3088795 = 4633193) B4633193
theorem B6857135 : Blo 802343 6857135 := bstep (se 1 (by rfl) ⟨5142851, by rfl⟩ : syracuseStep 6857135 = 10285703) B10285703
theorem B1811195 : Blo 802343 1811195 := bstep (se 1 (by rfl) ⟨1358396, by rfl⟩ : syracuseStep 1811195 = 2716793) B2716793
theorem B2040815 : Blo 802343 2040815 := bstep (se 1 (by rfl) ⟨1530611, by rfl⟩ : syracuseStep 2040815 = 3061223) B3061223
theorem B11150369 : Blo 802343 11150369 := bstep (se 2 (by rfl) ⟨4181388, by rfl⟩ : syracuseStep 11150369 = 8362777) B8362777
theorem B1811879 : Blo 802343 1811879 := bstep (se 1 (by rfl) ⟨1358909, by rfl⟩ : syracuseStep 1811879 = 2717819) B2717819
theorem B1811951 : Blo 802343 1811951 := bstep (se 1 (by rfl) ⟨1358963, by rfl⟩ : syracuseStep 1811951 = 2717927) B2717927
theorem B63546875 : Blo 802343 63546875 := bstep (se 1 (by rfl) ⟨47660156, by rfl⟩ : syracuseStep 63546875 = 95320313) B95320313
theorem B10462729 : Blo 802343 10462729 := bstep (se 2 (by rfl) ⟨3923523, by rfl⟩ : syracuseStep 10462729 = 7847047) B7847047
theorem B29403121 : Blo 802343 29403121 := bstep (se 2 (by rfl) ⟨11026170, by rfl⟩ : syracuseStep 29403121 = 22052341) B22052341
theorem B1812905 : Blo 802343 1812905 := bstep (se 2 (by rfl) ⟨679839, by rfl⟩ : syracuseStep 1812905 = 1359679) B1359679
theorem B4073975 : Blo 802343 4073975 := bstep (se 1 (by rfl) ⟨3055481, by rfl⟩ : syracuseStep 4073975 = 6110963) B6110963
theorem B1813679 : Blo 802343 1813679 := bstep (se 1 (by rfl) ⟨1360259, by rfl⟩ : syracuseStep 1813679 = 2720519) B2720519
theorem B26455747 : Blo 802343 26455747 := bstep (se 1 (by rfl) ⟨19841810, by rfl⟩ : syracuseStep 26455747 = 39683621) B39683621
theorem B6107561 : Blo 802343 6107561 := bstep (se 2 (by rfl) ⟨2290335, by rfl⟩ : syracuseStep 6107561 = 4580671) B4580671
theorem B1356203 : Blo 802343 1356203 := bstep (se 1 (by rfl) ⟨1017152, by rfl⟩ : syracuseStep 1356203 = 2034305) B2034305
theorem B7747721 : Blo 802343 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B32225489 : Blo 802343 32225489 := bstep (se 2 (by rfl) ⟨12084558, by rfl⟩ : syracuseStep 32225489 = 24169117) B24169117
theorem B4340087 : Blo 802343 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B7354871 : Blo 802343 7354871 := bstep (se 1 (by rfl) ⟨5516153, by rfl⟩ : syracuseStep 7354871 = 11032307) B11032307
theorem B1718975 : Blo 802343 1718975 := bstep (se 1 (by rfl) ⟨1289231, by rfl⟩ : syracuseStep 1718975 = 2578463) B2578463
theorem B6109991 : Blo 802343 6109991 := bstep (se 1 (by rfl) ⟨4582493, by rfl⟩ : syracuseStep 6109991 = 9164987) B9164987
theorem B1358761 : Blo 802343 1358761 := bstep (se 2 (by rfl) ⟨509535, by rfl⟩ : syracuseStep 1358761 = 1019071) B1019071
theorem B802495 : Blo 802343 802495 := bstep (se 1 (by rfl) ⟨601871, by rfl⟩ : syracuseStep 802495 = 1203743) B1203743
theorem B152584397 : Blo 802343 152584397 := bstep (se 3 (by rfl) ⟨28609574, by rfl⟩ : syracuseStep 152584397 = 57219149) B57219149
theorem B803039 : Blo 802343 803039 := bstep (se 1 (by rfl) ⟨602279, by rfl⟩ : syracuseStep 803039 = 1204559) B1204559
theorem B1360111 : Blo 802343 1360111 := bstep (se 1 (by rfl) ⟨1020083, by rfl⟩ : syracuseStep 1360111 = 2040167) B2040167
theorem B803419 : Blo 802343 803419 := bstep (se 1 (by rfl) ⟨602564, by rfl⟩ : syracuseStep 803419 = 1205129) B1205129
theorem B803687 : Blo 802343 803687 := bstep (se 1 (by rfl) ⟨602765, by rfl⟩ : syracuseStep 803687 = 1205531) B1205531
theorem B2573245 : Blo 802343 2573245 := bstep (se 3 (by rfl) ⟨482483, by rfl⟩ : syracuseStep 2573245 = 964967) B964967
theorem B803775 : Blo 802343 803775 := bstep (se 1 (by rfl) ⟨602831, by rfl⟩ : syracuseStep 803775 = 1205663) B1205663
theorem B12371381 : Blo 802343 12371381 := bstep (se 5 (by rfl) ⟨579908, by rfl⟩ : syracuseStep 12371381 = 1159817) B1159817
theorem B804335 : Blo 802343 804335 := bstep (se 1 (by rfl) ⟨603251, by rfl⟩ : syracuseStep 804335 = 1206503) B1206503
theorem B804507 : Blo 802343 804507 := bstep (se 1 (by rfl) ⟨603380, by rfl⟩ : syracuseStep 804507 = 1206761) B1206761
theorem B902983 : Blo 802343 902983 := bstep (se 1 (by rfl) ⟨677237, by rfl⟩ : syracuseStep 902983 = 1354475) B1354475
theorem B804927 : Blo 802343 804927 := bstep (se 1 (by rfl) ⟨603695, by rfl⟩ : syracuseStep 804927 = 1207391) B1207391
theorem B805223 : Blo 802343 805223 := bstep (se 1 (by rfl) ⟨603917, by rfl⟩ : syracuseStep 805223 = 1207835) B1207835
theorem B4082075 : Blo 802343 4082075 := bstep (se 1 (by rfl) ⟨3061556, by rfl⟩ : syracuseStep 4082075 = 6123113) B6123113
theorem B9816875 : Blo 802343 9816875 := bstep (se 1 (by rfl) ⟨7362656, by rfl⟩ : syracuseStep 9816875 = 14725313) B14725313
theorem B805695 : Blo 802343 805695 := bstep (se 1 (by rfl) ⟨604271, by rfl⟩ : syracuseStep 805695 = 1208543) B1208543
theorem B75189059 : Blo 802343 75189059 := bstep (se 1 (by rfl) ⟨56391794, by rfl⟩ : syracuseStep 75189059 = 112783589) B112783589
theorem B805823 : Blo 802343 805823 := bstep (se 1 (by rfl) ⟨604367, by rfl⟩ : syracuseStep 805823 = 1208735) B1208735
theorem B805999 : Blo 802343 805999 := bstep (se 1 (by rfl) ⟨604499, by rfl⟩ : syracuseStep 805999 = 1208999) B1208999
theorem B2575489 : Blo 802343 2575489 := bstep (se 2 (by rfl) ⟨965808, by rfl⟩ : syracuseStep 2575489 = 1931617) B1931617
theorem B13028609 : Blo 802343 13028609 := bstep (se 2 (by rfl) ⟨4885728, by rfl⟩ : syracuseStep 13028609 = 9771457) B9771457
theorem B904495 : Blo 802343 904495 := bstep (se 1 (by rfl) ⟨678371, by rfl⟩ : syracuseStep 904495 = 1356743) B1356743
theorem B1528121 : Blo 802343 1528121 := bstep (se 2 (by rfl) ⟨573045, by rfl⟩ : syracuseStep 1528121 = 1146091) B1146091
theorem B905755 : Blo 802343 905755 := bstep (se 1 (by rfl) ⟨679316, by rfl⟩ : syracuseStep 905755 = 1358633) B1358633
theorem B3265055 : Blo 802343 3265055 := bstep (se 1 (by rfl) ⟨2448791, by rfl⟩ : syracuseStep 3265055 = 4897583) B4897583
theorem B2708477 : Blo 802343 2708477 := bstep (se 3 (by rfl) ⟨507839, by rfl⟩ : syracuseStep 2708477 = 1015679) B1015679
theorem B906331 : Blo 802343 906331 := bstep (se 1 (by rfl) ⟨679748, by rfl⟩ : syracuseStep 906331 = 1359497) B1359497
theorem B2577577 : Blo 802343 2577577 := bstep (se 2 (by rfl) ⟨966591, by rfl⟩ : syracuseStep 2577577 = 1933183) B1933183
theorem B3429611 : Blo 802343 3429611 := bstep (se 1 (by rfl) ⟨2572208, by rfl⟩ : syracuseStep 3429611 = 5144417) B5144417
theorem B6510415 : Blo 802343 6510415 := bstep (se 1 (by rfl) ⟨4882811, by rfl⟩ : syracuseStep 6510415 = 9765623) B9765623
theorem B1204127 : Blo 802343 1204127 := bstep (se 1 (by rfl) ⟨903095, by rfl⟩ : syracuseStep 1204127 = 1806191) B1806191
theorem B2712311 : Blo 802343 2712311 := bstep (se 1 (by rfl) ⟨2034233, by rfl⟩ : syracuseStep 2712311 = 4068467) B4068467
theorem B1205063 : Blo 802343 1205063 := bstep (se 1 (by rfl) ⟨903797, by rfl⟩ : syracuseStep 1205063 = 1807595) B1807595
theorem B6350177 : Blo 802343 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B1205759 : Blo 802343 1205759 := bstep (se 1 (by rfl) ⟨904319, by rfl⟩ : syracuseStep 1205759 = 1808639) B1808639
theorem B14706755 : Blo 802343 14706755 := bstep (se 1 (by rfl) ⟨11030066, by rfl⟩ : syracuseStep 14706755 = 22060133) B22060133
theorem B1206479 : Blo 802343 1206479 := bstep (se 1 (by rfl) ⟨904859, by rfl⟩ : syracuseStep 1206479 = 1809719) B1809719
theorem B1206839 : Blo 802343 1206839 := bstep (se 1 (by rfl) ⟨905129, by rfl⟩ : syracuseStep 1206839 = 1810259) B1810259
theorem B2714255 : Blo 802343 2714255 := bstep (se 1 (by rfl) ⟨2035691, by rfl⟩ : syracuseStep 2714255 = 4071383) B4071383
theorem B14150447 : Blo 802343 14150447 := bstep (se 1 (by rfl) ⟨10612835, by rfl⟩ : syracuseStep 14150447 = 21225671) B21225671
theorem B2288969 : Blo 802343 2288969 := bstep (se 2 (by rfl) ⟨858363, by rfl⟩ : syracuseStep 2288969 = 1716727) B1716727
theorem B1207643 : Blo 802343 1207643 := bstep (se 1 (by rfl) ⟨905732, by rfl⟩ : syracuseStep 1207643 = 1811465) B1811465
theorem B1208039 : Blo 802343 1208039 := bstep (se 1 (by rfl) ⟨906029, by rfl⟩ : syracuseStep 1208039 = 1812059) B1812059
theorem B6877295 : Blo 802343 6877295 := bstep (se 1 (by rfl) ⟨5157971, by rfl⟩ : syracuseStep 6877295 = 10315943) B10315943
theorem B1208489 : Blo 802343 1208489 := bstep (se 2 (by rfl) ⟨453183, by rfl⟩ : syracuseStep 1208489 = 906367) B906367
theorem B1208807 : Blo 802343 1208807 := bstep (se 1 (by rfl) ⟨906605, by rfl⟩ : syracuseStep 1208807 = 1813211) B1813211
theorem B1208831 : Blo 802343 1208831 := bstep (se 1 (by rfl) ⟨906623, by rfl⟩ : syracuseStep 1208831 = 1813247) B1813247
theorem B2061127 : Blo 802343 2061127 := bstep (se 1 (by rfl) ⟨1545845, by rfl⟩ : syracuseStep 2061127 = 3091691) B3091691
theorem B2717225 : Blo 802343 2717225 := bstep (se 2 (by rfl) ⟨1018959, by rfl⟩ : syracuseStep 2717225 = 2037919) B2037919
theorem B1046143 : Blo 802343 1046143 := bstep (se 1 (by rfl) ⟨784607, by rfl⟩ : syracuseStep 1046143 = 1569215) B1569215
theorem B9042151 : Blo 802343 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B26081615 : Blo 802343 26081615 := bstep (se 1 (by rfl) ⟨19561211, by rfl⟩ : syracuseStep 26081615 = 39122423) B39122423
theorem B55769593 : Blo 802343 55769593 := bstep (se 2 (by rfl) ⟨20913597, by rfl⟩ : syracuseStep 55769593 = 41827195) B41827195
theorem B2718683 : Blo 802343 2718683 := bstep (se 1 (by rfl) ⟨2039012, by rfl⟩ : syracuseStep 2718683 = 4078025) B4078025
theorem B23559817 : Blo 802343 23559817 := bstep (se 2 (by rfl) ⟨8834931, by rfl⟩ : syracuseStep 23559817 = 17669863) B17669863
theorem B12353207 : Blo 802343 12353207 := bstep (se 1 (by rfl) ⟨9264905, by rfl⟩ : syracuseStep 12353207 = 18529811) B18529811
theorem B13729985 : Blo 802343 13729985 := bstep (se 2 (by rfl) ⟨5148744, by rfl⟩ : syracuseStep 13729985 = 10297489) B10297489
theorem B11011409 : Blo 802343 11011409 := bstep (se 2 (by rfl) ⟨4129278, by rfl⟩ : syracuseStep 11011409 = 8258557) B8258557
theorem B2721383 : Blo 802343 2721383 := bstep (se 1 (by rfl) ⟨2041037, by rfl⟩ : syracuseStep 2721383 = 4082075) B4082075
theorem B2033819 : Blo 802343 2033819 := bstep (se 1 (by rfl) ⟨1525364, by rfl⟩ : syracuseStep 2033819 = 3050729) B3050729
theorem B8685739 : Blo 802343 8685739 := bstep (se 1 (by rfl) ⟨6514304, by rfl⟩ : syracuseStep 8685739 = 13028609) B13028609
theorem B1018747 : Blo 802343 1018747 := bstep (se 1 (by rfl) ⟨764060, by rfl⟩ : syracuseStep 1018747 = 1528121) B1528121
theorem B1805651 : Blo 802343 1805651 := bstep (se 1 (by rfl) ⟨1354238, by rfl⟩ : syracuseStep 1805651 = 2708477) B2708477
theorem B35261891 : Blo 802343 35261891 := bstep (se 1 (by rfl) ⟨26446418, by rfl⟩ : syracuseStep 35261891 = 52892837) B52892837
theorem B1808207 : Blo 802343 1808207 := bstep (se 1 (by rfl) ⟨1356155, by rfl⟩ : syracuseStep 1808207 = 2712311) B2712311
theorem B9181025 : Blo 802343 9181025 := bstep (se 2 (by rfl) ⟨3442884, by rfl⟩ : syracuseStep 9181025 = 6885769) B6885769
theorem B9804503 : Blo 802343 9804503 := bstep (se 1 (by rfl) ⟨7353377, by rfl⟩ : syracuseStep 9804503 = 14706755) B14706755
theorem B1809503 : Blo 802343 1809503 := bstep (se 1 (by rfl) ⟨1357127, by rfl⟩ : syracuseStep 1809503 = 2714255) B2714255
theorem B4071545 : Blo 802343 4071545 := bstep (se 2 (by rfl) ⟨1526829, by rfl⟩ : syracuseStep 4071545 = 3053659) B3053659
theorem B4071707 : Blo 802343 4071707 := bstep (se 1 (by rfl) ⟨3053780, by rfl⟩ : syracuseStep 4071707 = 6107561) B6107561
theorem B74359457 : Blo 802343 74359457 := bstep (se 2 (by rfl) ⟨27884796, by rfl⟩ : syracuseStep 74359457 = 55769593) B55769593
theorem B1811483 : Blo 802343 1811483 := bstep (se 1 (by rfl) ⟨1358612, by rfl⟩ : syracuseStep 1811483 = 2717225) B2717225
theorem B1811681 : Blo 802343 1811681 := bstep (se 2 (by rfl) ⟨679380, by rfl⟩ : syracuseStep 1811681 = 1358761) B1358761
theorem B2893391 : Blo 802343 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B32941885 : Blo 802343 32941885 := bstep (se 3 (by rfl) ⟨6176603, by rfl⟩ : syracuseStep 32941885 = 12353207) B12353207
theorem B4073327 : Blo 802343 4073327 := bstep (se 1 (by rfl) ⟨3054995, by rfl⟩ : syracuseStep 4073327 = 6109991) B6109991
theorem B1812455 : Blo 802343 1812455 := bstep (se 1 (by rfl) ⟨1359341, by rfl⟩ : syracuseStep 1812455 = 2718683) B2718683
theorem B101722931 : Blo 802343 101722931 := bstep (se 1 (by rfl) ⟨76292198, by rfl⟩ : syracuseStep 101722931 = 152584397) B152584397
theorem B1289083 : Blo 802343 1289083 := bstep (se 1 (by rfl) ⟨966812, by rfl⟩ : syracuseStep 1289083 = 1933625) B1933625
theorem B1813481 : Blo 802343 1813481 := bstep (se 2 (by rfl) ⟨680055, by rfl⟩ : syracuseStep 1813481 = 1360111) B1360111
theorem B3256375 : Blo 802343 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B1356959 : Blo 802343 1356959 := bstep (se 1 (by rfl) ⟨1017719, by rfl⟩ : syracuseStep 1356959 = 2035439) B2035439
theorem B39204161 : Blo 802343 39204161 := bstep (se 2 (by rfl) ⟨14701560, by rfl⟩ : syracuseStep 39204161 = 29403121) B29403121
theorem B1357303 : Blo 802343 1357303 := bstep (se 1 (by rfl) ⟨1017977, by rfl⟩ : syracuseStep 1357303 = 2035955) B2035955
theorem B2176703 : Blo 802343 2176703 := bstep (se 1 (by rfl) ⟨1632527, by rfl⟩ : syracuseStep 2176703 = 3265055) B3265055
theorem B1358383 : Blo 802343 1358383 := bstep (se 1 (by rfl) ⟨1018787, by rfl⟩ : syracuseStep 1358383 = 2037575) B2037575
theorem B4635319 : Blo 802343 4635319 := bstep (se 1 (by rfl) ⟨3476489, by rfl⟩ : syracuseStep 4635319 = 6952979) B6952979
theorem B11582831 : Blo 802343 11582831 := bstep (se 1 (by rfl) ⟨8687123, by rfl⟩ : syracuseStep 11582831 = 17374247) B17374247
theorem B35274329 : Blo 802343 35274329 := bstep (se 2 (by rfl) ⟨13227873, by rfl⟩ : syracuseStep 35274329 = 26455747) B26455747
theorem B1359463 : Blo 802343 1359463 := bstep (se 1 (by rfl) ⟨1019597, by rfl⟩ : syracuseStep 1359463 = 2039195) B2039195
theorem B4570991 : Blo 802343 4570991 := bstep (se 1 (by rfl) ⟨3428243, by rfl⟩ : syracuseStep 4570991 = 6856487) B6856487
theorem B802751 : Blo 802343 802751 := bstep (se 1 (by rfl) ⟨602063, by rfl⟩ : syracuseStep 802751 = 1204127) B1204127
theorem B4571423 : Blo 802343 4571423 := bstep (se 1 (by rfl) ⟨3428567, by rfl⟩ : syracuseStep 4571423 = 6857135) B6857135
theorem B803375 : Blo 802343 803375 := bstep (se 1 (by rfl) ⟨602531, by rfl⟩ : syracuseStep 803375 = 1205063) B1205063
theorem B1360543 : Blo 802343 1360543 := bstep (se 1 (by rfl) ⟨1020407, by rfl⟩ : syracuseStep 1360543 = 2040815) B2040815
theorem B803839 : Blo 802343 803839 := bstep (se 1 (by rfl) ⟨602879, by rfl⟩ : syracuseStep 803839 = 1205759) B1205759
theorem B804319 : Blo 802343 804319 := bstep (se 1 (by rfl) ⟨603239, by rfl⟩ : syracuseStep 804319 = 1206479) B1206479
theorem B804559 : Blo 802343 804559 := bstep (se 1 (by rfl) ⟨603419, by rfl⟩ : syracuseStep 804559 = 1206839) B1206839
theorem B1394857 : Blo 802343 1394857 := bstep (se 2 (by rfl) ⟨523071, by rfl⟩ : syracuseStep 1394857 = 1046143) B1046143
theorem B1525979 : Blo 802343 1525979 := bstep (se 1 (by rfl) ⟨1144484, by rfl⟩ : syracuseStep 1525979 = 2288969) B2288969
theorem B805095 : Blo 802343 805095 := bstep (se 1 (by rfl) ⟨603821, by rfl⟩ : syracuseStep 805095 = 1207643) B1207643
theorem B805359 : Blo 802343 805359 := bstep (se 1 (by rfl) ⟨604019, by rfl⟩ : syracuseStep 805359 = 1208039) B1208039
theorem B5163689 : Blo 802343 5163689 := bstep (se 2 (by rfl) ⟨1936383, by rfl⟩ : syracuseStep 5163689 = 3872767) B3872767
theorem B805659 : Blo 802343 805659 := bstep (se 1 (by rfl) ⟨604244, by rfl⟩ : syracuseStep 805659 = 1208489) B1208489
theorem B904135 : Blo 802343 904135 := bstep (se 1 (by rfl) ⟨678101, by rfl⟩ : syracuseStep 904135 = 1356203) B1356203
theorem B805871 : Blo 802343 805871 := bstep (se 1 (by rfl) ⟨604403, by rfl⟩ : syracuseStep 805871 = 1208807) B1208807
theorem B805887 : Blo 802343 805887 := bstep (se 1 (by rfl) ⟨604415, by rfl⟩ : syracuseStep 805887 = 1208831) B1208831
theorem B5165147 : Blo 802343 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B21483659 : Blo 802343 21483659 := bstep (se 1 (by rfl) ⟨16112744, by rfl⟩ : syracuseStep 21483659 = 32225489) B32225489
theorem B17387743 : Blo 802343 17387743 := bstep (se 1 (by rfl) ⟨13040807, by rfl⟩ : syracuseStep 17387743 = 26081615) B26081615
theorem B4903247 : Blo 802343 4903247 := bstep (se 1 (by rfl) ⟨3677435, by rfl⟩ : syracuseStep 4903247 = 7354871) B7354871
theorem B31413089 : Blo 802343 31413089 := bstep (se 2 (by rfl) ⟨11779908, by rfl⟩ : syracuseStep 31413089 = 23559817) B23559817
theorem B4118393 : Blo 802343 4118393 := bstep (se 2 (by rfl) ⟨1544397, by rfl⟩ : syracuseStep 4118393 = 3088795) B3088795
theorem B2709503 : Blo 802343 2709503 := bstep (se 1 (by rfl) ⟨2032127, by rfl⟩ : syracuseStep 2709503 = 4064255) B4064255
theorem B8247587 : Blo 802343 8247587 := bstep (se 1 (by rfl) ⟨6185690, by rfl⟩ : syracuseStep 8247587 = 12371381) B12371381
theorem B3430993 : Blo 802343 3430993 := bstep (se 2 (by rfl) ⟨1286622, by rfl⟩ : syracuseStep 3430993 = 2573245) B2573245
theorem B6544583 : Blo 802343 6544583 := bstep (se 1 (by rfl) ⟨4908437, by rfl⟩ : syracuseStep 6544583 = 9816875) B9816875
theorem B50126039 : Blo 802343 50126039 := bstep (se 1 (by rfl) ⟨37594529, by rfl⟩ : syracuseStep 50126039 = 75189059) B75189059
theorem B13950305 : Blo 802343 13950305 := bstep (se 2 (by rfl) ⟨5231364, by rfl⟩ : syracuseStep 13950305 = 10462729) B10462729
theorem B1203611 : Blo 802343 1203611 := bstep (se 1 (by rfl) ⟨902708, by rfl⟩ : syracuseStep 1203611 = 1805417) B1805417
theorem B1203977 : Blo 802343 1203977 := bstep (se 2 (by rfl) ⟨451491, by rfl⟩ : syracuseStep 1203977 = 902983) B902983
theorem B1204319 : Blo 802343 1204319 := bstep (se 1 (by rfl) ⟨903239, by rfl⟩ : syracuseStep 1204319 = 1806479) B1806479
theorem B1204715 : Blo 802343 1204715 := bstep (se 1 (by rfl) ⟨903536, by rfl⟩ : syracuseStep 1204715 = 1807073) B1807073
theorem B2286407 : Blo 802343 2286407 := bstep (se 1 (by rfl) ⟨1714805, by rfl⟩ : syracuseStep 2286407 = 3429611) B3429611
theorem B16933805 : Blo 802343 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B2712527 : Blo 802343 2712527 := bstep (se 1 (by rfl) ⟨2034395, by rfl⟩ : syracuseStep 2712527 = 4068791) B4068791
theorem B1205279 : Blo 802343 1205279 := bstep (se 1 (by rfl) ⟨903959, by rfl⟩ : syracuseStep 1205279 = 1807919) B1807919
theorem B3433985 : Blo 802343 3433985 := bstep (se 2 (by rfl) ⟨1287744, by rfl⟩ : syracuseStep 3433985 = 2575489) B2575489
theorem B1205951 : Blo 802343 1205951 := bstep (se 1 (by rfl) ⟨904463, by rfl⟩ : syracuseStep 1205951 = 1808927) B1808927
theorem B1205993 : Blo 802343 1205993 := bstep (se 2 (by rfl) ⟨452247, by rfl⟩ : syracuseStep 1205993 = 904495) B904495
theorem B2713823 : Blo 802343 2713823 := bstep (se 1 (by rfl) ⟨2035367, by rfl⟩ : syracuseStep 2713823 = 4070735) B4070735
theorem B7629427 : Blo 802343 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B1207067 : Blo 802343 1207067 := bstep (se 1 (by rfl) ⟨905300, by rfl⟩ : syracuseStep 1207067 = 1810601) B1810601
theorem B2714525 : Blo 802343 2714525 := bstep (se 3 (by rfl) ⟨508973, by rfl⟩ : syracuseStep 2714525 = 1017947) B1017947
theorem B1207463 : Blo 802343 1207463 := bstep (se 1 (by rfl) ⟨905597, by rfl⟩ : syracuseStep 1207463 = 1811195) B1811195
theorem B7433579 : Blo 802343 7433579 := bstep (se 1 (by rfl) ⟨5575184, by rfl⟩ : syracuseStep 7433579 = 11150369) B11150369
theorem B1207673 : Blo 802343 1207673 := bstep (se 2 (by rfl) ⟨452877, by rfl⟩ : syracuseStep 1207673 = 905755) B905755
theorem B1207919 : Blo 802343 1207919 := bstep (se 1 (by rfl) ⟨905939, by rfl⟩ : syracuseStep 1207919 = 1811879) B1811879
theorem B1207967 : Blo 802343 1207967 := bstep (se 1 (by rfl) ⟨905975, by rfl⟩ : syracuseStep 1207967 = 1811951) B1811951
theorem B42364583 : Blo 802343 42364583 := bstep (se 1 (by rfl) ⟨31773437, by rfl⟩ : syracuseStep 42364583 = 63546875) B63546875
theorem B2748169 : Blo 802343 2748169 := bstep (se 2 (by rfl) ⟨1030563, by rfl⟩ : syracuseStep 2748169 = 2061127) B2061127
theorem B1208441 : Blo 802343 1208441 := bstep (se 2 (by rfl) ⟨453165, by rfl⟩ : syracuseStep 1208441 = 906331) B906331
theorem B3436769 : Blo 802343 3436769 := bstep (se 2 (by rfl) ⟨1288788, by rfl⟩ : syracuseStep 3436769 = 2577577) B2577577
theorem B1208603 : Blo 802343 1208603 := bstep (se 1 (by rfl) ⟨906452, by rfl⟩ : syracuseStep 1208603 = 1812905) B1812905
theorem B2715983 : Blo 802343 2715983 := bstep (se 1 (by rfl) ⟨2036987, by rfl⟩ : syracuseStep 2715983 = 4073975) B4073975
theorem B9433631 : Blo 802343 9433631 := bstep (se 1 (by rfl) ⟨7075223, by rfl⟩ : syracuseStep 9433631 = 14150447) B14150447
theorem B1209119 : Blo 802343 1209119 := bstep (se 1 (by rfl) ⟨906839, by rfl⟩ : syracuseStep 1209119 = 1813679) B1813679
theorem B8680553 : Blo 802343 8680553 := bstep (se 2 (by rfl) ⟨3255207, by rfl⟩ : syracuseStep 8680553 = 6510415) B6510415
theorem B4584863 : Blo 802343 4584863 := bstep (se 1 (by rfl) ⟨3438647, by rfl⟩ : syracuseStep 4584863 = 6877295) B6877295
theorem B12056201 : Blo 802343 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B1145983 : Blo 802343 1145983 := bstep (se 1 (by rfl) ⟨859487, by rfl⟩ : syracuseStep 1145983 = 1718975) B1718975
theorem B3047615 : Blo 802343 3047615 := bstep (se 1 (by rfl) ⟨2285711, by rfl⟩ : syracuseStep 3047615 = 4571423) B4571423
theorem B7340939 : Blo 802343 7340939 := bstep (se 1 (by rfl) ⟨5505704, by rfl⟩ : syracuseStep 7340939 = 11011409) B11011409
theorem B3442459 : Blo 802343 3442459 := bstep (se 1 (by rfl) ⟨2581844, by rfl⟩ : syracuseStep 3442459 = 5163689) B5163689
theorem B14322439 : Blo 802343 14322439 := bstep (se 1 (by rfl) ⟨10741829, by rfl⟩ : syracuseStep 14322439 = 21483659) B21483659
theorem B20942059 : Blo 802343 20942059 := bstep (se 1 (by rfl) ⟨15706544, by rfl⟩ : syracuseStep 20942059 = 31413089) B31413089
theorem B1806335 : Blo 802343 1806335 := bstep (se 1 (by rfl) ⟨1354751, by rfl⟩ : syracuseStep 1806335 = 2709503) B2709503
theorem B4363055 : Blo 802343 4363055 := bstep (se 1 (by rfl) ⟨3272291, by rfl⟩ : syracuseStep 4363055 = 6544583) B6544583
theorem B4069277 : Blo 802343 4069277 := bstep (se 3 (by rfl) ⟨762989, by rfl⟩ : syracuseStep 4069277 = 1525979) B1525979
theorem B1808351 : Blo 802343 1808351 := bstep (se 1 (by rfl) ⟨1356263, by rfl⟩ : syracuseStep 1808351 = 2712527) B2712527
theorem B21993565 : Blo 802343 21993565 := bstep (se 3 (by rfl) ⟨4123793, by rfl⟩ : syracuseStep 21993565 = 8247587) B8247587
theorem B1809215 : Blo 802343 1809215 := bstep (se 1 (by rfl) ⟨1356911, by rfl⟩ : syracuseStep 1809215 = 2713823) B2713823
theorem B1809683 : Blo 802343 1809683 := bstep (se 1 (by rfl) ⟨1357262, by rfl⟩ : syracuseStep 1809683 = 2714525) B2714525
theorem B1809737 : Blo 802343 1809737 := bstep (se 2 (by rfl) ⟨678651, by rfl⟩ : syracuseStep 1809737 = 1357303) B1357303
theorem B1810655 : Blo 802343 1810655 := bstep (se 1 (by rfl) ⟨1357991, by rfl⟩ : syracuseStep 1810655 = 2715983) B2715983
theorem B1811177 : Blo 802343 1811177 := bstep (se 2 (by rfl) ⟨679191, by rfl⟩ : syracuseStep 1811177 = 1358383) B1358383
theorem B3056575 : Blo 802343 3056575 := bstep (se 1 (by rfl) ⟨2292431, by rfl⟩ : syracuseStep 3056575 = 4584863) B4584863
theorem B8037467 : Blo 802343 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B1451135 : Blo 802343 1451135 := bstep (se 1 (by rfl) ⟨1088351, by rfl⟩ : syracuseStep 1451135 = 2176703) B2176703
theorem B1812617 : Blo 802343 1812617 := bstep (se 2 (by rfl) ⟨679731, by rfl⟩ : syracuseStep 1812617 = 1359463) B1359463
theorem B9153323 : Blo 802343 9153323 := bstep (se 1 (by rfl) ⟨6864992, by rfl⟩ : syracuseStep 9153323 = 13729985) B13729985
theorem B13773725 : Blo 802343 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B1814057 : Blo 802343 1814057 := bstep (se 2 (by rfl) ⟨680271, by rfl⟩ : syracuseStep 1814057 = 1360543) B1360543
theorem B1814255 : Blo 802343 1814255 := bstep (se 1 (by rfl) ⟨1360691, by rfl⟩ : syracuseStep 1814255 = 2721383) B2721383
theorem B1355879 : Blo 802343 1355879 := bstep (se 1 (by rfl) ⟨1016909, by rfl⟩ : syracuseStep 1355879 = 2033819) B2033819
theorem B23507927 : Blo 802343 23507927 := bstep (se 1 (by rfl) ⟨17630945, by rfl⟩ : syracuseStep 23507927 = 35261891) B35261891
theorem B43922513 : Blo 802343 43922513 := bstep (se 2 (by rfl) ⟨16470942, by rfl⟩ : syracuseStep 43922513 = 32941885) B32941885
theorem B11580985 : Blo 802343 11580985 := bstep (se 2 (by rfl) ⟨4342869, by rfl⟩ : syracuseStep 11580985 = 8685739) B8685739
theorem B10172569 : Blo 802343 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B1718777 : Blo 802343 1718777 := bstep (se 2 (by rfl) ⟨644541, by rfl⟩ : syracuseStep 1718777 = 1289083) B1289083
theorem B1358329 : Blo 802343 1358329 := bstep (se 2 (by rfl) ⟨509373, by rfl⟩ : syracuseStep 1358329 = 1018747) B1018747
theorem B6536335 : Blo 802343 6536335 := bstep (se 1 (by rfl) ⟨4902251, by rfl⟩ : syracuseStep 6536335 = 9804503) B9804503
theorem B802407 : Blo 802343 802407 := bstep (se 1 (by rfl) ⟨601805, by rfl⟩ : syracuseStep 802407 = 1203611) B1203611
theorem B802651 : Blo 802343 802651 := bstep (se 1 (by rfl) ⟨601988, by rfl⟩ : syracuseStep 802651 = 1203977) B1203977
theorem B802879 : Blo 802343 802879 := bstep (se 1 (by rfl) ⟨602159, by rfl⟩ : syracuseStep 802879 = 1204319) B1204319
theorem B4341833 : Blo 802343 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B23183657 : Blo 802343 23183657 := bstep (se 2 (by rfl) ⟨8693871, by rfl⟩ : syracuseStep 23183657 = 17387743) B17387743
theorem B803143 : Blo 802343 803143 := bstep (se 1 (by rfl) ⟨602357, by rfl⟩ : syracuseStep 803143 = 1204715) B1204715
theorem B1524271 : Blo 802343 1524271 := bstep (se 1 (by rfl) ⟨1143203, by rfl⟩ : syracuseStep 1524271 = 2286407) B2286407
theorem B11289203 : Blo 802343 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B803519 : Blo 802343 803519 := bstep (se 1 (by rfl) ⟨602639, by rfl⟩ : syracuseStep 803519 = 1205279) B1205279
theorem B803967 : Blo 802343 803967 := bstep (se 1 (by rfl) ⟨602975, by rfl⟩ : syracuseStep 803967 = 1205951) B1205951
theorem B803995 : Blo 802343 803995 := bstep (se 1 (by rfl) ⟨602996, by rfl⟩ : syracuseStep 803995 = 1205993) B1205993
theorem B804711 : Blo 802343 804711 := bstep (se 1 (by rfl) ⟨603533, by rfl⟩ : syracuseStep 804711 = 1207067) B1207067
theorem B67815287 : Blo 802343 67815287 := bstep (se 1 (by rfl) ⟨50861465, by rfl⟩ : syracuseStep 67815287 = 101722931) B101722931
theorem B804975 : Blo 802343 804975 := bstep (se 1 (by rfl) ⟨603731, by rfl⟩ : syracuseStep 804975 = 1207463) B1207463
theorem B805115 : Blo 802343 805115 := bstep (se 1 (by rfl) ⟨603836, by rfl⟩ : syracuseStep 805115 = 1207673) B1207673
theorem B805279 : Blo 802343 805279 := bstep (se 1 (by rfl) ⟨603959, by rfl⟩ : syracuseStep 805279 = 1207919) B1207919
theorem B805311 : Blo 802343 805311 := bstep (se 1 (by rfl) ⟨603983, by rfl⟩ : syracuseStep 805311 = 1207967) B1207967
theorem B805627 : Blo 802343 805627 := bstep (se 1 (by rfl) ⟨604220, by rfl⟩ : syracuseStep 805627 = 1208441) B1208441
theorem B805735 : Blo 802343 805735 := bstep (se 1 (by rfl) ⟨604301, by rfl⟩ : syracuseStep 805735 = 1208603) B1208603
theorem B806079 : Blo 802343 806079 := bstep (se 1 (by rfl) ⟨604559, by rfl⟩ : syracuseStep 806079 = 1209119) B1209119
theorem B5787035 : Blo 802343 5787035 := bstep (se 1 (by rfl) ⟨4340276, by rfl⟩ : syracuseStep 5787035 = 8680553) B8680553
theorem B904639 : Blo 802343 904639 := bstep (se 1 (by rfl) ⟨678479, by rfl⟩ : syracuseStep 904639 = 1356959) B1356959
theorem B4574657 : Blo 802343 4574657 := bstep (se 2 (by rfl) ⟨1715496, by rfl⟩ : syracuseStep 4574657 = 3430993) B3430993
theorem B26136107 : Blo 802343 26136107 := bstep (se 1 (by rfl) ⟨19602080, by rfl⟩ : syracuseStep 26136107 = 39204161) B39204161
theorem B6180425 : Blo 802343 6180425 := bstep (se 2 (by rfl) ⟨2317659, by rfl⟩ : syracuseStep 6180425 = 4635319) B4635319
theorem B1527977 : Blo 802343 1527977 := bstep (se 2 (by rfl) ⟨572991, by rfl⟩ : syracuseStep 1527977 = 1145983) B1145983
theorem B7721887 : Blo 802343 7721887 := bstep (se 1 (by rfl) ⟨5791415, by rfl⟩ : syracuseStep 7721887 = 11582831) B11582831
theorem B23516219 : Blo 802343 23516219 := bstep (se 1 (by rfl) ⟨17637164, by rfl⟩ : syracuseStep 23516219 = 35274329) B35274329
theorem B25156349 : Blo 802343 25156349 := bstep (se 3 (by rfl) ⟨4716815, by rfl⟩ : syracuseStep 25156349 = 9433631) B9433631
theorem B1203767 : Blo 802343 1203767 := bstep (se 1 (by rfl) ⟨902825, by rfl⟩ : syracuseStep 1203767 = 1805651) B1805651
theorem B3268831 : Blo 802343 3268831 := bstep (se 1 (by rfl) ⟨2451623, by rfl⟩ : syracuseStep 3268831 = 4903247) B4903247
theorem B1859809 : Blo 802343 1859809 := bstep (se 2 (by rfl) ⟨697428, by rfl⟩ : syracuseStep 1859809 = 1394857) B1394857
theorem B1205471 : Blo 802343 1205471 := bstep (se 1 (by rfl) ⟨904103, by rfl⟩ : syracuseStep 1205471 = 1808207) B1808207
theorem B6120683 : Blo 802343 6120683 := bstep (se 1 (by rfl) ⟨4590512, by rfl⟩ : syracuseStep 6120683 = 9181025) B9181025
theorem B2745595 : Blo 802343 2745595 := bstep (se 1 (by rfl) ⟨2059196, by rfl⟩ : syracuseStep 2745595 = 4118393) B4118393
theorem B1205513 : Blo 802343 1205513 := bstep (se 2 (by rfl) ⟨452067, by rfl⟩ : syracuseStep 1205513 = 904135) B904135
theorem B1206335 : Blo 802343 1206335 := bstep (se 1 (by rfl) ⟨904751, by rfl⟩ : syracuseStep 1206335 = 1809503) B1809503
theorem B33417359 : Blo 802343 33417359 := bstep (se 1 (by rfl) ⟨25063019, by rfl⟩ : syracuseStep 33417359 = 50126039) B50126039
theorem B9300203 : Blo 802343 9300203 := bstep (se 1 (by rfl) ⟨6975152, by rfl⟩ : syracuseStep 9300203 = 13950305) B13950305
theorem B3664225 : Blo 802343 3664225 := bstep (se 2 (by rfl) ⟨1374084, by rfl⟩ : syracuseStep 3664225 = 2748169) B2748169
theorem B2714363 : Blo 802343 2714363 := bstep (se 1 (by rfl) ⟨2035772, by rfl⟩ : syracuseStep 2714363 = 4071545) B4071545
theorem B2714471 : Blo 802343 2714471 := bstep (se 1 (by rfl) ⟨2035853, by rfl⟩ : syracuseStep 2714471 = 4071707) B4071707
theorem B49572971 : Blo 802343 49572971 := bstep (se 1 (by rfl) ⟨37179728, by rfl⟩ : syracuseStep 49572971 = 74359457) B74359457
theorem B1207655 : Blo 802343 1207655 := bstep (se 1 (by rfl) ⟨905741, by rfl⟩ : syracuseStep 1207655 = 1811483) B1811483
theorem B1207787 : Blo 802343 1207787 := bstep (se 1 (by rfl) ⟨905840, by rfl⟩ : syracuseStep 1207787 = 1811681) B1811681
theorem B2289323 : Blo 802343 2289323 := bstep (se 1 (by rfl) ⟨1716992, by rfl⟩ : syracuseStep 2289323 = 3433985) B3433985
theorem B1928927 : Blo 802343 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B2715551 : Blo 802343 2715551 := bstep (se 1 (by rfl) ⟨2036663, by rfl⟩ : syracuseStep 2715551 = 4073327) B4073327
theorem B1208303 : Blo 802343 1208303 := bstep (se 1 (by rfl) ⟨906227, by rfl⟩ : syracuseStep 1208303 = 1812455) B1812455
theorem B1208987 : Blo 802343 1208987 := bstep (se 1 (by rfl) ⟨906740, by rfl⟩ : syracuseStep 1208987 = 1813481) B1813481
theorem B28243055 : Blo 802343 28243055 := bstep (se 1 (by rfl) ⟨21182291, by rfl⟩ : syracuseStep 28243055 = 42364583) B42364583
theorem B2291179 : Blo 802343 2291179 := bstep (se 1 (by rfl) ⟨1718384, by rfl⟩ : syracuseStep 2291179 = 3436769) B3436769
theorem B19822877 : Blo 802343 19822877 := bstep (se 3 (by rfl) ⟨3716789, by rfl⟩ : syracuseStep 19822877 = 7433579) B7433579
theorem B3047327 : Blo 802343 3047327 := bstep (se 1 (by rfl) ⟨2285495, by rfl⟩ : syracuseStep 3047327 = 4570991) B4570991
theorem B2031743 : Blo 802343 2031743 := bstep (se 1 (by rfl) ⟨1523807, by rfl⟩ : syracuseStep 2031743 = 3047615) B3047615
theorem B4358441 : Blo 802343 4358441 := bstep (se 2 (by rfl) ⟨1634415, by rfl⟩ : syracuseStep 4358441 = 3268831) B3268831
theorem B2032361 : Blo 802343 2032361 := bstep (se 2 (by rfl) ⟨762135, by rfl⟩ : syracuseStep 2032361 = 1524271) B1524271
theorem B3049771 : Blo 802343 3049771 := bstep (se 1 (by rfl) ⟨2287328, by rfl⟩ : syracuseStep 3049771 = 4574657) B4574657
theorem B4589945 : Blo 802343 4589945 := bstep (se 2 (by rfl) ⟨1721229, by rfl⟩ : syracuseStep 4589945 = 3442459) B3442459
theorem B1018651 : Blo 802343 1018651 := bstep (se 1 (by rfl) ⟨763988, by rfl⟩ : syracuseStep 1018651 = 1527977) B1527977
theorem B3869693 : Blo 802343 3869693 := bstep (se 3 (by rfl) ⟨725567, by rfl⟩ : syracuseStep 3869693 = 1451135) B1451135
theorem B4885633 : Blo 802343 4885633 := bstep (se 2 (by rfl) ⟨1832112, by rfl⟩ : syracuseStep 4885633 = 3664225) B3664225
theorem B76386341 : Blo 802343 76386341 := bstep (se 4 (by rfl) ⟨7161219, by rfl⟩ : syracuseStep 76386341 = 14322439) B14322439
theorem B27922745 : Blo 802343 27922745 := bstep (se 2 (by rfl) ⟨10471029, by rfl⟩ : syracuseStep 27922745 = 20942059) B20942059
theorem B10295849 : Blo 802343 10295849 := bstep (se 2 (by rfl) ⟨3860943, by rfl⟩ : syracuseStep 10295849 = 7721887) B7721887
theorem B6200135 : Blo 802343 6200135 := bstep (se 1 (by rfl) ⟨4650101, by rfl⟩ : syracuseStep 6200135 = 9300203) B9300203
theorem B1809575 : Blo 802343 1809575 := bstep (se 1 (by rfl) ⟨1357181, by rfl⟩ : syracuseStep 1809575 = 2714363) B2714363
theorem B6102215 : Blo 802343 6102215 := bstep (se 1 (by rfl) ⟨4576661, by rfl⟩ : syracuseStep 6102215 = 9153323) B9153323
theorem B1809647 : Blo 802343 1809647 := bstep (se 1 (by rfl) ⟨1357235, by rfl⟩ : syracuseStep 1809647 = 2714471) B2714471
theorem B9182483 : Blo 802343 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B3054905 : Blo 802343 3054905 := bstep (se 2 (by rfl) ⟨1145589, by rfl⟩ : syracuseStep 3054905 = 2291179) B2291179
theorem B15441313 : Blo 802343 15441313 := bstep (se 2 (by rfl) ⟨5790492, by rfl⟩ : syracuseStep 15441313 = 11580985) B11580985
theorem B1285951 : Blo 802343 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B1810367 : Blo 802343 1810367 := bstep (se 1 (by rfl) ⟨1357775, by rfl⟩ : syracuseStep 1810367 = 2715551) B2715551
theorem B15671951 : Blo 802343 15671951 := bstep (se 1 (by rfl) ⟨11753963, by rfl⟩ : syracuseStep 15671951 = 23507927) B23507927
theorem B1811105 : Blo 802343 1811105 := bstep (se 2 (by rfl) ⟨679164, by rfl⟩ : syracuseStep 1811105 = 1358329) B1358329
theorem B13215251 : Blo 802343 13215251 := bstep (se 1 (by rfl) ⟨9911438, by rfl⟩ : syracuseStep 13215251 = 19822877) B19822877
theorem B2894555 : Blo 802343 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B4893959 : Blo 802343 4893959 := bstep (se 1 (by rfl) ⟨3670469, by rfl⟩ : syracuseStep 4893959 = 7340939) B7340939
theorem B4075433 : Blo 802343 4075433 := bstep (se 2 (by rfl) ⟨1528287, by rfl⟩ : syracuseStep 4075433 = 3056575) B3056575
theorem B15677479 : Blo 802343 15677479 := bstep (se 1 (by rfl) ⟨11758109, by rfl⟩ : syracuseStep 15677479 = 23516219) B23516219
theorem B802511 : Blo 802343 802511 := bstep (se 1 (by rfl) ⟨601883, by rfl⟩ : syracuseStep 802511 = 1203767) B1203767
theorem B5358311 : Blo 802343 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B803647 : Blo 802343 803647 := bstep (se 1 (by rfl) ⟨602735, by rfl⟩ : syracuseStep 803647 = 1205471) B1205471
theorem B4080455 : Blo 802343 4080455 := bstep (se 1 (by rfl) ⟨3060341, by rfl⟩ : syracuseStep 4080455 = 6120683) B6120683
theorem B803675 : Blo 802343 803675 := bstep (se 1 (by rfl) ⟨602756, by rfl⟩ : syracuseStep 803675 = 1205513) B1205513
theorem B804223 : Blo 802343 804223 := bstep (se 1 (by rfl) ⟨603167, by rfl⟩ : syracuseStep 804223 = 1206335) B1206335
theorem B33048647 : Blo 802343 33048647 := bstep (se 1 (by rfl) ⟨24786485, by rfl⟩ : syracuseStep 33048647 = 49572971) B49572971
theorem B805103 : Blo 802343 805103 := bstep (se 1 (by rfl) ⟨603827, by rfl⟩ : syracuseStep 805103 = 1207655) B1207655
theorem B805191 : Blo 802343 805191 := bstep (se 1 (by rfl) ⟨603893, by rfl⟩ : syracuseStep 805191 = 1207787) B1207787
theorem B1526215 : Blo 802343 1526215 := bstep (se 1 (by rfl) ⟨1144661, by rfl⟩ : syracuseStep 1526215 = 2289323) B2289323
theorem B805535 : Blo 802343 805535 := bstep (se 1 (by rfl) ⟨604151, by rfl⟩ : syracuseStep 805535 = 1208303) B1208303
theorem B903919 : Blo 802343 903919 := bstep (se 1 (by rfl) ⟨677939, by rfl⟩ : syracuseStep 903919 = 1355879) B1355879
theorem B805991 : Blo 802343 805991 := bstep (se 1 (by rfl) ⟨604493, by rfl⟩ : syracuseStep 805991 = 1208987) B1208987
theorem B29281675 : Blo 802343 29281675 := bstep (se 1 (by rfl) ⟨21961256, by rfl⟩ : syracuseStep 29281675 = 43922513) B43922513
theorem B18828703 : Blo 802343 18828703 := bstep (se 1 (by rfl) ⟨14121527, by rfl⟩ : syracuseStep 18828703 = 28243055) B28243055
theorem B15455771 : Blo 802343 15455771 := bstep (se 1 (by rfl) ⟨11591828, by rfl⟩ : syracuseStep 15455771 = 23183657) B23183657
theorem B2479745 : Blo 802343 2479745 := bstep (se 2 (by rfl) ⟨929904, by rfl⟩ : syracuseStep 2479745 = 1859809) B1859809
theorem B7526135 : Blo 802343 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B45210191 : Blo 802343 45210191 := bstep (se 1 (by rfl) ⟨33907643, by rfl⟩ : syracuseStep 45210191 = 67815287) B67815287
theorem B3858023 : Blo 802343 3858023 := bstep (se 1 (by rfl) ⟨2893517, by rfl⟩ : syracuseStep 3858023 = 5787035) B5787035
theorem B17424071 : Blo 802343 17424071 := bstep (se 1 (by rfl) ⟨13068053, by rfl⟩ : syracuseStep 17424071 = 26136107) B26136107
theorem B4120283 : Blo 802343 4120283 := bstep (se 1 (by rfl) ⟨3090212, by rfl⟩ : syracuseStep 4120283 = 6180425) B6180425
theorem B1204223 : Blo 802343 1204223 := bstep (se 1 (by rfl) ⟨903167, by rfl⟩ : syracuseStep 1204223 = 1806335) B1806335
theorem B2908703 : Blo 802343 2908703 := bstep (se 1 (by rfl) ⟨2181527, by rfl⟩ : syracuseStep 2908703 = 4363055) B4363055
theorem B2712851 : Blo 802343 2712851 := bstep (se 1 (by rfl) ⟨2034638, by rfl⟩ : syracuseStep 2712851 = 4069277) B4069277
theorem B1205567 : Blo 802343 1205567 := bstep (se 1 (by rfl) ⟨904175, by rfl⟩ : syracuseStep 1205567 = 1808351) B1808351
theorem B16770899 : Blo 802343 16770899 := bstep (se 1 (by rfl) ⟨12578174, by rfl⟩ : syracuseStep 16770899 = 25156349) B25156349
theorem B1206143 : Blo 802343 1206143 := bstep (se 1 (by rfl) ⟨904607, by rfl⟩ : syracuseStep 1206143 = 1809215) B1809215
theorem B1206185 : Blo 802343 1206185 := bstep (se 2 (by rfl) ⟨452319, by rfl⟩ : syracuseStep 1206185 = 904639) B904639
theorem B1206455 : Blo 802343 1206455 := bstep (se 1 (by rfl) ⟨904841, by rfl⟩ : syracuseStep 1206455 = 1809683) B1809683
theorem B1206491 : Blo 802343 1206491 := bstep (se 1 (by rfl) ⟨904868, by rfl⟩ : syracuseStep 1206491 = 1809737) B1809737
theorem B1207103 : Blo 802343 1207103 := bstep (se 1 (by rfl) ⟨905327, by rfl⟩ : syracuseStep 1207103 = 1810655) B1810655
theorem B1207451 : Blo 802343 1207451 := bstep (se 1 (by rfl) ⟨905588, by rfl⟩ : syracuseStep 1207451 = 1811177) B1811177
theorem B14643173 : Blo 802343 14643173 := bstep (se 4 (by rfl) ⟨1372797, by rfl⟩ : syracuseStep 14643173 = 2745595) B2745595
theorem B4583405 : Blo 802343 4583405 := bstep (se 3 (by rfl) ⟨859388, by rfl⟩ : syracuseStep 4583405 = 1718777) B1718777
theorem B1208411 : Blo 802343 1208411 := bstep (se 1 (by rfl) ⟨906308, by rfl⟩ : syracuseStep 1208411 = 1812617) B1812617
theorem B22278239 : Blo 802343 22278239 := bstep (se 1 (by rfl) ⟨16708679, by rfl⟩ : syracuseStep 22278239 = 33417359) B33417359
theorem B1209371 : Blo 802343 1209371 := bstep (se 1 (by rfl) ⟨907028, by rfl⟩ : syracuseStep 1209371 = 1814057) B1814057
theorem B1209503 : Blo 802343 1209503 := bstep (se 1 (by rfl) ⟨907127, by rfl⟩ : syracuseStep 1209503 = 1814255) B1814255
theorem B29324753 : Blo 802343 29324753 := bstep (se 2 (by rfl) ⟨10996782, by rfl⟩ : syracuseStep 29324753 = 21993565) B21993565
theorem B13563425 : Blo 802343 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B8715113 : Blo 802343 8715113 := bstep (se 2 (by rfl) ⟨3268167, by rfl⟩ : syracuseStep 8715113 = 6536335) B6536335
theorem B2031551 : Blo 802343 2031551 := bstep (se 1 (by rfl) ⟨1523663, by rfl⟩ : syracuseStep 2031551 = 3047327) B3047327
theorem B3572207 : Blo 802343 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B2720303 : Blo 802343 2720303 := bstep (se 1 (by rfl) ⟨2040227, by rfl⟩ : syracuseStep 2720303 = 4080455) B4080455
theorem B50924227 : Blo 802343 50924227 := bstep (se 1 (by rfl) ⟨38193170, by rfl⟩ : syracuseStep 50924227 = 76386341) B76386341
theorem B4066361 : Blo 802343 4066361 := bstep (se 2 (by rfl) ⟨1524885, by rfl⟩ : syracuseStep 4066361 = 3049771) B3049771
theorem B2034953 : Blo 802343 2034953 := bstep (se 2 (by rfl) ⟨763107, by rfl⟩ : syracuseStep 2034953 = 1526215) B1526215
theorem B5017423 : Blo 802343 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B4133423 : Blo 802343 4133423 := bstep (se 1 (by rfl) ⟨3100067, by rfl⟩ : syracuseStep 4133423 = 6200135) B6200135
theorem B4068143 : Blo 802343 4068143 := bstep (se 1 (by rfl) ⟨3051107, by rfl⟩ : syracuseStep 4068143 = 6102215) B6102215
theorem B2036603 : Blo 802343 2036603 := bstep (se 1 (by rfl) ⟨1527452, by rfl⟩ : syracuseStep 2036603 = 3054905) B3054905
theorem B1939135 : Blo 802343 1939135 := bstep (se 1 (by rfl) ⟨1454351, by rfl⟩ : syracuseStep 1939135 = 2908703) B2908703
theorem B1808567 : Blo 802343 1808567 := bstep (se 1 (by rfl) ⟨1356425, by rfl⟩ : syracuseStep 1808567 = 2712851) B2712851
theorem B11180599 : Blo 802343 11180599 := bstep (se 1 (by rfl) ⟨8385449, by rfl⟩ : syracuseStep 11180599 = 16770899) B16770899
theorem B120560509 : Blo 802343 120560509 := bstep (se 3 (by rfl) ⟨22605095, by rfl⟩ : syracuseStep 120560509 = 45210191) B45210191
theorem B3055603 : Blo 802343 3055603 := bstep (se 1 (by rfl) ⟨2291702, by rfl⟩ : syracuseStep 3055603 = 4583405) B4583405
theorem B14852159 : Blo 802343 14852159 := bstep (se 1 (by rfl) ⟨11139119, by rfl⟩ : syracuseStep 14852159 = 22278239) B22278239
theorem B20588417 : Blo 802343 20588417 := bstep (se 2 (by rfl) ⟨7720656, by rfl⟩ : syracuseStep 20588417 = 15441313) B15441313
theorem B5810075 : Blo 802343 5810075 := bstep (se 1 (by rfl) ⟨4357556, by rfl⟩ : syracuseStep 5810075 = 8715113) B8715113
theorem B1714601 : Blo 802343 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B1354367 : Blo 802343 1354367 := bstep (se 1 (by rfl) ⟨1015775, by rfl⟩ : syracuseStep 1354367 = 2031551) B2031551
theorem B1354495 : Blo 802343 1354495 := bstep (se 1 (by rfl) ⟨1015871, by rfl⟩ : syracuseStep 1354495 = 2031743) B2031743
theorem B1354907 : Blo 802343 1354907 := bstep (se 1 (by rfl) ⟨1016180, by rfl⟩ : syracuseStep 1354907 = 2032361) B2032361
theorem B74460653 : Blo 802343 74460653 := bstep (se 3 (by rfl) ⟨13961372, by rfl⟩ : syracuseStep 74460653 = 27922745) B27922745
theorem B22032431 : Blo 802343 22032431 := bstep (se 1 (by rfl) ⟨16524323, by rfl⟩ : syracuseStep 22032431 = 33048647) B33048647
theorem B3059963 : Blo 802343 3059963 := bstep (se 1 (by rfl) ⟨2294972, by rfl⟩ : syracuseStep 3059963 = 4589945) B4589945
theorem B10303847 : Blo 802343 10303847 := bstep (se 1 (by rfl) ⟨7727885, by rfl⟩ : syracuseStep 10303847 = 15455771) B15455771
theorem B1358201 : Blo 802343 1358201 := bstep (se 2 (by rfl) ⟨509325, by rfl⟩ : syracuseStep 1358201 = 1018651) B1018651
theorem B6863899 : Blo 802343 6863899 := bstep (se 1 (by rfl) ⟨5147924, by rfl⟩ : syracuseStep 6863899 = 10295849) B10295849
theorem B39042233 : Blo 802343 39042233 := bstep (se 2 (by rfl) ⟨14640837, by rfl⟩ : syracuseStep 39042233 = 29281675) B29281675
theorem B2572015 : Blo 802343 2572015 := bstep (se 1 (by rfl) ⟨1929011, by rfl⟩ : syracuseStep 2572015 = 3858023) B3858023
theorem B11616047 : Blo 802343 11616047 := bstep (se 1 (by rfl) ⟨8712035, by rfl⟩ : syracuseStep 11616047 = 17424071) B17424071
theorem B802815 : Blo 802343 802815 := bstep (se 1 (by rfl) ⟨602111, by rfl⟩ : syracuseStep 802815 = 1204223) B1204223
theorem B803711 : Blo 802343 803711 := bstep (se 1 (by rfl) ⟨602783, by rfl⟩ : syracuseStep 803711 = 1205567) B1205567
theorem B804095 : Blo 802343 804095 := bstep (se 1 (by rfl) ⟨603071, by rfl⟩ : syracuseStep 804095 = 1206143) B1206143
theorem B804123 : Blo 802343 804123 := bstep (se 1 (by rfl) ⟨603092, by rfl⟩ : syracuseStep 804123 = 1206185) B1206185
theorem B804303 : Blo 802343 804303 := bstep (se 1 (by rfl) ⟨603227, by rfl⟩ : syracuseStep 804303 = 1206455) B1206455
theorem B804327 : Blo 802343 804327 := bstep (se 1 (by rfl) ⟨603245, by rfl⟩ : syracuseStep 804327 = 1206491) B1206491
theorem B804735 : Blo 802343 804735 := bstep (se 1 (by rfl) ⟨603551, by rfl⟩ : syracuseStep 804735 = 1207103) B1207103
theorem B7718813 : Blo 802343 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B804967 : Blo 802343 804967 := bstep (se 1 (by rfl) ⟨603725, by rfl⟩ : syracuseStep 804967 = 1207451) B1207451
theorem B100419749 : Blo 802343 100419749 := bstep (se 4 (by rfl) ⟨9414351, by rfl⟩ : syracuseStep 100419749 = 18828703) B18828703
theorem B3262639 : Blo 802343 3262639 := bstep (se 1 (by rfl) ⟨2446979, by rfl⟩ : syracuseStep 3262639 = 4893959) B4893959
theorem B805607 : Blo 802343 805607 := bstep (se 1 (by rfl) ⟨604205, by rfl⟩ : syracuseStep 805607 = 1208411) B1208411
theorem B806247 : Blo 802343 806247 := bstep (se 1 (by rfl) ⟨604685, by rfl⟩ : syracuseStep 806247 = 1209371) B1209371
theorem B806335 : Blo 802343 806335 := bstep (se 1 (by rfl) ⟨604751, by rfl⟩ : syracuseStep 806335 = 1209503) B1209503
theorem B19549835 : Blo 802343 19549835 := bstep (se 1 (by rfl) ⟨14662376, by rfl⟩ : syracuseStep 19549835 = 29324753) B29324753
theorem B2905627 : Blo 802343 2905627 := bstep (se 1 (by rfl) ⟨2179220, by rfl⟩ : syracuseStep 2905627 = 4358441) B4358441
theorem B2579795 : Blo 802343 2579795 := bstep (se 1 (by rfl) ⟨1934846, by rfl⟩ : syracuseStep 2579795 = 3869693) B3869693
theorem B1205225 : Blo 802343 1205225 := bstep (se 2 (by rfl) ⟨451959, by rfl⟩ : syracuseStep 1205225 = 903919) B903919
theorem B6514177 : Blo 802343 6514177 := bstep (se 2 (by rfl) ⟨2442816, by rfl⟩ : syracuseStep 6514177 = 4885633) B4885633
theorem B6612653 : Blo 802343 6612653 := bstep (se 3 (by rfl) ⟨1239872, by rfl⟩ : syracuseStep 6612653 = 2479745) B2479745
theorem B1206383 : Blo 802343 1206383 := bstep (se 1 (by rfl) ⟨904787, by rfl⟩ : syracuseStep 1206383 = 1809575) B1809575
theorem B1206431 : Blo 802343 1206431 := bstep (se 1 (by rfl) ⟨904823, by rfl⟩ : syracuseStep 1206431 = 1809647) B1809647
theorem B6121655 : Blo 802343 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B2746855 : Blo 802343 2746855 := bstep (se 1 (by rfl) ⟨2060141, by rfl⟩ : syracuseStep 2746855 = 4120283) B4120283
theorem B1206911 : Blo 802343 1206911 := bstep (se 1 (by rfl) ⟨905183, by rfl⟩ : syracuseStep 1206911 = 1810367) B1810367
theorem B10447967 : Blo 802343 10447967 := bstep (se 1 (by rfl) ⟨7835975, by rfl⟩ : syracuseStep 10447967 = 15671951) B15671951
theorem B1207403 : Blo 802343 1207403 := bstep (se 1 (by rfl) ⟨905552, by rfl⟩ : syracuseStep 1207403 = 1811105) B1811105
theorem B8810167 : Blo 802343 8810167 := bstep (se 1 (by rfl) ⟨6607625, by rfl⟩ : syracuseStep 8810167 = 13215251) B13215251
theorem B2716955 : Blo 802343 2716955 := bstep (se 1 (by rfl) ⟨2037716, by rfl⟩ : syracuseStep 2716955 = 4075433) B4075433
theorem B9762115 : Blo 802343 9762115 := bstep (se 1 (by rfl) ⟨7321586, by rfl⟩ : syracuseStep 9762115 = 14643173) B14643173
theorem B20903305 : Blo 802343 20903305 := bstep (se 2 (by rfl) ⟨7838739, by rfl⟩ : syracuseStep 20903305 = 15677479) B15677479
theorem B9042283 : Blo 802343 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B5145875 : Blo 802343 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B66946499 : Blo 802343 66946499 := bstep (se 1 (by rfl) ⟨50209874, by rfl⟩ : syracuseStep 66946499 = 100419749) B100419749
theorem B8685569 : Blo 802343 8685569 := bstep (se 2 (by rfl) ⟨3257088, by rfl⟩ : syracuseStep 8685569 = 6514177) B6514177
theorem B14649893 : Blo 802343 14649893 := bstep (se 4 (by rfl) ⟨1373427, by rfl⟩ : syracuseStep 14649893 = 2746855) B2746855
theorem B2755615 : Blo 802343 2755615 := bstep (se 1 (by rfl) ⟨2066711, by rfl⟩ : syracuseStep 2755615 = 4133423) B4133423
theorem B67898969 : Blo 802343 67898969 := bstep (se 2 (by rfl) ⟨25462113, by rfl⟩ : syracuseStep 67898969 = 50924227) B50924227
theorem B1805993 : Blo 802343 1805993 := bstep (se 2 (by rfl) ⟨677247, by rfl⟩ : syracuseStep 1805993 = 1354495) B1354495
theorem B6689897 : Blo 802343 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B9901439 : Blo 802343 9901439 := bstep (se 1 (by rfl) ⟨7426079, by rfl⟩ : syracuseStep 9901439 = 14852159) B14852159
theorem B3873383 : Blo 802343 3873383 := bstep (se 1 (by rfl) ⟨2905037, by rfl⟩ : syracuseStep 3873383 = 5810075) B5810075
theorem B13016153 : Blo 802343 13016153 := bstep (se 2 (by rfl) ⟨4881057, by rfl⟩ : syracuseStep 13016153 = 9762115) B9762115
theorem B3874169 : Blo 802343 3874169 := bstep (se 2 (by rfl) ⟨1452813, by rfl⟩ : syracuseStep 3874169 = 2905627) B2905627
theorem B14688287 : Blo 802343 14688287 := bstep (se 1 (by rfl) ⟨11016215, by rfl⟩ : syracuseStep 14688287 = 22032431) B22032431
theorem B2039975 : Blo 802343 2039975 := bstep (se 1 (by rfl) ⟨1529981, by rfl⟩ : syracuseStep 2039975 = 3059963) B3059963
theorem B1811303 : Blo 802343 1811303 := bstep (se 1 (by rfl) ⟨1358477, by rfl⟩ : syracuseStep 1811303 = 2716955) B2716955
theorem B9151865 : Blo 802343 9151865 := bstep (se 2 (by rfl) ⟨3431949, by rfl⟩ : syracuseStep 9151865 = 6863899) B6863899
theorem B26028155 : Blo 802343 26028155 := bstep (se 1 (by rfl) ⟨19521116, by rfl⟩ : syracuseStep 26028155 = 39042233) B39042233
theorem B7744031 : Blo 802343 7744031 := bstep (se 1 (by rfl) ⟨5808023, by rfl⟩ : syracuseStep 7744031 = 11616047) B11616047
theorem B4074137 : Blo 802343 4074137 := bstep (se 2 (by rfl) ⟨1527801, by rfl⟩ : syracuseStep 4074137 = 3055603) B3055603
theorem B1813535 : Blo 802343 1813535 := bstep (se 1 (by rfl) ⟨1360151, by rfl⟩ : syracuseStep 1813535 = 2720303) B2720303
theorem B1356635 : Blo 802343 1356635 := bstep (se 1 (by rfl) ⟨1017476, by rfl⟩ : syracuseStep 1356635 = 2034953) B2034953
theorem B1357735 : Blo 802343 1357735 := bstep (se 1 (by rfl) ⟨1018301, by rfl⟩ : syracuseStep 1357735 = 2036603) B2036603
theorem B1719863 : Blo 802343 1719863 := bstep (se 1 (by rfl) ⟨1289897, by rfl⟩ : syracuseStep 1719863 = 2579795) B2579795
theorem B11746889 : Blo 802343 11746889 := bstep (se 2 (by rfl) ⟨4405083, by rfl⟩ : syracuseStep 11746889 = 8810167) B8810167
theorem B803483 : Blo 802343 803483 := bstep (se 1 (by rfl) ⟨602612, by rfl⟩ : syracuseStep 803483 = 1205225) B1205225
theorem B4408435 : Blo 802343 4408435 := bstep (se 1 (by rfl) ⟨3306326, by rfl⟩ : syracuseStep 4408435 = 6612653) B6612653
theorem B804255 : Blo 802343 804255 := bstep (se 1 (by rfl) ⟨603191, by rfl⟩ : syracuseStep 804255 = 1206383) B1206383
theorem B804287 : Blo 802343 804287 := bstep (se 1 (by rfl) ⟨603215, by rfl⟩ : syracuseStep 804287 = 1206431) B1206431
theorem B4081103 : Blo 802343 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B902911 : Blo 802343 902911 := bstep (se 1 (by rfl) ⟨677183, by rfl⟩ : syracuseStep 902911 = 1354367) B1354367
theorem B804607 : Blo 802343 804607 := bstep (se 1 (by rfl) ⟨603455, by rfl⟩ : syracuseStep 804607 = 1206911) B1206911
theorem B27871073 : Blo 802343 27871073 := bstep (se 2 (by rfl) ⟨10451652, by rfl⟩ : syracuseStep 27871073 = 20903305) B20903305
theorem B6965311 : Blo 802343 6965311 := bstep (se 1 (by rfl) ⟨5223983, by rfl⟩ : syracuseStep 6965311 = 10447967) B10447967
theorem B804935 : Blo 802343 804935 := bstep (se 1 (by rfl) ⟨603701, by rfl⟩ : syracuseStep 804935 = 1207403) B1207403
theorem B903271 : Blo 802343 903271 := bstep (se 1 (by rfl) ⟨677453, by rfl⟩ : syracuseStep 903271 = 1354907) B1354907
theorem B160747345 : Blo 802343 160747345 := bstep (se 2 (by rfl) ⟨60280254, by rfl⟩ : syracuseStep 160747345 = 120560509) B120560509
theorem B6869231 : Blo 802343 6869231 := bstep (se 1 (by rfl) ⟨5151923, by rfl⟩ : syracuseStep 6869231 = 10303847) B10303847
theorem B905467 : Blo 802343 905467 := bstep (se 1 (by rfl) ⟨679100, by rfl⟩ : syracuseStep 905467 = 1358201) B1358201
theorem B3429353 : Blo 802343 3429353 := bstep (se 2 (by rfl) ⟨1286007, by rfl⟩ : syracuseStep 3429353 = 2572015) B2572015
theorem B2381471 : Blo 802343 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B2710907 : Blo 802343 2710907 := bstep (se 1 (by rfl) ⟨2033180, by rfl⟩ : syracuseStep 2710907 = 4066361) B4066361
theorem B13033223 : Blo 802343 13033223 := bstep (se 1 (by rfl) ⟨9774917, by rfl⟩ : syracuseStep 13033223 = 19549835) B19549835
theorem B4350185 : Blo 802343 4350185 := bstep (se 2 (by rfl) ⟨1631319, by rfl⟩ : syracuseStep 4350185 = 3262639) B3262639
theorem B59629861 : Blo 802343 59629861 := bstep (se 4 (by rfl) ⟨5590299, by rfl⟩ : syracuseStep 59629861 = 11180599) B11180599
theorem B2712095 : Blo 802343 2712095 := bstep (se 1 (by rfl) ⟨2034071, by rfl⟩ : syracuseStep 2712095 = 4068143) B4068143
theorem B1205711 : Blo 802343 1205711 := bstep (se 1 (by rfl) ⟨904283, by rfl⟩ : syracuseStep 1205711 = 1808567) B1808567
theorem B13725611 : Blo 802343 13725611 := bstep (se 1 (by rfl) ⟨10294208, by rfl⟩ : syracuseStep 13725611 = 20588417) B20588417
theorem B1143067 : Blo 802343 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B2585513 : Blo 802343 2585513 := bstep (se 2 (by rfl) ⟨969567, by rfl⟩ : syracuseStep 2585513 = 1939135) B1939135
theorem B49640435 : Blo 802343 49640435 := bstep (se 1 (by rfl) ⟨37230326, by rfl⟩ : syracuseStep 49640435 = 74460653) B74460653
theorem B12056377 : Blo 802343 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B44630999 : Blo 802343 44630999 := bstep (se 1 (by rfl) ⟨33473249, by rfl⟩ : syracuseStep 44630999 = 66946499) B66946499
theorem B2720735 : Blo 802343 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B18580715 : Blo 802343 18580715 := bstep (se 1 (by rfl) ⟨13935536, by rfl⟩ : syracuseStep 18580715 = 27871073) B27871073
theorem B9766595 : Blo 802343 9766595 := bstep (se 1 (by rfl) ⟨7324946, by rfl⟩ : syracuseStep 9766595 = 14649893) B14649893
theorem B4459931 : Blo 802343 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B3674153 : Blo 802343 3674153 := bstep (se 2 (by rfl) ⟨1377807, by rfl⟩ : syracuseStep 3674153 = 2755615) B2755615
theorem B1807271 : Blo 802343 1807271 := bstep (se 1 (by rfl) ⟨1355453, by rfl⟩ : syracuseStep 1807271 = 2710907) B2710907
theorem B8688815 : Blo 802343 8688815 := bstep (se 1 (by rfl) ⟨6516611, by rfl⟩ : syracuseStep 8688815 = 13033223) B13033223
theorem B1808063 : Blo 802343 1808063 := bstep (se 1 (by rfl) ⟨1356047, by rfl⟩ : syracuseStep 1808063 = 2712095) B2712095
theorem B6101243 : Blo 802343 6101243 := bstep (se 1 (by rfl) ⟨4575932, by rfl⟩ : syracuseStep 6101243 = 9151865) B9151865
theorem B1810313 : Blo 802343 1810313 := bstep (se 2 (by rfl) ⟨678867, by rfl⟩ : syracuseStep 1810313 = 1357735) B1357735
theorem B9150407 : Blo 802343 9150407 := bstep (se 1 (by rfl) ⟨6862805, by rfl⟩ : syracuseStep 9150407 = 13725611) B13725611
theorem B34709741 : Blo 802343 34709741 := bstep (se 3 (by rfl) ⟨6508076, by rfl⟩ : syracuseStep 34709741 = 13016153) B13016153
theorem B857319173 : Blo 802343 857319173 := bstep (se 4 (by rfl) ⟨80373672, by rfl⟩ : syracuseStep 857319173 = 160747345) B160747345
theorem B79506481 : Blo 802343 79506481 := bstep (se 2 (by rfl) ⟨29814930, by rfl⟩ : syracuseStep 79506481 = 59629861) B59629861
theorem B45265979 : Blo 802343 45265979 := bstep (se 1 (by rfl) ⟨33949484, by rfl⟩ : syracuseStep 45265979 = 67898969) B67898969
theorem B9287081 : Blo 802343 9287081 := bstep (se 2 (by rfl) ⟨3482655, by rfl⟩ : syracuseStep 9287081 = 6965311) B6965311
theorem B6600959 : Blo 802343 6600959 := bstep (se 1 (by rfl) ⟨4950719, by rfl⟩ : syracuseStep 6600959 = 9901439) B9901439
theorem B1587647 : Blo 802343 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B1359983 : Blo 802343 1359983 := bstep (se 1 (by rfl) ⟨1019987, by rfl⟩ : syracuseStep 1359983 = 2039975) B2039975
theorem B2900123 : Blo 802343 2900123 := bstep (se 1 (by rfl) ⟨2175092, by rfl⟩ : syracuseStep 2900123 = 4350185) B4350185
theorem B1524089 : Blo 802343 1524089 := bstep (se 2 (by rfl) ⟨571533, by rfl⟩ : syracuseStep 1524089 = 1143067) B1143067
theorem B23511653 : Blo 802343 23511653 := bstep (se 4 (by rfl) ⟨2204217, by rfl⟩ : syracuseStep 23511653 = 4408435) B4408435
theorem B803807 : Blo 802343 803807 := bstep (se 1 (by rfl) ⟨602855, by rfl⟩ : syracuseStep 803807 = 1205711) B1205711
theorem B17352103 : Blo 802343 17352103 := bstep (se 1 (by rfl) ⟨13014077, by rfl⟩ : syracuseStep 17352103 = 26028155) B26028155
theorem B5162687 : Blo 802343 5162687 := bstep (se 1 (by rfl) ⟨3872015, by rfl⟩ : syracuseStep 5162687 = 7744031) B7744031
theorem B16075169 : Blo 802343 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B904423 : Blo 802343 904423 := bstep (se 1 (by rfl) ⟨678317, by rfl⟩ : syracuseStep 904423 = 1356635) B1356635
theorem B1723675 : Blo 802343 1723675 := bstep (se 1 (by rfl) ⟨1292756, by rfl⟩ : syracuseStep 1723675 = 2585513) B2585513
theorem B3430583 : Blo 802343 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B5790379 : Blo 802343 5790379 := bstep (se 1 (by rfl) ⟨4342784, by rfl⟩ : syracuseStep 5790379 = 8685569) B8685569
theorem B1203881 : Blo 802343 1203881 := bstep (se 2 (by rfl) ⟨451455, by rfl⟩ : syracuseStep 1203881 = 902911) B902911
theorem B1203995 : Blo 802343 1203995 := bstep (se 1 (by rfl) ⟨902996, by rfl⟩ : syracuseStep 1203995 = 1805993) B1805993
theorem B1204361 : Blo 802343 1204361 := bstep (se 2 (by rfl) ⟨451635, by rfl⟩ : syracuseStep 1204361 = 903271) B903271
theorem B4579487 : Blo 802343 4579487 := bstep (se 1 (by rfl) ⟨3434615, by rfl⟩ : syracuseStep 4579487 = 6869231) B6869231
theorem B2286235 : Blo 802343 2286235 := bstep (se 1 (by rfl) ⟨1714676, by rfl⟩ : syracuseStep 2286235 = 3429353) B3429353
theorem B2582255 : Blo 802343 2582255 := bstep (se 1 (by rfl) ⟨1936691, by rfl⟩ : syracuseStep 2582255 = 3873383) B3873383
theorem B2582779 : Blo 802343 2582779 := bstep (se 1 (by rfl) ⟨1937084, by rfl⟩ : syracuseStep 2582779 = 3874169) B3874169
theorem B9792191 : Blo 802343 9792191 := bstep (se 1 (by rfl) ⟨7344143, by rfl⟩ : syracuseStep 9792191 = 14688287) B14688287
theorem B1207289 : Blo 802343 1207289 := bstep (se 2 (by rfl) ⟨452733, by rfl⟩ : syracuseStep 1207289 = 905467) B905467
theorem B1207535 : Blo 802343 1207535 := bstep (se 1 (by rfl) ⟨905651, by rfl⟩ : syracuseStep 1207535 = 1811303) B1811303
theorem B2716091 : Blo 802343 2716091 := bstep (se 1 (by rfl) ⟨2037068, by rfl⟩ : syracuseStep 2716091 = 4074137) B4074137
theorem B1209023 : Blo 802343 1209023 := bstep (se 1 (by rfl) ⟨906767, by rfl⟩ : syracuseStep 1209023 = 1813535) B1813535
theorem B33093623 : Blo 802343 33093623 := bstep (se 1 (by rfl) ⟨24820217, by rfl⟩ : syracuseStep 33093623 = 49640435) B49640435
theorem B1146575 : Blo 802343 1146575 := bstep (se 1 (by rfl) ⟨859931, by rfl⟩ : syracuseStep 1146575 = 1719863) B1719863
theorem B7831259 : Blo 802343 7831259 := bstep (se 1 (by rfl) ⟨5873444, by rfl⟩ : syracuseStep 7831259 = 11746889) B11746889
theorem B1933415 : Blo 802343 1933415 := bstep (se 1 (by rfl) ⟨1450061, by rfl⟩ : syracuseStep 1933415 = 2900123) B2900123
theorem B1016059 : Blo 802343 1016059 := bstep (se 1 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 1016059 = 1524089) B1524089
theorem B29753999 : Blo 802343 29753999 := bstep (se 1 (by rfl) ⟨22315499, by rfl⟩ : syracuseStep 29753999 = 44630999) B44630999
theorem B12387143 : Blo 802343 12387143 := bstep (se 1 (by rfl) ⟨9290357, by rfl⟩ : syracuseStep 12387143 = 18580715) B18580715
theorem B3048313 : Blo 802343 3048313 := bstep (se 2 (by rfl) ⟨1143117, by rfl⟩ : syracuseStep 3048313 = 2286235) B2286235
theorem B3441791 : Blo 802343 3441791 := bstep (se 1 (by rfl) ⟨2581343, by rfl⟩ : syracuseStep 3441791 = 5162687) B5162687
theorem B10716779 : Blo 802343 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B23136137 : Blo 802343 23136137 := bstep (se 2 (by rfl) ⟨8676051, by rfl⟩ : syracuseStep 23136137 = 17352103) B17352103
theorem B3443705 : Blo 802343 3443705 := bstep (se 2 (by rfl) ⟨1291389, by rfl⟩ : syracuseStep 3443705 = 2582779) B2582779
theorem B106008641 : Blo 802343 106008641 := bstep (se 2 (by rfl) ⟨39753240, by rfl⟩ : syracuseStep 106008641 = 79506481) B79506481
theorem B4067495 : Blo 802343 4067495 := bstep (se 1 (by rfl) ⟨3050621, by rfl⟩ : syracuseStep 4067495 = 6101243) B6101243
theorem B2298233 : Blo 802343 2298233 := bstep (se 2 (by rfl) ⟨861837, by rfl⟩ : syracuseStep 2298233 = 1723675) B1723675
theorem B6100271 : Blo 802343 6100271 := bstep (se 1 (by rfl) ⟨4575203, by rfl⟩ : syracuseStep 6100271 = 9150407) B9150407
theorem B3052991 : Blo 802343 3052991 := bstep (se 1 (by rfl) ⟨2289743, by rfl⟩ : syracuseStep 3052991 = 4579487) B4579487
theorem B23139827 : Blo 802343 23139827 := bstep (se 1 (by rfl) ⟨17354870, by rfl⟩ : syracuseStep 23139827 = 34709741) B34709741
theorem B4233725 : Blo 802343 4233725 := bstep (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) B1587647
theorem B571546115 : Blo 802343 571546115 := bstep (se 1 (by rfl) ⟨428659586, by rfl⟩ : syracuseStep 571546115 = 857319173) B857319173
theorem B6528127 : Blo 802343 6528127 := bstep (se 1 (by rfl) ⟨4896095, by rfl⟩ : syracuseStep 6528127 = 9792191) B9792191
theorem B1810727 : Blo 802343 1810727 := bstep (se 1 (by rfl) ⟨1358045, by rfl⟩ : syracuseStep 1810727 = 2716091) B2716091
theorem B22062415 : Blo 802343 22062415 := bstep (se 1 (by rfl) ⟨16546811, by rfl⟩ : syracuseStep 22062415 = 33093623) B33093623
theorem B4400639 : Blo 802343 4400639 := bstep (se 1 (by rfl) ⟨3300479, by rfl⟩ : syracuseStep 4400639 = 6600959) B6600959
theorem B3057533 : Blo 802343 3057533 := bstep (se 3 (by rfl) ⟨573287, by rfl⟩ : syracuseStep 3057533 = 1146575) B1146575
theorem B5220839 : Blo 802343 5220839 := bstep (se 1 (by rfl) ⟨3915629, by rfl⟩ : syracuseStep 5220839 = 7831259) B7831259
theorem B15674435 : Blo 802343 15674435 := bstep (se 1 (by rfl) ⟨11755826, by rfl⟩ : syracuseStep 15674435 = 23511653) B23511653
theorem B1813823 : Blo 802343 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B802587 : Blo 802343 802587 := bstep (se 1 (by rfl) ⟨601940, by rfl⟩ : syracuseStep 802587 = 1203881) B1203881
theorem B802663 : Blo 802343 802663 := bstep (se 1 (by rfl) ⟨601997, by rfl⟩ : syracuseStep 802663 = 1203995) B1203995
theorem B802907 : Blo 802343 802907 := bstep (se 1 (by rfl) ⟨602180, by rfl⟩ : syracuseStep 802907 = 1204361) B1204361
theorem B1721503 : Blo 802343 1721503 := bstep (se 1 (by rfl) ⟨1291127, by rfl⟩ : syracuseStep 1721503 = 2582255) B2582255
theorem B804859 : Blo 802343 804859 := bstep (se 1 (by rfl) ⟨603644, by rfl⟩ : syracuseStep 804859 = 1207289) B1207289
theorem B805023 : Blo 802343 805023 := bstep (se 1 (by rfl) ⟨603767, by rfl⟩ : syracuseStep 805023 = 1207535) B1207535
theorem B806015 : Blo 802343 806015 := bstep (se 1 (by rfl) ⟨604511, by rfl⟩ : syracuseStep 806015 = 1209023) B1209023
theorem B7720505 : Blo 802343 7720505 := bstep (se 2 (by rfl) ⟨2895189, by rfl⟩ : syracuseStep 7720505 = 5790379) B5790379
theorem B906655 : Blo 802343 906655 := bstep (se 1 (by rfl) ⟨679991, by rfl⟩ : syracuseStep 906655 = 1359983) B1359983
theorem B2973287 : Blo 802343 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B2449435 : Blo 802343 2449435 := bstep (se 1 (by rfl) ⟨1837076, by rfl⟩ : syracuseStep 2449435 = 3674153) B3674153
theorem B1204847 : Blo 802343 1204847 := bstep (se 1 (by rfl) ⟨903635, by rfl⟩ : syracuseStep 1204847 = 1807271) B1807271
theorem B5792543 : Blo 802343 5792543 := bstep (se 1 (by rfl) ⟨4344407, by rfl⟩ : syracuseStep 5792543 = 8688815) B8688815
theorem B1205375 : Blo 802343 1205375 := bstep (se 1 (by rfl) ⟨904031, by rfl⟩ : syracuseStep 1205375 = 1808063) B1808063
theorem B2287055 : Blo 802343 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B1205897 : Blo 802343 1205897 := bstep (se 2 (by rfl) ⟨452211, by rfl⟩ : syracuseStep 1205897 = 904423) B904423
theorem B26044253 : Blo 802343 26044253 := bstep (se 3 (by rfl) ⟨4883297, by rfl⟩ : syracuseStep 26044253 = 9766595) B9766595
theorem B1206875 : Blo 802343 1206875 := bstep (se 1 (by rfl) ⟨905156, by rfl⟩ : syracuseStep 1206875 = 1810313) B1810313
theorem B30177319 : Blo 802343 30177319 := bstep (se 1 (by rfl) ⟨22632989, by rfl⟩ : syracuseStep 30177319 = 45265979) B45265979
theorem B6191387 : Blo 802343 6191387 := bstep (se 1 (by rfl) ⟨4643540, by rfl⟩ : syracuseStep 6191387 = 9287081) B9287081
theorem B8258095 : Blo 802343 8258095 := bstep (se 1 (by rfl) ⟨6193571, by rfl⟩ : syracuseStep 8258095 = 12387143) B12387143
theorem B7144519 : Blo 802343 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B4064417 : Blo 802343 4064417 := bstep (se 2 (by rfl) ⟨1524156, by rfl⟩ : syracuseStep 4064417 = 3048313) B3048313
theorem B2295337 : Blo 802343 2295337 := bstep (se 2 (by rfl) ⟨860751, by rfl⟩ : syracuseStep 2295337 = 1721503) B1721503
theorem B2295803 : Blo 802343 2295803 := bstep (se 1 (by rfl) ⟨1721852, by rfl⟩ : syracuseStep 2295803 = 3443705) B3443705
theorem B5147003 : Blo 802343 5147003 := bstep (se 1 (by rfl) ⟨3860252, by rfl⟩ : syracuseStep 5147003 = 7720505) B7720505
theorem B9178109 : Blo 802343 9178109 := bstep (se 3 (by rfl) ⟨1720895, by rfl⟩ : syracuseStep 9178109 = 3441791) B3441791
theorem B4066847 : Blo 802343 4066847 := bstep (se 1 (by rfl) ⟨3050135, by rfl⟩ : syracuseStep 4066847 = 6100271) B6100271
theorem B2035327 : Blo 802343 2035327 := bstep (se 1 (by rfl) ⟨1526495, by rfl⟩ : syracuseStep 2035327 = 3052991) B3052991
theorem B6098813 : Blo 802343 6098813 := bstep (se 3 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 6098813 = 2287055) B2287055
theorem B2822483 : Blo 802343 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B381030743 : Blo 802343 381030743 := bstep (se 1 (by rfl) ⟨285773057, by rfl⟩ : syracuseStep 381030743 = 571546115) B571546115
theorem B2038355 : Blo 802343 2038355 := bstep (se 1 (by rfl) ⟨1528766, by rfl⟩ : syracuseStep 2038355 = 3057533) B3057533
theorem B1288943 : Blo 802343 1288943 := bstep (se 1 (by rfl) ⟨966707, by rfl⟩ : syracuseStep 1288943 = 1933415) B1933415
theorem B1354745 : Blo 802343 1354745 := bstep (se 2 (by rfl) ⟨508029, by rfl⟩ : syracuseStep 1354745 = 1016059) B1016059
theorem B19835999 : Blo 802343 19835999 := bstep (se 1 (by rfl) ⟨14876999, by rfl⟩ : syracuseStep 19835999 = 29753999) B29753999
theorem B803231 : Blo 802343 803231 := bstep (se 1 (by rfl) ⟨602423, by rfl⟩ : syracuseStep 803231 = 1204847) B1204847
theorem B803583 : Blo 802343 803583 := bstep (se 1 (by rfl) ⟨602687, by rfl⟩ : syracuseStep 803583 = 1205375) B1205375
theorem B2933759 : Blo 802343 2933759 := bstep (se 1 (by rfl) ⟨2200319, by rfl⟩ : syracuseStep 2933759 = 4400639) B4400639
theorem B803931 : Blo 802343 803931 := bstep (se 1 (by rfl) ⟨602948, by rfl⟩ : syracuseStep 803931 = 1205897) B1205897
theorem B804583 : Blo 802343 804583 := bstep (se 1 (by rfl) ⟨603437, by rfl⟩ : syracuseStep 804583 = 1206875) B1206875
theorem B8704169 : Blo 802343 8704169 := bstep (se 2 (by rfl) ⟨3264063, by rfl⟩ : syracuseStep 8704169 = 6528127) B6528127
theorem B3265913 : Blo 802343 3265913 := bstep (se 2 (by rfl) ⟨1224717, by rfl⟩ : syracuseStep 3265913 = 2449435) B2449435
theorem B15424091 : Blo 802343 15424091 := bstep (se 1 (by rfl) ⟨11568068, by rfl⟩ : syracuseStep 15424091 = 23136137) B23136137
theorem B29416553 : Blo 802343 29416553 := bstep (se 2 (by rfl) ⟨11031207, by rfl⟩ : syracuseStep 29416553 = 22062415) B22062415
theorem B70672427 : Blo 802343 70672427 := bstep (se 1 (by rfl) ⟨53004320, by rfl⟩ : syracuseStep 70672427 = 106008641) B106008641
theorem B2711663 : Blo 802343 2711663 := bstep (se 1 (by rfl) ⟨2033747, by rfl⟩ : syracuseStep 2711663 = 4067495) B4067495
theorem B1532155 : Blo 802343 1532155 := bstep (se 1 (by rfl) ⟨1149116, by rfl⟩ : syracuseStep 1532155 = 2298233) B2298233
theorem B15426551 : Blo 802343 15426551 := bstep (se 1 (by rfl) ⟨11569913, by rfl⟩ : syracuseStep 15426551 = 23139827) B23139827
theorem B1207151 : Blo 802343 1207151 := bstep (se 1 (by rfl) ⟨905363, by rfl⟩ : syracuseStep 1207151 = 1810727) B1810727
theorem B3861695 : Blo 802343 3861695 := bstep (se 1 (by rfl) ⟨2896271, by rfl⟩ : syracuseStep 3861695 = 5792543) B5792543
theorem B17362835 : Blo 802343 17362835 := bstep (se 1 (by rfl) ⟨13022126, by rfl⟩ : syracuseStep 17362835 = 26044253) B26044253
theorem B13922237 : Blo 802343 13922237 := bstep (se 3 (by rfl) ⟨2610419, by rfl⟩ : syracuseStep 13922237 = 5220839) B5220839
theorem B1208873 : Blo 802343 1208873 := bstep (se 2 (by rfl) ⟨453327, by rfl⟩ : syracuseStep 1208873 = 906655) B906655
theorem B10449623 : Blo 802343 10449623 := bstep (se 1 (by rfl) ⟨7837217, by rfl⟩ : syracuseStep 10449623 = 15674435) B15674435
theorem B1209215 : Blo 802343 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B40236425 : Blo 802343 40236425 := bstep (se 2 (by rfl) ⟨15088659, by rfl⟩ : syracuseStep 40236425 = 30177319) B30177319
theorem B4127591 : Blo 802343 4127591 := bstep (se 1 (by rfl) ⟨3095693, by rfl⟩ : syracuseStep 4127591 = 6191387) B6191387
theorem B7928765 : Blo 802343 7928765 := bstep (se 3 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 7928765 = 2973287) B2973287
theorem B4065875 : Blo 802343 4065875 := bstep (se 1 (by rfl) ⟨3049406, by rfl⟩ : syracuseStep 4065875 = 6098813) B6098813
theorem B5802779 : Blo 802343 5802779 := bstep (se 1 (by rfl) ⟨4352084, by rfl⟩ : syracuseStep 5802779 = 8704169) B8704169
theorem B254020495 : Blo 802343 254020495 := bstep (se 1 (by rfl) ⟨190515371, by rfl⟩ : syracuseStep 254020495 = 381030743) B381030743
theorem B44043173 : Blo 802343 44043173 := bstep (se 4 (by rfl) ⟨4129047, by rfl⟩ : syracuseStep 44043173 = 8258095) B8258095
theorem B1807775 : Blo 802343 1807775 := bstep (se 1 (by rfl) ⟨1355831, by rfl⟩ : syracuseStep 1807775 = 2711663) B2711663
theorem B859295 : Blo 802343 859295 := bstep (se 1 (by rfl) ⟨644471, by rfl⟩ : syracuseStep 859295 = 1288943) B1288943
theorem B11575223 : Blo 802343 11575223 := bstep (se 1 (by rfl) ⟨8681417, by rfl⟩ : syracuseStep 11575223 = 17362835) B17362835
theorem B10297853 : Blo 802343 10297853 := bstep (se 3 (by rfl) ⟨1930847, by rfl⟩ : syracuseStep 10297853 = 3861695) B3861695
theorem B5285843 : Blo 802343 5285843 := bstep (se 1 (by rfl) ⟨3964382, by rfl⟩ : syracuseStep 5285843 = 7928765) B7928765
theorem B2042873 : Blo 802343 2042873 := bstep (se 2 (by rfl) ⟨766077, by rfl⟩ : syracuseStep 2042873 = 1532155) B1532155
theorem B3060449 : Blo 802343 3060449 := bstep (se 2 (by rfl) ⟨1147668, by rfl⟩ : syracuseStep 3060449 = 2295337) B2295337
theorem B2177275 : Blo 802343 2177275 := bstep (se 1 (by rfl) ⟨1632956, by rfl⟩ : syracuseStep 2177275 = 3265913) B3265913
theorem B1358903 : Blo 802343 1358903 := bstep (se 1 (by rfl) ⟨1019177, by rfl⟩ : syracuseStep 1358903 = 2038355) B2038355
theorem B19611035 : Blo 802343 19611035 := bstep (se 1 (by rfl) ⟨14708276, by rfl⟩ : syracuseStep 19611035 = 29416553) B29416553
theorem B804767 : Blo 802343 804767 := bstep (se 1 (by rfl) ⟨603575, by rfl⟩ : syracuseStep 804767 = 1207151) B1207151
theorem B903163 : Blo 802343 903163 := bstep (se 1 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 903163 = 1354745) B1354745
theorem B13223999 : Blo 802343 13223999 := bstep (se 1 (by rfl) ⟨9917999, by rfl⟩ : syracuseStep 13223999 = 19835999) B19835999
theorem B805915 : Blo 802343 805915 := bstep (se 1 (by rfl) ⟨604436, by rfl⟩ : syracuseStep 805915 = 1208873) B1208873
theorem B6966415 : Blo 802343 6966415 := bstep (se 1 (by rfl) ⟨5224811, by rfl⟩ : syracuseStep 6966415 = 10449623) B10449623
theorem B806143 : Blo 802343 806143 := bstep (se 1 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 806143 = 1209215) B1209215
theorem B26824283 : Blo 802343 26824283 := bstep (se 1 (by rfl) ⟨20118212, by rfl⟩ : syracuseStep 26824283 = 40236425) B40236425
theorem B1955839 : Blo 802343 1955839 := bstep (se 1 (by rfl) ⟨1466879, by rfl⟩ : syracuseStep 1955839 = 2933759) B2933759
theorem B2709611 : Blo 802343 2709611 := bstep (se 1 (by rfl) ⟨2032208, by rfl⟩ : syracuseStep 2709611 = 4064417) B4064417
theorem B7526621 : Blo 802343 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B9526025 : Blo 802343 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B3431335 : Blo 802343 3431335 := bstep (se 1 (by rfl) ⟨2573501, by rfl⟩ : syracuseStep 3431335 = 5147003) B5147003
theorem B6118739 : Blo 802343 6118739 := bstep (se 1 (by rfl) ⟨4589054, by rfl⟩ : syracuseStep 6118739 = 9178109) B9178109
theorem B2711231 : Blo 802343 2711231 := bstep (se 1 (by rfl) ⟨2033423, by rfl⟩ : syracuseStep 2711231 = 4066847) B4066847
theorem B10282727 : Blo 802343 10282727 := bstep (se 1 (by rfl) ⟨7712045, by rfl⟩ : syracuseStep 10282727 = 15424091) B15424091
theorem B2713769 : Blo 802343 2713769 := bstep (se 2 (by rfl) ⟨1017663, by rfl⟩ : syracuseStep 2713769 = 2035327) B2035327
theorem B6122141 : Blo 802343 6122141 := bstep (se 3 (by rfl) ⟨1147901, by rfl⟩ : syracuseStep 6122141 = 2295803) B2295803
theorem B47114951 : Blo 802343 47114951 := bstep (se 1 (by rfl) ⟨35336213, by rfl⟩ : syracuseStep 47114951 = 70672427) B70672427
theorem B10284367 : Blo 802343 10284367 := bstep (se 1 (by rfl) ⟨7713275, by rfl⟩ : syracuseStep 10284367 = 15426551) B15426551
theorem B2751727 : Blo 802343 2751727 := bstep (se 1 (by rfl) ⟨2063795, by rfl⟩ : syracuseStep 2751727 = 4127591) B4127591
theorem B37125965 : Blo 802343 37125965 := bstep (se 3 (by rfl) ⟨6961118, by rfl⟩ : syracuseStep 37125965 = 13922237) B13922237
theorem B8815999 : Blo 802343 8815999 := bstep (se 1 (by rfl) ⟨6611999, by rfl⟩ : syracuseStep 8815999 = 13223999) B13223999
theorem B3868519 : Blo 802343 3868519 := bstep (se 1 (by rfl) ⟨2901389, by rfl⟩ : syracuseStep 3868519 = 5802779) B5802779
theorem B29362115 : Blo 802343 29362115 := bstep (se 1 (by rfl) ⟨22021586, by rfl⟩ : syracuseStep 29362115 = 44043173) B44043173
theorem B338693993 : Blo 802343 338693993 := bstep (se 2 (by rfl) ⟨127010247, by rfl⟩ : syracuseStep 338693993 = 254020495) B254020495
theorem B1806407 : Blo 802343 1806407 := bstep (se 1 (by rfl) ⟨1354805, by rfl⟩ : syracuseStep 1806407 = 2709611) B2709611
theorem B1807487 : Blo 802343 1807487 := bstep (se 1 (by rfl) ⟨1355615, by rfl⟩ : syracuseStep 1807487 = 2711231) B2711231
theorem B6855151 : Blo 802343 6855151 := bstep (se 1 (by rfl) ⟨5141363, by rfl⟩ : syracuseStep 6855151 = 10282727) B10282727
theorem B1809179 : Blo 802343 1809179 := bstep (se 1 (by rfl) ⟨1356884, by rfl⟩ : syracuseStep 1809179 = 2713769) B2713769
theorem B2040299 : Blo 802343 2040299 := bstep (se 1 (by rfl) ⟨1530224, by rfl⟩ : syracuseStep 2040299 = 3060449) B3060449
theorem B99002573 : Blo 802343 99002573 := bstep (se 3 (by rfl) ⟨18562982, by rfl⟩ : syracuseStep 99002573 = 37125965) B37125965
theorem B13712489 : Blo 802343 13712489 := bstep (se 2 (by rfl) ⟨5142183, by rfl⟩ : syracuseStep 13712489 = 10284367) B10284367
theorem B4079159 : Blo 802343 4079159 := bstep (se 1 (by rfl) ⟨3059369, by rfl⟩ : syracuseStep 4079159 = 6118739) B6118739
theorem B7716815 : Blo 802343 7716815 := bstep (se 1 (by rfl) ⟨5787611, by rfl⟩ : syracuseStep 7716815 = 11575223) B11575223
theorem B6865235 : Blo 802343 6865235 := bstep (se 1 (by rfl) ⟨5148926, by rfl⟩ : syracuseStep 6865235 = 10297853) B10297853
theorem B20070989 : Blo 802343 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B3523895 : Blo 802343 3523895 := bstep (se 1 (by rfl) ⟨2642921, by rfl⟩ : syracuseStep 3523895 = 5285843) B5285843
theorem B4081427 : Blo 802343 4081427 := bstep (se 1 (by rfl) ⟨3061070, by rfl⟩ : syracuseStep 4081427 = 6122141) B6122141
theorem B1361915 : Blo 802343 1361915 := bstep (se 1 (by rfl) ⟨1021436, by rfl⟩ : syracuseStep 1361915 = 2042873) B2042873
theorem B2607785 : Blo 802343 2607785 := bstep (se 2 (by rfl) ⟨977919, by rfl⟩ : syracuseStep 2607785 = 1955839) B1955839
theorem B2903033 : Blo 802343 2903033 := bstep (se 2 (by rfl) ⟨1088637, by rfl⟩ : syracuseStep 2903033 = 2177275) B2177275
theorem B4575113 : Blo 802343 4575113 := bstep (se 2 (by rfl) ⟨1715667, by rfl⟩ : syracuseStep 4575113 = 3431335) B3431335
theorem B905935 : Blo 802343 905935 := bstep (se 1 (by rfl) ⟨679451, by rfl⟩ : syracuseStep 905935 = 1358903) B1358903
theorem B2710583 : Blo 802343 2710583 := bstep (se 1 (by rfl) ⟨2032937, by rfl⟩ : syracuseStep 2710583 = 4065875) B4065875
theorem B17882855 : Blo 802343 17882855 := bstep (se 1 (by rfl) ⟨13412141, by rfl⟩ : syracuseStep 17882855 = 26824283) B26824283
theorem B1204217 : Blo 802343 1204217 := bstep (se 2 (by rfl) ⟨451581, by rfl⟩ : syracuseStep 1204217 = 903163) B903163
theorem B1205183 : Blo 802343 1205183 := bstep (se 1 (by rfl) ⟨903887, by rfl⟩ : syracuseStep 1205183 = 1807775) B1807775
theorem B6350683 : Blo 802343 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B37154213 : Blo 802343 37154213 := bstep (se 4 (by rfl) ⟨3483207, by rfl⟩ : syracuseStep 37154213 = 6966415) B6966415
theorem B502559477 : Blo 802343 502559477 := bstep (se 5 (by rfl) ⟨23557475, by rfl⟩ : syracuseStep 502559477 = 47114951) B47114951
theorem B2291453 : Blo 802343 2291453 := bstep (se 3 (by rfl) ⟨429647, by rfl⟩ : syracuseStep 2291453 = 859295) B859295
theorem B3668969 : Blo 802343 3668969 := bstep (se 2 (by rfl) ⟨1375863, by rfl⟩ : syracuseStep 3668969 = 2751727) B2751727
theorem B13074023 : Blo 802343 13074023 := bstep (se 1 (by rfl) ⟨9805517, by rfl⟩ : syracuseStep 13074023 = 19611035) B19611035
theorem B2720951 : Blo 802343 2720951 := bstep (se 1 (by rfl) ⟨2040713, by rfl⟩ : syracuseStep 2720951 = 4081427) B4081427
theorem B1738523 : Blo 802343 1738523 := bstep (se 1 (by rfl) ⟨1303892, by rfl⟩ : syracuseStep 1738523 = 2607785) B2607785
theorem B1935355 : Blo 802343 1935355 := bstep (se 1 (by rfl) ⟨1451516, by rfl⟩ : syracuseStep 1935355 = 2903033) B2903033
theorem B3050075 : Blo 802343 3050075 := bstep (se 1 (by rfl) ⟨2287556, by rfl⟩ : syracuseStep 3050075 = 4575113) B4575113
theorem B1807055 : Blo 802343 1807055 := bstep (se 1 (by rfl) ⟨1355291, by rfl⟩ : syracuseStep 1807055 = 2710583) B2710583
theorem B66001715 : Blo 802343 66001715 := bstep (se 1 (by rfl) ⟨49501286, by rfl⟩ : syracuseStep 66001715 = 99002573) B99002573
theorem B13380659 : Blo 802343 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B8467577 : Blo 802343 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B5158025 : Blo 802343 5158025 := bstep (se 2 (by rfl) ⟨1934259, by rfl⟩ : syracuseStep 5158025 = 3868519) B3868519
theorem B78298973 : Blo 802343 78298973 := bstep (se 3 (by rfl) ⟨14681057, by rfl⟩ : syracuseStep 78298973 = 29362115) B29362115
theorem B802811 : Blo 802343 802811 := bstep (se 1 (by rfl) ⟨602108, by rfl⟩ : syracuseStep 802811 = 1204217) B1204217
theorem B1360199 : Blo 802343 1360199 := bstep (se 1 (by rfl) ⟨1020149, by rfl⟩ : syracuseStep 1360199 = 2040299) B2040299
theorem B803455 : Blo 802343 803455 := bstep (se 1 (by rfl) ⟨602591, by rfl⟩ : syracuseStep 803455 = 1205183) B1205183
theorem B335039651 : Blo 802343 335039651 := bstep (se 1 (by rfl) ⟨251279738, by rfl⟩ : syracuseStep 335039651 = 502559477) B502559477
theorem B1527635 : Blo 802343 1527635 := bstep (se 1 (by rfl) ⟨1145726, by rfl⟩ : syracuseStep 1527635 = 2291453) B2291453
theorem B2445979 : Blo 802343 2445979 := bstep (se 1 (by rfl) ⟨1834484, by rfl⟩ : syracuseStep 2445979 = 3668969) B3668969
theorem B4576823 : Blo 802343 4576823 := bstep (se 1 (by rfl) ⟨3432617, by rfl⟩ : syracuseStep 4576823 = 6865235) B6865235
theorem B2349263 : Blo 802343 2349263 := bstep (se 1 (by rfl) ⟨1761947, by rfl⟩ : syracuseStep 2349263 = 3523895) B3523895
theorem B907943 : Blo 802343 907943 := bstep (se 1 (by rfl) ⟨680957, by rfl⟩ : syracuseStep 907943 = 1361915) B1361915
theorem B11754665 : Blo 802343 11754665 := bstep (se 2 (by rfl) ⟨4407999, by rfl⟩ : syracuseStep 11754665 = 8815999) B8815999
theorem B225795995 : Blo 802343 225795995 := bstep (se 1 (by rfl) ⟨169346996, by rfl⟩ : syracuseStep 225795995 = 338693993) B338693993
theorem B1204271 : Blo 802343 1204271 := bstep (se 1 (by rfl) ⟨903203, by rfl⟩ : syracuseStep 1204271 = 1806407) B1806407
theorem B1204991 : Blo 802343 1204991 := bstep (se 1 (by rfl) ⟨903743, by rfl⟩ : syracuseStep 1204991 = 1807487) B1807487
theorem B1206119 : Blo 802343 1206119 := bstep (se 1 (by rfl) ⟨904589, by rfl⟩ : syracuseStep 1206119 = 1809179) B1809179
theorem B11921903 : Blo 802343 11921903 := bstep (se 1 (by rfl) ⟨8941427, by rfl⟩ : syracuseStep 11921903 = 17882855) B17882855
theorem B1207913 : Blo 802343 1207913 := bstep (se 2 (by rfl) ⟨452967, by rfl⟩ : syracuseStep 1207913 = 905935) B905935
theorem B24769475 : Blo 802343 24769475 := bstep (se 1 (by rfl) ⟨18577106, by rfl⟩ : syracuseStep 24769475 = 37154213) B37154213
theorem B9140201 : Blo 802343 9140201 := bstep (se 2 (by rfl) ⟨3427575, by rfl⟩ : syracuseStep 9140201 = 6855151) B6855151
theorem B9141659 : Blo 802343 9141659 := bstep (se 1 (by rfl) ⟨6856244, by rfl⟩ : syracuseStep 9141659 = 13712489) B13712489
theorem B2719439 : Blo 802343 2719439 := bstep (se 1 (by rfl) ⟨2039579, by rfl⟩ : syracuseStep 2719439 = 4079159) B4079159
theorem B8716015 : Blo 802343 8716015 := bstep (se 1 (by rfl) ⟨6537011, by rfl⟩ : syracuseStep 8716015 = 13074023) B13074023
theorem B5144543 : Blo 802343 5144543 := bstep (se 1 (by rfl) ⟨3858407, by rfl⟩ : syracuseStep 5144543 = 7716815) B7716815
theorem B2033383 : Blo 802343 2033383 := bstep (se 1 (by rfl) ⟨1525037, by rfl⟩ : syracuseStep 2033383 = 3050075) B3050075
theorem B1018423 : Blo 802343 1018423 := bstep (se 1 (by rfl) ⟨763817, by rfl⟩ : syracuseStep 1018423 = 1527635) B1527635
theorem B3051215 : Blo 802343 3051215 := bstep (se 1 (by rfl) ⟨2288411, by rfl⟩ : syracuseStep 3051215 = 4576823) B4576823
theorem B7836443 : Blo 802343 7836443 := bstep (se 1 (by rfl) ⟨5877332, by rfl⟩ : syracuseStep 7836443 = 11754665) B11754665
theorem B8920439 : Blo 802343 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B5645051 : Blo 802343 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B1812959 : Blo 802343 1812959 := bstep (se 1 (by rfl) ⟨1359719, by rfl⟩ : syracuseStep 1812959 = 2719439) B2719439
theorem B1813967 : Blo 802343 1813967 := bstep (se 1 (by rfl) ⟨1360475, by rfl⟩ : syracuseStep 1813967 = 2720951) B2720951
theorem B223359767 : Blo 802343 223359767 := bstep (se 1 (by rfl) ⟨167519825, by rfl⟩ : syracuseStep 223359767 = 335039651) B335039651
theorem B4636061 : Blo 802343 4636061 := bstep (se 3 (by rfl) ⟨869261, by rfl⟩ : syracuseStep 4636061 = 1738523) B1738523
theorem B802847 : Blo 802343 802847 := bstep (se 1 (by rfl) ⟨602135, by rfl⟩ : syracuseStep 802847 = 1204271) B1204271
theorem B803327 : Blo 802343 803327 := bstep (se 1 (by rfl) ⟨602495, by rfl⟩ : syracuseStep 803327 = 1204991) B1204991
theorem B3261305 : Blo 802343 3261305 := bstep (se 2 (by rfl) ⟨1222989, by rfl⟩ : syracuseStep 3261305 = 2445979) B2445979
theorem B804079 : Blo 802343 804079 := bstep (se 1 (by rfl) ⟨603059, by rfl⟩ : syracuseStep 804079 = 1206119) B1206119
theorem B7947935 : Blo 802343 7947935 := bstep (se 1 (by rfl) ⟨5960951, by rfl⟩ : syracuseStep 7947935 = 11921903) B11921903
theorem B805275 : Blo 802343 805275 := bstep (se 1 (by rfl) ⟨603956, by rfl⟩ : syracuseStep 805275 = 1207913) B1207913
theorem B11621353 : Blo 802343 11621353 := bstep (se 2 (by rfl) ⟨4358007, by rfl⟩ : syracuseStep 11621353 = 8716015) B8716015
theorem B3429695 : Blo 802343 3429695 := bstep (se 1 (by rfl) ⟨2572271, by rfl⟩ : syracuseStep 3429695 = 5144543) B5144543
theorem B906799 : Blo 802343 906799 := bstep (se 1 (by rfl) ⟨680099, by rfl⟩ : syracuseStep 906799 = 1360199) B1360199
theorem B2580473 : Blo 802343 2580473 := bstep (se 2 (by rfl) ⟨967677, by rfl⟩ : syracuseStep 2580473 = 1935355) B1935355
theorem B1204703 : Blo 802343 1204703 := bstep (se 1 (by rfl) ⟨903527, by rfl⟩ : syracuseStep 1204703 = 1807055) B1807055
theorem B1566175 : Blo 802343 1566175 := bstep (se 1 (by rfl) ⟨1174631, by rfl⟩ : syracuseStep 1566175 = 2349263) B2349263
theorem B44001143 : Blo 802343 44001143 := bstep (se 1 (by rfl) ⟨33000857, by rfl⟩ : syracuseStep 44001143 = 66001715) B66001715
theorem B150530663 : Blo 802343 150530663 := bstep (se 1 (by rfl) ⟨112897997, by rfl⟩ : syracuseStep 150530663 = 225795995) B225795995
theorem B2421181 : Blo 802343 2421181 := bstep (se 3 (by rfl) ⟨453971, by rfl⟩ : syracuseStep 2421181 = 907943) B907943
theorem B16512983 : Blo 802343 16512983 := bstep (se 1 (by rfl) ⟨12384737, by rfl⟩ : syracuseStep 16512983 = 24769475) B24769475
theorem B3438683 : Blo 802343 3438683 := bstep (se 1 (by rfl) ⟨2579012, by rfl⟩ : syracuseStep 3438683 = 5158025) B5158025
theorem B6093467 : Blo 802343 6093467 := bstep (se 1 (by rfl) ⟨4570100, by rfl⟩ : syracuseStep 6093467 = 9140201) B9140201
theorem B6094439 : Blo 802343 6094439 := bstep (se 1 (by rfl) ⟨4570829, by rfl⟩ : syracuseStep 6094439 = 9141659) B9141659
theorem B52199315 : Blo 802343 52199315 := bstep (se 1 (by rfl) ⟨39149486, by rfl⟩ : syracuseStep 52199315 = 78298973) B78298973
theorem B12912965 : Blo 802343 12912965 := bstep (se 4 (by rfl) ⟨1210590, by rfl⟩ : syracuseStep 12912965 = 2421181) B2421181
theorem B2034143 : Blo 802343 2034143 := bstep (se 1 (by rfl) ⟨1525607, by rfl⟩ : syracuseStep 2034143 = 3051215) B3051215
theorem B29334095 : Blo 802343 29334095 := bstep (se 1 (by rfl) ⟨22000571, by rfl⟩ : syracuseStep 29334095 = 44001143) B44001143
theorem B401415101 : Blo 802343 401415101 := bstep (se 3 (by rfl) ⟨75265331, by rfl⟩ : syracuseStep 401415101 = 150530663) B150530663
theorem B148906511 : Blo 802343 148906511 := bstep (se 1 (by rfl) ⟨111679883, by rfl⟩ : syracuseStep 148906511 = 223359767) B223359767
theorem B3090707 : Blo 802343 3090707 := bstep (se 1 (by rfl) ⟨2318030, by rfl⟩ : syracuseStep 3090707 = 4636061) B4636061
theorem B2174203 : Blo 802343 2174203 := bstep (se 1 (by rfl) ⟨1630652, by rfl⟩ : syracuseStep 2174203 = 3261305) B3261305
theorem B5224295 : Blo 802343 5224295 := bstep (se 1 (by rfl) ⟨3918221, by rfl⟩ : syracuseStep 5224295 = 7836443) B7836443
theorem B1357897 : Blo 802343 1357897 := bstep (se 2 (by rfl) ⟨509211, by rfl⟩ : syracuseStep 1357897 = 1018423) B1018423
theorem B5946959 : Blo 802343 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B1720315 : Blo 802343 1720315 := bstep (se 1 (by rfl) ⟨1290236, by rfl⟩ : syracuseStep 1720315 = 2580473) B2580473
theorem B803135 : Blo 802343 803135 := bstep (se 1 (by rfl) ⟨602351, by rfl⟩ : syracuseStep 803135 = 1204703) B1204703
theorem B5298623 : Blo 802343 5298623 := bstep (se 1 (by rfl) ⟨3973967, by rfl⟩ : syracuseStep 5298623 = 7947935) B7947935
theorem B2088233 : Blo 802343 2088233 := bstep (se 2 (by rfl) ⟨783087, by rfl⟩ : syracuseStep 2088233 = 1566175) B1566175
theorem B2711177 : Blo 802343 2711177 := bstep (se 2 (by rfl) ⟨1016691, by rfl⟩ : syracuseStep 2711177 = 2033383) B2033383
theorem B2286463 : Blo 802343 2286463 := bstep (se 1 (by rfl) ⟨1714847, by rfl⟩ : syracuseStep 2286463 = 3429695) B3429695
theorem B3763367 : Blo 802343 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B15495137 : Blo 802343 15495137 := bstep (se 2 (by rfl) ⟨5810676, by rfl⟩ : syracuseStep 15495137 = 11621353) B11621353
theorem B1208639 : Blo 802343 1208639 := bstep (se 1 (by rfl) ⟨906479, by rfl⟩ : syracuseStep 1208639 = 1812959) B1812959
theorem B1209065 : Blo 802343 1209065 := bstep (se 2 (by rfl) ⟨453399, by rfl⟩ : syracuseStep 1209065 = 906799) B906799
theorem B1209311 : Blo 802343 1209311 := bstep (se 1 (by rfl) ⟨906983, by rfl⟩ : syracuseStep 1209311 = 1813967) B1813967
theorem B11008655 : Blo 802343 11008655 := bstep (se 1 (by rfl) ⟨8256491, by rfl⟩ : syracuseStep 11008655 = 16512983) B16512983
theorem B2292455 : Blo 802343 2292455 := bstep (se 1 (by rfl) ⟨1719341, by rfl⟩ : syracuseStep 2292455 = 3438683) B3438683
theorem B4062311 : Blo 802343 4062311 := bstep (se 1 (by rfl) ⟨3046733, by rfl⟩ : syracuseStep 4062311 = 6093467) B6093467
theorem B4062959 : Blo 802343 4062959 := bstep (se 1 (by rfl) ⟨3047219, by rfl⟩ : syracuseStep 4062959 = 6094439) B6094439
theorem B34799543 : Blo 802343 34799543 := bstep (se 1 (by rfl) ⟨26099657, by rfl⟩ : syracuseStep 34799543 = 52199315) B52199315
theorem B3048617 : Blo 802343 3048617 := bstep (se 2 (by rfl) ⟨1143231, by rfl⟩ : syracuseStep 3048617 = 2286463) B2286463
theorem B13931453 : Blo 802343 13931453 := bstep (se 3 (by rfl) ⟨2612147, by rfl⟩ : syracuseStep 13931453 = 5224295) B5224295
theorem B1807451 : Blo 802343 1807451 := bstep (se 1 (by rfl) ⟨1355588, by rfl⟩ : syracuseStep 1807451 = 2711177) B2711177
theorem B10330091 : Blo 802343 10330091 := bstep (se 1 (by rfl) ⟨7747568, by rfl⟩ : syracuseStep 10330091 = 15495137) B15495137
theorem B1810529 : Blo 802343 1810529 := bstep (se 2 (by rfl) ⟨678948, by rfl⟩ : syracuseStep 1810529 = 1357897) B1357897
theorem B1356095 : Blo 802343 1356095 := bstep (se 1 (by rfl) ⟨1017071, by rfl⟩ : syracuseStep 1356095 = 2034143) B2034143
theorem B2898937 : Blo 802343 2898937 := bstep (se 2 (by rfl) ⟨1087101, by rfl⟩ : syracuseStep 2898937 = 2174203) B2174203
theorem B1392155 : Blo 802343 1392155 := bstep (se 1 (by rfl) ⟨1044116, by rfl⟩ : syracuseStep 1392155 = 2088233) B2088233
theorem B99271007 : Blo 802343 99271007 := bstep (se 1 (by rfl) ⟨74453255, by rfl⟩ : syracuseStep 99271007 = 148906511) B148906511
theorem B2508911 : Blo 802343 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B805759 : Blo 802343 805759 := bstep (se 1 (by rfl) ⟨604319, by rfl⟩ : syracuseStep 805759 = 1208639) B1208639
theorem B806043 : Blo 802343 806043 := bstep (se 1 (by rfl) ⟨604532, by rfl⟩ : syracuseStep 806043 = 1209065) B1209065
theorem B806207 : Blo 802343 806207 := bstep (se 1 (by rfl) ⟨604655, by rfl⟩ : syracuseStep 806207 = 1209311) B1209311
theorem B1528303 : Blo 802343 1528303 := bstep (se 1 (by rfl) ⟨1146227, by rfl⟩ : syracuseStep 1528303 = 2292455) B2292455
theorem B2708207 : Blo 802343 2708207 := bstep (se 1 (by rfl) ⟨2031155, by rfl⟩ : syracuseStep 2708207 = 4062311) B4062311
theorem B2708639 : Blo 802343 2708639 := bstep (se 1 (by rfl) ⟨2031479, by rfl⟩ : syracuseStep 2708639 = 4062959) B4062959
theorem B8608643 : Blo 802343 8608643 := bstep (se 1 (by rfl) ⟨6456482, by rfl⟩ : syracuseStep 8608643 = 12912965) B12912965
theorem B3532415 : Blo 802343 3532415 := bstep (se 1 (by rfl) ⟨2649311, by rfl⟩ : syracuseStep 3532415 = 5298623) B5298623
theorem B19556063 : Blo 802343 19556063 := bstep (se 1 (by rfl) ⟨14667047, by rfl⟩ : syracuseStep 19556063 = 29334095) B29334095
theorem B267610067 : Blo 802343 267610067 := bstep (se 1 (by rfl) ⟨200707550, by rfl⟩ : syracuseStep 267610067 = 401415101) B401415101
theorem B2060471 : Blo 802343 2060471 := bstep (se 1 (by rfl) ⟨1545353, by rfl⟩ : syracuseStep 2060471 = 3090707) B3090707
theorem B7339103 : Blo 802343 7339103 := bstep (se 1 (by rfl) ⟨5504327, by rfl⟩ : syracuseStep 7339103 = 11008655) B11008655
theorem B3964639 : Blo 802343 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B23199695 : Blo 802343 23199695 := bstep (se 1 (by rfl) ⟨17399771, by rfl⟩ : syracuseStep 23199695 = 34799543) B34799543
theorem B2293753 : Blo 802343 2293753 := bstep (se 2 (by rfl) ⟨860157, by rfl⟩ : syracuseStep 2293753 = 1720315) B1720315
theorem B2032411 : Blo 802343 2032411 := bstep (se 1 (by rfl) ⟨1524308, by rfl⟩ : syracuseStep 2032411 = 3048617) B3048617
theorem B1672607 : Blo 802343 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B1805471 : Blo 802343 1805471 := bstep (se 1 (by rfl) ⟨1354103, by rfl⟩ : syracuseStep 1805471 = 2708207) B2708207
theorem B1805759 : Blo 802343 1805759 := bstep (se 1 (by rfl) ⟨1354319, by rfl⟩ : syracuseStep 1805759 = 2708639) B2708639
theorem B5739095 : Blo 802343 5739095 := bstep (se 1 (by rfl) ⟨4304321, by rfl⟩ : syracuseStep 5739095 = 8608643) B8608643
theorem B6886727 : Blo 802343 6886727 := bstep (se 1 (by rfl) ⟨5165045, by rfl⟩ : syracuseStep 6886727 = 10330091) B10330091
theorem B2037737 : Blo 802343 2037737 := bstep (se 2 (by rfl) ⟨764151, by rfl⟩ : syracuseStep 2037737 = 1528303) B1528303
theorem B4892735 : Blo 802343 4892735 := bstep (se 1 (by rfl) ⟨3669551, by rfl⟩ : syracuseStep 4892735 = 7339103) B7339103
theorem B5286185 : Blo 802343 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B928103 : Blo 802343 928103 := bstep (se 1 (by rfl) ⟨696077, by rfl⟩ : syracuseStep 928103 = 1392155) B1392155
theorem B3058337 : Blo 802343 3058337 := bstep (se 2 (by rfl) ⟨1146876, by rfl⟩ : syracuseStep 3058337 = 2293753) B2293753
theorem B9287635 : Blo 802343 9287635 := bstep (se 1 (by rfl) ⟨6965726, by rfl⟩ : syracuseStep 9287635 = 13931453) B13931453
theorem B178406711 : Blo 802343 178406711 := bstep (se 1 (by rfl) ⟨133805033, by rfl⟩ : syracuseStep 178406711 = 267610067) B267610067
theorem B904063 : Blo 802343 904063 := bstep (se 1 (by rfl) ⟨678047, by rfl⟩ : syracuseStep 904063 = 1356095) B1356095
theorem B66180671 : Blo 802343 66180671 := bstep (se 1 (by rfl) ⟨49635503, by rfl⟩ : syracuseStep 66180671 = 99271007) B99271007
theorem B1204967 : Blo 802343 1204967 := bstep (se 1 (by rfl) ⟨903725, by rfl⟩ : syracuseStep 1204967 = 1807451) B1807451
theorem B1207019 : Blo 802343 1207019 := bstep (se 1 (by rfl) ⟨905264, by rfl⟩ : syracuseStep 1207019 = 1810529) B1810529
theorem B13037375 : Blo 802343 13037375 := bstep (se 1 (by rfl) ⟨9778031, by rfl⟩ : syracuseStep 13037375 = 19556063) B19556063
theorem B37679093 : Blo 802343 37679093 := bstep (se 5 (by rfl) ⟨1766207, by rfl⟩ : syracuseStep 37679093 = 3532415) B3532415
theorem B1373647 : Blo 802343 1373647 := bstep (se 1 (by rfl) ⟨1030235, by rfl⟩ : syracuseStep 1373647 = 2060471) B2060471
theorem B3865249 : Blo 802343 3865249 := bstep (se 2 (by rfl) ⟨1449468, by rfl⟩ : syracuseStep 3865249 = 2898937) B2898937
theorem B15466463 : Blo 802343 15466463 := bstep (se 1 (by rfl) ⟨11599847, by rfl⟩ : syracuseStep 15466463 = 23199695) B23199695
theorem B20614661 : Blo 802343 20614661 := bstep (se 4 (by rfl) ⟨1932624, by rfl⟩ : syracuseStep 20614661 = 3865249) B3865249
theorem B4591151 : Blo 802343 4591151 := bstep (se 1 (by rfl) ⟨3443363, by rfl⟩ : syracuseStep 4591151 = 6886727) B6886727
theorem B9899765 : Blo 802343 9899765 := bstep (se 5 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 9899765 = 928103) B928103
theorem B4460285 : Blo 802343 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B13047293 : Blo 802343 13047293 := bstep (se 3 (by rfl) ⟨2446367, by rfl⟩ : syracuseStep 13047293 = 4892735) B4892735
theorem B2038891 : Blo 802343 2038891 := bstep (se 1 (by rfl) ⟨1529168, by rfl⟩ : syracuseStep 2038891 = 3058337) B3058337
theorem B8691583 : Blo 802343 8691583 := bstep (se 1 (by rfl) ⟨6518687, by rfl⟩ : syracuseStep 8691583 = 13037375) B13037375
theorem B44120447 : Blo 802343 44120447 := bstep (se 1 (by rfl) ⟨33090335, by rfl⟩ : syracuseStep 44120447 = 66180671) B66180671
theorem B1358491 : Blo 802343 1358491 := bstep (se 1 (by rfl) ⟨1018868, by rfl⟩ : syracuseStep 1358491 = 2037737) B2037737
theorem B803311 : Blo 802343 803311 := bstep (se 1 (by rfl) ⟨602483, by rfl⟩ : syracuseStep 803311 = 1204967) B1204967
theorem B3524123 : Blo 802343 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B804679 : Blo 802343 804679 := bstep (se 1 (by rfl) ⟨603509, by rfl⟩ : syracuseStep 804679 = 1207019) B1207019
theorem B25119395 : Blo 802343 25119395 := bstep (se 1 (by rfl) ⟨18839546, by rfl⟩ : syracuseStep 25119395 = 37679093) B37679093
theorem B10310975 : Blo 802343 10310975 := bstep (se 1 (by rfl) ⟨7733231, by rfl⟩ : syracuseStep 10310975 = 15466463) B15466463
theorem B118937807 : Blo 802343 118937807 := bstep (se 1 (by rfl) ⟨89203355, by rfl⟩ : syracuseStep 118937807 = 178406711) B178406711
theorem B2709881 : Blo 802343 2709881 := bstep (se 2 (by rfl) ⟨1016205, by rfl⟩ : syracuseStep 2709881 = 2032411) B2032411
theorem B1203647 : Blo 802343 1203647 := bstep (se 1 (by rfl) ⟨902735, by rfl⟩ : syracuseStep 1203647 = 1805471) B1805471
theorem B1203839 : Blo 802343 1203839 := bstep (se 1 (by rfl) ⟨902879, by rfl⟩ : syracuseStep 1203839 = 1805759) B1805759
theorem B3826063 : Blo 802343 3826063 := bstep (se 1 (by rfl) ⟨2869547, by rfl⟩ : syracuseStep 3826063 = 5739095) B5739095
theorem B1205417 : Blo 802343 1205417 := bstep (se 2 (by rfl) ⟨452031, by rfl⟩ : syracuseStep 1205417 = 904063) B904063
theorem B1831529 : Blo 802343 1831529 := bstep (se 2 (by rfl) ⟨686823, by rfl⟩ : syracuseStep 1831529 = 1373647) B1373647
theorem B12383513 : Blo 802343 12383513 := bstep (se 2 (by rfl) ⟨4643817, by rfl⟩ : syracuseStep 12383513 = 9287635) B9287635
theorem B4884077 : Blo 802343 4884077 := bstep (se 3 (by rfl) ⟨915764, by rfl⟩ : syracuseStep 4884077 = 1831529) B1831529
theorem B16746263 : Blo 802343 16746263 := bstep (se 1 (by rfl) ⟨12559697, by rfl⟩ : syracuseStep 16746263 = 25119395) B25119395
theorem B1806587 : Blo 802343 1806587 := bstep (se 1 (by rfl) ⟨1354940, by rfl⟩ : syracuseStep 1806587 = 2709881) B2709881
theorem B1811321 : Blo 802343 1811321 := bstep (se 2 (by rfl) ⟨679245, by rfl⟩ : syracuseStep 1811321 = 1358491) B1358491
theorem B13743107 : Blo 802343 13743107 := bstep (se 1 (by rfl) ⟨10307330, by rfl⟩ : syracuseStep 13743107 = 20614661) B20614661
theorem B3060767 : Blo 802343 3060767 := bstep (se 1 (by rfl) ⟨2295575, by rfl⟩ : syracuseStep 3060767 = 4591151) B4591151
theorem B6599843 : Blo 802343 6599843 := bstep (se 1 (by rfl) ⟨4949882, by rfl⟩ : syracuseStep 6599843 = 9899765) B9899765
theorem B8698195 : Blo 802343 8698195 := bstep (se 1 (by rfl) ⟨6523646, by rfl⟩ : syracuseStep 8698195 = 13047293) B13047293
theorem B802431 : Blo 802343 802431 := bstep (se 1 (by rfl) ⟨601823, by rfl⟩ : syracuseStep 802431 = 1203647) B1203647
theorem B802559 : Blo 802343 802559 := bstep (se 1 (by rfl) ⟨601919, by rfl⟩ : syracuseStep 802559 = 1203839) B1203839
theorem B803611 : Blo 802343 803611 := bstep (se 1 (by rfl) ⟨602708, by rfl⟩ : syracuseStep 803611 = 1205417) B1205417
theorem B29413631 : Blo 802343 29413631 := bstep (se 1 (by rfl) ⟨22060223, by rfl⟩ : syracuseStep 29413631 = 44120447) B44120447
theorem B11588777 : Blo 802343 11588777 := bstep (se 2 (by rfl) ⟨4345791, by rfl⟩ : syracuseStep 11588777 = 8691583) B8691583
theorem B5101417 : Blo 802343 5101417 := bstep (se 2 (by rfl) ⟨1913031, by rfl⟩ : syracuseStep 5101417 = 3826063) B3826063
theorem B2349415 : Blo 802343 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B2973523 : Blo 802343 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B6873983 : Blo 802343 6873983 := bstep (se 1 (by rfl) ⟨5155487, by rfl⟩ : syracuseStep 6873983 = 10310975) B10310975
theorem B79291871 : Blo 802343 79291871 := bstep (se 1 (by rfl) ⟨59468903, by rfl⟩ : syracuseStep 79291871 = 118937807) B118937807
theorem B8255675 : Blo 802343 8255675 := bstep (se 1 (by rfl) ⟨6191756, by rfl⟩ : syracuseStep 8255675 = 12383513) B12383513
theorem B2718521 : Blo 802343 2718521 := bstep (se 2 (by rfl) ⟨1019445, by rfl⟩ : syracuseStep 2718521 = 2038891) B2038891
theorem B52861247 : Blo 802343 52861247 := bstep (se 1 (by rfl) ⟨39645935, by rfl⟩ : syracuseStep 52861247 = 79291871) B79291871
theorem B2040511 : Blo 802343 2040511 := bstep (se 1 (by rfl) ⟨1530383, by rfl⟩ : syracuseStep 2040511 = 3060767) B3060767
theorem B4399895 : Blo 802343 4399895 := bstep (se 1 (by rfl) ⟨3299921, by rfl⟩ : syracuseStep 4399895 = 6599843) B6599843
theorem B1812347 : Blo 802343 1812347 := bstep (se 1 (by rfl) ⟨1359260, by rfl⟩ : syracuseStep 1812347 = 2718521) B2718521
theorem B3256051 : Blo 802343 3256051 := bstep (se 1 (by rfl) ⟨2442038, by rfl⟩ : syracuseStep 3256051 = 4884077) B4884077
theorem B12530213 : Blo 802343 12530213 := bstep (se 4 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 12530213 = 2349415) B2349415
theorem B19609087 : Blo 802343 19609087 := bstep (se 1 (by rfl) ⟨14706815, by rfl⟩ : syracuseStep 19609087 = 29413631) B29413631
theorem B6801889 : Blo 802343 6801889 := bstep (se 2 (by rfl) ⟨2550708, by rfl⟩ : syracuseStep 6801889 = 5101417) B5101417
theorem B9162071 : Blo 802343 9162071 := bstep (se 1 (by rfl) ⟨6871553, by rfl⟩ : syracuseStep 9162071 = 13743107) B13743107
theorem B11164175 : Blo 802343 11164175 := bstep (se 1 (by rfl) ⟨8373131, by rfl⟩ : syracuseStep 11164175 = 16746263) B16746263
theorem B1204391 : Blo 802343 1204391 := bstep (se 1 (by rfl) ⟨903293, by rfl⟩ : syracuseStep 1204391 = 1806587) B1806587
theorem B7725851 : Blo 802343 7725851 := bstep (se 1 (by rfl) ⟨5794388, by rfl⟩ : syracuseStep 7725851 = 11588777) B11588777
theorem B1207547 : Blo 802343 1207547 := bstep (se 1 (by rfl) ⟨905660, by rfl⟩ : syracuseStep 1207547 = 1811321) B1811321
theorem B4582655 : Blo 802343 4582655 := bstep (se 1 (by rfl) ⟨3436991, by rfl⟩ : syracuseStep 4582655 = 6873983) B6873983
theorem B11597593 : Blo 802343 11597593 := bstep (se 2 (by rfl) ⟨4349097, by rfl⟩ : syracuseStep 11597593 = 8698195) B8698195
theorem B5503783 : Blo 802343 5503783 := bstep (se 1 (by rfl) ⟨4127837, by rfl⟩ : syracuseStep 5503783 = 8255675) B8255675
theorem B3964697 : Blo 802343 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B2720681 : Blo 802343 2720681 := bstep (se 2 (by rfl) ⟨1020255, by rfl⟩ : syracuseStep 2720681 = 2040511) B2040511
theorem B7442783 : Blo 802343 7442783 := bstep (se 1 (by rfl) ⟨5582087, by rfl⟩ : syracuseStep 7442783 = 11164175) B11164175
theorem B5150567 : Blo 802343 5150567 := bstep (se 1 (by rfl) ⟨3862925, by rfl⟩ : syracuseStep 5150567 = 7725851) B7725851
theorem B3055103 : Blo 802343 3055103 := bstep (se 1 (by rfl) ⟨2291327, by rfl⟩ : syracuseStep 3055103 = 4582655) B4582655
theorem B6108047 : Blo 802343 6108047 := bstep (se 1 (by rfl) ⟨4581035, by rfl⟩ : syracuseStep 6108047 = 9162071) B9162071
theorem B35240831 : Blo 802343 35240831 := bstep (se 1 (by rfl) ⟨26430623, by rfl⟩ : syracuseStep 35240831 = 52861247) B52861247
theorem B4341401 : Blo 802343 4341401 := bstep (se 2 (by rfl) ⟨1628025, by rfl⟩ : syracuseStep 4341401 = 3256051) B3256051
theorem B802927 : Blo 802343 802927 := bstep (se 1 (by rfl) ⟨602195, by rfl⟩ : syracuseStep 802927 = 1204391) B1204391
theorem B2933263 : Blo 802343 2933263 := bstep (se 1 (by rfl) ⟨2199947, by rfl⟩ : syracuseStep 2933263 = 4399895) B4399895
theorem B805031 : Blo 802343 805031 := bstep (se 1 (by rfl) ⟨603773, by rfl⟩ : syracuseStep 805031 = 1207547) B1207547
theorem B2643131 : Blo 802343 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B9069185 : Blo 802343 9069185 := bstep (se 2 (by rfl) ⟨3400944, by rfl⟩ : syracuseStep 9069185 = 6801889) B6801889
theorem B1208231 : Blo 802343 1208231 := bstep (se 1 (by rfl) ⟨906173, by rfl⟩ : syracuseStep 1208231 = 1812347) B1812347
theorem B26145449 : Blo 802343 26145449 := bstep (se 2 (by rfl) ⟨9804543, by rfl⟩ : syracuseStep 26145449 = 19609087) B19609087
theorem B15463457 : Blo 802343 15463457 := bstep (se 2 (by rfl) ⟨5798796, by rfl⟩ : syracuseStep 15463457 = 11597593) B11597593
theorem B8353475 : Blo 802343 8353475 := bstep (se 1 (by rfl) ⟨6265106, by rfl⟩ : syracuseStep 8353475 = 12530213) B12530213
theorem B7338377 : Blo 802343 7338377 := bstep (se 2 (by rfl) ⟨2751891, by rfl⟩ : syracuseStep 7338377 = 5503783) B5503783
theorem B2036735 : Blo 802343 2036735 := bstep (se 1 (by rfl) ⟨1527551, by rfl⟩ : syracuseStep 2036735 = 3055103) B3055103
theorem B4072031 : Blo 802343 4072031 := bstep (se 1 (by rfl) ⟨3054023, by rfl⟩ : syracuseStep 4072031 = 6108047) B6108047
theorem B4892251 : Blo 802343 4892251 := bstep (se 1 (by rfl) ⟨3669188, by rfl⟩ : syracuseStep 4892251 = 7338377) B7338377
theorem B2894267 : Blo 802343 2894267 := bstep (se 1 (by rfl) ⟨2170700, by rfl⟩ : syracuseStep 2894267 = 4341401) B4341401
theorem B1813787 : Blo 802343 1813787 := bstep (se 1 (by rfl) ⟨1360340, by rfl⟩ : syracuseStep 1813787 = 2720681) B2720681
theorem B3911017 : Blo 802343 3911017 := bstep (se 2 (by rfl) ⟨1466631, by rfl⟩ : syracuseStep 3911017 = 2933263) B2933263
theorem B4961855 : Blo 802343 4961855 := bstep (se 1 (by rfl) ⟨3721391, by rfl⟩ : syracuseStep 4961855 = 7442783) B7442783
theorem B6046123 : Blo 802343 6046123 := bstep (se 1 (by rfl) ⟨4534592, by rfl⟩ : syracuseStep 6046123 = 9069185) B9069185
theorem B805487 : Blo 802343 805487 := bstep (se 1 (by rfl) ⟨604115, by rfl⟩ : syracuseStep 805487 = 1208231) B1208231
theorem B10308971 : Blo 802343 10308971 := bstep (se 1 (by rfl) ⟨7731728, by rfl⟩ : syracuseStep 10308971 = 15463457) B15463457
theorem B1762087 : Blo 802343 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B3433711 : Blo 802343 3433711 := bstep (se 1 (by rfl) ⟨2575283, by rfl⟩ : syracuseStep 3433711 = 5150567) B5150567
theorem B17430299 : Blo 802343 17430299 := bstep (se 1 (by rfl) ⟨13072724, by rfl⟩ : syracuseStep 17430299 = 26145449) B26145449
theorem B5568983 : Blo 802343 5568983 := bstep (se 1 (by rfl) ⟨4176737, by rfl⟩ : syracuseStep 5568983 = 8353475) B8353475
theorem B23493887 : Blo 802343 23493887 := bstep (se 1 (by rfl) ⟨17620415, by rfl⟩ : syracuseStep 23493887 = 35240831) B35240831
theorem B8061497 : Blo 802343 8061497 := bstep (se 2 (by rfl) ⟨3023061, by rfl⟩ : syracuseStep 8061497 = 6046123) B6046123
theorem B6523001 : Blo 802343 6523001 := bstep (se 2 (by rfl) ⟨2446125, by rfl⟩ : syracuseStep 6523001 = 4892251) B4892251
theorem B5214689 : Blo 802343 5214689 := bstep (se 2 (by rfl) ⟨1955508, by rfl⟩ : syracuseStep 5214689 = 3911017) B3911017
theorem B3712655 : Blo 802343 3712655 := bstep (se 1 (by rfl) ⟨2784491, by rfl⟩ : syracuseStep 3712655 = 5568983) B5568983
theorem B1357823 : Blo 802343 1357823 := bstep (se 1 (by rfl) ⟨1018367, by rfl⟩ : syracuseStep 1357823 = 2036735) B2036735
theorem B11620199 : Blo 802343 11620199 := bstep (se 1 (by rfl) ⟨8715149, by rfl⟩ : syracuseStep 11620199 = 17430299) B17430299
theorem B2349449 : Blo 802343 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B4578281 : Blo 802343 4578281 := bstep (se 2 (by rfl) ⟨1716855, by rfl⟩ : syracuseStep 4578281 = 3433711) B3433711
theorem B6872647 : Blo 802343 6872647 := bstep (se 1 (by rfl) ⟨5154485, by rfl⟩ : syracuseStep 6872647 = 10308971) B10308971
theorem B13231613 : Blo 802343 13231613 := bstep (se 3 (by rfl) ⟨2480927, by rfl⟩ : syracuseStep 13231613 = 4961855) B4961855
theorem B2714687 : Blo 802343 2714687 := bstep (se 1 (by rfl) ⟨2036015, by rfl⟩ : syracuseStep 2714687 = 4072031) B4072031
theorem B1929511 : Blo 802343 1929511 := bstep (se 1 (by rfl) ⟨1447133, by rfl⟩ : syracuseStep 1929511 = 2894267) B2894267
theorem B1209191 : Blo 802343 1209191 := bstep (se 1 (by rfl) ⟨906893, by rfl⟩ : syracuseStep 1209191 = 1813787) B1813787
theorem B15662591 : Blo 802343 15662591 := bstep (se 1 (by rfl) ⟨11746943, by rfl⟩ : syracuseStep 15662591 = 23493887) B23493887
theorem B5374331 : Blo 802343 5374331 := bstep (se 1 (by rfl) ⟨4030748, by rfl⟩ : syracuseStep 5374331 = 8061497) B8061497
theorem B10290725 : Blo 802343 10290725 := bstep (se 4 (by rfl) ⟨964755, by rfl⟩ : syracuseStep 10290725 = 1929511) B1929511
theorem B3476459 : Blo 802343 3476459 := bstep (se 1 (by rfl) ⟨2607344, by rfl⟩ : syracuseStep 3476459 = 5214689) B5214689
theorem B9900413 : Blo 802343 9900413 := bstep (se 3 (by rfl) ⟨1856327, by rfl⟩ : syracuseStep 9900413 = 3712655) B3712655
theorem B3052187 : Blo 802343 3052187 := bstep (se 1 (by rfl) ⟨2289140, by rfl⟩ : syracuseStep 3052187 = 4578281) B4578281
theorem B1809791 : Blo 802343 1809791 := bstep (se 1 (by rfl) ⟨1357343, by rfl⟩ : syracuseStep 1809791 = 2714687) B2714687
theorem B7746799 : Blo 802343 7746799 := bstep (se 1 (by rfl) ⟨5810099, by rfl⟩ : syracuseStep 7746799 = 11620199) B11620199
theorem B806127 : Blo 802343 806127 := bstep (se 1 (by rfl) ⟨604595, by rfl⟩ : syracuseStep 806127 = 1209191) B1209191
theorem B905215 : Blo 802343 905215 := bstep (se 1 (by rfl) ⟨678911, by rfl⟩ : syracuseStep 905215 = 1357823) B1357823
theorem B9163529 : Blo 802343 9163529 := bstep (se 2 (by rfl) ⟨3436323, by rfl⟩ : syracuseStep 9163529 = 6872647) B6872647
theorem B10441727 : Blo 802343 10441727 := bstep (se 1 (by rfl) ⟨7831295, by rfl⟩ : syracuseStep 10441727 = 15662591) B15662591
theorem B4348667 : Blo 802343 4348667 := bstep (se 1 (by rfl) ⟨3261500, by rfl⟩ : syracuseStep 4348667 = 6523001) B6523001
theorem B35284301 : Blo 802343 35284301 := bstep (se 3 (by rfl) ⟨6615806, by rfl⟩ : syracuseStep 35284301 = 13231613) B13231613
theorem B1566299 : Blo 802343 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B2034791 : Blo 802343 2034791 := bstep (se 1 (by rfl) ⟨1526093, by rfl⟩ : syracuseStep 2034791 = 3052187) B3052187
theorem B10329065 : Blo 802343 10329065 := bstep (se 2 (by rfl) ⟨3873399, by rfl⟩ : syracuseStep 10329065 = 7746799) B7746799
theorem B3582887 : Blo 802343 3582887 := bstep (se 1 (by rfl) ⟨2687165, by rfl⟩ : syracuseStep 3582887 = 5374331) B5374331
theorem B6860483 : Blo 802343 6860483 := bstep (se 1 (by rfl) ⟨5145362, by rfl⟩ : syracuseStep 6860483 = 10290725) B10290725
theorem B6600275 : Blo 802343 6600275 := bstep (se 1 (by rfl) ⟨4950206, by rfl⟩ : syracuseStep 6600275 = 9900413) B9900413
theorem B6109019 : Blo 802343 6109019 := bstep (se 1 (by rfl) ⟨4581764, by rfl⟩ : syracuseStep 6109019 = 9163529) B9163529
theorem B6961151 : Blo 802343 6961151 := bstep (se 1 (by rfl) ⟨5220863, by rfl⟩ : syracuseStep 6961151 = 10441727) B10441727
theorem B1206527 : Blo 802343 1206527 := bstep (se 1 (by rfl) ⟨904895, by rfl⟩ : syracuseStep 1206527 = 1809791) B1809791
theorem B1206953 : Blo 802343 1206953 := bstep (se 2 (by rfl) ⟨452607, by rfl⟩ : syracuseStep 1206953 = 905215) B905215
theorem B23522867 : Blo 802343 23522867 := bstep (se 1 (by rfl) ⟨17642150, by rfl⟩ : syracuseStep 23522867 = 35284301) B35284301
theorem B1044199 : Blo 802343 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B11596445 : Blo 802343 11596445 := bstep (se 3 (by rfl) ⟨2174333, by rfl⟩ : syracuseStep 11596445 = 4348667) B4348667
theorem B9270557 : Blo 802343 9270557 := bstep (se 3 (by rfl) ⟨1738229, by rfl⟩ : syracuseStep 9270557 = 3476459) B3476459
theorem B6886043 : Blo 802343 6886043 := bstep (se 1 (by rfl) ⟨5164532, by rfl⟩ : syracuseStep 6886043 = 10329065) B10329065
theorem B250910581 : Blo 802343 250910581 := bstep (se 5 (by rfl) ⟨11761433, by rfl⟩ : syracuseStep 250910581 = 23522867) B23522867
theorem B4400183 : Blo 802343 4400183 := bstep (se 1 (by rfl) ⟨3300137, by rfl⟩ : syracuseStep 4400183 = 6600275) B6600275
theorem B4072679 : Blo 802343 4072679 := bstep (se 1 (by rfl) ⟨3054509, by rfl⟩ : syracuseStep 4072679 = 6109019) B6109019
theorem B1356527 : Blo 802343 1356527 := bstep (se 1 (by rfl) ⟨1017395, by rfl⟩ : syracuseStep 1356527 = 2034791) B2034791
theorem B1392265 : Blo 802343 1392265 := bstep (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) B1044199
theorem B18563069 : Blo 802343 18563069 := bstep (se 3 (by rfl) ⟨3480575, by rfl⟩ : syracuseStep 18563069 = 6961151) B6961151
theorem B804351 : Blo 802343 804351 := bstep (se 1 (by rfl) ⟨603263, by rfl⟩ : syracuseStep 804351 = 1206527) B1206527
theorem B804635 : Blo 802343 804635 := bstep (se 1 (by rfl) ⟨603476, by rfl⟩ : syracuseStep 804635 = 1206953) B1206953
theorem B9554365 : Blo 802343 9554365 := bstep (se 3 (by rfl) ⟨1791443, by rfl⟩ : syracuseStep 9554365 = 3582887) B3582887
theorem B4573655 : Blo 802343 4573655 := bstep (se 1 (by rfl) ⟨3430241, by rfl⟩ : syracuseStep 4573655 = 6860483) B6860483
theorem B6180371 : Blo 802343 6180371 := bstep (se 1 (by rfl) ⟨4635278, by rfl⟩ : syracuseStep 6180371 = 9270557) B9270557
theorem B7730963 : Blo 802343 7730963 := bstep (se 1 (by rfl) ⟨5798222, by rfl⟩ : syracuseStep 7730963 = 11596445) B11596445
theorem B3049103 : Blo 802343 3049103 := bstep (se 1 (by rfl) ⟨2286827, by rfl⟩ : syracuseStep 3049103 = 4573655) B4573655
theorem B4590695 : Blo 802343 4590695 := bstep (se 1 (by rfl) ⟨3443021, by rfl⟩ : syracuseStep 4590695 = 6886043) B6886043
theorem B5153975 : Blo 802343 5153975 := bstep (se 1 (by rfl) ⟨3865481, by rfl⟩ : syracuseStep 5153975 = 7730963) B7730963
theorem B2933455 : Blo 802343 2933455 := bstep (se 1 (by rfl) ⟨2200091, by rfl⟩ : syracuseStep 2933455 = 4400183) B4400183
theorem B334547441 : Blo 802343 334547441 := bstep (se 2 (by rfl) ⟨125455290, by rfl⟩ : syracuseStep 334547441 = 250910581) B250910581
theorem B904351 : Blo 802343 904351 := bstep (se 1 (by rfl) ⟨678263, by rfl⟩ : syracuseStep 904351 = 1356527) B1356527
theorem B1856353 : Blo 802343 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B12375379 : Blo 802343 12375379 := bstep (se 1 (by rfl) ⟨9281534, by rfl⟩ : syracuseStep 12375379 = 18563069) B18563069
theorem B4120247 : Blo 802343 4120247 := bstep (se 1 (by rfl) ⟨3090185, by rfl⟩ : syracuseStep 4120247 = 6180371) B6180371
theorem B12739153 : Blo 802343 12739153 := bstep (se 2 (by rfl) ⟨4777182, by rfl⟩ : syracuseStep 12739153 = 9554365) B9554365
theorem B2715119 : Blo 802343 2715119 := bstep (se 1 (by rfl) ⟨2036339, by rfl⟩ : syracuseStep 2715119 = 4072679) B4072679
theorem B2032735 : Blo 802343 2032735 := bstep (se 1 (by rfl) ⟨1524551, by rfl⟩ : syracuseStep 2032735 = 3049103) B3049103
theorem B1810079 : Blo 802343 1810079 := bstep (se 1 (by rfl) ⟨1357559, by rfl⟩ : syracuseStep 1810079 = 2715119) B2715119
theorem B16985537 : Blo 802343 16985537 := bstep (se 2 (by rfl) ⟨6369576, by rfl⟩ : syracuseStep 16985537 = 12739153) B12739153
theorem B3911273 : Blo 802343 3911273 := bstep (se 2 (by rfl) ⟨1466727, by rfl⟩ : syracuseStep 3911273 = 2933455) B2933455
theorem B223031627 : Blo 802343 223031627 := bstep (se 1 (by rfl) ⟨167273720, by rfl⟩ : syracuseStep 223031627 = 334547441) B334547441
theorem B3060463 : Blo 802343 3060463 := bstep (se 1 (by rfl) ⟨2295347, by rfl⟩ : syracuseStep 3060463 = 4590695) B4590695
theorem B2475137 : Blo 802343 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B16500505 : Blo 802343 16500505 := bstep (se 2 (by rfl) ⟨6187689, by rfl⟩ : syracuseStep 16500505 = 12375379) B12375379
theorem B1205801 : Blo 802343 1205801 := bstep (se 2 (by rfl) ⟨452175, by rfl⟩ : syracuseStep 1205801 = 904351) B904351
theorem B2746831 : Blo 802343 2746831 := bstep (se 1 (by rfl) ⟨2060123, by rfl⟩ : syracuseStep 2746831 = 4120247) B4120247
theorem B3435983 : Blo 802343 3435983 := bstep (se 1 (by rfl) ⟨2576987, by rfl⟩ : syracuseStep 3435983 = 5153975) B5153975
theorem B22000673 : Blo 802343 22000673 := bstep (se 2 (by rfl) ⟨8250252, by rfl⟩ : syracuseStep 22000673 = 16500505) B16500505
theorem B6600365 : Blo 802343 6600365 := bstep (se 3 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 6600365 = 2475137) B2475137
theorem B4080617 : Blo 802343 4080617 := bstep (se 2 (by rfl) ⟨1530231, by rfl⟩ : syracuseStep 4080617 = 3060463) B3060463
theorem B803867 : Blo 802343 803867 := bstep (se 1 (by rfl) ⟨602900, by rfl⟩ : syracuseStep 803867 = 1205801) B1205801
theorem B11323691 : Blo 802343 11323691 := bstep (se 1 (by rfl) ⟨8492768, by rfl⟩ : syracuseStep 11323691 = 16985537) B16985537
theorem B2607515 : Blo 802343 2607515 := bstep (se 1 (by rfl) ⟨1955636, by rfl⟩ : syracuseStep 2607515 = 3911273) B3911273
theorem B148687751 : Blo 802343 148687751 := bstep (se 1 (by rfl) ⟨111515813, by rfl⟩ : syracuseStep 148687751 = 223031627) B223031627
theorem B2710313 : Blo 802343 2710313 := bstep (se 2 (by rfl) ⟨1016367, by rfl⟩ : syracuseStep 2710313 = 2032735) B2032735
theorem B3662441 : Blo 802343 3662441 := bstep (se 2 (by rfl) ⟨1373415, by rfl⟩ : syracuseStep 3662441 = 2746831) B2746831
theorem B1206719 : Blo 802343 1206719 := bstep (se 1 (by rfl) ⟨905039, by rfl⟩ : syracuseStep 1206719 = 1810079) B1810079
theorem B2290655 : Blo 802343 2290655 := bstep (se 1 (by rfl) ⟨1717991, by rfl⟩ : syracuseStep 2290655 = 3435983) B3435983
theorem B2720411 : Blo 802343 2720411 := bstep (se 1 (by rfl) ⟨2040308, by rfl⟩ : syracuseStep 2720411 = 4080617) B4080617
theorem B1738343 : Blo 802343 1738343 := bstep (se 1 (by rfl) ⟨1303757, by rfl⟩ : syracuseStep 1738343 = 2607515) B2607515
theorem B99125167 : Blo 802343 99125167 := bstep (se 1 (by rfl) ⟨74343875, by rfl⟩ : syracuseStep 99125167 = 148687751) B148687751
theorem B1806875 : Blo 802343 1806875 := bstep (se 1 (by rfl) ⟨1355156, by rfl⟩ : syracuseStep 1806875 = 2710313) B2710313
theorem B4400243 : Blo 802343 4400243 := bstep (se 1 (by rfl) ⟨3300182, by rfl⟩ : syracuseStep 4400243 = 6600365) B6600365
theorem B7549127 : Blo 802343 7549127 := bstep (se 1 (by rfl) ⟨5661845, by rfl⟩ : syracuseStep 7549127 = 11323691) B11323691
theorem B58668461 : Blo 802343 58668461 := bstep (se 3 (by rfl) ⟨11000336, by rfl⟩ : syracuseStep 58668461 = 22000673) B22000673
theorem B2441627 : Blo 802343 2441627 := bstep (se 1 (by rfl) ⟨1831220, by rfl⟩ : syracuseStep 2441627 = 3662441) B3662441
theorem B804479 : Blo 802343 804479 := bstep (se 1 (by rfl) ⟨603359, by rfl⟩ : syracuseStep 804479 = 1206719) B1206719
theorem B1527103 : Blo 802343 1527103 := bstep (se 1 (by rfl) ⟨1145327, by rfl⟩ : syracuseStep 1527103 = 2290655) B2290655
theorem B2036137 : Blo 802343 2036137 := bstep (se 2 (by rfl) ⟨763551, by rfl⟩ : syracuseStep 2036137 = 1527103) B1527103
theorem B1813607 : Blo 802343 1813607 := bstep (se 1 (by rfl) ⟨1360205, by rfl⟩ : syracuseStep 1813607 = 2720411) B2720411
theorem B1158895 : Blo 802343 1158895 := bstep (se 1 (by rfl) ⟨869171, by rfl⟩ : syracuseStep 1158895 = 1738343) B1738343
theorem B132166889 : Blo 802343 132166889 := bstep (se 2 (by rfl) ⟨49562583, by rfl⟩ : syracuseStep 132166889 = 99125167) B99125167
theorem B2933495 : Blo 802343 2933495 := bstep (se 1 (by rfl) ⟨2200121, by rfl⟩ : syracuseStep 2933495 = 4400243) B4400243
theorem B5032751 : Blo 802343 5032751 := bstep (se 1 (by rfl) ⟨3774563, by rfl⟩ : syracuseStep 5032751 = 7549127) B7549127
theorem B39112307 : Blo 802343 39112307 := bstep (se 1 (by rfl) ⟨29334230, by rfl⟩ : syracuseStep 39112307 = 58668461) B58668461
theorem B1627751 : Blo 802343 1627751 := bstep (se 1 (by rfl) ⟨1220813, by rfl⟩ : syracuseStep 1627751 = 2441627) B2441627
theorem B1204583 : Blo 802343 1204583 := bstep (se 1 (by rfl) ⟨903437, by rfl⟩ : syracuseStep 1204583 = 1806875) B1806875
theorem B1085167 : Blo 802343 1085167 := bstep (se 1 (by rfl) ⟨813875, by rfl⟩ : syracuseStep 1085167 = 1627751) B1627751
theorem B1545193 : Blo 802343 1545193 := bstep (se 2 (by rfl) ⟨579447, by rfl⟩ : syracuseStep 1545193 = 1158895) B1158895
theorem B803055 : Blo 802343 803055 := bstep (se 1 (by rfl) ⟨602291, by rfl⟩ : syracuseStep 803055 = 1204583) B1204583
theorem B13420669 : Blo 802343 13420669 := bstep (se 3 (by rfl) ⟨2516375, by rfl⟩ : syracuseStep 13420669 = 5032751) B5032751
theorem B1955663 : Blo 802343 1955663 := bstep (se 1 (by rfl) ⟨1466747, by rfl⟩ : syracuseStep 1955663 = 2933495) B2933495
theorem B26074871 : Blo 802343 26074871 := bstep (se 1 (by rfl) ⟨19556153, by rfl⟩ : syracuseStep 26074871 = 39112307) B39112307
theorem B2714849 : Blo 802343 2714849 := bstep (se 2 (by rfl) ⟨1018068, by rfl⟩ : syracuseStep 2714849 = 2036137) B2036137
theorem B1209071 : Blo 802343 1209071 := bstep (se 1 (by rfl) ⟨906803, by rfl⟩ : syracuseStep 1209071 = 1813607) B1813607
theorem B88111259 : Blo 802343 88111259 := bstep (se 1 (by rfl) ⟨66083444, by rfl⟩ : syracuseStep 88111259 = 132166889) B132166889
theorem B17894225 : Blo 802343 17894225 := bstep (se 2 (by rfl) ⟨6710334, by rfl⟩ : syracuseStep 17894225 = 13420669) B13420669
theorem B1446889 : Blo 802343 1446889 := bstep (se 2 (by rfl) ⟨542583, by rfl⟩ : syracuseStep 1446889 = 1085167) B1085167
theorem B1809899 : Blo 802343 1809899 := bstep (se 1 (by rfl) ⟨1357424, by rfl⟩ : syracuseStep 1809899 = 2714849) B2714849
theorem B17383247 : Blo 802343 17383247 := bstep (se 1 (by rfl) ⟨13037435, by rfl⟩ : syracuseStep 17383247 = 26074871) B26074871
theorem B806047 : Blo 802343 806047 := bstep (se 1 (by rfl) ⟨604535, by rfl⟩ : syracuseStep 806047 = 1209071) B1209071
theorem B58740839 : Blo 802343 58740839 := bstep (se 1 (by rfl) ⟨44055629, by rfl⟩ : syracuseStep 58740839 = 88111259) B88111259
theorem B1303775 : Blo 802343 1303775 := bstep (se 1 (by rfl) ⟨977831, by rfl⟩ : syracuseStep 1303775 = 1955663) B1955663
theorem B2060257 : Blo 802343 2060257 := bstep (se 2 (by rfl) ⟨772596, by rfl⟩ : syracuseStep 2060257 = 1545193) B1545193
theorem B11929483 : Blo 802343 11929483 := bstep (se 1 (by rfl) ⟨8947112, by rfl⟩ : syracuseStep 11929483 = 17894225) B17894225
theorem B39160559 : Blo 802343 39160559 := bstep (se 1 (by rfl) ⟨29370419, by rfl⟩ : syracuseStep 39160559 = 58740839) B58740839
theorem B869183 : Blo 802343 869183 := bstep (se 1 (by rfl) ⟨651887, by rfl⟩ : syracuseStep 869183 = 1303775) B1303775
theorem B11588831 : Blo 802343 11588831 := bstep (se 1 (by rfl) ⟨8691623, by rfl⟩ : syracuseStep 11588831 = 17383247) B17383247
theorem B1206599 : Blo 802343 1206599 := bstep (se 1 (by rfl) ⟨904949, by rfl⟩ : syracuseStep 1206599 = 1809899) B1809899
theorem B2747009 : Blo 802343 2747009 := bstep (se 2 (by rfl) ⟨1030128, by rfl⟩ : syracuseStep 2747009 = 2060257) B2060257
theorem B1929185 : Blo 802343 1929185 := bstep (se 2 (by rfl) ⟨723444, by rfl⟩ : syracuseStep 1929185 = 1446889) B1446889
theorem B1286123 : Blo 802343 1286123 := bstep (se 1 (by rfl) ⟨964592, by rfl⟩ : syracuseStep 1286123 = 1929185) B1929185
theorem B15905977 : Blo 802343 15905977 := bstep (se 2 (by rfl) ⟨5964741, by rfl⟩ : syracuseStep 15905977 = 11929483) B11929483
theorem B804399 : Blo 802343 804399 := bstep (se 1 (by rfl) ⟨603299, by rfl⟩ : syracuseStep 804399 = 1206599) B1206599
theorem B26107039 : Blo 802343 26107039 := bstep (se 1 (by rfl) ⟨19580279, by rfl⟩ : syracuseStep 26107039 = 39160559) B39160559
theorem B37085141 : Blo 802343 37085141 := bstep (se 7 (by rfl) ⟨434591, by rfl⟩ : syracuseStep 37085141 = 869183) B869183
theorem B7725887 : Blo 802343 7725887 := bstep (se 1 (by rfl) ⟨5794415, by rfl⟩ : syracuseStep 7725887 = 11588831) B11588831
theorem B1831339 : Blo 802343 1831339 := bstep (se 1 (by rfl) ⟨1373504, by rfl⟩ : syracuseStep 1831339 = 2747009) B2747009
theorem B9767141 : Blo 802343 9767141 := bstep (se 4 (by rfl) ⟨915669, by rfl⟩ : syracuseStep 9767141 = 1831339) B1831339
theorem B5150591 : Blo 802343 5150591 := bstep (se 1 (by rfl) ⟨3862943, by rfl⟩ : syracuseStep 5150591 = 7725887) B7725887
theorem B34809385 : Blo 802343 34809385 := bstep (se 2 (by rfl) ⟨13053519, by rfl⟩ : syracuseStep 34809385 = 26107039) B26107039
theorem B24723427 : Blo 802343 24723427 := bstep (se 1 (by rfl) ⟨18542570, by rfl⟩ : syracuseStep 24723427 = 37085141) B37085141
theorem B3429661 : Blo 802343 3429661 := bstep (se 3 (by rfl) ⟨643061, by rfl⟩ : syracuseStep 3429661 = 1286123) B1286123
theorem B84831877 : Blo 802343 84831877 := bstep (se 4 (by rfl) ⟨7952988, by rfl⟩ : syracuseStep 84831877 = 15905977) B15905977
theorem B46412513 : Blo 802343 46412513 := bstep (se 2 (by rfl) ⟨17404692, by rfl⟩ : syracuseStep 46412513 = 34809385) B34809385
theorem B4572881 : Blo 802343 4572881 := bstep (se 2 (by rfl) ⟨1714830, by rfl⟩ : syracuseStep 4572881 = 3429661) B3429661
theorem B6511427 : Blo 802343 6511427 := bstep (se 1 (by rfl) ⟨4883570, by rfl⟩ : syracuseStep 6511427 = 9767141) B9767141
theorem B3433727 : Blo 802343 3433727 := bstep (se 1 (by rfl) ⟨2575295, by rfl⟩ : syracuseStep 3433727 = 5150591) B5150591
theorem B113109169 : Blo 802343 113109169 := bstep (se 2 (by rfl) ⟨42415938, by rfl⟩ : syracuseStep 113109169 = 84831877) B84831877
theorem B32964569 : Blo 802343 32964569 := bstep (se 2 (by rfl) ⟨12361713, by rfl⟩ : syracuseStep 32964569 = 24723427) B24723427
theorem B3048587 : Blo 802343 3048587 := bstep (se 1 (by rfl) ⟨2286440, by rfl⟩ : syracuseStep 3048587 = 4572881) B4572881
theorem B30941675 : Blo 802343 30941675 := bstep (se 1 (by rfl) ⟨23206256, by rfl⟩ : syracuseStep 30941675 = 46412513) B46412513
theorem B150812225 : Blo 802343 150812225 := bstep (se 2 (by rfl) ⟨56554584, by rfl⟩ : syracuseStep 150812225 = 113109169) B113109169
theorem B4340951 : Blo 802343 4340951 := bstep (se 1 (by rfl) ⟨3255713, by rfl⟩ : syracuseStep 4340951 = 6511427) B6511427
theorem B21976379 : Blo 802343 21976379 := bstep (se 1 (by rfl) ⟨16482284, by rfl⟩ : syracuseStep 21976379 = 32964569) B32964569
theorem B2289151 : Blo 802343 2289151 := bstep (se 1 (by rfl) ⟨1716863, by rfl⟩ : syracuseStep 2289151 = 3433727) B3433727
theorem B2032391 : Blo 802343 2032391 := bstep (se 1 (by rfl) ⟨1524293, by rfl⟩ : syracuseStep 2032391 = 3048587) B3048587
theorem B14650919 : Blo 802343 14650919 := bstep (se 1 (by rfl) ⟨10988189, by rfl⟩ : syracuseStep 14650919 = 21976379) B21976379
theorem B3052201 : Blo 802343 3052201 := bstep (se 2 (by rfl) ⟨1144575, by rfl⟩ : syracuseStep 3052201 = 2289151) B2289151
theorem B100541483 : Blo 802343 100541483 := bstep (se 1 (by rfl) ⟨75406112, by rfl⟩ : syracuseStep 100541483 = 150812225) B150812225
theorem B2893967 : Blo 802343 2893967 := bstep (se 1 (by rfl) ⟨2170475, by rfl⟩ : syracuseStep 2893967 = 4340951) B4340951
theorem B20627783 : Blo 802343 20627783 := bstep (se 1 (by rfl) ⟨15470837, by rfl⟩ : syracuseStep 20627783 = 30941675) B30941675
theorem B9767279 : Blo 802343 9767279 := bstep (se 1 (by rfl) ⟨7325459, by rfl⟩ : syracuseStep 9767279 = 14650919) B14650919
theorem B4069601 : Blo 802343 4069601 := bstep (se 2 (by rfl) ⟨1526100, by rfl⟩ : syracuseStep 4069601 = 3052201) B3052201
theorem B1354927 : Blo 802343 1354927 := bstep (se 1 (by rfl) ⟨1016195, by rfl⟩ : syracuseStep 1354927 = 2032391) B2032391
theorem B67027655 : Blo 802343 67027655 := bstep (se 1 (by rfl) ⟨50270741, by rfl⟩ : syracuseStep 67027655 = 100541483) B100541483
theorem B13751855 : Blo 802343 13751855 := bstep (se 1 (by rfl) ⟨10313891, by rfl⟩ : syracuseStep 13751855 = 20627783) B20627783
theorem B1929311 : Blo 802343 1929311 := bstep (se 1 (by rfl) ⟨1446983, by rfl⟩ : syracuseStep 1929311 = 2893967) B2893967
theorem B1806569 : Blo 802343 1806569 := bstep (se 2 (by rfl) ⟨677463, by rfl⟩ : syracuseStep 1806569 = 1354927) B1354927
theorem B1286207 : Blo 802343 1286207 := bstep (se 1 (by rfl) ⟨964655, by rfl⟩ : syracuseStep 1286207 = 1929311) B1929311
theorem B44685103 : Blo 802343 44685103 := bstep (se 1 (by rfl) ⟨33513827, by rfl⟩ : syracuseStep 44685103 = 67027655) B67027655
theorem B6511519 : Blo 802343 6511519 := bstep (se 1 (by rfl) ⟨4883639, by rfl⟩ : syracuseStep 6511519 = 9767279) B9767279
theorem B9167903 : Blo 802343 9167903 := bstep (se 1 (by rfl) ⟨6875927, by rfl⟩ : syracuseStep 9167903 = 13751855) B13751855
theorem B2713067 : Blo 802343 2713067 := bstep (se 1 (by rfl) ⟨2034800, by rfl⟩ : syracuseStep 2713067 = 4069601) B4069601
theorem B857471 : Blo 802343 857471 := bstep (se 1 (by rfl) ⟨643103, by rfl⟩ : syracuseStep 857471 = 1286207) B1286207
theorem B1808711 : Blo 802343 1808711 := bstep (se 1 (by rfl) ⟨1356533, by rfl⟩ : syracuseStep 1808711 = 2713067) B2713067
theorem B59580137 : Blo 802343 59580137 := bstep (se 2 (by rfl) ⟨22342551, by rfl⟩ : syracuseStep 59580137 = 44685103) B44685103
theorem B6111935 : Blo 802343 6111935 := bstep (se 1 (by rfl) ⟨4583951, by rfl⟩ : syracuseStep 6111935 = 9167903) B9167903
theorem B1204379 : Blo 802343 1204379 := bstep (se 1 (by rfl) ⟨903284, by rfl⟩ : syracuseStep 1204379 = 1806569) B1806569
theorem B8682025 : Blo 802343 8682025 := bstep (se 2 (by rfl) ⟨3255759, by rfl⟩ : syracuseStep 8682025 = 6511519) B6511519
theorem B11576033 : Blo 802343 11576033 := bstep (se 2 (by rfl) ⟨4341012, by rfl⟩ : syracuseStep 11576033 = 8682025) B8682025
theorem B4074623 : Blo 802343 4074623 := bstep (se 1 (by rfl) ⟨3055967, by rfl⟩ : syracuseStep 4074623 = 6111935) B6111935
theorem B802919 : Blo 802343 802919 := bstep (se 1 (by rfl) ⟨602189, by rfl⟩ : syracuseStep 802919 = 1204379) B1204379
theorem B158880365 : Blo 802343 158880365 := bstep (se 3 (by rfl) ⟨29790068, by rfl⟩ : syracuseStep 158880365 = 59580137) B59580137
theorem B2286589 : Blo 802343 2286589 := bstep (se 3 (by rfl) ⟨428735, by rfl⟩ : syracuseStep 2286589 = 857471) B857471
theorem B1205807 : Blo 802343 1205807 := bstep (se 1 (by rfl) ⟨904355, by rfl⟩ : syracuseStep 1205807 = 1808711) B1808711
theorem B3048785 : Blo 802343 3048785 := bstep (se 2 (by rfl) ⟨1143294, by rfl⟩ : syracuseStep 3048785 = 2286589) B2286589
theorem B105920243 : Blo 802343 105920243 := bstep (se 1 (by rfl) ⟨79440182, by rfl⟩ : syracuseStep 105920243 = 158880365) B158880365
theorem B7717355 : Blo 802343 7717355 := bstep (se 1 (by rfl) ⟨5788016, by rfl⟩ : syracuseStep 7717355 = 11576033) B11576033
theorem B803871 : Blo 802343 803871 := bstep (se 1 (by rfl) ⟨602903, by rfl⟩ : syracuseStep 803871 = 1205807) B1205807
theorem B2716415 : Blo 802343 2716415 := bstep (se 1 (by rfl) ⟨2037311, by rfl⟩ : syracuseStep 2716415 = 4074623) B4074623
theorem B5144903 : Blo 802343 5144903 := bstep (se 1 (by rfl) ⟨3858677, by rfl⟩ : syracuseStep 5144903 = 7717355) B7717355
theorem B2032523 : Blo 802343 2032523 := bstep (se 1 (by rfl) ⟨1524392, by rfl⟩ : syracuseStep 2032523 = 3048785) B3048785
theorem B1810943 : Blo 802343 1810943 := bstep (se 1 (by rfl) ⟨1358207, by rfl⟩ : syracuseStep 1810943 = 2716415) B2716415
theorem B70613495 : Blo 802343 70613495 := bstep (se 1 (by rfl) ⟨52960121, by rfl⟩ : syracuseStep 70613495 = 105920243) B105920243
theorem B1355015 : Blo 802343 1355015 := bstep (se 1 (by rfl) ⟨1016261, by rfl⟩ : syracuseStep 1355015 = 2032523) B2032523
theorem B47075663 : Blo 802343 47075663 := bstep (se 1 (by rfl) ⟨35306747, by rfl⟩ : syracuseStep 47075663 = 70613495) B70613495
theorem B3429935 : Blo 802343 3429935 := bstep (se 1 (by rfl) ⟨2572451, by rfl⟩ : syracuseStep 3429935 = 5144903) B5144903
theorem B1207295 : Blo 802343 1207295 := bstep (se 1 (by rfl) ⟨905471, by rfl⟩ : syracuseStep 1207295 = 1810943) B1810943
theorem B804863 : Blo 802343 804863 := bstep (se 1 (by rfl) ⟨603647, by rfl⟩ : syracuseStep 804863 = 1207295) B1207295
theorem B903343 : Blo 802343 903343 := bstep (se 1 (by rfl) ⟨677507, by rfl⟩ : syracuseStep 903343 = 1355015) B1355015
theorem B31383775 : Blo 802343 31383775 := bstep (se 1 (by rfl) ⟨23537831, by rfl⟩ : syracuseStep 31383775 = 47075663) B47075663
theorem B2286623 : Blo 802343 2286623 := bstep (se 1 (by rfl) ⟨1714967, by rfl⟩ : syracuseStep 2286623 = 3429935) B3429935
theorem B41845033 : Blo 802343 41845033 := bstep (se 2 (by rfl) ⟨15691887, by rfl⟩ : syracuseStep 41845033 = 31383775) B31383775
theorem B1524415 : Blo 802343 1524415 := bstep (se 1 (by rfl) ⟨1143311, by rfl⟩ : syracuseStep 1524415 = 2286623) B2286623
theorem B1204457 : Blo 802343 1204457 := bstep (se 2 (by rfl) ⟨451671, by rfl⟩ : syracuseStep 1204457 = 903343) B903343
theorem B2032553 : Blo 802343 2032553 := bstep (se 2 (by rfl) ⟨762207, by rfl⟩ : syracuseStep 2032553 = 1524415) B1524415
theorem B802971 : Blo 802343 802971 := bstep (se 1 (by rfl) ⟨602228, by rfl⟩ : syracuseStep 802971 = 1204457) B1204457
theorem B55793377 : Blo 802343 55793377 := bstep (se 2 (by rfl) ⟨20922516, by rfl⟩ : syracuseStep 55793377 = 41845033) B41845033
theorem B1355035 : Blo 802343 1355035 := bstep (se 1 (by rfl) ⟨1016276, by rfl⟩ : syracuseStep 1355035 = 2032553) B2032553
theorem B297564677 : Blo 802343 297564677 := bstep (se 4 (by rfl) ⟨27896688, by rfl⟩ : syracuseStep 297564677 = 55793377) B55793377
theorem B1806713 : Blo 802343 1806713 := bstep (se 2 (by rfl) ⟨677517, by rfl⟩ : syracuseStep 1806713 = 1355035) B1355035
theorem B198376451 : Blo 802343 198376451 := bstep (se 1 (by rfl) ⟨148782338, by rfl⟩ : syracuseStep 198376451 = 297564677) B297564677
theorem B1204475 : Blo 802343 1204475 := bstep (se 1 (by rfl) ⟨903356, by rfl⟩ : syracuseStep 1204475 = 1806713) B1806713
theorem B132250967 : Blo 802343 132250967 := bstep (se 1 (by rfl) ⟨99188225, by rfl⟩ : syracuseStep 132250967 = 198376451) B198376451
theorem B802983 : Blo 802343 802983 := bstep (se 1 (by rfl) ⟨602237, by rfl⟩ : syracuseStep 802983 = 1204475) B1204475
theorem B88167311 : Blo 802343 88167311 := bstep (se 1 (by rfl) ⟨66125483, by rfl⟩ : syracuseStep 88167311 = 132250967) B132250967
theorem B58778207 : Blo 802343 58778207 := bstep (se 1 (by rfl) ⟨44083655, by rfl⟩ : syracuseStep 58778207 = 88167311) B88167311
theorem B39185471 : Blo 802343 39185471 := bstep (se 1 (by rfl) ⟨29389103, by rfl⟩ : syracuseStep 39185471 = 58778207) B58778207
theorem B26123647 : Blo 802343 26123647 := bstep (se 1 (by rfl) ⟨19592735, by rfl⟩ : syracuseStep 26123647 = 39185471) B39185471
theorem B34831529 : Blo 802343 34831529 := bstep (se 2 (by rfl) ⟨13061823, by rfl⟩ : syracuseStep 34831529 = 26123647) B26123647
theorem B23221019 : Blo 802343 23221019 := bstep (se 1 (by rfl) ⟨17415764, by rfl⟩ : syracuseStep 23221019 = 34831529) B34831529
theorem B15480679 : Blo 802343 15480679 := bstep (se 1 (by rfl) ⟨11610509, by rfl⟩ : syracuseStep 15480679 = 23221019) B23221019
theorem B20640905 : Blo 802343 20640905 := bstep (se 2 (by rfl) ⟨7740339, by rfl⟩ : syracuseStep 20640905 = 15480679) B15480679
theorem B13760603 : Blo 802343 13760603 := bstep (se 1 (by rfl) ⟨10320452, by rfl⟩ : syracuseStep 13760603 = 20640905) B20640905
theorem B9173735 : Blo 802343 9173735 := bstep (se 1 (by rfl) ⟨6880301, by rfl⟩ : syracuseStep 9173735 = 13760603) B13760603
theorem B6115823 : Blo 802343 6115823 := bstep (se 1 (by rfl) ⟨4586867, by rfl⟩ : syracuseStep 6115823 = 9173735) B9173735
theorem B4077215 : Blo 802343 4077215 := bstep (se 1 (by rfl) ⟨3057911, by rfl⟩ : syracuseStep 4077215 = 6115823) B6115823
theorem B2718143 : Blo 802343 2718143 := bstep (se 1 (by rfl) ⟨2038607, by rfl⟩ : syracuseStep 2718143 = 4077215) B4077215
theorem B1812095 : Blo 802343 1812095 := bstep (se 1 (by rfl) ⟨1359071, by rfl⟩ : syracuseStep 1812095 = 2718143) B2718143
theorem B1208063 : Blo 802343 1208063 := bstep (se 1 (by rfl) ⟨906047, by rfl⟩ : syracuseStep 1208063 = 1812095) B1812095
theorem B805375 : Blo 802343 805375 := bstep (se 1 (by rfl) ⟨604031, by rfl⟩ : syracuseStep 805375 = 1208063) B1208063

theorem C0 (j : ℕ) (h1 : 200585 ≤ j) (h2 : j ≤ 201284) : Blo 802343 (4 * j + 3) := by
  interval_cases j
  · exact B802343
  · exact B802347
  · exact B802351
  · exact B802355
  · exact B802359
  · exact B802363
  · exact B802367
  · exact B802371
  · exact B802375
  · exact B802379
  · exact B802383
  · exact B802387
  · exact B802391
  · exact B802395
  · exact B802399
  · exact B802403
  · exact B802407
  · exact B802411
  · exact B802415
  · exact B802419
  · exact B802423
  · exact B802427
  · exact B802431
  · exact B802435
  · exact B802439
  · exact B802443
  · exact B802447
  · exact B802451
  · exact B802455
  · exact B802459
  · exact B802463
  · exact B802467
  · exact B802471
  · exact B802475
  · exact B802479
  · exact B802483
  · exact B802487
  · exact B802491
  · exact B802495
  · exact B802499
  · exact B802503
  · exact B802507
  · exact B802511
  · exact B802515
  · exact B802519
  · exact B802523
  · exact B802527
  · exact B802531
  · exact B802535
  · exact B802539
  · exact B802543
  · exact B802547
  · exact B802551
  · exact B802555
  · exact B802559
  · exact B802563
  · exact B802567
  · exact B802571
  · exact B802575
  · exact B802579
  · exact B802583
  · exact B802587
  · exact B802591
  · exact B802595
  · exact B802599
  · exact B802603
  · exact B802607
  · exact B802611
  · exact B802615
  · exact B802619
  · exact B802623
  · exact B802627
  · exact B802631
  · exact B802635
  · exact B802639
  · exact B802643
  · exact B802647
  · exact B802651
  · exact B802655
  · exact B802659
  · exact B802663
  · exact B802667
  · exact B802671
  · exact B802675
  · exact B802679
  · exact B802683
  · exact B802687
  · exact B802691
  · exact B802695
  · exact B802699
  · exact B802703
  · exact B802707
  · exact B802711
  · exact B802715
  · exact B802719
  · exact B802723
  · exact B802727
  · exact B802731
  · exact B802735
  · exact B802739
  · exact B802743
  · exact B802747
  · exact B802751
  · exact B802755
  · exact B802759
  · exact B802763
  · exact B802767
  · exact B802771
  · exact B802775
  · exact B802779
  · exact B802783
  · exact B802787
  · exact B802791
  · exact B802795
  · exact B802799
  · exact B802803
  · exact B802807
  · exact B802811
  · exact B802815
  · exact B802819
  · exact B802823
  · exact B802827
  · exact B802831
  · exact B802835
  · exact B802839
  · exact B802843
  · exact B802847
  · exact B802851
  · exact B802855
  · exact B802859
  · exact B802863
  · exact B802867
  · exact B802871
  · exact B802875
  · exact B802879
  · exact B802883
  · exact B802887
  · exact B802891
  · exact B802895
  · exact B802899
  · exact B802903
  · exact B802907
  · exact B802911
  · exact B802915
  · exact B802919
  · exact B802923
  · exact B802927
  · exact B802931
  · exact B802935
  · exact B802939
  · exact B802943
  · exact B802947
  · exact B802951
  · exact B802955
  · exact B802959
  · exact B802963
  · exact B802967
  · exact B802971
  · exact B802975
  · exact B802979
  · exact B802983
  · exact B802987
  · exact B802991
  · exact B802995
  · exact B802999
  · exact B803003
  · exact B803007
  · exact B803011
  · exact B803015
  · exact B803019
  · exact B803023
  · exact B803027
  · exact B803031
  · exact B803035
  · exact B803039
  · exact B803043
  · exact B803047
  · exact B803051
  · exact B803055
  · exact B803059
  · exact B803063
  · exact B803067
  · exact B803071
  · exact B803075
  · exact B803079
  · exact B803083
  · exact B803087
  · exact B803091
  · exact B803095
  · exact B803099
  · exact B803103
  · exact B803107
  · exact B803111
  · exact B803115
  · exact B803119
  · exact B803123
  · exact B803127
  · exact B803131
  · exact B803135
  · exact B803139
  · exact B803143
  · exact B803147
  · exact B803151
  · exact B803155
  · exact B803159
  · exact B803163
  · exact B803167
  · exact B803171
  · exact B803175
  · exact B803179
  · exact B803183
  · exact B803187
  · exact B803191
  · exact B803195
  · exact B803199
  · exact B803203
  · exact B803207
  · exact B803211
  · exact B803215
  · exact B803219
  · exact B803223
  · exact B803227
  · exact B803231
  · exact B803235
  · exact B803239
  · exact B803243
  · exact B803247
  · exact B803251
  · exact B803255
  · exact B803259
  · exact B803263
  · exact B803267
  · exact B803271
  · exact B803275
  · exact B803279
  · exact B803283
  · exact B803287
  · exact B803291
  · exact B803295
  · exact B803299
  · exact B803303
  · exact B803307
  · exact B803311
  · exact B803315
  · exact B803319
  · exact B803323
  · exact B803327
  · exact B803331
  · exact B803335
  · exact B803339
  · exact B803343
  · exact B803347
  · exact B803351
  · exact B803355
  · exact B803359
  · exact B803363
  · exact B803367
  · exact B803371
  · exact B803375
  · exact B803379
  · exact B803383
  · exact B803387
  · exact B803391
  · exact B803395
  · exact B803399
  · exact B803403
  · exact B803407
  · exact B803411
  · exact B803415
  · exact B803419
  · exact B803423
  · exact B803427
  · exact B803431
  · exact B803435
  · exact B803439
  · exact B803443
  · exact B803447
  · exact B803451
  · exact B803455
  · exact B803459
  · exact B803463
  · exact B803467
  · exact B803471
  · exact B803475
  · exact B803479
  · exact B803483
  · exact B803487
  · exact B803491
  · exact B803495
  · exact B803499
  · exact B803503
  · exact B803507
  · exact B803511
  · exact B803515
  · exact B803519
  · exact B803523
  · exact B803527
  · exact B803531
  · exact B803535
  · exact B803539
  · exact B803543
  · exact B803547
  · exact B803551
  · exact B803555
  · exact B803559
  · exact B803563
  · exact B803567
  · exact B803571
  · exact B803575
  · exact B803579
  · exact B803583
  · exact B803587
  · exact B803591
  · exact B803595
  · exact B803599
  · exact B803603
  · exact B803607
  · exact B803611
  · exact B803615
  · exact B803619
  · exact B803623
  · exact B803627
  · exact B803631
  · exact B803635
  · exact B803639
  · exact B803643
  · exact B803647
  · exact B803651
  · exact B803655
  · exact B803659
  · exact B803663
  · exact B803667
  · exact B803671
  · exact B803675
  · exact B803679
  · exact B803683
  · exact B803687
  · exact B803691
  · exact B803695
  · exact B803699
  · exact B803703
  · exact B803707
  · exact B803711
  · exact B803715
  · exact B803719
  · exact B803723
  · exact B803727
  · exact B803731
  · exact B803735
  · exact B803739
  · exact B803743
  · exact B803747
  · exact B803751
  · exact B803755
  · exact B803759
  · exact B803763
  · exact B803767
  · exact B803771
  · exact B803775
  · exact B803779
  · exact B803783
  · exact B803787
  · exact B803791
  · exact B803795
  · exact B803799
  · exact B803803
  · exact B803807
  · exact B803811
  · exact B803815
  · exact B803819
  · exact B803823
  · exact B803827
  · exact B803831
  · exact B803835
  · exact B803839
  · exact B803843
  · exact B803847
  · exact B803851
  · exact B803855
  · exact B803859
  · exact B803863
  · exact B803867
  · exact B803871
  · exact B803875
  · exact B803879
  · exact B803883
  · exact B803887
  · exact B803891
  · exact B803895
  · exact B803899
  · exact B803903
  · exact B803907
  · exact B803911
  · exact B803915
  · exact B803919
  · exact B803923
  · exact B803927
  · exact B803931
  · exact B803935
  · exact B803939
  · exact B803943
  · exact B803947
  · exact B803951
  · exact B803955
  · exact B803959
  · exact B803963
  · exact B803967
  · exact B803971
  · exact B803975
  · exact B803979
  · exact B803983
  · exact B803987
  · exact B803991
  · exact B803995
  · exact B803999
  · exact B804003
  · exact B804007
  · exact B804011
  · exact B804015
  · exact B804019
  · exact B804023
  · exact B804027
  · exact B804031
  · exact B804035
  · exact B804039
  · exact B804043
  · exact B804047
  · exact B804051
  · exact B804055
  · exact B804059
  · exact B804063
  · exact B804067
  · exact B804071
  · exact B804075
  · exact B804079
  · exact B804083
  · exact B804087
  · exact B804091
  · exact B804095
  · exact B804099
  · exact B804103
  · exact B804107
  · exact B804111
  · exact B804115
  · exact B804119
  · exact B804123
  · exact B804127
  · exact B804131
  · exact B804135
  · exact B804139
  · exact B804143
  · exact B804147
  · exact B804151
  · exact B804155
  · exact B804159
  · exact B804163
  · exact B804167
  · exact B804171
  · exact B804175
  · exact B804179
  · exact B804183
  · exact B804187
  · exact B804191
  · exact B804195
  · exact B804199
  · exact B804203
  · exact B804207
  · exact B804211
  · exact B804215
  · exact B804219
  · exact B804223
  · exact B804227
  · exact B804231
  · exact B804235
  · exact B804239
  · exact B804243
  · exact B804247
  · exact B804251
  · exact B804255
  · exact B804259
  · exact B804263
  · exact B804267
  · exact B804271
  · exact B804275
  · exact B804279
  · exact B804283
  · exact B804287
  · exact B804291
  · exact B804295
  · exact B804299
  · exact B804303
  · exact B804307
  · exact B804311
  · exact B804315
  · exact B804319
  · exact B804323
  · exact B804327
  · exact B804331
  · exact B804335
  · exact B804339
  · exact B804343
  · exact B804347
  · exact B804351
  · exact B804355
  · exact B804359
  · exact B804363
  · exact B804367
  · exact B804371
  · exact B804375
  · exact B804379
  · exact B804383
  · exact B804387
  · exact B804391
  · exact B804395
  · exact B804399
  · exact B804403
  · exact B804407
  · exact B804411
  · exact B804415
  · exact B804419
  · exact B804423
  · exact B804427
  · exact B804431
  · exact B804435
  · exact B804439
  · exact B804443
  · exact B804447
  · exact B804451
  · exact B804455
  · exact B804459
  · exact B804463
  · exact B804467
  · exact B804471
  · exact B804475
  · exact B804479
  · exact B804483
  · exact B804487
  · exact B804491
  · exact B804495
  · exact B804499
  · exact B804503
  · exact B804507
  · exact B804511
  · exact B804515
  · exact B804519
  · exact B804523
  · exact B804527
  · exact B804531
  · exact B804535
  · exact B804539
  · exact B804543
  · exact B804547
  · exact B804551
  · exact B804555
  · exact B804559
  · exact B804563
  · exact B804567
  · exact B804571
  · exact B804575
  · exact B804579
  · exact B804583
  · exact B804587
  · exact B804591
  · exact B804595
  · exact B804599
  · exact B804603
  · exact B804607
  · exact B804611
  · exact B804615
  · exact B804619
  · exact B804623
  · exact B804627
  · exact B804631
  · exact B804635
  · exact B804639
  · exact B804643
  · exact B804647
  · exact B804651
  · exact B804655
  · exact B804659
  · exact B804663
  · exact B804667
  · exact B804671
  · exact B804675
  · exact B804679
  · exact B804683
  · exact B804687
  · exact B804691
  · exact B804695
  · exact B804699
  · exact B804703
  · exact B804707
  · exact B804711
  · exact B804715
  · exact B804719
  · exact B804723
  · exact B804727
  · exact B804731
  · exact B804735
  · exact B804739
  · exact B804743
  · exact B804747
  · exact B804751
  · exact B804755
  · exact B804759
  · exact B804763
  · exact B804767
  · exact B804771
  · exact B804775
  · exact B804779
  · exact B804783
  · exact B804787
  · exact B804791
  · exact B804795
  · exact B804799
  · exact B804803
  · exact B804807
  · exact B804811
  · exact B804815
  · exact B804819
  · exact B804823
  · exact B804827
  · exact B804831
  · exact B804835
  · exact B804839
  · exact B804843
  · exact B804847
  · exact B804851
  · exact B804855
  · exact B804859
  · exact B804863
  · exact B804867
  · exact B804871
  · exact B804875
  · exact B804879
  · exact B804883
  · exact B804887
  · exact B804891
  · exact B804895
  · exact B804899
  · exact B804903
  · exact B804907
  · exact B804911
  · exact B804915
  · exact B804919
  · exact B804923
  · exact B804927
  · exact B804931
  · exact B804935
  · exact B804939
  · exact B804943
  · exact B804947
  · exact B804951
  · exact B804955
  · exact B804959
  · exact B804963
  · exact B804967
  · exact B804971
  · exact B804975
  · exact B804979
  · exact B804983
  · exact B804987
  · exact B804991
  · exact B804995
  · exact B804999
  · exact B805003
  · exact B805007
  · exact B805011
  · exact B805015
  · exact B805019
  · exact B805023
  · exact B805027
  · exact B805031
  · exact B805035
  · exact B805039
  · exact B805043
  · exact B805047
  · exact B805051
  · exact B805055
  · exact B805059
  · exact B805063
  · exact B805067
  · exact B805071
  · exact B805075
  · exact B805079
  · exact B805083
  · exact B805087
  · exact B805091
  · exact B805095
  · exact B805099
  · exact B805103
  · exact B805107
  · exact B805111
  · exact B805115
  · exact B805119
  · exact B805123
  · exact B805127
  · exact B805131
  · exact B805135
  · exact B805139

theorem C1 (j : ℕ) (h1 : 201285 ≤ j) (h2 : j ≤ 201585) : Blo 802343 (4 * j + 3) := by
  interval_cases j
  · exact B805143
  · exact B805147
  · exact B805151
  · exact B805155
  · exact B805159
  · exact B805163
  · exact B805167
  · exact B805171
  · exact B805175
  · exact B805179
  · exact B805183
  · exact B805187
  · exact B805191
  · exact B805195
  · exact B805199
  · exact B805203
  · exact B805207
  · exact B805211
  · exact B805215
  · exact B805219
  · exact B805223
  · exact B805227
  · exact B805231
  · exact B805235
  · exact B805239
  · exact B805243
  · exact B805247
  · exact B805251
  · exact B805255
  · exact B805259
  · exact B805263
  · exact B805267
  · exact B805271
  · exact B805275
  · exact B805279
  · exact B805283
  · exact B805287
  · exact B805291
  · exact B805295
  · exact B805299
  · exact B805303
  · exact B805307
  · exact B805311
  · exact B805315
  · exact B805319
  · exact B805323
  · exact B805327
  · exact B805331
  · exact B805335
  · exact B805339
  · exact B805343
  · exact B805347
  · exact B805351
  · exact B805355
  · exact B805359
  · exact B805363
  · exact B805367
  · exact B805371
  · exact B805375
  · exact B805379
  · exact B805383
  · exact B805387
  · exact B805391
  · exact B805395
  · exact B805399
  · exact B805403
  · exact B805407
  · exact B805411
  · exact B805415
  · exact B805419
  · exact B805423
  · exact B805427
  · exact B805431
  · exact B805435
  · exact B805439
  · exact B805443
  · exact B805447
  · exact B805451
  · exact B805455
  · exact B805459
  · exact B805463
  · exact B805467
  · exact B805471
  · exact B805475
  · exact B805479
  · exact B805483
  · exact B805487
  · exact B805491
  · exact B805495
  · exact B805499
  · exact B805503
  · exact B805507
  · exact B805511
  · exact B805515
  · exact B805519
  · exact B805523
  · exact B805527
  · exact B805531
  · exact B805535
  · exact B805539
  · exact B805543
  · exact B805547
  · exact B805551
  · exact B805555
  · exact B805559
  · exact B805563
  · exact B805567
  · exact B805571
  · exact B805575
  · exact B805579
  · exact B805583
  · exact B805587
  · exact B805591
  · exact B805595
  · exact B805599
  · exact B805603
  · exact B805607
  · exact B805611
  · exact B805615
  · exact B805619
  · exact B805623
  · exact B805627
  · exact B805631
  · exact B805635
  · exact B805639
  · exact B805643
  · exact B805647
  · exact B805651
  · exact B805655
  · exact B805659
  · exact B805663
  · exact B805667
  · exact B805671
  · exact B805675
  · exact B805679
  · exact B805683
  · exact B805687
  · exact B805691
  · exact B805695
  · exact B805699
  · exact B805703
  · exact B805707
  · exact B805711
  · exact B805715
  · exact B805719
  · exact B805723
  · exact B805727
  · exact B805731
  · exact B805735
  · exact B805739
  · exact B805743
  · exact B805747
  · exact B805751
  · exact B805755
  · exact B805759
  · exact B805763
  · exact B805767
  · exact B805771
  · exact B805775
  · exact B805779
  · exact B805783
  · exact B805787
  · exact B805791
  · exact B805795
  · exact B805799
  · exact B805803
  · exact B805807
  · exact B805811
  · exact B805815
  · exact B805819
  · exact B805823
  · exact B805827
  · exact B805831
  · exact B805835
  · exact B805839
  · exact B805843
  · exact B805847
  · exact B805851
  · exact B805855
  · exact B805859
  · exact B805863
  · exact B805867
  · exact B805871
  · exact B805875
  · exact B805879
  · exact B805883
  · exact B805887
  · exact B805891
  · exact B805895
  · exact B805899
  · exact B805903
  · exact B805907
  · exact B805911
  · exact B805915
  · exact B805919
  · exact B805923
  · exact B805927
  · exact B805931
  · exact B805935
  · exact B805939
  · exact B805943
  · exact B805947
  · exact B805951
  · exact B805955
  · exact B805959
  · exact B805963
  · exact B805967
  · exact B805971
  · exact B805975
  · exact B805979
  · exact B805983
  · exact B805987
  · exact B805991
  · exact B805995
  · exact B805999
  · exact B806003
  · exact B806007
  · exact B806011
  · exact B806015
  · exact B806019
  · exact B806023
  · exact B806027
  · exact B806031
  · exact B806035
  · exact B806039
  · exact B806043
  · exact B806047
  · exact B806051
  · exact B806055
  · exact B806059
  · exact B806063
  · exact B806067
  · exact B806071
  · exact B806075
  · exact B806079
  · exact B806083
  · exact B806087
  · exact B806091
  · exact B806095
  · exact B806099
  · exact B806103
  · exact B806107
  · exact B806111
  · exact B806115
  · exact B806119
  · exact B806123
  · exact B806127
  · exact B806131
  · exact B806135
  · exact B806139
  · exact B806143
  · exact B806147
  · exact B806151
  · exact B806155
  · exact B806159
  · exact B806163
  · exact B806167
  · exact B806171
  · exact B806175
  · exact B806179
  · exact B806183
  · exact B806187
  · exact B806191
  · exact B806195
  · exact B806199
  · exact B806203
  · exact B806207
  · exact B806211
  · exact B806215
  · exact B806219
  · exact B806223
  · exact B806227
  · exact B806231
  · exact B806235
  · exact B806239
  · exact B806243
  · exact B806247
  · exact B806251
  · exact B806255
  · exact B806259
  · exact B806263
  · exact B806267
  · exact B806271
  · exact B806275
  · exact B806279
  · exact B806283
  · exact B806287
  · exact B806291
  · exact B806295
  · exact B806299
  · exact B806303
  · exact B806307
  · exact B806311
  · exact B806315
  · exact B806319
  · exact B806323
  · exact B806327
  · exact B806331
  · exact B806335
  · exact B806339
  · exact B806343

theorem solution (m : ℕ) (hlo : 802343 ≤ m) (hhi : m ≤ 806343) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 200585 ≤ j := by omega
    have hj2 : j ≤ 201585 := by omega
    have hb : Blo 802343 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 201285 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
