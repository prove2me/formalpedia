-- Prove2me | solution 1 for syracuse_descends_range_1839621_1841621
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:03:20.447889+00:00
-- url     : https://prove2.me/submissions/59472847-1339-4f4d-8dc3-42846cda8ed0

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


theorem B2760725 : Blo 1839621 2760725 := bbase (se 6 (by rfl) ⟨64704, by rfl⟩ : syracuseStep 2760725 = 129409) (by norm_num)
theorem B3104797 : Blo 1839621 3104797 := bbase (se 3 (by rfl) ⟨582149, by rfl⟩ : syracuseStep 3104797 = 1164299) (by norm_num)
theorem B2760749 : Blo 1839621 2760749 := bbase (se 3 (by rfl) ⟨517640, by rfl⟩ : syracuseStep 2760749 = 1035281) (by norm_num)
theorem B6987829 : Blo 1839621 6987829 := bbase (se 5 (by rfl) ⟨327554, by rfl⟩ : syracuseStep 6987829 = 655109) (by norm_num)
theorem B2760773 : Blo 1839621 2760773 := bbase (se 4 (by rfl) ⟨258822, by rfl⟩ : syracuseStep 2760773 = 517645) (by norm_num)
theorem B6209621 : Blo 1839621 6209621 := bbase (se 8 (by rfl) ⟨36384, by rfl⟩ : syracuseStep 6209621 = 72769) (by norm_num)
theorem B10485845 : Blo 1839621 10485845 := bbase (se 8 (by rfl) ⟨61440, by rfl⟩ : syracuseStep 10485845 = 122881) (by norm_num)
theorem B2760797 : Blo 1839621 2760797 := bbase (se 3 (by rfl) ⟨517649, by rfl⟩ : syracuseStep 2760797 = 1035299) (by norm_num)
theorem B6635621 : Blo 1839621 6635621 := bbase (se 4 (by rfl) ⟨622089, by rfl⟩ : syracuseStep 6635621 = 1244179) (by norm_num)
theorem B2949221 : Blo 1839621 2949221 := bbase (se 4 (by rfl) ⟨276489, by rfl⟩ : syracuseStep 2949221 = 552979) (by norm_num)
theorem B4972661 : Blo 1839621 4972661 := bbase (se 5 (by rfl) ⟨233093, by rfl⟩ : syracuseStep 4972661 = 466187) (by norm_num)
theorem B3104885 : Blo 1839621 3104885 := bbase (se 5 (by rfl) ⟨145541, by rfl⟩ : syracuseStep 3104885 = 291083) (by norm_num)
theorem B2760821 : Blo 1839621 2760821 := bbase (se 5 (by rfl) ⟨129413, by rfl⟩ : syracuseStep 2760821 = 258827) (by norm_num)
theorem B9322613 : Blo 1839621 9322613 := bbase (se 5 (by rfl) ⟨436997, by rfl⟩ : syracuseStep 9322613 = 873995) (by norm_num)
theorem B2760845 : Blo 1839621 2760845 := bbase (se 3 (by rfl) ⟨517658, by rfl⟩ : syracuseStep 2760845 = 1035317) (by norm_num)
theorem B2760869 : Blo 1839621 2760869 := bbase (se 4 (by rfl) ⟨258831, by rfl⟩ : syracuseStep 2760869 = 517663) (by norm_num)
theorem B2760893 : Blo 1839621 2760893 := bbase (se 3 (by rfl) ⟨517667, by rfl⟩ : syracuseStep 2760893 = 1035335) (by norm_num)
theorem B10477781 : Blo 1839621 10477781 := bbase (se 7 (by rfl) ⟨122786, by rfl⟩ : syracuseStep 10477781 = 245573) (by norm_num)
theorem B2760917 : Blo 1839621 2760917 := bbase (se 7 (by rfl) ⟨32354, by rfl⟩ : syracuseStep 2760917 = 64709) (by norm_num)
theorem B3932381 : Blo 1839621 3932381 := bbase (se 3 (by rfl) ⟨737321, by rfl⟩ : syracuseStep 3932381 = 1474643) (by norm_num)
theorem B4423909 : Blo 1839621 4423909 := bbase (se 4 (by rfl) ⟨414741, by rfl⟩ : syracuseStep 4423909 = 829483) (by norm_num)
theorem B2760941 : Blo 1839621 2760941 := bbase (se 3 (by rfl) ⟨517676, by rfl⟩ : syracuseStep 2760941 = 1035353) (by norm_num)
theorem B3105013 : Blo 1839621 3105013 := bbase (se 5 (by rfl) ⟨145547, by rfl⟩ : syracuseStep 3105013 = 291095) (by norm_num)
theorem B2760965 : Blo 1839621 2760965 := bbase (se 4 (by rfl) ⟨258840, by rfl⟩ : syracuseStep 2760965 = 517681) (by norm_num)
theorem B4661509 : Blo 1839621 4661509 := bbase (se 4 (by rfl) ⟨437016, by rfl⟩ : syracuseStep 4661509 = 874033) (by norm_num)
theorem B1966361 : Blo 1839621 1966361 := bbase (se 2 (by rfl) ⟨737385, by rfl⟩ : syracuseStep 1966361 = 1474771) (by norm_num)
theorem B2760989 : Blo 1839621 2760989 := bbase (se 3 (by rfl) ⟨517685, by rfl⟩ : syracuseStep 2760989 = 1035371) (by norm_num)
theorem B2761013 : Blo 1839621 2761013 := bbase (se 5 (by rfl) ⟨129422, by rfl⟩ : syracuseStep 2761013 = 258845) (by norm_num)
theorem B4424005 : Blo 1839621 4424005 := bbase (se 4 (by rfl) ⟨414750, by rfl⟩ : syracuseStep 4424005 = 829501) (by norm_num)
theorem B3105101 : Blo 1839621 3105101 := bbase (se 3 (by rfl) ⟨582206, by rfl⟩ : syracuseStep 3105101 = 1164413) (by norm_num)
theorem B2761037 : Blo 1839621 2761037 := bbase (se 3 (by rfl) ⟨517694, by rfl⟩ : syracuseStep 2761037 = 1035389) (by norm_num)
theorem B6988133 : Blo 1839621 6988133 := bbase (se 4 (by rfl) ⟨655137, by rfl⟩ : syracuseStep 6988133 = 1310275) (by norm_num)
theorem B2761061 : Blo 1839621 2761061 := bbase (se 4 (by rfl) ⟨258849, by rfl⟩ : syracuseStep 2761061 = 517699) (by norm_num)
theorem B2761085 : Blo 1839621 2761085 := bbase (se 3 (by rfl) ⟨517703, by rfl⟩ : syracuseStep 2761085 = 1035407) (by norm_num)
theorem B2761109 : Blo 1839621 2761109 := bbase (se 6 (by rfl) ⟨64713, by rfl⟩ : syracuseStep 2761109 = 129427) (by norm_num)
theorem B2761133 : Blo 1839621 2761133 := bbase (se 3 (by rfl) ⟨517712, by rfl⟩ : syracuseStep 2761133 = 1035425) (by norm_num)
theorem B2761157 : Blo 1839621 2761157 := bbase (se 4 (by rfl) ⟨258858, by rfl⟩ : syracuseStep 2761157 = 517717) (by norm_num)
theorem B3105229 : Blo 1839621 3105229 := bbase (se 3 (by rfl) ⟨582230, by rfl⟩ : syracuseStep 3105229 = 1164461) (by norm_num)
theorem B3318221 : Blo 1839621 3318221 := bbase (se 3 (by rfl) ⟨622166, by rfl⟩ : syracuseStep 3318221 = 1244333) (by norm_num)
theorem B2761181 : Blo 1839621 2761181 := bbase (se 3 (by rfl) ⟨517721, by rfl⟩ : syracuseStep 2761181 = 1035443) (by norm_num)
theorem B2621917 : Blo 1839621 2621917 := bbase (se 3 (by rfl) ⟨491609, by rfl⟩ : syracuseStep 2621917 = 983219) (by norm_num)
theorem B2761205 : Blo 1839621 2761205 := bbase (se 5 (by rfl) ⟨129431, by rfl⟩ : syracuseStep 2761205 = 258863) (by norm_num)
theorem B6210053 : Blo 1839621 6210053 := bbase (se 4 (by rfl) ⟨582192, by rfl⟩ : syracuseStep 6210053 = 1164385) (by norm_num)
theorem B2761229 : Blo 1839621 2761229 := bbase (se 3 (by rfl) ⟨517730, by rfl⟩ : syracuseStep 2761229 = 1035461) (by norm_num)
theorem B1966609 : Blo 1839621 1966609 := bbase (se 2 (by rfl) ⟨737478, by rfl⟩ : syracuseStep 1966609 = 1474957) (by norm_num)
theorem B9314837 : Blo 1839621 9314837 := bbase (se 6 (by rfl) ⟨218316, by rfl⟩ : syracuseStep 9314837 = 436633) (by norm_num)
theorem B5243413 : Blo 1839621 5243413 := bbase (se 6 (by rfl) ⟨122892, by rfl⟩ : syracuseStep 5243413 = 245785) (by norm_num)
theorem B2212373 : Blo 1839621 2212373 := bbase (se 6 (by rfl) ⟨51852, by rfl⟩ : syracuseStep 2212373 = 103705) (by norm_num)
theorem B3105317 : Blo 1839621 3105317 := bbase (se 4 (by rfl) ⟨291123, by rfl⟩ : syracuseStep 3105317 = 582247) (by norm_num)
theorem B2761253 : Blo 1839621 2761253 := bbase (se 4 (by rfl) ⟨258867, by rfl⟩ : syracuseStep 2761253 = 517735) (by norm_num)
theorem B2761277 : Blo 1839621 2761277 := bbase (se 3 (by rfl) ⟨517739, by rfl⟩ : syracuseStep 2761277 = 1035479) (by norm_num)
theorem B2761301 : Blo 1839621 2761301 := bbase (se 8 (by rfl) ⟨16179, by rfl⟩ : syracuseStep 2761301 = 32359) (by norm_num)
theorem B2761325 : Blo 1839621 2761325 := bbase (se 3 (by rfl) ⟨517748, by rfl⟩ : syracuseStep 2761325 = 1035497) (by norm_num)
theorem B2761349 : Blo 1839621 2761349 := bbase (se 4 (by rfl) ⟨258876, by rfl⟩ : syracuseStep 2761349 = 517753) (by norm_num)
theorem B2761373 : Blo 1839621 2761373 := bbase (se 3 (by rfl) ⟨517757, by rfl⟩ : syracuseStep 2761373 = 1035515) (by norm_num)
theorem B4973221 : Blo 1839621 4973221 := bbase (se 4 (by rfl) ⟨466239, by rfl⟩ : syracuseStep 4973221 = 932479) (by norm_num)
theorem B3105445 : Blo 1839621 3105445 := bbase (se 4 (by rfl) ⟨291135, by rfl⟩ : syracuseStep 3105445 = 582271) (by norm_num)
theorem B2761397 : Blo 1839621 2761397 := bbase (se 5 (by rfl) ⟨129440, by rfl⟩ : syracuseStep 2761397 = 258881) (by norm_num)
theorem B2761421 : Blo 1839621 2761421 := bbase (se 3 (by rfl) ⟨517766, by rfl⟩ : syracuseStep 2761421 = 1035533) (by norm_num)
theorem B2761445 : Blo 1839621 2761445 := bbase (se 4 (by rfl) ⟨258885, by rfl⟩ : syracuseStep 2761445 = 517771) (by norm_num)
theorem B3318509 : Blo 1839621 3318509 := bbase (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) (by norm_num)
theorem B3105533 : Blo 1839621 3105533 := bbase (se 3 (by rfl) ⟨582287, by rfl⟩ : syracuseStep 3105533 = 1164575) (by norm_num)
theorem B2761469 : Blo 1839621 2761469 := bbase (se 3 (by rfl) ⟨517775, by rfl⟩ : syracuseStep 2761469 = 1035551) (by norm_num)
theorem B2761493 : Blo 1839621 2761493 := bbase (se 6 (by rfl) ⟨64722, by rfl⟩ : syracuseStep 2761493 = 129445) (by norm_num)
theorem B2761517 : Blo 1839621 2761517 := bbase (se 3 (by rfl) ⟨517784, by rfl⟩ : syracuseStep 2761517 = 1035569) (by norm_num)
theorem B2761541 : Blo 1839621 2761541 := bbase (se 4 (by rfl) ⟨258894, by rfl⟩ : syracuseStep 2761541 = 517789) (by norm_num)
theorem B37798741 : Blo 1839621 37798741 := bbase (se 9 (by rfl) ⟨110738, by rfl⟩ : syracuseStep 37798741 = 221477) (by norm_num)
theorem B2761565 : Blo 1839621 2761565 := bbase (se 3 (by rfl) ⟨517793, by rfl⟩ : syracuseStep 2761565 = 1035587) (by norm_num)
theorem B2761589 : Blo 1839621 2761589 := bbase (se 5 (by rfl) ⟨129449, by rfl⟩ : syracuseStep 2761589 = 258899) (by norm_num)
theorem B3105661 : Blo 1839621 3105661 := bbase (se 3 (by rfl) ⟨582311, by rfl⟩ : syracuseStep 3105661 = 1164623) (by norm_num)
theorem B2761613 : Blo 1839621 2761613 := bbase (se 3 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 2761613 = 1035605) (by norm_num)
theorem B11797397 : Blo 1839621 11797397 := bbase (se 6 (by rfl) ⟨276501, by rfl⟩ : syracuseStep 11797397 = 553003) (by norm_num)
theorem B2761637 : Blo 1839621 2761637 := bbase (se 4 (by rfl) ⟨258903, by rfl⟩ : syracuseStep 2761637 = 517807) (by norm_num)
theorem B6210485 : Blo 1839621 6210485 := bbase (se 5 (by rfl) ⟨291116, by rfl⟩ : syracuseStep 6210485 = 582233) (by norm_num)
theorem B2761661 : Blo 1839621 2761661 := bbase (se 3 (by rfl) ⟨517811, by rfl⟩ : syracuseStep 2761661 = 1035623) (by norm_num)
theorem B2098129 : Blo 1839621 2098129 := bbase (se 2 (by rfl) ⟨786798, by rfl⟩ : syracuseStep 2098129 = 1573597) (by norm_num)
theorem B3105749 : Blo 1839621 3105749 := bbase (se 7 (by rfl) ⟨36395, by rfl⟩ : syracuseStep 3105749 = 72791) (by norm_num)
theorem B2761685 : Blo 1839621 2761685 := bbase (se 7 (by rfl) ⟨32363, by rfl⟩ : syracuseStep 2761685 = 64727) (by norm_num)
theorem B2761709 : Blo 1839621 2761709 := bbase (se 3 (by rfl) ⟨517820, by rfl⟩ : syracuseStep 2761709 = 1035641) (by norm_num)
theorem B2761733 : Blo 1839621 2761733 := bbase (se 4 (by rfl) ⟨258912, by rfl⟩ : syracuseStep 2761733 = 517825) (by norm_num)
theorem B26240021 : Blo 1839621 26240021 := bbase (se 6 (by rfl) ⟨615000, by rfl⟩ : syracuseStep 26240021 = 1230001) (by norm_num)
theorem B2761757 : Blo 1839621 2761757 := bbase (se 3 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 2761757 = 1035659) (by norm_num)
theorem B2761781 : Blo 1839621 2761781 := bbase (se 5 (by rfl) ⟨129458, by rfl⟩ : syracuseStep 2761781 = 258917) (by norm_num)
theorem B2761805 : Blo 1839621 2761805 := bbase (se 3 (by rfl) ⟨517838, by rfl⟩ : syracuseStep 2761805 = 1035677) (by norm_num)
theorem B3105877 : Blo 1839621 3105877 := bbase (se 8 (by rfl) ⟨18198, by rfl⟩ : syracuseStep 3105877 = 36397) (by norm_num)
theorem B2761829 : Blo 1839621 2761829 := bbase (se 4 (by rfl) ⟨258921, by rfl⟩ : syracuseStep 2761829 = 517843) (by norm_num)
theorem B2761853 : Blo 1839621 2761853 := bbase (se 3 (by rfl) ⟨517847, by rfl⟩ : syracuseStep 2761853 = 1035695) (by norm_num)
theorem B2761877 : Blo 1839621 2761877 := bbase (se 6 (by rfl) ⟨64731, by rfl⟩ : syracuseStep 2761877 = 129463) (by norm_num)
theorem B3105965 : Blo 1839621 3105965 := bbase (se 3 (by rfl) ⟨582368, by rfl⟩ : syracuseStep 3105965 = 1164737) (by norm_num)
theorem B2761901 : Blo 1839621 2761901 := bbase (se 3 (by rfl) ⟨517856, by rfl⟩ : syracuseStep 2761901 = 1035713) (by norm_num)
theorem B2761925 : Blo 1839621 2761925 := bbase (se 4 (by rfl) ⟨258930, by rfl⟩ : syracuseStep 2761925 = 517861) (by norm_num)
theorem B2761949 : Blo 1839621 2761949 := bbase (se 3 (by rfl) ⟨517865, by rfl⟩ : syracuseStep 2761949 = 1035731) (by norm_num)
theorem B5899493 : Blo 1839621 5899493 := bbase (se 4 (by rfl) ⟨553077, by rfl⟩ : syracuseStep 5899493 = 1106155) (by norm_num)
theorem B2761973 : Blo 1839621 2761973 := bbase (se 5 (by rfl) ⟨129467, by rfl⟩ : syracuseStep 2761973 = 258935) (by norm_num)
theorem B10487029 : Blo 1839621 10487029 := bbase (se 5 (by rfl) ⟨491579, by rfl⟩ : syracuseStep 10487029 = 983159) (by norm_num)
theorem B2761997 : Blo 1839621 2761997 := bbase (se 3 (by rfl) ⟨517874, by rfl⟩ : syracuseStep 2761997 = 1035749) (by norm_num)
theorem B2360605 : Blo 1839621 2360605 := bbase (se 3 (by rfl) ⟨442613, by rfl⟩ : syracuseStep 2360605 = 885227) (by norm_num)
theorem B2762021 : Blo 1839621 2762021 := bbase (se 4 (by rfl) ⟨258939, by rfl⟩ : syracuseStep 2762021 = 517879) (by norm_num)
theorem B3106093 : Blo 1839621 3106093 := bbase (se 3 (by rfl) ⟨582392, by rfl⟩ : syracuseStep 3106093 = 1164785) (by norm_num)
theorem B2762045 : Blo 1839621 2762045 := bbase (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) (by norm_num)
theorem B2762069 : Blo 1839621 2762069 := bbase (se 12 (by rfl) ⟨1011, by rfl⟩ : syracuseStep 2762069 = 2023) (by norm_num)
theorem B6210917 : Blo 1839621 6210917 := bbase (se 4 (by rfl) ⟨582273, by rfl⟩ : syracuseStep 6210917 = 1164547) (by norm_num)
theorem B2762093 : Blo 1839621 2762093 := bbase (se 3 (by rfl) ⟨517892, by rfl⟩ : syracuseStep 2762093 = 1035785) (by norm_num)
theorem B3106181 : Blo 1839621 3106181 := bbase (se 4 (by rfl) ⟨291204, by rfl⟩ : syracuseStep 3106181 = 582409) (by norm_num)
theorem B2762117 : Blo 1839621 2762117 := bbase (se 4 (by rfl) ⟨258948, by rfl⟩ : syracuseStep 2762117 = 517897) (by norm_num)
theorem B2762141 : Blo 1839621 2762141 := bbase (se 3 (by rfl) ⟨517901, by rfl⟩ : syracuseStep 2762141 = 1035803) (by norm_num)
theorem B2762165 : Blo 1839621 2762165 := bbase (se 5 (by rfl) ⟨129476, by rfl⟩ : syracuseStep 2762165 = 258953) (by norm_num)
theorem B2762189 : Blo 1839621 2762189 := bbase (se 3 (by rfl) ⟨517910, by rfl⟩ : syracuseStep 2762189 = 1035821) (by norm_num)
theorem B2762213 : Blo 1839621 2762213 := bbase (se 4 (by rfl) ⟨258957, by rfl⟩ : syracuseStep 2762213 = 517915) (by norm_num)
theorem B2360821 : Blo 1839621 2360821 := bbase (se 5 (by rfl) ⟨110663, by rfl⟩ : syracuseStep 2360821 = 221327) (by norm_num)
theorem B2762237 : Blo 1839621 2762237 := bbase (se 3 (by rfl) ⟨517919, by rfl⟩ : syracuseStep 2762237 = 1035839) (by norm_num)
theorem B3106309 : Blo 1839621 3106309 := bbase (se 4 (by rfl) ⟨291216, by rfl⟩ : syracuseStep 3106309 = 582433) (by norm_num)
theorem B2762261 : Blo 1839621 2762261 := bbase (se 6 (by rfl) ⟨64740, by rfl⟩ : syracuseStep 2762261 = 129481) (by norm_num)
theorem B2762285 : Blo 1839621 2762285 := bbase (se 3 (by rfl) ⟨517928, by rfl⟩ : syracuseStep 2762285 = 1035857) (by norm_num)
theorem B4195901 : Blo 1839621 4195901 := bbase (se 3 (by rfl) ⟨786731, by rfl⟩ : syracuseStep 4195901 = 1573463) (by norm_num)
theorem B2762309 : Blo 1839621 2762309 := bbase (se 4 (by rfl) ⟨258966, by rfl⟩ : syracuseStep 2762309 = 517933) (by norm_num)
theorem B3106397 : Blo 1839621 3106397 := bbase (se 3 (by rfl) ⟨582449, by rfl⟩ : syracuseStep 3106397 = 1164899) (by norm_num)
theorem B2762333 : Blo 1839621 2762333 := bbase (se 3 (by rfl) ⟨517937, by rfl⟩ : syracuseStep 2762333 = 1035875) (by norm_num)
theorem B2762357 : Blo 1839621 2762357 := bbase (se 5 (by rfl) ⟨129485, by rfl⟩ : syracuseStep 2762357 = 258971) (by norm_num)
theorem B2762381 : Blo 1839621 2762381 := bbase (se 3 (by rfl) ⟨517946, by rfl⟩ : syracuseStep 2762381 = 1035893) (by norm_num)
theorem B2762405 : Blo 1839621 2762405 := bbase (se 4 (by rfl) ⟨258975, by rfl⟩ : syracuseStep 2762405 = 517951) (by norm_num)
theorem B2762429 : Blo 1839621 2762429 := bbase (se 3 (by rfl) ⟨517955, by rfl⟩ : syracuseStep 2762429 = 1035911) (by norm_num)
theorem B3540677 : Blo 1839621 3540677 := bbase (se 4 (by rfl) ⟨331938, by rfl⟩ : syracuseStep 3540677 = 663877) (by norm_num)
theorem B3106525 : Blo 1839621 3106525 := bbase (se 3 (by rfl) ⟨582473, by rfl⟩ : syracuseStep 3106525 = 1164947) (by norm_num)
theorem B6211349 : Blo 1839621 6211349 := bbase (se 6 (by rfl) ⟨145578, by rfl⟩ : syracuseStep 6211349 = 291157) (by norm_num)
theorem B9316133 : Blo 1839621 9316133 := bbase (se 4 (by rfl) ⟨873387, by rfl⟩ : syracuseStep 9316133 = 1746775) (by norm_num)
theorem B2328365 : Blo 1839621 2328365 := bbase (se 3 (by rfl) ⟨436568, by rfl⟩ : syracuseStep 2328365 = 873137) (by norm_num)
theorem B4974389 : Blo 1839621 4974389 := bbase (se 5 (by rfl) ⟨233174, by rfl⟩ : syracuseStep 4974389 = 466349) (by norm_num)
theorem B3106613 : Blo 1839621 3106613 := bbase (se 5 (by rfl) ⟨145622, by rfl⟩ : syracuseStep 3106613 = 291245) (by norm_num)
theorem B2328421 : Blo 1839621 2328421 := bbase (se 4 (by rfl) ⟨218289, by rfl⟩ : syracuseStep 2328421 = 436579) (by norm_num)
theorem B1992557 : Blo 1839621 1992557 := bbase (se 3 (by rfl) ⟨373604, by rfl⟩ : syracuseStep 1992557 = 747209) (by norm_num)
theorem B7866229 : Blo 1839621 7866229 := bbase (se 5 (by rfl) ⟨368729, by rfl⟩ : syracuseStep 7866229 = 737459) (by norm_num)
theorem B19400597 : Blo 1839621 19400597 := bbase (se 6 (by rfl) ⟨454701, by rfl⟩ : syracuseStep 19400597 = 909403) (by norm_num)
theorem B3106741 : Blo 1839621 3106741 := bbase (se 5 (by rfl) ⟨145628, by rfl⟩ : syracuseStep 3106741 = 291257) (by norm_num)
theorem B2328517 : Blo 1839621 2328517 := bbase (se 4 (by rfl) ⟨218298, by rfl⟩ : syracuseStep 2328517 = 436597) (by norm_num)
theorem B3106829 : Blo 1839621 3106829 := bbase (se 3 (by rfl) ⟨582530, by rfl⟩ : syracuseStep 3106829 = 1165061) (by norm_num)
theorem B13273109 : Blo 1839621 13273109 := bbase (se 6 (by rfl) ⟨311088, by rfl⟩ : syracuseStep 13273109 = 622177) (by norm_num)
theorem B3541085 : Blo 1839621 3541085 := bbase (se 3 (by rfl) ⟨663953, by rfl⟩ : syracuseStep 3541085 = 1327907) (by norm_num)
theorem B6383717 : Blo 1839621 6383717 := bbase (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) (by norm_num)
theorem B2328689 : Blo 1839621 2328689 := bbase (se 2 (by rfl) ⟨873258, by rfl⟩ : syracuseStep 2328689 = 1746517) (by norm_num)
theorem B4974725 : Blo 1839621 4974725 := bbase (se 4 (by rfl) ⟨466380, by rfl⟩ : syracuseStep 4974725 = 932761) (by norm_num)
theorem B3106957 : Blo 1839621 3106957 := bbase (se 3 (by rfl) ⟨582554, by rfl⟩ : syracuseStep 3106957 = 1165109) (by norm_num)
theorem B2328745 : Blo 1839621 2328745 := bbase (se 2 (by rfl) ⟨873279, by rfl⟩ : syracuseStep 2328745 = 1746559) (by norm_num)
theorem B4139189 : Blo 1839621 4139189 := bbase (se 5 (by rfl) ⟨194024, by rfl⟩ : syracuseStep 4139189 = 388049) (by norm_num)
theorem B6211781 : Blo 1839621 6211781 := bbase (se 4 (by rfl) ⟨582354, by rfl⟩ : syracuseStep 6211781 = 1164709) (by norm_num)
theorem B3107045 : Blo 1839621 3107045 := bbase (se 4 (by rfl) ⟨291285, by rfl⟩ : syracuseStep 3107045 = 582571) (by norm_num)
theorem B13977845 : Blo 1839621 13977845 := bbase (se 5 (by rfl) ⟨655211, by rfl⟩ : syracuseStep 13977845 = 1310423) (by norm_num)
theorem B4139261 : Blo 1839621 4139261 := bbase (se 3 (by rfl) ⟨776111, by rfl⟩ : syracuseStep 4139261 = 1552223) (by norm_num)
theorem B2328841 : Blo 1839621 2328841 := bbase (se 2 (by rfl) ⟨873315, by rfl⟩ : syracuseStep 2328841 = 1746631) (by norm_num)
theorem B3541277 : Blo 1839621 3541277 := bbase (se 3 (by rfl) ⟨663989, by rfl⟩ : syracuseStep 3541277 = 1327979) (by norm_num)
theorem B4139333 : Blo 1839621 4139333 := bbase (se 4 (by rfl) ⟨388062, by rfl⟩ : syracuseStep 4139333 = 776125) (by norm_num)
theorem B3107173 : Blo 1839621 3107173 := bbase (se 4 (by rfl) ⟨291297, by rfl⟩ : syracuseStep 3107173 = 582595) (by norm_num)
theorem B4139405 : Blo 1839621 4139405 := bbase (se 3 (by rfl) ⟨776138, by rfl⟩ : syracuseStep 4139405 = 1552277) (by norm_num)
theorem B6990245 : Blo 1839621 6990245 := bbase (se 4 (by rfl) ⟨655335, by rfl⟩ : syracuseStep 6990245 = 1310671) (by norm_num)
theorem B2329013 : Blo 1839621 2329013 := bbase (se 5 (by rfl) ⟨109172, by rfl⟩ : syracuseStep 2329013 = 218345) (by norm_num)
theorem B3107261 : Blo 1839621 3107261 := bbase (se 3 (by rfl) ⟨582611, by rfl⟩ : syracuseStep 3107261 = 1165223) (by norm_num)
theorem B4139477 : Blo 1839621 4139477 := bbase (se 7 (by rfl) ⟨48509, by rfl⟩ : syracuseStep 4139477 = 97019) (by norm_num)
theorem B3729901 : Blo 1839621 3729901 := bbase (se 3 (by rfl) ⟨699356, by rfl⟩ : syracuseStep 3729901 = 1398713) (by norm_num)
theorem B2329069 : Blo 1839621 2329069 := bbase (se 3 (by rfl) ⟨436700, by rfl⟩ : syracuseStep 2329069 = 873401) (by norm_num)
theorem B4139549 : Blo 1839621 4139549 := bbase (se 3 (by rfl) ⟨776165, by rfl⟩ : syracuseStep 4139549 = 1552331) (by norm_num)
theorem B3107389 : Blo 1839621 3107389 := bbase (se 3 (by rfl) ⟨582635, by rfl⟩ : syracuseStep 3107389 = 1165271) (by norm_num)
theorem B2329165 : Blo 1839621 2329165 := bbase (se 3 (by rfl) ⟨436718, by rfl⟩ : syracuseStep 2329165 = 873437) (by norm_num)
theorem B4139621 : Blo 1839621 4139621 := bbase (se 4 (by rfl) ⟨388089, by rfl⟩ : syracuseStep 4139621 = 776179) (by norm_num)
theorem B6212213 : Blo 1839621 6212213 := bbase (se 5 (by rfl) ⟨291197, by rfl⟩ : syracuseStep 6212213 = 582395) (by norm_num)
theorem B15944309 : Blo 1839621 15944309 := bbase (se 5 (by rfl) ⟨747389, by rfl⟩ : syracuseStep 15944309 = 1494779) (by norm_num)
theorem B13970069 : Blo 1839621 13970069 := bbase (se 6 (by rfl) ⟨327423, by rfl⟩ : syracuseStep 13970069 = 654847) (by norm_num)
theorem B3107477 : Blo 1839621 3107477 := bbase (se 6 (by rfl) ⟨72831, by rfl⟩ : syracuseStep 3107477 = 145663) (by norm_num)
theorem B2099881 : Blo 1839621 2099881 := bbase (se 2 (by rfl) ⟨787455, by rfl⟩ : syracuseStep 2099881 = 1574911) (by norm_num)
theorem B4139693 : Blo 1839621 4139693 := bbase (se 3 (by rfl) ⟨776192, by rfl⟩ : syracuseStep 4139693 = 1552385) (by norm_num)
theorem B3492533 : Blo 1839621 3492533 := bbase (se 5 (by rfl) ⟨163712, by rfl⟩ : syracuseStep 3492533 = 327425) (by norm_num)
theorem B6990533 : Blo 1839621 6990533 := bbase (se 4 (by rfl) ⟨655362, by rfl⟩ : syracuseStep 6990533 = 1310725) (by norm_num)
theorem B4139765 : Blo 1839621 4139765 := bbase (se 5 (by rfl) ⟨194051, by rfl⟩ : syracuseStep 4139765 = 388103) (by norm_num)
theorem B8841973 : Blo 1839621 8841973 := bbase (se 5 (by rfl) ⟨414467, by rfl⟩ : syracuseStep 8841973 = 828935) (by norm_num)
theorem B2329337 : Blo 1839621 2329337 := bbase (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) (by norm_num)
theorem B3148541 : Blo 1839621 3148541 := bbase (se 3 (by rfl) ⟨590351, by rfl⟩ : syracuseStep 3148541 = 1180703) (by norm_num)
theorem B3107605 : Blo 1839621 3107605 := bbase (se 6 (by rfl) ⟨72834, by rfl⟩ : syracuseStep 3107605 = 145669) (by norm_num)
theorem B2329393 : Blo 1839621 2329393 := bbase (se 2 (by rfl) ⟨873522, by rfl⟩ : syracuseStep 2329393 = 1747045) (by norm_num)
theorem B2362165 : Blo 1839621 2362165 := bbase (se 5 (by rfl) ⟨110726, by rfl⟩ : syracuseStep 2362165 = 221453) (by norm_num)
theorem B4139837 : Blo 1839621 4139837 := bbase (se 3 (by rfl) ⟨776219, by rfl⟩ : syracuseStep 4139837 = 1552439) (by norm_num)
theorem B3107693 : Blo 1839621 3107693 := bbase (se 3 (by rfl) ⟨582692, by rfl⟩ : syracuseStep 3107693 = 1165385) (by norm_num)
theorem B4139909 : Blo 1839621 4139909 := bbase (se 4 (by rfl) ⟨388116, by rfl⟩ : syracuseStep 4139909 = 776233) (by norm_num)
theorem B2329489 : Blo 1839621 2329489 := bbase (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) (by norm_num)
theorem B4139981 : Blo 1839621 4139981 := bbase (se 3 (by rfl) ⟨776246, by rfl⟩ : syracuseStep 4139981 = 1552493) (by norm_num)
theorem B3492821 : Blo 1839621 3492821 := bbase (se 7 (by rfl) ⟨40931, by rfl⟩ : syracuseStep 3492821 = 81863) (by norm_num)
theorem B4140053 : Blo 1839621 4140053 := bbase (se 6 (by rfl) ⟨97032, by rfl⟩ : syracuseStep 4140053 = 194065) (by norm_num)
theorem B6212645 : Blo 1839621 6212645 := bbase (se 4 (by rfl) ⟨582435, by rfl⟩ : syracuseStep 6212645 = 1164871) (by norm_num)
theorem B9317429 : Blo 1839621 9317429 := bbase (se 5 (by rfl) ⟨436754, by rfl⟩ : syracuseStep 9317429 = 873509) (by norm_num)
theorem B2329661 : Blo 1839621 2329661 := bbase (se 3 (by rfl) ⟨436811, by rfl⟩ : syracuseStep 2329661 = 873623) (by norm_num)
theorem B4140125 : Blo 1839621 4140125 := bbase (se 3 (by rfl) ⟨776273, by rfl⟩ : syracuseStep 4140125 = 1552547) (by norm_num)
theorem B3492973 : Blo 1839621 3492973 := bbase (se 3 (by rfl) ⟨654932, by rfl⟩ : syracuseStep 3492973 = 1309865) (by norm_num)
theorem B2329717 : Blo 1839621 2329717 := bbase (se 5 (by rfl) ⟨109205, by rfl⟩ : syracuseStep 2329717 = 218411) (by norm_num)
theorem B4140197 : Blo 1839621 4140197 := bbase (se 4 (by rfl) ⟨388143, by rfl⟩ : syracuseStep 4140197 = 776287) (by norm_num)
theorem B2329813 : Blo 1839621 2329813 := bbase (se 7 (by rfl) ⟨27302, by rfl⟩ : syracuseStep 2329813 = 54605) (by norm_num)
theorem B4140269 : Blo 1839621 4140269 := bbase (se 3 (by rfl) ⟨776300, by rfl⟩ : syracuseStep 4140269 = 1552601) (by norm_num)
theorem B4197653 : Blo 1839621 4197653 := bbase (se 6 (by rfl) ⟨98382, by rfl⟩ : syracuseStep 4197653 = 196765) (by norm_num)
theorem B4140341 : Blo 1839621 4140341 := bbase (se 5 (by rfl) ⟨194078, by rfl⟩ : syracuseStep 4140341 = 388157) (by norm_num)
theorem B5311813 : Blo 1839621 5311813 := bbase (se 4 (by rfl) ⟨497982, by rfl⟩ : syracuseStep 5311813 = 995965) (by norm_num)
theorem B4721989 : Blo 1839621 4721989 := bbase (se 4 (by rfl) ⟨442686, by rfl⟩ : syracuseStep 4721989 = 885373) (by norm_num)
theorem B4197725 : Blo 1839621 4197725 := bbase (se 3 (by rfl) ⟨787073, by rfl⟩ : syracuseStep 4197725 = 1574147) (by norm_num)
theorem B4140413 : Blo 1839621 4140413 := bbase (se 3 (by rfl) ⟨776327, by rfl⟩ : syracuseStep 4140413 = 1552655) (by norm_num)
theorem B2329985 : Blo 1839621 2329985 := bbase (se 2 (by rfl) ⟨873744, by rfl⟩ : syracuseStep 2329985 = 1747489) (by norm_num)
theorem B3493277 : Blo 1839621 3493277 := bbase (se 3 (by rfl) ⟨654989, by rfl⟩ : syracuseStep 3493277 = 1309979) (by norm_num)
theorem B2330041 : Blo 1839621 2330041 := bbase (se 2 (by rfl) ⟨873765, by rfl⟩ : syracuseStep 2330041 = 1747531) (by norm_num)
theorem B5893573 : Blo 1839621 5893573 := bbase (se 4 (by rfl) ⟨552522, by rfl⟩ : syracuseStep 5893573 = 1105045) (by norm_num)
theorem B4140485 : Blo 1839621 4140485 := bbase (se 4 (by rfl) ⟨388170, by rfl⟩ : syracuseStep 4140485 = 776341) (by norm_num)
theorem B6213077 : Blo 1839621 6213077 := bbase (se 7 (by rfl) ⟨72809, by rfl⟩ : syracuseStep 6213077 = 145619) (by norm_num)
theorem B4656629 : Blo 1839621 4656629 := bbase (se 5 (by rfl) ⟨218279, by rfl⟩ : syracuseStep 4656629 = 436559) (by norm_num)
theorem B4140557 : Blo 1839621 4140557 := bbase (se 3 (by rfl) ⟨776354, by rfl⟩ : syracuseStep 4140557 = 1552709) (by norm_num)
theorem B2330137 : Blo 1839621 2330137 := bbase (se 2 (by rfl) ⟨873801, by rfl⟩ : syracuseStep 2330137 = 1747603) (by norm_num)
theorem B4140629 : Blo 1839621 4140629 := bbase (se 8 (by rfl) ⟨24261, by rfl⟩ : syracuseStep 4140629 = 48523) (by norm_num)
theorem B4140701 : Blo 1839621 4140701 := bbase (se 3 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 4140701 = 1552763) (by norm_num)
theorem B17682101 : Blo 1839621 17682101 := bbase (se 5 (by rfl) ⟨828848, by rfl⟩ : syracuseStep 17682101 = 1657697) (by norm_num)
theorem B2330309 : Blo 1839621 2330309 := bbase (se 4 (by rfl) ⟨218466, by rfl⟩ : syracuseStep 2330309 = 436933) (by norm_num)
theorem B19910357 : Blo 1839621 19910357 := bbase (se 7 (by rfl) ⟨233324, by rfl⟩ : syracuseStep 19910357 = 466649) (by norm_num)
theorem B4140773 : Blo 1839621 4140773 := bbase (se 4 (by rfl) ⟨388197, by rfl⟩ : syracuseStep 4140773 = 776395) (by norm_num)
theorem B2330365 : Blo 1839621 2330365 := bbase (se 3 (by rfl) ⟨436943, by rfl⟩ : syracuseStep 2330365 = 873887) (by norm_num)
theorem B4140845 : Blo 1839621 4140845 := bbase (se 3 (by rfl) ⟨776408, by rfl⟩ : syracuseStep 4140845 = 1552817) (by norm_num)
theorem B4656973 : Blo 1839621 4656973 := bbase (se 3 (by rfl) ⟨873182, by rfl⟩ : syracuseStep 4656973 = 1746365) (by norm_num)
theorem B2330461 : Blo 1839621 2330461 := bbase (se 3 (by rfl) ⟨436961, by rfl⟩ : syracuseStep 2330461 = 873923) (by norm_num)
theorem B6991717 : Blo 1839621 6991717 := bbase (se 4 (by rfl) ⟨655473, by rfl⟩ : syracuseStep 6991717 = 1310947) (by norm_num)
theorem B4140917 : Blo 1839621 4140917 := bbase (se 5 (by rfl) ⟨194105, by rfl⟩ : syracuseStep 4140917 = 388211) (by norm_num)
theorem B6213509 : Blo 1839621 6213509 := bbase (se 4 (by rfl) ⟨582516, by rfl⟩ : syracuseStep 6213509 = 1165033) (by norm_num)
theorem B4657085 : Blo 1839621 4657085 := bbase (se 3 (by rfl) ⟨873203, by rfl⟩ : syracuseStep 4657085 = 1746407) (by norm_num)
theorem B4140989 : Blo 1839621 4140989 := bbase (se 3 (by rfl) ⟨776435, by rfl⟩ : syracuseStep 4140989 = 1552871) (by norm_num)
theorem B47173589 : Blo 1839621 47173589 := bbase (se 7 (by rfl) ⟨552815, by rfl⟩ : syracuseStep 47173589 = 1105631) (by norm_num)
theorem B4141061 : Blo 1839621 4141061 := bbase (se 4 (by rfl) ⟨388224, by rfl⟩ : syracuseStep 4141061 = 776449) (by norm_num)
theorem B2330633 : Blo 1839621 2330633 := bbase (se 2 (by rfl) ⟨873987, by rfl⟩ : syracuseStep 2330633 = 1747975) (by norm_num)
theorem B2330689 : Blo 1839621 2330689 := bbase (se 2 (by rfl) ⟨874008, by rfl⟩ : syracuseStep 2330689 = 1748017) (by norm_num)
theorem B5599301 : Blo 1839621 5599301 := bbase (se 4 (by rfl) ⟨524934, by rfl⟩ : syracuseStep 5599301 = 1049869) (by norm_num)
theorem B4141133 : Blo 1839621 4141133 := bbase (se 3 (by rfl) ⟨776462, by rfl⟩ : syracuseStep 4141133 = 1552925) (by norm_num)
theorem B31092821 : Blo 1839621 31092821 := bbase (se 8 (by rfl) ⟨182184, by rfl⟩ : syracuseStep 31092821 = 364369) (by norm_num)
theorem B4657277 : Blo 1839621 4657277 := bbase (se 3 (by rfl) ⟨873239, by rfl⟩ : syracuseStep 4657277 = 1746479) (by norm_num)
theorem B3494029 : Blo 1839621 3494029 := bbase (se 3 (by rfl) ⟨655130, by rfl⟩ : syracuseStep 3494029 = 1310261) (by norm_num)
theorem B4141205 : Blo 1839621 4141205 := bbase (se 6 (by rfl) ⟨97059, by rfl⟩ : syracuseStep 4141205 = 194119) (by norm_num)
theorem B6992021 : Blo 1839621 6992021 := bbase (se 6 (by rfl) ⟨163875, by rfl⟩ : syracuseStep 6992021 = 327751) (by norm_num)
theorem B2330785 : Blo 1839621 2330785 := bbase (se 2 (by rfl) ⟨874044, by rfl⟩ : syracuseStep 2330785 = 1748089) (by norm_num)
theorem B4141277 : Blo 1839621 4141277 := bbase (se 3 (by rfl) ⟨776489, by rfl⟩ : syracuseStep 4141277 = 1552979) (by norm_num)
theorem B3731717 : Blo 1839621 3731717 := bbase (se 4 (by rfl) ⟨349848, by rfl⟩ : syracuseStep 3731717 = 699697) (by norm_num)
theorem B3494173 : Blo 1839621 3494173 := bbase (se 3 (by rfl) ⟨655157, by rfl⟩ : syracuseStep 3494173 = 1310315) (by norm_num)
theorem B4141349 : Blo 1839621 4141349 := bbase (se 4 (by rfl) ⟨388251, by rfl⟩ : syracuseStep 4141349 = 776503) (by norm_num)
theorem B6213941 : Blo 1839621 6213941 := bbase (se 5 (by rfl) ⟨291278, by rfl⟩ : syracuseStep 6213941 = 582557) (by norm_num)
theorem B9318725 : Blo 1839621 9318725 := bbase (se 4 (by rfl) ⟨873630, by rfl⟩ : syracuseStep 9318725 = 1747261) (by norm_num)
theorem B4141421 : Blo 1839621 4141421 := bbase (se 3 (by rfl) ⟨776516, by rfl⟩ : syracuseStep 4141421 = 1553033) (by norm_num)
theorem B4198765 : Blo 1839621 4198765 := bbase (se 3 (by rfl) ⟨787268, by rfl⟩ : syracuseStep 4198765 = 1574537) (by norm_num)
theorem B4141493 : Blo 1839621 4141493 := bbase (se 5 (by rfl) ⟨194132, by rfl⟩ : syracuseStep 4141493 = 388265) (by norm_num)
theorem B3494333 : Blo 1839621 3494333 := bbase (se 3 (by rfl) ⟨655187, by rfl⟩ : syracuseStep 3494333 = 1310375) (by norm_num)
theorem B4657621 : Blo 1839621 4657621 := bbase (se 7 (by rfl) ⟨54581, by rfl⟩ : syracuseStep 4657621 = 109163) (by norm_num)
theorem B2486773 : Blo 1839621 2486773 := bbase (se 5 (by rfl) ⟨116567, by rfl⟩ : syracuseStep 2486773 = 233135) (by norm_num)
theorem B4141565 : Blo 1839621 4141565 := bbase (se 3 (by rfl) ⟨776543, by rfl⟩ : syracuseStep 4141565 = 1553087) (by norm_num)
theorem B4420133 : Blo 1839621 4420133 := bbase (se 4 (by rfl) ⟨414387, by rfl⟩ : syracuseStep 4420133 = 828775) (by norm_num)
theorem B15340085 : Blo 1839621 15340085 := bbase (se 5 (by rfl) ⟨719066, by rfl⟩ : syracuseStep 15340085 = 1438133) (by norm_num)
theorem B4657733 : Blo 1839621 4657733 := bbase (se 4 (by rfl) ⟨436662, by rfl⟩ : syracuseStep 4657733 = 873325) (by norm_num)
theorem B4141637 : Blo 1839621 4141637 := bbase (se 4 (by rfl) ⟨388278, by rfl⟩ : syracuseStep 4141637 = 776557) (by norm_num)
theorem B3494477 : Blo 1839621 3494477 := bbase (se 3 (by rfl) ⟨655214, by rfl⟩ : syracuseStep 3494477 = 1310429) (by norm_num)
theorem B7967317 : Blo 1839621 7967317 := bbase (se 8 (by rfl) ⟨46683, by rfl⟩ : syracuseStep 7967317 = 93367) (by norm_num)
theorem B9704069 : Blo 1839621 9704069 := bbase (se 4 (by rfl) ⟨909756, by rfl⟩ : syracuseStep 9704069 = 1819513) (by norm_num)
theorem B4141709 : Blo 1839621 4141709 := bbase (se 3 (by rfl) ⟨776570, by rfl⟩ : syracuseStep 4141709 = 1553141) (by norm_num)
theorem B6632117 : Blo 1839621 6632117 := bbase (se 5 (by rfl) ⟨310880, by rfl⟩ : syracuseStep 6632117 = 621761) (by norm_num)
theorem B4141781 : Blo 1839621 4141781 := bbase (se 7 (by rfl) ⟨48536, by rfl⟩ : syracuseStep 4141781 = 97073) (by norm_num)
theorem B6214373 : Blo 1839621 6214373 := bbase (se 4 (by rfl) ⟨582597, by rfl⟩ : syracuseStep 6214373 = 1165195) (by norm_num)
theorem B4657925 : Blo 1839621 4657925 := bbase (se 4 (by rfl) ⟨436680, by rfl⟩ : syracuseStep 4657925 = 873361) (by norm_num)
theorem B4141853 : Blo 1839621 4141853 := bbase (se 3 (by rfl) ⟨776597, by rfl⟩ : syracuseStep 4141853 = 1553195) (by norm_num)
theorem B8622949 : Blo 1839621 8622949 := bbase (se 4 (by rfl) ⟨808401, by rfl⟩ : syracuseStep 8622949 = 1616803) (by norm_num)
theorem B4141925 : Blo 1839621 4141925 := bbase (se 4 (by rfl) ⟨388305, by rfl⟩ : syracuseStep 4141925 = 776611) (by norm_num)
theorem B3494765 : Blo 1839621 3494765 := bbase (se 3 (by rfl) ⟨655268, by rfl⟩ : syracuseStep 3494765 = 1310537) (by norm_num)
theorem B4420469 : Blo 1839621 4420469 := bbase (se 5 (by rfl) ⟨207209, by rfl⟩ : syracuseStep 4420469 = 414419) (by norm_num)
theorem B4789109 : Blo 1839621 4789109 := bbase (se 5 (by rfl) ⟨224489, by rfl⟩ : syracuseStep 4789109 = 448979) (by norm_num)
theorem B7861157 : Blo 1839621 7861157 := bbase (se 4 (by rfl) ⟨736983, by rfl⟩ : syracuseStep 7861157 = 1473967) (by norm_num)
theorem B4141997 : Blo 1839621 4141997 := bbase (se 3 (by rfl) ⟨776624, by rfl⟩ : syracuseStep 4141997 = 1553249) (by norm_num)
theorem B4420565 : Blo 1839621 4420565 := bbase (se 7 (by rfl) ⟨51803, by rfl⟩ : syracuseStep 4420565 = 103607) (by norm_num)
theorem B4142069 : Blo 1839621 4142069 := bbase (se 5 (by rfl) ⟨194159, by rfl⟩ : syracuseStep 4142069 = 388319) (by norm_num)
theorem B3494917 : Blo 1839621 3494917 := bbase (se 4 (by rfl) ⟨327648, by rfl⟩ : syracuseStep 3494917 = 655297) (by norm_num)
theorem B4142141 : Blo 1839621 4142141 := bbase (se 3 (by rfl) ⟨776651, by rfl⟩ : syracuseStep 4142141 = 1553303) (by norm_num)
theorem B2069581 : Blo 1839621 2069581 := bbase (se 3 (by rfl) ⟨388046, by rfl⟩ : syracuseStep 2069581 = 776093) (by norm_num)
theorem B4658269 : Blo 1839621 4658269 := bbase (se 3 (by rfl) ⟨873425, by rfl⟩ : syracuseStep 4658269 = 1746851) (by norm_num)
theorem B6632549 : Blo 1839621 6632549 := bbase (se 4 (by rfl) ⟨621801, by rfl⟩ : syracuseStep 6632549 = 1243603) (by norm_num)
theorem B2069617 : Blo 1839621 2069617 := bbase (se 2 (by rfl) ⟨776106, by rfl⟩ : syracuseStep 2069617 = 1552213) (by norm_num)
theorem B1864829 : Blo 1839621 1864829 := bbase (se 3 (by rfl) ⟨349655, by rfl⟩ : syracuseStep 1864829 = 699311) (by norm_num)
theorem B4142213 : Blo 1839621 4142213 := bbase (se 4 (by rfl) ⟨388332, by rfl⟩ : syracuseStep 4142213 = 776665) (by norm_num)
theorem B2069653 : Blo 1839621 2069653 := bbase (se 6 (by rfl) ⟨48507, by rfl⟩ : syracuseStep 2069653 = 97015) (by norm_num)
theorem B4420757 : Blo 1839621 4420757 := bbase (se 6 (by rfl) ⟨103611, by rfl⟩ : syracuseStep 4420757 = 207223) (by norm_num)
theorem B6214805 : Blo 1839621 6214805 := bbase (se 6 (by rfl) ⟨145659, by rfl⟩ : syracuseStep 6214805 = 291319) (by norm_num)
theorem B1864877 : Blo 1839621 1864877 := bbase (se 3 (by rfl) ⟨349664, by rfl⟩ : syracuseStep 1864877 = 699329) (by norm_num)
theorem B2069689 : Blo 1839621 2069689 := bbase (se 2 (by rfl) ⟨776133, by rfl⟩ : syracuseStep 2069689 = 1552267) (by norm_num)
theorem B7861445 : Blo 1839621 7861445 := bbase (se 4 (by rfl) ⟨737010, by rfl⟩ : syracuseStep 7861445 = 1474021) (by norm_num)
theorem B4658381 : Blo 1839621 4658381 := bbase (se 3 (by rfl) ⟨873446, by rfl⟩ : syracuseStep 4658381 = 1746893) (by norm_num)
theorem B4142285 : Blo 1839621 4142285 := bbase (se 3 (by rfl) ⟨776678, by rfl⟩ : syracuseStep 4142285 = 1553357) (by norm_num)
theorem B2069725 : Blo 1839621 2069725 := bbase (se 3 (by rfl) ⟨388073, by rfl⟩ : syracuseStep 2069725 = 776147) (by norm_num)
theorem B2069761 : Blo 1839621 2069761 := bbase (se 2 (by rfl) ⟨776160, by rfl⟩ : syracuseStep 2069761 = 1552321) (by norm_num)
theorem B4142357 : Blo 1839621 4142357 := bbase (se 6 (by rfl) ⟨97086, by rfl⟩ : syracuseStep 4142357 = 194173) (by norm_num)
theorem B2069797 : Blo 1839621 2069797 := bbase (se 4 (by rfl) ⟨194043, by rfl⟩ : syracuseStep 2069797 = 388087) (by norm_num)
theorem B3495221 : Blo 1839621 3495221 := bbase (se 5 (by rfl) ⟨163838, by rfl⟩ : syracuseStep 3495221 = 327677) (by norm_num)
theorem B2069833 : Blo 1839621 2069833 := bbase (se 2 (by rfl) ⟨776187, by rfl⟩ : syracuseStep 2069833 = 1552375) (by norm_num)
theorem B4142429 : Blo 1839621 4142429 := bbase (se 3 (by rfl) ⟨776705, by rfl⟩ : syracuseStep 4142429 = 1553411) (by norm_num)
theorem B2069869 : Blo 1839621 2069869 := bbase (se 3 (by rfl) ⟨388100, by rfl⟩ : syracuseStep 2069869 = 776201) (by norm_num)
theorem B3929485 : Blo 1839621 3929485 := bbase (se 3 (by rfl) ⟨736778, by rfl⟩ : syracuseStep 3929485 = 1473557) (by norm_num)
theorem B4658573 : Blo 1839621 4658573 := bbase (se 3 (by rfl) ⟨873482, by rfl⟩ : syracuseStep 4658573 = 1746965) (by norm_num)
theorem B2069905 : Blo 1839621 2069905 := bbase (se 2 (by rfl) ⟨776214, by rfl⟩ : syracuseStep 2069905 = 1552429) (by norm_num)
theorem B2487709 : Blo 1839621 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B4724125 : Blo 1839621 4724125 := bbase (se 3 (by rfl) ⟨885773, by rfl⟩ : syracuseStep 4724125 = 1771547) (by norm_num)
theorem B4142501 : Blo 1839621 4142501 := bbase (se 4 (by rfl) ⟨388359, by rfl⟩ : syracuseStep 4142501 = 776719) (by norm_num)
theorem B2069941 : Blo 1839621 2069941 := bbase (se 5 (by rfl) ⟨97028, by rfl⟩ : syracuseStep 2069941 = 194057) (by norm_num)
theorem B2799061 : Blo 1839621 2799061 := bbase (se 7 (by rfl) ⟨32801, by rfl⟩ : syracuseStep 2799061 = 65603) (by norm_num)
theorem B2069977 : Blo 1839621 2069977 := bbase (se 2 (by rfl) ⟨776241, by rfl⟩ : syracuseStep 2069977 = 1552483) (by norm_num)
theorem B4142573 : Blo 1839621 4142573 := bbase (se 3 (by rfl) ⟨776732, by rfl⟩ : syracuseStep 4142573 = 1553465) (by norm_num)
theorem B2070013 : Blo 1839621 2070013 := bbase (se 3 (by rfl) ⟨388127, by rfl⟩ : syracuseStep 2070013 = 776255) (by norm_num)
theorem B8844821 : Blo 1839621 8844821 := bbase (se 6 (by rfl) ⟨207300, by rfl⟩ : syracuseStep 8844821 = 414601) (by norm_num)
theorem B3929629 : Blo 1839621 3929629 := bbase (se 3 (by rfl) ⟨736805, by rfl⟩ : syracuseStep 3929629 = 1473611) (by norm_num)
theorem B2070049 : Blo 1839621 2070049 := bbase (se 2 (by rfl) ⟨776268, by rfl⟩ : syracuseStep 2070049 = 1552537) (by norm_num)
theorem B2692661 : Blo 1839621 2692661 := bbase (se 5 (by rfl) ⟨126218, by rfl⟩ : syracuseStep 2692661 = 252437) (by norm_num)
theorem B4142645 : Blo 1839621 4142645 := bbase (se 5 (by rfl) ⟨194186, by rfl⟩ : syracuseStep 4142645 = 388373) (by norm_num)
theorem B2070085 : Blo 1839621 2070085 := bbase (se 4 (by rfl) ⟨194070, by rfl⟩ : syracuseStep 2070085 = 388141) (by norm_num)
theorem B6215237 : Blo 1839621 6215237 := bbase (se 4 (by rfl) ⟨582678, by rfl⟩ : syracuseStep 6215237 = 1165357) (by norm_num)
theorem B9320021 : Blo 1839621 9320021 := bbase (se 8 (by rfl) ⟨54609, by rfl⟩ : syracuseStep 9320021 = 109219) (by norm_num)
theorem B2070121 : Blo 1839621 2070121 := bbase (se 2 (by rfl) ⟨776295, by rfl⟩ : syracuseStep 2070121 = 1552591) (by norm_num)
theorem B15947381 : Blo 1839621 15947381 := bbase (se 5 (by rfl) ⟨747533, by rfl⟩ : syracuseStep 15947381 = 1495067) (by norm_num)
theorem B4142717 : Blo 1839621 4142717 := bbase (se 3 (by rfl) ⟨776759, by rfl⟩ : syracuseStep 4142717 = 1553519) (by norm_num)
theorem B2070157 : Blo 1839621 2070157 := bbase (se 3 (by rfl) ⟨388154, by rfl⟩ : syracuseStep 2070157 = 776309) (by norm_num)
theorem B2070193 : Blo 1839621 2070193 := bbase (se 2 (by rfl) ⟨776322, by rfl⟩ : syracuseStep 2070193 = 1552645) (by norm_num)
theorem B4142789 : Blo 1839621 4142789 := bbase (se 4 (by rfl) ⟨388386, by rfl⟩ : syracuseStep 4142789 = 776773) (by norm_num)
theorem B2070229 : Blo 1839621 2070229 := bbase (se 7 (by rfl) ⟨24260, by rfl⟩ : syracuseStep 2070229 = 48521) (by norm_num)
theorem B4658917 : Blo 1839621 4658917 := bbase (se 4 (by rfl) ⟨436773, by rfl⟩ : syracuseStep 4658917 = 873547) (by norm_num)
theorem B2070265 : Blo 1839621 2070265 := bbase (se 2 (by rfl) ⟨776349, by rfl⟩ : syracuseStep 2070265 = 1552699) (by norm_num)
theorem B4142861 : Blo 1839621 4142861 := bbase (se 3 (by rfl) ⟨776786, by rfl⟩ : syracuseStep 4142861 = 1553573) (by norm_num)
theorem B2070301 : Blo 1839621 2070301 := bbase (se 3 (by rfl) ⟨388181, by rfl⟩ : syracuseStep 2070301 = 776363) (by norm_num)
theorem B2070337 : Blo 1839621 2070337 := bbase (se 2 (by rfl) ⟨776376, by rfl⟩ : syracuseStep 2070337 = 1552753) (by norm_num)
theorem B5240645 : Blo 1839621 5240645 := bbase (se 4 (by rfl) ⟨491310, by rfl⟩ : syracuseStep 5240645 = 982621) (by norm_num)
theorem B4659029 : Blo 1839621 4659029 := bbase (se 9 (by rfl) ⟨13649, by rfl⟩ : syracuseStep 4659029 = 27299) (by norm_num)
theorem B4142933 : Blo 1839621 4142933 := bbase (se 9 (by rfl) ⟨12137, by rfl⟩ : syracuseStep 4142933 = 24275) (by norm_num)
theorem B2070373 : Blo 1839621 2070373 := bbase (se 4 (by rfl) ⟨194097, by rfl⟩ : syracuseStep 2070373 = 388195) (by norm_num)
theorem B2070409 : Blo 1839621 2070409 := bbase (se 2 (by rfl) ⟨776403, by rfl⟩ : syracuseStep 2070409 = 1552807) (by norm_num)
theorem B3930005 : Blo 1839621 3930005 := bbase (se 6 (by rfl) ⟨92109, by rfl⟩ : syracuseStep 3930005 = 184219) (by norm_num)
theorem B4143005 : Blo 1839621 4143005 := bbase (se 3 (by rfl) ⟨776813, by rfl⟩ : syracuseStep 4143005 = 1553627) (by norm_num)
theorem B2070445 : Blo 1839621 2070445 := bbase (se 3 (by rfl) ⟨388208, by rfl⟩ : syracuseStep 2070445 = 776417) (by norm_num)
theorem B7862197 : Blo 1839621 7862197 := bbase (se 5 (by rfl) ⟨368540, by rfl⟩ : syracuseStep 7862197 = 737081) (by norm_num)
theorem B2070481 : Blo 1839621 2070481 := bbase (se 2 (by rfl) ⟨776430, by rfl⟩ : syracuseStep 2070481 = 1552861) (by norm_num)
theorem B4143077 : Blo 1839621 4143077 := bbase (se 4 (by rfl) ⟨388413, by rfl⟩ : syracuseStep 4143077 = 776827) (by norm_num)
theorem B2070517 : Blo 1839621 2070517 := bbase (se 5 (by rfl) ⟨97055, by rfl⟩ : syracuseStep 2070517 = 194111) (by norm_num)
theorem B15726581 : Blo 1839621 15726581 := bbase (se 5 (by rfl) ⟨737183, by rfl⟩ : syracuseStep 15726581 = 1474367) (by norm_num)
theorem B4659221 : Blo 1839621 4659221 := bbase (se 6 (by rfl) ⟨109200, by rfl⟩ : syracuseStep 4659221 = 218401) (by norm_num)
theorem B2070553 : Blo 1839621 2070553 := bbase (se 2 (by rfl) ⟨776457, by rfl⟩ : syracuseStep 2070553 = 1552915) (by norm_num)
theorem B3495973 : Blo 1839621 3495973 := bbase (se 4 (by rfl) ⟨327747, by rfl⟩ : syracuseStep 3495973 = 655495) (by norm_num)
theorem B4143149 : Blo 1839621 4143149 := bbase (se 3 (by rfl) ⟨776840, by rfl⟩ : syracuseStep 4143149 = 1553681) (by norm_num)
theorem B2070589 : Blo 1839621 2070589 := bbase (se 3 (by rfl) ⟨388235, by rfl⟩ : syracuseStep 2070589 = 776471) (by norm_num)
theorem B2070625 : Blo 1839621 2070625 := bbase (se 2 (by rfl) ⟨776484, by rfl⟩ : syracuseStep 2070625 = 1552969) (by norm_num)
theorem B4143221 : Blo 1839621 4143221 := bbase (se 5 (by rfl) ⟨194213, by rfl⟩ : syracuseStep 4143221 = 388427) (by norm_num)
theorem B2070661 : Blo 1839621 2070661 := bbase (se 4 (by rfl) ⟨194124, by rfl⟩ : syracuseStep 2070661 = 388249) (by norm_num)
theorem B25540757 : Blo 1839621 25540757 := bbase (se 6 (by rfl) ⟨598611, by rfl⟩ : syracuseStep 25540757 = 1197223) (by norm_num)
theorem B2799773 : Blo 1839621 2799773 := bbase (se 3 (by rfl) ⟨524957, by rfl⟩ : syracuseStep 2799773 = 1049915) (by norm_num)
theorem B2070697 : Blo 1839621 2070697 := bbase (se 2 (by rfl) ⟨776511, by rfl⟩ : syracuseStep 2070697 = 1553023) (by norm_num)
theorem B3496117 : Blo 1839621 3496117 := bbase (se 5 (by rfl) ⟨163880, by rfl⟩ : syracuseStep 3496117 = 327761) (by norm_num)
theorem B4143293 : Blo 1839621 4143293 := bbase (se 3 (by rfl) ⟨776867, by rfl⟩ : syracuseStep 4143293 = 1553735) (by norm_num)
theorem B2070733 : Blo 1839621 2070733 := bbase (se 3 (by rfl) ⟨388262, by rfl⟩ : syracuseStep 2070733 = 776525) (by norm_num)
theorem B2070769 : Blo 1839621 2070769 := bbase (se 2 (by rfl) ⟨776538, by rfl⟩ : syracuseStep 2070769 = 1553077) (by norm_num)
theorem B3930373 : Blo 1839621 3930373 := bbase (se 4 (by rfl) ⟨368472, by rfl⟩ : syracuseStep 3930373 = 736945) (by norm_num)
theorem B4143365 : Blo 1839621 4143365 := bbase (se 4 (by rfl) ⟨388440, by rfl⟩ : syracuseStep 4143365 = 776881) (by norm_num)
theorem B4421909 : Blo 1839621 4421909 := bbase (se 6 (by rfl) ⟨103638, by rfl⟩ : syracuseStep 4421909 = 207277) (by norm_num)
theorem B2070805 : Blo 1839621 2070805 := bbase (se 6 (by rfl) ⟨48534, by rfl⟩ : syracuseStep 2070805 = 97069) (by norm_num)
theorem B2070841 : Blo 1839621 2070841 := bbase (se 2 (by rfl) ⟨776565, by rfl⟩ : syracuseStep 2070841 = 1553131) (by norm_num)
theorem B4143437 : Blo 1839621 4143437 := bbase (se 3 (by rfl) ⟨776894, by rfl⟩ : syracuseStep 4143437 = 1553789) (by norm_num)
theorem B2070877 : Blo 1839621 2070877 := bbase (se 3 (by rfl) ⟨388289, by rfl⟩ : syracuseStep 2070877 = 776579) (by norm_num)
theorem B4659565 : Blo 1839621 4659565 := bbase (se 3 (by rfl) ⟨873668, by rfl⟩ : syracuseStep 4659565 = 1747337) (by norm_num)
theorem B2070913 : Blo 1839621 2070913 := bbase (se 2 (by rfl) ⟨776592, by rfl⟩ : syracuseStep 2070913 = 1553185) (by norm_num)
theorem B5896597 : Blo 1839621 5896597 := bbase (se 6 (by rfl) ⟨138201, by rfl⟩ : syracuseStep 5896597 = 276403) (by norm_num)
theorem B4143509 : Blo 1839621 4143509 := bbase (se 6 (by rfl) ⟨97113, by rfl⟩ : syracuseStep 4143509 = 194227) (by norm_num)
theorem B2070949 : Blo 1839621 2070949 := bbase (se 4 (by rfl) ⟨194151, by rfl⟩ : syracuseStep 2070949 = 388303) (by norm_num)
theorem B2619821 : Blo 1839621 2619821 := bbase (se 3 (by rfl) ⟨491216, by rfl⟩ : syracuseStep 2619821 = 982433) (by norm_num)
theorem B2070985 : Blo 1839621 2070985 := bbase (se 2 (by rfl) ⟨776619, by rfl⟩ : syracuseStep 2070985 = 1553239) (by norm_num)
theorem B4659677 : Blo 1839621 4659677 := bbase (se 3 (by rfl) ⟨873689, by rfl⟩ : syracuseStep 4659677 = 1747379) (by norm_num)
theorem B4143581 : Blo 1839621 4143581 := bbase (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) (by norm_num)
theorem B2071021 : Blo 1839621 2071021 := bbase (se 3 (by rfl) ⟨388316, by rfl⟩ : syracuseStep 2071021 = 776633) (by norm_num)
theorem B2619901 : Blo 1839621 2619901 := bbase (se 3 (by rfl) ⟨491231, by rfl⟩ : syracuseStep 2619901 = 982463) (by norm_num)
theorem B2071057 : Blo 1839621 2071057 := bbase (se 2 (by rfl) ⟨776646, by rfl⟩ : syracuseStep 2071057 = 1553293) (by norm_num)
theorem B2071093 : Blo 1839621 2071093 := bbase (se 5 (by rfl) ⟨97082, by rfl⟩ : syracuseStep 2071093 = 194165) (by norm_num)
theorem B2071129 : Blo 1839621 2071129 := bbase (se 2 (by rfl) ⟨776673, by rfl⟩ : syracuseStep 2071129 = 1553347) (by norm_num)
theorem B11188853 : Blo 1839621 11188853 := bbase (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) (by norm_num)
theorem B6986357 : Blo 1839621 6986357 := bbase (se 5 (by rfl) ⟨327485, by rfl⟩ : syracuseStep 6986357 = 654971) (by norm_num)
theorem B2620021 : Blo 1839621 2620021 := bbase (se 5 (by rfl) ⟨122813, by rfl⟩ : syracuseStep 2620021 = 245627) (by norm_num)
theorem B2947709 : Blo 1839621 2947709 := bbase (se 3 (by rfl) ⟨552695, by rfl⟩ : syracuseStep 2947709 = 1105391) (by norm_num)
theorem B2071165 : Blo 1839621 2071165 := bbase (se 3 (by rfl) ⟨388343, by rfl⟩ : syracuseStep 2071165 = 776687) (by norm_num)
theorem B7862933 : Blo 1839621 7862933 := bbase (se 6 (by rfl) ⟨184287, by rfl⟩ : syracuseStep 7862933 = 368575) (by norm_num)
theorem B4659869 : Blo 1839621 4659869 := bbase (se 3 (by rfl) ⟨873725, by rfl⟩ : syracuseStep 4659869 = 1747451) (by norm_num)
theorem B2071201 : Blo 1839621 2071201 := bbase (se 2 (by rfl) ⟨776700, by rfl⟩ : syracuseStep 2071201 = 1553401) (by norm_num)
theorem B2071237 : Blo 1839621 2071237 := bbase (se 4 (by rfl) ⟨194178, by rfl⟩ : syracuseStep 2071237 = 388357) (by norm_num)
theorem B2620117 : Blo 1839621 2620117 := bbase (se 7 (by rfl) ⟨30704, by rfl⟩ : syracuseStep 2620117 = 61409) (by norm_num)
theorem B2071273 : Blo 1839621 2071273 := bbase (se 2 (by rfl) ⟨776727, by rfl⟩ : syracuseStep 2071273 = 1553455) (by norm_num)
theorem B14924533 : Blo 1839621 14924533 := bbase (se 5 (by rfl) ⟨699587, by rfl⟩ : syracuseStep 14924533 = 1399175) (by norm_num)
theorem B2947837 : Blo 1839621 2947837 := bbase (se 3 (by rfl) ⟨552719, by rfl⟩ : syracuseStep 2947837 = 1105439) (by norm_num)
theorem B2071309 : Blo 1839621 2071309 := bbase (se 3 (by rfl) ⟨388370, by rfl⟩ : syracuseStep 2071309 = 776741) (by norm_num)
theorem B2759453 : Blo 1839621 2759453 := bbase (se 3 (by rfl) ⟨517397, by rfl⟩ : syracuseStep 2759453 = 1034795) (by norm_num)
theorem B1964845 : Blo 1839621 1964845 := bbase (se 3 (by rfl) ⟨368408, by rfl⟩ : syracuseStep 1964845 = 736817) (by norm_num)
theorem B2210609 : Blo 1839621 2210609 := bbase (se 2 (by rfl) ⟨828978, by rfl⟩ : syracuseStep 2210609 = 1657957) (by norm_num)
theorem B2071345 : Blo 1839621 2071345 := bbase (se 2 (by rfl) ⟨776754, by rfl⟩ : syracuseStep 2071345 = 1553509) (by norm_num)
theorem B2759477 : Blo 1839621 2759477 := bbase (se 5 (by rfl) ⟨129350, by rfl⟩ : syracuseStep 2759477 = 258701) (by norm_num)
theorem B2759501 : Blo 1839621 2759501 := bbase (se 3 (by rfl) ⟨517406, by rfl⟩ : syracuseStep 2759501 = 1034813) (by norm_num)
theorem B8846165 : Blo 1839621 8846165 := bbase (se 9 (by rfl) ⟨25916, by rfl⟩ : syracuseStep 8846165 = 51833) (by norm_num)
theorem B2071381 : Blo 1839621 2071381 := bbase (se 9 (by rfl) ⟨6068, by rfl⟩ : syracuseStep 2071381 = 12137) (by norm_num)
theorem B2759525 : Blo 1839621 2759525 := bbase (se 4 (by rfl) ⟨258705, by rfl⟩ : syracuseStep 2759525 = 517411) (by norm_num)
theorem B9321317 : Blo 1839621 9321317 := bbase (se 4 (by rfl) ⟨873873, by rfl⟩ : syracuseStep 9321317 = 1747747) (by norm_num)
theorem B1964917 : Blo 1839621 1964917 := bbase (se 5 (by rfl) ⟨92105, by rfl⟩ : syracuseStep 1964917 = 184211) (by norm_num)
theorem B2071417 : Blo 1839621 2071417 := bbase (se 2 (by rfl) ⟨776781, by rfl⟩ : syracuseStep 2071417 = 1553563) (by norm_num)
theorem B2759549 : Blo 1839621 2759549 := bbase (se 3 (by rfl) ⟨517415, by rfl⟩ : syracuseStep 2759549 = 1034831) (by norm_num)
theorem B2759573 : Blo 1839621 2759573 := bbase (se 6 (by rfl) ⟨64677, by rfl⟩ : syracuseStep 2759573 = 129355) (by norm_num)
theorem B6986645 : Blo 1839621 6986645 := bbase (se 6 (by rfl) ⟨163749, by rfl⟩ : syracuseStep 6986645 = 327499) (by norm_num)
theorem B2071453 : Blo 1839621 2071453 := bbase (se 3 (by rfl) ⟨388397, by rfl⟩ : syracuseStep 2071453 = 776795) (by norm_num)
theorem B2759597 : Blo 1839621 2759597 := bbase (se 3 (by rfl) ⟨517424, by rfl⟩ : syracuseStep 2759597 = 1034849) (by norm_num)
theorem B2071489 : Blo 1839621 2071489 := bbase (se 2 (by rfl) ⟨776808, by rfl⟩ : syracuseStep 2071489 = 1553617) (by norm_num)
theorem B2759621 : Blo 1839621 2759621 := bbase (se 4 (by rfl) ⟨258714, by rfl⟩ : syracuseStep 2759621 = 517429) (by norm_num)
theorem B2759645 : Blo 1839621 2759645 := bbase (se 3 (by rfl) ⟨517433, by rfl⟩ : syracuseStep 2759645 = 1034867) (by norm_num)
theorem B5241829 : Blo 1839621 5241829 := bbase (se 4 (by rfl) ⟨491421, by rfl⟩ : syracuseStep 5241829 = 982843) (by norm_num)
theorem B2071525 : Blo 1839621 2071525 := bbase (se 4 (by rfl) ⟨194205, by rfl⟩ : syracuseStep 2071525 = 388411) (by norm_num)
theorem B2759669 : Blo 1839621 2759669 := bbase (se 5 (by rfl) ⟨129359, by rfl⟩ : syracuseStep 2759669 = 258719) (by norm_num)
theorem B7461877 : Blo 1839621 7461877 := bbase (se 5 (by rfl) ⟨349775, by rfl⟩ : syracuseStep 7461877 = 699551) (by norm_num)
theorem B4660213 : Blo 1839621 4660213 := bbase (se 5 (by rfl) ⟨218447, by rfl⟩ : syracuseStep 4660213 = 436895) (by norm_num)
theorem B2071561 : Blo 1839621 2071561 := bbase (se 2 (by rfl) ⟨776835, by rfl⟩ : syracuseStep 2071561 = 1553671) (by norm_num)
theorem B2759693 : Blo 1839621 2759693 := bbase (se 3 (by rfl) ⟨517442, by rfl⟩ : syracuseStep 2759693 = 1034885) (by norm_num)
theorem B8969237 : Blo 1839621 8969237 := bbase (se 6 (by rfl) ⟨210216, by rfl⟩ : syracuseStep 8969237 = 420433) (by norm_num)
theorem B2759717 : Blo 1839621 2759717 := bbase (se 4 (by rfl) ⟨258723, by rfl⟩ : syracuseStep 2759717 = 517447) (by norm_num)
theorem B1965097 : Blo 1839621 1965097 := bbase (se 2 (by rfl) ⟨736911, by rfl⟩ : syracuseStep 1965097 = 1473823) (by norm_num)
theorem B2071597 : Blo 1839621 2071597 := bbase (se 3 (by rfl) ⟨388424, by rfl⟩ : syracuseStep 2071597 = 776849) (by norm_num)
theorem B2759741 : Blo 1839621 2759741 := bbase (se 3 (by rfl) ⟨517451, by rfl⟩ : syracuseStep 2759741 = 1034903) (by norm_num)
theorem B2071633 : Blo 1839621 2071633 := bbase (se 2 (by rfl) ⟨776862, by rfl⟩ : syracuseStep 2071633 = 1553725) (by norm_num)
theorem B2759765 : Blo 1839621 2759765 := bbase (se 8 (by rfl) ⟨16170, by rfl⟩ : syracuseStep 2759765 = 32341) (by norm_num)
theorem B2210917 : Blo 1839621 2210917 := bbase (se 4 (by rfl) ⟨207273, by rfl⟩ : syracuseStep 2210917 = 414547) (by norm_num)
theorem B4660325 : Blo 1839621 4660325 := bbase (se 4 (by rfl) ⟨436905, by rfl⟩ : syracuseStep 4660325 = 873811) (by norm_num)
theorem B2759789 : Blo 1839621 2759789 := bbase (se 3 (by rfl) ⟨517460, by rfl⟩ : syracuseStep 2759789 = 1034921) (by norm_num)
theorem B2071669 : Blo 1839621 2071669 := bbase (se 5 (by rfl) ⟨97109, by rfl⟩ : syracuseStep 2071669 = 194219) (by norm_num)
theorem B2759813 : Blo 1839621 2759813 := bbase (se 4 (by rfl) ⟨258732, by rfl⟩ : syracuseStep 2759813 = 517465) (by norm_num)
theorem B5241989 : Blo 1839621 5241989 := bbase (se 4 (by rfl) ⟨491436, by rfl⟩ : syracuseStep 5241989 = 982873) (by norm_num)
theorem B2071705 : Blo 1839621 2071705 := bbase (se 2 (by rfl) ⟨776889, by rfl⟩ : syracuseStep 2071705 = 1553779) (by norm_num)
theorem B2759837 : Blo 1839621 2759837 := bbase (se 3 (by rfl) ⟨517469, by rfl⟩ : syracuseStep 2759837 = 1034939) (by norm_num)
theorem B2759861 : Blo 1839621 2759861 := bbase (se 5 (by rfl) ⟨129368, by rfl⟩ : syracuseStep 2759861 = 258737) (by norm_num)
theorem B2071741 : Blo 1839621 2071741 := bbase (se 3 (by rfl) ⟨388451, by rfl⟩ : syracuseStep 2071741 = 776903) (by norm_num)
theorem B2211013 : Blo 1839621 2211013 := bbase (se 4 (by rfl) ⟨207282, by rfl⟩ : syracuseStep 2211013 = 414565) (by norm_num)
theorem B2620613 : Blo 1839621 2620613 := bbase (se 4 (by rfl) ⟨245682, by rfl⟩ : syracuseStep 2620613 = 491365) (by norm_num)
theorem B2759885 : Blo 1839621 2759885 := bbase (se 3 (by rfl) ⟨517478, by rfl⟩ : syracuseStep 2759885 = 1034957) (by norm_num)
theorem B13270229 : Blo 1839621 13270229 := bbase (se 7 (by rfl) ⟨155510, by rfl⟩ : syracuseStep 13270229 = 311021) (by norm_num)
theorem B2071777 : Blo 1839621 2071777 := bbase (se 2 (by rfl) ⟨776916, by rfl⟩ : syracuseStep 2071777 = 1553833) (by norm_num)
theorem B2759909 : Blo 1839621 2759909 := bbase (se 4 (by rfl) ⟨258741, by rfl⟩ : syracuseStep 2759909 = 517483) (by norm_num)
theorem B6208757 : Blo 1839621 6208757 := bbase (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) (by norm_num)
theorem B2759933 : Blo 1839621 2759933 := bbase (se 3 (by rfl) ⟨517487, by rfl⟩ : syracuseStep 2759933 = 1034975) (by norm_num)
theorem B9313541 : Blo 1839621 9313541 := bbase (se 4 (by rfl) ⟨873144, by rfl⟩ : syracuseStep 9313541 = 1746289) (by norm_num)
theorem B2071813 : Blo 1839621 2071813 := bbase (se 4 (by rfl) ⟨194232, by rfl⟩ : syracuseStep 2071813 = 388465) (by norm_num)
theorem B2759957 : Blo 1839621 2759957 := bbase (se 6 (by rfl) ⟨64686, by rfl⟩ : syracuseStep 2759957 = 129373) (by norm_num)
theorem B4660517 : Blo 1839621 4660517 := bbase (se 4 (by rfl) ⟨436923, by rfl⟩ : syracuseStep 4660517 = 873847) (by norm_num)
theorem B2759981 : Blo 1839621 2759981 := bbase (se 3 (by rfl) ⟨517496, by rfl⟩ : syracuseStep 2759981 = 1034993) (by norm_num)
theorem B2760005 : Blo 1839621 2760005 := bbase (se 4 (by rfl) ⟨258750, by rfl⟩ : syracuseStep 2760005 = 517501) (by norm_num)
theorem B2760029 : Blo 1839621 2760029 := bbase (se 3 (by rfl) ⟨517505, by rfl⟩ : syracuseStep 2760029 = 1035011) (by norm_num)
theorem B2760053 : Blo 1839621 2760053 := bbase (se 5 (by rfl) ⟨129377, by rfl⟩ : syracuseStep 2760053 = 258755) (by norm_num)
theorem B5242229 : Blo 1839621 5242229 := bbase (se 5 (by rfl) ⟨245729, by rfl⟩ : syracuseStep 5242229 = 491459) (by norm_num)
theorem B2760077 : Blo 1839621 2760077 := bbase (se 3 (by rfl) ⟨517514, by rfl⟩ : syracuseStep 2760077 = 1035029) (by norm_num)
theorem B2760101 : Blo 1839621 2760101 := bbase (se 4 (by rfl) ⟨258759, by rfl⟩ : syracuseStep 2760101 = 517519) (by norm_num)
theorem B1891765 : Blo 1839621 1891765 := bbase (se 5 (by rfl) ⟨88676, by rfl⟩ : syracuseStep 1891765 = 177353) (by norm_num)
theorem B2760125 : Blo 1839621 2760125 := bbase (se 3 (by rfl) ⟨517523, by rfl⟩ : syracuseStep 2760125 = 1035047) (by norm_num)
theorem B2760149 : Blo 1839621 2760149 := bbase (se 7 (by rfl) ⟨32345, by rfl⟩ : syracuseStep 2760149 = 64691) (by norm_num)
theorem B12590549 : Blo 1839621 12590549 := bbase (se 7 (by rfl) ⟨147545, by rfl⟩ : syracuseStep 12590549 = 295091) (by norm_num)
theorem B1965541 : Blo 1839621 1965541 := bbase (se 4 (by rfl) ⟨184269, by rfl⟩ : syracuseStep 1965541 = 368539) (by norm_num)
theorem B2211301 : Blo 1839621 2211301 := bbase (se 4 (by rfl) ⟨207309, by rfl⟩ : syracuseStep 2211301 = 414619) (by norm_num)
theorem B2760173 : Blo 1839621 2760173 := bbase (se 3 (by rfl) ⟨517532, by rfl⟩ : syracuseStep 2760173 = 1035065) (by norm_num)
theorem B9952757 : Blo 1839621 9952757 := bbase (se 5 (by rfl) ⟨466535, by rfl⟩ : syracuseStep 9952757 = 933071) (by norm_num)
theorem B2760197 : Blo 1839621 2760197 := bbase (se 4 (by rfl) ⟨258768, by rfl⟩ : syracuseStep 2760197 = 517537) (by norm_num)
theorem B3317269 : Blo 1839621 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B2760221 : Blo 1839621 2760221 := bbase (se 3 (by rfl) ⟨517541, by rfl⟩ : syracuseStep 2760221 = 1035083) (by norm_num)
theorem B2760245 : Blo 1839621 2760245 := bbase (se 5 (by rfl) ⟨129386, by rfl⟩ : syracuseStep 2760245 = 258773) (by norm_num)
theorem B5242421 : Blo 1839621 5242421 := bbase (se 5 (by rfl) ⟨245738, by rfl⟩ : syracuseStep 5242421 = 491477) (by norm_num)
theorem B2760269 : Blo 1839621 2760269 := bbase (se 3 (by rfl) ⟨517550, by rfl⟩ : syracuseStep 2760269 = 1035101) (by norm_num)
theorem B1965665 : Blo 1839621 1965665 := bbase (se 2 (by rfl) ⟨737124, by rfl⟩ : syracuseStep 1965665 = 1474249) (by norm_num)
theorem B2760293 : Blo 1839621 2760293 := bbase (se 4 (by rfl) ⟨258777, by rfl⟩ : syracuseStep 2760293 = 517555) (by norm_num)
theorem B3104365 : Blo 1839621 3104365 := bbase (se 3 (by rfl) ⟨582068, by rfl⟩ : syracuseStep 3104365 = 1164137) (by norm_num)
theorem B2760317 : Blo 1839621 2760317 := bbase (se 3 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 2760317 = 1035119) (by norm_num)
theorem B4660861 : Blo 1839621 4660861 := bbase (se 3 (by rfl) ⟨873911, by rfl⟩ : syracuseStep 4660861 = 1747823) (by norm_num)
theorem B2760341 : Blo 1839621 2760341 := bbase (se 6 (by rfl) ⟨64695, by rfl⟩ : syracuseStep 2760341 = 129391) (by norm_num)
theorem B6209189 : Blo 1839621 6209189 := bbase (se 4 (by rfl) ⟨582111, by rfl⟩ : syracuseStep 6209189 = 1164223) (by norm_num)
theorem B2211493 : Blo 1839621 2211493 := bbase (se 4 (by rfl) ⟨207327, by rfl⟩ : syracuseStep 2211493 = 414655) (by norm_num)
theorem B2760365 : Blo 1839621 2760365 := bbase (se 3 (by rfl) ⟨517568, by rfl⟩ : syracuseStep 2760365 = 1035137) (by norm_num)
theorem B3104453 : Blo 1839621 3104453 := bbase (se 4 (by rfl) ⟨291042, by rfl⟩ : syracuseStep 3104453 = 582085) (by norm_num)
theorem B2760389 : Blo 1839621 2760389 := bbase (se 4 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 2760389 = 517573) (by norm_num)
theorem B2760413 : Blo 1839621 2760413 := bbase (se 3 (by rfl) ⟨517577, by rfl⟩ : syracuseStep 2760413 = 1035155) (by norm_num)
theorem B3931877 : Blo 1839621 3931877 := bbase (se 4 (by rfl) ⟨368613, by rfl⟩ : syracuseStep 3931877 = 737227) (by norm_num)
theorem B2621165 : Blo 1839621 2621165 := bbase (se 3 (by rfl) ⟨491468, by rfl⟩ : syracuseStep 2621165 = 982937) (by norm_num)
theorem B4660973 : Blo 1839621 4660973 := bbase (se 3 (by rfl) ⟨873932, by rfl⟩ : syracuseStep 4660973 = 1747865) (by norm_num)
theorem B2760437 : Blo 1839621 2760437 := bbase (se 5 (by rfl) ⟨129395, by rfl⟩ : syracuseStep 2760437 = 258791) (by norm_num)
theorem B2760461 : Blo 1839621 2760461 := bbase (se 3 (by rfl) ⟨517586, by rfl⟩ : syracuseStep 2760461 = 1035173) (by norm_num)
theorem B2760485 : Blo 1839621 2760485 := bbase (se 4 (by rfl) ⟨258795, by rfl⟩ : syracuseStep 2760485 = 517591) (by norm_num)
theorem B6635317 : Blo 1839621 6635317 := bbase (se 5 (by rfl) ⟨311030, by rfl⟩ : syracuseStep 6635317 = 622061) (by norm_num)
theorem B2760509 : Blo 1839621 2760509 := bbase (se 3 (by rfl) ⟨517595, by rfl⟩ : syracuseStep 2760509 = 1035191) (by norm_num)
theorem B3104581 : Blo 1839621 3104581 := bbase (se 4 (by rfl) ⟨291054, by rfl⟩ : syracuseStep 3104581 = 582109) (by norm_num)
theorem B2760533 : Blo 1839621 2760533 := bbase (se 9 (by rfl) ⟨8087, by rfl⟩ : syracuseStep 2760533 = 16175) (by norm_num)
theorem B1965917 : Blo 1839621 1965917 := bbase (se 3 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 1965917 = 737219) (by norm_num)
theorem B2760557 : Blo 1839621 2760557 := bbase (se 3 (by rfl) ⟨517604, by rfl⟩ : syracuseStep 2760557 = 1035209) (by norm_num)
theorem B3932021 : Blo 1839621 3932021 := bbase (se 5 (by rfl) ⟨184313, by rfl⟩ : syracuseStep 3932021 = 368627) (by norm_num)
theorem B2760581 : Blo 1839621 2760581 := bbase (se 4 (by rfl) ⟨258804, by rfl⟩ : syracuseStep 2760581 = 517609) (by norm_num)
theorem B3104669 : Blo 1839621 3104669 := bbase (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) (by norm_num)
theorem B2760605 : Blo 1839621 2760605 := bbase (se 3 (by rfl) ⟨517613, by rfl⟩ : syracuseStep 2760605 = 1035227) (by norm_num)
theorem B4661165 : Blo 1839621 4661165 := bbase (se 3 (by rfl) ⟨873968, by rfl⟩ : syracuseStep 4661165 = 1747937) (by norm_num)
theorem B2760629 : Blo 1839621 2760629 := bbase (se 5 (by rfl) ⟨129404, by rfl⟩ : syracuseStep 2760629 = 258809) (by norm_num)
theorem B3317701 : Blo 1839621 3317701 := bbase (se 4 (by rfl) ⟨311034, by rfl⟩ : syracuseStep 3317701 = 622069) (by norm_num)
theorem B2760653 : Blo 1839621 2760653 := bbase (se 3 (by rfl) ⟨517622, by rfl⟩ : syracuseStep 2760653 = 1035245) (by norm_num)
theorem B2760677 : Blo 1839621 2760677 := bbase (se 4 (by rfl) ⟨258813, by rfl⟩ : syracuseStep 2760677 = 517627) (by norm_num)
theorem B2760701 : Blo 1839621 2760701 := bbase (se 3 (by rfl) ⟨517631, by rfl⟩ : syracuseStep 2760701 = 1035263) (by norm_num)
theorem B2760707 : Blo 1839621 2760707 := bstep (se 1 (by rfl) ⟨2070530, by rfl⟩ : syracuseStep 2760707 = 4141061) B4141061
theorem B2760737 : Blo 1839621 2760737 := bstep (se 2 (by rfl) ⟨1035276, by rfl⟩ : syracuseStep 2760737 = 2070553) B2070553
theorem B4661297 : Blo 1839621 4661297 := bstep (se 2 (by rfl) ⟨1747986, by rfl⟩ : syracuseStep 4661297 = 3495973) B3495973
theorem B2760755 : Blo 1839621 2760755 := bstep (se 1 (by rfl) ⟨2070566, by rfl⟩ : syracuseStep 2760755 = 4141133) B4141133
theorem B4423747 : Blo 1839621 4423747 := bstep (se 1 (by rfl) ⟨3317810, by rfl⟩ : syracuseStep 4423747 = 6635621) B6635621
theorem B2760785 : Blo 1839621 2760785 := bstep (se 2 (by rfl) ⟨1035294, by rfl⟩ : syracuseStep 2760785 = 2070589) B2070589
theorem B3104851 : Blo 1839621 3104851 := bstep (se 1 (by rfl) ⟨2328638, by rfl⟩ : syracuseStep 3104851 = 4657277) B4657277
theorem B2760803 : Blo 1839621 2760803 := bstep (se 1 (by rfl) ⟨2070602, by rfl⟩ : syracuseStep 2760803 = 4141205) B4141205
theorem B4661347 : Blo 1839621 4661347 := bstep (se 1 (by rfl) ⟨3496010, by rfl⟩ : syracuseStep 4661347 = 6992021) B6992021
theorem B2760833 : Blo 1839621 2760833 := bstep (se 2 (by rfl) ⟨1035312, by rfl⟩ : syracuseStep 2760833 = 2070625) B2070625
theorem B2760851 : Blo 1839621 2760851 := bstep (se 1 (by rfl) ⟨2070638, by rfl⟩ : syracuseStep 2760851 = 4141277) B4141277
theorem B2621587 : Blo 1839621 2621587 := bstep (se 1 (by rfl) ⟨1966190, by rfl⟩ : syracuseStep 2621587 = 3932381) B3932381
theorem B2760881 : Blo 1839621 2760881 := bstep (se 2 (by rfl) ⟨1035330, by rfl⟩ : syracuseStep 2760881 = 2070661) B2070661
theorem B2760899 : Blo 1839621 2760899 := bstep (se 1 (by rfl) ⟨2070674, by rfl⟩ : syracuseStep 2760899 = 4141349) B4141349
theorem B3104993 : Blo 1839621 3104993 := bstep (se 2 (by rfl) ⟨1164372, by rfl⟩ : syracuseStep 3104993 = 2328745) B2328745
theorem B2760929 : Blo 1839621 2760929 := bstep (se 2 (by rfl) ⟨1035348, by rfl⟩ : syracuseStep 2760929 = 2070697) B2070697
theorem B4661489 : Blo 1839621 4661489 := bstep (se 2 (by rfl) ⟨1748058, by rfl⟩ : syracuseStep 4661489 = 3496117) B3496117
theorem B2760947 : Blo 1839621 2760947 := bstep (se 1 (by rfl) ⟨2070710, by rfl⟩ : syracuseStep 2760947 = 4141421) B4141421
theorem B7864589 : Blo 1839621 7864589 := bstep (se 3 (by rfl) ⟨1474610, by rfl⟩ : syracuseStep 7864589 = 2949221) B2949221
theorem B2760977 : Blo 1839621 2760977 := bstep (se 2 (by rfl) ⟨1035366, by rfl⟩ : syracuseStep 2760977 = 2070733) B2070733
theorem B2760995 : Blo 1839621 2760995 := bstep (se 1 (by rfl) ⟨2070746, by rfl⟩ : syracuseStep 2760995 = 4141493) B4141493
theorem B6209837 : Blo 1839621 6209837 := bstep (se 3 (by rfl) ⟨1164344, by rfl⟩ : syracuseStep 6209837 = 2328689) B2328689
theorem B5898545 : Blo 1839621 5898545 := bstep (se 2 (by rfl) ⟨2211954, by rfl⟩ : syracuseStep 5898545 = 4423909) B4423909
theorem B2212147 : Blo 1839621 2212147 := bstep (se 1 (by rfl) ⟨1659110, by rfl⟩ : syracuseStep 2212147 = 3318221) B3318221
theorem B2761025 : Blo 1839621 2761025 := bstep (se 2 (by rfl) ⟨1035384, by rfl⟩ : syracuseStep 2761025 = 2070769) B2070769
theorem B4972877 : Blo 1839621 4972877 := bstep (se 3 (by rfl) ⟨932414, by rfl⟩ : syracuseStep 4972877 = 1864829) B1864829
theorem B2761043 : Blo 1839621 2761043 := bstep (se 1 (by rfl) ⟨2070782, by rfl⟩ : syracuseStep 2761043 = 4141565) B4141565
theorem B3105121 : Blo 1839621 3105121 := bstep (se 2 (by rfl) ⟨1164420, by rfl⟩ : syracuseStep 3105121 = 2328841) B2328841
theorem B6209891 : Blo 1839621 6209891 := bstep (se 1 (by rfl) ⟨4657418, by rfl⟩ : syracuseStep 6209891 = 9314837) B9314837
theorem B2761073 : Blo 1839621 2761073 := bstep (se 2 (by rfl) ⟨1035402, by rfl⟩ : syracuseStep 2761073 = 2070805) B2070805
theorem B3105155 : Blo 1839621 3105155 := bstep (se 1 (by rfl) ⟨2328866, by rfl⟩ : syracuseStep 3105155 = 4657733) B4657733
theorem B2761091 : Blo 1839621 2761091 := bstep (se 1 (by rfl) ⟨2070818, by rfl⟩ : syracuseStep 2761091 = 4141637) B4141637
theorem B2761121 : Blo 1839621 2761121 := bstep (se 2 (by rfl) ⟨1035420, by rfl⟩ : syracuseStep 2761121 = 2070841) B2070841
theorem B5898673 : Blo 1839621 5898673 := bstep (se 2 (by rfl) ⟨2212002, by rfl⟩ : syracuseStep 5898673 = 4424005) B4424005
theorem B2761139 : Blo 1839621 2761139 := bstep (se 1 (by rfl) ⟨2070854, by rfl⟩ : syracuseStep 2761139 = 4141709) B4141709
theorem B4973005 : Blo 1839621 4973005 := bstep (se 3 (by rfl) ⟨932438, by rfl⟩ : syracuseStep 4973005 = 1864877) B1864877
theorem B2761169 : Blo 1839621 2761169 := bstep (se 2 (by rfl) ⟨1035438, by rfl⟩ : syracuseStep 2761169 = 2070877) B2070877
theorem B2761187 : Blo 1839621 2761187 := bstep (se 1 (by rfl) ⟨2070890, by rfl⟩ : syracuseStep 2761187 = 4141781) B4141781
theorem B2212339 : Blo 1839621 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B2761217 : Blo 1839621 2761217 := bstep (se 2 (by rfl) ⟨1035456, by rfl⟩ : syracuseStep 2761217 = 2070913) B2070913
theorem B3105283 : Blo 1839621 3105283 := bstep (se 1 (by rfl) ⟨2328962, by rfl⟩ : syracuseStep 3105283 = 4657925) B4657925
theorem B6988301 : Blo 1839621 6988301 := bstep (se 3 (by rfl) ⟨1310306, by rfl⟩ : syracuseStep 6988301 = 2620613) B2620613
theorem B2761235 : Blo 1839621 2761235 := bstep (se 1 (by rfl) ⟨2070926, by rfl⟩ : syracuseStep 2761235 = 4141853) B4141853
theorem B2761265 : Blo 1839621 2761265 := bstep (se 2 (by rfl) ⟨1035474, by rfl⟩ : syracuseStep 2761265 = 2070949) B2070949
theorem B28721717 : Blo 1839621 28721717 := bstep (se 5 (by rfl) ⟨1346330, by rfl⟩ : syracuseStep 28721717 = 2692661) B2692661
theorem B163627573 : Blo 1839621 163627573 := bstep (se 5 (by rfl) ⟨7670042, by rfl⟩ : syracuseStep 163627573 = 15340085) B15340085
theorem B2761283 : Blo 1839621 2761283 := bstep (se 1 (by rfl) ⟨2070962, by rfl⟩ : syracuseStep 2761283 = 4141925) B4141925
theorem B2761313 : Blo 1839621 2761313 := bstep (se 2 (by rfl) ⟨1035492, by rfl⟩ : syracuseStep 2761313 = 2070985) B2070985
theorem B7864931 : Blo 1839621 7864931 := bstep (se 1 (by rfl) ⟨5898698, by rfl⟩ : syracuseStep 7864931 = 11797397) B11797397
theorem B6210161 : Blo 1839621 6210161 := bstep (se 2 (by rfl) ⟨2328810, by rfl⟩ : syracuseStep 6210161 = 4657621) B4657621
theorem B2761331 : Blo 1839621 2761331 := bstep (se 1 (by rfl) ⟨2070998, by rfl⟩ : syracuseStep 2761331 = 4141997) B4141997
theorem B4973201 : Blo 1839621 4973201 := bstep (se 2 (by rfl) ⟨1864950, by rfl⟩ : syracuseStep 4973201 = 3729901) B3729901
theorem B3105425 : Blo 1839621 3105425 := bstep (se 2 (by rfl) ⟨1164534, by rfl⟩ : syracuseStep 3105425 = 2329069) B2329069
theorem B2761361 : Blo 1839621 2761361 := bstep (se 2 (by rfl) ⟨1035510, by rfl⟩ : syracuseStep 2761361 = 2071021) B2071021
theorem B2761379 : Blo 1839621 2761379 := bstep (se 1 (by rfl) ⟨2071034, by rfl⟩ : syracuseStep 2761379 = 4142069) B4142069
theorem B2761409 : Blo 1839621 2761409 := bstep (se 2 (by rfl) ⟨1035528, by rfl⟩ : syracuseStep 2761409 = 2071057) B2071057
theorem B2622145 : Blo 1839621 2622145 := bstep (se 2 (by rfl) ⟨983304, by rfl⟩ : syracuseStep 2622145 = 1966609) B1966609
theorem B2761427 : Blo 1839621 2761427 := bstep (se 1 (by rfl) ⟨2071070, by rfl⟩ : syracuseStep 2761427 = 4142141) B4142141
theorem B5243629 : Blo 1839621 5243629 := bstep (se 3 (by rfl) ⟨983180, by rfl⟩ : syracuseStep 5243629 = 1966361) B1966361
theorem B2761457 : Blo 1839621 2761457 := bstep (se 2 (by rfl) ⟨1035546, by rfl⟩ : syracuseStep 2761457 = 2071093) B2071093
theorem B2761475 : Blo 1839621 2761475 := bstep (se 1 (by rfl) ⟨2071106, by rfl⟩ : syracuseStep 2761475 = 4142213) B4142213
theorem B3105553 : Blo 1839621 3105553 := bstep (se 2 (by rfl) ⟨1164582, by rfl⟩ : syracuseStep 3105553 = 2329165) B2329165
theorem B2761505 : Blo 1839621 2761505 := bstep (se 2 (by rfl) ⟨1035564, by rfl⟩ : syracuseStep 2761505 = 2071129) B2071129
theorem B3105587 : Blo 1839621 3105587 := bstep (se 1 (by rfl) ⟨2329190, by rfl⟩ : syracuseStep 3105587 = 4658381) B4658381
theorem B2761523 : Blo 1839621 2761523 := bstep (se 1 (by rfl) ⟨2071142, by rfl⟩ : syracuseStep 2761523 = 4142285) B4142285
theorem B2761553 : Blo 1839621 2761553 := bstep (se 2 (by rfl) ⟨1035582, by rfl⟩ : syracuseStep 2761553 = 2071165) B2071165
theorem B2761571 : Blo 1839621 2761571 := bstep (se 1 (by rfl) ⟨2071178, by rfl⟩ : syracuseStep 2761571 = 4142357) B4142357
theorem B2761601 : Blo 1839621 2761601 := bstep (se 2 (by rfl) ⟨1035600, by rfl⟩ : syracuseStep 2761601 = 2071201) B2071201
theorem B2761619 : Blo 1839621 2761619 := bstep (se 1 (by rfl) ⟨2071214, by rfl⟩ : syracuseStep 2761619 = 4142429) B4142429
theorem B2761649 : Blo 1839621 2761649 := bstep (se 2 (by rfl) ⟨1035618, by rfl⟩ : syracuseStep 2761649 = 2071237) B2071237
theorem B3105715 : Blo 1839621 3105715 := bstep (se 1 (by rfl) ⟨2329286, by rfl⟩ : syracuseStep 3105715 = 4658573) B4658573
theorem B2761667 : Blo 1839621 2761667 := bstep (se 1 (by rfl) ⟨2071250, by rfl⟩ : syracuseStep 2761667 = 4142501) B4142501
theorem B2761697 : Blo 1839621 2761697 := bstep (se 2 (by rfl) ⟨1035636, by rfl⟩ : syracuseStep 2761697 = 2071273) B2071273
theorem B11789297 : Blo 1839621 11789297 := bstep (se 2 (by rfl) ⟨4420986, by rfl⟩ : syracuseStep 11789297 = 8841973) B8841973
theorem B19899377 : Blo 1839621 19899377 := bstep (se 2 (by rfl) ⟨7462266, by rfl⟩ : syracuseStep 19899377 = 14924533) B14924533
theorem B2761715 : Blo 1839621 2761715 := bstep (se 1 (by rfl) ⟨2071286, by rfl⟩ : syracuseStep 2761715 = 4142573) B4142573
theorem B2761745 : Blo 1839621 2761745 := bstep (se 2 (by rfl) ⟨1035654, by rfl⟩ : syracuseStep 2761745 = 2071309) B2071309
theorem B2761763 : Blo 1839621 2761763 := bstep (se 1 (by rfl) ⟨2071322, by rfl⟩ : syracuseStep 2761763 = 4142645) B4142645
theorem B3105857 : Blo 1839621 3105857 := bstep (se 2 (by rfl) ⟨1164696, by rfl⟩ : syracuseStep 3105857 = 2329393) B2329393
theorem B2761793 : Blo 1839621 2761793 := bstep (se 2 (by rfl) ⟨1035672, by rfl⟩ : syracuseStep 2761793 = 2071345) B2071345
theorem B2761811 : Blo 1839621 2761811 := bstep (se 1 (by rfl) ⟨2071358, by rfl⟩ : syracuseStep 2761811 = 4142717) B4142717
theorem B2761841 : Blo 1839621 2761841 := bstep (se 2 (by rfl) ⟨1035690, by rfl⟩ : syracuseStep 2761841 = 2071381) B2071381
theorem B2761859 : Blo 1839621 2761859 := bstep (se 1 (by rfl) ⟨2071394, by rfl⟩ : syracuseStep 2761859 = 4142789) B4142789
theorem B6210701 : Blo 1839621 6210701 := bstep (se 3 (by rfl) ⟨1164506, by rfl⟩ : syracuseStep 6210701 = 2329013) B2329013
theorem B2761889 : Blo 1839621 2761889 := bstep (se 2 (by rfl) ⟨1035708, by rfl⟩ : syracuseStep 2761889 = 2071417) B2071417
theorem B2761907 : Blo 1839621 2761907 := bstep (se 1 (by rfl) ⟨2071430, by rfl⟩ : syracuseStep 2761907 = 4142861) B4142861
theorem B3105985 : Blo 1839621 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B6210755 : Blo 1839621 6210755 := bstep (se 1 (by rfl) ⟨4658066, by rfl⟩ : syracuseStep 6210755 = 9316133) B9316133
theorem B2761937 : Blo 1839621 2761937 := bstep (se 2 (by rfl) ⟨1035726, by rfl⟩ : syracuseStep 2761937 = 2071453) B2071453
theorem B3106019 : Blo 1839621 3106019 := bstep (se 1 (by rfl) ⟨2329514, by rfl⟩ : syracuseStep 3106019 = 4659029) B4659029
theorem B2761955 : Blo 1839621 2761955 := bstep (se 1 (by rfl) ⟨2071466, by rfl⟩ : syracuseStep 2761955 = 4142933) B4142933
theorem B2761985 : Blo 1839621 2761985 := bstep (se 2 (by rfl) ⟨1035744, by rfl⟩ : syracuseStep 2761985 = 2071489) B2071489
theorem B2762003 : Blo 1839621 2762003 := bstep (se 1 (by rfl) ⟨2071502, by rfl⟩ : syracuseStep 2762003 = 4143005) B4143005
theorem B6989105 : Blo 1839621 6989105 := bstep (se 2 (by rfl) ⟨2620914, by rfl⟩ : syracuseStep 6989105 = 5241829) B5241829
theorem B2762033 : Blo 1839621 2762033 := bstep (se 2 (by rfl) ⟨1035762, by rfl⟩ : syracuseStep 2762033 = 2071525) B2071525
theorem B2762051 : Blo 1839621 2762051 := bstep (se 1 (by rfl) ⟨2071538, by rfl⟩ : syracuseStep 2762051 = 4143077) B4143077
theorem B2762081 : Blo 1839621 2762081 := bstep (se 2 (by rfl) ⟨1035780, by rfl⟩ : syracuseStep 2762081 = 2071561) B2071561
theorem B3106147 : Blo 1839621 3106147 := bstep (se 1 (by rfl) ⟨2329610, by rfl⟩ : syracuseStep 3106147 = 4659221) B4659221
theorem B8848739 : Blo 1839621 8848739 := bstep (se 1 (by rfl) ⟨6636554, by rfl⟩ : syracuseStep 8848739 = 13273109) B13273109
theorem B2762099 : Blo 1839621 2762099 := bstep (se 1 (by rfl) ⟨2071574, by rfl⟩ : syracuseStep 2762099 = 4143149) B4143149
theorem B5899661 : Blo 1839621 5899661 := bstep (se 3 (by rfl) ⟨1106186, by rfl⟩ : syracuseStep 5899661 = 2212373) B2212373
theorem B2762129 : Blo 1839621 2762129 := bstep (se 2 (by rfl) ⟨1035798, by rfl⟩ : syracuseStep 2762129 = 2071597) B2071597
theorem B2360723 : Blo 1839621 2360723 := bstep (se 1 (by rfl) ⟨1770542, by rfl⟩ : syracuseStep 2360723 = 3541085) B3541085
theorem B2762147 : Blo 1839621 2762147 := bstep (se 1 (by rfl) ⟨2071610, by rfl⟩ : syracuseStep 2762147 = 4143221) B4143221
theorem B2762177 : Blo 1839621 2762177 := bstep (se 2 (by rfl) ⟨1035816, by rfl⟩ : syracuseStep 2762177 = 2071633) B2071633
theorem B6211025 : Blo 1839621 6211025 := bstep (se 2 (by rfl) ⟨2329134, by rfl⟩ : syracuseStep 6211025 = 4658269) B4658269
theorem B2762195 : Blo 1839621 2762195 := bstep (se 1 (by rfl) ⟨2071646, by rfl⟩ : syracuseStep 2762195 = 4143293) B4143293
theorem B3106289 : Blo 1839621 3106289 := bstep (se 2 (by rfl) ⟨1164858, by rfl⟩ : syracuseStep 3106289 = 2329717) B2329717
theorem B2762225 : Blo 1839621 2762225 := bstep (se 2 (by rfl) ⟨1035834, by rfl⟩ : syracuseStep 2762225 = 2071669) B2071669
theorem B2762243 : Blo 1839621 2762243 := bstep (se 1 (by rfl) ⟨2071682, by rfl⟩ : syracuseStep 2762243 = 4143365) B4143365
theorem B2762273 : Blo 1839621 2762273 := bstep (se 2 (by rfl) ⟨1035852, by rfl⟩ : syracuseStep 2762273 = 2071705) B2071705
theorem B2762291 : Blo 1839621 2762291 := bstep (se 1 (by rfl) ⟨2071718, by rfl⟩ : syracuseStep 2762291 = 4143437) B4143437
theorem B2762321 : Blo 1839621 2762321 := bstep (se 2 (by rfl) ⟨1035870, by rfl⟩ : syracuseStep 2762321 = 2071741) B2071741
theorem B2762339 : Blo 1839621 2762339 := bstep (se 1 (by rfl) ⟨2071754, by rfl⟩ : syracuseStep 2762339 = 4143509) B4143509
theorem B3106417 : Blo 1839621 3106417 := bstep (se 2 (by rfl) ⟨1164906, by rfl⟩ : syracuseStep 3106417 = 2329813) B2329813
theorem B2762369 : Blo 1839621 2762369 := bstep (se 2 (by rfl) ⟨1035888, by rfl⟩ : syracuseStep 2762369 = 2071777) B2071777
theorem B3106451 : Blo 1839621 3106451 := bstep (se 1 (by rfl) ⟨2329838, by rfl⟩ : syracuseStep 3106451 = 4659677) B4659677
theorem B2762387 : Blo 1839621 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B2762417 : Blo 1839621 2762417 := bstep (se 2 (by rfl) ⟨1035906, by rfl⟩ : syracuseStep 2762417 = 2071813) B2071813
theorem B3147473 : Blo 1839621 3147473 := bstep (se 2 (by rfl) ⟨1180302, by rfl⟩ : syracuseStep 3147473 = 2360605) B2360605
theorem B3106579 : Blo 1839621 3106579 := bstep (se 1 (by rfl) ⟨2329934, by rfl⟩ : syracuseStep 3106579 = 4659869) B4659869
theorem B59713301 : Blo 1839621 59713301 := bstep (se 6 (by rfl) ⟨1399530, by rfl⟩ : syracuseStep 59713301 = 2799061) B2799061
theorem B2328355 : Blo 1839621 2328355 := bstep (se 1 (by rfl) ⟨1746266, by rfl⟩ : syracuseStep 2328355 = 3492533) B3492533
theorem B2099027 : Blo 1839621 2099027 := bstep (se 1 (by rfl) ⟨1574270, by rfl⟩ : syracuseStep 2099027 = 3148541) B3148541
theorem B3106721 : Blo 1839621 3106721 := bstep (se 2 (by rfl) ⟨1165020, by rfl⟩ : syracuseStep 3106721 = 2330041) B2330041
theorem B7858097 : Blo 1839621 7858097 := bstep (se 2 (by rfl) ⟨2946786, by rfl⟩ : syracuseStep 7858097 = 5893573) B5893573
theorem B10479557 : Blo 1839621 10479557 := bstep (se 4 (by rfl) ⟨982458, by rfl⟩ : syracuseStep 10479557 = 1964917) B1964917
theorem B6989773 : Blo 1839621 6989773 := bstep (se 3 (by rfl) ⟨1310582, by rfl⟩ : syracuseStep 6989773 = 2621165) B2621165
theorem B6211565 : Blo 1839621 6211565 := bstep (se 3 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 6211565 = 2329337) B2329337
theorem B3147761 : Blo 1839621 3147761 := bstep (se 2 (by rfl) ⟨1180410, by rfl⟩ : syracuseStep 3147761 = 2360821) B2360821
theorem B3106849 : Blo 1839621 3106849 := bstep (se 2 (by rfl) ⟨1165068, by rfl⟩ : syracuseStep 3106849 = 2330137) B2330137
theorem B6211619 : Blo 1839621 6211619 := bstep (se 1 (by rfl) ⟨4658714, by rfl⟩ : syracuseStep 6211619 = 9317429) B9317429
theorem B37767221 : Blo 1839621 37767221 := bstep (se 5 (by rfl) ⟨1770338, by rfl⟩ : syracuseStep 37767221 = 3540677) B3540677
theorem B3106883 : Blo 1839621 3106883 := bstep (se 1 (by rfl) ⟨2330162, by rfl⟩ : syracuseStep 3106883 = 4660325) B4660325
theorem B4139153 : Blo 1839621 4139153 := bstep (se 2 (by rfl) ⟨1552182, by rfl⟩ : syracuseStep 4139153 = 3104365) B3104365
theorem B4139171 : Blo 1839621 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B3107011 : Blo 1839621 3107011 := bstep (se 1 (by rfl) ⟨2330258, by rfl⟩ : syracuseStep 3107011 = 4660517) B4660517
theorem B2328851 : Blo 1839621 2328851 := bstep (se 1 (by rfl) ⟨1746638, by rfl⟩ : syracuseStep 2328851 = 3493277) B3493277
theorem B6211889 : Blo 1839621 6211889 := bstep (se 2 (by rfl) ⟨2329458, by rfl⟩ : syracuseStep 6211889 = 4658917) B4658917
theorem B3107153 : Blo 1839621 3107153 := bstep (se 2 (by rfl) ⟨1165182, by rfl⟩ : syracuseStep 3107153 = 2330365) B2330365
theorem B10480013 : Blo 1839621 10480013 := bstep (se 3 (by rfl) ⟨1965002, by rfl⟩ : syracuseStep 10480013 = 3930005) B3930005
theorem B4139441 : Blo 1839621 4139441 := bstep (se 2 (by rfl) ⟨1552290, by rfl⟩ : syracuseStep 4139441 = 3104581) B3104581
theorem B4139459 : Blo 1839621 4139459 := bstep (se 1 (by rfl) ⟨3104594, by rfl⟩ : syracuseStep 4139459 = 6209189) B6209189
theorem B3107281 : Blo 1839621 3107281 := bstep (se 2 (by rfl) ⟨1165230, by rfl⟩ : syracuseStep 3107281 = 2330461) B2330461
theorem B13273571 : Blo 1839621 13273571 := bstep (se 1 (by rfl) ⟨9955178, by rfl⟩ : syracuseStep 13273571 = 19910357) B19910357
theorem B10488305 : Blo 1839621 10488305 := bstep (se 2 (by rfl) ⟨3933114, by rfl⟩ : syracuseStep 10488305 = 7866229) B7866229
theorem B3107315 : Blo 1839621 3107315 := bstep (se 1 (by rfl) ⟨2330486, by rfl⟩ : syracuseStep 3107315 = 4660973) B4660973
theorem B3107443 : Blo 1839621 3107443 := bstep (se 1 (by rfl) ⟨2330582, by rfl⟩ : syracuseStep 3107443 = 4661165) B4661165
theorem B4139729 : Blo 1839621 4139729 := bstep (se 2 (by rfl) ⟨1552398, by rfl⟩ : syracuseStep 4139729 = 3104797) B3104797
theorem B4139747 : Blo 1839621 4139747 := bstep (se 1 (by rfl) ⟨3104810, by rfl⟩ : syracuseStep 4139747 = 6209621) B6209621
theorem B20728547 : Blo 1839621 20728547 := bstep (se 1 (by rfl) ⟨15546410, by rfl⟩ : syracuseStep 20728547 = 31092821) B31092821
theorem B6990563 : Blo 1839621 6990563 := bstep (se 1 (by rfl) ⟨5242922, by rfl⟩ : syracuseStep 6990563 = 10485845) B10485845
theorem B9317105 : Blo 1839621 9317105 := bstep (se 2 (by rfl) ⟨3493914, by rfl⟩ : syracuseStep 9317105 = 6987829) B6987829
theorem B3107585 : Blo 1839621 3107585 := bstep (se 2 (by rfl) ⟨1165344, by rfl⟩ : syracuseStep 3107585 = 2330689) B2330689
theorem B6212429 : Blo 1839621 6212429 := bstep (se 3 (by rfl) ⟨1164830, by rfl⟩ : syracuseStep 6212429 = 2329661) B2329661
theorem B3107713 : Blo 1839621 3107713 := bstep (se 2 (by rfl) ⟨1165392, by rfl⟩ : syracuseStep 3107713 = 2330785) B2330785
theorem B6212483 : Blo 1839621 6212483 := bstep (se 1 (by rfl) ⟨4659362, by rfl⟩ : syracuseStep 6212483 = 9318725) B9318725
theorem B2329555 : Blo 1839621 2329555 := bstep (se 1 (by rfl) ⟨1747166, by rfl⟩ : syracuseStep 2329555 = 3494333) B3494333
theorem B4140017 : Blo 1839621 4140017 := bstep (se 2 (by rfl) ⟨1552506, by rfl⟩ : syracuseStep 4140017 = 3105013) B3105013
theorem B4140035 : Blo 1839621 4140035 := bstep (se 1 (by rfl) ⟨3105026, by rfl⟩ : syracuseStep 4140035 = 6210053) B6210053
theorem B2329651 : Blo 1839621 2329651 := bstep (se 1 (by rfl) ⟨1747238, by rfl⟩ : syracuseStep 2329651 = 3494477) B3494477
theorem B6212753 : Blo 1839621 6212753 := bstep (se 2 (by rfl) ⟨2329782, by rfl⟩ : syracuseStep 6212753 = 4659565) B4659565
theorem B5598353 : Blo 1839621 5598353 := bstep (se 2 (by rfl) ⟨2099382, by rfl⟩ : syracuseStep 5598353 = 4198765) B4198765
theorem B15731981 : Blo 1839621 15731981 := bstep (se 3 (by rfl) ⟨2949746, by rfl⟩ : syracuseStep 15731981 = 5899493) B5899493
theorem B4140305 : Blo 1839621 4140305 := bstep (se 2 (by rfl) ⟨1552614, by rfl⟩ : syracuseStep 4140305 = 3105229) B3105229
theorem B4140323 : Blo 1839621 4140323 := bstep (se 1 (by rfl) ⟨3105242, by rfl⟩ : syracuseStep 4140323 = 6210485) B6210485
theorem B3493201 : Blo 1839621 3493201 := bstep (se 2 (by rfl) ⟨1309950, by rfl⟩ : syracuseStep 3493201 = 2619901) B2619901
theorem B17493347 : Blo 1839621 17493347 := bstep (se 1 (by rfl) ⟨13120010, by rfl⟩ : syracuseStep 17493347 = 26240021) B26240021
theorem B6991217 : Blo 1839621 6991217 := bstep (se 2 (by rfl) ⟨2621706, by rfl⟩ : syracuseStep 6991217 = 5243413) B5243413
theorem B11791757 : Blo 1839621 11791757 := bstep (se 3 (by rfl) ⟨2210954, by rfl⟩ : syracuseStep 11791757 = 4421909) B4421909
theorem B3493361 : Blo 1839621 3493361 := bstep (se 2 (by rfl) ⟨1310010, by rfl⟩ : syracuseStep 3493361 = 2620021) B2620021
theorem B2330147 : Blo 1839621 2330147 := bstep (se 1 (by rfl) ⟨1747610, by rfl⟩ : syracuseStep 2330147 = 3495221) B3495221
theorem B4140593 : Blo 1839621 4140593 := bstep (se 2 (by rfl) ⟨1552722, by rfl⟩ : syracuseStep 4140593 = 3105445) B3105445
theorem B4140611 : Blo 1839621 4140611 := bstep (se 1 (by rfl) ⟨3105458, by rfl⟩ : syracuseStep 4140611 = 6210917) B6210917
theorem B6213293 : Blo 1839621 6213293 := bstep (se 3 (by rfl) ⟨1164992, by rfl⟩ : syracuseStep 6213293 = 2329985) B2329985
theorem B2797267 : Blo 1839621 2797267 := bstep (se 1 (by rfl) ⟨2097950, by rfl⟩ : syracuseStep 2797267 = 4195901) B4195901
theorem B6213347 : Blo 1839621 6213347 := bstep (se 1 (by rfl) ⟨4660010, by rfl⟩ : syracuseStep 6213347 = 9320021) B9320021
theorem B11497265 : Blo 1839621 11497265 := bstep (se 2 (by rfl) ⟨4311474, by rfl⟩ : syracuseStep 11497265 = 8622949) B8622949
theorem B4140881 : Blo 1839621 4140881 := bstep (se 2 (by rfl) ⟨1552830, by rfl⟩ : syracuseStep 4140881 = 3105661) B3105661
theorem B4140899 : Blo 1839621 4140899 := bstep (se 1 (by rfl) ⟨3105674, by rfl⟩ : syracuseStep 4140899 = 6211349) B6211349
theorem B3493763 : Blo 1839621 3493763 := bstep (se 1 (by rfl) ⟨2620322, by rfl⟩ : syracuseStep 3493763 = 5240645) B5240645
theorem B2797505 : Blo 1839621 2797505 := bstep (se 2 (by rfl) ⟨1049064, by rfl⟩ : syracuseStep 2797505 = 2098129) B2098129
theorem B9949169 : Blo 1839621 9949169 := bstep (se 2 (by rfl) ⟨3730938, by rfl⟩ : syracuseStep 9949169 = 7461877) B7461877
theorem B6213617 : Blo 1839621 6213617 := bstep (se 2 (by rfl) ⟨2330106, by rfl⟩ : syracuseStep 6213617 = 4660213) B4660213
theorem B4255811 : Blo 1839621 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B17027171 : Blo 1839621 17027171 := bstep (se 1 (by rfl) ⟨12770378, by rfl⟩ : syracuseStep 17027171 = 25540757) B25540757
theorem B4141169 : Blo 1839621 4141169 := bstep (se 2 (by rfl) ⟨1552938, by rfl⟩ : syracuseStep 4141169 = 3105877) B3105877
theorem B4141187 : Blo 1839621 4141187 := bstep (se 1 (by rfl) ⟨3105890, by rfl⟩ : syracuseStep 4141187 = 6211781) B6211781
theorem B13979789 : Blo 1839621 13979789 := bstep (se 3 (by rfl) ⟨2621210, by rfl⟩ : syracuseStep 13979789 = 5242421) B5242421
theorem B4657297 : Blo 1839621 4657297 := bstep (se 2 (by rfl) ⟨1746486, by rfl⟩ : syracuseStep 4657297 = 3492973) B3492973
theorem B9318563 : Blo 1839621 9318563 := bstep (se 1 (by rfl) ⟨6988922, by rfl⟩ : syracuseStep 9318563 = 13977845) B13977845
theorem B7860557 : Blo 1839621 7860557 := bstep (se 3 (by rfl) ⟨1473854, by rfl⟩ : syracuseStep 7860557 = 2947709) B2947709
theorem B4141457 : Blo 1839621 4141457 := bstep (se 2 (by rfl) ⟨1553046, by rfl⟩ : syracuseStep 4141457 = 3106093) B3106093
theorem B7459235 : Blo 1839621 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B4657571 : Blo 1839621 4657571 := bstep (se 1 (by rfl) ⟨3493178, by rfl⟩ : syracuseStep 4657571 = 6986357) B6986357
theorem B4141475 : Blo 1839621 4141475 := bstep (se 1 (by rfl) ⟨3106106, by rfl⟩ : syracuseStep 4141475 = 6212213) B6212213
theorem B10629539 : Blo 1839621 10629539 := bstep (se 1 (by rfl) ⟨7972154, by rfl⟩ : syracuseStep 10629539 = 15944309) B15944309
theorem B7082417 : Blo 1839621 7082417 := bstep (se 2 (by rfl) ⟨2655906, by rfl⟩ : syracuseStep 7082417 = 5311813) B5311813
theorem B6295985 : Blo 1839621 6295985 := bstep (se 2 (by rfl) ⟨2360994, by rfl⟩ : syracuseStep 6295985 = 4721989) B4721989
theorem B201593285 : Blo 1839621 201593285 := bstep (se 4 (by rfl) ⟨18899370, by rfl⟩ : syracuseStep 201593285 = 37798741) B37798741
theorem B6214157 : Blo 1839621 6214157 := bstep (se 3 (by rfl) ⟨1165154, by rfl⟩ : syracuseStep 6214157 = 2330309) B2330309
theorem B5239313 : Blo 1839621 5239313 := bstep (se 2 (by rfl) ⟨1964742, by rfl⟩ : syracuseStep 5239313 = 3929485) B3929485
theorem B1839635 : Blo 1839621 1839635 := bstep (se 1 (by rfl) ⟨1379726, by rfl⟩ : syracuseStep 1839635 = 2759453) B2759453
theorem B1839651 : Blo 1839621 1839651 := bstep (se 1 (by rfl) ⟨1379738, by rfl⟩ : syracuseStep 1839651 = 2759477) B2759477
theorem B1839667 : Blo 1839621 1839667 := bstep (se 1 (by rfl) ⟨1379750, by rfl⟩ : syracuseStep 1839667 = 2759501) B2759501
theorem B1839683 : Blo 1839621 1839683 := bstep (se 1 (by rfl) ⟨1379762, by rfl⟩ : syracuseStep 1839683 = 2759525) B2759525
theorem B6214211 : Blo 1839621 6214211 := bstep (se 1 (by rfl) ⟨4660658, by rfl⟩ : syracuseStep 6214211 = 9321317) B9321317
theorem B1839699 : Blo 1839621 1839699 := bstep (se 1 (by rfl) ⟨1379774, by rfl⟩ : syracuseStep 1839699 = 2759549) B2759549
theorem B1839715 : Blo 1839621 1839715 := bstep (se 1 (by rfl) ⟨1379786, by rfl⟩ : syracuseStep 1839715 = 2759573) B2759573
theorem B4657763 : Blo 1839621 4657763 := bstep (se 1 (by rfl) ⟨3493322, by rfl⟩ : syracuseStep 4657763 = 6986645) B6986645
theorem B1839731 : Blo 1839621 1839731 := bstep (se 1 (by rfl) ⟨1379798, by rfl⟩ : syracuseStep 1839731 = 2759597) B2759597
theorem B1839747 : Blo 1839621 1839747 := bstep (se 1 (by rfl) ⟨1379810, by rfl⟩ : syracuseStep 1839747 = 2759621) B2759621
theorem B1839763 : Blo 1839621 1839763 := bstep (se 1 (by rfl) ⟨1379822, by rfl⟩ : syracuseStep 1839763 = 2759645) B2759645
theorem B1839779 : Blo 1839621 1839779 := bstep (se 1 (by rfl) ⟨1379834, by rfl⟩ : syracuseStep 1839779 = 2759669) B2759669
theorem B4141745 : Blo 1839621 4141745 := bstep (se 2 (by rfl) ⟨1553154, by rfl⟩ : syracuseStep 4141745 = 3106309) B3106309
theorem B1839795 : Blo 1839621 1839795 := bstep (se 1 (by rfl) ⟨1379846, by rfl⟩ : syracuseStep 1839795 = 2759693) B2759693
theorem B1839811 : Blo 1839621 1839811 := bstep (se 1 (by rfl) ⟨1379858, by rfl⟩ : syracuseStep 1839811 = 2759717) B2759717
theorem B4141763 : Blo 1839621 4141763 := bstep (se 1 (by rfl) ⟨3106322, by rfl⟩ : syracuseStep 4141763 = 6212645) B6212645
theorem B5239505 : Blo 1839621 5239505 := bstep (se 2 (by rfl) ⟨1964814, by rfl⟩ : syracuseStep 5239505 = 3929629) B3929629
theorem B1839827 : Blo 1839621 1839827 := bstep (se 1 (by rfl) ⟨1379870, by rfl⟩ : syracuseStep 1839827 = 2759741) B2759741
theorem B1839843 : Blo 1839621 1839843 := bstep (se 1 (by rfl) ⟨1379882, by rfl⟩ : syracuseStep 1839843 = 2759765) B2759765
theorem B1839859 : Blo 1839621 1839859 := bstep (se 1 (by rfl) ⟨1379894, by rfl⟩ : syracuseStep 1839859 = 2759789) B2759789
theorem B1839875 : Blo 1839621 1839875 := bstep (se 1 (by rfl) ⟨1379906, by rfl⟩ : syracuseStep 1839875 = 2759813) B2759813
theorem B3494659 : Blo 1839621 3494659 := bstep (se 1 (by rfl) ⟨2620994, by rfl⟩ : syracuseStep 3494659 = 5241989) B5241989
theorem B1839891 : Blo 1839621 1839891 := bstep (se 1 (by rfl) ⟨1379918, by rfl⟩ : syracuseStep 1839891 = 2759837) B2759837
theorem B1839907 : Blo 1839621 1839907 := bstep (se 1 (by rfl) ⟨1379930, by rfl⟩ : syracuseStep 1839907 = 2759861) B2759861
theorem B5894957 : Blo 1839621 5894957 := bstep (se 3 (by rfl) ⟨1105304, by rfl⟩ : syracuseStep 5894957 = 2210609) B2210609
theorem B1839923 : Blo 1839621 1839923 := bstep (se 1 (by rfl) ⟨1379942, by rfl⟩ : syracuseStep 1839923 = 2759885) B2759885
theorem B1839939 : Blo 1839621 1839939 := bstep (se 1 (by rfl) ⟨1379954, by rfl⟩ : syracuseStep 1839939 = 2759909) B2759909
theorem B25195333 : Blo 1839621 25195333 := bstep (se 4 (by rfl) ⟨2362062, by rfl⟩ : syracuseStep 25195333 = 4724125) B4724125
theorem B6214481 : Blo 1839621 6214481 := bstep (se 2 (by rfl) ⟨2330430, by rfl⟩ : syracuseStep 6214481 = 4660861) B4660861
theorem B1839955 : Blo 1839621 1839955 := bstep (se 1 (by rfl) ⟨1379966, by rfl⟩ : syracuseStep 1839955 = 2759933) B2759933
theorem B1839971 : Blo 1839621 1839971 := bstep (se 1 (by rfl) ⟨1379978, by rfl⟩ : syracuseStep 1839971 = 2759957) B2759957
theorem B2798435 : Blo 1839621 2798435 := bstep (se 1 (by rfl) ⟨2098826, by rfl⟩ : syracuseStep 2798435 = 4197653) B4197653
theorem B1839987 : Blo 1839621 1839987 := bstep (se 1 (by rfl) ⟨1379990, by rfl⟩ : syracuseStep 1839987 = 2759981) B2759981
theorem B1840003 : Blo 1839621 1840003 := bstep (se 1 (by rfl) ⟨1380002, by rfl⟩ : syracuseStep 1840003 = 2760005) B2760005
theorem B1840019 : Blo 1839621 1840019 := bstep (se 1 (by rfl) ⟨1380014, by rfl⟩ : syracuseStep 1840019 = 2760029) B2760029
theorem B2798483 : Blo 1839621 2798483 := bstep (se 1 (by rfl) ⟨2098862, by rfl⟩ : syracuseStep 2798483 = 4197725) B4197725
theorem B1840035 : Blo 1839621 1840035 := bstep (se 1 (by rfl) ⟨1380026, by rfl⟩ : syracuseStep 1840035 = 2760053) B2760053
theorem B3494819 : Blo 1839621 3494819 := bstep (se 1 (by rfl) ⟨2621114, by rfl⟩ : syracuseStep 3494819 = 5242229) B5242229
theorem B1840051 : Blo 1839621 1840051 := bstep (se 1 (by rfl) ⟨1380038, by rfl⟩ : syracuseStep 1840051 = 2760077) B2760077
theorem B1840067 : Blo 1839621 1840067 := bstep (se 1 (by rfl) ⟨1380050, by rfl⟩ : syracuseStep 1840067 = 2760101) B2760101
theorem B5313485 : Blo 1839621 5313485 := bstep (se 3 (by rfl) ⟨996278, by rfl⟩ : syracuseStep 5313485 = 1992557) B1992557
theorem B9319373 : Blo 1839621 9319373 := bstep (se 3 (by rfl) ⟨1747382, by rfl⟩ : syracuseStep 9319373 = 3494765) B3494765
theorem B1840083 : Blo 1839621 1840083 := bstep (se 1 (by rfl) ⟨1380062, by rfl⟩ : syracuseStep 1840083 = 2760125) B2760125
theorem B4142033 : Blo 1839621 4142033 := bstep (se 2 (by rfl) ⟨1553262, by rfl⟩ : syracuseStep 4142033 = 3106525) B3106525
theorem B1840099 : Blo 1839621 1840099 := bstep (se 1 (by rfl) ⟨1380074, by rfl⟩ : syracuseStep 1840099 = 2760149) B2760149
theorem B8393699 : Blo 1839621 8393699 := bstep (se 1 (by rfl) ⟨6295274, by rfl⟩ : syracuseStep 8393699 = 12590549) B12590549
theorem B4142051 : Blo 1839621 4142051 := bstep (se 1 (by rfl) ⟨3106538, by rfl⟩ : syracuseStep 4142051 = 6213077) B6213077
theorem B1840115 : Blo 1839621 1840115 := bstep (se 1 (by rfl) ⟨1380086, by rfl⟩ : syracuseStep 1840115 = 2760173) B2760173
theorem B1840131 : Blo 1839621 1840131 := bstep (se 1 (by rfl) ⟨1380098, by rfl⟩ : syracuseStep 1840131 = 2760197) B2760197
theorem B1840147 : Blo 1839621 1840147 := bstep (se 1 (by rfl) ⟨1380110, by rfl⟩ : syracuseStep 1840147 = 2760221) B2760221
theorem B1840163 : Blo 1839621 1840163 := bstep (se 1 (by rfl) ⟨1380122, by rfl⟩ : syracuseStep 1840163 = 2760245) B2760245
theorem B1840179 : Blo 1839621 1840179 := bstep (se 1 (by rfl) ⟨1380134, by rfl⟩ : syracuseStep 1840179 = 2760269) B2760269
theorem B1840195 : Blo 1839621 1840195 := bstep (se 1 (by rfl) ⟨1380146, by rfl⟩ : syracuseStep 1840195 = 2760293) B2760293
theorem B1840211 : Blo 1839621 1840211 := bstep (se 1 (by rfl) ⟨1380158, by rfl⟩ : syracuseStep 1840211 = 2760317) B2760317
theorem B1840227 : Blo 1839621 1840227 := bstep (se 1 (by rfl) ⟨1380170, by rfl⟩ : syracuseStep 1840227 = 2760341) B2760341
theorem B1840243 : Blo 1839621 1840243 := bstep (se 1 (by rfl) ⟨1380182, by rfl⟩ : syracuseStep 1840243 = 2760365) B2760365
theorem B2069635 : Blo 1839621 2069635 := bstep (se 1 (by rfl) ⟨1552226, by rfl⟩ : syracuseStep 2069635 = 3104453) B3104453
theorem B1840259 : Blo 1839621 1840259 := bstep (se 1 (by rfl) ⟨1380194, by rfl⟩ : syracuseStep 1840259 = 2760389) B2760389
theorem B1840275 : Blo 1839621 1840275 := bstep (se 1 (by rfl) ⟨1380206, by rfl⟩ : syracuseStep 1840275 = 2760413) B2760413
theorem B1840291 : Blo 1839621 1840291 := bstep (se 1 (by rfl) ⟨1380218, by rfl⟩ : syracuseStep 1840291 = 2760437) B2760437
theorem B1840307 : Blo 1839621 1840307 := bstep (se 1 (by rfl) ⟨1380230, by rfl⟩ : syracuseStep 1840307 = 2760461) B2760461
theorem B1840323 : Blo 1839621 1840323 := bstep (se 1 (by rfl) ⟨1380242, by rfl⟩ : syracuseStep 1840323 = 2760485) B2760485
theorem B1840339 : Blo 1839621 1840339 := bstep (se 1 (by rfl) ⟨1380254, by rfl⟩ : syracuseStep 1840339 = 2760509) B2760509
theorem B1840355 : Blo 1839621 1840355 := bstep (se 1 (by rfl) ⟨1380266, by rfl⟩ : syracuseStep 1840355 = 2760533) B2760533
theorem B10482929 : Blo 1839621 10482929 := bstep (se 2 (by rfl) ⟨3931098, by rfl⟩ : syracuseStep 10482929 = 7862197) B7862197
theorem B4142321 : Blo 1839621 4142321 := bstep (se 2 (by rfl) ⟨1553370, by rfl⟩ : syracuseStep 4142321 = 3106741) B3106741
theorem B1840371 : Blo 1839621 1840371 := bstep (se 1 (by rfl) ⟨1380278, by rfl⟩ : syracuseStep 1840371 = 2760557) B2760557
theorem B1840387 : Blo 1839621 1840387 := bstep (se 1 (by rfl) ⟨1380290, by rfl⟩ : syracuseStep 1840387 = 2760581) B2760581
theorem B4142339 : Blo 1839621 4142339 := bstep (se 1 (by rfl) ⟨3106754, by rfl⟩ : syracuseStep 4142339 = 6213509) B6213509
theorem B2069779 : Blo 1839621 2069779 := bstep (se 1 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 2069779 = 3104669) B3104669
theorem B1840403 : Blo 1839621 1840403 := bstep (se 1 (by rfl) ⟨1380302, by rfl⟩ : syracuseStep 1840403 = 2760605) B2760605
theorem B1840419 : Blo 1839621 1840419 := bstep (se 1 (by rfl) ⟨1380314, by rfl⟩ : syracuseStep 1840419 = 2760629) B2760629
theorem B1840435 : Blo 1839621 1840435 := bstep (se 1 (by rfl) ⟨1380326, by rfl⟩ : syracuseStep 1840435 = 2760653) B2760653
theorem B1840451 : Blo 1839621 1840451 := bstep (se 1 (by rfl) ⟨1380338, by rfl⟩ : syracuseStep 1840451 = 2760677) B2760677
theorem B1840467 : Blo 1839621 1840467 := bstep (se 1 (by rfl) ⟨1380350, by rfl⟩ : syracuseStep 1840467 = 2760701) B2760701
theorem B1840483 : Blo 1839621 1840483 := bstep (se 1 (by rfl) ⟨1380362, by rfl⟩ : syracuseStep 1840483 = 2760725) B2760725
theorem B6215021 : Blo 1839621 6215021 := bstep (se 3 (by rfl) ⟨1165316, by rfl⟩ : syracuseStep 6215021 = 2330633) B2330633
theorem B1840499 : Blo 1839621 1840499 := bstep (se 1 (by rfl) ⟨1380374, by rfl⟩ : syracuseStep 1840499 = 2760749) B2760749
theorem B1840515 : Blo 1839621 1840515 := bstep (se 1 (by rfl) ⟨1380386, by rfl⟩ : syracuseStep 1840515 = 2760773) B2760773
theorem B1840531 : Blo 1839621 1840531 := bstep (se 1 (by rfl) ⟨1380398, by rfl⟩ : syracuseStep 1840531 = 2760797) B2760797
theorem B3315107 : Blo 1839621 3315107 := bstep (se 1 (by rfl) ⟨2486330, by rfl⟩ : syracuseStep 3315107 = 4972661) B4972661
theorem B2069923 : Blo 1839621 2069923 := bstep (se 1 (by rfl) ⟨1552442, by rfl⟩ : syracuseStep 2069923 = 3104885) B3104885
theorem B1840547 : Blo 1839621 1840547 := bstep (se 1 (by rfl) ⟨1380410, by rfl⟩ : syracuseStep 1840547 = 2760821) B2760821
theorem B6215075 : Blo 1839621 6215075 := bstep (se 1 (by rfl) ⟨4661306, by rfl⟩ : syracuseStep 6215075 = 9322613) B9322613
theorem B1840563 : Blo 1839621 1840563 := bstep (se 1 (by rfl) ⟨1380422, by rfl⟩ : syracuseStep 1840563 = 2760845) B2760845
theorem B1840579 : Blo 1839621 1840579 := bstep (se 1 (by rfl) ⟨1380434, by rfl⟩ : syracuseStep 1840579 = 2760869) B2760869
theorem B1840595 : Blo 1839621 1840595 := bstep (se 1 (by rfl) ⟨1380446, by rfl⟩ : syracuseStep 1840595 = 2760893) B2760893
theorem B6985187 : Blo 1839621 6985187 := bstep (se 1 (by rfl) ⟨5238890, by rfl⟩ : syracuseStep 6985187 = 10477781) B10477781
theorem B1840611 : Blo 1839621 1840611 := bstep (se 1 (by rfl) ⟨1380458, by rfl⟩ : syracuseStep 1840611 = 2760917) B2760917
theorem B1840627 : Blo 1839621 1840627 := bstep (se 1 (by rfl) ⟨1380470, by rfl⟩ : syracuseStep 1840627 = 2760941) B2760941
theorem B1840643 : Blo 1839621 1840643 := bstep (se 1 (by rfl) ⟨1380482, by rfl⟩ : syracuseStep 1840643 = 2760965) B2760965
theorem B14931469 : Blo 1839621 14931469 := bstep (se 3 (by rfl) ⟨2799650, by rfl⟩ : syracuseStep 14931469 = 5599301) B5599301
theorem B4658705 : Blo 1839621 4658705 := bstep (se 2 (by rfl) ⟨1747014, by rfl⟩ : syracuseStep 4658705 = 3494029) B3494029
theorem B1840659 : Blo 1839621 1840659 := bstep (se 1 (by rfl) ⟨1380494, by rfl⟩ : syracuseStep 1840659 = 2760989) B2760989
theorem B4142609 : Blo 1839621 4142609 := bstep (se 2 (by rfl) ⟨1553478, by rfl⟩ : syracuseStep 4142609 = 3106957) B3106957
theorem B1840675 : Blo 1839621 1840675 := bstep (se 1 (by rfl) ⟨1380506, by rfl⟩ : syracuseStep 1840675 = 2761013) B2761013
theorem B4142627 : Blo 1839621 4142627 := bstep (se 1 (by rfl) ⟨3106970, by rfl⟩ : syracuseStep 4142627 = 6213941) B6213941
theorem B2070067 : Blo 1839621 2070067 := bstep (se 1 (by rfl) ⟨1552550, by rfl⟩ : syracuseStep 2070067 = 3105101) B3105101
theorem B1840691 : Blo 1839621 1840691 := bstep (se 1 (by rfl) ⟨1380518, by rfl⟩ : syracuseStep 1840691 = 2761037) B2761037
theorem B4658755 : Blo 1839621 4658755 := bstep (se 1 (by rfl) ⟨3494066, by rfl⟩ : syracuseStep 4658755 = 6988133) B6988133
theorem B1840707 : Blo 1839621 1840707 := bstep (se 1 (by rfl) ⟨1380530, by rfl⟩ : syracuseStep 1840707 = 2761061) B2761061
theorem B1840723 : Blo 1839621 1840723 := bstep (se 1 (by rfl) ⟨1380542, by rfl⟩ : syracuseStep 1840723 = 2761085) B2761085
theorem B1840739 : Blo 1839621 1840739 := bstep (se 1 (by rfl) ⟨1380554, by rfl⟩ : syracuseStep 1840739 = 2761109) B2761109
theorem B1840755 : Blo 1839621 1840755 := bstep (se 1 (by rfl) ⟨1380566, by rfl⟩ : syracuseStep 1840755 = 2761133) B2761133
theorem B1840771 : Blo 1839621 1840771 := bstep (se 1 (by rfl) ⟨1380578, by rfl⟩ : syracuseStep 1840771 = 2761157) B2761157
theorem B1840787 : Blo 1839621 1840787 := bstep (se 1 (by rfl) ⟨1380590, by rfl⟩ : syracuseStep 1840787 = 2761181) B2761181
theorem B1840803 : Blo 1839621 1840803 := bstep (se 1 (by rfl) ⟨1380602, by rfl⟩ : syracuseStep 1840803 = 2761205) B2761205
theorem B5240497 : Blo 1839621 5240497 := bstep (se 2 (by rfl) ⟨1965186, by rfl⟩ : syracuseStep 5240497 = 3930373) B3930373
theorem B1840819 : Blo 1839621 1840819 := bstep (se 1 (by rfl) ⟨1380614, by rfl⟩ : syracuseStep 1840819 = 2761229) B2761229
theorem B6215345 : Blo 1839621 6215345 := bstep (se 2 (by rfl) ⟨2330754, by rfl⟩ : syracuseStep 6215345 = 4661509) B4661509
theorem B2946755 : Blo 1839621 2946755 := bstep (se 1 (by rfl) ⟨2210066, by rfl⟩ : syracuseStep 2946755 = 4420133) B4420133
theorem B2070211 : Blo 1839621 2070211 := bstep (se 1 (by rfl) ⟨1552658, by rfl⟩ : syracuseStep 2070211 = 3105317) B3105317
theorem B1840835 : Blo 1839621 1840835 := bstep (se 1 (by rfl) ⟨1380626, by rfl⟩ : syracuseStep 1840835 = 2761253) B2761253
theorem B4658897 : Blo 1839621 4658897 := bstep (se 2 (by rfl) ⟨1747086, by rfl⟩ : syracuseStep 4658897 = 3494173) B3494173
theorem B1840851 : Blo 1839621 1840851 := bstep (se 1 (by rfl) ⟨1380638, by rfl⟩ : syracuseStep 1840851 = 2761277) B2761277
theorem B1840867 : Blo 1839621 1840867 := bstep (se 1 (by rfl) ⟨1380650, by rfl⟩ : syracuseStep 1840867 = 2761301) B2761301
theorem B1840883 : Blo 1839621 1840883 := bstep (se 1 (by rfl) ⟨1380662, by rfl⟩ : syracuseStep 1840883 = 2761325) B2761325
theorem B6469379 : Blo 1839621 6469379 := bstep (se 1 (by rfl) ⟨4852034, by rfl⟩ : syracuseStep 6469379 = 9704069) B9704069
theorem B1840899 : Blo 1839621 1840899 := bstep (se 1 (by rfl) ⟨1380674, by rfl⟩ : syracuseStep 1840899 = 2761349) B2761349
theorem B1840915 : Blo 1839621 1840915 := bstep (se 1 (by rfl) ⟨1380686, by rfl⟩ : syracuseStep 1840915 = 2761373) B2761373
theorem B4421411 : Blo 1839621 4421411 := bstep (se 1 (by rfl) ⟨3316058, by rfl⟩ : syracuseStep 4421411 = 6632117) B6632117
theorem B1840931 : Blo 1839621 1840931 := bstep (se 1 (by rfl) ⟨1380698, by rfl⟩ : syracuseStep 1840931 = 2761397) B2761397
theorem B4142897 : Blo 1839621 4142897 := bstep (se 2 (by rfl) ⟨1553586, by rfl⟩ : syracuseStep 4142897 = 3107173) B3107173
theorem B1840947 : Blo 1839621 1840947 := bstep (se 1 (by rfl) ⟨1380710, by rfl⟩ : syracuseStep 1840947 = 2761421) B2761421
theorem B1840963 : Blo 1839621 1840963 := bstep (se 1 (by rfl) ⟨1380722, by rfl⟩ : syracuseStep 1840963 = 2761445) B2761445
theorem B4142915 : Blo 1839621 4142915 := bstep (se 1 (by rfl) ⟨3107186, by rfl⟩ : syracuseStep 4142915 = 6214373) B6214373
theorem B2070355 : Blo 1839621 2070355 := bstep (se 1 (by rfl) ⟨1552766, by rfl⟩ : syracuseStep 2070355 = 3105533) B3105533
theorem B1840979 : Blo 1839621 1840979 := bstep (se 1 (by rfl) ⟨1380734, by rfl⟩ : syracuseStep 1840979 = 2761469) B2761469
theorem B1840995 : Blo 1839621 1840995 := bstep (se 1 (by rfl) ⟨1380746, by rfl⟩ : syracuseStep 1840995 = 2761493) B2761493
theorem B7862129 : Blo 1839621 7862129 := bstep (se 2 (by rfl) ⟨2948298, by rfl⟩ : syracuseStep 7862129 = 5896597) B5896597
theorem B1841011 : Blo 1839621 1841011 := bstep (se 1 (by rfl) ⟨1380758, by rfl⟩ : syracuseStep 1841011 = 2761517) B2761517
theorem B1841027 : Blo 1839621 1841027 := bstep (se 1 (by rfl) ⟨1380770, by rfl⟩ : syracuseStep 1841027 = 2761541) B2761541
theorem B1841043 : Blo 1839621 1841043 := bstep (se 1 (by rfl) ⟨1380782, by rfl⟩ : syracuseStep 1841043 = 2761565) B2761565
theorem B2946979 : Blo 1839621 2946979 := bstep (se 1 (by rfl) ⟨2210234, by rfl⟩ : syracuseStep 2946979 = 4420469) B4420469
theorem B1841059 : Blo 1839621 1841059 := bstep (se 1 (by rfl) ⟨1380794, by rfl⟩ : syracuseStep 1841059 = 2761589) B2761589
theorem B1841075 : Blo 1839621 1841075 := bstep (se 1 (by rfl) ⟨1380806, by rfl⟩ : syracuseStep 1841075 = 2761613) B2761613
theorem B5240771 : Blo 1839621 5240771 := bstep (se 1 (by rfl) ⟨3930578, by rfl⟩ : syracuseStep 5240771 = 7861157) B7861157
theorem B1841091 : Blo 1839621 1841091 := bstep (se 1 (by rfl) ⟨1380818, by rfl⟩ : syracuseStep 1841091 = 2761637) B2761637
theorem B3495889 : Blo 1839621 3495889 := bstep (se 2 (by rfl) ⟨1310958, by rfl⟩ : syracuseStep 3495889 = 2621917) B2621917
theorem B1841107 : Blo 1839621 1841107 := bstep (se 1 (by rfl) ⟨1380830, by rfl⟩ : syracuseStep 1841107 = 2761661) B2761661
theorem B2947043 : Blo 1839621 2947043 := bstep (se 1 (by rfl) ⟨2210282, by rfl⟩ : syracuseStep 2947043 = 4420565) B4420565
theorem B2070499 : Blo 1839621 2070499 := bstep (se 1 (by rfl) ⟨1552874, by rfl⟩ : syracuseStep 2070499 = 3105749) B3105749
theorem B1841123 : Blo 1839621 1841123 := bstep (se 1 (by rfl) ⟨1380842, by rfl⟩ : syracuseStep 1841123 = 2761685) B2761685
theorem B3315697 : Blo 1839621 3315697 := bstep (se 2 (by rfl) ⟨1243386, by rfl⟩ : syracuseStep 3315697 = 2486773) B2486773
theorem B1841139 : Blo 1839621 1841139 := bstep (se 1 (by rfl) ⟨1380854, by rfl⟩ : syracuseStep 1841139 = 2761709) B2761709
theorem B1841155 : Blo 1839621 1841155 := bstep (se 1 (by rfl) ⟨1380866, by rfl⟩ : syracuseStep 1841155 = 2761733) B2761733
theorem B9951245 : Blo 1839621 9951245 := bstep (se 3 (by rfl) ⟨1865858, by rfl⟩ : syracuseStep 9951245 = 3731717) B3731717
theorem B1841171 : Blo 1839621 1841171 := bstep (se 1 (by rfl) ⟨1380878, by rfl⟩ : syracuseStep 1841171 = 2761757) B2761757
theorem B1841187 : Blo 1839621 1841187 := bstep (se 1 (by rfl) ⟨1380890, by rfl⟩ : syracuseStep 1841187 = 2761781) B2761781
theorem B1841203 : Blo 1839621 1841203 := bstep (se 1 (by rfl) ⟨1380902, by rfl⟩ : syracuseStep 1841203 = 2761805) B2761805
theorem B4421699 : Blo 1839621 4421699 := bstep (se 1 (by rfl) ⟨3316274, by rfl⟩ : syracuseStep 4421699 = 6632549) B6632549
theorem B1841219 : Blo 1839621 1841219 := bstep (se 1 (by rfl) ⟨1380914, by rfl⟩ : syracuseStep 1841219 = 2761829) B2761829
theorem B9443405 : Blo 1839621 9443405 := bstep (se 3 (by rfl) ⟨1770638, by rfl⟩ : syracuseStep 9443405 = 3541277) B3541277
theorem B4143185 : Blo 1839621 4143185 := bstep (se 2 (by rfl) ⟨1553694, by rfl⟩ : syracuseStep 4143185 = 3107389) B3107389
theorem B1841235 : Blo 1839621 1841235 := bstep (se 1 (by rfl) ⟨1380926, by rfl⟩ : syracuseStep 1841235 = 2761853) B2761853
theorem B2947171 : Blo 1839621 2947171 := bstep (se 1 (by rfl) ⟨2210378, by rfl⟩ : syracuseStep 2947171 = 4420757) B4420757
theorem B1841251 : Blo 1839621 1841251 := bstep (se 1 (by rfl) ⟨1380938, by rfl⟩ : syracuseStep 1841251 = 2761877) B2761877
theorem B4143203 : Blo 1839621 4143203 := bstep (se 1 (by rfl) ⟨3107402, by rfl⟩ : syracuseStep 4143203 = 6214805) B6214805
theorem B10623089 : Blo 1839621 10623089 := bstep (se 2 (by rfl) ⟨3983658, by rfl⟩ : syracuseStep 10623089 = 7967317) B7967317
theorem B2070643 : Blo 1839621 2070643 := bstep (se 1 (by rfl) ⟨1552982, by rfl⟩ : syracuseStep 2070643 = 3105965) B3105965
theorem B1841267 : Blo 1839621 1841267 := bstep (se 1 (by rfl) ⟨1380950, by rfl⟩ : syracuseStep 1841267 = 2761901) B2761901
theorem B5240963 : Blo 1839621 5240963 := bstep (se 1 (by rfl) ⟨3930722, by rfl⟩ : syracuseStep 5240963 = 7861445) B7861445
theorem B1841283 : Blo 1839621 1841283 := bstep (se 1 (by rfl) ⟨1380962, by rfl⟩ : syracuseStep 1841283 = 2761925) B2761925
theorem B1841299 : Blo 1839621 1841299 := bstep (se 1 (by rfl) ⟨1380974, by rfl⟩ : syracuseStep 1841299 = 2761949) B2761949
theorem B1841315 : Blo 1839621 1841315 := bstep (se 1 (by rfl) ⟨1380986, by rfl⟩ : syracuseStep 1841315 = 2761973) B2761973
theorem B1841331 : Blo 1839621 1841331 := bstep (se 1 (by rfl) ⟨1380998, by rfl⟩ : syracuseStep 1841331 = 2761997) B2761997
theorem B1841347 : Blo 1839621 1841347 := bstep (se 1 (by rfl) ⟨1381010, by rfl⟩ : syracuseStep 1841347 = 2762021) B2762021
theorem B26523845 : Blo 1839621 26523845 := bstep (se 4 (by rfl) ⟨2486610, by rfl⟩ : syracuseStep 26523845 = 4973221) B4973221
theorem B1841363 : Blo 1839621 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B2799841 : Blo 1839621 2799841 := bstep (se 2 (by rfl) ⟨1049940, by rfl⟩ : syracuseStep 2799841 = 2099881) B2099881
theorem B1841379 : Blo 1839621 1841379 := bstep (se 1 (by rfl) ⟨1381034, by rfl⟩ : syracuseStep 1841379 = 2762069) B2762069
theorem B1841395 : Blo 1839621 1841395 := bstep (se 1 (by rfl) ⟨1381046, by rfl⟩ : syracuseStep 1841395 = 2762093) B2762093
theorem B2070787 : Blo 1839621 2070787 := bstep (se 1 (by rfl) ⟨1553090, by rfl⟩ : syracuseStep 2070787 = 3106181) B3106181
theorem B1841411 : Blo 1839621 1841411 := bstep (se 1 (by rfl) ⟨1381058, by rfl⟩ : syracuseStep 1841411 = 2762117) B2762117
theorem B1841427 : Blo 1839621 1841427 := bstep (se 1 (by rfl) ⟨1381070, by rfl⟩ : syracuseStep 1841427 = 2762141) B2762141
theorem B1841443 : Blo 1839621 1841443 := bstep (se 1 (by rfl) ⟨1381082, by rfl⟩ : syracuseStep 1841443 = 2762165) B2762165
theorem B1841459 : Blo 1839621 1841459 := bstep (se 1 (by rfl) ⟨1381094, by rfl⟩ : syracuseStep 1841459 = 2762189) B2762189
theorem B1841475 : Blo 1839621 1841475 := bstep (se 1 (by rfl) ⟨1381106, by rfl⟩ : syracuseStep 1841475 = 2762213) B2762213
theorem B3930449 : Blo 1839621 3930449 := bstep (se 2 (by rfl) ⟨1473918, by rfl⟩ : syracuseStep 3930449 = 2947837) B2947837
theorem B1841491 : Blo 1839621 1841491 := bstep (se 1 (by rfl) ⟨1381118, by rfl⟩ : syracuseStep 1841491 = 2762237) B2762237
theorem B5896547 : Blo 1839621 5896547 := bstep (se 1 (by rfl) ⟨4422410, by rfl⟩ : syracuseStep 5896547 = 8844821) B8844821
theorem B1841507 : Blo 1839621 1841507 := bstep (se 1 (by rfl) ⟨1381130, by rfl⟩ : syracuseStep 1841507 = 2762261) B2762261
theorem B4143473 : Blo 1839621 4143473 := bstep (se 2 (by rfl) ⟨1553802, by rfl⟩ : syracuseStep 4143473 = 3107605) B3107605
theorem B1841523 : Blo 1839621 1841523 := bstep (se 1 (by rfl) ⟨1381142, by rfl⟩ : syracuseStep 1841523 = 2762285) B2762285
theorem B1841539 : Blo 1839621 1841539 := bstep (se 1 (by rfl) ⟨1381154, by rfl⟩ : syracuseStep 1841539 = 2762309) B2762309
theorem B4143491 : Blo 1839621 4143491 := bstep (se 1 (by rfl) ⟨3107618, by rfl⟩ : syracuseStep 4143491 = 6215237) B6215237
theorem B2619793 : Blo 1839621 2619793 := bstep (se 2 (by rfl) ⟨982422, by rfl⟩ : syracuseStep 2619793 = 1964845) B1964845
theorem B2070931 : Blo 1839621 2070931 := bstep (se 1 (by rfl) ⟨1553198, by rfl⟩ : syracuseStep 2070931 = 3106397) B3106397
theorem B1841555 : Blo 1839621 1841555 := bstep (se 1 (by rfl) ⟨1381166, by rfl⟩ : syracuseStep 1841555 = 2762333) B2762333
theorem B1841571 : Blo 1839621 1841571 := bstep (se 1 (by rfl) ⟨1381178, by rfl⟩ : syracuseStep 1841571 = 2762357) B2762357
theorem B10631587 : Blo 1839621 10631587 := bstep (se 1 (by rfl) ⟨7973690, by rfl⟩ : syracuseStep 10631587 = 15947381) B15947381
theorem B1841587 : Blo 1839621 1841587 := bstep (se 1 (by rfl) ⟨1381190, by rfl⟩ : syracuseStep 1841587 = 2762381) B2762381
theorem B1841603 : Blo 1839621 1841603 := bstep (se 1 (by rfl) ⟨1381202, by rfl⟩ : syracuseStep 1841603 = 2762405) B2762405
theorem B13973957 : Blo 1839621 13973957 := bstep (se 4 (by rfl) ⟨1310058, by rfl⟩ : syracuseStep 13973957 = 2620117) B2620117
theorem B6986189 : Blo 1839621 6986189 := bstep (se 3 (by rfl) ⟨1309910, by rfl⟩ : syracuseStep 6986189 = 2619821) B2619821
theorem B1841619 : Blo 1839621 1841619 := bstep (se 1 (by rfl) ⟨1381214, by rfl⟩ : syracuseStep 1841619 = 2762429) B2762429
theorem B3316259 : Blo 1839621 3316259 := bstep (se 1 (by rfl) ⟨2487194, by rfl⟩ : syracuseStep 3316259 = 4974389) B4974389
theorem B2071075 : Blo 1839621 2071075 := bstep (se 1 (by rfl) ⟨1553306, by rfl⟩ : syracuseStep 2071075 = 3106613) B3106613
theorem B12933731 : Blo 1839621 12933731 := bstep (se 1 (by rfl) ⟨9700298, by rfl⟩ : syracuseStep 12933731 = 19400597) B19400597
theorem B10484387 : Blo 1839621 10484387 := bstep (se 1 (by rfl) ⟨7863290, by rfl⟩ : syracuseStep 10484387 = 15726581) B15726581
theorem B4659889 : Blo 1839621 4659889 := bstep (se 2 (by rfl) ⟨1747458, by rfl⟩ : syracuseStep 4659889 = 3494917) B3494917
theorem B2071219 : Blo 1839621 2071219 := bstep (se 1 (by rfl) ⟨1553414, by rfl⟩ : syracuseStep 2071219 = 3106829) B3106829
theorem B2620129 : Blo 1839621 2620129 := bstep (se 2 (by rfl) ⟨982548, by rfl⟩ : syracuseStep 2620129 = 1965097) B1965097
theorem B3316483 : Blo 1839621 3316483 := bstep (se 1 (by rfl) ⟨2487362, by rfl⟩ : syracuseStep 3316483 = 4974725) B4974725
theorem B2759441 : Blo 1839621 2759441 := bstep (se 2 (by rfl) ⟨1034790, by rfl⟩ : syracuseStep 2759441 = 2069581) B2069581
theorem B1866515 : Blo 1839621 1866515 := bstep (se 1 (by rfl) ⟨1399886, by rfl⟩ : syracuseStep 1866515 = 2799773) B2799773
theorem B2759459 : Blo 1839621 2759459 := bstep (se 1 (by rfl) ⟨2069594, by rfl⟩ : syracuseStep 2759459 = 4139189) B4139189
theorem B2947889 : Blo 1839621 2947889 := bstep (se 2 (by rfl) ⟨1105458, by rfl⟩ : syracuseStep 2947889 = 2210917) B2210917
theorem B2759489 : Blo 1839621 2759489 := bstep (se 2 (by rfl) ⟨1034808, by rfl⟩ : syracuseStep 2759489 = 2069617) B2069617
theorem B2071363 : Blo 1839621 2071363 := bstep (se 1 (by rfl) ⟨1553522, by rfl⟩ : syracuseStep 2071363 = 3107045) B3107045
theorem B2759507 : Blo 1839621 2759507 := bstep (se 1 (by rfl) ⟨2069630, by rfl⟩ : syracuseStep 2759507 = 4139261) B4139261
theorem B2759537 : Blo 1839621 2759537 := bstep (se 2 (by rfl) ⟨1034826, by rfl⟩ : syracuseStep 2759537 = 2069653) B2069653
theorem B2759555 : Blo 1839621 2759555 := bstep (se 1 (by rfl) ⟨2069666, by rfl⟩ : syracuseStep 2759555 = 4139333) B4139333
theorem B2759585 : Blo 1839621 2759585 := bstep (se 2 (by rfl) ⟨1034844, by rfl⟩ : syracuseStep 2759585 = 2069689) B2069689
theorem B5241773 : Blo 1839621 5241773 := bstep (se 3 (by rfl) ⟨982832, by rfl⟩ : syracuseStep 5241773 = 1965665) B1965665
theorem B2948017 : Blo 1839621 2948017 := bstep (se 2 (by rfl) ⟨1105506, by rfl⟩ : syracuseStep 2948017 = 2211013) B2211013
theorem B2759603 : Blo 1839621 2759603 := bstep (se 1 (by rfl) ⟨2069702, by rfl⟩ : syracuseStep 2759603 = 4139405) B4139405
theorem B4660163 : Blo 1839621 4660163 := bstep (se 1 (by rfl) ⟨3495122, by rfl⟩ : syracuseStep 4660163 = 6990245) B6990245
theorem B12598213 : Blo 1839621 12598213 := bstep (se 4 (by rfl) ⟨1181082, by rfl⟩ : syracuseStep 12598213 = 2362165) B2362165
theorem B2759633 : Blo 1839621 2759633 := bstep (se 2 (by rfl) ⟨1034862, by rfl⟩ : syracuseStep 2759633 = 2069725) B2069725
theorem B2071507 : Blo 1839621 2071507 := bstep (se 1 (by rfl) ⟨1553630, by rfl⟩ : syracuseStep 2071507 = 3107261) B3107261
theorem B2759651 : Blo 1839621 2759651 := bstep (se 1 (by rfl) ⟨2069738, by rfl⟩ : syracuseStep 2759651 = 4139477) B4139477
theorem B13982705 : Blo 1839621 13982705 := bstep (se 2 (by rfl) ⟨5243514, by rfl⟩ : syracuseStep 13982705 = 10487029) B10487029
theorem B2759681 : Blo 1839621 2759681 := bstep (se 2 (by rfl) ⟨1034880, by rfl⟩ : syracuseStep 2759681 = 2069761) B2069761
theorem B2759699 : Blo 1839621 2759699 := bstep (se 1 (by rfl) ⟨2069774, by rfl⟩ : syracuseStep 2759699 = 4139549) B4139549
theorem B2759729 : Blo 1839621 2759729 := bstep (se 2 (by rfl) ⟨1034898, by rfl⟩ : syracuseStep 2759729 = 2069797) B2069797
theorem B2759747 : Blo 1839621 2759747 := bstep (se 1 (by rfl) ⟨2069810, by rfl⟩ : syracuseStep 2759747 = 4139621) B4139621
theorem B2759777 : Blo 1839621 2759777 := bstep (se 2 (by rfl) ⟨1034916, by rfl⟩ : syracuseStep 2759777 = 2069833) B2069833
theorem B9313379 : Blo 1839621 9313379 := bstep (se 1 (by rfl) ⟨6985034, by rfl⟩ : syracuseStep 9313379 = 13970069) B13970069
theorem B5241955 : Blo 1839621 5241955 := bstep (se 1 (by rfl) ⟨3931466, by rfl⟩ : syracuseStep 5241955 = 7862933) B7862933
theorem B2071651 : Blo 1839621 2071651 := bstep (se 1 (by rfl) ⟨1553738, by rfl⟩ : syracuseStep 2071651 = 3107477) B3107477
theorem B2759795 : Blo 1839621 2759795 := bstep (se 1 (by rfl) ⟨2069846, by rfl⟩ : syracuseStep 2759795 = 4139693) B4139693
theorem B4660355 : Blo 1839621 4660355 := bstep (se 1 (by rfl) ⟨3495266, by rfl⟩ : syracuseStep 4660355 = 6990533) B6990533
theorem B2759825 : Blo 1839621 2759825 := bstep (se 2 (by rfl) ⟨1034934, by rfl⟩ : syracuseStep 2759825 = 2069869) B2069869
theorem B2759843 : Blo 1839621 2759843 := bstep (se 1 (by rfl) ⟨2069882, by rfl⟩ : syracuseStep 2759843 = 4139765) B4139765
theorem B2759873 : Blo 1839621 2759873 := bstep (se 2 (by rfl) ⟨1034952, by rfl⟩ : syracuseStep 2759873 = 2069905) B2069905
theorem B3316945 : Blo 1839621 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B2759891 : Blo 1839621 2759891 := bstep (se 1 (by rfl) ⟨2069918, by rfl⟩ : syracuseStep 2759891 = 4139837) B4139837
theorem B5897443 : Blo 1839621 5897443 := bstep (se 1 (by rfl) ⟨4423082, by rfl⟩ : syracuseStep 5897443 = 8846165) B8846165
theorem B2759921 : Blo 1839621 2759921 := bstep (se 2 (by rfl) ⟨1034970, by rfl⟩ : syracuseStep 2759921 = 2069941) B2069941
theorem B2522353 : Blo 1839621 2522353 := bstep (se 2 (by rfl) ⟨945882, by rfl⟩ : syracuseStep 2522353 = 1891765) B1891765
theorem B2071795 : Blo 1839621 2071795 := bstep (se 1 (by rfl) ⟨1553846, by rfl⟩ : syracuseStep 2071795 = 3107693) B3107693
theorem B2759939 : Blo 1839621 2759939 := bstep (se 1 (by rfl) ⟨2069954, by rfl⟩ : syracuseStep 2759939 = 4139909) B4139909
theorem B2759969 : Blo 1839621 2759969 := bstep (se 2 (by rfl) ⟨1034988, by rfl⟩ : syracuseStep 2759969 = 2069977) B2069977
theorem B2620721 : Blo 1839621 2620721 := bstep (se 2 (by rfl) ⟨982770, by rfl⟩ : syracuseStep 2620721 = 1965541) B1965541
theorem B2948401 : Blo 1839621 2948401 := bstep (se 2 (by rfl) ⟨1105650, by rfl⟩ : syracuseStep 2948401 = 2211301) B2211301
theorem B2759987 : Blo 1839621 2759987 := bstep (se 1 (by rfl) ⟨2069990, by rfl⟩ : syracuseStep 2759987 = 4139981) B4139981
theorem B2760017 : Blo 1839621 2760017 := bstep (se 2 (by rfl) ⟨1035006, by rfl⟩ : syracuseStep 2760017 = 2070013) B2070013
theorem B2760035 : Blo 1839621 2760035 := bstep (se 1 (by rfl) ⟨2070026, by rfl⟩ : syracuseStep 2760035 = 4140053) B4140053
theorem B5979491 : Blo 1839621 5979491 := bstep (se 1 (by rfl) ⟨4484618, by rfl⟩ : syracuseStep 5979491 = 8969237) B8969237
theorem B4423025 : Blo 1839621 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B2760065 : Blo 1839621 2760065 := bstep (se 2 (by rfl) ⟨1035024, by rfl⟩ : syracuseStep 2760065 = 2070049) B2070049
theorem B2760083 : Blo 1839621 2760083 := bstep (se 1 (by rfl) ⟨2070062, by rfl⟩ : syracuseStep 2760083 = 4140125) B4140125
theorem B2760113 : Blo 1839621 2760113 := bstep (se 2 (by rfl) ⟨1035042, by rfl⟩ : syracuseStep 2760113 = 2070085) B2070085
theorem B2760131 : Blo 1839621 2760131 := bstep (se 1 (by rfl) ⟨2070098, by rfl⟩ : syracuseStep 2760131 = 4140197) B4140197
theorem B6208973 : Blo 1839621 6208973 := bstep (se 3 (by rfl) ⟨1164182, by rfl⟩ : syracuseStep 6208973 = 2328365) B2328365
theorem B2760161 : Blo 1839621 2760161 := bstep (se 2 (by rfl) ⟨1035060, by rfl⟩ : syracuseStep 2760161 = 2070121) B2070121
theorem B8846819 : Blo 1839621 8846819 := bstep (se 1 (by rfl) ⟨6635114, by rfl⟩ : syracuseStep 8846819 = 13270229) B13270229
theorem B2760179 : Blo 1839621 2760179 := bstep (se 1 (by rfl) ⟨2070134, by rfl⟩ : syracuseStep 2760179 = 4140269) B4140269
theorem B6209027 : Blo 1839621 6209027 := bstep (se 1 (by rfl) ⟨4656770, by rfl⟩ : syracuseStep 6209027 = 9313541) B9313541
theorem B2760209 : Blo 1839621 2760209 := bstep (se 2 (by rfl) ⟨1035078, by rfl⟩ : syracuseStep 2760209 = 2070157) B2070157
theorem B2760227 : Blo 1839621 2760227 := bstep (se 1 (by rfl) ⟨2070170, by rfl⟩ : syracuseStep 2760227 = 4140341) B4140341
theorem B2948657 : Blo 1839621 2948657 := bstep (se 2 (by rfl) ⟨1105746, by rfl⟩ : syracuseStep 2948657 = 2211493) B2211493
theorem B2760257 : Blo 1839621 2760257 := bstep (se 2 (by rfl) ⟨1035096, by rfl⟩ : syracuseStep 2760257 = 2070193) B2070193
theorem B5242445 : Blo 1839621 5242445 := bstep (se 3 (by rfl) ⟨982958, by rfl⟩ : syracuseStep 5242445 = 1965917) B1965917
theorem B2760275 : Blo 1839621 2760275 := bstep (se 1 (by rfl) ⟨2070206, by rfl⟩ : syracuseStep 2760275 = 4140413) B4140413
theorem B2760305 : Blo 1839621 2760305 := bstep (se 2 (by rfl) ⟨1035114, by rfl⟩ : syracuseStep 2760305 = 2070229) B2070229
theorem B2760323 : Blo 1839621 2760323 := bstep (se 1 (by rfl) ⟨2070242, by rfl⟩ : syracuseStep 2760323 = 4140485) B4140485
theorem B10485389 : Blo 1839621 10485389 := bstep (se 3 (by rfl) ⟨1966010, by rfl⟩ : syracuseStep 10485389 = 3932021) B3932021
theorem B12770957 : Blo 1839621 12770957 := bstep (se 3 (by rfl) ⟨2394554, by rfl⟩ : syracuseStep 12770957 = 4789109) B4789109
theorem B2760353 : Blo 1839621 2760353 := bstep (se 2 (by rfl) ⟨1035132, by rfl⟩ : syracuseStep 2760353 = 2070265) B2070265
theorem B3104419 : Blo 1839621 3104419 := bstep (se 1 (by rfl) ⟨2328314, by rfl⟩ : syracuseStep 3104419 = 4656629) B4656629
theorem B6635171 : Blo 1839621 6635171 := bstep (se 1 (by rfl) ⟨4976378, by rfl⟩ : syracuseStep 6635171 = 9952757) B9952757
theorem B2760371 : Blo 1839621 2760371 := bstep (se 1 (by rfl) ⟨2070278, by rfl⟩ : syracuseStep 2760371 = 4140557) B4140557
theorem B2760401 : Blo 1839621 2760401 := bstep (se 2 (by rfl) ⟨1035150, by rfl⟩ : syracuseStep 2760401 = 2070301) B2070301
theorem B2760419 : Blo 1839621 2760419 := bstep (se 1 (by rfl) ⟨2070314, by rfl⟩ : syracuseStep 2760419 = 4140629) B4140629
theorem B8847089 : Blo 1839621 8847089 := bstep (se 2 (by rfl) ⟨3317658, by rfl⟩ : syracuseStep 8847089 = 6635317) B6635317
theorem B2760449 : Blo 1839621 2760449 := bstep (se 2 (by rfl) ⟨1035168, by rfl⟩ : syracuseStep 2760449 = 2070337) B2070337
theorem B6209297 : Blo 1839621 6209297 := bstep (se 2 (by rfl) ⟨2328486, by rfl⟩ : syracuseStep 6209297 = 4656973) B4656973
theorem B2760467 : Blo 1839621 2760467 := bstep (se 1 (by rfl) ⟨2070350, by rfl⟩ : syracuseStep 2760467 = 4140701) B4140701
theorem B11788067 : Blo 1839621 11788067 := bstep (se 1 (by rfl) ⟨8841050, by rfl⟩ : syracuseStep 11788067 = 17682101) B17682101
theorem B3104561 : Blo 1839621 3104561 := bstep (se 2 (by rfl) ⟨1164210, by rfl⟩ : syracuseStep 3104561 = 2328421) B2328421
theorem B2760497 : Blo 1839621 2760497 := bstep (se 2 (by rfl) ⟨1035186, by rfl⟩ : syracuseStep 2760497 = 2070373) B2070373
theorem B9322289 : Blo 1839621 9322289 := bstep (se 2 (by rfl) ⟨3495858, by rfl⟩ : syracuseStep 9322289 = 6991717) B6991717
theorem B2760515 : Blo 1839621 2760515 := bstep (se 1 (by rfl) ⟨2070386, by rfl⟩ : syracuseStep 2760515 = 4140773) B4140773
theorem B2621251 : Blo 1839621 2621251 := bstep (se 1 (by rfl) ⟨1965938, by rfl⟩ : syracuseStep 2621251 = 3931877) B3931877
theorem B2760545 : Blo 1839621 2760545 := bstep (se 2 (by rfl) ⟨1035204, by rfl⟩ : syracuseStep 2760545 = 2070409) B2070409
theorem B2760563 : Blo 1839621 2760563 := bstep (se 1 (by rfl) ⟨2070422, by rfl⟩ : syracuseStep 2760563 = 4140845) B4140845
theorem B9314189 : Blo 1839621 9314189 := bstep (se 3 (by rfl) ⟨1746410, by rfl⟩ : syracuseStep 9314189 = 3492821) B3492821
theorem B2760593 : Blo 1839621 2760593 := bstep (se 2 (by rfl) ⟨1035222, by rfl⟩ : syracuseStep 2760593 = 2070445) B2070445
theorem B2760611 : Blo 1839621 2760611 := bstep (se 1 (by rfl) ⟨2070458, by rfl⟩ : syracuseStep 2760611 = 4140917) B4140917
theorem B3104689 : Blo 1839621 3104689 := bstep (se 2 (by rfl) ⟨1164258, by rfl⟩ : syracuseStep 3104689 = 2328517) B2328517
theorem B4423601 : Blo 1839621 4423601 := bstep (se 2 (by rfl) ⟨1658850, by rfl⟩ : syracuseStep 4423601 = 3317701) B3317701
theorem B2760641 : Blo 1839621 2760641 := bstep (se 2 (by rfl) ⟨1035240, by rfl⟩ : syracuseStep 2760641 = 2070481) B2070481
theorem B3104723 : Blo 1839621 3104723 := bstep (se 1 (by rfl) ⟨2328542, by rfl⟩ : syracuseStep 3104723 = 4657085) B4657085
theorem B2760659 : Blo 1839621 2760659 := bstep (se 1 (by rfl) ⟨2070494, by rfl⟩ : syracuseStep 2760659 = 4140989) B4140989
theorem B31449059 : Blo 1839621 31449059 := bstep (se 1 (by rfl) ⟨23586794, by rfl⟩ : syracuseStep 31449059 = 47173589) B47173589
theorem B2760689 : Blo 1839621 2760689 := bstep (se 2 (by rfl) ⟨1035258, by rfl⟩ : syracuseStep 2760689 = 2070517) B2070517
theorem B79634501 : Blo 1839621 79634501 := bstep (se 4 (by rfl) ⟨7465734, by rfl⟩ : syracuseStep 79634501 = 14931469) B14931469
theorem B2760779 : Blo 1839621 2760779 := bstep (se 1 (by rfl) ⟨2070584, by rfl⟩ : syracuseStep 2760779 = 4141169) B4141169
theorem B2760791 : Blo 1839621 2760791 := bstep (se 1 (by rfl) ⟨2070593, by rfl⟩ : syracuseStep 2760791 = 4141187) B4141187
theorem B5898329 : Blo 1839621 5898329 := bstep (se 2 (by rfl) ⟨2211873, by rfl⟩ : syracuseStep 5898329 = 4423747) B4423747
theorem B2760857 : Blo 1839621 2760857 := bstep (se 2 (by rfl) ⟨1035321, by rfl⟩ : syracuseStep 2760857 = 2070643) B2070643
theorem B5243059 : Blo 1839621 5243059 := bstep (se 1 (by rfl) ⟨3932294, by rfl⟩ : syracuseStep 5243059 = 7864589) B7864589
theorem B6209729 : Blo 1839621 6209729 := bstep (se 2 (by rfl) ⟨2328648, by rfl⟩ : syracuseStep 6209729 = 4657297) B4657297
theorem B3932363 : Blo 1839621 3932363 := bstep (se 1 (by rfl) ⟨2949272, by rfl⟩ : syracuseStep 3932363 = 5898545) B5898545
theorem B2760971 : Blo 1839621 2760971 := bstep (se 1 (by rfl) ⟨2070728, by rfl⟩ : syracuseStep 2760971 = 4141457) B4141457
theorem B4972823 : Blo 1839621 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B3105047 : Blo 1839621 3105047 := bstep (se 1 (by rfl) ⟨2328785, by rfl⟩ : syracuseStep 3105047 = 4657571) B4657571
theorem B2760983 : Blo 1839621 2760983 := bstep (se 1 (by rfl) ⟨2070737, by rfl⟩ : syracuseStep 2760983 = 4141475) B4141475
theorem B7086359 : Blo 1839621 7086359 := bstep (se 1 (by rfl) ⟨5314769, by rfl⟩ : syracuseStep 7086359 = 10629539) B10629539
theorem B2761049 : Blo 1839621 2761049 := bstep (se 2 (by rfl) ⟨1035393, by rfl⟩ : syracuseStep 2761049 = 2070787) B2070787
theorem B13975901 : Blo 1839621 13975901 := bstep (se 3 (by rfl) ⟨2620481, by rfl⟩ : syracuseStep 13975901 = 5240963) B5240963
theorem B3105175 : Blo 1839621 3105175 := bstep (se 1 (by rfl) ⟨2328881, by rfl⟩ : syracuseStep 3105175 = 4657763) B4657763
theorem B5243287 : Blo 1839621 5243287 := bstep (se 1 (by rfl) ⟨3932465, by rfl⟩ : syracuseStep 5243287 = 7864931) B7864931
theorem B2949529 : Blo 1839621 2949529 := bstep (se 2 (by rfl) ⟨1106073, by rfl⟩ : syracuseStep 2949529 = 2212147) B2212147
theorem B2761163 : Blo 1839621 2761163 := bstep (se 1 (by rfl) ⟨2070872, by rfl⟩ : syracuseStep 2761163 = 4141745) B4141745
theorem B2761175 : Blo 1839621 2761175 := bstep (se 1 (by rfl) ⟨2070881, by rfl⟩ : syracuseStep 2761175 = 4141763) B4141763
theorem B2761241 : Blo 1839621 2761241 := bstep (se 2 (by rfl) ⟨1035465, by rfl⟩ : syracuseStep 2761241 = 2070931) B2070931
theorem B7864897 : Blo 1839621 7864897 := bstep (se 2 (by rfl) ⟨2949336, by rfl⟩ : syracuseStep 7864897 = 5898673) B5898673
theorem B2761355 : Blo 1839621 2761355 := bstep (se 1 (by rfl) ⟨2071016, by rfl⟩ : syracuseStep 2761355 = 4142033) B4142033
theorem B5595799 : Blo 1839621 5595799 := bstep (se 1 (by rfl) ⟨4196849, by rfl⟩ : syracuseStep 5595799 = 8393699) B8393699
theorem B2761367 : Blo 1839621 2761367 := bstep (se 1 (by rfl) ⟨2071025, by rfl⟩ : syracuseStep 2761367 = 4142051) B4142051
theorem B2949785 : Blo 1839621 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B2761433 : Blo 1839621 2761433 := bstep (se 2 (by rfl) ⟨1035537, by rfl⟩ : syracuseStep 2761433 = 2071075) B2071075
theorem B6210269 : Blo 1839621 6210269 := bstep (se 3 (by rfl) ⟨1164425, by rfl⟩ : syracuseStep 6210269 = 2328851) B2328851
theorem B218170097 : Blo 1839621 218170097 := bstep (se 2 (by rfl) ⟨81813786, by rfl⟩ : syracuseStep 218170097 = 163627573) B163627573
theorem B6988589 : Blo 1839621 6988589 := bstep (se 3 (by rfl) ⟨1310360, by rfl⟩ : syracuseStep 6988589 = 2620721) B2620721
theorem B6988619 : Blo 1839621 6988619 := bstep (se 1 (by rfl) ⟨5241464, by rfl⟩ : syracuseStep 6988619 = 10482929) B10482929
theorem B2761547 : Blo 1839621 2761547 := bstep (se 1 (by rfl) ⟨2071160, by rfl⟩ : syracuseStep 2761547 = 4142321) B4142321
theorem B2761559 : Blo 1839621 2761559 := bstep (se 1 (by rfl) ⟨2071169, by rfl⟩ : syracuseStep 2761559 = 4142339) B4142339
theorem B5899159 : Blo 1839621 5899159 := bstep (se 1 (by rfl) ⟨4424369, by rfl⟩ : syracuseStep 5899159 = 8848739) B8848739
theorem B2761625 : Blo 1839621 2761625 := bstep (se 2 (by rfl) ⟨1035609, by rfl⟩ : syracuseStep 2761625 = 2071219) B2071219
theorem B3933107 : Blo 1839621 3933107 := bstep (se 1 (by rfl) ⟨2949830, by rfl⟩ : syracuseStep 3933107 = 5899661) B5899661
theorem B3105803 : Blo 1839621 3105803 := bstep (se 1 (by rfl) ⟨2329352, by rfl⟩ : syracuseStep 3105803 = 4658705) B4658705
theorem B2761739 : Blo 1839621 2761739 := bstep (se 1 (by rfl) ⟨2071304, by rfl⟩ : syracuseStep 2761739 = 4142609) B4142609
theorem B2761751 : Blo 1839621 2761751 := bstep (se 1 (by rfl) ⟨2071313, by rfl⟩ : syracuseStep 2761751 = 4142627) B4142627
theorem B2761817 : Blo 1839621 2761817 := bstep (se 2 (by rfl) ⟨1035681, by rfl⟩ : syracuseStep 2761817 = 2071363) B2071363
theorem B2098315 : Blo 1839621 2098315 := bstep (se 1 (by rfl) ⟨1573736, by rfl⟩ : syracuseStep 2098315 = 3147473) B3147473
theorem B3105931 : Blo 1839621 3105931 := bstep (se 1 (by rfl) ⟨2329448, by rfl⟩ : syracuseStep 3105931 = 4658897) B4658897
theorem B2761931 : Blo 1839621 2761931 := bstep (se 1 (by rfl) ⟨2071448, by rfl⟩ : syracuseStep 2761931 = 4142897) B4142897
theorem B2761943 : Blo 1839621 2761943 := bstep (se 1 (by rfl) ⟨2071457, by rfl⟩ : syracuseStep 2761943 = 4142915) B4142915
theorem B3106073 : Blo 1839621 3106073 := bstep (se 2 (by rfl) ⟨1164777, by rfl⟩ : syracuseStep 3106073 = 2329555) B2329555
theorem B2762009 : Blo 1839621 2762009 := bstep (se 2 (by rfl) ⟨1035753, by rfl⟩ : syracuseStep 2762009 = 2071507) B2071507
theorem B17687909 : Blo 1839621 17687909 := bstep (se 4 (by rfl) ⟨1658241, by rfl⟩ : syracuseStep 17687909 = 3316483) B3316483
theorem B2762123 : Blo 1839621 2762123 := bstep (se 1 (by rfl) ⟨2071592, by rfl⟩ : syracuseStep 2762123 = 4143185) B4143185
theorem B2762135 : Blo 1839621 2762135 := bstep (se 1 (by rfl) ⟨2071601, by rfl⟩ : syracuseStep 2762135 = 4143203) B4143203
theorem B3106201 : Blo 1839621 3106201 := bstep (se 2 (by rfl) ⟨1164825, by rfl⟩ : syracuseStep 3106201 = 2329651) B2329651
theorem B6989273 : Blo 1839621 6989273 := bstep (se 2 (by rfl) ⟨2620977, by rfl⟩ : syracuseStep 6989273 = 5241955) B5241955
theorem B2762201 : Blo 1839621 2762201 := bstep (se 2 (by rfl) ⟨1035825, by rfl⟩ : syracuseStep 2762201 = 2071651) B2071651
theorem B2762315 : Blo 1839621 2762315 := bstep (se 1 (by rfl) ⟨2071736, by rfl⟩ : syracuseStep 2762315 = 4143473) B4143473
theorem B2762327 : Blo 1839621 2762327 := bstep (se 1 (by rfl) ⟨2071745, by rfl⟩ : syracuseStep 2762327 = 4143491) B4143491
theorem B9315971 : Blo 1839621 9315971 := bstep (se 1 (by rfl) ⟨6986978, by rfl⟩ : syracuseStep 9315971 = 13973957) B13973957
theorem B8849047 : Blo 1839621 8849047 := bstep (se 1 (by rfl) ⟨6636785, by rfl⟩ : syracuseStep 8849047 = 13273571) B13273571
theorem B2762393 : Blo 1839621 2762393 := bstep (se 2 (by rfl) ⟨1035897, by rfl⟩ : syracuseStep 2762393 = 2071795) B2071795
theorem B34055885 : Blo 1839621 34055885 := bstep (se 3 (by rfl) ⟨6385478, by rfl⟩ : syracuseStep 34055885 = 12770957) B12770957
theorem B6989591 : Blo 1839621 6989591 := bstep (se 1 (by rfl) ⟨5242193, by rfl⟩ : syracuseStep 6989591 = 10484387) B10484387
theorem B6211403 : Blo 1839621 6211403 := bstep (se 1 (by rfl) ⟨4658552, by rfl⟩ : syracuseStep 6211403 = 9317105) B9317105
theorem B3106775 : Blo 1839621 3106775 := bstep (se 1 (by rfl) ⟨2330081, by rfl⟩ : syracuseStep 3106775 = 4660163) B4660163
theorem B3106903 : Blo 1839621 3106903 := bstep (se 1 (by rfl) ⟨2330177, by rfl⟩ : syracuseStep 3106903 = 4660355) B4660355
theorem B6211673 : Blo 1839621 6211673 := bstep (se 2 (by rfl) ⟨2329377, by rfl⟩ : syracuseStep 6211673 = 4658755) B4658755
theorem B10487987 : Blo 1839621 10487987 := bstep (se 1 (by rfl) ⟨7865990, by rfl⟩ : syracuseStep 10487987 = 15731981) B15731981
theorem B4139225 : Blo 1839621 4139225 := bstep (se 2 (by rfl) ⟨1552209, by rfl⟩ : syracuseStep 4139225 = 3104419) B3104419
theorem B5597405 : Blo 1839621 5597405 := bstep (se 3 (by rfl) ⟨1049513, by rfl⟩ : syracuseStep 5597405 = 2099027) B2099027
theorem B3729689 : Blo 1839621 3729689 := bstep (se 2 (by rfl) ⟨1398633, by rfl⟩ : syracuseStep 3729689 = 2797267) B2797267
theorem B4139315 : Blo 1839621 4139315 := bstep (se 1 (by rfl) ⟨3104486, by rfl⟩ : syracuseStep 4139315 = 6208973) B6208973
theorem B2328907 : Blo 1839621 2328907 := bstep (se 1 (by rfl) ⟨1746680, by rfl⟩ : syracuseStep 2328907 = 3493361) B3493361
theorem B4139351 : Blo 1839621 4139351 := bstep (se 1 (by rfl) ⟨3104513, by rfl⟩ : syracuseStep 4139351 = 6209027) B6209027
theorem B6990259 : Blo 1839621 6990259 := bstep (se 1 (by rfl) ⟨5242694, by rfl⟩ : syracuseStep 6990259 = 10485389) B10485389
theorem B4139531 : Blo 1839621 4139531 := bstep (se 1 (by rfl) ⟨3104648, by rfl⟩ : syracuseStep 4139531 = 6209297) B6209297
theorem B7858711 : Blo 1839621 7858711 := bstep (se 1 (by rfl) ⟨5894033, by rfl⟩ : syracuseStep 7858711 = 11788067) B11788067
theorem B4139585 : Blo 1839621 4139585 := bstep (se 2 (by rfl) ⟨1552344, by rfl⟩ : syracuseStep 4139585 = 3104689) B3104689
theorem B2329175 : Blo 1839621 2329175 := bstep (se 1 (by rfl) ⟨1746881, by rfl⟩ : syracuseStep 2329175 = 3493763) B3493763
theorem B7858781 : Blo 1839621 7858781 := bstep (se 3 (by rfl) ⟨1473521, by rfl⟩ : syracuseStep 7858781 = 2947043) B2947043
theorem B20966039 : Blo 1839621 20966039 := bstep (se 1 (by rfl) ⟨15724529, by rfl⟩ : syracuseStep 20966039 = 31449059) B31449059
theorem B3107531 : Blo 1839621 3107531 := bstep (se 1 (by rfl) ⟨2330648, by rfl⟩ : syracuseStep 3107531 = 4661297) B4661297
theorem B2837207 : Blo 1839621 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B6212375 : Blo 1839621 6212375 := bstep (se 1 (by rfl) ⟨4659281, by rfl⟩ : syracuseStep 6212375 = 9318563) B9318563
theorem B4139801 : Blo 1839621 4139801 := bstep (se 2 (by rfl) ⟨1552425, by rfl⟩ : syracuseStep 4139801 = 3104851) B3104851
theorem B3107659 : Blo 1839621 3107659 := bstep (se 1 (by rfl) ⟨2330744, by rfl⟩ : syracuseStep 3107659 = 4661489) B4661489
theorem B4139891 : Blo 1839621 4139891 := bstep (se 1 (by rfl) ⟨3104918, by rfl⟩ : syracuseStep 4139891 = 6209837) B6209837
theorem B4139927 : Blo 1839621 4139927 := bstep (se 1 (by rfl) ⟨3104945, by rfl⟩ : syracuseStep 4139927 = 6209891) B6209891
theorem B4197323 : Blo 1839621 4197323 := bstep (se 1 (by rfl) ⟨3147992, by rfl⟩ : syracuseStep 4197323 = 6295985) B6295985
theorem B3492875 : Blo 1839621 3492875 := bstep (se 1 (by rfl) ⟨2619656, by rfl⟩ : syracuseStep 3492875 = 5239313) B5239313
theorem B19147811 : Blo 1839621 19147811 := bstep (se 1 (by rfl) ⟨14360858, by rfl⟩ : syracuseStep 19147811 = 28721717) B28721717
theorem B14928941 : Blo 1839621 14928941 := bstep (se 3 (by rfl) ⟨2799176, by rfl⟩ : syracuseStep 14928941 = 5598353) B5598353
theorem B4140107 : Blo 1839621 4140107 := bstep (se 1 (by rfl) ⟨3105080, by rfl⟩ : syracuseStep 4140107 = 6210161) B6210161
theorem B4140161 : Blo 1839621 4140161 := bstep (se 2 (by rfl) ⟨1552560, by rfl⟩ : syracuseStep 4140161 = 3105121) B3105121
theorem B3493057 : Blo 1839621 3493057 := bstep (se 2 (by rfl) ⟨1309896, by rfl⟩ : syracuseStep 3493057 = 2619793) B2619793
theorem B14175449 : Blo 1839621 14175449 := bstep (se 2 (by rfl) ⟨5315793, by rfl⟩ : syracuseStep 14175449 = 10631587) B10631587
theorem B6630673 : Blo 1839621 6630673 := bstep (se 2 (by rfl) ⟨2486502, by rfl⟩ : syracuseStep 6630673 = 4973005) B4973005
theorem B2329879 : Blo 1839621 2329879 := bstep (se 1 (by rfl) ⟨1747409, by rfl⟩ : syracuseStep 2329879 = 3494819) B3494819
theorem B6212915 : Blo 1839621 6212915 := bstep (se 1 (by rfl) ⟨4659686, by rfl⟩ : syracuseStep 6212915 = 9319373) B9319373
theorem B7859531 : Blo 1839621 7859531 := bstep (se 1 (by rfl) ⟨5894648, by rfl⟩ : syracuseStep 7859531 = 11789297) B11789297
theorem B13266251 : Blo 1839621 13266251 := bstep (se 1 (by rfl) ⟨9949688, by rfl⟩ : syracuseStep 13266251 = 19899377) B19899377
theorem B4140377 : Blo 1839621 4140377 := bstep (se 2 (by rfl) ⟨1552641, by rfl⟩ : syracuseStep 4140377 = 3105283) B3105283
theorem B4140467 : Blo 1839621 4140467 := bstep (se 1 (by rfl) ⟨3105350, by rfl⟩ : syracuseStep 4140467 = 6210701) B6210701
theorem B4140503 : Blo 1839621 4140503 := bstep (se 1 (by rfl) ⟨3105377, by rfl⟩ : syracuseStep 4140503 = 6210755) B6210755
theorem B10481197 : Blo 1839621 10481197 := bstep (se 3 (by rfl) ⟨1965224, by rfl⟩ : syracuseStep 10481197 = 3930449) B3930449
theorem B6213185 : Blo 1839621 6213185 := bstep (se 2 (by rfl) ⟨2329944, by rfl⟩ : syracuseStep 6213185 = 4659889) B4659889
theorem B3493505 : Blo 1839621 3493505 := bstep (se 2 (by rfl) ⟨1310064, by rfl⟩ : syracuseStep 3493505 = 2620129) B2620129
theorem B4140683 : Blo 1839621 4140683 := bstep (se 1 (by rfl) ⟨3105512, by rfl⟩ : syracuseStep 4140683 = 6211025) B6211025
theorem B6991505 : Blo 1839621 6991505 := bstep (se 2 (by rfl) ⟨2621814, by rfl⟩ : syracuseStep 6991505 = 5243629) B5243629
theorem B4656791 : Blo 1839621 4656791 := bstep (se 1 (by rfl) ⟨3492593, by rfl⟩ : syracuseStep 4656791 = 6985187) B6985187
theorem B4140737 : Blo 1839621 4140737 := bstep (se 2 (by rfl) ⟨1552776, by rfl⟩ : syracuseStep 4140737 = 3105553) B3105553
theorem B31444685 : Blo 1839621 31444685 := bstep (se 3 (by rfl) ⟨5895878, by rfl⟩ : syracuseStep 31444685 = 11791757) B11791757
theorem B6295261 : Blo 1839621 6295261 := bstep (se 3 (by rfl) ⟨1180361, by rfl⟩ : syracuseStep 6295261 = 2360723) B2360723
theorem B18886445 : Blo 1839621 18886445 := bstep (se 3 (by rfl) ⟨3541208, by rfl⟩ : syracuseStep 18886445 = 7082417) B7082417
theorem B4312919 : Blo 1839621 4312919 := bstep (se 1 (by rfl) ⟨3234689, by rfl⟩ : syracuseStep 4312919 = 6469379) B6469379
theorem B39808867 : Blo 1839621 39808867 := bstep (se 1 (by rfl) ⟨29856650, by rfl⟩ : syracuseStep 39808867 = 59713301) B59713301
theorem B4140953 : Blo 1839621 4140953 := bstep (se 2 (by rfl) ⟨1552857, by rfl⟩ : syracuseStep 4140953 = 3105715) B3105715
theorem B16797617 : Blo 1839621 16797617 := bstep (se 2 (by rfl) ⟨6299106, by rfl⟩ : syracuseStep 16797617 = 12598213) B12598213
theorem B5238731 : Blo 1839621 5238731 := bstep (se 1 (by rfl) ⟨3929048, by rfl⟩ : syracuseStep 5238731 = 7858097) B7858097
theorem B3493847 : Blo 1839621 3493847 := bstep (se 1 (by rfl) ⟨2620385, by rfl⟩ : syracuseStep 3493847 = 5240771) B5240771
theorem B4141043 : Blo 1839621 4141043 := bstep (se 1 (by rfl) ⟨3105782, by rfl⟩ : syracuseStep 4141043 = 6211565) B6211565
theorem B4141079 : Blo 1839621 4141079 := bstep (se 1 (by rfl) ⟨3105809, by rfl⟩ : syracuseStep 4141079 = 6211619) B6211619
theorem B25178147 : Blo 1839621 25178147 := bstep (se 1 (by rfl) ⟨18883610, by rfl⟩ : syracuseStep 25178147 = 37767221) B37767221
theorem B6295603 : Blo 1839621 6295603 := bstep (se 1 (by rfl) ⟨4721702, by rfl⟩ : syracuseStep 6295603 = 9443405) B9443405
theorem B7082059 : Blo 1839621 7082059 := bstep (se 1 (by rfl) ⟨5311544, by rfl⟩ : syracuseStep 7082059 = 10623089) B10623089
theorem B8843357 : Blo 1839621 8843357 := bstep (se 3 (by rfl) ⟨1658129, by rfl⟩ : syracuseStep 8843357 = 3316259) B3316259
theorem B6213725 : Blo 1839621 6213725 := bstep (se 3 (by rfl) ⟨1165073, by rfl⟩ : syracuseStep 6213725 = 2330147) B2330147
theorem B17682563 : Blo 1839621 17682563 := bstep (se 1 (by rfl) ⟨13261922, by rfl⟩ : syracuseStep 17682563 = 26523845) B26523845
theorem B4141259 : Blo 1839621 4141259 := bstep (se 1 (by rfl) ⟨3105944, by rfl⟩ : syracuseStep 4141259 = 6211889) B6211889
theorem B4141313 : Blo 1839621 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B4657459 : Blo 1839621 4657459 := bstep (se 1 (by rfl) ⟨3493094, by rfl⟩ : syracuseStep 4657459 = 6986189) B6986189
theorem B3363137 : Blo 1839621 3363137 := bstep (se 2 (by rfl) ⟨1261176, by rfl⟩ : syracuseStep 3363137 = 2522353) B2522353
theorem B6992203 : Blo 1839621 6992203 := bstep (se 1 (by rfl) ⟨5244152, by rfl⟩ : syracuseStep 6992203 = 10488305) B10488305
theorem B8622487 : Blo 1839621 8622487 := bstep (se 1 (by rfl) ⟨6466865, by rfl⟩ : syracuseStep 8622487 = 12933731) B12933731
theorem B4657601 : Blo 1839621 4657601 := bstep (se 2 (by rfl) ⟨1746600, by rfl⟩ : syracuseStep 4657601 = 3493201) B3493201
theorem B4141529 : Blo 1839621 4141529 := bstep (se 2 (by rfl) ⟨1553073, by rfl⟩ : syracuseStep 4141529 = 3106147) B3106147
theorem B1839627 : Blo 1839621 1839627 := bstep (se 1 (by rfl) ⟨1379720, by rfl⟩ : syracuseStep 1839627 = 2759441) B2759441
theorem B1839639 : Blo 1839621 1839639 := bstep (se 1 (by rfl) ⟨1379729, by rfl⟩ : syracuseStep 1839639 = 2759459) B2759459
theorem B1839659 : Blo 1839621 1839659 := bstep (se 1 (by rfl) ⟨1379744, by rfl⟩ : syracuseStep 1839659 = 2759489) B2759489
theorem B13972013 : Blo 1839621 13972013 := bstep (se 3 (by rfl) ⟨2619752, by rfl⟩ : syracuseStep 13972013 = 5239505) B5239505
theorem B4141619 : Blo 1839621 4141619 := bstep (se 1 (by rfl) ⟨3106214, by rfl⟩ : syracuseStep 4141619 = 6212429) B6212429
theorem B1839671 : Blo 1839621 1839671 := bstep (se 1 (by rfl) ⟨1379753, by rfl⟩ : syracuseStep 1839671 = 2759507) B2759507
theorem B1839691 : Blo 1839621 1839691 := bstep (se 1 (by rfl) ⟨1379768, by rfl⟩ : syracuseStep 1839691 = 2759537) B2759537
theorem B1839703 : Blo 1839621 1839703 := bstep (se 1 (by rfl) ⟨1379777, by rfl⟩ : syracuseStep 1839703 = 2759555) B2759555
theorem B4141655 : Blo 1839621 4141655 := bstep (se 1 (by rfl) ⟨3106241, by rfl⟩ : syracuseStep 4141655 = 6212483) B6212483
theorem B1839723 : Blo 1839621 1839723 := bstep (se 1 (by rfl) ⟨1379792, by rfl⟩ : syracuseStep 1839723 = 2759585) B2759585
theorem B3494515 : Blo 1839621 3494515 := bstep (se 1 (by rfl) ⟨2620886, by rfl⟩ : syracuseStep 3494515 = 5241773) B5241773
theorem B1839735 : Blo 1839621 1839735 := bstep (se 1 (by rfl) ⟨1379801, by rfl⟩ : syracuseStep 1839735 = 2759603) B2759603
theorem B1839755 : Blo 1839621 1839755 := bstep (se 1 (by rfl) ⟨1379816, by rfl⟩ : syracuseStep 1839755 = 2759633) B2759633
theorem B1839767 : Blo 1839621 1839767 := bstep (se 1 (by rfl) ⟨1379825, by rfl⟩ : syracuseStep 1839767 = 2759651) B2759651
theorem B1839787 : Blo 1839621 1839787 := bstep (se 1 (by rfl) ⟨1379840, by rfl⟩ : syracuseStep 1839787 = 2759681) B2759681
theorem B1839799 : Blo 1839621 1839799 := bstep (se 1 (by rfl) ⟨1379849, by rfl⟩ : syracuseStep 1839799 = 2759699) B2759699
theorem B1839819 : Blo 1839621 1839819 := bstep (se 1 (by rfl) ⟨1379864, by rfl⟩ : syracuseStep 1839819 = 2759729) B2759729
theorem B1839831 : Blo 1839621 1839831 := bstep (se 1 (by rfl) ⟨1379873, by rfl⟩ : syracuseStep 1839831 = 2759747) B2759747
theorem B4977373 : Blo 1839621 4977373 := bstep (se 3 (by rfl) ⟨933257, by rfl⟩ : syracuseStep 4977373 = 1866515) B1866515
theorem B1839851 : Blo 1839621 1839851 := bstep (se 1 (by rfl) ⟨1379888, by rfl⟩ : syracuseStep 1839851 = 2759777) B2759777
theorem B1839863 : Blo 1839621 1839863 := bstep (se 1 (by rfl) ⟨1379897, by rfl⟩ : syracuseStep 1839863 = 2759795) B2759795
theorem B1839883 : Blo 1839621 1839883 := bstep (se 1 (by rfl) ⟨1379912, by rfl⟩ : syracuseStep 1839883 = 2759825) B2759825
theorem B4141835 : Blo 1839621 4141835 := bstep (se 1 (by rfl) ⟨3106376, by rfl⟩ : syracuseStep 4141835 = 6212753) B6212753
theorem B1839895 : Blo 1839621 1839895 := bstep (se 1 (by rfl) ⟨1379921, by rfl⟩ : syracuseStep 1839895 = 2759843) B2759843
theorem B1839915 : Blo 1839621 1839915 := bstep (se 1 (by rfl) ⟨1379936, by rfl⟩ : syracuseStep 1839915 = 2759873) B2759873
theorem B1839927 : Blo 1839621 1839927 := bstep (se 1 (by rfl) ⟨1379945, by rfl⟩ : syracuseStep 1839927 = 2759891) B2759891
theorem B4141889 : Blo 1839621 4141889 := bstep (se 2 (by rfl) ⟨1553208, by rfl⟩ : syracuseStep 4141889 = 3106417) B3106417
theorem B1839947 : Blo 1839621 1839947 := bstep (se 1 (by rfl) ⟨1379960, by rfl⟩ : syracuseStep 1839947 = 2759921) B2759921
theorem B1839959 : Blo 1839621 1839959 := bstep (se 1 (by rfl) ⟨1379969, by rfl⟩ : syracuseStep 1839959 = 2759939) B2759939
theorem B1839979 : Blo 1839621 1839979 := bstep (se 1 (by rfl) ⟨1379984, by rfl⟩ : syracuseStep 1839979 = 2759969) B2759969
theorem B1839991 : Blo 1839621 1839991 := bstep (se 1 (by rfl) ⟨1379993, by rfl⟩ : syracuseStep 1839991 = 2759987) B2759987
theorem B1840011 : Blo 1839621 1840011 := bstep (se 1 (by rfl) ⟨1380008, by rfl⟩ : syracuseStep 1840011 = 2760017) B2760017
theorem B1840023 : Blo 1839621 1840023 := bstep (se 1 (by rfl) ⟨1380017, by rfl⟩ : syracuseStep 1840023 = 2760035) B2760035
theorem B11662231 : Blo 1839621 11662231 := bstep (se 1 (by rfl) ⟨8746673, by rfl⟩ : syracuseStep 11662231 = 17493347) B17493347
theorem B3986327 : Blo 1839621 3986327 := bstep (se 1 (by rfl) ⟨2989745, by rfl⟩ : syracuseStep 3986327 = 5979491) B5979491
theorem B1840043 : Blo 1839621 1840043 := bstep (se 1 (by rfl) ⟨1380032, by rfl⟩ : syracuseStep 1840043 = 2760065) B2760065
theorem B1840055 : Blo 1839621 1840055 := bstep (se 1 (by rfl) ⟨1380041, by rfl⟩ : syracuseStep 1840055 = 2760083) B2760083
theorem B1840075 : Blo 1839621 1840075 := bstep (se 1 (by rfl) ⟨1380056, by rfl⟩ : syracuseStep 1840075 = 2760113) B2760113
theorem B1840087 : Blo 1839621 1840087 := bstep (se 1 (by rfl) ⟨1380065, by rfl⟩ : syracuseStep 1840087 = 2760131) B2760131
theorem B1840107 : Blo 1839621 1840107 := bstep (se 1 (by rfl) ⟨1380080, by rfl⟩ : syracuseStep 1840107 = 2760161) B2760161
theorem B1840119 : Blo 1839621 1840119 := bstep (se 1 (by rfl) ⟨1380089, by rfl⟩ : syracuseStep 1840119 = 2760179) B2760179
theorem B1840139 : Blo 1839621 1840139 := bstep (se 1 (by rfl) ⟨1380104, by rfl⟩ : syracuseStep 1840139 = 2760209) B2760209
theorem B1840151 : Blo 1839621 1840151 := bstep (se 1 (by rfl) ⟨1380113, by rfl⟩ : syracuseStep 1840151 = 2760227) B2760227
theorem B4142105 : Blo 1839621 4142105 := bstep (se 2 (by rfl) ⟨1553289, by rfl⟩ : syracuseStep 4142105 = 3106579) B3106579
theorem B1840171 : Blo 1839621 1840171 := bstep (se 1 (by rfl) ⟨1380128, by rfl⟩ : syracuseStep 1840171 = 2760257) B2760257
theorem B3494963 : Blo 1839621 3494963 := bstep (se 1 (by rfl) ⟨2621222, by rfl⟩ : syracuseStep 3494963 = 5242445) B5242445
theorem B1840183 : Blo 1839621 1840183 := bstep (se 1 (by rfl) ⟨1380137, by rfl⟩ : syracuseStep 1840183 = 2760275) B2760275
theorem B1840203 : Blo 1839621 1840203 := bstep (se 1 (by rfl) ⟨1380152, by rfl⟩ : syracuseStep 1840203 = 2760305) B2760305
theorem B1840215 : Blo 1839621 1840215 := bstep (se 1 (by rfl) ⟨1380161, by rfl⟩ : syracuseStep 1840215 = 2760323) B2760323
theorem B3495001 : Blo 1839621 3495001 := bstep (se 2 (by rfl) ⟨1310625, by rfl⟩ : syracuseStep 3495001 = 2621251) B2621251
theorem B1840235 : Blo 1839621 1840235 := bstep (se 1 (by rfl) ⟨1380176, by rfl⟩ : syracuseStep 1840235 = 2760353) B2760353
theorem B4142195 : Blo 1839621 4142195 := bstep (se 1 (by rfl) ⟨3106646, by rfl⟩ : syracuseStep 4142195 = 6213293) B6213293
theorem B1840247 : Blo 1839621 1840247 := bstep (se 1 (by rfl) ⟨1380185, by rfl⟩ : syracuseStep 1840247 = 2760371) B2760371
theorem B1840267 : Blo 1839621 1840267 := bstep (se 1 (by rfl) ⟨1380200, by rfl⟩ : syracuseStep 1840267 = 2760401) B2760401
theorem B1840279 : Blo 1839621 1840279 := bstep (se 1 (by rfl) ⟨1380209, by rfl⟩ : syracuseStep 1840279 = 2760419) B2760419
theorem B4142231 : Blo 1839621 4142231 := bstep (se 1 (by rfl) ⟨3106673, by rfl⟩ : syracuseStep 4142231 = 6213347) B6213347
theorem B1840299 : Blo 1839621 1840299 := bstep (se 1 (by rfl) ⟨1380224, by rfl⟩ : syracuseStep 1840299 = 2760449) B2760449
theorem B1840311 : Blo 1839621 1840311 := bstep (se 1 (by rfl) ⟨1380233, by rfl⟩ : syracuseStep 1840311 = 2760467) B2760467
theorem B2069707 : Blo 1839621 2069707 := bstep (se 1 (by rfl) ⟨1552280, by rfl⟩ : syracuseStep 2069707 = 3104561) B3104561
theorem B7664843 : Blo 1839621 7664843 := bstep (se 1 (by rfl) ⟨5748632, by rfl⟩ : syracuseStep 7664843 = 11497265) B11497265
theorem B1840331 : Blo 1839621 1840331 := bstep (se 1 (by rfl) ⟨1380248, by rfl⟩ : syracuseStep 1840331 = 2760497) B2760497
theorem B14169293 : Blo 1839621 14169293 := bstep (se 3 (by rfl) ⟨2656742, by rfl⟩ : syracuseStep 14169293 = 5313485) B5313485
theorem B1840343 : Blo 1839621 1840343 := bstep (se 1 (by rfl) ⟨1380257, by rfl⟩ : syracuseStep 1840343 = 2760515) B2760515
theorem B3929305 : Blo 1839621 3929305 := bstep (se 2 (by rfl) ⟨1473489, by rfl⟩ : syracuseStep 3929305 = 2946979) B2946979
theorem B1840363 : Blo 1839621 1840363 := bstep (se 1 (by rfl) ⟨1380272, by rfl⟩ : syracuseStep 1840363 = 2760545) B2760545
theorem B1840375 : Blo 1839621 1840375 := bstep (se 1 (by rfl) ⟨1380281, by rfl⟩ : syracuseStep 1840375 = 2760563) B2760563
theorem B17683717 : Blo 1839621 17683717 := bstep (se 4 (by rfl) ⟨1657848, by rfl⟩ : syracuseStep 17683717 = 3315697) B3315697
theorem B1840395 : Blo 1839621 1840395 := bstep (se 1 (by rfl) ⟨1380296, by rfl⟩ : syracuseStep 1840395 = 2760593) B2760593
theorem B9319697 : Blo 1839621 9319697 := bstep (se 2 (by rfl) ⟨3494886, by rfl⟩ : syracuseStep 9319697 = 6989773) B6989773
theorem B1840407 : Blo 1839621 1840407 := bstep (se 1 (by rfl) ⟨1380305, by rfl⟩ : syracuseStep 1840407 = 2760611) B2760611
theorem B1865003 : Blo 1839621 1865003 := bstep (se 1 (by rfl) ⟨1398752, by rfl⟩ : syracuseStep 1865003 = 2797505) B2797505
theorem B1840427 : Blo 1839621 1840427 := bstep (se 1 (by rfl) ⟨1380320, by rfl⟩ : syracuseStep 1840427 = 2760641) B2760641
theorem B8394029 : Blo 1839621 8394029 := bstep (se 3 (by rfl) ⟨1573880, by rfl⟩ : syracuseStep 8394029 = 3147761) B3147761
theorem B2069815 : Blo 1839621 2069815 := bstep (se 1 (by rfl) ⟨1552361, by rfl⟩ : syracuseStep 2069815 = 3104723) B3104723
theorem B1840439 : Blo 1839621 1840439 := bstep (se 1 (by rfl) ⟨1380329, by rfl⟩ : syracuseStep 1840439 = 2760659) B2760659
theorem B6632779 : Blo 1839621 6632779 := bstep (se 1 (by rfl) ⟨4974584, by rfl⟩ : syracuseStep 6632779 = 9949169) B9949169
theorem B1840459 : Blo 1839621 1840459 := bstep (se 1 (by rfl) ⟨1380344, by rfl⟩ : syracuseStep 1840459 = 2760689) B2760689
theorem B4142411 : Blo 1839621 4142411 := bstep (se 1 (by rfl) ⟨3106808, by rfl⟩ : syracuseStep 4142411 = 6213617) B6213617
theorem B1840471 : Blo 1839621 1840471 := bstep (se 1 (by rfl) ⟨1380353, by rfl⟩ : syracuseStep 1840471 = 2760707) B2760707
theorem B1840491 : Blo 1839621 1840491 := bstep (se 1 (by rfl) ⟨1380368, by rfl⟩ : syracuseStep 1840491 = 2760737) B2760737
theorem B1840503 : Blo 1839621 1840503 := bstep (se 1 (by rfl) ⟨1380377, by rfl⟩ : syracuseStep 1840503 = 2760755) B2760755
theorem B4142465 : Blo 1839621 4142465 := bstep (se 2 (by rfl) ⟨1553424, by rfl⟩ : syracuseStep 4142465 = 3106849) B3106849
theorem B1840523 : Blo 1839621 1840523 := bstep (se 1 (by rfl) ⟨1380392, by rfl⟩ : syracuseStep 1840523 = 2760785) B2760785
theorem B1840535 : Blo 1839621 1840535 := bstep (se 1 (by rfl) ⟨1380401, by rfl⟩ : syracuseStep 1840535 = 2760803) B2760803
theorem B11351447 : Blo 1839621 11351447 := bstep (se 1 (by rfl) ⟨8513585, by rfl⟩ : syracuseStep 11351447 = 17027171) B17027171
theorem B1840555 : Blo 1839621 1840555 := bstep (se 1 (by rfl) ⟨1380416, by rfl⟩ : syracuseStep 1840555 = 2760833) B2760833
theorem B9319859 : Blo 1839621 9319859 := bstep (se 1 (by rfl) ⟨6989894, by rfl⟩ : syracuseStep 9319859 = 13979789) B13979789
theorem B1840567 : Blo 1839621 1840567 := bstep (se 1 (by rfl) ⟨1380425, by rfl⟩ : syracuseStep 1840567 = 2760851) B2760851
theorem B1840587 : Blo 1839621 1840587 := bstep (se 1 (by rfl) ⟨1380440, by rfl⟩ : syracuseStep 1840587 = 2760881) B2760881
theorem B1840599 : Blo 1839621 1840599 := bstep (se 1 (by rfl) ⟨1380449, by rfl⟩ : syracuseStep 1840599 = 2760899) B2760899
theorem B3929561 : Blo 1839621 3929561 := bstep (se 2 (by rfl) ⟨1473585, by rfl⟩ : syracuseStep 3929561 = 2947171) B2947171
theorem B6215129 : Blo 1839621 6215129 := bstep (se 2 (by rfl) ⟨2330673, by rfl⟩ : syracuseStep 6215129 = 4661347) B4661347
theorem B2069995 : Blo 1839621 2069995 := bstep (se 1 (by rfl) ⟨1552496, by rfl⟩ : syracuseStep 2069995 = 3104993) B3104993
theorem B1840619 : Blo 1839621 1840619 := bstep (se 1 (by rfl) ⟨1380464, by rfl⟩ : syracuseStep 1840619 = 2760929) B2760929
theorem B1840631 : Blo 1839621 1840631 := bstep (se 1 (by rfl) ⟨1380473, by rfl⟩ : syracuseStep 1840631 = 2760947) B2760947
theorem B1840651 : Blo 1839621 1840651 := bstep (se 1 (by rfl) ⟨1380488, by rfl⟩ : syracuseStep 1840651 = 2760977) B2760977
theorem B1840663 : Blo 1839621 1840663 := bstep (se 1 (by rfl) ⟨1380497, by rfl⟩ : syracuseStep 1840663 = 2760995) B2760995
theorem B3495449 : Blo 1839621 3495449 := bstep (se 2 (by rfl) ⟨1310793, by rfl⟩ : syracuseStep 3495449 = 2621587) B2621587
theorem B1840683 : Blo 1839621 1840683 := bstep (se 1 (by rfl) ⟨1380512, by rfl⟩ : syracuseStep 1840683 = 2761025) B2761025
theorem B3315251 : Blo 1839621 3315251 := bstep (se 1 (by rfl) ⟨2486438, by rfl⟩ : syracuseStep 3315251 = 4972877) B4972877
theorem B5240371 : Blo 1839621 5240371 := bstep (se 1 (by rfl) ⟨3930278, by rfl⟩ : syracuseStep 5240371 = 7860557) B7860557
theorem B1840695 : Blo 1839621 1840695 := bstep (se 1 (by rfl) ⟨1380521, by rfl⟩ : syracuseStep 1840695 = 2761043) B2761043
theorem B1840715 : Blo 1839621 1840715 := bstep (se 1 (by rfl) ⟨1380536, by rfl⟩ : syracuseStep 1840715 = 2761073) B2761073
theorem B2070103 : Blo 1839621 2070103 := bstep (se 1 (by rfl) ⟨1552577, by rfl⟩ : syracuseStep 2070103 = 3105155) B3105155
theorem B1840727 : Blo 1839621 1840727 := bstep (se 1 (by rfl) ⟨1380545, by rfl⟩ : syracuseStep 1840727 = 2761091) B2761091
theorem B4142681 : Blo 1839621 4142681 := bstep (se 2 (by rfl) ⟨1553505, by rfl⟩ : syracuseStep 4142681 = 3107011) B3107011
theorem B1840747 : Blo 1839621 1840747 := bstep (se 1 (by rfl) ⟨1380560, by rfl⟩ : syracuseStep 1840747 = 2761121) B2761121
theorem B1840759 : Blo 1839621 1840759 := bstep (se 1 (by rfl) ⟨1380569, by rfl⟩ : syracuseStep 1840759 = 2761139) B2761139
theorem B3733121 : Blo 1839621 3733121 := bstep (se 2 (by rfl) ⟨1399920, by rfl⟩ : syracuseStep 3733121 = 2799841) B2799841
theorem B134395523 : Blo 1839621 134395523 := bstep (se 1 (by rfl) ⟨100796642, by rfl⟩ : syracuseStep 134395523 = 201593285) B201593285
theorem B1840779 : Blo 1839621 1840779 := bstep (se 1 (by rfl) ⟨1380584, by rfl⟩ : syracuseStep 1840779 = 2761169) B2761169
theorem B1840791 : Blo 1839621 1840791 := bstep (se 1 (by rfl) ⟨1380593, by rfl⟩ : syracuseStep 1840791 = 2761187) B2761187
theorem B1840811 : Blo 1839621 1840811 := bstep (se 1 (by rfl) ⟨1380608, by rfl⟩ : syracuseStep 1840811 = 2761217) B2761217
theorem B4658867 : Blo 1839621 4658867 := bstep (se 1 (by rfl) ⟨3494150, by rfl⟩ : syracuseStep 4658867 = 6988301) B6988301
theorem B4142771 : Blo 1839621 4142771 := bstep (se 1 (by rfl) ⟨3107078, by rfl⟩ : syracuseStep 4142771 = 6214157) B6214157
theorem B1840823 : Blo 1839621 1840823 := bstep (se 1 (by rfl) ⟨1380617, by rfl⟩ : syracuseStep 1840823 = 2761235) B2761235
theorem B1840843 : Blo 1839621 1840843 := bstep (se 1 (by rfl) ⟨1380632, by rfl⟩ : syracuseStep 1840843 = 2761265) B2761265
theorem B1840855 : Blo 1839621 1840855 := bstep (se 1 (by rfl) ⟨1380641, by rfl⟩ : syracuseStep 1840855 = 2761283) B2761283
theorem B4142807 : Blo 1839621 4142807 := bstep (se 1 (by rfl) ⟨3107105, by rfl⟩ : syracuseStep 4142807 = 6214211) B6214211
theorem B1840875 : Blo 1839621 1840875 := bstep (se 1 (by rfl) ⟨1380656, by rfl⟩ : syracuseStep 1840875 = 2761313) B2761313
theorem B1840887 : Blo 1839621 1840887 := bstep (se 1 (by rfl) ⟨1380665, by rfl⟩ : syracuseStep 1840887 = 2761331) B2761331
theorem B3315467 : Blo 1839621 3315467 := bstep (se 1 (by rfl) ⟨2486600, by rfl⟩ : syracuseStep 3315467 = 4973201) B4973201
theorem B2070283 : Blo 1839621 2070283 := bstep (se 1 (by rfl) ⟨1552712, by rfl⟩ : syracuseStep 2070283 = 3105425) B3105425
theorem B1840907 : Blo 1839621 1840907 := bstep (se 1 (by rfl) ⟨1380680, by rfl⟩ : syracuseStep 1840907 = 2761361) B2761361
theorem B1840919 : Blo 1839621 1840919 := bstep (se 1 (by rfl) ⟨1380689, by rfl⟩ : syracuseStep 1840919 = 2761379) B2761379
theorem B1840939 : Blo 1839621 1840939 := bstep (se 1 (by rfl) ⟨1380704, by rfl⟩ : syracuseStep 1840939 = 2761409) B2761409
theorem B1840951 : Blo 1839621 1840951 := bstep (se 1 (by rfl) ⟨1380713, by rfl⟩ : syracuseStep 1840951 = 2761427) B2761427
theorem B1840971 : Blo 1839621 1840971 := bstep (se 1 (by rfl) ⟨1380728, by rfl⟩ : syracuseStep 1840971 = 2761457) B2761457
theorem B1840983 : Blo 1839621 1840983 := bstep (se 1 (by rfl) ⟨1380737, by rfl⟩ : syracuseStep 1840983 = 2761475) B2761475
theorem B1841003 : Blo 1839621 1841003 := bstep (se 1 (by rfl) ⟨1380752, by rfl⟩ : syracuseStep 1841003 = 2761505) B2761505
theorem B3929971 : Blo 1839621 3929971 := bstep (se 1 (by rfl) ⟨2947478, by rfl⟩ : syracuseStep 3929971 = 5894957) B5894957
theorem B2070391 : Blo 1839621 2070391 := bstep (se 1 (by rfl) ⟨1552793, by rfl⟩ : syracuseStep 2070391 = 3105587) B3105587
theorem B1841015 : Blo 1839621 1841015 := bstep (se 1 (by rfl) ⟨1380761, by rfl⟩ : syracuseStep 1841015 = 2761523) B2761523
theorem B1841035 : Blo 1839621 1841035 := bstep (se 1 (by rfl) ⟨1380776, by rfl⟩ : syracuseStep 1841035 = 2761553) B2761553
theorem B4142987 : Blo 1839621 4142987 := bstep (se 1 (by rfl) ⟨3107240, by rfl⟩ : syracuseStep 4142987 = 6214481) B6214481
theorem B1841047 : Blo 1839621 1841047 := bstep (se 1 (by rfl) ⟨1380785, by rfl⟩ : syracuseStep 1841047 = 2761571) B2761571
theorem B1841067 : Blo 1839621 1841067 := bstep (se 1 (by rfl) ⟨1380800, by rfl⟩ : syracuseStep 1841067 = 2761601) B2761601
theorem B1841079 : Blo 1839621 1841079 := bstep (se 1 (by rfl) ⟨1380809, by rfl⟩ : syracuseStep 1841079 = 2761619) B2761619
theorem B4143041 : Blo 1839621 4143041 := bstep (se 2 (by rfl) ⟨1553640, by rfl⟩ : syracuseStep 4143041 = 3107281) B3107281
theorem B1841099 : Blo 1839621 1841099 := bstep (se 1 (by rfl) ⟨1380824, by rfl⟩ : syracuseStep 1841099 = 2761649) B2761649
theorem B1841111 : Blo 1839621 1841111 := bstep (se 1 (by rfl) ⟨1380833, by rfl⟩ : syracuseStep 1841111 = 2761667) B2761667
theorem B1841131 : Blo 1839621 1841131 := bstep (se 1 (by rfl) ⟨1380848, by rfl⟩ : syracuseStep 1841131 = 2761697) B2761697
theorem B1841143 : Blo 1839621 1841143 := bstep (se 1 (by rfl) ⟨1380857, by rfl⟩ : syracuseStep 1841143 = 2761715) B2761715
theorem B1841163 : Blo 1839621 1841163 := bstep (se 1 (by rfl) ⟨1380872, by rfl⟩ : syracuseStep 1841163 = 2761745) B2761745
theorem B1841175 : Blo 1839621 1841175 := bstep (se 1 (by rfl) ⟨1380881, by rfl⟩ : syracuseStep 1841175 = 2761763) B2761763
theorem B2070571 : Blo 1839621 2070571 := bstep (se 1 (by rfl) ⟨1552928, by rfl⟩ : syracuseStep 2070571 = 3105857) B3105857
theorem B1841195 : Blo 1839621 1841195 := bstep (se 1 (by rfl) ⟨1380896, by rfl⟩ : syracuseStep 1841195 = 2761793) B2761793
theorem B1841207 : Blo 1839621 1841207 := bstep (se 1 (by rfl) ⟨1380905, by rfl⟩ : syracuseStep 1841207 = 2761811) B2761811
theorem B1841227 : Blo 1839621 1841227 := bstep (se 1 (by rfl) ⟨1380920, by rfl⟩ : syracuseStep 1841227 = 2761841) B2761841
theorem B1841239 : Blo 1839621 1841239 := bstep (se 1 (by rfl) ⟨1380929, by rfl⟩ : syracuseStep 1841239 = 2761859) B2761859
theorem B1841259 : Blo 1839621 1841259 := bstep (se 1 (by rfl) ⟨1380944, by rfl⟩ : syracuseStep 1841259 = 2761889) B2761889
theorem B1841271 : Blo 1839621 1841271 := bstep (se 1 (by rfl) ⟨1380953, by rfl⟩ : syracuseStep 1841271 = 2761907) B2761907
theorem B1841291 : Blo 1839621 1841291 := bstep (se 1 (by rfl) ⟨1380968, by rfl⟩ : syracuseStep 1841291 = 2761937) B2761937
theorem B2070679 : Blo 1839621 2070679 := bstep (se 1 (by rfl) ⟨1553009, by rfl⟩ : syracuseStep 2070679 = 3106019) B3106019
theorem B1841303 : Blo 1839621 1841303 := bstep (se 1 (by rfl) ⟨1380977, by rfl⟩ : syracuseStep 1841303 = 2761955) B2761955
theorem B4143257 : Blo 1839621 4143257 := bstep (se 2 (by rfl) ⟨1553721, by rfl⟩ : syracuseStep 4143257 = 3107443) B3107443
theorem B1841323 : Blo 1839621 1841323 := bstep (se 1 (by rfl) ⟨1380992, by rfl⟩ : syracuseStep 1841323 = 2761985) B2761985
theorem B1841335 : Blo 1839621 1841335 := bstep (se 1 (by rfl) ⟨1381001, by rfl⟩ : syracuseStep 1841335 = 2762003) B2762003
theorem B4659403 : Blo 1839621 4659403 := bstep (se 1 (by rfl) ⟨3494552, by rfl⟩ : syracuseStep 4659403 = 6989105) B6989105
theorem B1841355 : Blo 1839621 1841355 := bstep (se 1 (by rfl) ⟨1381016, by rfl⟩ : syracuseStep 1841355 = 2762033) B2762033
theorem B1841367 : Blo 1839621 1841367 := bstep (se 1 (by rfl) ⟨1381025, by rfl⟩ : syracuseStep 1841367 = 2762051) B2762051
theorem B1841387 : Blo 1839621 1841387 := bstep (se 1 (by rfl) ⟨1381040, by rfl⟩ : syracuseStep 1841387 = 2762081) B2762081
theorem B4143347 : Blo 1839621 4143347 := bstep (se 1 (by rfl) ⟨3107510, by rfl⟩ : syracuseStep 4143347 = 6215021) B6215021
theorem B1841399 : Blo 1839621 1841399 := bstep (se 1 (by rfl) ⟨1381049, by rfl⟩ : syracuseStep 1841399 = 2762099) B2762099
theorem B3496193 : Blo 1839621 3496193 := bstep (se 2 (by rfl) ⟨1311072, by rfl⟩ : syracuseStep 3496193 = 2622145) B2622145
theorem B1841419 : Blo 1839621 1841419 := bstep (se 1 (by rfl) ⟨1381064, by rfl⟩ : syracuseStep 1841419 = 2762129) B2762129
theorem B2210071 : Blo 1839621 2210071 := bstep (se 1 (by rfl) ⟨1657553, by rfl⟩ : syracuseStep 2210071 = 3315107) B3315107
theorem B1841431 : Blo 1839621 1841431 := bstep (se 1 (by rfl) ⟨1381073, by rfl⟩ : syracuseStep 1841431 = 2762147) B2762147
theorem B4143383 : Blo 1839621 4143383 := bstep (se 1 (by rfl) ⟨3107537, by rfl⟩ : syracuseStep 4143383 = 6215075) B6215075
theorem B1841451 : Blo 1839621 1841451 := bstep (se 1 (by rfl) ⟨1381088, by rfl⟩ : syracuseStep 1841451 = 2762177) B2762177
theorem B11794733 : Blo 1839621 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B1841463 : Blo 1839621 1841463 := bstep (se 1 (by rfl) ⟨1381097, by rfl⟩ : syracuseStep 1841463 = 2762195) B2762195
theorem B2070859 : Blo 1839621 2070859 := bstep (se 1 (by rfl) ⟨1553144, by rfl⟩ : syracuseStep 2070859 = 3106289) B3106289
theorem B1841483 : Blo 1839621 1841483 := bstep (se 1 (by rfl) ⟨1381112, by rfl⟩ : syracuseStep 1841483 = 2762225) B2762225
theorem B1841495 : Blo 1839621 1841495 := bstep (se 1 (by rfl) ⟨1381121, by rfl⟩ : syracuseStep 1841495 = 2762243) B2762243
theorem B4659545 : Blo 1839621 4659545 := bstep (se 2 (by rfl) ⟨1747329, by rfl⟩ : syracuseStep 4659545 = 3494659) B3494659
theorem B1841515 : Blo 1839621 1841515 := bstep (se 1 (by rfl) ⟨1381136, by rfl⟩ : syracuseStep 1841515 = 2762273) B2762273
theorem B1841527 : Blo 1839621 1841527 := bstep (se 1 (by rfl) ⟨1381145, by rfl⟩ : syracuseStep 1841527 = 2762291) B2762291
theorem B1841547 : Blo 1839621 1841547 := bstep (se 1 (by rfl) ⟨1381160, by rfl⟩ : syracuseStep 1841547 = 2762321) B2762321
theorem B1841559 : Blo 1839621 1841559 := bstep (se 1 (by rfl) ⟨1381169, by rfl⟩ : syracuseStep 1841559 = 2762339) B2762339
theorem B1841579 : Blo 1839621 1841579 := bstep (se 1 (by rfl) ⟨1381184, by rfl⟩ : syracuseStep 1841579 = 2762369) B2762369
theorem B33593777 : Blo 1839621 33593777 := bstep (se 2 (by rfl) ⟨12597666, by rfl⟩ : syracuseStep 33593777 = 25195333) B25195333
theorem B2070967 : Blo 1839621 2070967 := bstep (se 1 (by rfl) ⟨1553225, by rfl⟩ : syracuseStep 2070967 = 3106451) B3106451
theorem B1841591 : Blo 1839621 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B4143563 : Blo 1839621 4143563 := bstep (se 1 (by rfl) ⟨3107672, by rfl⟩ : syracuseStep 4143563 = 6215345) B6215345
theorem B1841611 : Blo 1839621 1841611 := bstep (se 1 (by rfl) ⟨1381208, by rfl⟩ : syracuseStep 1841611 = 2762417) B2762417
theorem B1964503 : Blo 1839621 1964503 := bstep (se 1 (by rfl) ⟨1473377, by rfl⟩ : syracuseStep 1964503 = 2946755) B2946755
theorem B4143617 : Blo 1839621 4143617 := bstep (se 2 (by rfl) ⟨1553856, by rfl⟩ : syracuseStep 4143617 = 3107713) B3107713
theorem B2947607 : Blo 1839621 2947607 := bstep (se 1 (by rfl) ⟨2210705, by rfl⟩ : syracuseStep 2947607 = 4421411) B4421411
theorem B3930689 : Blo 1839621 3930689 := bstep (se 2 (by rfl) ⟨1474008, by rfl⟩ : syracuseStep 3930689 = 2948017) B2948017
theorem B5241419 : Blo 1839621 5241419 := bstep (se 1 (by rfl) ⟨3931064, by rfl⟩ : syracuseStep 5241419 = 7862129) B7862129
theorem B2071147 : Blo 1839621 2071147 := bstep (se 1 (by rfl) ⟨1553360, by rfl⟩ : syracuseStep 2071147 = 3106721) B3106721
theorem B6986371 : Blo 1839621 6986371 := bstep (se 1 (by rfl) ⟨5239778, by rfl⟩ : syracuseStep 6986371 = 10479557) B10479557
theorem B6634163 : Blo 1839621 6634163 := bstep (se 1 (by rfl) ⟨4975622, by rfl⟩ : syracuseStep 6634163 = 9951245) B9951245
theorem B2947799 : Blo 1839621 2947799 := bstep (se 1 (by rfl) ⟨2210849, by rfl⟩ : syracuseStep 2947799 = 4421699) B4421699
theorem B2071255 : Blo 1839621 2071255 := bstep (se 1 (by rfl) ⟨1553441, by rfl⟩ : syracuseStep 2071255 = 3106883) B3106883
theorem B2759435 : Blo 1839621 2759435 := bstep (se 1 (by rfl) ⟨2069576, by rfl⟩ : syracuseStep 2759435 = 4139153) B4139153
theorem B2759447 : Blo 1839621 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B7863085 : Blo 1839621 7863085 := bstep (se 3 (by rfl) ⟨1474328, by rfl⟩ : syracuseStep 7863085 = 2948657) B2948657
theorem B2759513 : Blo 1839621 2759513 := bstep (se 2 (by rfl) ⟨1034817, by rfl⟩ : syracuseStep 2759513 = 2069635) B2069635
theorem B2071435 : Blo 1839621 2071435 := bstep (se 1 (by rfl) ⟨1553576, by rfl⟩ : syracuseStep 2071435 = 3107153) B3107153
theorem B3931031 : Blo 1839621 3931031 := bstep (se 1 (by rfl) ⟨2948273, by rfl⟩ : syracuseStep 3931031 = 5896547) B5896547
theorem B6986675 : Blo 1839621 6986675 := bstep (se 1 (by rfl) ⟨5240006, by rfl⟩ : syracuseStep 6986675 = 10480013) B10480013
theorem B4422593 : Blo 1839621 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B2759627 : Blo 1839621 2759627 := bstep (se 1 (by rfl) ⟨2069720, by rfl⟩ : syracuseStep 2759627 = 4139441) B4139441
theorem B2759639 : Blo 1839621 2759639 := bstep (se 1 (by rfl) ⟨2069729, by rfl⟩ : syracuseStep 2759639 = 4139459) B4139459
theorem B7863257 : Blo 1839621 7863257 := bstep (se 2 (by rfl) ⟨2948721, by rfl⟩ : syracuseStep 7863257 = 5897443) B5897443
theorem B2071543 : Blo 1839621 2071543 := bstep (se 1 (by rfl) ⟨1553657, by rfl⟩ : syracuseStep 2071543 = 3107315) B3107315
theorem B2759705 : Blo 1839621 2759705 := bstep (se 2 (by rfl) ⟨1034889, by rfl⟩ : syracuseStep 2759705 = 2069779) B2069779
theorem B3931201 : Blo 1839621 3931201 := bstep (se 2 (by rfl) ⟨1474200, by rfl⟩ : syracuseStep 3931201 = 2948401) B2948401
theorem B2759819 : Blo 1839621 2759819 := bstep (se 1 (by rfl) ⟨2069864, by rfl⟩ : syracuseStep 2759819 = 4139729) B4139729
theorem B2759831 : Blo 1839621 2759831 := bstep (se 1 (by rfl) ⟨2069873, by rfl⟩ : syracuseStep 2759831 = 4139747) B4139747
theorem B13819031 : Blo 1839621 13819031 := bstep (se 1 (by rfl) ⟨10364273, by rfl⟩ : syracuseStep 13819031 = 20728547) B20728547
theorem B4660375 : Blo 1839621 4660375 := bstep (se 1 (by rfl) ⟨3495281, by rfl⟩ : syracuseStep 4660375 = 6990563) B6990563
theorem B2071723 : Blo 1839621 2071723 := bstep (se 1 (by rfl) ⟨1553792, by rfl⟩ : syracuseStep 2071723 = 3107585) B3107585
theorem B1965259 : Blo 1839621 1965259 := bstep (se 1 (by rfl) ⟨1473944, by rfl⟩ : syracuseStep 1965259 = 2947889) B2947889
theorem B2759897 : Blo 1839621 2759897 := bstep (se 2 (by rfl) ⟨1034961, by rfl⟩ : syracuseStep 2759897 = 2069923) B2069923
theorem B2760011 : Blo 1839621 2760011 := bstep (se 1 (by rfl) ⟨2070008, by rfl⟩ : syracuseStep 2760011 = 4140017) B4140017
theorem B9321803 : Blo 1839621 9321803 := bstep (se 1 (by rfl) ⟨6991352, by rfl⟩ : syracuseStep 9321803 = 13982705) B13982705
theorem B2760023 : Blo 1839621 2760023 := bstep (se 1 (by rfl) ⟨2070017, by rfl⟩ : syracuseStep 2760023 = 4140035) B4140035
theorem B6208919 : Blo 1839621 6208919 := bstep (se 1 (by rfl) ⟨4656689, by rfl⟩ : syracuseStep 6208919 = 9313379) B9313379
theorem B2760089 : Blo 1839621 2760089 := bstep (se 2 (by rfl) ⟨1035033, by rfl⟩ : syracuseStep 2760089 = 2070067) B2070067
theorem B2760203 : Blo 1839621 2760203 := bstep (se 1 (by rfl) ⟨2070152, by rfl⟩ : syracuseStep 2760203 = 4140305) B4140305
theorem B2760215 : Blo 1839621 2760215 := bstep (se 1 (by rfl) ⟨2070161, by rfl⟩ : syracuseStep 2760215 = 4140323) B4140323
theorem B6987329 : Blo 1839621 6987329 := bstep (se 2 (by rfl) ⟨2620248, by rfl⟩ : syracuseStep 6987329 = 5240497) B5240497
theorem B4660811 : Blo 1839621 4660811 := bstep (se 1 (by rfl) ⟨3495608, by rfl⟩ : syracuseStep 4660811 = 6991217) B6991217
theorem B2760281 : Blo 1839621 2760281 := bstep (se 2 (by rfl) ⟨1035105, by rfl⟩ : syracuseStep 2760281 = 2070211) B2070211
theorem B7462493 : Blo 1839621 7462493 := bstep (se 3 (by rfl) ⟨1399217, by rfl⟩ : syracuseStep 7462493 = 2798435) B2798435
theorem B5897879 : Blo 1839621 5897879 := bstep (se 1 (by rfl) ⟨4423409, by rfl⟩ : syracuseStep 5897879 = 8846819) B8846819
theorem B6214859 : Blo 1839621 6214859 := bstep (se 1 (by rfl) ⟨4661144, by rfl⟩ : syracuseStep 6214859 = 9322289) B9322289
theorem B2760395 : Blo 1839621 2760395 := bstep (se 1 (by rfl) ⟨2070296, by rfl⟩ : syracuseStep 2760395 = 4140593) B4140593
theorem B2760407 : Blo 1839621 2760407 := bstep (se 1 (by rfl) ⟨2070305, by rfl⟩ : syracuseStep 2760407 = 4140611) B4140611
theorem B3104473 : Blo 1839621 3104473 := bstep (se 2 (by rfl) ⟨1164177, by rfl⟩ : syracuseStep 3104473 = 2328355) B2328355
theorem B7462621 : Blo 1839621 7462621 := bstep (se 3 (by rfl) ⟨1399241, by rfl⟩ : syracuseStep 7462621 = 2798483) B2798483
theorem B4423447 : Blo 1839621 4423447 := bstep (se 1 (by rfl) ⟨3317585, by rfl⟩ : syracuseStep 4423447 = 6635171) B6635171
theorem B2760473 : Blo 1839621 2760473 := bstep (se 2 (by rfl) ⟨1035177, by rfl⟩ : syracuseStep 2760473 = 2070355) B2070355
theorem B5898059 : Blo 1839621 5898059 := bstep (se 1 (by rfl) ⟨4423544, by rfl⟩ : syracuseStep 5898059 = 8847089) B8847089
theorem B2760587 : Blo 1839621 2760587 := bstep (se 1 (by rfl) ⟨2070440, by rfl⟩ : syracuseStep 2760587 = 4140881) B4140881
theorem B2760599 : Blo 1839621 2760599 := bstep (se 1 (by rfl) ⟨2070449, by rfl⟩ : syracuseStep 2760599 = 4140899) B4140899
theorem B6209459 : Blo 1839621 6209459 := bstep (se 1 (by rfl) ⟨4657094, by rfl⟩ : syracuseStep 6209459 = 9314189) B9314189
theorem B4661185 : Blo 1839621 4661185 := bstep (se 2 (by rfl) ⟨1747944, by rfl⟩ : syracuseStep 4661185 = 3495889) B3495889
theorem B2949067 : Blo 1839621 2949067 := bstep (se 1 (by rfl) ⟨2211800, by rfl⟩ : syracuseStep 2949067 = 4423601) B4423601
theorem B2760665 : Blo 1839621 2760665 := bstep (se 2 (by rfl) ⟨1035249, by rfl⟩ : syracuseStep 2760665 = 2070499) B2070499
theorem B2760719 : Blo 1839621 2760719 := bstep (se 1 (by rfl) ⟨2070539, by rfl⟩ : syracuseStep 2760719 = 4141079) B4141079
theorem B16785431 : Blo 1839621 16785431 := bstep (se 1 (by rfl) ⟨12589073, by rfl⟩ : syracuseStep 16785431 = 25178147) B25178147
theorem B2760761 : Blo 1839621 2760761 := bstep (se 2 (by rfl) ⟨1035285, by rfl⟩ : syracuseStep 2760761 = 2070571) B2070571
theorem B3932219 : Blo 1839621 3932219 := bstep (se 1 (by rfl) ⟨2949164, by rfl⟩ : syracuseStep 3932219 = 5898329) B5898329
theorem B11788375 : Blo 1839621 11788375 := bstep (se 1 (by rfl) ⟨8841281, by rfl⟩ : syracuseStep 11788375 = 17682563) B17682563
theorem B51060829 : Blo 1839621 51060829 := bstep (se 3 (by rfl) ⟨9573905, by rfl⟩ : syracuseStep 51060829 = 19147811) B19147811
theorem B2760839 : Blo 1839621 2760839 := bstep (se 1 (by rfl) ⟨2070629, by rfl⟩ : syracuseStep 2760839 = 4141259) B4141259
theorem B2621575 : Blo 1839621 2621575 := bstep (se 1 (by rfl) ⟨1966181, by rfl⟩ : syracuseStep 2621575 = 3932363) B3932363
theorem B2760875 : Blo 1839621 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B2760905 : Blo 1839621 2760905 := bstep (se 2 (by rfl) ⟨1035339, by rfl⟩ : syracuseStep 2760905 = 2070679) B2070679
theorem B3105067 : Blo 1839621 3105067 := bstep (se 1 (by rfl) ⟨2328800, by rfl⟩ : syracuseStep 3105067 = 4657601) B4657601
theorem B2761019 : Blo 1839621 2761019 := bstep (se 1 (by rfl) ⟨2070764, by rfl⟩ : syracuseStep 2761019 = 4141529) B4141529
theorem B9314675 : Blo 1839621 9314675 := bstep (se 1 (by rfl) ⟨6986006, by rfl⟩ : syracuseStep 9314675 = 13972013) B13972013
theorem B2761079 : Blo 1839621 2761079 := bstep (se 1 (by rfl) ⟨2070809, by rfl⟩ : syracuseStep 2761079 = 4141619) B4141619
theorem B2761103 : Blo 1839621 2761103 := bstep (se 1 (by rfl) ⟨2070827, by rfl⟩ : syracuseStep 2761103 = 4141655) B4141655
theorem B6209945 : Blo 1839621 6209945 := bstep (se 2 (by rfl) ⟨2328729, by rfl⟩ : syracuseStep 6209945 = 4657459) B4657459
theorem B3105209 : Blo 1839621 3105209 := bstep (se 2 (by rfl) ⟨1164453, by rfl⟩ : syracuseStep 3105209 = 2328907) B2328907
theorem B2761145 : Blo 1839621 2761145 := bstep (se 2 (by rfl) ⟨1035429, by rfl⟩ : syracuseStep 2761145 = 2070859) B2070859
theorem B1966523 : Blo 1839621 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B9322937 : Blo 1839621 9322937 := bstep (se 2 (by rfl) ⟨3496101, by rfl⟩ : syracuseStep 9322937 = 6992203) B6992203
theorem B2761223 : Blo 1839621 2761223 := bstep (se 1 (by rfl) ⟨2070917, by rfl⟩ : syracuseStep 2761223 = 4141835) B4141835
theorem B3932705 : Blo 1839621 3932705 := bstep (se 2 (by rfl) ⟨1474764, by rfl⟩ : syracuseStep 3932705 = 2949529) B2949529
theorem B2761259 : Blo 1839621 2761259 := bstep (se 1 (by rfl) ⟨2070944, by rfl⟩ : syracuseStep 2761259 = 4141889) B4141889
theorem B2761289 : Blo 1839621 2761289 := bstep (se 2 (by rfl) ⟨1035483, by rfl⟩ : syracuseStep 2761289 = 2070967) B2070967
theorem B2622071 : Blo 1839621 2622071 := bstep (se 1 (by rfl) ⟨1966553, by rfl⟩ : syracuseStep 2622071 = 3933107) B3933107
theorem B2761403 : Blo 1839621 2761403 := bstep (se 1 (by rfl) ⟨2071052, by rfl⟩ : syracuseStep 2761403 = 4142105) B4142105
theorem B10478281 : Blo 1839621 10478281 := bstep (se 2 (by rfl) ⟨3929355, by rfl⟩ : syracuseStep 10478281 = 7858711) B7858711
theorem B11191013 : Blo 1839621 11191013 := bstep (se 4 (by rfl) ⟨1049157, by rfl⟩ : syracuseStep 11191013 = 2098315) B2098315
theorem B2761463 : Blo 1839621 2761463 := bstep (se 1 (by rfl) ⟨2071097, by rfl⟩ : syracuseStep 2761463 = 4142195) B4142195
theorem B10486529 : Blo 1839621 10486529 := bstep (se 2 (by rfl) ⟨3932448, by rfl⟩ : syracuseStep 10486529 = 7864897) B7864897
theorem B2761487 : Blo 1839621 2761487 := bstep (se 1 (by rfl) ⟨2071115, by rfl⟩ : syracuseStep 2761487 = 4142231) B4142231
theorem B4973341 : Blo 1839621 4973341 := bstep (se 3 (by rfl) ⟨932501, by rfl⟩ : syracuseStep 4973341 = 1865003) B1865003
theorem B9446195 : Blo 1839621 9446195 := bstep (se 1 (by rfl) ⟨7084646, by rfl⟩ : syracuseStep 9446195 = 14169293) B14169293
theorem B2761529 : Blo 1839621 2761529 := bstep (se 2 (by rfl) ⟨1035573, by rfl⟩ : syracuseStep 2761529 = 2071147) B2071147
theorem B9315161 : Blo 1839621 9315161 := bstep (se 2 (by rfl) ⟨3493185, by rfl⟩ : syracuseStep 9315161 = 6986371) B6986371
theorem B5596019 : Blo 1839621 5596019 := bstep (se 1 (by rfl) ⟨4197014, by rfl⟩ : syracuseStep 5596019 = 8394029) B8394029
theorem B2761607 : Blo 1839621 2761607 := bstep (se 1 (by rfl) ⟨2071205, by rfl⟩ : syracuseStep 2761607 = 4142411) B4142411
theorem B2761643 : Blo 1839621 2761643 := bstep (se 1 (by rfl) ⟨2071232, by rfl⟩ : syracuseStep 2761643 = 4142465) B4142465
theorem B2761673 : Blo 1839621 2761673 := bstep (se 2 (by rfl) ⟨1035627, by rfl⟩ : syracuseStep 2761673 = 2071255) B2071255
theorem B6636497 : Blo 1839621 6636497 := bstep (se 2 (by rfl) ⟨2488686, by rfl⟩ : syracuseStep 6636497 = 4977373) B4977373
theorem B2761787 : Blo 1839621 2761787 := bstep (se 1 (by rfl) ⟨2071340, by rfl⟩ : syracuseStep 2761787 = 4142681) B4142681
theorem B6210647 : Blo 1839621 6210647 := bstep (se 1 (by rfl) ⟨4657985, by rfl⟩ : syracuseStep 6210647 = 9315971) B9315971
theorem B89597015 : Blo 1839621 89597015 := bstep (se 1 (by rfl) ⟨67197761, by rfl⟩ : syracuseStep 89597015 = 134395523) B134395523
theorem B3105911 : Blo 1839621 3105911 := bstep (se 1 (by rfl) ⟨2329433, by rfl⟩ : syracuseStep 3105911 = 4658867) B4658867
theorem B2761847 : Blo 1839621 2761847 := bstep (se 1 (by rfl) ⟨2071385, by rfl⟩ : syracuseStep 2761847 = 4142771) B4142771
theorem B2761871 : Blo 1839621 2761871 := bstep (se 1 (by rfl) ⟨2071403, by rfl⟩ : syracuseStep 2761871 = 4142807) B4142807
theorem B2761913 : Blo 1839621 2761913 := bstep (se 2 (by rfl) ⟨1035717, by rfl⟩ : syracuseStep 2761913 = 2071435) B2071435
theorem B15549641 : Blo 1839621 15549641 := bstep (se 2 (by rfl) ⟨5831115, by rfl⟩ : syracuseStep 15549641 = 11662231) B11662231
theorem B2761991 : Blo 1839621 2761991 := bstep (se 1 (by rfl) ⟨2071493, by rfl⟩ : syracuseStep 2761991 = 4142987) B4142987
theorem B2762027 : Blo 1839621 2762027 := bstep (se 1 (by rfl) ⟨2071520, by rfl⟩ : syracuseStep 2762027 = 4143041) B4143041
theorem B2762057 : Blo 1839621 2762057 := bstep (se 2 (by rfl) ⟨1035771, by rfl⟩ : syracuseStep 2762057 = 2071543) B2071543
theorem B2762171 : Blo 1839621 2762171 := bstep (se 1 (by rfl) ⟨2071628, by rfl⟩ : syracuseStep 2762171 = 4143257) B4143257
theorem B2762231 : Blo 1839621 2762231 := bstep (se 1 (by rfl) ⟨2071673, by rfl⟩ : syracuseStep 2762231 = 4143347) B4143347
theorem B2762255 : Blo 1839621 2762255 := bstep (se 1 (by rfl) ⟨2071691, by rfl⟩ : syracuseStep 2762255 = 4143383) B4143383
theorem B2762297 : Blo 1839621 2762297 := bstep (se 2 (by rfl) ⟨1035861, by rfl⟩ : syracuseStep 2762297 = 2071723) B2071723
theorem B3106363 : Blo 1839621 3106363 := bstep (se 1 (by rfl) ⟨2329772, by rfl⟩ : syracuseStep 3106363 = 4659545) B4659545
theorem B6211133 : Blo 1839621 6211133 := bstep (se 3 (by rfl) ⟨1164587, by rfl⟩ : syracuseStep 6211133 = 2329175) B2329175
theorem B2762375 : Blo 1839621 2762375 := bstep (se 1 (by rfl) ⟨2071781, by rfl⟩ : syracuseStep 2762375 = 4143563) B4143563
theorem B2762411 : Blo 1839621 2762411 := bstep (se 1 (by rfl) ⟨2071808, by rfl⟩ : syracuseStep 2762411 = 4143617) B4143617
theorem B23578289 : Blo 1839621 23578289 := bstep (se 2 (by rfl) ⟨8841858, by rfl⟩ : syracuseStep 23578289 = 17683717) B17683717
theorem B8840897 : Blo 1839621 8840897 := bstep (se 2 (by rfl) ⟨3315336, by rfl⟩ : syracuseStep 8840897 = 6630673) B6630673
theorem B3106505 : Blo 1839621 3106505 := bstep (se 2 (by rfl) ⟨1164939, by rfl⟩ : syracuseStep 3106505 = 2329879) B2329879
theorem B13977359 : Blo 1839621 13977359 := bstep (se 1 (by rfl) ⟨10483019, by rfl⟩ : syracuseStep 13977359 = 20966039) B20966039
theorem B2328583 : Blo 1839621 2328583 := bstep (se 1 (by rfl) ⟨1746437, by rfl⟩ : syracuseStep 2328583 = 3492875) B3492875
theorem B11798729 : Blo 1839621 11798729 := bstep (se 2 (by rfl) ⟨4424523, by rfl⟩ : syracuseStep 11798729 = 8849047) B8849047
theorem B4139279 : Blo 1839621 4139279 := bstep (se 1 (by rfl) ⟨3104459, by rfl⟩ : syracuseStep 4139279 = 6208919) B6208919
theorem B4139297 : Blo 1839621 4139297 := bstep (se 2 (by rfl) ⟨1552236, by rfl⟩ : syracuseStep 4139297 = 3104473) B3104473
theorem B3107207 : Blo 1839621 3107207 := bstep (se 1 (by rfl) ⟨2330405, by rfl⟩ : syracuseStep 3107207 = 4660811) B4660811
theorem B4974995 : Blo 1839621 4974995 := bstep (se 1 (by rfl) ⟨3731246, by rfl⟩ : syracuseStep 4974995 = 7462493) B7462493
theorem B2329003 : Blo 1839621 2329003 := bstep (se 1 (by rfl) ⟨1746752, by rfl⟩ : syracuseStep 2329003 = 3493505) B3493505
theorem B53078489 : Blo 1839621 53078489 := bstep (se 2 (by rfl) ⟨19904433, by rfl⟩ : syracuseStep 53078489 = 39808867) B39808867
theorem B11192861 : Blo 1839621 11192861 := bstep (se 3 (by rfl) ⟨2098661, by rfl⟩ : syracuseStep 11192861 = 4197323) B4197323
theorem B4139639 : Blo 1839621 4139639 := bstep (se 1 (by rfl) ⟨3104729, by rfl⟩ : syracuseStep 4139639 = 6209459) B6209459
theorem B3492487 : Blo 1839621 3492487 := bstep (se 1 (by rfl) ⟨2619365, by rfl⟩ : syracuseStep 3492487 = 5238731) B5238731
theorem B2329231 : Blo 1839621 2329231 := bstep (se 1 (by rfl) ⟨1746923, by rfl⟩ : syracuseStep 2329231 = 3493847) B3493847
theorem B4139819 : Blo 1839621 4139819 := bstep (se 1 (by rfl) ⟨3104864, by rfl⟩ : syracuseStep 4139819 = 6209729) B6209729
theorem B9317267 : Blo 1839621 9317267 := bstep (se 1 (by rfl) ⟨6987950, by rfl⟩ : syracuseStep 9317267 = 13975901) B13975901
theorem B6990745 : Blo 1839621 6990745 := bstep (se 2 (by rfl) ⟨2621529, by rfl⟩ : syracuseStep 6990745 = 5243059) B5243059
theorem B6212537 : Blo 1839621 6212537 := bstep (se 2 (by rfl) ⟨2329701, by rfl⟩ : syracuseStep 6212537 = 4659403) B4659403
theorem B4140179 : Blo 1839621 4140179 := bstep (se 1 (by rfl) ⟨3105134, by rfl⟩ : syracuseStep 4140179 = 6210269) B6210269
theorem B11496649 : Blo 1839621 11496649 := bstep (se 2 (by rfl) ⟨4311243, by rfl⟩ : syracuseStep 11496649 = 8622487) B8622487
theorem B4140233 : Blo 1839621 4140233 := bstep (se 2 (by rfl) ⟨1552587, by rfl⟩ : syracuseStep 4140233 = 3105175) B3105175
theorem B6991049 : Blo 1839621 6991049 := bstep (se 2 (by rfl) ⟨2621643, by rfl⟩ : syracuseStep 6991049 = 5243287) B5243287
theorem B2657551 : Blo 1839621 2657551 := bstep (se 1 (by rfl) ⟨1993163, by rfl⟩ : syracuseStep 2657551 = 3986327) B3986327
theorem B2329975 : Blo 1839621 2329975 := bstep (se 1 (by rfl) ⟨1747481, by rfl⟩ : syracuseStep 2329975 = 3494963) B3494963
theorem B6213131 : Blo 1839621 6213131 := bstep (se 1 (by rfl) ⟨4659848, by rfl⟩ : syracuseStep 6213131 = 9319697) B9319697
theorem B20958749 : Blo 1839621 20958749 := bstep (se 3 (by rfl) ⟨3929765, by rfl⟩ : syracuseStep 20958749 = 7859531) B7859531
theorem B11791939 : Blo 1839621 11791939 := bstep (se 1 (by rfl) ⟨8843954, by rfl⟩ : syracuseStep 11791939 = 17687909) B17687909
theorem B6213239 : Blo 1839621 6213239 := bstep (se 1 (by rfl) ⟨4659929, by rfl⟩ : syracuseStep 6213239 = 9319859) B9319859
theorem B2330299 : Blo 1839621 2330299 := bstep (se 1 (by rfl) ⟨1747724, by rfl⟩ : syracuseStep 2330299 = 3495449) B3495449
theorem B22703923 : Blo 1839621 22703923 := bstep (se 1 (by rfl) ⟨17027942, by rfl⟩ : syracuseStep 22703923 = 34055885) B34055885
theorem B39800645 : Blo 1839621 39800645 := bstep (se 4 (by rfl) ⟨3731310, by rfl⟩ : syracuseStep 39800645 = 7462621) B7462621
theorem B4140935 : Blo 1839621 4140935 := bstep (se 1 (by rfl) ⟨3105701, by rfl⟩ : syracuseStep 4140935 = 6211403) B6211403
theorem B4141115 : Blo 1839621 4141115 := bstep (se 1 (by rfl) ⟨3105836, by rfl⟩ : syracuseStep 4141115 = 6211673) B6211673
theorem B6991991 : Blo 1839621 6991991 := bstep (se 1 (by rfl) ⟨5243993, by rfl⟩ : syracuseStep 6991991 = 10487987) B10487987
theorem B3731603 : Blo 1839621 3731603 := bstep (se 1 (by rfl) ⟨2798702, by rfl⟩ : syracuseStep 3731603 = 5597405) B5597405
theorem B2330795 : Blo 1839621 2330795 := bstep (se 1 (by rfl) ⟨1748096, by rfl⟩ : syracuseStep 2330795 = 3496193) B3496193
theorem B4141241 : Blo 1839621 4141241 := bstep (se 2 (by rfl) ⟨1552965, by rfl⟩ : syracuseStep 4141241 = 3105931) B3105931
theorem B2486459 : Blo 1839621 2486459 := bstep (se 1 (by rfl) ⟨1864844, by rfl⟩ : syracuseStep 2486459 = 3729689) B3729689
theorem B6213833 : Blo 1839621 6213833 := bstep (se 2 (by rfl) ⟨2330187, by rfl⟩ : syracuseStep 6213833 = 4660375) B4660375
theorem B4657409 : Blo 1839621 4657409 := bstep (se 2 (by rfl) ⟨1746528, by rfl⟩ : syracuseStep 4657409 = 3493057) B3493057
theorem B5239073 : Blo 1839621 5239073 := bstep (se 2 (by rfl) ⟨1964652, by rfl⟩ : syracuseStep 5239073 = 3929305) B3929305
theorem B3494279 : Blo 1839621 3494279 := bstep (se 1 (by rfl) ⟨2620709, by rfl⟩ : syracuseStep 3494279 = 5241419) B5241419
theorem B5239187 : Blo 1839621 5239187 := bstep (se 1 (by rfl) ⟨3929390, by rfl⟩ : syracuseStep 5239187 = 7858781) B7858781
theorem B8843705 : Blo 1839621 8843705 := bstep (se 2 (by rfl) ⟨3316389, by rfl⟩ : syracuseStep 8843705 = 6632779) B6632779
theorem B1839623 : Blo 1839621 1839623 := bstep (se 1 (by rfl) ⟨1379717, by rfl⟩ : syracuseStep 1839623 = 2759435) B2759435
theorem B1839631 : Blo 1839621 1839631 := bstep (se 1 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 1839631 = 2759447) B2759447
theorem B4141583 : Blo 1839621 4141583 := bstep (se 1 (by rfl) ⟨3106187, by rfl⟩ : syracuseStep 4141583 = 6212375) B6212375
theorem B4141601 : Blo 1839621 4141601 := bstep (se 2 (by rfl) ⟨1553100, by rfl⟩ : syracuseStep 4141601 = 3106201) B3106201
theorem B1839675 : Blo 1839621 1839675 := bstep (se 1 (by rfl) ⟨1379756, by rfl⟩ : syracuseStep 1839675 = 2759513) B2759513
theorem B7860797 : Blo 1839621 7860797 := bstep (se 3 (by rfl) ⟨1473899, by rfl⟩ : syracuseStep 7860797 = 2947799) B2947799
theorem B7565885 : Blo 1839621 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B4657783 : Blo 1839621 4657783 := bstep (se 1 (by rfl) ⟨3493337, by rfl⟩ : syracuseStep 4657783 = 6986675) B6986675
theorem B1839751 : Blo 1839621 1839751 := bstep (se 1 (by rfl) ⟨1379813, by rfl⟩ : syracuseStep 1839751 = 2759627) B2759627
theorem B1839759 : Blo 1839621 1839759 := bstep (se 1 (by rfl) ⟨1379819, by rfl⟩ : syracuseStep 1839759 = 2759639) B2759639
theorem B1839803 : Blo 1839621 1839803 := bstep (se 1 (by rfl) ⟨1379852, by rfl⟩ : syracuseStep 1839803 = 2759705) B2759705
theorem B1839879 : Blo 1839621 1839879 := bstep (se 1 (by rfl) ⟨1379909, by rfl⟩ : syracuseStep 1839879 = 2759819) B2759819
theorem B1839887 : Blo 1839621 1839887 := bstep (se 1 (by rfl) ⟨1379915, by rfl⟩ : syracuseStep 1839887 = 2759831) B2759831
theorem B9212687 : Blo 1839621 9212687 := bstep (se 1 (by rfl) ⟨6909515, by rfl⟩ : syracuseStep 9212687 = 13819031) B13819031
theorem B31462181 : Blo 1839621 31462181 := bstep (se 4 (by rfl) ⟨2949579, by rfl⟩ : syracuseStep 31462181 = 5899159) B5899159
theorem B1839931 : Blo 1839621 1839931 := bstep (se 1 (by rfl) ⟨1379948, by rfl⟩ : syracuseStep 1839931 = 2759897) B2759897
theorem B9450299 : Blo 1839621 9450299 := bstep (se 1 (by rfl) ⟨7087724, by rfl⟩ : syracuseStep 9450299 = 14175449) B14175449
theorem B4141943 : Blo 1839621 4141943 := bstep (se 1 (by rfl) ⟨3106457, by rfl⟩ : syracuseStep 4141943 = 6212915) B6212915
theorem B1840007 : Blo 1839621 1840007 := bstep (se 1 (by rfl) ⟨1380005, by rfl⟩ : syracuseStep 1840007 = 2760011) B2760011
theorem B8844167 : Blo 1839621 8844167 := bstep (se 1 (by rfl) ⟨6633125, by rfl⟩ : syracuseStep 8844167 = 13266251) B13266251
theorem B6214535 : Blo 1839621 6214535 := bstep (se 1 (by rfl) ⟨4660901, by rfl⟩ : syracuseStep 6214535 = 9321803) B9321803
theorem B1840015 : Blo 1839621 1840015 := bstep (se 1 (by rfl) ⟨1380011, by rfl⟩ : syracuseStep 1840015 = 2760023) B2760023
theorem B1840059 : Blo 1839621 1840059 := bstep (se 1 (by rfl) ⟨1380044, by rfl⟩ : syracuseStep 1840059 = 2760089) B2760089
theorem B8393681 : Blo 1839621 8393681 := bstep (se 2 (by rfl) ⟨3147630, by rfl⟩ : syracuseStep 8393681 = 6295261) B6295261
theorem B1840135 : Blo 1839621 1840135 := bstep (se 1 (by rfl) ⟨1380101, by rfl⟩ : syracuseStep 1840135 = 2760203) B2760203
theorem B1840143 : Blo 1839621 1840143 := bstep (se 1 (by rfl) ⟨1380107, by rfl⟩ : syracuseStep 1840143 = 2760215) B2760215
theorem B4658219 : Blo 1839621 4658219 := bstep (se 1 (by rfl) ⟨3493664, by rfl⟩ : syracuseStep 4658219 = 6987329) B6987329
theorem B4142123 : Blo 1839621 4142123 := bstep (se 1 (by rfl) ⟨3106592, by rfl⟩ : syracuseStep 4142123 = 6213185) B6213185
theorem B1840187 : Blo 1839621 1840187 := bstep (se 1 (by rfl) ⟨1380140, by rfl⟩ : syracuseStep 1840187 = 2760281) B2760281
theorem B1840263 : Blo 1839621 1840263 := bstep (se 1 (by rfl) ⟨1380197, by rfl⟩ : syracuseStep 1840263 = 2760395) B2760395
theorem B1840271 : Blo 1839621 1840271 := bstep (se 1 (by rfl) ⟨1380203, by rfl⟩ : syracuseStep 1840271 = 2760407) B2760407
theorem B5239961 : Blo 1839621 5239961 := bstep (se 2 (by rfl) ⟨1964985, by rfl⟩ : syracuseStep 5239961 = 3929971) B3929971
theorem B1840315 : Blo 1839621 1840315 := bstep (se 1 (by rfl) ⟨1380236, by rfl⟩ : syracuseStep 1840315 = 2760473) B2760473
theorem B6214913 : Blo 1839621 6214913 := bstep (se 2 (by rfl) ⟨2330592, by rfl⟩ : syracuseStep 6214913 = 4661185) B4661185
theorem B1840391 : Blo 1839621 1840391 := bstep (se 1 (by rfl) ⟨1380293, by rfl⟩ : syracuseStep 1840391 = 2760587) B2760587
theorem B1840399 : Blo 1839621 1840399 := bstep (se 1 (by rfl) ⟨1380299, by rfl⟩ : syracuseStep 1840399 = 2760599) B2760599
theorem B1840443 : Blo 1839621 1840443 := bstep (se 1 (by rfl) ⟨1380332, by rfl⟩ : syracuseStep 1840443 = 2760665) B2760665
theorem B53089667 : Blo 1839621 53089667 := bstep (se 1 (by rfl) ⟨39817250, by rfl⟩ : syracuseStep 53089667 = 79634501) B79634501
theorem B1840519 : Blo 1839621 1840519 := bstep (se 1 (by rfl) ⟨1380389, by rfl⟩ : syracuseStep 1840519 = 2760779) B2760779
theorem B1840527 : Blo 1839621 1840527 := bstep (se 1 (by rfl) ⟨1380395, by rfl⟩ : syracuseStep 1840527 = 2760791) B2760791
theorem B4142483 : Blo 1839621 4142483 := bstep (se 1 (by rfl) ⟨3106862, by rfl⟩ : syracuseStep 4142483 = 6213725) B6213725
theorem B8394137 : Blo 1839621 8394137 := bstep (se 2 (by rfl) ⟨3147801, by rfl⟩ : syracuseStep 8394137 = 6295603) B6295603
theorem B9442745 : Blo 1839621 9442745 := bstep (se 2 (by rfl) ⟨3541029, by rfl⟩ : syracuseStep 9442745 = 7082059) B7082059
theorem B1840571 : Blo 1839621 1840571 := bstep (se 1 (by rfl) ⟨1380428, by rfl⟩ : syracuseStep 1840571 = 2760857) B2760857
theorem B4142537 : Blo 1839621 4142537 := bstep (se 2 (by rfl) ⟨1553451, by rfl⟩ : syracuseStep 4142537 = 3106903) B3106903
theorem B1840647 : Blo 1839621 1840647 := bstep (se 1 (by rfl) ⟨1380485, by rfl⟩ : syracuseStep 1840647 = 2760971) B2760971
theorem B3315215 : Blo 1839621 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B2070031 : Blo 1839621 2070031 := bstep (se 1 (by rfl) ⟨1552523, by rfl⟩ : syracuseStep 2070031 = 3105047) B3105047
theorem B1840655 : Blo 1839621 1840655 := bstep (se 1 (by rfl) ⟨1380491, by rfl⟩ : syracuseStep 1840655 = 2760983) B2760983
theorem B4724239 : Blo 1839621 4724239 := bstep (se 1 (by rfl) ⟨3543179, by rfl⟩ : syracuseStep 4724239 = 7086359) B7086359
theorem B2242091 : Blo 1839621 2242091 := bstep (se 1 (by rfl) ⟨1681568, by rfl⟩ : syracuseStep 2242091 = 3363137) B3363137
theorem B1840699 : Blo 1839621 1840699 := bstep (se 1 (by rfl) ⟨1380524, by rfl⟩ : syracuseStep 1840699 = 2761049) B2761049
theorem B23582285 : Blo 1839621 23582285 := bstep (se 3 (by rfl) ⟨4421678, by rfl⟩ : syracuseStep 23582285 = 8843357) B8843357
theorem B1840775 : Blo 1839621 1840775 := bstep (se 1 (by rfl) ⟨1380581, by rfl⟩ : syracuseStep 1840775 = 2761163) B2761163
theorem B1840783 : Blo 1839621 1840783 := bstep (se 1 (by rfl) ⟨1380587, by rfl⟩ : syracuseStep 1840783 = 2761175) B2761175
theorem B1840827 : Blo 1839621 1840827 := bstep (se 1 (by rfl) ⟨1380620, by rfl⟩ : syracuseStep 1840827 = 2761241) B2761241
theorem B2946761 : Blo 1839621 2946761 := bstep (se 2 (by rfl) ⟨1105035, by rfl⟩ : syracuseStep 2946761 = 2210071) B2210071
theorem B1840903 : Blo 1839621 1840903 := bstep (se 1 (by rfl) ⟨1380677, by rfl⟩ : syracuseStep 1840903 = 2761355) B2761355
theorem B1840911 : Blo 1839621 1840911 := bstep (se 1 (by rfl) ⟨1380683, by rfl⟩ : syracuseStep 1840911 = 2761367) B2761367
theorem B1840955 : Blo 1839621 1840955 := bstep (se 1 (by rfl) ⟨1380716, by rfl⟩ : syracuseStep 1840955 = 2761433) B2761433
theorem B145446731 : Blo 1839621 145446731 := bstep (se 1 (by rfl) ⟨109085048, by rfl⟩ : syracuseStep 145446731 = 218170097) B218170097
theorem B4659059 : Blo 1839621 4659059 := bstep (se 1 (by rfl) ⟨3494294, by rfl⟩ : syracuseStep 4659059 = 6988589) B6988589
theorem B4659079 : Blo 1839621 4659079 := bstep (se 1 (by rfl) ⟨3494309, by rfl⟩ : syracuseStep 4659079 = 6988619) B6988619
theorem B1841031 : Blo 1839621 1841031 := bstep (se 1 (by rfl) ⟨1380773, by rfl⟩ : syracuseStep 1841031 = 2761547) B2761547
theorem B1841039 : Blo 1839621 1841039 := bstep (se 1 (by rfl) ⟨1380779, by rfl⟩ : syracuseStep 1841039 = 2761559) B2761559
theorem B9320345 : Blo 1839621 9320345 := bstep (se 2 (by rfl) ⟨3495129, by rfl⟩ : syracuseStep 9320345 = 6990259) B6990259
theorem B1841083 : Blo 1839621 1841083 := bstep (se 1 (by rfl) ⟨1380812, by rfl⟩ : syracuseStep 1841083 = 2761625) B2761625
theorem B2070535 : Blo 1839621 2070535 := bstep (se 1 (by rfl) ⟨1552901, by rfl⟩ : syracuseStep 2070535 = 3105803) B3105803
theorem B1841159 : Blo 1839621 1841159 := bstep (se 1 (by rfl) ⟨1380869, by rfl⟩ : syracuseStep 1841159 = 2761739) B2761739
theorem B1841167 : Blo 1839621 1841167 := bstep (se 1 (by rfl) ⟨1380875, by rfl⟩ : syracuseStep 1841167 = 2761751) B2761751
theorem B1841211 : Blo 1839621 1841211 := bstep (se 1 (by rfl) ⟨1380908, by rfl⟩ : syracuseStep 1841211 = 2761817) B2761817
theorem B5109895 : Blo 1839621 5109895 := bstep (se 1 (by rfl) ⟨3832421, by rfl⟩ : syracuseStep 5109895 = 7664843) B7664843
theorem B1841287 : Blo 1839621 1841287 := bstep (se 1 (by rfl) ⟨1380965, by rfl⟩ : syracuseStep 1841287 = 2761931) B2761931
theorem B4143239 : Blo 1839621 4143239 := bstep (se 1 (by rfl) ⟨3107429, by rfl⟩ : syracuseStep 4143239 = 6214859) B6214859
theorem B1841295 : Blo 1839621 1841295 := bstep (se 1 (by rfl) ⟨1380971, by rfl⟩ : syracuseStep 1841295 = 2761943) B2761943
theorem B4659353 : Blo 1839621 4659353 := bstep (se 2 (by rfl) ⟨1747257, by rfl⟩ : syracuseStep 4659353 = 3494515) B3494515
theorem B2070715 : Blo 1839621 2070715 := bstep (se 1 (by rfl) ⟨1553036, by rfl⟩ : syracuseStep 2070715 = 3106073) B3106073
theorem B1841339 : Blo 1839621 1841339 := bstep (se 1 (by rfl) ⟨1381004, by rfl⟩ : syracuseStep 1841339 = 2762009) B2762009
theorem B7461065 : Blo 1839621 7461065 := bstep (se 2 (by rfl) ⟨2797899, by rfl⟩ : syracuseStep 7461065 = 5595799) B5595799
theorem B1841415 : Blo 1839621 1841415 := bstep (se 1 (by rfl) ⟨1381061, by rfl⟩ : syracuseStep 1841415 = 2762123) B2762123
theorem B7567631 : Blo 1839621 7567631 := bstep (se 1 (by rfl) ⟨5675723, by rfl⟩ : syracuseStep 7567631 = 11351447) B11351447
theorem B1841423 : Blo 1839621 1841423 := bstep (se 1 (by rfl) ⟨1381067, by rfl⟩ : syracuseStep 1841423 = 2762135) B2762135
theorem B2619707 : Blo 1839621 2619707 := bstep (se 1 (by rfl) ⟨1964780, by rfl⟩ : syracuseStep 2619707 = 3929561) B3929561
theorem B4659515 : Blo 1839621 4659515 := bstep (se 1 (by rfl) ⟨3494636, by rfl⟩ : syracuseStep 4659515 = 6989273) B6989273
theorem B1841467 : Blo 1839621 1841467 := bstep (se 1 (by rfl) ⟨1381100, by rfl⟩ : syracuseStep 1841467 = 2762201) B2762201
theorem B4143419 : Blo 1839621 4143419 := bstep (se 1 (by rfl) ⟨3107564, by rfl⟩ : syracuseStep 4143419 = 6215129) B6215129
theorem B2210167 : Blo 1839621 2210167 := bstep (se 1 (by rfl) ⟨1657625, by rfl⟩ : syracuseStep 2210167 = 3315251) B3315251
theorem B1841543 : Blo 1839621 1841543 := bstep (se 1 (by rfl) ⟨1381157, by rfl⟩ : syracuseStep 1841543 = 2762315) B2762315
theorem B1841551 : Blo 1839621 1841551 := bstep (se 1 (by rfl) ⟨1381163, by rfl⟩ : syracuseStep 1841551 = 2762327) B2762327
theorem B10484113 : Blo 1839621 10484113 := bstep (se 2 (by rfl) ⟨3931542, by rfl⟩ : syracuseStep 10484113 = 7863085) B7863085
theorem B2488747 : Blo 1839621 2488747 := bstep (se 1 (by rfl) ⟨1866560, by rfl⟩ : syracuseStep 2488747 = 3733121) B3733121
theorem B4143545 : Blo 1839621 4143545 := bstep (se 2 (by rfl) ⟨1553829, by rfl⟩ : syracuseStep 4143545 = 3107659) B3107659
theorem B1841595 : Blo 1839621 1841595 := bstep (se 1 (by rfl) ⟨1381196, by rfl⟩ : syracuseStep 1841595 = 2762393) B2762393
theorem B2210311 : Blo 1839621 2210311 := bstep (se 1 (by rfl) ⟨1657733, by rfl⟩ : syracuseStep 2210311 = 3315467) B3315467
theorem B4659727 : Blo 1839621 4659727 := bstep (se 1 (by rfl) ⟨3494795, by rfl⟩ : syracuseStep 4659727 = 6989591) B6989591
theorem B2071183 : Blo 1839621 2071183 := bstep (se 1 (by rfl) ⟨1553387, by rfl⟩ : syracuseStep 2071183 = 3106775) B3106775
theorem B5241601 : Blo 1839621 5241601 := bstep (se 2 (by rfl) ⟨1965600, by rfl⟩ : syracuseStep 5241601 = 3931201) B3931201
theorem B4660001 : Blo 1839621 4660001 := bstep (se 2 (by rfl) ⟨1747500, by rfl⟩ : syracuseStep 4660001 = 3495001) B3495001
theorem B2759483 : Blo 1839621 2759483 := bstep (se 1 (by rfl) ⟨2069612, by rfl⟩ : syracuseStep 2759483 = 4139225) B4139225
theorem B7863155 : Blo 1839621 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B2759543 : Blo 1839621 2759543 := bstep (se 1 (by rfl) ⟨2069657, by rfl⟩ : syracuseStep 2759543 = 4139315) B4139315
theorem B2759567 : Blo 1839621 2759567 := bstep (se 1 (by rfl) ⟨2069675, by rfl⟩ : syracuseStep 2759567 = 4139351) B4139351
theorem B2759609 : Blo 1839621 2759609 := bstep (se 2 (by rfl) ⟨1034853, by rfl⟩ : syracuseStep 2759609 = 2069707) B2069707
theorem B2620345 : Blo 1839621 2620345 := bstep (se 2 (by rfl) ⟨982629, by rfl⟩ : syracuseStep 2620345 = 1965259) B1965259
theorem B22395851 : Blo 1839621 22395851 := bstep (se 1 (by rfl) ⟨16796888, by rfl⟩ : syracuseStep 22395851 = 33593777) B33593777
theorem B2759687 : Blo 1839621 2759687 := bstep (se 1 (by rfl) ⟨2069765, by rfl⟩ : syracuseStep 2759687 = 4139531) B4139531
theorem B1965071 : Blo 1839621 1965071 := bstep (se 1 (by rfl) ⟨1473803, by rfl⟩ : syracuseStep 1965071 = 2947607) B2947607
theorem B2759723 : Blo 1839621 2759723 := bstep (se 1 (by rfl) ⟨2069792, by rfl⟩ : syracuseStep 2759723 = 4139585) B4139585
theorem B2620459 : Blo 1839621 2620459 := bstep (se 1 (by rfl) ⟨1965344, by rfl⟩ : syracuseStep 2620459 = 3930689) B3930689
theorem B2759753 : Blo 1839621 2759753 := bstep (se 2 (by rfl) ⟨1034907, by rfl⟩ : syracuseStep 2759753 = 2069815) B2069815
theorem B4422775 : Blo 1839621 4422775 := bstep (se 1 (by rfl) ⟨3317081, by rfl⟩ : syracuseStep 4422775 = 6634163) B6634163
theorem B2071687 : Blo 1839621 2071687 := bstep (se 1 (by rfl) ⟨1553765, by rfl⟩ : syracuseStep 2071687 = 3107531) B3107531
theorem B2759867 : Blo 1839621 2759867 := bstep (se 1 (by rfl) ⟨2069900, by rfl⟩ : syracuseStep 2759867 = 4139801) B4139801
theorem B2759927 : Blo 1839621 2759927 := bstep (se 1 (by rfl) ⟨2069945, by rfl⟩ : syracuseStep 2759927 = 4139891) B4139891
theorem B2759951 : Blo 1839621 2759951 := bstep (se 1 (by rfl) ⟨2069963, by rfl⟩ : syracuseStep 2759951 = 4139927) B4139927
theorem B2620687 : Blo 1839621 2620687 := bstep (se 1 (by rfl) ⟨1965515, by rfl⟩ : syracuseStep 2620687 = 3931031) B3931031
theorem B2948395 : Blo 1839621 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B2759993 : Blo 1839621 2759993 := bstep (se 2 (by rfl) ⟨1034997, by rfl⟩ : syracuseStep 2759993 = 2069995) B2069995
theorem B5242171 : Blo 1839621 5242171 := bstep (se 1 (by rfl) ⟨3931628, by rfl⟩ : syracuseStep 5242171 = 7863257) B7863257
theorem B9952627 : Blo 1839621 9952627 := bstep (se 1 (by rfl) ⟨7464470, by rfl⟩ : syracuseStep 9952627 = 14928941) B14928941
theorem B2760071 : Blo 1839621 2760071 := bstep (se 1 (by rfl) ⟨2070053, by rfl⟩ : syracuseStep 2760071 = 4140107) B4140107
theorem B13974929 : Blo 1839621 13974929 := bstep (se 2 (by rfl) ⟨5240598, by rfl⟩ : syracuseStep 13974929 = 10481197) B10481197
theorem B6987161 : Blo 1839621 6987161 := bstep (se 2 (by rfl) ⟨2620185, by rfl⟩ : syracuseStep 6987161 = 5240371) B5240371
theorem B2760107 : Blo 1839621 2760107 := bstep (se 1 (by rfl) ⟨2070080, by rfl⟩ : syracuseStep 2760107 = 4140161) B4140161
theorem B2760137 : Blo 1839621 2760137 := bstep (se 2 (by rfl) ⟨1035051, by rfl⟩ : syracuseStep 2760137 = 2070103) B2070103
theorem B2760251 : Blo 1839621 2760251 := bstep (se 1 (by rfl) ⟨2070188, by rfl⟩ : syracuseStep 2760251 = 4140377) B4140377
theorem B2760311 : Blo 1839621 2760311 := bstep (se 1 (by rfl) ⟨2070233, by rfl⟩ : syracuseStep 2760311 = 4140467) B4140467
theorem B2760335 : Blo 1839621 2760335 := bstep (se 1 (by rfl) ⟨2070251, by rfl⟩ : syracuseStep 2760335 = 4140503) B4140503
theorem B2760377 : Blo 1839621 2760377 := bstep (se 2 (by rfl) ⟨1035141, by rfl⟩ : syracuseStep 2760377 = 2070283) B2070283
theorem B5897929 : Blo 1839621 5897929 := bstep (se 2 (by rfl) ⟨2211723, by rfl⟩ : syracuseStep 5897929 = 4423447) B4423447
theorem B15728357 : Blo 1839621 15728357 := bstep (se 4 (by rfl) ⟨1474533, by rfl⟩ : syracuseStep 15728357 = 2949067) B2949067
theorem B2760455 : Blo 1839621 2760455 := bstep (se 1 (by rfl) ⟨2070341, by rfl⟩ : syracuseStep 2760455 = 4140683) B4140683
theorem B4661003 : Blo 1839621 4661003 := bstep (se 1 (by rfl) ⟨3495752, by rfl⟩ : syracuseStep 4661003 = 6991505) B6991505
theorem B3104527 : Blo 1839621 3104527 := bstep (se 1 (by rfl) ⟨2328395, by rfl⟩ : syracuseStep 3104527 = 4656791) B4656791
theorem B3931919 : Blo 1839621 3931919 := bstep (se 1 (by rfl) ⟨2948939, by rfl⟩ : syracuseStep 3931919 = 5897879) B5897879
theorem B10477349 : Blo 1839621 10477349 := bstep (se 4 (by rfl) ⟨982251, by rfl⟩ : syracuseStep 10477349 = 1964503) B1964503
theorem B2760491 : Blo 1839621 2760491 := bstep (se 1 (by rfl) ⟨2070368, by rfl⟩ : syracuseStep 2760491 = 4140737) B4140737
theorem B20963123 : Blo 1839621 20963123 := bstep (se 1 (by rfl) ⟨15722342, by rfl⟩ : syracuseStep 20963123 = 31444685) B31444685
theorem B2760521 : Blo 1839621 2760521 := bstep (se 2 (by rfl) ⟨1035195, by rfl⟩ : syracuseStep 2760521 = 2070391) B2070391
theorem B12590963 : Blo 1839621 12590963 := bstep (se 1 (by rfl) ⟨9443222, by rfl⟩ : syracuseStep 12590963 = 18886445) B18886445
theorem B3932039 : Blo 1839621 3932039 := bstep (se 1 (by rfl) ⟨2949029, by rfl⟩ : syracuseStep 3932039 = 5898059) B5898059
theorem B2875279 : Blo 1839621 2875279 := bstep (se 1 (by rfl) ⟨2156459, by rfl⟩ : syracuseStep 2875279 = 4312919) B4312919
theorem B2760635 : Blo 1839621 2760635 := bstep (se 1 (by rfl) ⟨2070476, by rfl⟩ : syracuseStep 2760635 = 4140953) B4140953
theorem B11198411 : Blo 1839621 11198411 := bstep (se 1 (by rfl) ⟨8398808, by rfl⟩ : syracuseStep 11198411 = 16797617) B16797617
theorem B2760695 : Blo 1839621 2760695 := bstep (se 1 (by rfl) ⟨2070521, by rfl⟩ : syracuseStep 2760695 = 4141043) B4141043
theorem B3104777 : Blo 1839621 3104777 := bstep (se 2 (by rfl) ⟨1164291, by rfl⟩ : syracuseStep 3104777 = 2328583) B2328583
theorem B2760713 : Blo 1839621 2760713 := bstep (se 2 (by rfl) ⟨1035267, by rfl⟩ : syracuseStep 2760713 = 2070535) B2070535
theorem B11190287 : Blo 1839621 11190287 := bstep (se 1 (by rfl) ⟨8392715, by rfl⟩ : syracuseStep 11190287 = 16785431) B16785431
theorem B11788325 : Blo 1839621 11788325 := bstep (se 4 (by rfl) ⟨1105155, by rfl⟩ : syracuseStep 11788325 = 2210311) B2210311
theorem B2760743 : Blo 1839621 2760743 := bstep (se 1 (by rfl) ⟨2070557, by rfl⟩ : syracuseStep 2760743 = 4141115) B4141115
theorem B2621479 : Blo 1839621 2621479 := bstep (se 1 (by rfl) ⟨1966109, by rfl⟩ : syracuseStep 2621479 = 3932219) B3932219
theorem B4661327 : Blo 1839621 4661327 := bstep (se 1 (by rfl) ⟨3495995, by rfl⟩ : syracuseStep 4661327 = 6991991) B6991991
theorem B2760827 : Blo 1839621 2760827 := bstep (se 1 (by rfl) ⟨2070620, by rfl⟩ : syracuseStep 2760827 = 4141241) B4141241
theorem B3104939 : Blo 1839621 3104939 := bstep (se 1 (by rfl) ⟨2328704, by rfl⟩ : syracuseStep 3104939 = 4657409) B4657409
theorem B6209783 : Blo 1839621 6209783 := bstep (se 1 (by rfl) ⟨4657337, by rfl⟩ : syracuseStep 6209783 = 9314675) B9314675
theorem B2760953 : Blo 1839621 2760953 := bstep (se 2 (by rfl) ⟨1035357, by rfl⟩ : syracuseStep 2760953 = 2070715) B2070715
theorem B2761055 : Blo 1839621 2761055 := bstep (se 1 (by rfl) ⟨2070791, by rfl⟩ : syracuseStep 2761055 = 4141583) B4141583
theorem B2761067 : Blo 1839621 2761067 := bstep (se 1 (by rfl) ⟨2070800, by rfl⟩ : syracuseStep 2761067 = 4141601) B4141601
theorem B2621803 : Blo 1839621 2621803 := bstep (se 1 (by rfl) ⟨1966352, by rfl⟩ : syracuseStep 2621803 = 3932705) B3932705
theorem B6300199 : Blo 1839621 6300199 := bstep (se 1 (by rfl) ⟨4725149, by rfl⟩ : syracuseStep 6300199 = 9450299) B9450299
theorem B3105337 : Blo 1839621 3105337 := bstep (se 2 (by rfl) ⟨1164501, by rfl⟩ : syracuseStep 3105337 = 2329003) B2329003
theorem B3318329 : Blo 1839621 3318329 := bstep (se 2 (by rfl) ⟨1244373, by rfl⟩ : syracuseStep 3318329 = 2488747) B2488747
theorem B6210107 : Blo 1839621 6210107 := bstep (se 1 (by rfl) ⟨4657580, by rfl⟩ : syracuseStep 6210107 = 9315161) B9315161
theorem B2761295 : Blo 1839621 2761295 := bstep (se 1 (by rfl) ⟨2070971, by rfl⟩ : syracuseStep 2761295 = 4141943) B4141943
theorem B5595787 : Blo 1839621 5595787 := bstep (se 1 (by rfl) ⟨4196840, by rfl⟩ : syracuseStep 5595787 = 8393681) B8393681
theorem B3105479 : Blo 1839621 3105479 := bstep (se 1 (by rfl) ⟨2329109, by rfl⟩ : syracuseStep 3105479 = 4658219) B4658219
theorem B2761415 : Blo 1839621 2761415 := bstep (se 1 (by rfl) ⟨2071061, by rfl⟩ : syracuseStep 2761415 = 4142123) B4142123
theorem B6210377 : Blo 1839621 6210377 := bstep (se 2 (by rfl) ⟨2328891, by rfl⟩ : syracuseStep 6210377 = 4657783) B4657783
theorem B3105641 : Blo 1839621 3105641 := bstep (se 2 (by rfl) ⟨1164615, by rfl⟩ : syracuseStep 3105641 = 2329231) B2329231
theorem B2761577 : Blo 1839621 2761577 := bstep (se 2 (by rfl) ⟨1035591, by rfl⟩ : syracuseStep 2761577 = 2071183) B2071183
theorem B2761655 : Blo 1839621 2761655 := bstep (se 1 (by rfl) ⟨2071241, by rfl⟩ : syracuseStep 2761655 = 4142483) B4142483
theorem B5596091 : Blo 1839621 5596091 := bstep (se 1 (by rfl) ⟨4197068, by rfl⟩ : syracuseStep 5596091 = 8394137) B8394137
theorem B2761691 : Blo 1839621 2761691 := bstep (se 1 (by rfl) ⟨2071268, by rfl⟩ : syracuseStep 2761691 = 4142537) B4142537
theorem B6988801 : Blo 1839621 6988801 := bstep (se 2 (by rfl) ⟨2620800, by rfl⟩ : syracuseStep 6988801 = 5241601) B5241601
theorem B15721523 : Blo 1839621 15721523 := bstep (se 1 (by rfl) ⟨11791142, by rfl⟩ : syracuseStep 15721523 = 23582285) B23582285
theorem B3106039 : Blo 1839621 3106039 := bstep (se 1 (by rfl) ⟨2329529, by rfl⟩ : syracuseStep 3106039 = 4659059) B4659059
theorem B8840573 : Blo 1839621 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B2762159 : Blo 1839621 2762159 := bstep (se 1 (by rfl) ⟨2071619, by rfl⟩ : syracuseStep 2762159 = 4143239) B4143239
theorem B3106235 : Blo 1839621 3106235 := bstep (se 1 (by rfl) ⟨2329676, by rfl⟩ : syracuseStep 3106235 = 4659353) B4659353
theorem B4974043 : Blo 1839621 4974043 := bstep (se 1 (by rfl) ⟨3730532, by rfl⟩ : syracuseStep 4974043 = 7461065) B7461065
theorem B7865819 : Blo 1839621 7865819 := bstep (se 1 (by rfl) ⟨5899364, by rfl⟩ : syracuseStep 7865819 = 11798729) B11798729
theorem B2762249 : Blo 1839621 2762249 := bstep (se 2 (by rfl) ⟨1035843, by rfl⟩ : syracuseStep 2762249 = 2071687) B2071687
theorem B3106343 : Blo 1839621 3106343 := bstep (se 1 (by rfl) ⟨2329757, by rfl⟩ : syracuseStep 3106343 = 4659515) B4659515
theorem B2762279 : Blo 1839621 2762279 := bstep (se 1 (by rfl) ⟨2071709, by rfl⟩ : syracuseStep 2762279 = 4143419) B4143419
theorem B15328865 : Blo 1839621 15328865 := bstep (se 2 (by rfl) ⟨5748324, by rfl⟩ : syracuseStep 15328865 = 11496649) B11496649
theorem B2762363 : Blo 1839621 2762363 := bstep (se 1 (by rfl) ⟨2071772, by rfl⟩ : syracuseStep 2762363 = 4143545) B4143545
theorem B6989561 : Blo 1839621 6989561 := bstep (se 2 (by rfl) ⟨2621085, by rfl⟩ : syracuseStep 6989561 = 5242171) B5242171
theorem B3106633 : Blo 1839621 3106633 := bstep (se 2 (by rfl) ⟨1164987, by rfl⟩ : syracuseStep 3106633 = 2329975) B2329975
theorem B3106667 : Blo 1839621 3106667 := bstep (se 1 (by rfl) ⟨2330000, by rfl⟩ : syracuseStep 3106667 = 4660001) B4660001
theorem B6211511 : Blo 1839621 6211511 := bstep (se 1 (by rfl) ⟨4658633, by rfl⟩ : syracuseStep 6211511 = 9317267) B9317267
theorem B15722585 : Blo 1839621 15722585 := bstep (se 2 (by rfl) ⟨5895969, by rfl⟩ : syracuseStep 15722585 = 11791939) B11791939
theorem B3107065 : Blo 1839621 3107065 := bstep (se 2 (by rfl) ⟨1165149, by rfl⟩ : syracuseStep 3107065 = 2330299) B2330299
theorem B9316619 : Blo 1839621 9316619 := bstep (se 1 (by rfl) ⟨6987464, by rfl⟩ : syracuseStep 9316619 = 13974929) B13974929
theorem B4139369 : Blo 1839621 4139369 := bstep (se 2 (by rfl) ⟨1552263, by rfl⟩ : syracuseStep 4139369 = 3104527) B3104527
theorem B30271897 : Blo 1839621 30271897 := bstep (se 2 (by rfl) ⟨11351961, by rfl⟩ : syracuseStep 30271897 = 22703923) B22703923
theorem B3107335 : Blo 1839621 3107335 := bstep (se 1 (by rfl) ⟨2330501, by rfl⟩ : syracuseStep 3107335 = 4661003) B4661003
theorem B6212105 : Blo 1839621 6212105 := bstep (se 2 (by rfl) ⟨2329539, by rfl⟩ : syracuseStep 6212105 = 4659079) B4659079
theorem B17697325 : Blo 1839621 17697325 := bstep (se 3 (by rfl) ⟨3318248, by rfl⟩ : syracuseStep 17697325 = 6636497) B6636497
theorem B7465607 : Blo 1839621 7465607 := bstep (se 1 (by rfl) ⟨5599205, by rfl⟩ : syracuseStep 7465607 = 11198411) B11198411
theorem B3492715 : Blo 1839621 3492715 := bstep (se 1 (by rfl) ⟨2619536, by rfl⟩ : syracuseStep 3492715 = 5239073) B5239073
theorem B3492791 : Blo 1839621 3492791 := bstep (se 1 (by rfl) ⟨2619593, by rfl⟩ : syracuseStep 3492791 = 5239187) B5239187
theorem B4139963 : Blo 1839621 4139963 := bstep (se 1 (by rfl) ⟨3104972, by rfl⟩ : syracuseStep 4139963 = 6209945) B6209945
theorem B4140089 : Blo 1839621 4140089 := bstep (se 2 (by rfl) ⟨1552533, by rfl⟩ : syracuseStep 4140089 = 3105067) B3105067
theorem B6630557 : Blo 1839621 6630557 := bstep (se 3 (by rfl) ⟨1243229, by rfl⟩ : syracuseStep 6630557 = 2486459) B2486459
theorem B6991019 : Blo 1839621 6991019 := bstep (se 1 (by rfl) ⟨5243264, by rfl⟩ : syracuseStep 6991019 = 10486529) B10486529
theorem B13978817 : Blo 1839621 13978817 := bstep (se 2 (by rfl) ⟨5242056, by rfl⟩ : syracuseStep 13978817 = 10484113) B10484113
theorem B20974787 : Blo 1839621 20974787 := bstep (se 1 (by rfl) ⟨15731090, by rfl⟩ : syracuseStep 20974787 = 31462181) B31462181
theorem B3730679 : Blo 1839621 3730679 := bstep (se 1 (by rfl) ⟨2798009, by rfl⟩ : syracuseStep 3730679 = 5596019) B5596019
theorem B6212969 : Blo 1839621 6212969 := bstep (se 2 (by rfl) ⟨2329863, by rfl⟩ : syracuseStep 6212969 = 4659727) B4659727
theorem B4140431 : Blo 1839621 4140431 := bstep (se 1 (by rfl) ⟨3105323, by rfl⟩ : syracuseStep 4140431 = 6210647) B6210647
theorem B59731343 : Blo 1839621 59731343 := bstep (se 1 (by rfl) ⟨44798507, by rfl⟩ : syracuseStep 59731343 = 89597015) B89597015
theorem B3493307 : Blo 1839621 3493307 := bstep (se 1 (by rfl) ⟨2619980, by rfl⟩ : syracuseStep 3493307 = 5239961) B5239961
theorem B10366427 : Blo 1839621 10366427 := bstep (se 1 (by rfl) ⟨7774820, by rfl⟩ : syracuseStep 10366427 = 15549641) B15549641
theorem B4656649 : Blo 1839621 4656649 := bstep (se 2 (by rfl) ⟨1746243, by rfl⟩ : syracuseStep 4656649 = 3492487) B3492487
theorem B35393111 : Blo 1839621 35393111 := bstep (se 1 (by rfl) ⟨26544833, by rfl⟩ : syracuseStep 35393111 = 53089667) B53089667
theorem B13971041 : Blo 1839621 13971041 := bstep (se 2 (by rfl) ⟨5239140, by rfl⟩ : syracuseStep 13971041 = 10478281) B10478281
theorem B6295163 : Blo 1839621 6295163 := bstep (se 1 (by rfl) ⟨4721372, by rfl⟩ : syracuseStep 6295163 = 9442745) B9442745
theorem B9318077 : Blo 1839621 9318077 := bstep (se 3 (by rfl) ⟨1747139, by rfl⟩ : syracuseStep 9318077 = 3494279) B3494279
theorem B6631121 : Blo 1839621 6631121 := bstep (se 2 (by rfl) ⟨2486670, by rfl⟩ : syracuseStep 6631121 = 4973341) B4973341
theorem B4140755 : Blo 1839621 4140755 := bstep (se 1 (by rfl) ⟨3105566, by rfl⟩ : syracuseStep 4140755 = 6211133) B6211133
theorem B5893931 : Blo 1839621 5893931 := bstep (se 1 (by rfl) ⟨4420448, by rfl⟩ : syracuseStep 5893931 = 8840897) B8840897
theorem B9318239 : Blo 1839621 9318239 := bstep (se 1 (by rfl) ⟨6988679, by rfl⟩ : syracuseStep 9318239 = 13977359) B13977359
theorem B96964487 : Blo 1839621 96964487 := bstep (se 1 (by rfl) ⟨72723365, by rfl⟩ : syracuseStep 96964487 = 145446731) B145446731
theorem B3493793 : Blo 1839621 3493793 := bstep (se 2 (by rfl) ⟨1310172, by rfl⟩ : syracuseStep 3493793 = 2620345) B2620345
theorem B6213563 : Blo 1839621 6213563 := bstep (se 1 (by rfl) ⟨4660172, by rfl⟩ : syracuseStep 6213563 = 9320345) B9320345
theorem B3493945 : Blo 1839621 3493945 := bstep (se 2 (by rfl) ⟨1310229, by rfl⟩ : syracuseStep 3493945 = 2620459) B2620459
theorem B29847629 : Blo 1839621 29847629 := bstep (se 3 (by rfl) ⟨5596430, by rfl⟩ : syracuseStep 29847629 = 11192861) B11192861
theorem B35385659 : Blo 1839621 35385659 := bstep (se 1 (by rfl) ⟨26539244, by rfl⟩ : syracuseStep 35385659 = 53078489) B53078489
theorem B6992189 : Blo 1839621 6992189 := bstep (se 3 (by rfl) ⟨1311035, by rfl⟩ : syracuseStep 6992189 = 2622071) B2622071
theorem B3494249 : Blo 1839621 3494249 := bstep (se 2 (by rfl) ⟨1310343, by rfl⟩ : syracuseStep 3494249 = 2620687) B2620687
theorem B1839655 : Blo 1839621 1839655 := bstep (se 1 (by rfl) ⟨1379741, by rfl⟩ : syracuseStep 1839655 = 2759483) B2759483
theorem B1839695 : Blo 1839621 1839695 := bstep (se 1 (by rfl) ⟨1379771, by rfl⟩ : syracuseStep 1839695 = 2759543) B2759543
theorem B1839711 : Blo 1839621 1839711 := bstep (se 1 (by rfl) ⟨1379783, by rfl⟩ : syracuseStep 1839711 = 2759567) B2759567
theorem B20976245 : Blo 1839621 20976245 := bstep (se 5 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 20976245 = 1966523) B1966523
theorem B1839739 : Blo 1839621 1839739 := bstep (se 1 (by rfl) ⟨1379804, by rfl⟩ : syracuseStep 1839739 = 2759609) B2759609
theorem B4141691 : Blo 1839621 4141691 := bstep (se 1 (by rfl) ⟨3106268, by rfl⟩ : syracuseStep 4141691 = 6212537) B6212537
theorem B14930567 : Blo 1839621 14930567 := bstep (se 1 (by rfl) ⟨11197925, by rfl⟩ : syracuseStep 14930567 = 22395851) B22395851
theorem B1839791 : Blo 1839621 1839791 := bstep (se 1 (by rfl) ⟨1379843, by rfl⟩ : syracuseStep 1839791 = 2759687) B2759687
theorem B1839815 : Blo 1839621 1839815 := bstep (se 1 (by rfl) ⟨1379861, by rfl⟩ : syracuseStep 1839815 = 2759723) B2759723
theorem B1839835 : Blo 1839621 1839835 := bstep (se 1 (by rfl) ⟨1379876, by rfl⟩ : syracuseStep 1839835 = 2759753) B2759753
theorem B4141817 : Blo 1839621 4141817 := bstep (se 2 (by rfl) ⟨1553181, by rfl⟩ : syracuseStep 4141817 = 3106363) B3106363
theorem B1839911 : Blo 1839621 1839911 := bstep (se 1 (by rfl) ⟨1379933, by rfl⟩ : syracuseStep 1839911 = 2759867) B2759867
theorem B1839951 : Blo 1839621 1839951 := bstep (se 1 (by rfl) ⟨1379963, by rfl⟩ : syracuseStep 1839951 = 2759927) B2759927
theorem B1839967 : Blo 1839621 1839967 := bstep (se 1 (by rfl) ⟨1379975, by rfl⟩ : syracuseStep 1839967 = 2759951) B2759951
theorem B1839995 : Blo 1839621 1839995 := bstep (se 1 (by rfl) ⟨1379996, by rfl⟩ : syracuseStep 1839995 = 2759993) B2759993
theorem B1840047 : Blo 1839621 1840047 := bstep (se 1 (by rfl) ⟨1380035, by rfl⟩ : syracuseStep 1840047 = 2760071) B2760071
theorem B4658107 : Blo 1839621 4658107 := bstep (se 1 (by rfl) ⟨3493580, by rfl⟩ : syracuseStep 4658107 = 6987161) B6987161
theorem B1840071 : Blo 1839621 1840071 := bstep (se 1 (by rfl) ⟨1380053, by rfl⟩ : syracuseStep 1840071 = 2760107) B2760107
theorem B1840091 : Blo 1839621 1840091 := bstep (se 1 (by rfl) ⟨1380068, by rfl⟩ : syracuseStep 1840091 = 2760137) B2760137
theorem B4142087 : Blo 1839621 4142087 := bstep (se 1 (by rfl) ⟨3106565, by rfl⟩ : syracuseStep 4142087 = 6213131) B6213131
theorem B13972499 : Blo 1839621 13972499 := bstep (se 1 (by rfl) ⟨10479374, by rfl⟩ : syracuseStep 13972499 = 20958749) B20958749
theorem B1840167 : Blo 1839621 1840167 := bstep (se 1 (by rfl) ⟨1380125, by rfl⟩ : syracuseStep 1840167 = 2760251) B2760251
theorem B1840207 : Blo 1839621 1840207 := bstep (se 1 (by rfl) ⟨1380155, by rfl⟩ : syracuseStep 1840207 = 2760311) B2760311
theorem B4142159 : Blo 1839621 4142159 := bstep (se 1 (by rfl) ⟨3106619, by rfl⟩ : syracuseStep 4142159 = 6213239) B6213239
theorem B1840223 : Blo 1839621 1840223 := bstep (se 1 (by rfl) ⟨1380167, by rfl⟩ : syracuseStep 1840223 = 2760335) B2760335
theorem B1840251 : Blo 1839621 1840251 := bstep (se 1 (by rfl) ⟨1380188, by rfl⟩ : syracuseStep 1840251 = 2760377) B2760377
theorem B1840303 : Blo 1839621 1840303 := bstep (se 1 (by rfl) ⟨1380227, by rfl⟩ : syracuseStep 1840303 = 2760455) B2760455
theorem B6984899 : Blo 1839621 6984899 := bstep (se 1 (by rfl) ⟨5238674, by rfl⟩ : syracuseStep 6984899 = 10477349) B10477349
theorem B1840327 : Blo 1839621 1840327 := bstep (se 1 (by rfl) ⟨1380245, by rfl⟩ : syracuseStep 1840327 = 2760491) B2760491
theorem B1840347 : Blo 1839621 1840347 := bstep (se 1 (by rfl) ⟨1380260, by rfl⟩ : syracuseStep 1840347 = 2760521) B2760521
theorem B8393975 : Blo 1839621 8393975 := bstep (se 1 (by rfl) ⟨6295481, by rfl⟩ : syracuseStep 8393975 = 12590963) B12590963
theorem B1840423 : Blo 1839621 1840423 := bstep (se 1 (by rfl) ⟨1380317, by rfl⟩ : syracuseStep 1840423 = 2760635) B2760635
theorem B1840463 : Blo 1839621 1840463 := bstep (se 1 (by rfl) ⟨1380347, by rfl⟩ : syracuseStep 1840463 = 2760695) B2760695
theorem B1840479 : Blo 1839621 1840479 := bstep (se 1 (by rfl) ⟨1380359, by rfl⟩ : syracuseStep 1840479 = 2760719) B2760719
theorem B1840507 : Blo 1839621 1840507 := bstep (se 1 (by rfl) ⟨1380380, by rfl⟩ : syracuseStep 1840507 = 2760761) B2760761
theorem B5240189 : Blo 1839621 5240189 := bstep (se 3 (by rfl) ⟨982535, by rfl⟩ : syracuseStep 5240189 = 1965071) B1965071
theorem B1840559 : Blo 1839621 1840559 := bstep (se 1 (by rfl) ⟨1380419, by rfl⟩ : syracuseStep 1840559 = 2760839) B2760839
theorem B1840583 : Blo 1839621 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B15717833 : Blo 1839621 15717833 := bstep (se 2 (by rfl) ⟨5894187, by rfl⟩ : syracuseStep 15717833 = 11788375) B11788375
theorem B68081105 : Blo 1839621 68081105 := bstep (se 2 (by rfl) ⟨25530414, by rfl⟩ : syracuseStep 68081105 = 51060829) B51060829
theorem B1840603 : Blo 1839621 1840603 := bstep (se 1 (by rfl) ⟨1380452, by rfl⟩ : syracuseStep 1840603 = 2760905) B2760905
theorem B4142555 : Blo 1839621 4142555 := bstep (se 1 (by rfl) ⟨3106916, by rfl⟩ : syracuseStep 4142555 = 6213833) B6213833
theorem B6813193 : Blo 1839621 6813193 := bstep (se 2 (by rfl) ⟨2554947, by rfl⟩ : syracuseStep 6813193 = 5109895) B5109895
theorem B1840679 : Blo 1839621 1840679 := bstep (se 1 (by rfl) ⟨1380509, by rfl⟩ : syracuseStep 1840679 = 2761019) B2761019
theorem B1840719 : Blo 1839621 1840719 := bstep (se 1 (by rfl) ⟨1380539, by rfl⟩ : syracuseStep 1840719 = 2761079) B2761079
theorem B1840735 : Blo 1839621 1840735 := bstep (se 1 (by rfl) ⟨1380551, by rfl⟩ : syracuseStep 1840735 = 2761103) B2761103
theorem B2070139 : Blo 1839621 2070139 := bstep (se 1 (by rfl) ⟨1552604, by rfl⟩ : syracuseStep 2070139 = 3105209) B3105209
theorem B5895803 : Blo 1839621 5895803 := bstep (se 1 (by rfl) ⟨4421852, by rfl⟩ : syracuseStep 5895803 = 8843705) B8843705
theorem B1840763 : Blo 1839621 1840763 := bstep (se 1 (by rfl) ⟨1380572, by rfl⟩ : syracuseStep 1840763 = 2761145) B2761145
theorem B6215291 : Blo 1839621 6215291 := bstep (se 1 (by rfl) ⟨4661468, by rfl⟩ : syracuseStep 6215291 = 9322937) B9322937
theorem B56694421 : Blo 1839621 56694421 := bstep (se 6 (by rfl) ⟨1328775, by rfl⟩ : syracuseStep 56694421 = 2657551) B2657551
theorem B1840815 : Blo 1839621 1840815 := bstep (se 1 (by rfl) ⟨1380611, by rfl⟩ : syracuseStep 1840815 = 2761223) B2761223
theorem B1840839 : Blo 1839621 1840839 := bstep (se 1 (by rfl) ⟨1380629, by rfl⟩ : syracuseStep 1840839 = 2761259) B2761259
theorem B5240531 : Blo 1839621 5240531 := bstep (se 1 (by rfl) ⟨3930398, by rfl⟩ : syracuseStep 5240531 = 7860797) B7860797
theorem B5043923 : Blo 1839621 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B1840859 : Blo 1839621 1840859 := bstep (se 1 (by rfl) ⟨1380644, by rfl⟩ : syracuseStep 1840859 = 2761289) B2761289
theorem B9950941 : Blo 1839621 9950941 := bstep (se 3 (by rfl) ⟨1865801, by rfl⟩ : syracuseStep 9950941 = 3731603) B3731603
theorem B6215453 : Blo 1839621 6215453 := bstep (se 3 (by rfl) ⟨1165397, by rfl⟩ : syracuseStep 6215453 = 2330795) B2330795
theorem B1840935 : Blo 1839621 1840935 := bstep (se 1 (by rfl) ⟨1380701, by rfl⟩ : syracuseStep 1840935 = 2761403) B2761403
theorem B7460675 : Blo 1839621 7460675 := bstep (se 1 (by rfl) ⟨5595506, by rfl⟩ : syracuseStep 7460675 = 11191013) B11191013
theorem B2946889 : Blo 1839621 2946889 := bstep (se 2 (by rfl) ⟨1105083, by rfl⟩ : syracuseStep 2946889 = 2210167) B2210167
theorem B1840975 : Blo 1839621 1840975 := bstep (se 1 (by rfl) ⟨1380731, by rfl⟩ : syracuseStep 1840975 = 2761463) B2761463
theorem B6141791 : Blo 1839621 6141791 := bstep (se 1 (by rfl) ⟨4606343, by rfl⟩ : syracuseStep 6141791 = 9212687) B9212687
theorem B1840991 : Blo 1839621 1840991 := bstep (se 1 (by rfl) ⟨1380743, by rfl⟩ : syracuseStep 1840991 = 2761487) B2761487
theorem B6297463 : Blo 1839621 6297463 := bstep (se 1 (by rfl) ⟨4723097, by rfl⟩ : syracuseStep 6297463 = 9446195) B9446195
theorem B1841019 : Blo 1839621 1841019 := bstep (se 1 (by rfl) ⟨1380764, by rfl⟩ : syracuseStep 1841019 = 2761529) B2761529
theorem B5896111 : Blo 1839621 5896111 := bstep (se 1 (by rfl) ⟨4422083, by rfl⟩ : syracuseStep 5896111 = 8844167) B8844167
theorem B1841071 : Blo 1839621 1841071 := bstep (se 1 (by rfl) ⟨1380803, by rfl⟩ : syracuseStep 1841071 = 2761607) B2761607
theorem B4143023 : Blo 1839621 4143023 := bstep (se 1 (by rfl) ⟨3107267, by rfl⟩ : syracuseStep 4143023 = 6214535) B6214535
theorem B1841095 : Blo 1839621 1841095 := bstep (se 1 (by rfl) ⟨1380821, by rfl⟩ : syracuseStep 1841095 = 2761643) B2761643
theorem B1841115 : Blo 1839621 1841115 := bstep (se 1 (by rfl) ⟨1380836, by rfl⟩ : syracuseStep 1841115 = 2761673) B2761673
theorem B13981733 : Blo 1839621 13981733 := bstep (se 4 (by rfl) ⟨1310787, by rfl⟩ : syracuseStep 13981733 = 2621575) B2621575
theorem B1841191 : Blo 1839621 1841191 := bstep (se 1 (by rfl) ⟨1380893, by rfl⟩ : syracuseStep 1841191 = 2761787) B2761787
theorem B2070607 : Blo 1839621 2070607 := bstep (se 1 (by rfl) ⟨1552955, by rfl⟩ : syracuseStep 2070607 = 3105911) B3105911
theorem B1841231 : Blo 1839621 1841231 := bstep (se 1 (by rfl) ⟨1380923, by rfl⟩ : syracuseStep 1841231 = 2761847) B2761847
theorem B1841247 : Blo 1839621 1841247 := bstep (se 1 (by rfl) ⟨1380935, by rfl⟩ : syracuseStep 1841247 = 2761871) B2761871
theorem B1841275 : Blo 1839621 1841275 := bstep (se 1 (by rfl) ⟨1380956, by rfl⟩ : syracuseStep 1841275 = 2761913) B2761913
theorem B6985885 : Blo 1839621 6985885 := bstep (se 3 (by rfl) ⟨1309853, by rfl⟩ : syracuseStep 6985885 = 2619707) B2619707
theorem B4143275 : Blo 1839621 4143275 := bstep (se 1 (by rfl) ⟨3107456, by rfl⟩ : syracuseStep 4143275 = 6214913) B6214913
theorem B1841327 : Blo 1839621 1841327 := bstep (se 1 (by rfl) ⟨1380995, by rfl⟩ : syracuseStep 1841327 = 2761991) B2761991
theorem B1841351 : Blo 1839621 1841351 := bstep (se 1 (by rfl) ⟨1381013, by rfl⟩ : syracuseStep 1841351 = 2762027) B2762027
theorem B1841371 : Blo 1839621 1841371 := bstep (se 1 (by rfl) ⟨1381028, by rfl⟩ : syracuseStep 1841371 = 2762057) B2762057
theorem B1841447 : Blo 1839621 1841447 := bstep (se 1 (by rfl) ⟨1381085, by rfl⟩ : syracuseStep 1841447 = 2762171) B2762171
theorem B1841487 : Blo 1839621 1841487 := bstep (se 1 (by rfl) ⟨1381115, by rfl⟩ : syracuseStep 1841487 = 2762231) B2762231
theorem B1841503 : Blo 1839621 1841503 := bstep (se 1 (by rfl) ⟨1381127, by rfl⟩ : syracuseStep 1841503 = 2762255) B2762255
theorem B1841531 : Blo 1839621 1841531 := bstep (se 1 (by rfl) ⟨1381148, by rfl⟩ : syracuseStep 1841531 = 2762297) B2762297
theorem B1841583 : Blo 1839621 1841583 := bstep (se 1 (by rfl) ⟨1381187, by rfl⟩ : syracuseStep 1841583 = 2762375) B2762375
theorem B1841607 : Blo 1839621 1841607 := bstep (se 1 (by rfl) ⟨1381205, by rfl⟩ : syracuseStep 1841607 = 2762411) B2762411
theorem B15718859 : Blo 1839621 15718859 := bstep (se 1 (by rfl) ⟨11789144, by rfl⟩ : syracuseStep 15718859 = 23578289) B23578289
theorem B1964507 : Blo 1839621 1964507 := bstep (se 1 (by rfl) ⟨1473380, by rfl⟩ : syracuseStep 1964507 = 2946761) B2946761
theorem B2071003 : Blo 1839621 2071003 := bstep (se 1 (by rfl) ⟨1553252, by rfl⟩ : syracuseStep 2071003 = 3106505) B3106505
theorem B9320993 : Blo 1839621 9320993 := bstep (se 2 (by rfl) ⟨3495372, by rfl⟩ : syracuseStep 9320993 = 6990745) B6990745
theorem B5978909 : Blo 1839621 5978909 := bstep (se 3 (by rfl) ⟨1121045, by rfl⟩ : syracuseStep 5978909 = 2242091) B2242091
theorem B5897033 : Blo 1839621 5897033 := bstep (se 2 (by rfl) ⟨2211387, by rfl⟩ : syracuseStep 5897033 = 4422775) B4422775
theorem B2759519 : Blo 1839621 2759519 := bstep (se 1 (by rfl) ⟨2069639, by rfl⟩ : syracuseStep 2759519 = 4139279) B4139279
theorem B5045087 : Blo 1839621 5045087 := bstep (se 1 (by rfl) ⟨3783815, by rfl⟩ : syracuseStep 5045087 = 7567631) B7567631
theorem B2759531 : Blo 1839621 2759531 := bstep (se 1 (by rfl) ⟨2069648, by rfl⟩ : syracuseStep 2759531 = 4139297) B4139297
theorem B2071471 : Blo 1839621 2071471 := bstep (se 1 (by rfl) ⟨1553603, by rfl⟩ : syracuseStep 2071471 = 3107207) B3107207
theorem B3316663 : Blo 1839621 3316663 := bstep (se 1 (by rfl) ⟨2487497, by rfl⟩ : syracuseStep 3316663 = 4974995) B4974995
theorem B3931193 : Blo 1839621 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B2759759 : Blo 1839621 2759759 := bstep (se 1 (by rfl) ⟨2069819, by rfl⟩ : syracuseStep 2759759 = 4139639) B4139639
theorem B13270169 : Blo 1839621 13270169 := bstep (se 2 (by rfl) ⟨4976313, by rfl⟩ : syracuseStep 13270169 = 9952627) B9952627
theorem B2759879 : Blo 1839621 2759879 := bstep (se 1 (by rfl) ⟨2069909, by rfl⟩ : syracuseStep 2759879 = 4139819) B4139819
theorem B5242103 : Blo 1839621 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B2760041 : Blo 1839621 2760041 := bstep (se 2 (by rfl) ⟨1035015, by rfl⟩ : syracuseStep 2760041 = 2070031) B2070031
theorem B6298985 : Blo 1839621 6298985 := bstep (se 2 (by rfl) ⟨2362119, by rfl⟩ : syracuseStep 6298985 = 4724239) B4724239
theorem B2760119 : Blo 1839621 2760119 := bstep (se 1 (by rfl) ⟨2070089, by rfl⟩ : syracuseStep 2760119 = 4140179) B4140179
theorem B2760155 : Blo 1839621 2760155 := bstep (se 1 (by rfl) ⟨2070116, by rfl⟩ : syracuseStep 2760155 = 4140233) B4140233
theorem B4660699 : Blo 1839621 4660699 := bstep (se 1 (by rfl) ⟨3495524, by rfl⟩ : syracuseStep 4660699 = 6991049) B6991049
theorem B7863905 : Blo 1839621 7863905 := bstep (se 2 (by rfl) ⟨2948964, by rfl⟩ : syracuseStep 7863905 = 5897929) B5897929
theorem B10485571 : Blo 1839621 10485571 := bstep (se 1 (by rfl) ⟨7864178, by rfl⟩ : syracuseStep 10485571 = 15728357) B15728357
theorem B2621279 : Blo 1839621 2621279 := bstep (se 1 (by rfl) ⟨1965959, by rfl⟩ : syracuseStep 2621279 = 3931919) B3931919
theorem B3833705 : Blo 1839621 3833705 := bstep (se 2 (by rfl) ⟨1437639, by rfl⟩ : syracuseStep 3833705 = 2875279) B2875279
theorem B13975415 : Blo 1839621 13975415 := bstep (se 1 (by rfl) ⟨10481561, by rfl⟩ : syracuseStep 13975415 = 20963123) B20963123
theorem B26533763 : Blo 1839621 26533763 := bstep (se 1 (by rfl) ⟨19900322, by rfl⟩ : syracuseStep 26533763 = 39800645) B39800645
theorem B2760623 : Blo 1839621 2760623 := bstep (se 1 (by rfl) ⟨2070467, by rfl⟩ : syracuseStep 2760623 = 4140935) B4140935
theorem B2621359 : Blo 1839621 2621359 := bstep (se 1 (by rfl) ⟨1966019, by rfl⟩ : syracuseStep 2621359 = 3932039) B3932039
theorem B2760809 : Blo 1839621 2760809 := bstep (se 2 (by rfl) ⟨1035303, by rfl⟩ : syracuseStep 2760809 = 2070607) B2070607
theorem B79593677 : Blo 1839621 79593677 := bstep (se 3 (by rfl) ⟨14923814, by rfl⟩ : syracuseStep 79593677 = 29847629) B29847629
theorem B9314513 : Blo 1839621 9314513 := bstep (se 2 (by rfl) ⟨3492942, by rfl⟩ : syracuseStep 9314513 = 6985885) B6985885
theorem B4661459 : Blo 1839621 4661459 := bstep (se 1 (by rfl) ⟨3496094, by rfl⟩ : syracuseStep 4661459 = 6992189) B6992189
theorem B2212219 : Blo 1839621 2212219 := bstep (se 1 (by rfl) ⟨1659164, by rfl⟩ : syracuseStep 2212219 = 3318329) B3318329
theorem B13984163 : Blo 1839621 13984163 := bstep (se 1 (by rfl) ⟨10488122, by rfl⟩ : syracuseStep 13984163 = 20976245) B20976245
theorem B2761127 : Blo 1839621 2761127 := bstep (se 1 (by rfl) ⟨2070845, by rfl⟩ : syracuseStep 2761127 = 4141691) B4141691
theorem B9953711 : Blo 1839621 9953711 := bstep (se 1 (by rfl) ⟨7465283, by rfl⟩ : syracuseStep 9953711 = 14930567) B14930567
theorem B2761211 : Blo 1839621 2761211 := bstep (se 1 (by rfl) ⟨2070908, by rfl⟩ : syracuseStep 2761211 = 4141817) B4141817
theorem B2761337 : Blo 1839621 2761337 := bstep (se 2 (by rfl) ⟨1035501, by rfl⟩ : syracuseStep 2761337 = 2071003) B2071003
theorem B2761391 : Blo 1839621 2761391 := bstep (se 1 (by rfl) ⟨2071043, by rfl⟩ : syracuseStep 2761391 = 4142087) B4142087
theorem B9314999 : Blo 1839621 9314999 := bstep (se 1 (by rfl) ⟨6986249, by rfl⟩ : syracuseStep 9314999 = 13972499) B13972499
theorem B2761439 : Blo 1839621 2761439 := bstep (se 1 (by rfl) ⟨2071079, by rfl⟩ : syracuseStep 2761439 = 4142159) B4142159
theorem B29844197 : Blo 1839621 29844197 := bstep (se 4 (by rfl) ⟨2797893, by rfl⟩ : syracuseStep 29844197 = 5595787) B5595787
theorem B5595983 : Blo 1839621 5595983 := bstep (se 1 (by rfl) ⟨4196987, by rfl⟩ : syracuseStep 5595983 = 8393975) B8393975
theorem B10478555 : Blo 1839621 10478555 := bstep (se 1 (by rfl) ⟨7858916, by rfl⟩ : syracuseStep 10478555 = 15717833) B15717833
theorem B2761703 : Blo 1839621 2761703 := bstep (se 1 (by rfl) ⟨2071277, by rfl⟩ : syracuseStep 2761703 = 4142555) B4142555
theorem B5243879 : Blo 1839621 5243879 := bstep (se 1 (by rfl) ⟨3932909, by rfl⟩ : syracuseStep 5243879 = 7865819) B7865819
theorem B9315485 : Blo 1839621 9315485 := bstep (se 3 (by rfl) ⟨1746653, by rfl⟩ : syracuseStep 9315485 = 3493307) B3493307
theorem B4973783 : Blo 1839621 4973783 := bstep (se 1 (by rfl) ⟨3730337, by rfl⟩ : syracuseStep 4973783 = 7460675) B7460675
theorem B2761961 : Blo 1839621 2761961 := bstep (se 2 (by rfl) ⟨1035735, by rfl⟩ : syracuseStep 2761961 = 2071471) B2071471
theorem B6210809 : Blo 1839621 6210809 := bstep (se 2 (by rfl) ⟨2329053, by rfl⟩ : syracuseStep 6210809 = 4658107) B4658107
theorem B2762015 : Blo 1839621 2762015 := bstep (se 1 (by rfl) ⟨2071511, by rfl⟩ : syracuseStep 2762015 = 4143023) B4143023
theorem B2762183 : Blo 1839621 2762183 := bstep (se 1 (by rfl) ⟨2071637, by rfl⟩ : syracuseStep 2762183 = 4143275) B4143275
theorem B6211079 : Blo 1839621 6211079 := bstep (se 1 (by rfl) ⟨4658309, by rfl⟩ : syracuseStep 6211079 = 9316619) B9316619
theorem B10479239 : Blo 1839621 10479239 := bstep (se 1 (by rfl) ⟨7859429, by rfl⟩ : syracuseStep 10479239 = 15718859) B15718859
theorem B16787101 : Blo 1839621 16787101 := bstep (se 3 (by rfl) ⟨3147581, by rfl⟩ : syracuseStep 16787101 = 6295163) B6295163
theorem B2328527 : Blo 1839621 2328527 := bstep (se 1 (by rfl) ⟨1746395, by rfl⟩ : syracuseStep 2328527 = 3492791) B3492791
theorem B161450117 : Blo 1839621 161450117 := bstep (se 4 (by rfl) ⟨15135948, by rfl⟩ : syracuseStep 161450117 = 30271897) B30271897
theorem B16378109 : Blo 1839621 16378109 := bstep (se 3 (by rfl) ⟨3070895, by rfl⟩ : syracuseStep 16378109 = 6141791) B6141791
theorem B6990077 : Blo 1839621 6990077 := bstep (se 3 (by rfl) ⟨1310639, by rfl⟩ : syracuseStep 6990077 = 2621279) B2621279
theorem B23595407 : Blo 1839621 23595407 := bstep (se 1 (by rfl) ⟨17696555, by rfl⟩ : syracuseStep 23595407 = 35393111) B35393111
theorem B9316781 : Blo 1839621 9316781 := bstep (se 3 (by rfl) ⟨1746896, by rfl⟩ : syracuseStep 9316781 = 3493793) B3493793
theorem B6212051 : Blo 1839621 6212051 := bstep (se 1 (by rfl) ⟨4659038, by rfl⟩ : syracuseStep 6212051 = 9318077) B9318077
theorem B6212159 : Blo 1839621 6212159 := bstep (se 1 (by rfl) ⟨4659119, by rfl⟩ : syracuseStep 6212159 = 9318239) B9318239
theorem B9316943 : Blo 1839621 9316943 := bstep (se 1 (by rfl) ⟨6987707, by rfl⟩ : syracuseStep 9316943 = 13975415) B13975415
theorem B17689175 : Blo 1839621 17689175 := bstep (se 1 (by rfl) ⟨13266881, by rfl⟩ : syracuseStep 17689175 = 26533763) B26533763
theorem B7858883 : Blo 1839621 7858883 := bstep (se 1 (by rfl) ⟨5894162, by rfl⟩ : syracuseStep 7858883 = 11788325) B11788325
theorem B3107551 : Blo 1839621 3107551 := bstep (se 1 (by rfl) ⟨2330663, by rfl⟩ : syracuseStep 3107551 = 4661327) B4661327
theorem B4139855 : Blo 1839621 4139855 := bstep (se 1 (by rfl) ⟨3104891, by rfl⟩ : syracuseStep 4139855 = 6209783) B6209783
theorem B2329499 : Blo 1839621 2329499 := bstep (se 1 (by rfl) ⟨1747124, by rfl⟩ : syracuseStep 2329499 = 3494249) B3494249
theorem B4140071 : Blo 1839621 4140071 := bstep (se 1 (by rfl) ⟨3105053, by rfl⟩ : syracuseStep 4140071 = 6210107) B6210107
theorem B17681485 : Blo 1839621 17681485 := bstep (se 3 (by rfl) ⟨3315278, by rfl⟩ : syracuseStep 17681485 = 6630557) B6630557
theorem B4140251 : Blo 1839621 4140251 := bstep (se 1 (by rfl) ⟨3105188, by rfl⟩ : syracuseStep 4140251 = 6210377) B6210377
theorem B3730727 : Blo 1839621 3730727 := bstep (se 1 (by rfl) ⟨2798045, by rfl⟩ : syracuseStep 3730727 = 5596091) B5596091
theorem B10481015 : Blo 1839621 10481015 := bstep (se 1 (by rfl) ⟨7860761, by rfl⟩ : syracuseStep 10481015 = 15721523) B15721523
theorem B23596433 : Blo 1839621 23596433 := bstep (se 2 (by rfl) ⟨8848662, by rfl⟩ : syracuseStep 23596433 = 17697325) B17697325
theorem B4140449 : Blo 1839621 4140449 := bstep (se 2 (by rfl) ⟨1552668, by rfl⟩ : syracuseStep 4140449 = 3105337) B3105337
theorem B4656599 : Blo 1839621 4656599 := bstep (se 1 (by rfl) ⟨3492449, by rfl⟩ : syracuseStep 4656599 = 6984899) B6984899
theorem B5893715 : Blo 1839621 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B3493459 : Blo 1839621 3493459 := bstep (se 1 (by rfl) ⟨2620094, by rfl⟩ : syracuseStep 3493459 = 5240189) B5240189
theorem B10219243 : Blo 1839621 10219243 := bstep (se 1 (by rfl) ⟨7664432, by rfl⟩ : syracuseStep 10219243 = 15328865) B15328865
theorem B3493687 : Blo 1839621 3493687 := bstep (se 1 (by rfl) ⟨2620265, by rfl⟩ : syracuseStep 3493687 = 5240531) B5240531
theorem B3362615 : Blo 1839621 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B4656953 : Blo 1839621 4656953 := bstep (se 2 (by rfl) ⟨1746357, by rfl⟩ : syracuseStep 4656953 = 3492715) B3492715
theorem B5238685 : Blo 1839621 5238685 := bstep (se 3 (by rfl) ⟨982253, by rfl⟩ : syracuseStep 5238685 = 1964507) B1964507
theorem B4141007 : Blo 1839621 4141007 := bstep (se 1 (by rfl) ⟨3105755, by rfl⟩ : syracuseStep 4141007 = 6211511) B6211511
theorem B9318401 : Blo 1839621 9318401 := bstep (se 2 (by rfl) ⟨3494400, by rfl⟩ : syracuseStep 9318401 = 6988801) B6988801
theorem B10481723 : Blo 1839621 10481723 := bstep (se 1 (by rfl) ⟨7861292, by rfl⟩ : syracuseStep 10481723 = 15722585) B15722585
theorem B4141385 : Blo 1839621 4141385 := bstep (se 2 (by rfl) ⟨1553019, by rfl⟩ : syracuseStep 4141385 = 3106039) B3106039
theorem B4141403 : Blo 1839621 4141403 := bstep (se 1 (by rfl) ⟨3106052, by rfl⟩ : syracuseStep 4141403 = 6212105) B6212105
theorem B6213995 : Blo 1839621 6213995 := bstep (se 1 (by rfl) ⟨4660496, by rfl⟩ : syracuseStep 6213995 = 9320993) B9320993
theorem B4977071 : Blo 1839621 4977071 := bstep (se 1 (by rfl) ⟨3732803, by rfl⟩ : syracuseStep 4977071 = 7465607) B7465607
theorem B3985939 : Blo 1839621 3985939 := bstep (se 1 (by rfl) ⟨2989454, by rfl⟩ : syracuseStep 3985939 = 5978909) B5978909
theorem B1839679 : Blo 1839621 1839679 := bstep (se 1 (by rfl) ⟨1379759, by rfl⟩ : syracuseStep 1839679 = 2759519) B2759519
theorem B3363391 : Blo 1839621 3363391 := bstep (se 1 (by rfl) ⟨2522543, by rfl⟩ : syracuseStep 3363391 = 5045087) B5045087
theorem B1839687 : Blo 1839621 1839687 := bstep (se 1 (by rfl) ⟨1379765, by rfl⟩ : syracuseStep 1839687 = 2759531) B2759531
theorem B6632057 : Blo 1839621 6632057 := bstep (se 2 (by rfl) ⟨2487021, by rfl⟩ : syracuseStep 6632057 = 4974043) B4974043
theorem B6214265 : Blo 1839621 6214265 := bstep (se 2 (by rfl) ⟨2330349, by rfl⟩ : syracuseStep 6214265 = 4660699) B4660699
theorem B1839839 : Blo 1839621 1839839 := bstep (se 1 (by rfl) ⟨1379879, by rfl⟩ : syracuseStep 1839839 = 2759759) B2759759
theorem B15717149 : Blo 1839621 15717149 := bstep (se 3 (by rfl) ⟨2946965, by rfl⟩ : syracuseStep 15717149 = 5893931) B5893931
theorem B9319211 : Blo 1839621 9319211 := bstep (se 1 (by rfl) ⟨6989408, by rfl⟩ : syracuseStep 9319211 = 13978817) B13978817
theorem B1839919 : Blo 1839621 1839919 := bstep (se 1 (by rfl) ⟨1379939, by rfl⟩ : syracuseStep 1839919 = 2759879) B2759879
theorem B2487119 : Blo 1839621 2487119 := bstep (se 1 (by rfl) ⟨1865339, by rfl⟩ : syracuseStep 2487119 = 3730679) B3730679
theorem B3494735 : Blo 1839621 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B75592561 : Blo 1839621 75592561 := bstep (se 2 (by rfl) ⟨28347210, by rfl⟩ : syracuseStep 75592561 = 56694421) B56694421
theorem B1840027 : Blo 1839621 1840027 := bstep (se 1 (by rfl) ⟨1380020, by rfl⟩ : syracuseStep 1840027 = 2760041) B2760041
theorem B4141979 : Blo 1839621 4141979 := bstep (se 1 (by rfl) ⟨3106484, by rfl⟩ : syracuseStep 4141979 = 6212969) B6212969
theorem B4199323 : Blo 1839621 4199323 := bstep (se 1 (by rfl) ⟨3149492, by rfl⟩ : syracuseStep 4199323 = 6298985) B6298985
theorem B1840079 : Blo 1839621 1840079 := bstep (se 1 (by rfl) ⟨1380059, by rfl⟩ : syracuseStep 1840079 = 2760119) B2760119
theorem B13267921 : Blo 1839621 13267921 := bstep (se 2 (by rfl) ⟨4975470, by rfl⟩ : syracuseStep 13267921 = 9950941) B9950941
theorem B1840103 : Blo 1839621 1840103 := bstep (se 1 (by rfl) ⟨1380077, by rfl⟩ : syracuseStep 1840103 = 2760155) B2760155
theorem B6910951 : Blo 1839621 6910951 := bstep (se 1 (by rfl) ⟨5183213, by rfl⟩ : syracuseStep 6910951 = 10366427) B10366427
theorem B13980761 : Blo 1839621 13980761 := bstep (se 2 (by rfl) ⟨5242785, by rfl⟩ : syracuseStep 13980761 = 10485571) B10485571
theorem B3929185 : Blo 1839621 3929185 := bstep (se 2 (by rfl) ⟨1473444, by rfl⟩ : syracuseStep 3929185 = 2946889) B2946889
theorem B4142177 : Blo 1839621 4142177 := bstep (se 2 (by rfl) ⟨1553316, by rfl⟩ : syracuseStep 4142177 = 3106633) B3106633
theorem B4420747 : Blo 1839621 4420747 := bstep (se 1 (by rfl) ⟨3315560, by rfl⟩ : syracuseStep 4420747 = 6631121) B6631121
theorem B7861481 : Blo 1839621 7861481 := bstep (se 2 (by rfl) ⟨2948055, by rfl⟩ : syracuseStep 7861481 = 5896111) B5896111
theorem B3495145 : Blo 1839621 3495145 := bstep (se 2 (by rfl) ⟨1310679, by rfl⟩ : syracuseStep 3495145 = 2621359) B2621359
theorem B1840415 : Blo 1839621 1840415 := bstep (se 1 (by rfl) ⟨1380311, by rfl⟩ : syracuseStep 1840415 = 2760623) B2760623
theorem B4142375 : Blo 1839621 4142375 := bstep (se 1 (by rfl) ⟨3106781, by rfl⟩ : syracuseStep 4142375 = 6213563) B6213563
theorem B2069851 : Blo 1839621 2069851 := bstep (se 1 (by rfl) ⟨1552388, by rfl⟩ : syracuseStep 2069851 = 3104777) B3104777
theorem B1840475 : Blo 1839621 1840475 := bstep (se 1 (by rfl) ⟨1380356, by rfl⟩ : syracuseStep 1840475 = 2760713) B2760713
theorem B7460191 : Blo 1839621 7460191 := bstep (se 1 (by rfl) ⟨5595143, by rfl⟩ : syracuseStep 7460191 = 11190287) B11190287
theorem B1840495 : Blo 1839621 1840495 := bstep (se 1 (by rfl) ⟨1380371, by rfl⟩ : syracuseStep 1840495 = 2760743) B2760743
theorem B3495305 : Blo 1839621 3495305 := bstep (se 2 (by rfl) ⟨1310739, by rfl⟩ : syracuseStep 3495305 = 2621479) B2621479
theorem B4658593 : Blo 1839621 4658593 := bstep (se 2 (by rfl) ⟨1746972, by rfl⟩ : syracuseStep 4658593 = 3493945) B3493945
theorem B1840551 : Blo 1839621 1840551 := bstep (se 1 (by rfl) ⟨1380413, by rfl⟩ : syracuseStep 1840551 = 2760827) B2760827
theorem B2069959 : Blo 1839621 2069959 := bstep (se 1 (by rfl) ⟨1552469, by rfl⟩ : syracuseStep 2069959 = 3104939) B3104939
theorem B10483181 : Blo 1839621 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B1840635 : Blo 1839621 1840635 := bstep (se 1 (by rfl) ⟨1380476, by rfl⟩ : syracuseStep 1840635 = 2760953) B2760953
theorem B33601061 : Blo 1839621 33601061 := bstep (se 4 (by rfl) ⟨3150099, by rfl⟩ : syracuseStep 33601061 = 6300199) B6300199
theorem B23590439 : Blo 1839621 23590439 := bstep (se 1 (by rfl) ⟨17692829, by rfl⟩ : syracuseStep 23590439 = 35385659) B35385659
theorem B1840703 : Blo 1839621 1840703 := bstep (se 1 (by rfl) ⟨1380527, by rfl⟩ : syracuseStep 1840703 = 2761055) B2761055
theorem B1840711 : Blo 1839621 1840711 := bstep (se 1 (by rfl) ⟨1380533, by rfl⟩ : syracuseStep 1840711 = 2761067) B2761067
theorem B4142753 : Blo 1839621 4142753 := bstep (se 2 (by rfl) ⟨1553532, by rfl⟩ : syracuseStep 4142753 = 3107065) B3107065
theorem B1840863 : Blo 1839621 1840863 := bstep (se 1 (by rfl) ⟨1380647, by rfl⟩ : syracuseStep 1840863 = 2761295) B2761295
theorem B35387117 : Blo 1839621 35387117 := bstep (se 3 (by rfl) ⟨6635084, by rfl⟩ : syracuseStep 35387117 = 13270169) B13270169
theorem B2070319 : Blo 1839621 2070319 := bstep (se 1 (by rfl) ⟨1552739, by rfl⟩ : syracuseStep 2070319 = 3105479) B3105479
theorem B1840943 : Blo 1839621 1840943 := bstep (se 1 (by rfl) ⟨1380707, by rfl⟩ : syracuseStep 1840943 = 2761415) B2761415
theorem B3495737 : Blo 1839621 3495737 := bstep (se 2 (by rfl) ⟨1310901, by rfl⟩ : syracuseStep 3495737 = 2621803) B2621803
theorem B2070427 : Blo 1839621 2070427 := bstep (se 1 (by rfl) ⟨1552820, by rfl⟩ : syracuseStep 2070427 = 3105641) B3105641
theorem B1841051 : Blo 1839621 1841051 := bstep (se 1 (by rfl) ⟨1380788, by rfl⟩ : syracuseStep 1841051 = 2761577) B2761577
theorem B1841103 : Blo 1839621 1841103 := bstep (se 1 (by rfl) ⟨1380827, by rfl⟩ : syracuseStep 1841103 = 2761655) B2761655
theorem B1841127 : Blo 1839621 1841127 := bstep (se 1 (by rfl) ⟨1380845, by rfl⟩ : syracuseStep 1841127 = 2761691) B2761691
theorem B4143113 : Blo 1839621 4143113 := bstep (se 2 (by rfl) ⟨1553667, by rfl⟩ : syracuseStep 4143113 = 3107335) B3107335
theorem B1841439 : Blo 1839621 1841439 := bstep (se 1 (by rfl) ⟨1381079, by rfl⟩ : syracuseStep 1841439 = 2762159) B2762159
theorem B2070823 : Blo 1839621 2070823 := bstep (se 1 (by rfl) ⟨1553117, by rfl⟩ : syracuseStep 2070823 = 3106235) B3106235
theorem B1841499 : Blo 1839621 1841499 := bstep (se 1 (by rfl) ⟨1381124, by rfl⟩ : syracuseStep 1841499 = 2762249) B2762249
theorem B2070895 : Blo 1839621 2070895 := bstep (se 1 (by rfl) ⟨1553171, by rfl⟩ : syracuseStep 2070895 = 3106343) B3106343
theorem B1841519 : Blo 1839621 1841519 := bstep (se 1 (by rfl) ⟨1381139, by rfl⟩ : syracuseStep 1841519 = 2762279) B2762279
theorem B3930535 : Blo 1839621 3930535 := bstep (se 1 (by rfl) ⟨2947901, by rfl⟩ : syracuseStep 3930535 = 5895803) B5895803
theorem B4143527 : Blo 1839621 4143527 := bstep (se 1 (by rfl) ⟨3107645, by rfl⟩ : syracuseStep 4143527 = 6215291) B6215291
theorem B1841575 : Blo 1839621 1841575 := bstep (se 1 (by rfl) ⟨1381181, by rfl⟩ : syracuseStep 1841575 = 2762363) B2762363
theorem B4659707 : Blo 1839621 4659707 := bstep (se 1 (by rfl) ⟨3494780, by rfl⟩ : syracuseStep 4659707 = 6989561) B6989561
theorem B4143635 : Blo 1839621 4143635 := bstep (se 1 (by rfl) ⟨3107726, by rfl⟩ : syracuseStep 4143635 = 6215453) B6215453
theorem B181549613 : Blo 1839621 181549613 := bstep (se 3 (by rfl) ⟨34040552, by rfl⟩ : syracuseStep 181549613 = 68081105) B68081105
theorem B2071111 : Blo 1839621 2071111 := bstep (se 1 (by rfl) ⟨1553333, by rfl⟩ : syracuseStep 2071111 = 3106667) B3106667
theorem B4422217 : Blo 1839621 4422217 := bstep (se 2 (by rfl) ⟨1658331, by rfl⟩ : syracuseStep 4422217 = 3316663) B3316663
theorem B9321155 : Blo 1839621 9321155 := bstep (se 1 (by rfl) ⟨6990866, by rfl⟩ : syracuseStep 9321155 = 13981733) B13981733
theorem B2759579 : Blo 1839621 2759579 := bstep (se 1 (by rfl) ⟨2069684, by rfl⟩ : syracuseStep 2759579 = 4139369) B4139369
theorem B20970413 : Blo 1839621 20970413 := bstep (se 3 (by rfl) ⟨3931952, by rfl⟩ : syracuseStep 20970413 = 7863905) B7863905
theorem B3931355 : Blo 1839621 3931355 := bstep (se 1 (by rfl) ⟨2948516, by rfl⟩ : syracuseStep 3931355 = 5897033) B5897033
theorem B2759975 : Blo 1839621 2759975 := bstep (se 1 (by rfl) ⟨2069981, by rfl⟩ : syracuseStep 2759975 = 4139963) B4139963
theorem B6208865 : Blo 1839621 6208865 := bstep (se 2 (by rfl) ⟨2328324, by rfl⟩ : syracuseStep 6208865 = 4656649) B4656649
theorem B9084257 : Blo 1839621 9084257 := bstep (se 2 (by rfl) ⟨3406596, by rfl⟩ : syracuseStep 9084257 = 6813193) B6813193
theorem B2760059 : Blo 1839621 2760059 := bstep (se 1 (by rfl) ⟨2070044, by rfl⟩ : syracuseStep 2760059 = 4140089) B4140089
theorem B4660679 : Blo 1839621 4660679 := bstep (se 1 (by rfl) ⟨3495509, by rfl⟩ : syracuseStep 4660679 = 6991019) B6991019
theorem B13983191 : Blo 1839621 13983191 := bstep (se 1 (by rfl) ⟨10487393, by rfl⟩ : syracuseStep 13983191 = 20974787) B20974787
theorem B2760185 : Blo 1839621 2760185 := bstep (se 2 (by rfl) ⟨1035069, by rfl⟩ : syracuseStep 2760185 = 2070139) B2070139
theorem B2760287 : Blo 1839621 2760287 := bstep (se 1 (by rfl) ⟨2070215, by rfl⟩ : syracuseStep 2760287 = 4140431) B4140431
theorem B39820895 : Blo 1839621 39820895 := bstep (se 1 (by rfl) ⟨29865671, by rfl⟩ : syracuseStep 39820895 = 59731343) B59731343
theorem B9314027 : Blo 1839621 9314027 := bstep (se 1 (by rfl) ⟨6985520, by rfl⟩ : syracuseStep 9314027 = 13971041) B13971041
theorem B2760503 : Blo 1839621 2760503 := bstep (se 1 (by rfl) ⟨2070377, by rfl⟩ : syracuseStep 2760503 = 4140755) B4140755
theorem B8396617 : Blo 1839621 8396617 := bstep (se 2 (by rfl) ⟨3148731, by rfl⟩ : syracuseStep 8396617 = 6297463) B6297463
theorem B2555803 : Blo 1839621 2555803 := bstep (se 1 (by rfl) ⟨1916852, by rfl⟩ : syracuseStep 2555803 = 3833705) B3833705
theorem B64642991 : Blo 1839621 64642991 := bstep (se 1 (by rfl) ⟨48482243, by rfl⟩ : syracuseStep 64642991 = 96964487) B96964487
theorem B6987815 : Blo 1839621 6987815 := bstep (se 1 (by rfl) ⟨5240861, by rfl⟩ : syracuseStep 6987815 = 10481723) B10481723
theorem B6209675 : Blo 1839621 6209675 := bstep (se 1 (by rfl) ⟨4657256, by rfl⟩ : syracuseStep 6209675 = 9314513) B9314513
theorem B2760923 : Blo 1839621 2760923 := bstep (se 1 (by rfl) ⟨2070692, by rfl⟩ : syracuseStep 2760923 = 4141385) B4141385
theorem B2760935 : Blo 1839621 2760935 := bstep (se 1 (by rfl) ⟨2070701, by rfl⟩ : syracuseStep 2760935 = 4141403) B4141403
theorem B9322775 : Blo 1839621 9322775 := bstep (se 1 (by rfl) ⟨6992081, by rfl⟩ : syracuseStep 9322775 = 13984163) B13984163
theorem B6635807 : Blo 1839621 6635807 := bstep (se 1 (by rfl) ⟨4976855, by rfl⟩ : syracuseStep 6635807 = 9953711) B9953711
theorem B3318047 : Blo 1839621 3318047 := bstep (se 1 (by rfl) ⟨2488535, by rfl⟩ : syracuseStep 3318047 = 4977071) B4977071
theorem B2761097 : Blo 1839621 2761097 := bstep (se 2 (by rfl) ⟨1035411, by rfl⟩ : syracuseStep 2761097 = 2070823) B2070823
theorem B6209999 : Blo 1839621 6209999 := bstep (se 1 (by rfl) ⟨4657499, by rfl⟩ : syracuseStep 6209999 = 9314999) B9314999
theorem B2761193 : Blo 1839621 2761193 := bstep (se 2 (by rfl) ⟨1035447, by rfl⟩ : syracuseStep 2761193 = 2070895) B2070895
theorem B2949625 : Blo 1839621 2949625 := bstep (se 2 (by rfl) ⟨1106109, by rfl⟩ : syracuseStep 2949625 = 2212219) B2212219
theorem B10478099 : Blo 1839621 10478099 := bstep (se 1 (by rfl) ⟨7858574, by rfl⟩ : syracuseStep 10478099 = 15717149) B15717149
theorem B13263421 : Blo 1839621 13263421 := bstep (se 3 (by rfl) ⟨2486891, by rfl⟩ : syracuseStep 13263421 = 4973783) B4973783
theorem B2761319 : Blo 1839621 2761319 := bstep (se 1 (by rfl) ⟨2070989, by rfl⟩ : syracuseStep 2761319 = 4141979) B4141979
theorem B23577317 : Blo 1839621 23577317 := bstep (se 4 (by rfl) ⟨2210373, by rfl⟩ : syracuseStep 23577317 = 4420747) B4420747
theorem B2761451 : Blo 1839621 2761451 := bstep (se 1 (by rfl) ⟨2071088, by rfl⟩ : syracuseStep 2761451 = 4142177) B4142177
theorem B2761481 : Blo 1839621 2761481 := bstep (se 2 (by rfl) ⟨1035555, by rfl⟩ : syracuseStep 2761481 = 2071111) B2071111
theorem B6210323 : Blo 1839621 6210323 := bstep (se 1 (by rfl) ⟨4657742, by rfl⟩ : syracuseStep 6210323 = 9315485) B9315485
theorem B2761583 : Blo 1839621 2761583 := bstep (se 1 (by rfl) ⟨2071187, by rfl⟩ : syracuseStep 2761583 = 4142375) B4142375
theorem B6988787 : Blo 1839621 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B2761835 : Blo 1839621 2761835 := bstep (se 1 (by rfl) ⟨2071376, by rfl⟩ : syracuseStep 2761835 = 4142753) B4142753
theorem B2762075 : Blo 1839621 2762075 := bstep (se 1 (by rfl) ⟨2071556, by rfl⟩ : syracuseStep 2762075 = 4143113) B4143113
theorem B15730271 : Blo 1839621 15730271 := bstep (se 1 (by rfl) ⟨11797703, by rfl⟩ : syracuseStep 15730271 = 23595407) B23595407
theorem B2762351 : Blo 1839621 2762351 := bstep (se 1 (by rfl) ⟨2071763, by rfl⟩ : syracuseStep 2762351 = 4143527) B4143527
theorem B6211187 : Blo 1839621 6211187 := bstep (se 1 (by rfl) ⟨4658390, by rfl⟩ : syracuseStep 6211187 = 9316781) B9316781
theorem B3106471 : Blo 1839621 3106471 := bstep (se 1 (by rfl) ⟨2329853, by rfl⟩ : syracuseStep 3106471 = 4659707) B4659707
theorem B2762423 : Blo 1839621 2762423 := bstep (se 1 (by rfl) ⟨2071817, by rfl⟩ : syracuseStep 2762423 = 4143635) B4143635
theorem B6211295 : Blo 1839621 6211295 := bstep (se 1 (by rfl) ⟨4658471, by rfl⟩ : syracuseStep 6211295 = 9316943) B9316943
theorem B9946921 : Blo 1839621 9946921 := bstep (se 2 (by rfl) ⟨3730095, by rfl⟩ : syracuseStep 9946921 = 7460191) B7460191
theorem B6211457 : Blo 1839621 6211457 := bstep (se 2 (by rfl) ⟨2329296, by rfl⟩ : syracuseStep 6211457 = 4658593) B4658593
theorem B147433621 : Blo 1839621 147433621 := bstep (se 6 (by rfl) ⟨3455475, by rfl⟩ : syracuseStep 147433621 = 6910951) B6910951
theorem B22382801 : Blo 1839621 22382801 := bstep (se 2 (by rfl) ⟨8393550, by rfl⟩ : syracuseStep 22382801 = 16787101) B16787101
theorem B4139243 : Blo 1839621 4139243 := bstep (se 1 (by rfl) ⟨3104432, by rfl⟩ : syracuseStep 4139243 = 6208865) B6208865
theorem B6056171 : Blo 1839621 6056171 := bstep (se 1 (by rfl) ⟨4542128, by rfl⟩ : syracuseStep 6056171 = 9084257) B9084257
theorem B15730955 : Blo 1839621 15730955 := bstep (se 1 (by rfl) ⟨11798216, by rfl⟩ : syracuseStep 15730955 = 23596433) B23596433
theorem B3107119 : Blo 1839621 3107119 := bstep (se 1 (by rfl) ⟨2330339, by rfl⟩ : syracuseStep 3107119 = 4660679) B4660679
theorem B13625657 : Blo 1839621 13625657 := bstep (se 2 (by rfl) ⟨5109621, by rfl⟩ : syracuseStep 13625657 = 10219243) B10219243
theorem B6211997 : Blo 1839621 6211997 := bstep (se 3 (by rfl) ⟨1164749, by rfl⟩ : syracuseStep 6211997 = 2329499) B2329499
theorem B6212267 : Blo 1839621 6212267 := bstep (se 1 (by rfl) ⟨4659200, by rfl⟩ : syracuseStep 6212267 = 9318401) B9318401
theorem B53062451 : Blo 1839621 53062451 := bstep (se 1 (by rfl) ⟨39796838, by rfl⟩ : syracuseStep 53062451 = 79593677) B79593677
theorem B3107639 : Blo 1839621 3107639 := bstep (se 1 (by rfl) ⟨2330729, by rfl⟩ : syracuseStep 3107639 = 4661459) B4661459
theorem B6212807 : Blo 1839621 6212807 := bstep (se 1 (by rfl) ⟨4659605, by rfl⟩ : syracuseStep 6212807 = 9319211) B9319211
theorem B3730655 : Blo 1839621 3730655 := bstep (se 1 (by rfl) ⟨2797991, by rfl⟩ : syracuseStep 3730655 = 5595983) B5595983
theorem B2329823 : Blo 1839621 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B4484521 : Blo 1839621 4484521 := bstep (se 2 (by rfl) ⟨1681695, by rfl⟩ : syracuseStep 4484521 = 3363391) B3363391
theorem B4140539 : Blo 1839621 4140539 := bstep (se 1 (by rfl) ⟨3105404, by rfl⟩ : syracuseStep 4140539 = 6210809) B6210809
theorem B2330203 : Blo 1839621 2330203 := bstep (se 1 (by rfl) ⟨1747652, by rfl⟩ : syracuseStep 2330203 = 3495305) B3495305
theorem B4140719 : Blo 1839621 4140719 := bstep (se 1 (by rfl) ⟨3105539, by rfl⟩ : syracuseStep 4140719 = 6211079) B6211079
theorem B22400707 : Blo 1839621 22400707 := bstep (se 1 (by rfl) ⟨16800530, by rfl⟩ : syracuseStep 22400707 = 33601061) B33601061
theorem B100790081 : Blo 1839621 100790081 := bstep (se 2 (by rfl) ⟨37796280, by rfl⟩ : syracuseStep 100790081 = 75592561) B75592561
theorem B5599097 : Blo 1839621 5599097 := bstep (se 2 (by rfl) ⟨2099661, by rfl⟩ : syracuseStep 5599097 = 4199323) B4199323
theorem B17690561 : Blo 1839621 17690561 := bstep (se 2 (by rfl) ⟨6633960, by rfl⟩ : syracuseStep 17690561 = 13267921) B13267921
theorem B5238913 : Blo 1839621 5238913 := bstep (se 2 (by rfl) ⟨1964592, by rfl⟩ : syracuseStep 5238913 = 3929185) B3929185
theorem B4141367 : Blo 1839621 4141367 := bstep (se 1 (by rfl) ⟨3106025, by rfl⟩ : syracuseStep 4141367 = 6212051) B6212051
theorem B121033075 : Blo 1839621 121033075 := bstep (se 1 (by rfl) ⟨90774806, by rfl⟩ : syracuseStep 121033075 = 181549613) B181549613
theorem B4141439 : Blo 1839621 4141439 := bstep (se 1 (by rfl) ⟨3106079, by rfl⟩ : syracuseStep 4141439 = 6212159) B6212159
theorem B11792783 : Blo 1839621 11792783 := bstep (se 1 (by rfl) ⟨8844587, by rfl⟩ : syracuseStep 11792783 = 17689175) B17689175
theorem B5239255 : Blo 1839621 5239255 := bstep (se 1 (by rfl) ⟨3929441, by rfl⟩ : syracuseStep 5239255 = 7858883) B7858883
theorem B6214103 : Blo 1839621 6214103 := bstep (se 1 (by rfl) ⟨4660577, by rfl⟩ : syracuseStep 6214103 = 9321155) B9321155
theorem B689525237 : Blo 1839621 689525237 := bstep (se 5 (by rfl) ⟨32321495, by rfl⟩ : syracuseStep 689525237 = 64642991) B64642991
theorem B1839719 : Blo 1839621 1839719 := bstep (se 1 (by rfl) ⟨1379789, by rfl⟩ : syracuseStep 1839719 = 2759579) B2759579
theorem B13980275 : Blo 1839621 13980275 := bstep (se 1 (by rfl) ⟨10485206, by rfl⟩ : syracuseStep 13980275 = 20970413) B20970413
theorem B4657945 : Blo 1839621 4657945 := bstep (se 2 (by rfl) ⟨1746729, by rfl⟩ : syracuseStep 4657945 = 3493459) B3493459
theorem B1839983 : Blo 1839621 1839983 := bstep (se 1 (by rfl) ⟨1379987, by rfl⟩ : syracuseStep 1839983 = 2759975) B2759975
theorem B2487151 : Blo 1839621 2487151 := bstep (se 1 (by rfl) ⟨1865363, by rfl⟩ : syracuseStep 2487151 = 3730727) B3730727
theorem B6632317 : Blo 1839621 6632317 := bstep (se 3 (by rfl) ⟨1243559, by rfl⟩ : syracuseStep 6632317 = 2487119) B2487119
theorem B1840039 : Blo 1839621 1840039 := bstep (se 1 (by rfl) ⟨1380029, by rfl⟩ : syracuseStep 1840039 = 2760059) B2760059
theorem B1840123 : Blo 1839621 1840123 := bstep (se 1 (by rfl) ⟨1380092, by rfl⟩ : syracuseStep 1840123 = 2760185) B2760185
theorem B3929143 : Blo 1839621 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B1840191 : Blo 1839621 1840191 := bstep (se 1 (by rfl) ⟨1380143, by rfl⟩ : syracuseStep 1840191 = 2760287) B2760287
theorem B26547263 : Blo 1839621 26547263 := bstep (se 1 (by rfl) ⟨19910447, by rfl⟩ : syracuseStep 26547263 = 39820895) B39820895
theorem B4658249 : Blo 1839621 4658249 := bstep (se 2 (by rfl) ⟨1746843, by rfl⟩ : syracuseStep 4658249 = 3493687) B3493687
theorem B11195489 : Blo 1839621 11195489 := bstep (se 2 (by rfl) ⟨4198308, by rfl⟩ : syracuseStep 11195489 = 8396617) B8396617
theorem B1840335 : Blo 1839621 1840335 := bstep (se 1 (by rfl) ⟨1380251, by rfl⟩ : syracuseStep 1840335 = 2760503) B2760503
theorem B6984913 : Blo 1839621 6984913 := bstep (se 2 (by rfl) ⟨2619342, by rfl⟩ : syracuseStep 6984913 = 5238685) B5238685
theorem B2241743 : Blo 1839621 2241743 := bstep (se 1 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 2241743 = 3362615) B3362615
theorem B1840539 : Blo 1839621 1840539 := bstep (se 1 (by rfl) ⟨1380404, by rfl⟩ : syracuseStep 1840539 = 2760809) B2760809
theorem B4142663 : Blo 1839621 4142663 := bstep (se 1 (by rfl) ⟨3106997, by rfl⟩ : syracuseStep 4142663 = 6213995) B6213995
theorem B1840751 : Blo 1839621 1840751 := bstep (se 1 (by rfl) ⟨1380563, by rfl⟩ : syracuseStep 1840751 = 2761127) B2761127
theorem B1840807 : Blo 1839621 1840807 := bstep (se 1 (by rfl) ⟨1380605, by rfl⟩ : syracuseStep 1840807 = 2761211) B2761211
theorem B1840891 : Blo 1839621 1840891 := bstep (se 1 (by rfl) ⟨1380668, by rfl⟩ : syracuseStep 1840891 = 2761337) B2761337
theorem B4142843 : Blo 1839621 4142843 := bstep (se 1 (by rfl) ⟨3107132, by rfl⟩ : syracuseStep 4142843 = 6214265) B6214265
theorem B1840927 : Blo 1839621 1840927 := bstep (se 1 (by rfl) ⟨1380695, by rfl⟩ : syracuseStep 1840927 = 2761391) B2761391
theorem B1840959 : Blo 1839621 1840959 := bstep (se 1 (by rfl) ⟨1380719, by rfl⟩ : syracuseStep 1840959 = 2761439) B2761439
theorem B19896131 : Blo 1839621 19896131 := bstep (se 1 (by rfl) ⟨14922098, by rfl⟩ : syracuseStep 19896131 = 29844197) B29844197
theorem B5240713 : Blo 1839621 5240713 := bstep (se 2 (by rfl) ⟨1965267, by rfl⟩ : syracuseStep 5240713 = 3930535) B3930535
theorem B10483613 : Blo 1839621 10483613 := bstep (se 3 (by rfl) ⟨1965677, by rfl⟩ : syracuseStep 10483613 = 3931355) B3931355
theorem B6985703 : Blo 1839621 6985703 := bstep (se 1 (by rfl) ⟨5239277, by rfl⟩ : syracuseStep 6985703 = 10478555) B10478555
theorem B1841135 : Blo 1839621 1841135 := bstep (se 1 (by rfl) ⟨1380851, by rfl⟩ : syracuseStep 1841135 = 2761703) B2761703
theorem B5314585 : Blo 1839621 5314585 := bstep (se 2 (by rfl) ⟨1992969, by rfl⟩ : syracuseStep 5314585 = 3985939) B3985939
theorem B9320507 : Blo 1839621 9320507 := bstep (se 1 (by rfl) ⟨6990380, by rfl⟩ : syracuseStep 9320507 = 13980761) B13980761
theorem B5896289 : Blo 1839621 5896289 := bstep (se 2 (by rfl) ⟨2211108, by rfl⟩ : syracuseStep 5896289 = 4422217) B4422217
theorem B5240987 : Blo 1839621 5240987 := bstep (se 1 (by rfl) ⟨3930740, by rfl⟩ : syracuseStep 5240987 = 7861481) B7861481
theorem B1841307 : Blo 1839621 1841307 := bstep (se 1 (by rfl) ⟨1380980, by rfl⟩ : syracuseStep 1841307 = 2761961) B2761961
theorem B1841343 : Blo 1839621 1841343 := bstep (se 1 (by rfl) ⟨1381007, by rfl⟩ : syracuseStep 1841343 = 2762015) B2762015
theorem B4143401 : Blo 1839621 4143401 := bstep (se 2 (by rfl) ⟨1553775, by rfl⟩ : syracuseStep 4143401 = 3107551) B3107551
theorem B1841455 : Blo 1839621 1841455 := bstep (se 1 (by rfl) ⟨1381091, by rfl⟩ : syracuseStep 1841455 = 2762183) B2762183
theorem B15726959 : Blo 1839621 15726959 := bstep (se 1 (by rfl) ⟨11795219, by rfl⟩ : syracuseStep 15726959 = 23590439) B23590439
theorem B6986159 : Blo 1839621 6986159 := bstep (se 1 (by rfl) ⟨5239619, by rfl⟩ : syracuseStep 6986159 = 10479239) B10479239
theorem B23591411 : Blo 1839621 23591411 := bstep (se 1 (by rfl) ⟨17693558, by rfl⟩ : syracuseStep 23591411 = 35387117) B35387117
theorem B107633411 : Blo 1839621 107633411 := bstep (se 1 (by rfl) ⟨80725058, by rfl⟩ : syracuseStep 107633411 = 161450117) B161450117
theorem B23575313 : Blo 1839621 23575313 := bstep (se 2 (by rfl) ⟨8840742, by rfl⟩ : syracuseStep 23575313 = 17681485) B17681485
theorem B10918739 : Blo 1839621 10918739 := bstep (se 1 (by rfl) ⟨8189054, by rfl⟩ : syracuseStep 10918739 = 16378109) B16378109
theorem B4660051 : Blo 1839621 4660051 := bstep (se 1 (by rfl) ⟨3495038, by rfl⟩ : syracuseStep 4660051 = 6990077) B6990077
theorem B4660193 : Blo 1839621 4660193 := bstep (se 2 (by rfl) ⟨1747572, by rfl⟩ : syracuseStep 4660193 = 3495145) B3495145
theorem B17685485 : Blo 1839621 17685485 := bstep (se 3 (by rfl) ⟨3316028, by rfl⟩ : syracuseStep 17685485 = 6632057) B6632057
theorem B2759801 : Blo 1839621 2759801 := bstep (se 2 (by rfl) ⟨1034925, by rfl⟩ : syracuseStep 2759801 = 2069851) B2069851
theorem B2759903 : Blo 1839621 2759903 := bstep (se 1 (by rfl) ⟨2069927, by rfl⟩ : syracuseStep 2759903 = 4139855) B4139855
theorem B2759945 : Blo 1839621 2759945 := bstep (se 2 (by rfl) ⟨1034979, by rfl⟩ : syracuseStep 2759945 = 2069959) B2069959
theorem B2760047 : Blo 1839621 2760047 := bstep (se 1 (by rfl) ⟨2070035, by rfl⟩ : syracuseStep 2760047 = 4140071) B4140071
theorem B13630949 : Blo 1839621 13630949 := bstep (se 4 (by rfl) ⟨1277901, by rfl⟩ : syracuseStep 13630949 = 2555803) B2555803
theorem B2760167 : Blo 1839621 2760167 := bstep (se 1 (by rfl) ⟨2070125, by rfl⟩ : syracuseStep 2760167 = 4140251) B4140251
theorem B9321965 : Blo 1839621 9321965 := bstep (se 3 (by rfl) ⟨1747868, by rfl⟩ : syracuseStep 9321965 = 3495737) B3495737
theorem B6987343 : Blo 1839621 6987343 := bstep (se 1 (by rfl) ⟨5240507, by rfl⟩ : syracuseStep 6987343 = 10481015) B10481015
theorem B2760299 : Blo 1839621 2760299 := bstep (se 1 (by rfl) ⟨2070224, by rfl⟩ : syracuseStep 2760299 = 4140449) B4140449
theorem B3104399 : Blo 1839621 3104399 := bstep (se 1 (by rfl) ⟨2328299, by rfl⟩ : syracuseStep 3104399 = 4656599) B4656599
theorem B9322127 : Blo 1839621 9322127 := bstep (se 1 (by rfl) ⟨6991595, by rfl⟩ : syracuseStep 9322127 = 13983191) B13983191
theorem B2760425 : Blo 1839621 2760425 := bstep (se 2 (by rfl) ⟨1035159, by rfl⟩ : syracuseStep 2760425 = 2070319) B2070319
theorem B6209351 : Blo 1839621 6209351 := bstep (se 1 (by rfl) ⟨4657013, by rfl⟩ : syracuseStep 6209351 = 9314027) B9314027
theorem B2760569 : Blo 1839621 2760569 := bstep (se 2 (by rfl) ⟨1035213, by rfl⟩ : syracuseStep 2760569 = 2070427) B2070427
theorem B3104635 : Blo 1839621 3104635 := bstep (se 1 (by rfl) ⟨2328476, by rfl⟩ : syracuseStep 3104635 = 4656953) B4656953
theorem B6209405 : Blo 1839621 6209405 := bstep (se 3 (by rfl) ⟨1164263, by rfl⟩ : syracuseStep 6209405 = 2328527) B2328527
theorem B13983677 : Blo 1839621 13983677 := bstep (se 3 (by rfl) ⟨2621939, by rfl⟩ : syracuseStep 13983677 = 5243879) B5243879
theorem B2760671 : Blo 1839621 2760671 := bstep (se 1 (by rfl) ⟨2070503, by rfl⟩ : syracuseStep 2760671 = 4141007) B4141007
theorem B7086113 : Blo 1839621 7086113 := bstep (se 2 (by rfl) ⟨2657292, by rfl⟩ : syracuseStep 7086113 = 5314585) B5314585
theorem B4423871 : Blo 1839621 4423871 := bstep (se 1 (by rfl) ⟨3317903, by rfl⟩ : syracuseStep 4423871 = 6635807) B6635807
theorem B2212031 : Blo 1839621 2212031 := bstep (se 1 (by rfl) ⟨1659023, by rfl⟩ : syracuseStep 2212031 = 3318047) B3318047
theorem B2760911 : Blo 1839621 2760911 := bstep (se 1 (by rfl) ⟨2070683, by rfl⟩ : syracuseStep 2760911 = 4141367) B4141367
theorem B2760959 : Blo 1839621 2760959 := bstep (se 1 (by rfl) ⟨2070719, by rfl⟩ : syracuseStep 2760959 = 4141439) B4141439
theorem B3105499 : Blo 1839621 3105499 := bstep (se 1 (by rfl) ⟨2329124, by rfl⟩ : syracuseStep 3105499 = 4658249) B4658249
theorem B7463659 : Blo 1839621 7463659 := bstep (se 1 (by rfl) ⟨5597744, by rfl⟩ : syracuseStep 7463659 = 11195489) B11195489
theorem B6210593 : Blo 1839621 6210593 := bstep (se 2 (by rfl) ⟨2328972, by rfl⟩ : syracuseStep 6210593 = 4657945) B4657945
theorem B2761775 : Blo 1839621 2761775 := bstep (se 1 (by rfl) ⟨2071331, by rfl⟩ : syracuseStep 2761775 = 4142663) B4142663
theorem B10486847 : Blo 1839621 10486847 := bstep (se 1 (by rfl) ⟨7865135, by rfl⟩ : syracuseStep 10486847 = 15730271) B15730271
theorem B2761895 : Blo 1839621 2761895 := bstep (se 1 (by rfl) ⟨2071421, by rfl⟩ : syracuseStep 2761895 = 4142843) B4142843
theorem B13264087 : Blo 1839621 13264087 := bstep (se 1 (by rfl) ⟨9948065, by rfl⟩ : syracuseStep 13264087 = 19896131) B19896131
theorem B6215183 : Blo 1839621 6215183 := bstep (se 1 (by rfl) ⟨4661387, by rfl⟩ : syracuseStep 6215183 = 9322775) B9322775
theorem B6989075 : Blo 1839621 6989075 := bstep (se 1 (by rfl) ⟨5241806, by rfl⟩ : syracuseStep 6989075 = 10483613) B10483613
theorem B10487303 : Blo 1839621 10487303 := bstep (se 1 (by rfl) ⟨7865477, by rfl⟩ : syracuseStep 10487303 = 15730955) B15730955
theorem B2762267 : Blo 1839621 2762267 := bstep (se 1 (by rfl) ⟨2071700, by rfl⟩ : syracuseStep 2762267 = 4143401) B4143401
theorem B71755607 : Blo 1839621 71755607 := bstep (se 1 (by rfl) ⟨53816705, by rfl⟩ : syracuseStep 71755607 = 107633411) B107633411
theorem B35374967 : Blo 1839621 35374967 := bstep (se 1 (by rfl) ⟨26531225, by rfl⟩ : syracuseStep 35374967 = 53062451) B53062451
theorem B13264805 : Blo 1839621 13264805 := bstep (se 4 (by rfl) ⟨1243575, by rfl⟩ : syracuseStep 13264805 = 2487151) B2487151
theorem B3106795 : Blo 1839621 3106795 := bstep (se 1 (by rfl) ⟨2330096, by rfl⟩ : syracuseStep 3106795 = 4660193) B4660193
theorem B11790323 : Blo 1839621 11790323 := bstep (se 1 (by rfl) ⟨8842742, by rfl⟩ : syracuseStep 11790323 = 17685485) B17685485
theorem B9316457 : Blo 1839621 9316457 := bstep (se 2 (by rfl) ⟨3493671, by rfl⟩ : syracuseStep 9316457 = 6987343) B6987343
theorem B3106937 : Blo 1839621 3106937 := bstep (se 2 (by rfl) ⟨1165101, by rfl⟩ : syracuseStep 3106937 = 2330203) B2330203
theorem B9087299 : Blo 1839621 9087299 := bstep (se 1 (by rfl) ⟨6815474, by rfl⟩ : syracuseStep 9087299 = 13630949) B13630949
theorem B4139513 : Blo 1839621 4139513 := bstep (se 2 (by rfl) ⟨1552317, by rfl⟩ : syracuseStep 4139513 = 3104635) B3104635
theorem B67193387 : Blo 1839621 67193387 := bstep (se 1 (by rfl) ⟨50395040, by rfl⟩ : syracuseStep 67193387 = 100790081) B100790081
theorem B4139567 : Blo 1839621 4139567 := bstep (se 1 (by rfl) ⟨3104675, by rfl⟩ : syracuseStep 4139567 = 6209351) B6209351
theorem B4139603 : Blo 1839621 4139603 := bstep (se 1 (by rfl) ⟨3104702, by rfl⟩ : syracuseStep 4139603 = 6209405) B6209405
theorem B15731333 : Blo 1839621 15731333 := bstep (se 4 (by rfl) ⟨1474812, by rfl⟩ : syracuseStep 15731333 = 2949625) B2949625
theorem B4139783 : Blo 1839621 4139783 := bstep (se 1 (by rfl) ⟨3104837, by rfl⟩ : syracuseStep 4139783 = 6209675) B6209675
theorem B196578161 : Blo 1839621 196578161 := bstep (se 2 (by rfl) ⟨73716810, by rfl⟩ : syracuseStep 196578161 = 147433621) B147433621
theorem B4139999 : Blo 1839621 4139999 := bstep (se 1 (by rfl) ⟨3104999, by rfl⟩ : syracuseStep 4139999 = 6209999) B6209999
theorem B161377433 : Blo 1839621 161377433 := bstep (se 2 (by rfl) ⟨60516537, by rfl⟩ : syracuseStep 161377433 = 121033075) B121033075
theorem B4140215 : Blo 1839621 4140215 := bstep (se 1 (by rfl) ⟨3105161, by rfl⟩ : syracuseStep 4140215 = 6210323) B6210323
theorem B9948413 : Blo 1839621 9948413 := bstep (se 3 (by rfl) ⟨1865327, by rfl⟩ : syracuseStep 9948413 = 3730655) B3730655
theorem B6212861 : Blo 1839621 6212861 := bstep (se 3 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 6212861 = 2329823) B2329823
theorem B17698175 : Blo 1839621 17698175 := bstep (se 1 (by rfl) ⟨13273631, by rfl⟩ : syracuseStep 17698175 = 26547263) B26547263
theorem B4140791 : Blo 1839621 4140791 := bstep (se 1 (by rfl) ⟨3105593, by rfl⟩ : syracuseStep 4140791 = 6211187) B6211187
theorem B6213401 : Blo 1839621 6213401 := bstep (se 2 (by rfl) ⟨2330025, by rfl⟩ : syracuseStep 6213401 = 4660051) B4660051
theorem B4140863 : Blo 1839621 4140863 := bstep (se 1 (by rfl) ⟨3105647, by rfl⟩ : syracuseStep 4140863 = 6211295) B6211295
theorem B8843089 : Blo 1839621 8843089 := bstep (se 2 (by rfl) ⟨3316158, by rfl⟩ : syracuseStep 8843089 = 6632317) B6632317
theorem B4140971 : Blo 1839621 4140971 := bstep (se 1 (by rfl) ⟨3105728, by rfl⟩ : syracuseStep 4140971 = 6211457) B6211457
theorem B4657135 : Blo 1839621 4657135 := bstep (se 1 (by rfl) ⟨3492851, by rfl⟩ : syracuseStep 4657135 = 6985703) B6985703
theorem B6213671 : Blo 1839621 6213671 := bstep (se 1 (by rfl) ⟨4660253, by rfl⟩ : syracuseStep 6213671 = 9320507) B9320507
theorem B5238857 : Blo 1839621 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B3493991 : Blo 1839621 3493991 := bstep (se 1 (by rfl) ⟨2620493, by rfl⟩ : syracuseStep 3493991 = 5240987) B5240987
theorem B14921867 : Blo 1839621 14921867 := bstep (se 1 (by rfl) ⟨11191400, by rfl⟩ : syracuseStep 14921867 = 22382801) B22382801
theorem B4141331 : Blo 1839621 4141331 := bstep (se 1 (by rfl) ⟨3105998, by rfl⟩ : syracuseStep 4141331 = 6211997) B6211997
theorem B4657439 : Blo 1839621 4657439 := bstep (se 1 (by rfl) ⟨3493079, by rfl⟩ : syracuseStep 4657439 = 6986159) B6986159
theorem B4141511 : Blo 1839621 4141511 := bstep (se 1 (by rfl) ⟨3106133, by rfl⟩ : syracuseStep 4141511 = 6212267) B6212267
theorem B15716875 : Blo 1839621 15716875 := bstep (se 1 (by rfl) ⟨11787656, by rfl⟩ : syracuseStep 15716875 = 23575313) B23575313
theorem B7279159 : Blo 1839621 7279159 := bstep (se 1 (by rfl) ⟨5459369, by rfl⟩ : syracuseStep 7279159 = 10918739) B10918739
theorem B1839867 : Blo 1839621 1839867 := bstep (se 1 (by rfl) ⟨1379900, by rfl⟩ : syracuseStep 1839867 = 2759801) B2759801
theorem B4141871 : Blo 1839621 4141871 := bstep (se 1 (by rfl) ⟨3106403, by rfl⟩ : syracuseStep 4141871 = 6212807) B6212807
theorem B1839935 : Blo 1839621 1839935 := bstep (se 1 (by rfl) ⟨1379951, by rfl⟩ : syracuseStep 1839935 = 2759903) B2759903
theorem B1839963 : Blo 1839621 1839963 := bstep (se 1 (by rfl) ⟨1379972, by rfl⟩ : syracuseStep 1839963 = 2759945) B2759945
theorem B4141961 : Blo 1839621 4141961 := bstep (se 2 (by rfl) ⟨1553235, by rfl⟩ : syracuseStep 4141961 = 3106471) B3106471
theorem B1840031 : Blo 1839621 1840031 := bstep (se 1 (by rfl) ⟨1380023, by rfl⟩ : syracuseStep 1840031 = 2760047) B2760047
theorem B1840111 : Blo 1839621 1840111 := bstep (se 1 (by rfl) ⟨1380083, by rfl⟩ : syracuseStep 1840111 = 2760167) B2760167
theorem B6214643 : Blo 1839621 6214643 := bstep (se 1 (by rfl) ⟨4660982, by rfl⟩ : syracuseStep 6214643 = 9321965) B9321965
theorem B1840199 : Blo 1839621 1840199 := bstep (se 1 (by rfl) ⟨1380149, by rfl⟩ : syracuseStep 1840199 = 2760299) B2760299
theorem B2069599 : Blo 1839621 2069599 := bstep (se 1 (by rfl) ⟨1552199, by rfl⟩ : syracuseStep 2069599 = 3104399) B3104399
theorem B6214751 : Blo 1839621 6214751 := bstep (se 1 (by rfl) ⟨4661063, by rfl⟩ : syracuseStep 6214751 = 9322127) B9322127
theorem B1840283 : Blo 1839621 1840283 := bstep (se 1 (by rfl) ⟨1380212, by rfl⟩ : syracuseStep 1840283 = 2760425) B2760425
theorem B1840379 : Blo 1839621 1840379 := bstep (se 1 (by rfl) ⟨1380284, by rfl⟩ : syracuseStep 1840379 = 2760569) B2760569
theorem B3732731 : Blo 1839621 3732731 := bstep (se 1 (by rfl) ⟨2799548, by rfl⟩ : syracuseStep 3732731 = 5599097) B5599097
theorem B11793707 : Blo 1839621 11793707 := bstep (se 1 (by rfl) ⟨8845280, by rfl⟩ : syracuseStep 11793707 = 17690561) B17690561
theorem B1840447 : Blo 1839621 1840447 := bstep (se 1 (by rfl) ⟨1380335, by rfl⟩ : syracuseStep 1840447 = 2760671) B2760671
theorem B4658543 : Blo 1839621 4658543 := bstep (se 1 (by rfl) ⟨3493907, by rfl⟩ : syracuseStep 4658543 = 6987815) B6987815
theorem B1840615 : Blo 1839621 1840615 := bstep (se 1 (by rfl) ⟨1380461, by rfl⟩ : syracuseStep 1840615 = 2760923) B2760923
theorem B1840623 : Blo 1839621 1840623 := bstep (se 1 (by rfl) ⟨1380467, by rfl⟩ : syracuseStep 1840623 = 2760935) B2760935
theorem B6985217 : Blo 1839621 6985217 := bstep (se 2 (by rfl) ⟨2619456, by rfl⟩ : syracuseStep 6985217 = 5238913) B5238913
theorem B1840731 : Blo 1839621 1840731 := bstep (se 1 (by rfl) ⟨1380548, by rfl⟩ : syracuseStep 1840731 = 2761097) B2761097
theorem B7861855 : Blo 1839621 7861855 := bstep (se 1 (by rfl) ⟨5896391, by rfl⟩ : syracuseStep 7861855 = 11792783) B11792783
theorem B4142735 : Blo 1839621 4142735 := bstep (se 1 (by rfl) ⟨3107051, by rfl⟩ : syracuseStep 4142735 = 6214103) B6214103
theorem B1840795 : Blo 1839621 1840795 := bstep (se 1 (by rfl) ⟨1380596, by rfl⟩ : syracuseStep 1840795 = 2761193) B2761193
theorem B6985399 : Blo 1839621 6985399 := bstep (se 1 (by rfl) ⟨5239049, by rfl⟩ : syracuseStep 6985399 = 10478099) B10478099
theorem B4142825 : Blo 1839621 4142825 := bstep (se 2 (by rfl) ⟨1553559, by rfl⟩ : syracuseStep 4142825 = 3107119) B3107119
theorem B1840879 : Blo 1839621 1840879 := bstep (se 1 (by rfl) ⟨1380659, by rfl⟩ : syracuseStep 1840879 = 2761319) B2761319
theorem B9320183 : Blo 1839621 9320183 := bstep (se 1 (by rfl) ⟨6990137, by rfl⟩ : syracuseStep 9320183 = 13980275) B13980275
theorem B15718211 : Blo 1839621 15718211 := bstep (se 1 (by rfl) ⟨11788658, by rfl⟩ : syracuseStep 15718211 = 23577317) B23577317
theorem B1840967 : Blo 1839621 1840967 := bstep (se 1 (by rfl) ⟨1380725, by rfl⟩ : syracuseStep 1840967 = 2761451) B2761451
theorem B1840987 : Blo 1839621 1840987 := bstep (se 1 (by rfl) ⟨1380740, by rfl⟩ : syracuseStep 1840987 = 2761481) B2761481
theorem B5977981 : Blo 1839621 5977981 := bstep (se 3 (by rfl) ⟨1120871, by rfl⟩ : syracuseStep 5977981 = 2241743) B2241743
theorem B1841055 : Blo 1839621 1841055 := bstep (se 1 (by rfl) ⟨1380791, by rfl⟩ : syracuseStep 1841055 = 2761583) B2761583
theorem B6985673 : Blo 1839621 6985673 := bstep (se 2 (by rfl) ⟨2619627, by rfl⟩ : syracuseStep 6985673 = 5239255) B5239255
theorem B4659191 : Blo 1839621 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B1841223 : Blo 1839621 1841223 := bstep (se 1 (by rfl) ⟨1380917, by rfl⟩ : syracuseStep 1841223 = 2761835) B2761835
theorem B17684561 : Blo 1839621 17684561 := bstep (se 2 (by rfl) ⟨6631710, by rfl⟩ : syracuseStep 17684561 = 13263421) B13263421
theorem B1841383 : Blo 1839621 1841383 := bstep (se 1 (by rfl) ⟨1381037, by rfl⟩ : syracuseStep 1841383 = 2762075) B2762075
theorem B1841567 : Blo 1839621 1841567 := bstep (se 1 (by rfl) ⟨1381175, by rfl⟩ : syracuseStep 1841567 = 2762351) B2762351
theorem B1841615 : Blo 1839621 1841615 := bstep (se 1 (by rfl) ⟨1381211, by rfl⟩ : syracuseStep 1841615 = 2762423) B2762423
theorem B1838733965 : Blo 1839621 1838733965 := bstep (se 3 (by rfl) ⟨344762618, by rfl⟩ : syracuseStep 1838733965 = 689525237) B689525237
theorem B3930859 : Blo 1839621 3930859 := bstep (se 1 (by rfl) ⟨2948144, by rfl⟩ : syracuseStep 3930859 = 5896289) B5896289
theorem B2759495 : Blo 1839621 2759495 := bstep (se 1 (by rfl) ⟨2069621, by rfl⟩ : syracuseStep 2759495 = 4139243) B4139243
theorem B4037447 : Blo 1839621 4037447 := bstep (se 1 (by rfl) ⟨3028085, by rfl⟩ : syracuseStep 4037447 = 6056171) B6056171
theorem B9083771 : Blo 1839621 9083771 := bstep (se 1 (by rfl) ⟨6812828, by rfl⟩ : syracuseStep 9083771 = 13625657) B13625657
theorem B10484639 : Blo 1839621 10484639 := bstep (se 1 (by rfl) ⟨7863479, by rfl⟩ : syracuseStep 10484639 = 15726959) B15726959
theorem B9313217 : Blo 1839621 9313217 := bstep (se 2 (by rfl) ⟨3492456, by rfl⟩ : syracuseStep 9313217 = 6984913) B6984913
theorem B15727607 : Blo 1839621 15727607 := bstep (se 1 (by rfl) ⟨11795705, by rfl⟩ : syracuseStep 15727607 = 23591411) B23591411
theorem B2071759 : Blo 1839621 2071759 := bstep (se 1 (by rfl) ⟨1553819, by rfl⟩ : syracuseStep 2071759 = 3107639) B3107639
theorem B5979361 : Blo 1839621 5979361 := bstep (se 2 (by rfl) ⟨2242260, by rfl⟩ : syracuseStep 5979361 = 4484521) B4484521
theorem B29867609 : Blo 1839621 29867609 := bstep (se 2 (by rfl) ⟨11200353, by rfl⟩ : syracuseStep 29867609 = 22400707) B22400707
theorem B2760359 : Blo 1839621 2760359 := bstep (se 1 (by rfl) ⟨2070269, by rfl⟩ : syracuseStep 2760359 = 4140539) B4140539
theorem B13262561 : Blo 1839621 13262561 := bstep (se 2 (by rfl) ⟨4973460, by rfl⟩ : syracuseStep 13262561 = 9946921) B9946921
theorem B2760479 : Blo 1839621 2760479 := bstep (se 1 (by rfl) ⟨2070359, by rfl⟩ : syracuseStep 2760479 = 4140719) B4140719
theorem B6987617 : Blo 1839621 6987617 := bstep (se 2 (by rfl) ⟨2620356, by rfl⟩ : syracuseStep 6987617 = 5240713) B5240713
theorem B9322451 : Blo 1839621 9322451 := bstep (se 1 (by rfl) ⟨6991838, by rfl⟩ : syracuseStep 9322451 = 13983677) B13983677
theorem B2949247 : Blo 1839621 2949247 := bstep (se 1 (by rfl) ⟨2211935, by rfl⟩ : syracuseStep 2949247 = 4423871) B4423871
theorem B2760887 : Blo 1839621 2760887 := bstep (se 1 (by rfl) ⟨2070665, by rfl⟩ : syracuseStep 2760887 = 4141331) B4141331
theorem B3104959 : Blo 1839621 3104959 := bstep (se 1 (by rfl) ⟨2328719, by rfl⟩ : syracuseStep 3104959 = 4657439) B4657439
theorem B2761007 : Blo 1839621 2761007 := bstep (se 1 (by rfl) ⟨2070755, by rfl⟩ : syracuseStep 2761007 = 4141511) B4141511
theorem B5898749 : Blo 1839621 5898749 := bstep (se 3 (by rfl) ⟨1106015, by rfl⟩ : syracuseStep 5898749 = 2212031) B2212031
theorem B2761247 : Blo 1839621 2761247 := bstep (se 1 (by rfl) ⟨2070935, by rfl⟩ : syracuseStep 2761247 = 4141871) B4141871
theorem B2761307 : Blo 1839621 2761307 := bstep (se 1 (by rfl) ⟨2070980, by rfl⟩ : syracuseStep 2761307 = 4141961) B4141961
theorem B20955833 : Blo 1839621 20955833 := bstep (se 2 (by rfl) ⟨7858437, by rfl⟩ : syracuseStep 20955833 = 15716875) B15716875
theorem B3105695 : Blo 1839621 3105695 := bstep (se 1 (by rfl) ⟨2329271, by rfl⟩ : syracuseStep 3105695 = 4658543) B4658543
theorem B2761823 : Blo 1839621 2761823 := bstep (se 1 (by rfl) ⟨2071367, by rfl⟩ : syracuseStep 2761823 = 4142735) B4142735
theorem B2761883 : Blo 1839621 2761883 := bstep (se 1 (by rfl) ⟨2071412, by rfl⟩ : syracuseStep 2761883 = 4142825) B4142825
theorem B10478807 : Blo 1839621 10478807 := bstep (se 1 (by rfl) ⟨7859105, by rfl⟩ : syracuseStep 10478807 = 15718211) B15718211
theorem B20964581 : Blo 1839621 20964581 := bstep (se 4 (by rfl) ⟨1965429, by rfl⟩ : syracuseStep 20964581 = 3930859) B3930859
theorem B3106127 : Blo 1839621 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B11789707 : Blo 1839621 11789707 := bstep (se 1 (by rfl) ⟨8842280, by rfl⟩ : syracuseStep 11789707 = 17684561) B17684561
theorem B6210971 : Blo 1839621 6210971 := bstep (se 1 (by rfl) ⟨4658228, by rfl⟩ : syracuseStep 6210971 = 9316457) B9316457
theorem B2762345 : Blo 1839621 2762345 := bstep (se 2 (by rfl) ⟨1035879, by rfl⟩ : syracuseStep 2762345 = 2071759) B2071759
theorem B7972481 : Blo 1839621 7972481 := bstep (se 2 (by rfl) ⟨2989680, by rfl⟩ : syracuseStep 7972481 = 5979361) B5979361
theorem B44795591 : Blo 1839621 44795591 := bstep (se 1 (by rfl) ⟨33596693, by rfl⟩ : syracuseStep 44795591 = 67193387) B67193387
theorem B10487555 : Blo 1839621 10487555 := bstep (se 1 (by rfl) ⟨7865666, by rfl⟩ : syracuseStep 10487555 = 15731333) B15731333
theorem B6055847 : Blo 1839621 6055847 := bstep (se 1 (by rfl) ⟨4541885, by rfl⟩ : syracuseStep 6055847 = 9083771) B9083771
theorem B6989759 : Blo 1839621 6989759 := bstep (se 1 (by rfl) ⟨5242319, by rfl⟩ : syracuseStep 6989759 = 10484639) B10484639
theorem B11798783 : Blo 1839621 11798783 := bstep (se 1 (by rfl) ⟨8849087, by rfl⟩ : syracuseStep 11798783 = 17698175) B17698175
theorem B11790785 : Blo 1839621 11790785 := bstep (se 2 (by rfl) ⟨4421544, by rfl⟩ : syracuseStep 11790785 = 8843089) B8843089
theorem B8841707 : Blo 1839621 8841707 := bstep (se 1 (by rfl) ⟨6631280, by rfl⟩ : syracuseStep 8841707 = 13262561) B13262561
theorem B3492571 : Blo 1839621 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B2329327 : Blo 1839621 2329327 := bstep (se 1 (by rfl) ⟨1746995, by rfl⟩ : syracuseStep 2329327 = 3493991) B3493991
theorem B39791645 : Blo 1839621 39791645 := bstep (se 3 (by rfl) ⟨7460933, by rfl⟩ : syracuseStep 39791645 = 14921867) B14921867
theorem B4140395 : Blo 1839621 4140395 := bstep (se 1 (by rfl) ⟨3105296, by rfl⟩ : syracuseStep 4140395 = 6210593) B6210593
theorem B6991231 : Blo 1839621 6991231 := bstep (se 1 (by rfl) ⟨5243423, by rfl⟩ : syracuseStep 6991231 = 10486847) B10486847
theorem B4140665 : Blo 1839621 4140665 := bstep (se 2 (by rfl) ⟨1552749, by rfl⟩ : syracuseStep 4140665 = 3105499) B3105499
theorem B4656811 : Blo 1839621 4656811 := bstep (se 1 (by rfl) ⟨3492608, by rfl⟩ : syracuseStep 4656811 = 6985217) B6985217
theorem B6991535 : Blo 1839621 6991535 := bstep (se 1 (by rfl) ⟨5243651, by rfl⟩ : syracuseStep 6991535 = 10487303) B10487303
theorem B6213455 : Blo 1839621 6213455 := bstep (se 1 (by rfl) ⟨4660091, by rfl⟩ : syracuseStep 6213455 = 9320183) B9320183
theorem B47837071 : Blo 1839621 47837071 := bstep (se 1 (by rfl) ⟨35877803, by rfl⟩ : syracuseStep 47837071 = 71755607) B71755607
theorem B8843203 : Blo 1839621 8843203 := bstep (se 1 (by rfl) ⟨6632402, by rfl⟩ : syracuseStep 8843203 = 13264805) B13264805
theorem B4657115 : Blo 1839621 4657115 := bstep (se 1 (by rfl) ⟨3492836, by rfl⟩ : syracuseStep 4657115 = 6985673) B6985673
theorem B7860215 : Blo 1839621 7860215 := bstep (se 1 (by rfl) ⟨5895161, by rfl⟩ : syracuseStep 7860215 = 11790323) B11790323
theorem B6058199 : Blo 1839621 6058199 := bstep (se 1 (by rfl) ⟨4543649, by rfl⟩ : syracuseStep 6058199 = 9087299) B9087299
theorem B1225822643 : Blo 1839621 1225822643 := bstep (se 1 (by rfl) ⟨919366982, by rfl⟩ : syracuseStep 1225822643 = 1838733965) B1838733965
theorem B1839663 : Blo 1839621 1839663 := bstep (se 1 (by rfl) ⟨1379747, by rfl⟩ : syracuseStep 1839663 = 2759495) B2759495
theorem B2691631 : Blo 1839621 2691631 := bstep (se 1 (by rfl) ⟨2018723, by rfl⟩ : syracuseStep 2691631 = 4037447) B4037447
theorem B131052107 : Blo 1839621 131052107 := bstep (se 1 (by rfl) ⟨98289080, by rfl⟩ : syracuseStep 131052107 = 196578161) B196578161
theorem B10482473 : Blo 1839621 10482473 := bstep (se 2 (by rfl) ⟨3930927, by rfl⟩ : syracuseStep 10482473 = 7861855) B7861855
theorem B6632275 : Blo 1839621 6632275 := bstep (se 1 (by rfl) ⟨4974206, by rfl⟩ : syracuseStep 6632275 = 9948413) B9948413
theorem B4141907 : Blo 1839621 4141907 := bstep (se 1 (by rfl) ⟨3106430, by rfl⟩ : syracuseStep 4141907 = 6212861) B6212861
theorem B19911739 : Blo 1839621 19911739 := bstep (se 1 (by rfl) ⟨14933804, by rfl⟩ : syracuseStep 19911739 = 29867609) B29867609
theorem B1840239 : Blo 1839621 1840239 := bstep (se 1 (by rfl) ⟨1380179, by rfl⟩ : syracuseStep 1840239 = 2760359) B2760359
theorem B4142267 : Blo 1839621 4142267 := bstep (se 1 (by rfl) ⟨3106700, by rfl⟩ : syracuseStep 4142267 = 6213401) B6213401
theorem B1840319 : Blo 1839621 1840319 := bstep (se 1 (by rfl) ⟨1380239, by rfl⟩ : syracuseStep 1840319 = 2760479) B2760479
theorem B4658411 : Blo 1839621 4658411 := bstep (se 1 (by rfl) ⟨3493808, by rfl⟩ : syracuseStep 4658411 = 6987617) B6987617
theorem B4142393 : Blo 1839621 4142393 := bstep (se 2 (by rfl) ⟨1553397, by rfl⟩ : syracuseStep 4142393 = 3106795) B3106795
theorem B6214967 : Blo 1839621 6214967 := bstep (se 1 (by rfl) ⟨4661225, by rfl⟩ : syracuseStep 6214967 = 9322451) B9322451
theorem B4724075 : Blo 1839621 4724075 := bstep (se 1 (by rfl) ⟨3543056, by rfl⟩ : syracuseStep 4724075 = 7086113) B7086113
theorem B4142447 : Blo 1839621 4142447 := bstep (se 1 (by rfl) ⟨3106835, by rfl⟩ : syracuseStep 4142447 = 6213671) B6213671
theorem B1840607 : Blo 1839621 1840607 := bstep (se 1 (by rfl) ⟨1380455, by rfl⟩ : syracuseStep 1840607 = 2760911) B2760911
theorem B1840639 : Blo 1839621 1840639 := bstep (se 1 (by rfl) ⟨1380479, by rfl⟩ : syracuseStep 1840639 = 2760959) B2760959
theorem B4143095 : Blo 1839621 4143095 := bstep (se 1 (by rfl) ⟨3107321, by rfl⟩ : syracuseStep 4143095 = 6214643) B6214643
theorem B1841183 : Blo 1839621 1841183 := bstep (se 1 (by rfl) ⟨1380887, by rfl⟩ : syracuseStep 1841183 = 2761775) B2761775
theorem B4143167 : Blo 1839621 4143167 := bstep (se 1 (by rfl) ⟨3107375, by rfl⟩ : syracuseStep 4143167 = 6214751) B6214751
theorem B9705545 : Blo 1839621 9705545 := bstep (se 2 (by rfl) ⟨3639579, by rfl⟩ : syracuseStep 9705545 = 7279159) B7279159
theorem B1841263 : Blo 1839621 1841263 := bstep (se 1 (by rfl) ⟨1380947, by rfl⟩ : syracuseStep 1841263 = 2761895) B2761895
theorem B2488487 : Blo 1839621 2488487 := bstep (se 1 (by rfl) ⟨1866365, by rfl⟩ : syracuseStep 2488487 = 3732731) B3732731
theorem B4659383 : Blo 1839621 4659383 := bstep (se 1 (by rfl) ⟨3494537, by rfl⟩ : syracuseStep 4659383 = 6989075) B6989075
theorem B7862471 : Blo 1839621 7862471 := bstep (se 1 (by rfl) ⟨5896853, by rfl⟩ : syracuseStep 7862471 = 11793707) B11793707
theorem B9951545 : Blo 1839621 9951545 := bstep (se 2 (by rfl) ⟨3731829, by rfl⟩ : syracuseStep 9951545 = 7463659) B7463659
theorem B4143455 : Blo 1839621 4143455 := bstep (se 1 (by rfl) ⟨3107591, by rfl⟩ : syracuseStep 4143455 = 6215183) B6215183
theorem B1841511 : Blo 1839621 1841511 := bstep (se 1 (by rfl) ⟨1381133, by rfl⟩ : syracuseStep 1841511 = 2762267) B2762267
theorem B23583311 : Blo 1839621 23583311 := bstep (se 1 (by rfl) ⟨17687483, by rfl⟩ : syracuseStep 23583311 = 35374967) B35374967
theorem B2071291 : Blo 1839621 2071291 := bstep (se 1 (by rfl) ⟨1553468, by rfl⟩ : syracuseStep 2071291 = 3106937) B3106937
theorem B2759465 : Blo 1839621 2759465 := bstep (se 2 (by rfl) ⟨1034799, by rfl⟩ : syracuseStep 2759465 = 2069599) B2069599
theorem B17685449 : Blo 1839621 17685449 := bstep (se 2 (by rfl) ⟨6632043, by rfl⟩ : syracuseStep 17685449 = 13264087) B13264087
theorem B2759675 : Blo 1839621 2759675 := bstep (se 1 (by rfl) ⟨2069756, by rfl⟩ : syracuseStep 2759675 = 4139513) B4139513
theorem B2759711 : Blo 1839621 2759711 := bstep (se 1 (by rfl) ⟨2069783, by rfl⟩ : syracuseStep 2759711 = 4139567) B4139567
theorem B2759735 : Blo 1839621 2759735 := bstep (se 1 (by rfl) ⟨2069801, by rfl⟩ : syracuseStep 2759735 = 4139603) B4139603
theorem B2759855 : Blo 1839621 2759855 := bstep (se 1 (by rfl) ⟨2069891, by rfl⟩ : syracuseStep 2759855 = 4139783) B4139783
theorem B6208811 : Blo 1839621 6208811 := bstep (se 1 (by rfl) ⟨4656608, by rfl⟩ : syracuseStep 6208811 = 9313217) B9313217
theorem B2759999 : Blo 1839621 2759999 := bstep (se 1 (by rfl) ⟨2069999, by rfl⟩ : syracuseStep 2759999 = 4139999) B4139999
theorem B31882565 : Blo 1839621 31882565 := bstep (se 4 (by rfl) ⟨2988990, by rfl⟩ : syracuseStep 31882565 = 5977981) B5977981
theorem B10485071 : Blo 1839621 10485071 := bstep (se 1 (by rfl) ⟨7863803, by rfl⟩ : syracuseStep 10485071 = 15727607) B15727607
theorem B107584955 : Blo 1839621 107584955 := bstep (se 1 (by rfl) ⟨80688716, by rfl⟩ : syracuseStep 107584955 = 161377433) B161377433
theorem B2760143 : Blo 1839621 2760143 := bstep (se 1 (by rfl) ⟨2070107, by rfl⟩ : syracuseStep 2760143 = 4140215) B4140215
theorem B9313865 : Blo 1839621 9313865 := bstep (se 2 (by rfl) ⟨3492699, by rfl⟩ : syracuseStep 9313865 = 6985399) B6985399
theorem B2760527 : Blo 1839621 2760527 := bstep (se 1 (by rfl) ⟨2070395, by rfl⟩ : syracuseStep 2760527 = 4140791) B4140791
theorem B2760575 : Blo 1839621 2760575 := bstep (se 1 (by rfl) ⟨2070431, by rfl⟩ : syracuseStep 2760575 = 4140863) B4140863
theorem B2760647 : Blo 1839621 2760647 := bstep (se 1 (by rfl) ⟨2070485, by rfl⟩ : syracuseStep 2760647 = 4140971) B4140971
theorem B6209513 : Blo 1839621 6209513 := bstep (se 2 (by rfl) ⟨2328567, by rfl⟩ : syracuseStep 6209513 = 4657135) B4657135
theorem B3932329 : Blo 1839621 3932329 := bstep (se 2 (by rfl) ⟨1474623, by rfl⟩ : syracuseStep 3932329 = 2949247) B2949247
theorem B87368071 : Blo 1839621 87368071 := bstep (se 1 (by rfl) ⟨65526053, by rfl⟩ : syracuseStep 87368071 = 131052107) B131052107
theorem B6988315 : Blo 1839621 6988315 := bstep (se 1 (by rfl) ⟨5241236, by rfl⟩ : syracuseStep 6988315 = 10482473) B10482473
theorem B2761271 : Blo 1839621 2761271 := bstep (se 1 (by rfl) ⟨2070953, by rfl⟩ : syracuseStep 2761271 = 4141907) B4141907
theorem B16155197 : Blo 1839621 16155197 := bstep (se 3 (by rfl) ⟨3029099, by rfl⟩ : syracuseStep 16155197 = 6058199) B6058199
theorem B2761511 : Blo 1839621 2761511 := bstep (se 1 (by rfl) ⟨2071133, by rfl⟩ : syracuseStep 2761511 = 4142267) B4142267
theorem B13976387 : Blo 1839621 13976387 := bstep (se 1 (by rfl) ⟨10482290, by rfl⟩ : syracuseStep 13976387 = 20964581) B20964581
theorem B3105607 : Blo 1839621 3105607 := bstep (se 1 (by rfl) ⟨2329205, by rfl⟩ : syracuseStep 3105607 = 4658411) B4658411
theorem B2761595 : Blo 1839621 2761595 := bstep (se 1 (by rfl) ⟨2071196, by rfl⟩ : syracuseStep 2761595 = 4142393) B4142393
theorem B2761631 : Blo 1839621 2761631 := bstep (se 1 (by rfl) ⟨2071223, by rfl⟩ : syracuseStep 2761631 = 4142447) B4142447
theorem B3105769 : Blo 1839621 3105769 := bstep (se 2 (by rfl) ⟨1164663, by rfl⟩ : syracuseStep 3105769 = 2329327) B2329327
theorem B2761721 : Blo 1839621 2761721 := bstep (se 2 (by rfl) ⟨1035645, by rfl⟩ : syracuseStep 2761721 = 2071291) B2071291
theorem B15729997 : Blo 1839621 15729997 := bstep (se 3 (by rfl) ⟨2949374, by rfl⟩ : syracuseStep 15729997 = 5898749) B5898749
theorem B2762063 : Blo 1839621 2762063 := bstep (se 1 (by rfl) ⟨2071547, by rfl⟩ : syracuseStep 2762063 = 4143095) B4143095
theorem B2762111 : Blo 1839621 2762111 := bstep (se 1 (by rfl) ⟨2071583, by rfl⟩ : syracuseStep 2762111 = 4143167) B4143167
theorem B3106255 : Blo 1839621 3106255 := bstep (se 1 (by rfl) ⟨2329691, by rfl⟩ : syracuseStep 3106255 = 4659383) B4659383
theorem B7865855 : Blo 1839621 7865855 := bstep (se 1 (by rfl) ⟨5899391, by rfl⟩ : syracuseStep 7865855 = 11798783) B11798783
theorem B2762303 : Blo 1839621 2762303 := bstep (se 1 (by rfl) ⟨2071727, by rfl⟩ : syracuseStep 2762303 = 4143455) B4143455
theorem B15722207 : Blo 1839621 15722207 := bstep (se 1 (by rfl) ⟨11791655, by rfl⟩ : syracuseStep 15722207 = 23583311) B23583311
theorem B26543861 : Blo 1839621 26543861 := bstep (se 5 (by rfl) ⟨1244243, by rfl⟩ : syracuseStep 26543861 = 2488487) B2488487
theorem B11790299 : Blo 1839621 11790299 := bstep (se 1 (by rfl) ⟨8842724, by rfl⟩ : syracuseStep 11790299 = 17685449) B17685449
theorem B26527763 : Blo 1839621 26527763 := bstep (se 1 (by rfl) ⟨19895822, by rfl⟩ : syracuseStep 26527763 = 39791645) B39791645
theorem B4139207 : Blo 1839621 4139207 := bstep (se 1 (by rfl) ⟨3104405, by rfl⟩ : syracuseStep 4139207 = 6208811) B6208811
theorem B6990047 : Blo 1839621 6990047 := bstep (se 1 (by rfl) ⟨5242535, by rfl⟩ : syracuseStep 6990047 = 10485071) B10485071
theorem B71723303 : Blo 1839621 71723303 := bstep (se 1 (by rfl) ⟨53792477, by rfl⟩ : syracuseStep 71723303 = 107584955) B107584955
theorem B11790937 : Blo 1839621 11790937 := bstep (se 2 (by rfl) ⟨4421601, by rfl⟩ : syracuseStep 11790937 = 8843203) B8843203
theorem B4139675 : Blo 1839621 4139675 := bstep (se 1 (by rfl) ⟨3104756, by rfl⟩ : syracuseStep 4139675 = 6209513) B6209513
theorem B14355365 : Blo 1839621 14355365 := bstep (se 4 (by rfl) ⟨1345815, by rfl⟩ : syracuseStep 14355365 = 2691631) B2691631
theorem B4139945 : Blo 1839621 4139945 := bstep (se 2 (by rfl) ⟨1552479, by rfl⟩ : syracuseStep 4139945 = 3104959) B3104959
theorem B13970555 : Blo 1839621 13970555 := bstep (se 1 (by rfl) ⟨10477916, by rfl⟩ : syracuseStep 13970555 = 20955833) B20955833
theorem B26537453 : Blo 1839621 26537453 := bstep (se 3 (by rfl) ⟨4975772, by rfl⟩ : syracuseStep 26537453 = 9951545) B9951545
theorem B3149383 : Blo 1839621 3149383 := bstep (se 1 (by rfl) ⟨2362037, by rfl⟩ : syracuseStep 3149383 = 4724075) B4724075
theorem B4140647 : Blo 1839621 4140647 := bstep (se 1 (by rfl) ⟨3105485, by rfl⟩ : syracuseStep 4140647 = 6210971) B6210971
theorem B4656761 : Blo 1839621 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B8843033 : Blo 1839621 8843033 := bstep (se 2 (by rfl) ⟨3316137, by rfl⟩ : syracuseStep 8843033 = 6632275) B6632275
theorem B29863727 : Blo 1839621 29863727 := bstep (se 1 (by rfl) ⟨22397795, by rfl⟩ : syracuseStep 29863727 = 44795591) B44795591
theorem B6991703 : Blo 1839621 6991703 := bstep (se 1 (by rfl) ⟨5243777, by rfl⟩ : syracuseStep 6991703 = 10487555) B10487555
theorem B7860523 : Blo 1839621 7860523 := bstep (se 1 (by rfl) ⟨5895392, by rfl⟩ : syracuseStep 7860523 = 11790785) B11790785
theorem B5894471 : Blo 1839621 5894471 := bstep (se 1 (by rfl) ⟨4420853, by rfl⟩ : syracuseStep 5894471 = 8841707) B8841707
theorem B1839643 : Blo 1839621 1839643 := bstep (se 1 (by rfl) ⟨1379732, by rfl⟩ : syracuseStep 1839643 = 2759465) B2759465
theorem B1839783 : Blo 1839621 1839783 := bstep (se 1 (by rfl) ⟨1379837, by rfl⟩ : syracuseStep 1839783 = 2759675) B2759675
theorem B1839807 : Blo 1839621 1839807 := bstep (se 1 (by rfl) ⟨1379855, by rfl⟩ : syracuseStep 1839807 = 2759711) B2759711
theorem B1839823 : Blo 1839621 1839823 := bstep (se 1 (by rfl) ⟨1379867, by rfl⟩ : syracuseStep 1839823 = 2759735) B2759735
theorem B1839903 : Blo 1839621 1839903 := bstep (se 1 (by rfl) ⟨1379927, by rfl⟩ : syracuseStep 1839903 = 2759855) B2759855
theorem B1839999 : Blo 1839621 1839999 := bstep (se 1 (by rfl) ⟨1379999, by rfl⟩ : syracuseStep 1839999 = 2759999) B2759999
theorem B21255043 : Blo 1839621 21255043 := bstep (se 1 (by rfl) ⟨15941282, by rfl⟩ : syracuseStep 21255043 = 31882565) B31882565
theorem B1840095 : Blo 1839621 1840095 := bstep (se 1 (by rfl) ⟨1380071, by rfl⟩ : syracuseStep 1840095 = 2760143) B2760143
theorem B1840351 : Blo 1839621 1840351 := bstep (se 1 (by rfl) ⟨1380263, by rfl⟩ : syracuseStep 1840351 = 2760527) B2760527
theorem B4142303 : Blo 1839621 4142303 := bstep (se 1 (by rfl) ⟨3106727, by rfl⟩ : syracuseStep 4142303 = 6213455) B6213455
theorem B1840383 : Blo 1839621 1840383 := bstep (se 1 (by rfl) ⟨1380287, by rfl⟩ : syracuseStep 1840383 = 2760575) B2760575
theorem B1840431 : Blo 1839621 1840431 := bstep (se 1 (by rfl) ⟨1380323, by rfl⟩ : syracuseStep 1840431 = 2760647) B2760647
theorem B5240143 : Blo 1839621 5240143 := bstep (se 1 (by rfl) ⟨3930107, by rfl⟩ : syracuseStep 5240143 = 7860215) B7860215
theorem B1840591 : Blo 1839621 1840591 := bstep (se 1 (by rfl) ⟨1380443, by rfl⟩ : syracuseStep 1840591 = 2760887) B2760887
theorem B1840671 : Blo 1839621 1840671 := bstep (se 1 (by rfl) ⟨1380503, by rfl⟩ : syracuseStep 1840671 = 2761007) B2761007
theorem B817215095 : Blo 1839621 817215095 := bstep (se 1 (by rfl) ⟨612911321, by rfl⟩ : syracuseStep 817215095 = 1225822643) B1225822643
theorem B1840831 : Blo 1839621 1840831 := bstep (se 1 (by rfl) ⟨1380623, by rfl⟩ : syracuseStep 1840831 = 2761247) B2761247
theorem B1840871 : Blo 1839621 1840871 := bstep (se 1 (by rfl) ⟨1380653, by rfl⟩ : syracuseStep 1840871 = 2761307) B2761307
theorem B2070463 : Blo 1839621 2070463 := bstep (se 1 (by rfl) ⟨1552847, by rfl⟩ : syracuseStep 2070463 = 3105695) B3105695
theorem B1841215 : Blo 1839621 1841215 := bstep (se 1 (by rfl) ⟨1380911, by rfl⟩ : syracuseStep 1841215 = 2761823) B2761823
theorem B1841255 : Blo 1839621 1841255 := bstep (se 1 (by rfl) ⟨1380941, by rfl⟩ : syracuseStep 1841255 = 2761883) B2761883
theorem B6985871 : Blo 1839621 6985871 := bstep (se 1 (by rfl) ⟨5239403, by rfl⟩ : syracuseStep 6985871 = 10478807) B10478807
theorem B4143311 : Blo 1839621 4143311 := bstep (se 1 (by rfl) ⟨3107483, by rfl⟩ : syracuseStep 4143311 = 6214967) B6214967
theorem B2070751 : Blo 1839621 2070751 := bstep (se 1 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 2070751 = 3106127) B3106127
theorem B1841563 : Blo 1839621 1841563 := bstep (se 1 (by rfl) ⟨1381172, by rfl⟩ : syracuseStep 1841563 = 2762345) B2762345
theorem B5314987 : Blo 1839621 5314987 := bstep (se 1 (by rfl) ⟨3986240, by rfl⟩ : syracuseStep 5314987 = 7972481) B7972481
theorem B4037231 : Blo 1839621 4037231 := bstep (se 1 (by rfl) ⟨3027923, by rfl⟩ : syracuseStep 4037231 = 6055847) B6055847
theorem B4659839 : Blo 1839621 4659839 := bstep (se 1 (by rfl) ⟨3494879, by rfl⟩ : syracuseStep 4659839 = 6989759) B6989759
theorem B6470363 : Blo 1839621 6470363 := bstep (se 1 (by rfl) ⟨4852772, by rfl⟩ : syracuseStep 6470363 = 9705545) B9705545
theorem B26548985 : Blo 1839621 26548985 := bstep (se 2 (by rfl) ⟨9955869, by rfl⟩ : syracuseStep 26548985 = 19911739) B19911739
theorem B5241647 : Blo 1839621 5241647 := bstep (se 1 (by rfl) ⟨3931235, by rfl⟩ : syracuseStep 5241647 = 7862471) B7862471
theorem B9321641 : Blo 1839621 9321641 := bstep (se 2 (by rfl) ⟨3495615, by rfl⟩ : syracuseStep 9321641 = 6991231) B6991231
theorem B15719609 : Blo 1839621 15719609 := bstep (se 2 (by rfl) ⟨5894853, by rfl⟩ : syracuseStep 15719609 = 11789707) B11789707
theorem B6209081 : Blo 1839621 6209081 := bstep (se 2 (by rfl) ⟨2328405, by rfl⟩ : syracuseStep 6209081 = 4656811) B4656811
theorem B2760263 : Blo 1839621 2760263 := bstep (se 1 (by rfl) ⟨2070197, by rfl⟩ : syracuseStep 2760263 = 4140395) B4140395
theorem B6209243 : Blo 1839621 6209243 := bstep (se 1 (by rfl) ⟨4656932, by rfl⟩ : syracuseStep 6209243 = 9313865) B9313865
theorem B2760443 : Blo 1839621 2760443 := bstep (se 1 (by rfl) ⟨2070332, by rfl⟩ : syracuseStep 2760443 = 4140665) B4140665
theorem B4661023 : Blo 1839621 4661023 := bstep (se 1 (by rfl) ⟨3495767, by rfl⟩ : syracuseStep 4661023 = 6991535) B6991535
theorem B63782761 : Blo 1839621 63782761 := bstep (se 2 (by rfl) ⟨23918535, by rfl⟩ : syracuseStep 63782761 = 47837071) B47837071
theorem B3104743 : Blo 1839621 3104743 := bstep (se 1 (by rfl) ⟨2328557, by rfl⟩ : syracuseStep 3104743 = 4657115) B4657115
theorem B5243105 : Blo 1839621 5243105 := bstep (se 2 (by rfl) ⟨1966164, by rfl⟩ : syracuseStep 5243105 = 3932329) B3932329
theorem B2761001 : Blo 1839621 2761001 := bstep (se 2 (by rfl) ⟨1035375, by rfl⟩ : syracuseStep 2761001 = 2070751) B2070751
theorem B116490761 : Blo 1839621 116490761 := bstep (se 2 (by rfl) ⟨43684035, by rfl⟩ : syracuseStep 116490761 = 87368071) B87368071
theorem B15721249 : Blo 1839621 15721249 := bstep (se 2 (by rfl) ⟨5895468, by rfl⟩ : syracuseStep 15721249 = 11790937) B11790937
theorem B2761535 : Blo 1839621 2761535 := bstep (se 1 (by rfl) ⟨2071151, by rfl⟩ : syracuseStep 2761535 = 4142303) B4142303
theorem B5243903 : Blo 1839621 5243903 := bstep (se 1 (by rfl) ⟨3932927, by rfl⟩ : syracuseStep 5243903 = 7865855) B7865855
theorem B544810063 : Blo 1839621 544810063 := bstep (se 1 (by rfl) ⟨408607547, by rfl⟩ : syracuseStep 544810063 = 817215095) B817215095
theorem B17695907 : Blo 1839621 17695907 := bstep (se 1 (by rfl) ⟨13271930, by rfl⟩ : syracuseStep 17695907 = 26543861) B26543861
theorem B2762207 : Blo 1839621 2762207 := bstep (se 1 (by rfl) ⟨2071655, by rfl⟩ : syracuseStep 2762207 = 4143311) B4143311
theorem B3106559 : Blo 1839621 3106559 := bstep (se 1 (by rfl) ⟨2329919, by rfl⟩ : syracuseStep 3106559 = 4659839) B4659839
theorem B20973329 : Blo 1839621 20973329 := bstep (se 2 (by rfl) ⟨7864998, by rfl⟩ : syracuseStep 20973329 = 15729997) B15729997
theorem B10479739 : Blo 1839621 10479739 := bstep (se 1 (by rfl) ⟨7859804, by rfl⟩ : syracuseStep 10479739 = 15719609) B15719609
theorem B28346597 : Blo 1839621 28346597 := bstep (se 4 (by rfl) ⟨2657493, by rfl⟩ : syracuseStep 28346597 = 5314987) B5314987
theorem B4139387 : Blo 1839621 4139387 := bstep (se 1 (by rfl) ⟨3104540, by rfl⟩ : syracuseStep 4139387 = 6209081) B6209081
theorem B85043681 : Blo 1839621 85043681 := bstep (se 2 (by rfl) ⟨31891380, by rfl⟩ : syracuseStep 85043681 = 63782761) B63782761
theorem B4139495 : Blo 1839621 4139495 := bstep (se 1 (by rfl) ⟨3104621, by rfl⟩ : syracuseStep 4139495 = 6209243) B6209243
theorem B19909151 : Blo 1839621 19909151 := bstep (se 1 (by rfl) ⟨14931863, by rfl⟩ : syracuseStep 19909151 = 29863727) B29863727
theorem B4139657 : Blo 1839621 4139657 := bstep (se 2 (by rfl) ⟨1552371, by rfl⟩ : syracuseStep 4139657 = 3104743) B3104743
theorem B70740701 : Blo 1839621 70740701 := bstep (se 3 (by rfl) ⟨13263881, by rfl⟩ : syracuseStep 70740701 = 26527763) B26527763
theorem B10480697 : Blo 1839621 10480697 := bstep (se 2 (by rfl) ⟨3930261, by rfl⟩ : syracuseStep 10480697 = 7860523) B7860523
theorem B9317591 : Blo 1839621 9317591 := bstep (se 1 (by rfl) ⟨6988193, by rfl⟩ : syracuseStep 9317591 = 13976387) B13976387
theorem B9317753 : Blo 1839621 9317753 := bstep (se 2 (by rfl) ⟨3494157, by rfl⟩ : syracuseStep 9317753 = 6988315) B6988315
theorem B4140809 : Blo 1839621 4140809 := bstep (se 2 (by rfl) ⟨1552803, by rfl⟩ : syracuseStep 4140809 = 3105607) B3105607
theorem B10481471 : Blo 1839621 10481471 := bstep (se 1 (by rfl) ⟨7861103, by rfl⟩ : syracuseStep 10481471 = 15722207) B15722207
theorem B28340057 : Blo 1839621 28340057 := bstep (se 2 (by rfl) ⟨10627521, by rfl⟩ : syracuseStep 28340057 = 21255043) B21255043
theorem B4141025 : Blo 1839621 4141025 := bstep (se 2 (by rfl) ⟨1552884, by rfl⟩ : syracuseStep 4141025 = 3105769) B3105769
theorem B7860199 : Blo 1839621 7860199 := bstep (se 1 (by rfl) ⟨5895149, by rfl⟩ : syracuseStep 7860199 = 11790299) B11790299
theorem B4657247 : Blo 1839621 4657247 := bstep (se 1 (by rfl) ⟨3492935, by rfl⟩ : syracuseStep 4657247 = 6985871) B6985871
theorem B2691487 : Blo 1839621 2691487 := bstep (se 1 (by rfl) ⟨2018615, by rfl⟩ : syracuseStep 2691487 = 4037231) B4037231
theorem B4313575 : Blo 1839621 4313575 := bstep (se 1 (by rfl) ⟨3235181, by rfl⟩ : syracuseStep 4313575 = 6470363) B6470363
theorem B17699323 : Blo 1839621 17699323 := bstep (se 1 (by rfl) ⟨13274492, by rfl⟩ : syracuseStep 17699323 = 26548985) B26548985
theorem B3494431 : Blo 1839621 3494431 := bstep (se 1 (by rfl) ⟨2620823, by rfl⟩ : syracuseStep 3494431 = 5241647) B5241647
theorem B4141673 : Blo 1839621 4141673 := bstep (se 2 (by rfl) ⟨1553127, by rfl⟩ : syracuseStep 4141673 = 3106255) B3106255
theorem B4199177 : Blo 1839621 4199177 := bstep (se 2 (by rfl) ⟨1574691, by rfl⟩ : syracuseStep 4199177 = 3149383) B3149383
theorem B6214427 : Blo 1839621 6214427 := bstep (se 1 (by rfl) ⟨4660820, by rfl⟩ : syracuseStep 6214427 = 9321641) B9321641
theorem B17691635 : Blo 1839621 17691635 := bstep (se 1 (by rfl) ⟨13268726, by rfl⟩ : syracuseStep 17691635 = 26537453) B26537453
theorem B6214697 : Blo 1839621 6214697 := bstep (se 2 (by rfl) ⟨2330511, by rfl⟩ : syracuseStep 6214697 = 4661023) B4661023
theorem B1840175 : Blo 1839621 1840175 := bstep (se 1 (by rfl) ⟨1380131, by rfl⟩ : syracuseStep 1840175 = 2760263) B2760263
theorem B1840295 : Blo 1839621 1840295 := bstep (se 1 (by rfl) ⟨1380221, by rfl⟩ : syracuseStep 1840295 = 2760443) B2760443
theorem B5895355 : Blo 1839621 5895355 := bstep (se 1 (by rfl) ⟨4421516, by rfl⟩ : syracuseStep 5895355 = 8843033) B8843033
theorem B3929647 : Blo 1839621 3929647 := bstep (se 1 (by rfl) ⟨2947235, by rfl⟩ : syracuseStep 3929647 = 5894471) B5894471
theorem B1840847 : Blo 1839621 1840847 := bstep (se 1 (by rfl) ⟨1380635, by rfl⟩ : syracuseStep 1840847 = 2761271) B2761271
theorem B10770131 : Blo 1839621 10770131 := bstep (se 1 (by rfl) ⟨8077598, by rfl⟩ : syracuseStep 10770131 = 16155197) B16155197
theorem B1841007 : Blo 1839621 1841007 := bstep (se 1 (by rfl) ⟨1380755, by rfl⟩ : syracuseStep 1841007 = 2761511) B2761511
theorem B1841063 : Blo 1839621 1841063 := bstep (se 1 (by rfl) ⟨1380797, by rfl⟩ : syracuseStep 1841063 = 2761595) B2761595
theorem B1841087 : Blo 1839621 1841087 := bstep (se 1 (by rfl) ⟨1380815, by rfl⟩ : syracuseStep 1841087 = 2761631) B2761631
theorem B1841147 : Blo 1839621 1841147 := bstep (se 1 (by rfl) ⟨1380860, by rfl⟩ : syracuseStep 1841147 = 2761721) B2761721
theorem B1841375 : Blo 1839621 1841375 := bstep (se 1 (by rfl) ⟨1381031, by rfl⟩ : syracuseStep 1841375 = 2762063) B2762063
theorem B1841407 : Blo 1839621 1841407 := bstep (se 1 (by rfl) ⟨1381055, by rfl⟩ : syracuseStep 1841407 = 2762111) B2762111
theorem B1841535 : Blo 1839621 1841535 := bstep (se 1 (by rfl) ⟨1381151, by rfl⟩ : syracuseStep 1841535 = 2762303) B2762303
theorem B2759471 : Blo 1839621 2759471 := bstep (se 1 (by rfl) ⟨2069603, by rfl⟩ : syracuseStep 2759471 = 4139207) B4139207
theorem B4660031 : Blo 1839621 4660031 := bstep (se 1 (by rfl) ⟨3495023, by rfl⟩ : syracuseStep 4660031 = 6990047) B6990047
theorem B47815535 : Blo 1839621 47815535 := bstep (se 1 (by rfl) ⟨35861651, by rfl⟩ : syracuseStep 47815535 = 71723303) B71723303
theorem B2759783 : Blo 1839621 2759783 := bstep (se 1 (by rfl) ⟨2069837, by rfl⟩ : syracuseStep 2759783 = 4139675) B4139675
theorem B6986857 : Blo 1839621 6986857 := bstep (se 2 (by rfl) ⟨2620071, by rfl⟩ : syracuseStep 6986857 = 5240143) B5240143
theorem B2759963 : Blo 1839621 2759963 := bstep (se 1 (by rfl) ⟨2069972, by rfl⟩ : syracuseStep 2759963 = 4139945) B4139945
theorem B9313703 : Blo 1839621 9313703 := bstep (se 1 (by rfl) ⟨6985277, by rfl⟩ : syracuseStep 9313703 = 13970555) B13970555
theorem B2760431 : Blo 1839621 2760431 := bstep (se 1 (by rfl) ⟨2070323, by rfl⟩ : syracuseStep 2760431 = 4140647) B4140647
theorem B3104507 : Blo 1839621 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B38280973 : Blo 1839621 38280973 := bstep (se 3 (by rfl) ⟨7177682, by rfl⟩ : syracuseStep 38280973 = 14355365) B14355365
theorem B4661135 : Blo 1839621 4661135 := bstep (se 1 (by rfl) ⟨3495851, by rfl⟩ : syracuseStep 4661135 = 6991703) B6991703
theorem B2760617 : Blo 1839621 2760617 := bstep (se 2 (by rfl) ⟨1035231, by rfl⟩ : syracuseStep 2760617 = 2070463) B2070463
theorem B3104831 : Blo 1839621 3104831 := bstep (se 1 (by rfl) ⟨2328623, by rfl⟩ : syracuseStep 3104831 = 4657247) B4657247
theorem B77660507 : Blo 1839621 77660507 := bstep (se 1 (by rfl) ⟨58245380, by rfl⟩ : syracuseStep 77660507 = 116490761) B116490761
theorem B2761115 : Blo 1839621 2761115 := bstep (se 1 (by rfl) ⟨2070836, by rfl⟩ : syracuseStep 2761115 = 4141673) B4141673
theorem B5751433 : Blo 1839621 5751433 := bstep (se 2 (by rfl) ⟨2156787, by rfl⟩ : syracuseStep 5751433 = 4313575) B4313575
theorem B11797271 : Blo 1839621 11797271 := bstep (se 1 (by rfl) ⟨8847953, by rfl⟩ : syracuseStep 11797271 = 17695907) B17695907
theorem B9315809 : Blo 1839621 9315809 := bstep (se 2 (by rfl) ⟨3493428, by rfl⟩ : syracuseStep 9315809 = 6986857) B6986857
theorem B13272767 : Blo 1839621 13272767 := bstep (se 1 (by rfl) ⟨9954575, by rfl⟩ : syracuseStep 13272767 = 19909151) B19909151
theorem B3106687 : Blo 1839621 3106687 := bstep (se 1 (by rfl) ⟨2330015, by rfl⟩ : syracuseStep 3106687 = 4660031) B4660031
theorem B6211727 : Blo 1839621 6211727 := bstep (se 1 (by rfl) ⟨4658795, by rfl⟩ : syracuseStep 6211727 = 9317591) B9317591
theorem B14354597 : Blo 1839621 14354597 := bstep (se 4 (by rfl) ⟨1345743, by rfl⟩ : syracuseStep 14354597 = 2691487) B2691487
theorem B75573485 : Blo 1839621 75573485 := bstep (se 3 (by rfl) ⟨14170028, by rfl⟩ : syracuseStep 75573485 = 28340057) B28340057
theorem B6211835 : Blo 1839621 6211835 := bstep (se 1 (by rfl) ⟨4658876, by rfl⟩ : syracuseStep 6211835 = 9317753) B9317753
theorem B3107423 : Blo 1839621 3107423 := bstep (se 1 (by rfl) ⟨2330567, by rfl⟩ : syracuseStep 3107423 = 4661135) B4661135
theorem B10480265 : Blo 1839621 10480265 := bstep (se 2 (by rfl) ⟨3930099, by rfl⟩ : syracuseStep 10480265 = 7860199) B7860199
theorem B726413417 : Blo 1839621 726413417 := bstep (se 2 (by rfl) ⟨272405031, by rfl⟩ : syracuseStep 726413417 = 544810063) B544810063
theorem B7860473 : Blo 1839621 7860473 := bstep (se 2 (by rfl) ⟨2947677, by rfl⟩ : syracuseStep 7860473 = 5895355) B5895355
theorem B1839647 : Blo 1839621 1839647 := bstep (se 1 (by rfl) ⟨1379735, by rfl⟩ : syracuseStep 1839647 = 2759471) B2759471
theorem B5239529 : Blo 1839621 5239529 := bstep (se 2 (by rfl) ⟨1964823, by rfl⟩ : syracuseStep 5239529 = 3929647) B3929647
theorem B1839855 : Blo 1839621 1839855 := bstep (se 1 (by rfl) ⟨1379891, by rfl⟩ : syracuseStep 1839855 = 2759783) B2759783
theorem B1839975 : Blo 1839621 1839975 := bstep (se 1 (by rfl) ⟨1379981, by rfl⟩ : syracuseStep 1839975 = 2759963) B2759963
theorem B51041297 : Blo 1839621 51041297 := bstep (se 2 (by rfl) ⟨19140486, by rfl⟩ : syracuseStep 51041297 = 38280973) B38280973
theorem B1840287 : Blo 1839621 1840287 := bstep (se 1 (by rfl) ⟨1380215, by rfl⟩ : syracuseStep 1840287 = 2760431) B2760431
theorem B2069671 : Blo 1839621 2069671 := bstep (se 1 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 2069671 = 3104507) B3104507
theorem B1840411 : Blo 1839621 1840411 := bstep (se 1 (by rfl) ⟨1380308, by rfl⟩ : syracuseStep 1840411 = 2760617) B2760617
theorem B3495403 : Blo 1839621 3495403 := bstep (se 1 (by rfl) ⟨2621552, by rfl⟩ : syracuseStep 3495403 = 5243105) B5243105
theorem B13972985 : Blo 1839621 13972985 := bstep (se 2 (by rfl) ⟨5239869, by rfl⟩ : syracuseStep 13972985 = 10479739) B10479739
theorem B1840667 : Blo 1839621 1840667 := bstep (se 1 (by rfl) ⟨1380500, by rfl⟩ : syracuseStep 1840667 = 2761001) B2761001
theorem B2799451 : Blo 1839621 2799451 := bstep (se 1 (by rfl) ⟨2099588, by rfl⟩ : syracuseStep 2799451 = 4199177) B4199177
theorem B4142951 : Blo 1839621 4142951 := bstep (se 1 (by rfl) ⟨3107213, by rfl⟩ : syracuseStep 4142951 = 6214427) B6214427
theorem B1841023 : Blo 1839621 1841023 := bstep (se 1 (by rfl) ⟨1380767, by rfl⟩ : syracuseStep 1841023 = 2761535) B2761535
theorem B11794423 : Blo 1839621 11794423 := bstep (se 1 (by rfl) ⟨8845817, by rfl⟩ : syracuseStep 11794423 = 17691635) B17691635
theorem B23599097 : Blo 1839621 23599097 := bstep (se 2 (by rfl) ⟨8849661, by rfl⟩ : syracuseStep 23599097 = 17699323) B17699323
theorem B3495935 : Blo 1839621 3495935 := bstep (se 1 (by rfl) ⟨2621951, by rfl⟩ : syracuseStep 3495935 = 5243903) B5243903
theorem B4143131 : Blo 1839621 4143131 := bstep (se 1 (by rfl) ⟨3107348, by rfl⟩ : syracuseStep 4143131 = 6214697) B6214697
theorem B4659241 : Blo 1839621 4659241 := bstep (se 2 (by rfl) ⟨1747215, by rfl⟩ : syracuseStep 4659241 = 3494431) B3494431
theorem B1841471 : Blo 1839621 1841471 := bstep (se 1 (by rfl) ⟨1381103, by rfl⟩ : syracuseStep 1841471 = 2762207) B2762207
theorem B20961665 : Blo 1839621 20961665 := bstep (se 2 (by rfl) ⟨7860624, by rfl⟩ : syracuseStep 20961665 = 15721249) B15721249
theorem B2071039 : Blo 1839621 2071039 := bstep (se 1 (by rfl) ⟨1553279, by rfl⟩ : syracuseStep 2071039 = 3106559) B3106559
theorem B13982219 : Blo 1839621 13982219 := bstep (se 1 (by rfl) ⟨10486664, by rfl⟩ : syracuseStep 13982219 = 20973329) B20973329
theorem B18897731 : Blo 1839621 18897731 := bstep (se 1 (by rfl) ⟨14173298, by rfl⟩ : syracuseStep 18897731 = 28346597) B28346597
theorem B2759591 : Blo 1839621 2759591 := bstep (se 1 (by rfl) ⟨2069693, by rfl⟩ : syracuseStep 2759591 = 4139387) B4139387
theorem B56695787 : Blo 1839621 56695787 := bstep (se 1 (by rfl) ⟨42521840, by rfl⟩ : syracuseStep 56695787 = 85043681) B85043681
theorem B2759663 : Blo 1839621 2759663 := bstep (se 1 (by rfl) ⟨2069747, by rfl⟩ : syracuseStep 2759663 = 4139495) B4139495
theorem B2759771 : Blo 1839621 2759771 := bstep (se 1 (by rfl) ⟨2069828, by rfl⟩ : syracuseStep 2759771 = 4139657) B4139657
theorem B47160467 : Blo 1839621 47160467 := bstep (se 1 (by rfl) ⟨35370350, by rfl⟩ : syracuseStep 47160467 = 70740701) B70740701
theorem B28720349 : Blo 1839621 28720349 := bstep (se 3 (by rfl) ⟨5385065, by rfl⟩ : syracuseStep 28720349 = 10770131) B10770131
theorem B6987131 : Blo 1839621 6987131 := bstep (se 1 (by rfl) ⟨5240348, by rfl⟩ : syracuseStep 6987131 = 10480697) B10480697
theorem B6209135 : Blo 1839621 6209135 := bstep (se 1 (by rfl) ⟨4656851, by rfl⟩ : syracuseStep 6209135 = 9313703) B9313703
theorem B127508093 : Blo 1839621 127508093 := bstep (se 3 (by rfl) ⟨23907767, by rfl⟩ : syracuseStep 127508093 = 47815535) B47815535
theorem B2760539 : Blo 1839621 2760539 := bstep (se 1 (by rfl) ⟨2070404, by rfl⟩ : syracuseStep 2760539 = 4140809) B4140809
theorem B6987647 : Blo 1839621 6987647 := bstep (se 1 (by rfl) ⟨5240735, by rfl⟩ : syracuseStep 6987647 = 10481471) B10481471
theorem B2760683 : Blo 1839621 2760683 := bstep (se 1 (by rfl) ⟨2070512, by rfl⟩ : syracuseStep 2760683 = 4141025) B4141025
theorem B136110125 : Blo 1839621 136110125 := bstep (se 3 (by rfl) ⟨25520648, by rfl⟩ : syracuseStep 136110125 = 51041297) B51041297
theorem B51773671 : Blo 1839621 51773671 := bstep (se 1 (by rfl) ⟨38830253, by rfl⟩ : syracuseStep 51773671 = 77660507) B77660507
theorem B7864847 : Blo 1839621 7864847 := bstep (se 1 (by rfl) ⟨5898635, by rfl⟩ : syracuseStep 7864847 = 11797271) B11797271
theorem B2761385 : Blo 1839621 2761385 := bstep (se 2 (by rfl) ⟨1035519, by rfl⟩ : syracuseStep 2761385 = 2071039) B2071039
theorem B7668577 : Blo 1839621 7668577 := bstep (se 2 (by rfl) ⟨2875716, by rfl⟩ : syracuseStep 7668577 = 5751433) B5751433
theorem B6210539 : Blo 1839621 6210539 := bstep (se 1 (by rfl) ⟨4657904, by rfl⟩ : syracuseStep 6210539 = 9315809) B9315809
theorem B9315323 : Blo 1839621 9315323 := bstep (se 1 (by rfl) ⟨6986492, by rfl⟩ : syracuseStep 9315323 = 13972985) B13972985
theorem B8848511 : Blo 1839621 8848511 := bstep (se 1 (by rfl) ⟨6636383, by rfl⟩ : syracuseStep 8848511 = 13272767) B13272767
theorem B2761967 : Blo 1839621 2761967 := bstep (se 1 (by rfl) ⟨2071475, by rfl⟩ : syracuseStep 2761967 = 4142951) B4142951
theorem B2762087 : Blo 1839621 2762087 := bstep (se 1 (by rfl) ⟨2071565, by rfl⟩ : syracuseStep 2762087 = 4143131) B4143131
theorem B50382323 : Blo 1839621 50382323 := bstep (se 1 (by rfl) ⟨37786742, by rfl⟩ : syracuseStep 50382323 = 75573485) B75573485
theorem B19146899 : Blo 1839621 19146899 := bstep (se 1 (by rfl) ⟨14360174, by rfl⟩ : syracuseStep 19146899 = 28720349) B28720349
theorem B4139423 : Blo 1839621 4139423 := bstep (se 1 (by rfl) ⟨3104567, by rfl⟩ : syracuseStep 4139423 = 6209135) B6209135
theorem B6212321 : Blo 1839621 6212321 := bstep (se 2 (by rfl) ⟨2329620, by rfl⟩ : syracuseStep 6212321 = 4659241) B4659241
theorem B3493019 : Blo 1839621 3493019 := bstep (se 1 (by rfl) ⟨2619764, by rfl⟩ : syracuseStep 3493019 = 5239529) B5239529
theorem B15732731 : Blo 1839621 15732731 := bstep (se 1 (by rfl) ⟨11799548, by rfl⟩ : syracuseStep 15732731 = 23599097) B23599097
theorem B2330623 : Blo 1839621 2330623 := bstep (se 1 (by rfl) ⟨1747967, by rfl⟩ : syracuseStep 2330623 = 3495935) B3495935
theorem B4141151 : Blo 1839621 4141151 := bstep (se 1 (by rfl) ⟨3105863, by rfl⟩ : syracuseStep 4141151 = 6211727) B6211727
theorem B4141223 : Blo 1839621 4141223 := bstep (se 1 (by rfl) ⟨3105917, by rfl⟩ : syracuseStep 4141223 = 6211835) B6211835
theorem B14930405 : Blo 1839621 14930405 := bstep (se 4 (by rfl) ⟨1399725, by rfl⟩ : syracuseStep 14930405 = 2799451) B2799451
theorem B1839727 : Blo 1839621 1839727 := bstep (se 1 (by rfl) ⟨1379795, by rfl⟩ : syracuseStep 1839727 = 2759591) B2759591
theorem B1839775 : Blo 1839621 1839775 := bstep (se 1 (by rfl) ⟨1379831, by rfl⟩ : syracuseStep 1839775 = 2759663) B2759663
theorem B1839847 : Blo 1839621 1839847 := bstep (se 1 (by rfl) ⟨1379885, by rfl⟩ : syracuseStep 1839847 = 2759771) B2759771
theorem B4658087 : Blo 1839621 4658087 := bstep (se 1 (by rfl) ⟨3493565, by rfl⟩ : syracuseStep 4658087 = 6987131) B6987131
theorem B85005395 : Blo 1839621 85005395 := bstep (se 1 (by rfl) ⟨63754046, by rfl⟩ : syracuseStep 85005395 = 127508093) B127508093
theorem B4142249 : Blo 1839621 4142249 := bstep (se 2 (by rfl) ⟨1553343, by rfl⟩ : syracuseStep 4142249 = 3106687) B3106687
theorem B1840359 : Blo 1839621 1840359 := bstep (se 1 (by rfl) ⟨1380269, by rfl⟩ : syracuseStep 1840359 = 2760539) B2760539
theorem B4658431 : Blo 1839621 4658431 := bstep (se 1 (by rfl) ⟨3493823, by rfl⟩ : syracuseStep 4658431 = 6987647) B6987647
theorem B1840455 : Blo 1839621 1840455 := bstep (se 1 (by rfl) ⟨1380341, by rfl⟩ : syracuseStep 1840455 = 2760683) B2760683
theorem B15725897 : Blo 1839621 15725897 := bstep (se 2 (by rfl) ⟨5897211, by rfl⟩ : syracuseStep 15725897 = 11794423) B11794423
theorem B2069887 : Blo 1839621 2069887 := bstep (se 1 (by rfl) ⟨1552415, by rfl⟩ : syracuseStep 2069887 = 3104831) B3104831
theorem B484275611 : Blo 1839621 484275611 := bstep (se 1 (by rfl) ⟨363206708, by rfl⟩ : syracuseStep 484275611 = 726413417) B726413417
theorem B5240315 : Blo 1839621 5240315 := bstep (se 1 (by rfl) ⟨3930236, by rfl⟩ : syracuseStep 5240315 = 7860473) B7860473
theorem B1840743 : Blo 1839621 1840743 := bstep (se 1 (by rfl) ⟨1380557, by rfl⟩ : syracuseStep 1840743 = 2761115) B2761115
theorem B38278925 : Blo 1839621 38278925 := bstep (se 3 (by rfl) ⟨7177298, by rfl⟩ : syracuseStep 38278925 = 14354597) B14354597
theorem B2759561 : Blo 1839621 2759561 := bstep (se 2 (by rfl) ⟨1034835, by rfl⟩ : syracuseStep 2759561 = 2069671) B2069671
theorem B13974443 : Blo 1839621 13974443 := bstep (se 1 (by rfl) ⟨10480832, by rfl⟩ : syracuseStep 13974443 = 20961665) B20961665
theorem B9321479 : Blo 1839621 9321479 := bstep (se 1 (by rfl) ⟨6991109, by rfl⟩ : syracuseStep 9321479 = 13982219) B13982219
theorem B2071615 : Blo 1839621 2071615 := bstep (se 1 (by rfl) ⟨1553711, by rfl⟩ : syracuseStep 2071615 = 3107423) B3107423
theorem B6986843 : Blo 1839621 6986843 := bstep (se 1 (by rfl) ⟨5240132, by rfl⟩ : syracuseStep 6986843 = 10480265) B10480265
theorem B12598487 : Blo 1839621 12598487 := bstep (se 1 (by rfl) ⟨9448865, by rfl⟩ : syracuseStep 12598487 = 18897731) B18897731
theorem B4660537 : Blo 1839621 4660537 := bstep (se 2 (by rfl) ⟨1747701, by rfl⟩ : syracuseStep 4660537 = 3495403) B3495403
theorem B37797191 : Blo 1839621 37797191 := bstep (se 1 (by rfl) ⟨28347893, by rfl⟩ : syracuseStep 37797191 = 56695787) B56695787
theorem B31440311 : Blo 1839621 31440311 := bstep (se 1 (by rfl) ⟨23580233, by rfl⟩ : syracuseStep 31440311 = 47160467) B47160467
theorem B2760767 : Blo 1839621 2760767 := bstep (se 1 (by rfl) ⟨2070575, by rfl⟩ : syracuseStep 2760767 = 4141151) B4141151
theorem B2760815 : Blo 1839621 2760815 := bstep (se 1 (by rfl) ⟨2070611, by rfl⟩ : syracuseStep 2760815 = 4141223) B4141223
theorem B9953603 : Blo 1839621 9953603 := bstep (se 1 (by rfl) ⟨7465202, by rfl⟩ : syracuseStep 9953603 = 14930405) B14930405
theorem B5243231 : Blo 1839621 5243231 := bstep (se 1 (by rfl) ⟨3932423, by rfl⟩ : syracuseStep 5243231 = 7864847) B7864847
theorem B3105391 : Blo 1839621 3105391 := bstep (se 1 (by rfl) ⟨2329043, by rfl⟩ : syracuseStep 3105391 = 4658087) B4658087
theorem B6210215 : Blo 1839621 6210215 := bstep (se 1 (by rfl) ⟨4657661, by rfl⟩ : syracuseStep 6210215 = 9315323) B9315323
theorem B5899007 : Blo 1839621 5899007 := bstep (se 1 (by rfl) ⟨4424255, by rfl⟩ : syracuseStep 5899007 = 8848511) B8848511
theorem B2761499 : Blo 1839621 2761499 := bstep (se 1 (by rfl) ⟨2071124, by rfl⟩ : syracuseStep 2761499 = 4142249) B4142249
theorem B33588215 : Blo 1839621 33588215 := bstep (se 1 (by rfl) ⟨25191161, by rfl⟩ : syracuseStep 33588215 = 50382323) B50382323
theorem B25519283 : Blo 1839621 25519283 := bstep (se 1 (by rfl) ⟨19139462, by rfl⟩ : syracuseStep 25519283 = 38278925) B38278925
theorem B2762153 : Blo 1839621 2762153 := bstep (se 2 (by rfl) ⟨1035807, by rfl⟩ : syracuseStep 2762153 = 2071615) B2071615
theorem B6211241 : Blo 1839621 6211241 := bstep (se 2 (by rfl) ⟨2329215, by rfl⟩ : syracuseStep 6211241 = 4658431) B4658431
theorem B9316295 : Blo 1839621 9316295 := bstep (se 1 (by rfl) ⟨6987221, by rfl⟩ : syracuseStep 9316295 = 13974443) B13974443
theorem B2328679 : Blo 1839621 2328679 := bstep (se 1 (by rfl) ⟨1746509, by rfl⟩ : syracuseStep 2328679 = 3493019) B3493019
theorem B8398991 : Blo 1839621 8398991 := bstep (se 1 (by rfl) ⟨6299243, by rfl⟩ : syracuseStep 8398991 = 12598487) B12598487
theorem B10488487 : Blo 1839621 10488487 := bstep (se 1 (by rfl) ⟨7866365, by rfl⟩ : syracuseStep 10488487 = 15732731) B15732731
theorem B3107497 : Blo 1839621 3107497 := bstep (se 2 (by rfl) ⟨1165311, by rfl⟩ : syracuseStep 3107497 = 2330623) B2330623
theorem B4140359 : Blo 1839621 4140359 := bstep (se 1 (by rfl) ⟨3105269, by rfl⟩ : syracuseStep 4140359 = 6210539) B6210539
theorem B3493543 : Blo 1839621 3493543 := bstep (se 1 (by rfl) ⟨2620157, by rfl⟩ : syracuseStep 3493543 = 5240315) B5240315
theorem B6214049 : Blo 1839621 6214049 := bstep (se 2 (by rfl) ⟨2330268, by rfl⟩ : syracuseStep 6214049 = 4660537) B4660537
theorem B4141547 : Blo 1839621 4141547 := bstep (se 1 (by rfl) ⟨3106160, by rfl⟩ : syracuseStep 4141547 = 6212321) B6212321
theorem B40899077 : Blo 1839621 40899077 := bstep (se 4 (by rfl) ⟨3834288, by rfl⟩ : syracuseStep 40899077 = 7668577) B7668577
theorem B1839707 : Blo 1839621 1839707 := bstep (se 1 (by rfl) ⟨1379780, by rfl⟩ : syracuseStep 1839707 = 2759561) B2759561
theorem B6214319 : Blo 1839621 6214319 := bstep (se 1 (by rfl) ⟨4660739, by rfl⟩ : syracuseStep 6214319 = 9321479) B9321479
theorem B4657895 : Blo 1839621 4657895 := bstep (se 1 (by rfl) ⟨3493421, by rfl⟩ : syracuseStep 4657895 = 6986843) B6986843
theorem B20960207 : Blo 1839621 20960207 := bstep (se 1 (by rfl) ⟨15720155, by rfl⟩ : syracuseStep 20960207 = 31440311) B31440311
theorem B90740083 : Blo 1839621 90740083 := bstep (se 1 (by rfl) ⟨68055062, by rfl⟩ : syracuseStep 90740083 = 136110125) B136110125
theorem B69031561 : Blo 1839621 69031561 := bstep (se 2 (by rfl) ⟨25886835, by rfl⟩ : syracuseStep 69031561 = 51773671) B51773671
theorem B51058397 : Blo 1839621 51058397 := bstep (se 3 (by rfl) ⟨9573449, by rfl⟩ : syracuseStep 51058397 = 19146899) B19146899
theorem B1840923 : Blo 1839621 1840923 := bstep (se 1 (by rfl) ⟨1380692, by rfl⟩ : syracuseStep 1840923 = 2761385) B2761385
theorem B56670263 : Blo 1839621 56670263 := bstep (se 1 (by rfl) ⟨42502697, by rfl⟩ : syracuseStep 56670263 = 85005395) B85005395
theorem B1841311 : Blo 1839621 1841311 := bstep (se 1 (by rfl) ⟨1380983, by rfl⟩ : syracuseStep 1841311 = 2761967) B2761967
theorem B10483931 : Blo 1839621 10483931 := bstep (se 1 (by rfl) ⟨7862948, by rfl⟩ : syracuseStep 10483931 = 15725897) B15725897
theorem B1841391 : Blo 1839621 1841391 := bstep (se 1 (by rfl) ⟨1381043, by rfl⟩ : syracuseStep 1841391 = 2762087) B2762087
theorem B1291401629 : Blo 1839621 1291401629 := bstep (se 3 (by rfl) ⟨242137805, by rfl⟩ : syracuseStep 1291401629 = 484275611) B484275611
theorem B2759615 : Blo 1839621 2759615 := bstep (se 1 (by rfl) ⟨2069711, by rfl⟩ : syracuseStep 2759615 = 4139423) B4139423
theorem B2759849 : Blo 1839621 2759849 := bstep (se 2 (by rfl) ⟨1034943, by rfl⟩ : syracuseStep 2759849 = 2069887) B2069887
theorem B25198127 : Blo 1839621 25198127 := bstep (se 1 (by rfl) ⟨18898595, by rfl⟩ : syracuseStep 25198127 = 37797191) B37797191
theorem B3104905 : Blo 1839621 3104905 := bstep (se 2 (by rfl) ⟨1164339, by rfl⟩ : syracuseStep 3104905 = 2328679) B2328679
theorem B6635735 : Blo 1839621 6635735 := bstep (se 1 (by rfl) ⟨4976801, by rfl⟩ : syracuseStep 6635735 = 9953603) B9953603
theorem B2761031 : Blo 1839621 2761031 := bstep (se 1 (by rfl) ⟨2070773, by rfl⟩ : syracuseStep 2761031 = 4141547) B4141547
theorem B22397309 : Blo 1839621 22397309 := bstep (se 3 (by rfl) ⟨4199495, by rfl⟩ : syracuseStep 22397309 = 8398991) B8398991
theorem B3105263 : Blo 1839621 3105263 := bstep (se 1 (by rfl) ⟨2328947, by rfl⟩ : syracuseStep 3105263 = 4657895) B4657895
theorem B3932671 : Blo 1839621 3932671 := bstep (se 1 (by rfl) ⟨2949503, by rfl⟩ : syracuseStep 3932671 = 5899007) B5899007
theorem B13984649 : Blo 1839621 13984649 := bstep (se 2 (by rfl) ⟨5244243, by rfl⟩ : syracuseStep 13984649 = 10488487) B10488487
theorem B6210863 : Blo 1839621 6210863 := bstep (se 1 (by rfl) ⟨4658147, by rfl⟩ : syracuseStep 6210863 = 9316295) B9316295
theorem B6989287 : Blo 1839621 6989287 := bstep (se 1 (by rfl) ⟨5241965, by rfl⟩ : syracuseStep 6989287 = 10483931) B10483931
theorem B27266051 : Blo 1839621 27266051 := bstep (se 1 (by rfl) ⟨20449538, by rfl⟩ : syracuseStep 27266051 = 40899077) B40899077
theorem B4140143 : Blo 1839621 4140143 := bstep (se 1 (by rfl) ⟨3105107, by rfl⟩ : syracuseStep 4140143 = 6210215) B6210215
theorem B22392143 : Blo 1839621 22392143 := bstep (se 1 (by rfl) ⟨16794107, by rfl⟩ : syracuseStep 22392143 = 33588215) B33588215
theorem B4140521 : Blo 1839621 4140521 := bstep (se 2 (by rfl) ⟨1552695, by rfl⟩ : syracuseStep 4140521 = 3105391) B3105391
theorem B4140827 : Blo 1839621 4140827 := bstep (se 1 (by rfl) ⟨3105620, by rfl⟩ : syracuseStep 4140827 = 6211241) B6211241
theorem B860934419 : Blo 1839621 860934419 := bstep (se 1 (by rfl) ⟨645700814, by rfl⟩ : syracuseStep 860934419 = 1291401629) B1291401629
theorem B136155725 : Blo 1839621 136155725 := bstep (se 3 (by rfl) ⟨25529198, by rfl⟩ : syracuseStep 136155725 = 51058397) B51058397
theorem B1839743 : Blo 1839621 1839743 := bstep (se 1 (by rfl) ⟨1379807, by rfl⟩ : syracuseStep 1839743 = 2759615) B2759615
theorem B1839899 : Blo 1839621 1839899 := bstep (se 1 (by rfl) ⟨1379924, by rfl⟩ : syracuseStep 1839899 = 2759849) B2759849
theorem B92042081 : Blo 1839621 92042081 := bstep (se 2 (by rfl) ⟨34515780, by rfl⟩ : syracuseStep 92042081 = 69031561) B69031561
theorem B4658057 : Blo 1839621 4658057 := bstep (se 2 (by rfl) ⟨1746771, by rfl⟩ : syracuseStep 4658057 = 3493543) B3493543
theorem B16798751 : Blo 1839621 16798751 := bstep (se 1 (by rfl) ⟨12599063, by rfl⟩ : syracuseStep 16798751 = 25198127) B25198127
theorem B1840511 : Blo 1839621 1840511 := bstep (se 1 (by rfl) ⟨1380383, by rfl⟩ : syracuseStep 1840511 = 2760767) B2760767
theorem B1840543 : Blo 1839621 1840543 := bstep (se 1 (by rfl) ⟨1380407, by rfl⟩ : syracuseStep 1840543 = 2760815) B2760815
theorem B3495487 : Blo 1839621 3495487 := bstep (se 1 (by rfl) ⟨2621615, by rfl⟩ : syracuseStep 3495487 = 5243231) B5243231
theorem B4142699 : Blo 1839621 4142699 := bstep (se 1 (by rfl) ⟨3107024, by rfl⟩ : syracuseStep 4142699 = 6214049) B6214049
theorem B4142879 : Blo 1839621 4142879 := bstep (se 1 (by rfl) ⟨3107159, by rfl⟩ : syracuseStep 4142879 = 6214319) B6214319
theorem B1840999 : Blo 1839621 1840999 := bstep (se 1 (by rfl) ⟨1380749, by rfl⟩ : syracuseStep 1840999 = 2761499) B2761499
theorem B13973471 : Blo 1839621 13973471 := bstep (se 1 (by rfl) ⟨10480103, by rfl⟩ : syracuseStep 13973471 = 20960207) B20960207
theorem B17012855 : Blo 1839621 17012855 := bstep (se 1 (by rfl) ⟨12759641, by rfl⟩ : syracuseStep 17012855 = 25519283) B25519283
theorem B4143329 : Blo 1839621 4143329 := bstep (se 2 (by rfl) ⟨1553748, by rfl⟩ : syracuseStep 4143329 = 3107497) B3107497
theorem B1841435 : Blo 1839621 1841435 := bstep (se 1 (by rfl) ⟨1381076, by rfl⟩ : syracuseStep 1841435 = 2762153) B2762153
theorem B37780175 : Blo 1839621 37780175 := bstep (se 1 (by rfl) ⟨28335131, by rfl⟩ : syracuseStep 37780175 = 56670263) B56670263
theorem B120986777 : Blo 1839621 120986777 := bstep (se 2 (by rfl) ⟨45370041, by rfl⟩ : syracuseStep 120986777 = 90740083) B90740083
theorem B2760239 : Blo 1839621 2760239 := bstep (se 1 (by rfl) ⟨2070179, by rfl⟩ : syracuseStep 2760239 = 4140359) B4140359
theorem B4423823 : Blo 1839621 4423823 := bstep (se 1 (by rfl) ⟨3317867, by rfl⟩ : syracuseStep 4423823 = 6635735) B6635735
theorem B573956279 : Blo 1839621 573956279 := bstep (se 1 (by rfl) ⟨430467209, by rfl⟩ : syracuseStep 573956279 = 860934419) B860934419
theorem B3105371 : Blo 1839621 3105371 := bstep (se 1 (by rfl) ⟨2329028, by rfl⟩ : syracuseStep 3105371 = 4658057) B4658057
theorem B9323099 : Blo 1839621 9323099 := bstep (se 1 (by rfl) ⟨6992324, by rfl⟩ : syracuseStep 9323099 = 13984649) B13984649
theorem B5243561 : Blo 1839621 5243561 := bstep (se 2 (by rfl) ⟨1966335, by rfl⟩ : syracuseStep 5243561 = 3932671) B3932671
theorem B11199167 : Blo 1839621 11199167 := bstep (se 1 (by rfl) ⟨8399375, by rfl⟩ : syracuseStep 11199167 = 16798751) B16798751
theorem B2761799 : Blo 1839621 2761799 := bstep (se 1 (by rfl) ⟨2071349, by rfl⟩ : syracuseStep 2761799 = 4142699) B4142699
theorem B2761919 : Blo 1839621 2761919 := bstep (se 1 (by rfl) ⟨2071439, by rfl⟩ : syracuseStep 2761919 = 4142879) B4142879
theorem B9315647 : Blo 1839621 9315647 := bstep (se 1 (by rfl) ⟨6986735, by rfl⟩ : syracuseStep 9315647 = 13973471) B13973471
theorem B2762219 : Blo 1839621 2762219 := bstep (se 1 (by rfl) ⟨2071664, by rfl⟩ : syracuseStep 2762219 = 4143329) B4143329
theorem B14928095 : Blo 1839621 14928095 := bstep (se 1 (by rfl) ⟨11196071, by rfl⟩ : syracuseStep 14928095 = 22392143) B22392143
theorem B4139873 : Blo 1839621 4139873 := bstep (se 2 (by rfl) ⟨1552452, by rfl⟩ : syracuseStep 4139873 = 3104905) B3104905
theorem B90770483 : Blo 1839621 90770483 := bstep (se 1 (by rfl) ⟨68077862, by rfl⟩ : syracuseStep 90770483 = 136155725) B136155725
theorem B61361387 : Blo 1839621 61361387 := bstep (se 1 (by rfl) ⟨46021040, by rfl⟩ : syracuseStep 61361387 = 92042081) B92042081
theorem B4140575 : Blo 1839621 4140575 := bstep (se 1 (by rfl) ⟨3105431, by rfl⟩ : syracuseStep 4140575 = 6210863) B6210863
theorem B11341903 : Blo 1839621 11341903 := bstep (se 1 (by rfl) ⟨8506427, by rfl⟩ : syracuseStep 11341903 = 17012855) B17012855
theorem B25186783 : Blo 1839621 25186783 := bstep (se 1 (by rfl) ⟨18890087, by rfl⟩ : syracuseStep 25186783 = 37780175) B37780175
theorem B9319049 : Blo 1839621 9319049 := bstep (se 2 (by rfl) ⟨3494643, by rfl⟩ : syracuseStep 9319049 = 6989287) B6989287
theorem B1840159 : Blo 1839621 1840159 := bstep (se 1 (by rfl) ⟨1380119, by rfl⟩ : syracuseStep 1840159 = 2760239) B2760239
theorem B1840687 : Blo 1839621 1840687 := bstep (se 1 (by rfl) ⟨1380515, by rfl⟩ : syracuseStep 1840687 = 2761031) B2761031
theorem B14931539 : Blo 1839621 14931539 := bstep (se 1 (by rfl) ⟨11198654, by rfl⟩ : syracuseStep 14931539 = 22397309) B22397309
theorem B2070175 : Blo 1839621 2070175 := bstep (se 1 (by rfl) ⟨1552631, by rfl⟩ : syracuseStep 2070175 = 3105263) B3105263
theorem B18177367 : Blo 1839621 18177367 := bstep (se 1 (by rfl) ⟨13633025, by rfl⟩ : syracuseStep 18177367 = 27266051) B27266051
theorem B2760095 : Blo 1839621 2760095 := bstep (se 1 (by rfl) ⟨2070071, by rfl⟩ : syracuseStep 2760095 = 4140143) B4140143
theorem B4660649 : Blo 1839621 4660649 := bstep (se 2 (by rfl) ⟨1747743, by rfl⟩ : syracuseStep 4660649 = 3495487) B3495487
theorem B80657851 : Blo 1839621 80657851 := bstep (se 1 (by rfl) ⟨60493388, by rfl⟩ : syracuseStep 80657851 = 120986777) B120986777
theorem B2760347 : Blo 1839621 2760347 := bstep (se 1 (by rfl) ⟨2070260, by rfl⟩ : syracuseStep 2760347 = 4140521) B4140521
theorem B2760551 : Blo 1839621 2760551 := bstep (se 1 (by rfl) ⟨2070413, by rfl⟩ : syracuseStep 2760551 = 4140827) B4140827
theorem B2949215 : Blo 1839621 2949215 := bstep (se 1 (by rfl) ⟨2211911, by rfl⟩ : syracuseStep 2949215 = 4423823) B4423823
theorem B15122537 : Blo 1839621 15122537 := bstep (se 2 (by rfl) ⟨5670951, by rfl⟩ : syracuseStep 15122537 = 11341903) B11341903
theorem B6210431 : Blo 1839621 6210431 := bstep (se 1 (by rfl) ⟨4657823, by rfl⟩ : syracuseStep 6210431 = 9315647) B9315647
theorem B9954359 : Blo 1839621 9954359 := bstep (se 1 (by rfl) ⟨7465769, by rfl⟩ : syracuseStep 9954359 = 14931539) B14931539
theorem B3107099 : Blo 1839621 3107099 := bstep (se 1 (by rfl) ⟨2330324, by rfl⟩ : syracuseStep 3107099 = 4660649) B4660649
theorem B6212699 : Blo 1839621 6212699 := bstep (se 1 (by rfl) ⟨4659524, by rfl⟩ : syracuseStep 6212699 = 9319049) B9319049
theorem B7466111 : Blo 1839621 7466111 := bstep (se 1 (by rfl) ⟨5599583, by rfl⟩ : syracuseStep 7466111 = 11199167) B11199167
theorem B39808253 : Blo 1839621 39808253 := bstep (se 3 (by rfl) ⟨7464047, by rfl⟩ : syracuseStep 39808253 = 14928095) B14928095
theorem B33582377 : Blo 1839621 33582377 := bstep (se 2 (by rfl) ⟨12593391, by rfl⟩ : syracuseStep 33582377 = 25186783) B25186783
theorem B24236489 : Blo 1839621 24236489 := bstep (se 2 (by rfl) ⟨9088683, by rfl⟩ : syracuseStep 24236489 = 18177367) B18177367
theorem B40907591 : Blo 1839621 40907591 := bstep (se 1 (by rfl) ⟨30680693, by rfl⟩ : syracuseStep 40907591 = 61361387) B61361387
theorem B1840063 : Blo 1839621 1840063 := bstep (se 1 (by rfl) ⟨1380047, by rfl⟩ : syracuseStep 1840063 = 2760095) B2760095
theorem B1840231 : Blo 1839621 1840231 := bstep (se 1 (by rfl) ⟨1380173, by rfl⟩ : syracuseStep 1840231 = 2760347) B2760347
theorem B1840367 : Blo 1839621 1840367 := bstep (se 1 (by rfl) ⟨1380275, by rfl⟩ : syracuseStep 1840367 = 2760551) B2760551
theorem B382637519 : Blo 1839621 382637519 := bstep (se 1 (by rfl) ⟨286978139, by rfl⟩ : syracuseStep 382637519 = 573956279) B573956279
theorem B2070247 : Blo 1839621 2070247 := bstep (se 1 (by rfl) ⟨1552685, by rfl⟩ : syracuseStep 2070247 = 3105371) B3105371
theorem B6215399 : Blo 1839621 6215399 := bstep (se 1 (by rfl) ⟨4661549, by rfl⟩ : syracuseStep 6215399 = 9323099) B9323099
theorem B3495707 : Blo 1839621 3495707 := bstep (se 1 (by rfl) ⟨2621780, by rfl⟩ : syracuseStep 3495707 = 5243561) B5243561
theorem B1841199 : Blo 1839621 1841199 := bstep (se 1 (by rfl) ⟨1380899, by rfl⟩ : syracuseStep 1841199 = 2761799) B2761799
theorem B1841279 : Blo 1839621 1841279 := bstep (se 1 (by rfl) ⟨1380959, by rfl⟩ : syracuseStep 1841279 = 2761919) B2761919
theorem B1841479 : Blo 1839621 1841479 := bstep (se 1 (by rfl) ⟨1381109, by rfl⟩ : syracuseStep 1841479 = 2762219) B2762219
theorem B2759915 : Blo 1839621 2759915 := bstep (se 1 (by rfl) ⟨2069936, by rfl⟩ : syracuseStep 2759915 = 4139873) B4139873
theorem B107543801 : Blo 1839621 107543801 := bstep (se 2 (by rfl) ⟨40328925, by rfl⟩ : syracuseStep 107543801 = 80657851) B80657851
theorem B60513655 : Blo 1839621 60513655 := bstep (se 1 (by rfl) ⟨45385241, by rfl⟩ : syracuseStep 60513655 = 90770483) B90770483
theorem B2760233 : Blo 1839621 2760233 := bstep (se 2 (by rfl) ⟨1035087, by rfl⟩ : syracuseStep 2760233 = 2070175) B2070175
theorem B2760383 : Blo 1839621 2760383 := bstep (se 1 (by rfl) ⟨2070287, by rfl⟩ : syracuseStep 2760383 = 4140575) B4140575
theorem B7864573 : Blo 1839621 7864573 := bstep (se 3 (by rfl) ⟨1474607, by rfl⟩ : syracuseStep 7864573 = 2949215) B2949215
theorem B27271727 : Blo 1839621 27271727 := bstep (se 1 (by rfl) ⟨20453795, by rfl⟩ : syracuseStep 27271727 = 40907591) B40907591
theorem B6636239 : Blo 1839621 6636239 := bstep (se 1 (by rfl) ⟨4977179, by rfl⟩ : syracuseStep 6636239 = 9954359) B9954359
theorem B255091679 : Blo 1839621 255091679 := bstep (se 1 (by rfl) ⟨191318759, by rfl⟩ : syracuseStep 255091679 = 382637519) B382637519
theorem B80684873 : Blo 1839621 80684873 := bstep (se 2 (by rfl) ⟨30256827, by rfl⟩ : syracuseStep 80684873 = 60513655) B60513655
theorem B16157659 : Blo 1839621 16157659 := bstep (se 1 (by rfl) ⟨12118244, by rfl⟩ : syracuseStep 16157659 = 24236489) B24236489
theorem B4140287 : Blo 1839621 4140287 := bstep (se 1 (by rfl) ⟨3105215, by rfl⟩ : syracuseStep 4140287 = 6210431) B6210431
theorem B2330471 : Blo 1839621 2330471 := bstep (se 1 (by rfl) ⟨1747853, by rfl⟩ : syracuseStep 2330471 = 3495707) B3495707
theorem B4141799 : Blo 1839621 4141799 := bstep (se 1 (by rfl) ⟨3106349, by rfl⟩ : syracuseStep 4141799 = 6212699) B6212699
theorem B4977407 : Blo 1839621 4977407 := bstep (se 1 (by rfl) ⟨3733055, by rfl⟩ : syracuseStep 4977407 = 7466111) B7466111
theorem B1839943 : Blo 1839621 1839943 := bstep (se 1 (by rfl) ⟨1379957, by rfl⟩ : syracuseStep 1839943 = 2759915) B2759915
theorem B26538835 : Blo 1839621 26538835 := bstep (se 1 (by rfl) ⟨19904126, by rfl⟩ : syracuseStep 26538835 = 39808253) B39808253
theorem B1840155 : Blo 1839621 1840155 := bstep (se 1 (by rfl) ⟨1380116, by rfl⟩ : syracuseStep 1840155 = 2760233) B2760233
theorem B1840255 : Blo 1839621 1840255 := bstep (se 1 (by rfl) ⟨1380191, by rfl⟩ : syracuseStep 1840255 = 2760383) B2760383
theorem B10081691 : Blo 1839621 10081691 := bstep (se 1 (by rfl) ⟨7561268, by rfl⟩ : syracuseStep 10081691 = 15122537) B15122537
theorem B4143599 : Blo 1839621 4143599 := bstep (se 1 (by rfl) ⟨3107699, by rfl⟩ : syracuseStep 4143599 = 6215399) B6215399
theorem B2071399 : Blo 1839621 2071399 := bstep (se 1 (by rfl) ⟨1553549, by rfl⟩ : syracuseStep 2071399 = 3107099) B3107099
theorem B71695867 : Blo 1839621 71695867 := bstep (se 1 (by rfl) ⟨53771900, by rfl⟩ : syracuseStep 71695867 = 107543801) B107543801
theorem B22388251 : Blo 1839621 22388251 := bstep (se 1 (by rfl) ⟨16791188, by rfl⟩ : syracuseStep 22388251 = 33582377) B33582377
theorem B2760329 : Blo 1839621 2760329 := bstep (se 2 (by rfl) ⟨1035123, by rfl⟩ : syracuseStep 2760329 = 2070247) B2070247
theorem B10486097 : Blo 1839621 10486097 := bstep (se 2 (by rfl) ⟨3932286, by rfl⟩ : syracuseStep 10486097 = 7864573) B7864573
theorem B4424159 : Blo 1839621 4424159 := bstep (se 1 (by rfl) ⟨3318119, by rfl⟩ : syracuseStep 4424159 = 6636239) B6636239
theorem B2761199 : Blo 1839621 2761199 := bstep (se 1 (by rfl) ⟨2070899, by rfl⟩ : syracuseStep 2761199 = 4141799) B4141799
theorem B2761865 : Blo 1839621 2761865 := bstep (se 2 (by rfl) ⟨1035699, by rfl⟩ : syracuseStep 2761865 = 2071399) B2071399
theorem B53789915 : Blo 1839621 53789915 := bstep (se 1 (by rfl) ⟨40342436, by rfl⟩ : syracuseStep 53789915 = 80684873) B80684873
theorem B2762399 : Blo 1839621 2762399 := bstep (se 1 (by rfl) ⟨2071799, by rfl⟩ : syracuseStep 2762399 = 4143599) B4143599
theorem B95594489 : Blo 1839621 95594489 := bstep (se 2 (by rfl) ⟨35847933, by rfl⟩ : syracuseStep 95594489 = 71695867) B71695867
theorem B13273085 : Blo 1839621 13273085 := bstep (se 3 (by rfl) ⟨2488703, by rfl⟩ : syracuseStep 13273085 = 4977407) B4977407
theorem B18181151 : Blo 1839621 18181151 := bstep (se 1 (by rfl) ⟨13635863, by rfl⟩ : syracuseStep 18181151 = 27271727) B27271727
theorem B170061119 : Blo 1839621 170061119 := bstep (se 1 (by rfl) ⟨127545839, by rfl⟩ : syracuseStep 170061119 = 255091679) B255091679
theorem B6721127 : Blo 1839621 6721127 := bstep (se 1 (by rfl) ⟨5040845, by rfl⟩ : syracuseStep 6721127 = 10081691) B10081691
theorem B35385113 : Blo 1839621 35385113 := bstep (se 2 (by rfl) ⟨13269417, by rfl⟩ : syracuseStep 35385113 = 26538835) B26538835
theorem B6214589 : Blo 1839621 6214589 := bstep (se 3 (by rfl) ⟨1165235, by rfl⟩ : syracuseStep 6214589 = 2330471) B2330471
theorem B1840219 : Blo 1839621 1840219 := bstep (se 1 (by rfl) ⟨1380164, by rfl⟩ : syracuseStep 1840219 = 2760329) B2760329
theorem B21543545 : Blo 1839621 21543545 := bstep (se 2 (by rfl) ⟨8078829, by rfl⟩ : syracuseStep 21543545 = 16157659) B16157659
theorem B29851001 : Blo 1839621 29851001 := bstep (se 2 (by rfl) ⟨11194125, by rfl⟩ : syracuseStep 29851001 = 22388251) B22388251
theorem B2760191 : Blo 1839621 2760191 := bstep (se 1 (by rfl) ⟨2070143, by rfl⟩ : syracuseStep 2760191 = 4140287) B4140287
theorem B11797757 : Blo 1839621 11797757 := bstep (se 3 (by rfl) ⟨2212079, by rfl⟩ : syracuseStep 11797757 = 4424159) B4424159
theorem B8848723 : Blo 1839621 8848723 := bstep (se 1 (by rfl) ⟨6636542, by rfl⟩ : syracuseStep 8848723 = 13273085) B13273085
theorem B14362363 : Blo 1839621 14362363 := bstep (se 1 (by rfl) ⟨10771772, by rfl⟩ : syracuseStep 14362363 = 21543545) B21543545
theorem B19900667 : Blo 1839621 19900667 := bstep (se 1 (by rfl) ⟨14925500, by rfl⟩ : syracuseStep 19900667 = 29851001) B29851001
theorem B6990731 : Blo 1839621 6990731 := bstep (se 1 (by rfl) ⟨5243048, by rfl⟩ : syracuseStep 6990731 = 10486097) B10486097
theorem B35859943 : Blo 1839621 35859943 := bstep (se 1 (by rfl) ⟨26894957, by rfl⟩ : syracuseStep 35859943 = 53789915) B53789915
theorem B63729659 : Blo 1839621 63729659 := bstep (se 1 (by rfl) ⟨47797244, by rfl⟩ : syracuseStep 63729659 = 95594489) B95594489
theorem B12120767 : Blo 1839621 12120767 := bstep (se 1 (by rfl) ⟨9090575, by rfl⟩ : syracuseStep 12120767 = 18181151) B18181151
theorem B113374079 : Blo 1839621 113374079 := bstep (se 1 (by rfl) ⟨85030559, by rfl⟩ : syracuseStep 113374079 = 170061119) B170061119
theorem B1840127 : Blo 1839621 1840127 := bstep (se 1 (by rfl) ⟨1380095, by rfl⟩ : syracuseStep 1840127 = 2760191) B2760191
theorem B23590075 : Blo 1839621 23590075 := bstep (se 1 (by rfl) ⟨17692556, by rfl⟩ : syracuseStep 23590075 = 35385113) B35385113
theorem B1840799 : Blo 1839621 1840799 := bstep (se 1 (by rfl) ⟨1380599, by rfl⟩ : syracuseStep 1840799 = 2761199) B2761199
theorem B4143059 : Blo 1839621 4143059 := bstep (se 1 (by rfl) ⟨3107294, by rfl⟩ : syracuseStep 4143059 = 6214589) B6214589
theorem B1841243 : Blo 1839621 1841243 := bstep (se 1 (by rfl) ⟨1380932, by rfl⟩ : syracuseStep 1841243 = 2761865) B2761865
theorem B1841599 : Blo 1839621 1841599 := bstep (se 1 (by rfl) ⟨1381199, by rfl⟩ : syracuseStep 1841599 = 2762399) B2762399
theorem B4480751 : Blo 1839621 4480751 := bstep (se 1 (by rfl) ⟨3360563, by rfl⟩ : syracuseStep 4480751 = 6721127) B6721127
theorem B53068445 : Blo 1839621 53068445 := bstep (se 3 (by rfl) ⟨9950333, by rfl⟩ : syracuseStep 53068445 = 19900667) B19900667
theorem B7865171 : Blo 1839621 7865171 := bstep (se 1 (by rfl) ⟨5898878, by rfl⟩ : syracuseStep 7865171 = 11797757) B11797757
theorem B2762039 : Blo 1839621 2762039 := bstep (se 1 (by rfl) ⟨2071529, by rfl⟩ : syracuseStep 2762039 = 4143059) B4143059
theorem B11798297 : Blo 1839621 11798297 := bstep (se 2 (by rfl) ⟨4424361, by rfl⟩ : syracuseStep 11798297 = 8848723) B8848723
theorem B42486439 : Blo 1839621 42486439 := bstep (se 1 (by rfl) ⟨31864829, by rfl⟩ : syracuseStep 42486439 = 63729659) B63729659
theorem B8080511 : Blo 1839621 8080511 := bstep (se 1 (by rfl) ⟨6060383, by rfl⟩ : syracuseStep 8080511 = 12120767) B12120767
theorem B75582719 : Blo 1839621 75582719 := bstep (se 1 (by rfl) ⟨56687039, by rfl⟩ : syracuseStep 75582719 = 113374079) B113374079
theorem B31453433 : Blo 1839621 31453433 := bstep (se 2 (by rfl) ⟨11795037, by rfl⟩ : syracuseStep 31453433 = 23590075) B23590075
theorem B47813257 : Blo 1839621 47813257 := bstep (se 2 (by rfl) ⟨17929971, by rfl⟩ : syracuseStep 47813257 = 35859943) B35859943
theorem B19149817 : Blo 1839621 19149817 := bstep (se 2 (by rfl) ⟨7181181, by rfl⟩ : syracuseStep 19149817 = 14362363) B14362363
theorem B2987167 : Blo 1839621 2987167 := bstep (se 1 (by rfl) ⟨2240375, by rfl⟩ : syracuseStep 2987167 = 4480751) B4480751
theorem B4660487 : Blo 1839621 4660487 := bstep (se 1 (by rfl) ⟨3495365, by rfl⟩ : syracuseStep 4660487 = 6990731) B6990731
theorem B5243447 : Blo 1839621 5243447 := bstep (se 1 (by rfl) ⟨3932585, by rfl⟩ : syracuseStep 5243447 = 7865171) B7865171
theorem B63751009 : Blo 1839621 63751009 := bstep (se 2 (by rfl) ⟨23906628, by rfl⟩ : syracuseStep 63751009 = 47813257) B47813257
theorem B56648585 : Blo 1839621 56648585 := bstep (se 2 (by rfl) ⟨21243219, by rfl⟩ : syracuseStep 56648585 = 42486439) B42486439
theorem B7865531 : Blo 1839621 7865531 := bstep (se 1 (by rfl) ⟨5899148, by rfl⟩ : syracuseStep 7865531 = 11798297) B11798297
theorem B3982889 : Blo 1839621 3982889 := bstep (se 2 (by rfl) ⟨1493583, by rfl⟩ : syracuseStep 3982889 = 2987167) B2987167
theorem B3106991 : Blo 1839621 3106991 := bstep (se 1 (by rfl) ⟨2330243, by rfl⟩ : syracuseStep 3106991 = 4660487) B4660487
theorem B21548029 : Blo 1839621 21548029 := bstep (se 3 (by rfl) ⟨4040255, by rfl⟩ : syracuseStep 21548029 = 8080511) B8080511
theorem B20968955 : Blo 1839621 20968955 := bstep (se 1 (by rfl) ⟨15726716, by rfl⟩ : syracuseStep 20968955 = 31453433) B31453433
theorem B35378963 : Blo 1839621 35378963 := bstep (se 1 (by rfl) ⟨26534222, by rfl⟩ : syracuseStep 35378963 = 53068445) B53068445
theorem B1841359 : Blo 1839621 1841359 := bstep (se 1 (by rfl) ⟨1381019, by rfl⟩ : syracuseStep 1841359 = 2762039) B2762039
theorem B25533089 : Blo 1839621 25533089 := bstep (se 2 (by rfl) ⟨9574908, by rfl⟩ : syracuseStep 25533089 = 19149817) B19149817
theorem B50388479 : Blo 1839621 50388479 := bstep (se 1 (by rfl) ⟨37791359, by rfl⟩ : syracuseStep 50388479 = 75582719) B75582719
theorem B5243687 : Blo 1839621 5243687 := bstep (se 1 (by rfl) ⟨3932765, by rfl⟩ : syracuseStep 5243687 = 7865531) B7865531
theorem B85001345 : Blo 1839621 85001345 := bstep (se 2 (by rfl) ⟨31875504, by rfl⟩ : syracuseStep 85001345 = 63751009) B63751009
theorem B23585975 : Blo 1839621 23585975 := bstep (se 1 (by rfl) ⟨17689481, by rfl⟩ : syracuseStep 23585975 = 35378963) B35378963
theorem B28730705 : Blo 1839621 28730705 := bstep (se 2 (by rfl) ⟨10774014, by rfl⟩ : syracuseStep 28730705 = 21548029) B21548029
theorem B151062893 : Blo 1839621 151062893 := bstep (se 3 (by rfl) ⟨28324292, by rfl⟩ : syracuseStep 151062893 = 56648585) B56648585
theorem B13979303 : Blo 1839621 13979303 := bstep (se 1 (by rfl) ⟨10484477, by rfl⟩ : syracuseStep 13979303 = 20968955) B20968955
theorem B10621037 : Blo 1839621 10621037 := bstep (se 3 (by rfl) ⟨1991444, by rfl⟩ : syracuseStep 10621037 = 3982889) B3982889
theorem B33592319 : Blo 1839621 33592319 := bstep (se 1 (by rfl) ⟨25194239, by rfl⟩ : syracuseStep 33592319 = 50388479) B50388479
theorem B3495631 : Blo 1839621 3495631 := bstep (se 1 (by rfl) ⟨2621723, by rfl⟩ : syracuseStep 3495631 = 5243447) B5243447
theorem B2071327 : Blo 1839621 2071327 := bstep (se 1 (by rfl) ⟨1553495, by rfl⟩ : syracuseStep 2071327 = 3106991) B3106991
theorem B17022059 : Blo 1839621 17022059 := bstep (se 1 (by rfl) ⟨12766544, by rfl⟩ : syracuseStep 17022059 = 25533089) B25533089
theorem B2761769 : Blo 1839621 2761769 := bstep (se 2 (by rfl) ⟨1035663, by rfl⟩ : syracuseStep 2761769 = 2071327) B2071327
theorem B11348039 : Blo 1839621 11348039 := bstep (se 1 (by rfl) ⟨8511029, by rfl⟩ : syracuseStep 11348039 = 17022059) B17022059
theorem B7080691 : Blo 1839621 7080691 := bstep (se 1 (by rfl) ⟨5310518, by rfl⟩ : syracuseStep 7080691 = 10621037) B10621037
theorem B56667563 : Blo 1839621 56667563 := bstep (se 1 (by rfl) ⟨42500672, by rfl⟩ : syracuseStep 56667563 = 85001345) B85001345
theorem B15723983 : Blo 1839621 15723983 := bstep (se 1 (by rfl) ⟨11792987, by rfl⟩ : syracuseStep 15723983 = 23585975) B23585975
theorem B100708595 : Blo 1839621 100708595 := bstep (se 1 (by rfl) ⟨75531446, by rfl⟩ : syracuseStep 100708595 = 151062893) B151062893
theorem B9319535 : Blo 1839621 9319535 := bstep (se 1 (by rfl) ⟨6989651, by rfl⟩ : syracuseStep 9319535 = 13979303) B13979303
theorem B3495791 : Blo 1839621 3495791 := bstep (se 1 (by rfl) ⟨2621843, by rfl⟩ : syracuseStep 3495791 = 5243687) B5243687
theorem B22394879 : Blo 1839621 22394879 := bstep (se 1 (by rfl) ⟨16796159, by rfl⟩ : syracuseStep 22394879 = 33592319) B33592319
theorem B306460853 : Blo 1839621 306460853 := bstep (se 5 (by rfl) ⟨14365352, by rfl⟩ : syracuseStep 306460853 = 28730705) B28730705
theorem B4660841 : Blo 1839621 4660841 := bstep (se 2 (by rfl) ⟨1747815, by rfl⟩ : syracuseStep 4660841 = 3495631) B3495631
theorem B30261437 : Blo 1839621 30261437 := bstep (se 3 (by rfl) ⟨5674019, by rfl⟩ : syracuseStep 30261437 = 11348039) B11348039
theorem B3107227 : Blo 1839621 3107227 := bstep (se 1 (by rfl) ⟨2330420, by rfl⟩ : syracuseStep 3107227 = 4660841) B4660841
theorem B6213023 : Blo 1839621 6213023 := bstep (se 1 (by rfl) ⟨4659767, by rfl⟩ : syracuseStep 6213023 = 9319535) B9319535
theorem B9440921 : Blo 1839621 9440921 := bstep (se 2 (by rfl) ⟨3540345, by rfl⟩ : syracuseStep 9440921 = 7080691) B7080691
theorem B2330527 : Blo 1839621 2330527 := bstep (se 1 (by rfl) ⟨1747895, by rfl⟩ : syracuseStep 2330527 = 3495791) B3495791
theorem B14929919 : Blo 1839621 14929919 := bstep (se 1 (by rfl) ⟨11197439, by rfl⟩ : syracuseStep 14929919 = 22394879) B22394879
theorem B37778375 : Blo 1839621 37778375 := bstep (se 1 (by rfl) ⟨28333781, by rfl⟩ : syracuseStep 37778375 = 56667563) B56667563
theorem B10482655 : Blo 1839621 10482655 := bstep (se 1 (by rfl) ⟨7861991, by rfl⟩ : syracuseStep 10482655 = 15723983) B15723983
theorem B67139063 : Blo 1839621 67139063 := bstep (se 1 (by rfl) ⟨50354297, by rfl⟩ : syracuseStep 67139063 = 100708595) B100708595
theorem B1841179 : Blo 1839621 1841179 := bstep (se 1 (by rfl) ⟨1380884, by rfl⟩ : syracuseStep 1841179 = 2761769) B2761769
theorem B204307235 : Blo 1839621 204307235 := bstep (se 1 (by rfl) ⟨153230426, by rfl⟩ : syracuseStep 204307235 = 306460853) B306460853
theorem B13976873 : Blo 1839621 13976873 := bstep (se 2 (by rfl) ⟨5241327, by rfl⟩ : syracuseStep 13976873 = 10482655) B10482655
theorem B6293947 : Blo 1839621 6293947 := bstep (se 1 (by rfl) ⟨4720460, by rfl⟩ : syracuseStep 6293947 = 9440921) B9440921
theorem B3107369 : Blo 1839621 3107369 := bstep (se 2 (by rfl) ⟨1165263, by rfl⟩ : syracuseStep 3107369 = 2330527) B2330527
theorem B25185583 : Blo 1839621 25185583 := bstep (se 1 (by rfl) ⟨18889187, by rfl⟩ : syracuseStep 25185583 = 37778375) B37778375
theorem B136204823 : Blo 1839621 136204823 := bstep (se 1 (by rfl) ⟨102153617, by rfl⟩ : syracuseStep 136204823 = 204307235) B204307235
theorem B4142015 : Blo 1839621 4142015 := bstep (se 1 (by rfl) ⟨3106511, by rfl⟩ : syracuseStep 4142015 = 6213023) B6213023
theorem B20174291 : Blo 1839621 20174291 := bstep (se 1 (by rfl) ⟨15130718, by rfl⟩ : syracuseStep 20174291 = 30261437) B30261437
theorem B4142969 : Blo 1839621 4142969 := bstep (se 2 (by rfl) ⟨1553613, by rfl⟩ : syracuseStep 4142969 = 3107227) B3107227
theorem B44759375 : Blo 1839621 44759375 := bstep (se 1 (by rfl) ⟨33569531, by rfl⟩ : syracuseStep 44759375 = 67139063) B67139063
theorem B9953279 : Blo 1839621 9953279 := bstep (se 1 (by rfl) ⟨7464959, by rfl⟩ : syracuseStep 9953279 = 14929919) B14929919
theorem B2761343 : Blo 1839621 2761343 := bstep (se 1 (by rfl) ⟨2071007, by rfl⟩ : syracuseStep 2761343 = 4142015) B4142015
theorem B2761979 : Blo 1839621 2761979 := bstep (se 1 (by rfl) ⟨2071484, by rfl⟩ : syracuseStep 2761979 = 4142969) B4142969
theorem B33580777 : Blo 1839621 33580777 := bstep (se 2 (by rfl) ⟨12592791, by rfl⟩ : syracuseStep 33580777 = 25185583) B25185583
theorem B6635519 : Blo 1839621 6635519 := bstep (se 1 (by rfl) ⟨4976639, by rfl⟩ : syracuseStep 6635519 = 9953279) B9953279
theorem B90803215 : Blo 1839621 90803215 := bstep (se 1 (by rfl) ⟨68102411, by rfl⟩ : syracuseStep 90803215 = 136204823) B136204823
theorem B8391929 : Blo 1839621 8391929 := bstep (se 2 (by rfl) ⟨3146973, by rfl⟩ : syracuseStep 8391929 = 6293947) B6293947
theorem B9317915 : Blo 1839621 9317915 := bstep (se 1 (by rfl) ⟨6988436, by rfl⟩ : syracuseStep 9317915 = 13976873) B13976873
theorem B29839583 : Blo 1839621 29839583 := bstep (se 1 (by rfl) ⟨22379687, by rfl⟩ : syracuseStep 29839583 = 44759375) B44759375
theorem B13449527 : Blo 1839621 13449527 := bstep (se 1 (by rfl) ⟨10087145, by rfl⟩ : syracuseStep 13449527 = 20174291) B20174291
theorem B2071579 : Blo 1839621 2071579 := bstep (se 1 (by rfl) ⟨1553684, by rfl⟩ : syracuseStep 2071579 = 3107369) B3107369
theorem B121070953 : Blo 1839621 121070953 := bstep (se 2 (by rfl) ⟨45401607, by rfl⟩ : syracuseStep 121070953 = 90803215) B90803215
theorem B2762105 : Blo 1839621 2762105 := bstep (se 2 (by rfl) ⟨1035789, by rfl⟩ : syracuseStep 2762105 = 2071579) B2071579
theorem B6211943 : Blo 1839621 6211943 := bstep (se 1 (by rfl) ⟨4658957, by rfl⟩ : syracuseStep 6211943 = 9317915) B9317915
theorem B19893055 : Blo 1839621 19893055 := bstep (se 1 (by rfl) ⟨14919791, by rfl⟩ : syracuseStep 19893055 = 29839583) B29839583
theorem B8966351 : Blo 1839621 8966351 := bstep (se 1 (by rfl) ⟨6724763, by rfl⟩ : syracuseStep 8966351 = 13449527) B13449527
theorem B44774369 : Blo 1839621 44774369 := bstep (se 2 (by rfl) ⟨16790388, by rfl⟩ : syracuseStep 44774369 = 33580777) B33580777
theorem B1840895 : Blo 1839621 1840895 := bstep (se 1 (by rfl) ⟨1380671, by rfl⟩ : syracuseStep 1840895 = 2761343) B2761343
theorem B1841319 : Blo 1839621 1841319 := bstep (se 1 (by rfl) ⟨1380989, by rfl⟩ : syracuseStep 1841319 = 2761979) B2761979
theorem B4423679 : Blo 1839621 4423679 := bstep (se 1 (by rfl) ⟨3317759, by rfl⟩ : syracuseStep 4423679 = 6635519) B6635519
theorem B89513909 : Blo 1839621 89513909 := bstep (se 5 (by rfl) ⟨4195964, by rfl⟩ : syracuseStep 89513909 = 8391929) B8391929
theorem B2949119 : Blo 1839621 2949119 := bstep (se 1 (by rfl) ⟨2211839, by rfl⟩ : syracuseStep 2949119 = 4423679) B4423679
theorem B4141295 : Blo 1839621 4141295 := bstep (se 1 (by rfl) ⟨3105971, by rfl⟩ : syracuseStep 4141295 = 6211943) B6211943
theorem B161427937 : Blo 1839621 161427937 := bstep (se 2 (by rfl) ⟨60535476, by rfl⟩ : syracuseStep 161427937 = 121070953) B121070953
theorem B59675939 : Blo 1839621 59675939 := bstep (se 1 (by rfl) ⟨44756954, by rfl⟩ : syracuseStep 59675939 = 89513909) B89513909
theorem B5977567 : Blo 1839621 5977567 := bstep (se 1 (by rfl) ⟨4483175, by rfl⟩ : syracuseStep 5977567 = 8966351) B8966351
theorem B29849579 : Blo 1839621 29849579 := bstep (se 1 (by rfl) ⟨22387184, by rfl⟩ : syracuseStep 29849579 = 44774369) B44774369
theorem B1841403 : Blo 1839621 1841403 := bstep (se 1 (by rfl) ⟨1381052, by rfl⟩ : syracuseStep 1841403 = 2762105) B2762105
theorem B26524073 : Blo 1839621 26524073 := bstep (se 2 (by rfl) ⟨9946527, by rfl⟩ : syracuseStep 26524073 = 19893055) B19893055
theorem B2760863 : Blo 1839621 2760863 := bstep (se 1 (by rfl) ⟨2070647, by rfl⟩ : syracuseStep 2760863 = 4141295) B4141295
theorem B215237249 : Blo 1839621 215237249 := bstep (se 2 (by rfl) ⟨80713968, by rfl⟩ : syracuseStep 215237249 = 161427937) B161427937
theorem B19899719 : Blo 1839621 19899719 := bstep (se 1 (by rfl) ⟨14924789, by rfl⟩ : syracuseStep 19899719 = 29849579) B29849579
theorem B39783959 : Blo 1839621 39783959 := bstep (se 1 (by rfl) ⟨29837969, by rfl⟩ : syracuseStep 39783959 = 59675939) B59675939
theorem B17682715 : Blo 1839621 17682715 := bstep (se 1 (by rfl) ⟨13262036, by rfl⟩ : syracuseStep 17682715 = 26524073) B26524073
theorem B7970089 : Blo 1839621 7970089 := bstep (se 2 (by rfl) ⟨2988783, by rfl⟩ : syracuseStep 7970089 = 5977567) B5977567
theorem B1966079 : Blo 1839621 1966079 := bstep (se 1 (by rfl) ⟨1474559, by rfl⟩ : syracuseStep 1966079 = 2949119) B2949119
theorem B23576953 : Blo 1839621 23576953 := bstep (se 2 (by rfl) ⟨8841357, by rfl⟩ : syracuseStep 23576953 = 17682715) B17682715
theorem B143491499 : Blo 1839621 143491499 := bstep (se 1 (by rfl) ⟨107618624, by rfl⟩ : syracuseStep 143491499 = 215237249) B215237249
theorem B10626785 : Blo 1839621 10626785 := bstep (se 2 (by rfl) ⟨3985044, by rfl⟩ : syracuseStep 10626785 = 7970089) B7970089
theorem B13266479 : Blo 1839621 13266479 := bstep (se 1 (by rfl) ⟨9949859, by rfl⟩ : syracuseStep 13266479 = 19899719) B19899719
theorem B26522639 : Blo 1839621 26522639 := bstep (se 1 (by rfl) ⟨19891979, by rfl⟩ : syracuseStep 26522639 = 39783959) B39783959
theorem B1840575 : Blo 1839621 1840575 := bstep (se 1 (by rfl) ⟨1380431, by rfl⟩ : syracuseStep 1840575 = 2760863) B2760863
theorem B5242877 : Blo 1839621 5242877 := bstep (se 3 (by rfl) ⟨983039, by rfl⟩ : syracuseStep 5242877 = 1966079) B1966079
theorem B95660999 : Blo 1839621 95660999 := bstep (se 1 (by rfl) ⟨71745749, by rfl⟩ : syracuseStep 95660999 = 143491499) B143491499
theorem B31435937 : Blo 1839621 31435937 := bstep (se 2 (by rfl) ⟨11788476, by rfl⟩ : syracuseStep 31435937 = 23576953) B23576953
theorem B17681759 : Blo 1839621 17681759 := bstep (se 1 (by rfl) ⟨13261319, by rfl⟩ : syracuseStep 17681759 = 26522639) B26522639
theorem B8844319 : Blo 1839621 8844319 := bstep (se 1 (by rfl) ⟨6633239, by rfl⟩ : syracuseStep 8844319 = 13266479) B13266479
theorem B3495251 : Blo 1839621 3495251 := bstep (se 1 (by rfl) ⟨2621438, by rfl⟩ : syracuseStep 3495251 = 5242877) B5242877
theorem B7084523 : Blo 1839621 7084523 := bstep (se 1 (by rfl) ⟨5313392, by rfl⟩ : syracuseStep 7084523 = 10626785) B10626785
theorem B20957291 : Blo 1839621 20957291 := bstep (se 1 (by rfl) ⟨15717968, by rfl⟩ : syracuseStep 20957291 = 31435937) B31435937
theorem B11792425 : Blo 1839621 11792425 := bstep (se 2 (by rfl) ⟨4422159, by rfl⟩ : syracuseStep 11792425 = 8844319) B8844319
theorem B4723015 : Blo 1839621 4723015 := bstep (se 1 (by rfl) ⟨3542261, by rfl⟩ : syracuseStep 4723015 = 7084523) B7084523
theorem B9320669 : Blo 1839621 9320669 := bstep (se 3 (by rfl) ⟨1747625, by rfl⟩ : syracuseStep 9320669 = 3495251) B3495251
theorem B63773999 : Blo 1839621 63773999 := bstep (se 1 (by rfl) ⟨47830499, by rfl⟩ : syracuseStep 63773999 = 95660999) B95660999
theorem B11787839 : Blo 1839621 11787839 := bstep (se 1 (by rfl) ⟨8840879, by rfl⟩ : syracuseStep 11787839 = 17681759) B17681759
theorem B7858559 : Blo 1839621 7858559 := bstep (se 1 (by rfl) ⟨5893919, by rfl⟩ : syracuseStep 7858559 = 11787839) B11787839
theorem B15723233 : Blo 1839621 15723233 := bstep (se 2 (by rfl) ⟨5896212, by rfl⟩ : syracuseStep 15723233 = 11792425) B11792425
theorem B13971527 : Blo 1839621 13971527 := bstep (se 1 (by rfl) ⟨10478645, by rfl⟩ : syracuseStep 13971527 = 20957291) B20957291
theorem B6213779 : Blo 1839621 6213779 := bstep (se 1 (by rfl) ⟨4660334, by rfl⟩ : syracuseStep 6213779 = 9320669) B9320669
theorem B6297353 : Blo 1839621 6297353 := bstep (se 2 (by rfl) ⟨2361507, by rfl⟩ : syracuseStep 6297353 = 4723015) B4723015
theorem B42515999 : Blo 1839621 42515999 := bstep (se 1 (by rfl) ⟨31886999, by rfl⟩ : syracuseStep 42515999 = 63773999) B63773999
theorem B9314351 : Blo 1839621 9314351 := bstep (se 1 (by rfl) ⟨6985763, by rfl⟩ : syracuseStep 9314351 = 13971527) B13971527
theorem B4198235 : Blo 1839621 4198235 := bstep (se 1 (by rfl) ⟨3148676, by rfl⟩ : syracuseStep 4198235 = 6297353) B6297353
theorem B5239039 : Blo 1839621 5239039 := bstep (se 1 (by rfl) ⟨3929279, by rfl⟩ : syracuseStep 5239039 = 7858559) B7858559
theorem B10482155 : Blo 1839621 10482155 := bstep (se 1 (by rfl) ⟨7861616, by rfl⟩ : syracuseStep 10482155 = 15723233) B15723233
theorem B4142519 : Blo 1839621 4142519 := bstep (se 1 (by rfl) ⟨3106889, by rfl⟩ : syracuseStep 4142519 = 6213779) B6213779
theorem B28343999 : Blo 1839621 28343999 := bstep (se 1 (by rfl) ⟨21257999, by rfl⟩ : syracuseStep 28343999 = 42515999) B42515999
theorem B6209567 : Blo 1839621 6209567 := bstep (se 1 (by rfl) ⟨4657175, by rfl⟩ : syracuseStep 6209567 = 9314351) B9314351
theorem B6988103 : Blo 1839621 6988103 := bstep (se 1 (by rfl) ⟨5241077, by rfl⟩ : syracuseStep 6988103 = 10482155) B10482155
theorem B2761679 : Blo 1839621 2761679 := bstep (se 1 (by rfl) ⟨2071259, by rfl⟩ : syracuseStep 2761679 = 4142519) B4142519
theorem B44781173 : Blo 1839621 44781173 := bstep (se 5 (by rfl) ⟨2099117, by rfl⟩ : syracuseStep 44781173 = 4198235) B4198235
theorem B18895999 : Blo 1839621 18895999 := bstep (se 1 (by rfl) ⟨14171999, by rfl⟩ : syracuseStep 18895999 = 28343999) B28343999
theorem B6985385 : Blo 1839621 6985385 := bstep (se 2 (by rfl) ⟨2619519, by rfl⟩ : syracuseStep 6985385 = 5239039) B5239039
theorem B29854115 : Blo 1839621 29854115 := bstep (se 1 (by rfl) ⟨22390586, by rfl⟩ : syracuseStep 29854115 = 44781173) B44781173
theorem B4139711 : Blo 1839621 4139711 := bstep (se 1 (by rfl) ⟨3104783, by rfl⟩ : syracuseStep 4139711 = 6209567) B6209567
theorem B4656923 : Blo 1839621 4656923 := bstep (se 1 (by rfl) ⟨3492692, by rfl⟩ : syracuseStep 4656923 = 6985385) B6985385
theorem B25194665 : Blo 1839621 25194665 := bstep (se 2 (by rfl) ⟨9447999, by rfl⟩ : syracuseStep 25194665 = 18895999) B18895999
theorem B4658735 : Blo 1839621 4658735 := bstep (se 1 (by rfl) ⟨3494051, by rfl⟩ : syracuseStep 4658735 = 6988103) B6988103
theorem B1841119 : Blo 1839621 1841119 := bstep (se 1 (by rfl) ⟨1380839, by rfl⟩ : syracuseStep 1841119 = 2761679) B2761679
theorem B3105823 : Blo 1839621 3105823 := bstep (se 1 (by rfl) ⟨2329367, by rfl⟩ : syracuseStep 3105823 = 4658735) B4658735
theorem B16796443 : Blo 1839621 16796443 := bstep (se 1 (by rfl) ⟨12597332, by rfl⟩ : syracuseStep 16796443 = 25194665) B25194665
theorem B19902743 : Blo 1839621 19902743 := bstep (se 1 (by rfl) ⟨14927057, by rfl⟩ : syracuseStep 19902743 = 29854115) B29854115
theorem B2759807 : Blo 1839621 2759807 := bstep (se 1 (by rfl) ⟨2069855, by rfl⟩ : syracuseStep 2759807 = 4139711) B4139711
theorem B3104615 : Blo 1839621 3104615 := bstep (se 1 (by rfl) ⟨2328461, by rfl⟩ : syracuseStep 3104615 = 4656923) B4656923
theorem B4141097 : Blo 1839621 4141097 := bstep (se 2 (by rfl) ⟨1552911, by rfl⟩ : syracuseStep 4141097 = 3105823) B3105823
theorem B1839871 : Blo 1839621 1839871 := bstep (se 1 (by rfl) ⟨1379903, by rfl⟩ : syracuseStep 1839871 = 2759807) B2759807
theorem B2069743 : Blo 1839621 2069743 := bstep (se 1 (by rfl) ⟨1552307, by rfl⟩ : syracuseStep 2069743 = 3104615) B3104615
theorem B13268495 : Blo 1839621 13268495 := bstep (se 1 (by rfl) ⟨9951371, by rfl⟩ : syracuseStep 13268495 = 19902743) B19902743
theorem B22395257 : Blo 1839621 22395257 := bstep (se 2 (by rfl) ⟨8398221, by rfl⟩ : syracuseStep 22395257 = 16796443) B16796443
theorem B2760731 : Blo 1839621 2760731 := bstep (se 1 (by rfl) ⟨2070548, by rfl⟩ : syracuseStep 2760731 = 4141097) B4141097
theorem B35382653 : Blo 1839621 35382653 := bstep (se 3 (by rfl) ⟨6634247, by rfl⟩ : syracuseStep 35382653 = 13268495) B13268495
theorem B14930171 : Blo 1839621 14930171 := bstep (se 1 (by rfl) ⟨11197628, by rfl⟩ : syracuseStep 14930171 = 22395257) B22395257
theorem B2759657 : Blo 1839621 2759657 := bstep (se 2 (by rfl) ⟨1034871, by rfl⟩ : syracuseStep 2759657 = 2069743) B2069743
theorem B9953447 : Blo 1839621 9953447 := bstep (se 1 (by rfl) ⟨7465085, by rfl⟩ : syracuseStep 9953447 = 14930171) B14930171
theorem B23588435 : Blo 1839621 23588435 := bstep (se 1 (by rfl) ⟨17691326, by rfl⟩ : syracuseStep 23588435 = 35382653) B35382653
theorem B1839771 : Blo 1839621 1839771 := bstep (se 1 (by rfl) ⟨1379828, by rfl⟩ : syracuseStep 1839771 = 2759657) B2759657
theorem B1840487 : Blo 1839621 1840487 := bstep (se 1 (by rfl) ⟨1380365, by rfl⟩ : syracuseStep 1840487 = 2760731) B2760731
theorem B106170101 : Blo 1839621 106170101 := bstep (se 5 (by rfl) ⟨4976723, by rfl⟩ : syracuseStep 106170101 = 9953447) B9953447
theorem B15725623 : Blo 1839621 15725623 := bstep (se 1 (by rfl) ⟨11794217, by rfl⟩ : syracuseStep 15725623 = 23588435) B23588435
theorem B70780067 : Blo 1839621 70780067 := bstep (se 1 (by rfl) ⟨53085050, by rfl⟩ : syracuseStep 70780067 = 106170101) B106170101
theorem B20967497 : Blo 1839621 20967497 := bstep (se 2 (by rfl) ⟨7862811, by rfl⟩ : syracuseStep 20967497 = 15725623) B15725623
theorem B47186711 : Blo 1839621 47186711 := bstep (se 1 (by rfl) ⟨35390033, by rfl⟩ : syracuseStep 47186711 = 70780067) B70780067
theorem B13978331 : Blo 1839621 13978331 := bstep (se 1 (by rfl) ⟨10483748, by rfl⟩ : syracuseStep 13978331 = 20967497) B20967497
theorem B31457807 : Blo 1839621 31457807 := bstep (se 1 (by rfl) ⟨23593355, by rfl⟩ : syracuseStep 31457807 = 47186711) B47186711
theorem B9318887 : Blo 1839621 9318887 := bstep (se 1 (by rfl) ⟨6989165, by rfl⟩ : syracuseStep 9318887 = 13978331) B13978331
theorem B20971871 : Blo 1839621 20971871 := bstep (se 1 (by rfl) ⟨15728903, by rfl⟩ : syracuseStep 20971871 = 31457807) B31457807
theorem B6212591 : Blo 1839621 6212591 := bstep (se 1 (by rfl) ⟨4659443, by rfl⟩ : syracuseStep 6212591 = 9318887) B9318887
theorem B4141727 : Blo 1839621 4141727 := bstep (se 1 (by rfl) ⟨3106295, by rfl⟩ : syracuseStep 4141727 = 6212591) B6212591
theorem B13981247 : Blo 1839621 13981247 := bstep (se 1 (by rfl) ⟨10485935, by rfl⟩ : syracuseStep 13981247 = 20971871) B20971871
theorem B2761151 : Blo 1839621 2761151 := bstep (se 1 (by rfl) ⟨2070863, by rfl⟩ : syracuseStep 2761151 = 4141727) B4141727
theorem B9320831 : Blo 1839621 9320831 := bstep (se 1 (by rfl) ⟨6990623, by rfl⟩ : syracuseStep 9320831 = 13981247) B13981247
theorem B6213887 : Blo 1839621 6213887 := bstep (se 1 (by rfl) ⟨4660415, by rfl⟩ : syracuseStep 6213887 = 9320831) B9320831
theorem B1840767 : Blo 1839621 1840767 := bstep (se 1 (by rfl) ⟨1380575, by rfl⟩ : syracuseStep 1840767 = 2761151) B2761151
theorem B4142591 : Blo 1839621 4142591 := bstep (se 1 (by rfl) ⟨3106943, by rfl⟩ : syracuseStep 4142591 = 6213887) B6213887
theorem B2761727 : Blo 1839621 2761727 := bstep (se 1 (by rfl) ⟨2071295, by rfl⟩ : syracuseStep 2761727 = 4142591) B4142591
theorem B1841151 : Blo 1839621 1841151 := bstep (se 1 (by rfl) ⟨1380863, by rfl⟩ : syracuseStep 1841151 = 2761727) B2761727

theorem C0 (j : ℕ) (h1 : 459905 ≤ j) (h2 : j ≤ 460404) : Blo 1839621 (4 * j + 3) := by
  interval_cases j
  · exact B1839623
  · exact B1839627
  · exact B1839631
  · exact B1839635
  · exact B1839639
  · exact B1839643
  · exact B1839647
  · exact B1839651
  · exact B1839655
  · exact B1839659
  · exact B1839663
  · exact B1839667
  · exact B1839671
  · exact B1839675
  · exact B1839679
  · exact B1839683
  · exact B1839687
  · exact B1839691
  · exact B1839695
  · exact B1839699
  · exact B1839703
  · exact B1839707
  · exact B1839711
  · exact B1839715
  · exact B1839719
  · exact B1839723
  · exact B1839727
  · exact B1839731
  · exact B1839735
  · exact B1839739
  · exact B1839743
  · exact B1839747
  · exact B1839751
  · exact B1839755
  · exact B1839759
  · exact B1839763
  · exact B1839767
  · exact B1839771
  · exact B1839775
  · exact B1839779
  · exact B1839783
  · exact B1839787
  · exact B1839791
  · exact B1839795
  · exact B1839799
  · exact B1839803
  · exact B1839807
  · exact B1839811
  · exact B1839815
  · exact B1839819
  · exact B1839823
  · exact B1839827
  · exact B1839831
  · exact B1839835
  · exact B1839839
  · exact B1839843
  · exact B1839847
  · exact B1839851
  · exact B1839855
  · exact B1839859
  · exact B1839863
  · exact B1839867
  · exact B1839871
  · exact B1839875
  · exact B1839879
  · exact B1839883
  · exact B1839887
  · exact B1839891
  · exact B1839895
  · exact B1839899
  · exact B1839903
  · exact B1839907
  · exact B1839911
  · exact B1839915
  · exact B1839919
  · exact B1839923
  · exact B1839927
  · exact B1839931
  · exact B1839935
  · exact B1839939
  · exact B1839943
  · exact B1839947
  · exact B1839951
  · exact B1839955
  · exact B1839959
  · exact B1839963
  · exact B1839967
  · exact B1839971
  · exact B1839975
  · exact B1839979
  · exact B1839983
  · exact B1839987
  · exact B1839991
  · exact B1839995
  · exact B1839999
  · exact B1840003
  · exact B1840007
  · exact B1840011
  · exact B1840015
  · exact B1840019
  · exact B1840023
  · exact B1840027
  · exact B1840031
  · exact B1840035
  · exact B1840039
  · exact B1840043
  · exact B1840047
  · exact B1840051
  · exact B1840055
  · exact B1840059
  · exact B1840063
  · exact B1840067
  · exact B1840071
  · exact B1840075
  · exact B1840079
  · exact B1840083
  · exact B1840087
  · exact B1840091
  · exact B1840095
  · exact B1840099
  · exact B1840103
  · exact B1840107
  · exact B1840111
  · exact B1840115
  · exact B1840119
  · exact B1840123
  · exact B1840127
  · exact B1840131
  · exact B1840135
  · exact B1840139
  · exact B1840143
  · exact B1840147
  · exact B1840151
  · exact B1840155
  · exact B1840159
  · exact B1840163
  · exact B1840167
  · exact B1840171
  · exact B1840175
  · exact B1840179
  · exact B1840183
  · exact B1840187
  · exact B1840191
  · exact B1840195
  · exact B1840199
  · exact B1840203
  · exact B1840207
  · exact B1840211
  · exact B1840215
  · exact B1840219
  · exact B1840223
  · exact B1840227
  · exact B1840231
  · exact B1840235
  · exact B1840239
  · exact B1840243
  · exact B1840247
  · exact B1840251
  · exact B1840255
  · exact B1840259
  · exact B1840263
  · exact B1840267
  · exact B1840271
  · exact B1840275
  · exact B1840279
  · exact B1840283
  · exact B1840287
  · exact B1840291
  · exact B1840295
  · exact B1840299
  · exact B1840303
  · exact B1840307
  · exact B1840311
  · exact B1840315
  · exact B1840319
  · exact B1840323
  · exact B1840327
  · exact B1840331
  · exact B1840335
  · exact B1840339
  · exact B1840343
  · exact B1840347
  · exact B1840351
  · exact B1840355
  · exact B1840359
  · exact B1840363
  · exact B1840367
  · exact B1840371
  · exact B1840375
  · exact B1840379
  · exact B1840383
  · exact B1840387
  · exact B1840391
  · exact B1840395
  · exact B1840399
  · exact B1840403
  · exact B1840407
  · exact B1840411
  · exact B1840415
  · exact B1840419
  · exact B1840423
  · exact B1840427
  · exact B1840431
  · exact B1840435
  · exact B1840439
  · exact B1840443
  · exact B1840447
  · exact B1840451
  · exact B1840455
  · exact B1840459
  · exact B1840463
  · exact B1840467
  · exact B1840471
  · exact B1840475
  · exact B1840479
  · exact B1840483
  · exact B1840487
  · exact B1840491
  · exact B1840495
  · exact B1840499
  · exact B1840503
  · exact B1840507
  · exact B1840511
  · exact B1840515
  · exact B1840519
  · exact B1840523
  · exact B1840527
  · exact B1840531
  · exact B1840535
  · exact B1840539
  · exact B1840543
  · exact B1840547
  · exact B1840551
  · exact B1840555
  · exact B1840559
  · exact B1840563
  · exact B1840567
  · exact B1840571
  · exact B1840575
  · exact B1840579
  · exact B1840583
  · exact B1840587
  · exact B1840591
  · exact B1840595
  · exact B1840599
  · exact B1840603
  · exact B1840607
  · exact B1840611
  · exact B1840615
  · exact B1840619
  · exact B1840623
  · exact B1840627
  · exact B1840631
  · exact B1840635
  · exact B1840639
  · exact B1840643
  · exact B1840647
  · exact B1840651
  · exact B1840655
  · exact B1840659
  · exact B1840663
  · exact B1840667
  · exact B1840671
  · exact B1840675
  · exact B1840679
  · exact B1840683
  · exact B1840687
  · exact B1840691
  · exact B1840695
  · exact B1840699
  · exact B1840703
  · exact B1840707
  · exact B1840711
  · exact B1840715
  · exact B1840719
  · exact B1840723
  · exact B1840727
  · exact B1840731
  · exact B1840735
  · exact B1840739
  · exact B1840743
  · exact B1840747
  · exact B1840751
  · exact B1840755
  · exact B1840759
  · exact B1840763
  · exact B1840767
  · exact B1840771
  · exact B1840775
  · exact B1840779
  · exact B1840783
  · exact B1840787
  · exact B1840791
  · exact B1840795
  · exact B1840799
  · exact B1840803
  · exact B1840807
  · exact B1840811
  · exact B1840815
  · exact B1840819
  · exact B1840823
  · exact B1840827
  · exact B1840831
  · exact B1840835
  · exact B1840839
  · exact B1840843
  · exact B1840847
  · exact B1840851
  · exact B1840855
  · exact B1840859
  · exact B1840863
  · exact B1840867
  · exact B1840871
  · exact B1840875
  · exact B1840879
  · exact B1840883
  · exact B1840887
  · exact B1840891
  · exact B1840895
  · exact B1840899
  · exact B1840903
  · exact B1840907
  · exact B1840911
  · exact B1840915
  · exact B1840919
  · exact B1840923
  · exact B1840927
  · exact B1840931
  · exact B1840935
  · exact B1840939
  · exact B1840943
  · exact B1840947
  · exact B1840951
  · exact B1840955
  · exact B1840959
  · exact B1840963
  · exact B1840967
  · exact B1840971
  · exact B1840975
  · exact B1840979
  · exact B1840983
  · exact B1840987
  · exact B1840991
  · exact B1840995
  · exact B1840999
  · exact B1841003
  · exact B1841007
  · exact B1841011
  · exact B1841015
  · exact B1841019
  · exact B1841023
  · exact B1841027
  · exact B1841031
  · exact B1841035
  · exact B1841039
  · exact B1841043
  · exact B1841047
  · exact B1841051
  · exact B1841055
  · exact B1841059
  · exact B1841063
  · exact B1841067
  · exact B1841071
  · exact B1841075
  · exact B1841079
  · exact B1841083
  · exact B1841087
  · exact B1841091
  · exact B1841095
  · exact B1841099
  · exact B1841103
  · exact B1841107
  · exact B1841111
  · exact B1841115
  · exact B1841119
  · exact B1841123
  · exact B1841127
  · exact B1841131
  · exact B1841135
  · exact B1841139
  · exact B1841143
  · exact B1841147
  · exact B1841151
  · exact B1841155
  · exact B1841159
  · exact B1841163
  · exact B1841167
  · exact B1841171
  · exact B1841175
  · exact B1841179
  · exact B1841183
  · exact B1841187
  · exact B1841191
  · exact B1841195
  · exact B1841199
  · exact B1841203
  · exact B1841207
  · exact B1841211
  · exact B1841215
  · exact B1841219
  · exact B1841223
  · exact B1841227
  · exact B1841231
  · exact B1841235
  · exact B1841239
  · exact B1841243
  · exact B1841247
  · exact B1841251
  · exact B1841255
  · exact B1841259
  · exact B1841263
  · exact B1841267
  · exact B1841271
  · exact B1841275
  · exact B1841279
  · exact B1841283
  · exact B1841287
  · exact B1841291
  · exact B1841295
  · exact B1841299
  · exact B1841303
  · exact B1841307
  · exact B1841311
  · exact B1841315
  · exact B1841319
  · exact B1841323
  · exact B1841327
  · exact B1841331
  · exact B1841335
  · exact B1841339
  · exact B1841343
  · exact B1841347
  · exact B1841351
  · exact B1841355
  · exact B1841359
  · exact B1841363
  · exact B1841367
  · exact B1841371
  · exact B1841375
  · exact B1841379
  · exact B1841383
  · exact B1841387
  · exact B1841391
  · exact B1841395
  · exact B1841399
  · exact B1841403
  · exact B1841407
  · exact B1841411
  · exact B1841415
  · exact B1841419
  · exact B1841423
  · exact B1841427
  · exact B1841431
  · exact B1841435
  · exact B1841439
  · exact B1841443
  · exact B1841447
  · exact B1841451
  · exact B1841455
  · exact B1841459
  · exact B1841463
  · exact B1841467
  · exact B1841471
  · exact B1841475
  · exact B1841479
  · exact B1841483
  · exact B1841487
  · exact B1841491
  · exact B1841495
  · exact B1841499
  · exact B1841503
  · exact B1841507
  · exact B1841511
  · exact B1841515
  · exact B1841519
  · exact B1841523
  · exact B1841527
  · exact B1841531
  · exact B1841535
  · exact B1841539
  · exact B1841543
  · exact B1841547
  · exact B1841551
  · exact B1841555
  · exact B1841559
  · exact B1841563
  · exact B1841567
  · exact B1841571
  · exact B1841575
  · exact B1841579
  · exact B1841583
  · exact B1841587
  · exact B1841591
  · exact B1841595
  · exact B1841599
  · exact B1841603
  · exact B1841607
  · exact B1841611
  · exact B1841615
  · exact B1841619

theorem solution (m : ℕ) (hlo : 1839621 ≤ m) (hhi : m ≤ 1841621) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 459905 ≤ j := by omega
    have hj2 : j ≤ 460404 := by omega
    have hb : Blo 1839621 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
