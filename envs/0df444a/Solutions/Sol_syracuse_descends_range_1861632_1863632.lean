-- Prove2me | solution 1 for syracuse_descends_range_1861632_1863632
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:10:51.042981+00:00
-- url     : https://prove2.me/submissions/feee175c-e30a-4e8f-b20d-faa935d671e1

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


theorem B2793485 : Blo 1861632 2793485 := bbase (se 3 (by rfl) ⟨523778, by rfl⟩ : syracuseStep 2793485 = 1047557) (by norm_num)
theorem B2793509 : Blo 1861632 2793509 := bbase (se 4 (by rfl) ⟨261891, by rfl⟩ : syracuseStep 2793509 = 523783) (by norm_num)
theorem B2793533 : Blo 1861632 2793533 := bbase (se 3 (by rfl) ⟨523787, by rfl⟩ : syracuseStep 2793533 = 1047575) (by norm_num)
theorem B7069781 : Blo 1861632 7069781 := bbase (se 8 (by rfl) ⟨41424, by rfl⟩ : syracuseStep 7069781 = 82849) (by norm_num)
theorem B2793557 : Blo 1861632 2793557 := bbase (se 8 (by rfl) ⟨16368, by rfl⟩ : syracuseStep 2793557 = 32737) (by norm_num)
theorem B2793581 : Blo 1861632 2793581 := bbase (se 3 (by rfl) ⟨523796, by rfl⟩ : syracuseStep 2793581 = 1047593) (by norm_num)
theorem B2793605 : Blo 1861632 2793605 := bbase (se 4 (by rfl) ⟨261900, by rfl⟩ : syracuseStep 2793605 = 523801) (by norm_num)
theorem B2793629 : Blo 1861632 2793629 := bbase (se 3 (by rfl) ⟨523805, by rfl⟩ : syracuseStep 2793629 = 1047611) (by norm_num)
theorem B2793653 : Blo 1861632 2793653 := bbase (se 5 (by rfl) ⟨130952, by rfl⟩ : syracuseStep 2793653 = 261905) (by norm_num)
theorem B2793677 : Blo 1861632 2793677 := bbase (se 3 (by rfl) ⟨523814, by rfl⟩ : syracuseStep 2793677 = 1047629) (by norm_num)
theorem B6283493 : Blo 1861632 6283493 := bbase (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) (by norm_num)
theorem B2793701 : Blo 1861632 2793701 := bbase (se 4 (by rfl) ⟨261909, by rfl⟩ : syracuseStep 2793701 = 523819) (by norm_num)
theorem B2793725 : Blo 1861632 2793725 := bbase (se 3 (by rfl) ⟨523823, by rfl⟩ : syracuseStep 2793725 = 1047647) (by norm_num)
theorem B2793749 : Blo 1861632 2793749 := bbase (se 6 (by rfl) ⟨65478, by rfl⟩ : syracuseStep 2793749 = 130957) (by norm_num)
theorem B4727069 : Blo 1861632 4727069 := bbase (se 3 (by rfl) ⟨886325, by rfl⟩ : syracuseStep 4727069 = 1772651) (by norm_num)
theorem B2793773 : Blo 1861632 2793773 := bbase (se 3 (by rfl) ⟨523832, by rfl⟩ : syracuseStep 2793773 = 1047665) (by norm_num)
theorem B2793797 : Blo 1861632 2793797 := bbase (se 4 (by rfl) ⟨261918, by rfl⟩ : syracuseStep 2793797 = 523837) (by norm_num)
theorem B2793821 : Blo 1861632 2793821 := bbase (se 3 (by rfl) ⟨523841, by rfl⟩ : syracuseStep 2793821 = 1047683) (by norm_num)
theorem B2793845 : Blo 1861632 2793845 := bbase (se 5 (by rfl) ⟨130961, by rfl⟩ : syracuseStep 2793845 = 261923) (by norm_num)
theorem B2793869 : Blo 1861632 2793869 := bbase (se 3 (by rfl) ⟨523850, by rfl⟩ : syracuseStep 2793869 = 1047701) (by norm_num)
theorem B7553429 : Blo 1861632 7553429 := bbase (se 6 (by rfl) ⟨177033, by rfl⟩ : syracuseStep 7553429 = 354067) (by norm_num)
theorem B2793893 : Blo 1861632 2793893 := bbase (se 4 (by rfl) ⟨261927, by rfl⟩ : syracuseStep 2793893 = 523855) (by norm_num)
theorem B2793917 : Blo 1861632 2793917 := bbase (se 3 (by rfl) ⟨523859, by rfl⟩ : syracuseStep 2793917 = 1047719) (by norm_num)
theorem B2793941 : Blo 1861632 2793941 := bbase (se 7 (by rfl) ⟨32741, by rfl⟩ : syracuseStep 2793941 = 65483) (by norm_num)
theorem B2793965 : Blo 1861632 2793965 := bbase (se 3 (by rfl) ⟨523868, by rfl⟩ : syracuseStep 2793965 = 1047737) (by norm_num)
theorem B8610293 : Blo 1861632 8610293 := bbase (se 5 (by rfl) ⟨403607, by rfl⟩ : syracuseStep 8610293 = 807215) (by norm_num)
theorem B7168517 : Blo 1861632 7168517 := bbase (se 4 (by rfl) ⟨672048, by rfl⟩ : syracuseStep 7168517 = 1344097) (by norm_num)
theorem B2793989 : Blo 1861632 2793989 := bbase (se 4 (by rfl) ⟨261936, by rfl⟩ : syracuseStep 2793989 = 523873) (by norm_num)
theorem B2794013 : Blo 1861632 2794013 := bbase (se 3 (by rfl) ⟨523877, by rfl⟩ : syracuseStep 2794013 = 1047755) (by norm_num)
theorem B2236981 : Blo 1861632 2236981 := bbase (se 5 (by rfl) ⟨104858, by rfl⟩ : syracuseStep 2236981 = 209717) (by norm_num)
theorem B2794037 : Blo 1861632 2794037 := bbase (se 5 (by rfl) ⟨130970, by rfl⟩ : syracuseStep 2794037 = 261941) (by norm_num)
theorem B2794061 : Blo 1861632 2794061 := bbase (se 3 (by rfl) ⟨523886, by rfl⟩ : syracuseStep 2794061 = 1047773) (by norm_num)
theorem B2794085 : Blo 1861632 2794085 := bbase (se 4 (by rfl) ⟨261945, by rfl⟩ : syracuseStep 2794085 = 523891) (by norm_num)
theorem B2794109 : Blo 1861632 2794109 := bbase (se 3 (by rfl) ⟨523895, by rfl⟩ : syracuseStep 2794109 = 1047791) (by norm_num)
theorem B6283925 : Blo 1861632 6283925 := bbase (se 6 (by rfl) ⟨147279, by rfl⟩ : syracuseStep 6283925 = 294559) (by norm_num)
theorem B2237077 : Blo 1861632 2237077 := bbase (se 6 (by rfl) ⟨52431, by rfl⟩ : syracuseStep 2237077 = 104863) (by norm_num)
theorem B2794133 : Blo 1861632 2794133 := bbase (se 6 (by rfl) ⟨65487, by rfl⟩ : syracuseStep 2794133 = 130975) (by norm_num)
theorem B26854037 : Blo 1861632 26854037 := bbase (se 6 (by rfl) ⟨629391, by rfl⟩ : syracuseStep 26854037 = 1258783) (by norm_num)
theorem B2761381 : Blo 1861632 2761381 := bbase (se 4 (by rfl) ⟨258879, by rfl⟩ : syracuseStep 2761381 = 517759) (by norm_num)
theorem B2794157 : Blo 1861632 2794157 := bbase (se 3 (by rfl) ⟨523904, by rfl⟩ : syracuseStep 2794157 = 1047809) (by norm_num)
theorem B2794181 : Blo 1861632 2794181 := bbase (se 4 (by rfl) ⟨261954, by rfl⟩ : syracuseStep 2794181 = 523909) (by norm_num)
theorem B2794205 : Blo 1861632 2794205 := bbase (se 3 (by rfl) ⟨523913, by rfl⟩ : syracuseStep 2794205 = 1047827) (by norm_num)
theorem B2794229 : Blo 1861632 2794229 := bbase (se 5 (by rfl) ⟨130979, by rfl⟩ : syracuseStep 2794229 = 261959) (by norm_num)
theorem B2794253 : Blo 1861632 2794253 := bbase (se 3 (by rfl) ⟨523922, by rfl⟩ : syracuseStep 2794253 = 1047845) (by norm_num)
theorem B2794277 : Blo 1861632 2794277 := bbase (se 4 (by rfl) ⟨261963, by rfl⟩ : syracuseStep 2794277 = 523927) (by norm_num)
theorem B2794301 : Blo 1861632 2794301 := bbase (se 3 (by rfl) ⟨523931, by rfl⟩ : syracuseStep 2794301 = 1047863) (by norm_num)
theorem B2794325 : Blo 1861632 2794325 := bbase (se 9 (by rfl) ⟨8186, by rfl⟩ : syracuseStep 2794325 = 16373) (by norm_num)
theorem B2982757 : Blo 1861632 2982757 := bbase (se 4 (by rfl) ⟨279633, by rfl⟩ : syracuseStep 2982757 = 559267) (by norm_num)
theorem B2794349 : Blo 1861632 2794349 := bbase (se 3 (by rfl) ⟨523940, by rfl⟩ : syracuseStep 2794349 = 1047881) (by norm_num)
theorem B2794373 : Blo 1861632 2794373 := bbase (se 4 (by rfl) ⟨261972, by rfl⟩ : syracuseStep 2794373 = 523945) (by norm_num)
theorem B2794397 : Blo 1861632 2794397 := bbase (se 3 (by rfl) ⟨523949, by rfl⟩ : syracuseStep 2794397 = 1047899) (by norm_num)
theorem B2794421 : Blo 1861632 2794421 := bbase (se 5 (by rfl) ⟨130988, by rfl⟩ : syracuseStep 2794421 = 261977) (by norm_num)
theorem B2794445 : Blo 1861632 2794445 := bbase (se 3 (by rfl) ⟨523958, by rfl⟩ : syracuseStep 2794445 = 1047917) (by norm_num)
theorem B2794469 : Blo 1861632 2794469 := bbase (se 4 (by rfl) ⟨261981, by rfl⟩ : syracuseStep 2794469 = 523963) (by norm_num)
theorem B2794493 : Blo 1861632 2794493 := bbase (se 3 (by rfl) ⟨523967, by rfl⟩ : syracuseStep 2794493 = 1047935) (by norm_num)
theorem B2794517 : Blo 1861632 2794517 := bbase (se 6 (by rfl) ⟨65496, by rfl⟩ : syracuseStep 2794517 = 130993) (by norm_num)
theorem B2794541 : Blo 1861632 2794541 := bbase (se 3 (by rfl) ⟨523976, by rfl⟩ : syracuseStep 2794541 = 1047953) (by norm_num)
theorem B6284357 : Blo 1861632 6284357 := bbase (se 4 (by rfl) ⟨589158, by rfl⟩ : syracuseStep 6284357 = 1178317) (by norm_num)
theorem B2794565 : Blo 1861632 2794565 := bbase (se 4 (by rfl) ⟨261990, by rfl⟩ : syracuseStep 2794565 = 523981) (by norm_num)
theorem B2794589 : Blo 1861632 2794589 := bbase (se 3 (by rfl) ⟨523985, by rfl⟩ : syracuseStep 2794589 = 1047971) (by norm_num)
theorem B8954981 : Blo 1861632 8954981 := bbase (se 4 (by rfl) ⟨839529, by rfl⟩ : syracuseStep 8954981 = 1679059) (by norm_num)
theorem B2794613 : Blo 1861632 2794613 := bbase (se 5 (by rfl) ⟨130997, by rfl⟩ : syracuseStep 2794613 = 261995) (by norm_num)
theorem B2794637 : Blo 1861632 2794637 := bbase (se 3 (by rfl) ⟨523994, by rfl⟩ : syracuseStep 2794637 = 1047989) (by norm_num)
theorem B9430181 : Blo 1861632 9430181 := bbase (se 4 (by rfl) ⟨884079, by rfl⟩ : syracuseStep 9430181 = 1768159) (by norm_num)
theorem B2794661 : Blo 1861632 2794661 := bbase (se 4 (by rfl) ⟨261999, by rfl⟩ : syracuseStep 2794661 = 523999) (by norm_num)
theorem B2794685 : Blo 1861632 2794685 := bbase (se 3 (by rfl) ⟨524003, by rfl⟩ : syracuseStep 2794685 = 1048007) (by norm_num)
theorem B2794709 : Blo 1861632 2794709 := bbase (se 7 (by rfl) ⟨32750, by rfl⟩ : syracuseStep 2794709 = 65501) (by norm_num)
theorem B2794733 : Blo 1861632 2794733 := bbase (se 3 (by rfl) ⟨524012, by rfl⟩ : syracuseStep 2794733 = 1048025) (by norm_num)
theorem B2794757 : Blo 1861632 2794757 := bbase (se 4 (by rfl) ⟨262008, by rfl⟩ : syracuseStep 2794757 = 524017) (by norm_num)
theorem B2123029 : Blo 1861632 2123029 := bbase (se 6 (by rfl) ⟨49758, by rfl⟩ : syracuseStep 2123029 = 99517) (by norm_num)
theorem B2794781 : Blo 1861632 2794781 := bbase (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) (by norm_num)
theorem B2516269 : Blo 1861632 2516269 := bbase (se 3 (by rfl) ⟨471800, by rfl⟩ : syracuseStep 2516269 = 943601) (by norm_num)
theorem B2794805 : Blo 1861632 2794805 := bbase (se 5 (by rfl) ⟨131006, by rfl⟩ : syracuseStep 2794805 = 262013) (by norm_num)
theorem B14148917 : Blo 1861632 14148917 := bbase (se 5 (by rfl) ⟨663230, by rfl⟩ : syracuseStep 14148917 = 1326461) (by norm_num)
theorem B6710597 : Blo 1861632 6710597 := bbase (se 4 (by rfl) ⟨629118, by rfl⟩ : syracuseStep 6710597 = 1258237) (by norm_num)
theorem B2794829 : Blo 1861632 2794829 := bbase (se 3 (by rfl) ⟨524030, by rfl⟩ : syracuseStep 2794829 = 1048061) (by norm_num)
theorem B12739925 : Blo 1861632 12739925 := bbase (se 12 (by rfl) ⟨4665, by rfl⟩ : syracuseStep 12739925 = 9331) (by norm_num)
theorem B2794853 : Blo 1861632 2794853 := bbase (se 4 (by rfl) ⟨262017, by rfl⟩ : syracuseStep 2794853 = 524035) (by norm_num)
theorem B2794877 : Blo 1861632 2794877 := bbase (se 3 (by rfl) ⟨524039, by rfl⟩ : syracuseStep 2794877 = 1048079) (by norm_num)
theorem B2794901 : Blo 1861632 2794901 := bbase (se 6 (by rfl) ⟨65505, by rfl⟩ : syracuseStep 2794901 = 131011) (by norm_num)
theorem B2794925 : Blo 1861632 2794925 := bbase (se 3 (by rfl) ⟨524048, by rfl⟩ : syracuseStep 2794925 = 1048097) (by norm_num)
theorem B2794949 : Blo 1861632 2794949 := bbase (se 4 (by rfl) ⟨262026, by rfl⟩ : syracuseStep 2794949 = 524053) (by norm_num)
theorem B9561557 : Blo 1861632 9561557 := bbase (se 7 (by rfl) ⟨112049, by rfl⟩ : syracuseStep 9561557 = 224099) (by norm_num)
theorem B2794973 : Blo 1861632 2794973 := bbase (se 3 (by rfl) ⟨524057, by rfl⟩ : syracuseStep 2794973 = 1048115) (by norm_num)
theorem B5301733 : Blo 1861632 5301733 := bbase (se 4 (by rfl) ⟨497037, by rfl⟩ : syracuseStep 5301733 = 994075) (by norm_num)
theorem B6284789 : Blo 1861632 6284789 := bbase (se 5 (by rfl) ⟨294599, by rfl⟩ : syracuseStep 6284789 = 589199) (by norm_num)
theorem B2794997 : Blo 1861632 2794997 := bbase (se 5 (by rfl) ⟨131015, by rfl⟩ : syracuseStep 2794997 = 262031) (by norm_num)
theorem B2795021 : Blo 1861632 2795021 := bbase (se 3 (by rfl) ⟨524066, by rfl⟩ : syracuseStep 2795021 = 1048133) (by norm_num)
theorem B2795045 : Blo 1861632 2795045 := bbase (se 4 (by rfl) ⟨262035, by rfl⟩ : syracuseStep 2795045 = 524071) (by norm_num)
theorem B3778085 : Blo 1861632 3778085 := bbase (se 4 (by rfl) ⟨354195, by rfl⟩ : syracuseStep 3778085 = 708391) (by norm_num)
theorem B2795069 : Blo 1861632 2795069 := bbase (se 3 (by rfl) ⟨524075, by rfl⟩ : syracuseStep 2795069 = 1048151) (by norm_num)
theorem B11322965 : Blo 1861632 11322965 := bbase (se 8 (by rfl) ⟨66345, by rfl⟩ : syracuseStep 11322965 = 132691) (by norm_num)
theorem B2795093 : Blo 1861632 2795093 := bbase (se 8 (by rfl) ⟨16377, by rfl⟩ : syracuseStep 2795093 = 32755) (by norm_num)
theorem B2795117 : Blo 1861632 2795117 := bbase (se 3 (by rfl) ⟨524084, by rfl⟩ : syracuseStep 2795117 = 1048169) (by norm_num)
theorem B2123381 : Blo 1861632 2123381 := bbase (se 5 (by rfl) ⟨99533, by rfl⟩ : syracuseStep 2123381 = 199067) (by norm_num)
theorem B2238077 : Blo 1861632 2238077 := bbase (se 3 (by rfl) ⟨419639, by rfl⟩ : syracuseStep 2238077 = 839279) (by norm_num)
theorem B2795141 : Blo 1861632 2795141 := bbase (se 4 (by rfl) ⟨262044, by rfl⟩ : syracuseStep 2795141 = 524089) (by norm_num)
theorem B2795165 : Blo 1861632 2795165 := bbase (se 3 (by rfl) ⟨524093, by rfl⟩ : syracuseStep 2795165 = 1048187) (by norm_num)
theorem B2795189 : Blo 1861632 2795189 := bbase (se 5 (by rfl) ⟨131024, by rfl⟩ : syracuseStep 2795189 = 262049) (by norm_num)
theorem B2795213 : Blo 1861632 2795213 := bbase (se 3 (by rfl) ⟨524102, by rfl⟩ : syracuseStep 2795213 = 1048205) (by norm_num)
theorem B14141141 : Blo 1861632 14141141 := bbase (se 7 (by rfl) ⟨165716, by rfl⟩ : syracuseStep 14141141 = 331433) (by norm_num)
theorem B16131797 : Blo 1861632 16131797 := bbase (se 7 (by rfl) ⟨189044, by rfl⟩ : syracuseStep 16131797 = 378089) (by norm_num)
theorem B4474597 : Blo 1861632 4474597 := bbase (se 4 (by rfl) ⟨419493, by rfl⟩ : syracuseStep 4474597 = 838987) (by norm_num)
theorem B2795237 : Blo 1861632 2795237 := bbase (se 4 (by rfl) ⟨262053, by rfl⟩ : syracuseStep 2795237 = 524107) (by norm_num)
theorem B2795261 : Blo 1861632 2795261 := bbase (se 3 (by rfl) ⟨524111, by rfl⟩ : syracuseStep 2795261 = 1048223) (by norm_num)
theorem B4777741 : Blo 1861632 4777741 := bbase (se 3 (by rfl) ⟨895826, by rfl⟩ : syracuseStep 4777741 = 1791653) (by norm_num)
theorem B2795285 : Blo 1861632 2795285 := bbase (se 6 (by rfl) ⟨65514, by rfl⟩ : syracuseStep 2795285 = 131029) (by norm_num)
theorem B2795309 : Blo 1861632 2795309 := bbase (se 3 (by rfl) ⟨524120, by rfl⟩ : syracuseStep 2795309 = 1048241) (by norm_num)
theorem B6801221 : Blo 1861632 6801221 := bbase (se 4 (by rfl) ⟨637614, by rfl⟩ : syracuseStep 6801221 = 1275229) (by norm_num)
theorem B4474693 : Blo 1861632 4474693 := bbase (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) (by norm_num)
theorem B2795333 : Blo 1861632 2795333 := bbase (se 4 (by rfl) ⟨262062, by rfl⟩ : syracuseStep 2795333 = 524125) (by norm_num)
theorem B2795357 : Blo 1861632 2795357 := bbase (se 3 (by rfl) ⟨524129, by rfl⟩ : syracuseStep 2795357 = 1048259) (by norm_num)
theorem B2795381 : Blo 1861632 2795381 := bbase (se 5 (by rfl) ⟨131033, by rfl⟩ : syracuseStep 2795381 = 262067) (by norm_num)
theorem B2795405 : Blo 1861632 2795405 := bbase (se 3 (by rfl) ⟨524138, by rfl⟩ : syracuseStep 2795405 = 1048277) (by norm_num)
theorem B2238365 : Blo 1861632 2238365 := bbase (se 3 (by rfl) ⟨419693, by rfl⟩ : syracuseStep 2238365 = 839387) (by norm_num)
theorem B4712357 : Blo 1861632 4712357 := bbase (se 4 (by rfl) ⟨441783, by rfl⟩ : syracuseStep 4712357 = 883567) (by norm_num)
theorem B6285221 : Blo 1861632 6285221 := bbase (se 4 (by rfl) ⟨589239, by rfl⟩ : syracuseStep 6285221 = 1178479) (by norm_num)
theorem B2795429 : Blo 1861632 2795429 := bbase (se 4 (by rfl) ⟨262071, by rfl⟩ : syracuseStep 2795429 = 524143) (by norm_num)
theorem B2123713 : Blo 1861632 2123713 := bbase (se 2 (by rfl) ⟨796392, by rfl⟩ : syracuseStep 2123713 = 1592785) (by norm_num)
theorem B5105605 : Blo 1861632 5105605 := bbase (se 4 (by rfl) ⟨478650, by rfl⟩ : syracuseStep 5105605 = 957301) (by norm_num)
theorem B2017229 : Blo 1861632 2017229 := bbase (se 3 (by rfl) ⟨378230, by rfl⟩ : syracuseStep 2017229 = 756461) (by norm_num)
theorem B4474885 : Blo 1861632 4474885 := bbase (se 4 (by rfl) ⟨419520, by rfl⟩ : syracuseStep 4474885 = 839041) (by norm_num)
theorem B2983949 : Blo 1861632 2983949 := bbase (se 3 (by rfl) ⟨559490, by rfl⟩ : syracuseStep 2983949 = 1118981) (by norm_num)
theorem B2238529 : Blo 1861632 2238529 := bbase (se 2 (by rfl) ⟨839448, by rfl⟩ : syracuseStep 2238529 = 1678897) (by norm_num)
theorem B2238557 : Blo 1861632 2238557 := bbase (se 3 (by rfl) ⟨419729, by rfl⟩ : syracuseStep 2238557 = 839459) (by norm_num)
theorem B7071893 : Blo 1861632 7071893 := bbase (se 6 (by rfl) ⟨165747, by rfl⟩ : syracuseStep 7071893 = 331495) (by norm_num)
theorem B2984141 : Blo 1861632 2984141 := bbase (se 3 (by rfl) ⟨559526, by rfl⟩ : syracuseStep 2984141 = 1119053) (by norm_num)
theorem B2238673 : Blo 1861632 2238673 := bbase (se 2 (by rfl) ⟨839502, by rfl⟩ : syracuseStep 2238673 = 1679005) (by norm_num)
theorem B4712701 : Blo 1861632 4712701 := bbase (se 3 (by rfl) ⟨883631, by rfl⟩ : syracuseStep 4712701 = 1767263) (by norm_num)
theorem B2238769 : Blo 1861632 2238769 := bbase (se 2 (by rfl) ⟨839538, by rfl⟩ : syracuseStep 2238769 = 1679077) (by norm_num)
theorem B4475213 : Blo 1861632 4475213 := bbase (se 3 (by rfl) ⟨839102, by rfl⟩ : syracuseStep 4475213 = 1678205) (by norm_num)
theorem B6285653 : Blo 1861632 6285653 := bbase (se 10 (by rfl) ⟨9207, by rfl⟩ : syracuseStep 6285653 = 18415) (by norm_num)
theorem B4712813 : Blo 1861632 4712813 := bbase (se 3 (by rfl) ⟨883652, by rfl⟩ : syracuseStep 4712813 = 1767305) (by norm_num)
theorem B7072181 : Blo 1861632 7072181 := bbase (se 5 (by rfl) ⟨331508, by rfl⟩ : syracuseStep 7072181 = 663017) (by norm_num)
theorem B9431477 : Blo 1861632 9431477 := bbase (se 5 (by rfl) ⟨442100, by rfl⟩ : syracuseStep 9431477 = 884201) (by norm_num)
theorem B6048229 : Blo 1861632 6048229 := bbase (se 4 (by rfl) ⟨567021, by rfl⟩ : syracuseStep 6048229 = 1134043) (by norm_num)
theorem B14330357 : Blo 1861632 14330357 := bbase (se 5 (by rfl) ⟨671735, by rfl⟩ : syracuseStep 14330357 = 1343471) (by norm_num)
theorem B4713005 : Blo 1861632 4713005 := bbase (se 3 (by rfl) ⟨883688, by rfl⟩ : syracuseStep 4713005 = 1767377) (by norm_num)
theorem B4188725 : Blo 1861632 4188725 := bbase (se 5 (by rfl) ⟨196346, by rfl⟩ : syracuseStep 4188725 = 392693) (by norm_num)
theorem B5302837 : Blo 1861632 5302837 := bbase (se 5 (by rfl) ⟨248570, by rfl⟩ : syracuseStep 5302837 = 497141) (by norm_num)
theorem B3025493 : Blo 1861632 3025493 := bbase (se 8 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 3025493 = 35455) (by norm_num)
theorem B4188797 : Blo 1861632 4188797 := bbase (se 3 (by rfl) ⟨785399, by rfl⟩ : syracuseStep 4188797 = 1570799) (by norm_num)
theorem B2517637 : Blo 1861632 2517637 := bbase (se 4 (by rfl) ⟨236028, by rfl⟩ : syracuseStep 2517637 = 472057) (by norm_num)
theorem B2517653 : Blo 1861632 2517653 := bbase (se 6 (by rfl) ⟨59007, by rfl⟩ : syracuseStep 2517653 = 118015) (by norm_num)
theorem B15313589 : Blo 1861632 15313589 := bbase (se 5 (by rfl) ⟨717824, by rfl⟩ : syracuseStep 15313589 = 1435649) (by norm_num)
theorem B4188869 : Blo 1861632 4188869 := bbase (se 4 (by rfl) ⟨392706, by rfl⟩ : syracuseStep 4188869 = 785413) (by norm_num)
theorem B5663429 : Blo 1861632 5663429 := bbase (se 4 (by rfl) ⟨530946, by rfl⟩ : syracuseStep 5663429 = 1061893) (by norm_num)
theorem B17222357 : Blo 1861632 17222357 := bbase (se 7 (by rfl) ⟨201824, by rfl⟩ : syracuseStep 17222357 = 403649) (by norm_num)
theorem B4475645 : Blo 1861632 4475645 := bbase (se 3 (by rfl) ⟨839183, by rfl⟩ : syracuseStep 4475645 = 1678367) (by norm_num)
theorem B6286085 : Blo 1861632 6286085 := bbase (se 4 (by rfl) ⟨589320, by rfl⟩ : syracuseStep 6286085 = 1178641) (by norm_num)
theorem B4188941 : Blo 1861632 4188941 := bbase (se 3 (by rfl) ⟨785426, by rfl⟩ : syracuseStep 4188941 = 1570853) (by norm_num)
theorem B4189013 : Blo 1861632 4189013 := bbase (se 9 (by rfl) ⟨12272, by rfl⟩ : syracuseStep 4189013 = 24545) (by norm_num)
theorem B135940949 : Blo 1861632 135940949 := bbase (se 9 (by rfl) ⟨398264, by rfl⟩ : syracuseStep 135940949 = 796529) (by norm_num)
theorem B3976069 : Blo 1861632 3976069 := bbase (se 4 (by rfl) ⟨372756, by rfl⟩ : syracuseStep 3976069 = 745513) (by norm_num)
theorem B4713349 : Blo 1861632 4713349 := bbase (se 4 (by rfl) ⟨441876, by rfl⟩ : syracuseStep 4713349 = 883753) (by norm_num)
theorem B4189085 : Blo 1861632 4189085 := bbase (se 3 (by rfl) ⟨785453, by rfl⟩ : syracuseStep 4189085 = 1570907) (by norm_num)
theorem B4189157 : Blo 1861632 4189157 := bbase (se 4 (by rfl) ⟨392733, by rfl⟩ : syracuseStep 4189157 = 785467) (by norm_num)
theorem B4713461 : Blo 1861632 4713461 := bbase (se 5 (by rfl) ⟨220943, by rfl⟩ : syracuseStep 4713461 = 441887) (by norm_num)
theorem B4189229 : Blo 1861632 4189229 := bbase (se 3 (by rfl) ⟨785480, by rfl⟩ : syracuseStep 4189229 = 1570961) (by norm_num)
theorem B4475981 : Blo 1861632 4475981 := bbase (se 3 (by rfl) ⟨839246, by rfl⟩ : syracuseStep 4475981 = 1678493) (by norm_num)
theorem B2518117 : Blo 1861632 2518117 := bbase (se 4 (by rfl) ⟨236073, by rfl⟩ : syracuseStep 2518117 = 472147) (by norm_num)
theorem B4189301 : Blo 1861632 4189301 := bbase (se 5 (by rfl) ⟨196373, by rfl⟩ : syracuseStep 4189301 = 392747) (by norm_num)
theorem B10603669 : Blo 1861632 10603669 := bbase (se 6 (by rfl) ⟨248523, by rfl⟩ : syracuseStep 10603669 = 497047) (by norm_num)
theorem B4713653 : Blo 1861632 4713653 := bbase (se 5 (by rfl) ⟨220952, by rfl⟩ : syracuseStep 4713653 = 441905) (by norm_num)
theorem B6286517 : Blo 1861632 6286517 := bbase (se 5 (by rfl) ⟨294680, by rfl⟩ : syracuseStep 6286517 = 589361) (by norm_num)
theorem B4189373 : Blo 1861632 4189373 := bbase (se 3 (by rfl) ⟨785507, by rfl⟩ : syracuseStep 4189373 = 1571015) (by norm_num)
theorem B3230917 : Blo 1861632 3230917 := bbase (se 4 (by rfl) ⟨302898, by rfl⟩ : syracuseStep 3230917 = 605797) (by norm_num)
theorem B3976445 : Blo 1861632 3976445 := bbase (se 3 (by rfl) ⟨745583, by rfl⟩ : syracuseStep 3976445 = 1491167) (by norm_num)
theorem B1887485 : Blo 1861632 1887485 := bbase (se 3 (by rfl) ⟨353903, by rfl⟩ : syracuseStep 1887485 = 707807) (by norm_num)
theorem B4189445 : Blo 1861632 4189445 := bbase (se 4 (by rfl) ⟨392760, by rfl⟩ : syracuseStep 4189445 = 785521) (by norm_num)
theorem B4189517 : Blo 1861632 4189517 := bbase (se 3 (by rfl) ⟨785534, by rfl⟩ : syracuseStep 4189517 = 1571069) (by norm_num)
theorem B4189589 : Blo 1861632 4189589 := bbase (se 6 (by rfl) ⟨98193, by rfl⟩ : syracuseStep 4189589 = 196387) (by norm_num)
theorem B3829189 : Blo 1861632 3829189 := bbase (se 4 (by rfl) ⟨358986, by rfl⟩ : syracuseStep 3829189 = 717973) (by norm_num)
theorem B4304341 : Blo 1861632 4304341 := bbase (se 7 (by rfl) ⟨50441, by rfl⟩ : syracuseStep 4304341 = 100883) (by norm_num)
theorem B4189661 : Blo 1861632 4189661 := bbase (se 3 (by rfl) ⟨785561, by rfl⟩ : syracuseStep 4189661 = 1571123) (by norm_num)
theorem B4845037 : Blo 1861632 4845037 := bbase (se 3 (by rfl) ⟨908444, by rfl⟩ : syracuseStep 4845037 = 1816889) (by norm_num)
theorem B4713997 : Blo 1861632 4713997 := bbase (se 3 (by rfl) ⟨883874, by rfl⟩ : syracuseStep 4713997 = 1767749) (by norm_num)
theorem B4189733 : Blo 1861632 4189733 := bbase (se 4 (by rfl) ⟨392787, by rfl⟩ : syracuseStep 4189733 = 785575) (by norm_num)
theorem B7073365 : Blo 1861632 7073365 := bbase (se 8 (by rfl) ⟨41445, by rfl⟩ : syracuseStep 7073365 = 82891) (by norm_num)
theorem B6286949 : Blo 1861632 6286949 := bbase (se 4 (by rfl) ⟨589401, by rfl⟩ : syracuseStep 6286949 = 1178803) (by norm_num)
theorem B4189805 : Blo 1861632 4189805 := bbase (se 3 (by rfl) ⟨785588, by rfl⟩ : syracuseStep 4189805 = 1571177) (by norm_num)
theorem B4714109 : Blo 1861632 4714109 := bbase (se 3 (by rfl) ⟨883895, by rfl⟩ : syracuseStep 4714109 = 1767791) (by norm_num)
theorem B4189877 : Blo 1861632 4189877 := bbase (se 5 (by rfl) ⟨196400, by rfl⟩ : syracuseStep 4189877 = 392801) (by norm_num)
theorem B9432773 : Blo 1861632 9432773 := bbase (se 4 (by rfl) ⟨884322, by rfl⟩ : syracuseStep 9432773 = 1768645) (by norm_num)
theorem B4247245 : Blo 1861632 4247245 := bbase (se 3 (by rfl) ⟨796358, by rfl⟩ : syracuseStep 4247245 = 1592717) (by norm_num)
theorem B5967589 : Blo 1861632 5967589 := bbase (se 4 (by rfl) ⟨559461, by rfl⟩ : syracuseStep 5967589 = 1118923) (by norm_num)
theorem B6713077 : Blo 1861632 6713077 := bbase (se 5 (by rfl) ⟨314675, by rfl⟩ : syracuseStep 6713077 = 629351) (by norm_num)
theorem B4189949 : Blo 1861632 4189949 := bbase (se 3 (by rfl) ⟨785615, by rfl⟩ : syracuseStep 4189949 = 1571231) (by norm_num)
theorem B4714301 : Blo 1861632 4714301 := bbase (se 3 (by rfl) ⟨883931, by rfl⟩ : syracuseStep 4714301 = 1767863) (by norm_num)
theorem B4190021 : Blo 1861632 4190021 := bbase (se 4 (by rfl) ⟨392814, by rfl⟩ : syracuseStep 4190021 = 785629) (by norm_num)
theorem B7958357 : Blo 1861632 7958357 := bbase (se 9 (by rfl) ⟨23315, by rfl⟩ : syracuseStep 7958357 = 46631) (by norm_num)
theorem B15109973 : Blo 1861632 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B2723701 : Blo 1861632 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B7073669 : Blo 1861632 7073669 := bbase (se 4 (by rfl) ⟨663156, by rfl⟩ : syracuseStep 7073669 = 1326313) (by norm_num)
theorem B3141517 : Blo 1861632 3141517 := bbase (se 3 (by rfl) ⟨589034, by rfl⟩ : syracuseStep 3141517 = 1178069) (by norm_num)
theorem B4190093 : Blo 1861632 4190093 := bbase (se 3 (by rfl) ⟨785642, by rfl⟩ : syracuseStep 4190093 = 1571285) (by norm_num)
theorem B4190165 : Blo 1861632 4190165 := bbase (se 7 (by rfl) ⟨49103, by rfl⟩ : syracuseStep 4190165 = 98207) (by norm_num)
theorem B3141605 : Blo 1861632 3141605 := bbase (se 4 (by rfl) ⟨294525, by rfl⟩ : syracuseStep 3141605 = 589051) (by norm_num)
theorem B5967845 : Blo 1861632 5967845 := bbase (se 4 (by rfl) ⟨559485, by rfl⟩ : syracuseStep 5967845 = 1118971) (by norm_num)
theorem B3534853 : Blo 1861632 3534853 := bbase (se 4 (by rfl) ⟨331392, by rfl⟩ : syracuseStep 3534853 = 662785) (by norm_num)
theorem B5304341 : Blo 1861632 5304341 := bbase (se 6 (by rfl) ⟨124320, by rfl⟩ : syracuseStep 5304341 = 248641) (by norm_num)
theorem B6287381 : Blo 1861632 6287381 := bbase (se 6 (by rfl) ⟨147360, by rfl⟩ : syracuseStep 6287381 = 294721) (by norm_num)
theorem B4190237 : Blo 1861632 4190237 := bbase (se 3 (by rfl) ⟨785669, by rfl⟩ : syracuseStep 4190237 = 1571339) (by norm_num)
theorem B9424997 : Blo 1861632 9424997 := bbase (se 4 (by rfl) ⟨883593, by rfl⟩ : syracuseStep 9424997 = 1767187) (by norm_num)
theorem B3141733 : Blo 1861632 3141733 := bbase (se 4 (by rfl) ⟨294537, by rfl⟩ : syracuseStep 3141733 = 589075) (by norm_num)
theorem B4190309 : Blo 1861632 4190309 := bbase (se 4 (by rfl) ⟨392841, by rfl⟩ : syracuseStep 4190309 = 785683) (by norm_num)
theorem B4477037 : Blo 1861632 4477037 := bbase (se 3 (by rfl) ⟨839444, by rfl⟩ : syracuseStep 4477037 = 1678889) (by norm_num)
theorem B3534997 : Blo 1861632 3534997 := bbase (se 6 (by rfl) ⟨82851, by rfl⟩ : syracuseStep 3534997 = 165703) (by norm_num)
theorem B4714645 : Blo 1861632 4714645 := bbase (se 6 (by rfl) ⟨110499, by rfl⟩ : syracuseStep 4714645 = 220999) (by norm_num)
theorem B4190381 : Blo 1861632 4190381 := bbase (se 3 (by rfl) ⟨785696, by rfl⟩ : syracuseStep 4190381 = 1571393) (by norm_num)
theorem B3141821 : Blo 1861632 3141821 := bbase (se 3 (by rfl) ⟨589091, by rfl⟩ : syracuseStep 3141821 = 1178183) (by norm_num)
theorem B3354853 : Blo 1861632 3354853 := bbase (se 4 (by rfl) ⟨314517, by rfl⟩ : syracuseStep 3354853 = 629035) (by norm_num)
theorem B4190453 : Blo 1861632 4190453 := bbase (se 5 (by rfl) ⟨196427, by rfl⟩ : syracuseStep 4190453 = 392855) (by norm_num)
theorem B4714757 : Blo 1861632 4714757 := bbase (se 4 (by rfl) ⟨442008, by rfl⟩ : syracuseStep 4714757 = 884017) (by norm_num)
theorem B3535157 : Blo 1861632 3535157 := bbase (se 5 (by rfl) ⟨165710, by rfl⟩ : syracuseStep 3535157 = 331421) (by norm_num)
theorem B3141949 : Blo 1861632 3141949 := bbase (se 3 (by rfl) ⟨589115, by rfl⟩ : syracuseStep 3141949 = 1178231) (by norm_num)
theorem B4190525 : Blo 1861632 4190525 := bbase (se 3 (by rfl) ⟨785723, by rfl⟩ : syracuseStep 4190525 = 1571447) (by norm_num)
theorem B1888637 : Blo 1861632 1888637 := bbase (se 3 (by rfl) ⟨354119, by rfl⟩ : syracuseStep 1888637 = 708239) (by norm_num)
theorem B4190597 : Blo 1861632 4190597 := bbase (se 4 (by rfl) ⟨392868, by rfl⟩ : syracuseStep 4190597 = 785737) (by norm_num)
theorem B3142037 : Blo 1861632 3142037 := bbase (se 6 (by rfl) ⟨73641, by rfl⟩ : syracuseStep 3142037 = 147283) (by norm_num)
theorem B3535301 : Blo 1861632 3535301 := bbase (se 4 (by rfl) ⟨331434, by rfl⟩ : syracuseStep 3535301 = 662869) (by norm_num)
theorem B4714949 : Blo 1861632 4714949 := bbase (se 4 (by rfl) ⟨442026, by rfl⟩ : syracuseStep 4714949 = 884053) (by norm_num)
theorem B6287813 : Blo 1861632 6287813 := bbase (se 4 (by rfl) ⟨589482, by rfl⟩ : syracuseStep 6287813 = 1178965) (by norm_num)
theorem B4190669 : Blo 1861632 4190669 := bbase (se 3 (by rfl) ⟨785750, by rfl⟩ : syracuseStep 4190669 = 1571501) (by norm_num)
theorem B3355141 : Blo 1861632 3355141 := bbase (se 4 (by rfl) ⟨314544, by rfl⟩ : syracuseStep 3355141 = 629089) (by norm_num)
theorem B3142165 : Blo 1861632 3142165 := bbase (se 6 (by rfl) ⟨73644, by rfl⟩ : syracuseStep 3142165 = 147289) (by norm_num)
theorem B11932181 : Blo 1861632 11932181 := bbase (se 6 (by rfl) ⟨279660, by rfl⟩ : syracuseStep 11932181 = 559321) (by norm_num)
theorem B4190741 : Blo 1861632 4190741 := bbase (se 6 (by rfl) ⟨98220, by rfl⟩ : syracuseStep 4190741 = 196441) (by norm_num)
theorem B17904149 : Blo 1861632 17904149 := bbase (se 6 (by rfl) ⟨419628, by rfl⟩ : syracuseStep 17904149 = 839257) (by norm_num)
theorem B4190813 : Blo 1861632 4190813 := bbase (se 3 (by rfl) ⟨785777, by rfl⟩ : syracuseStep 4190813 = 1571555) (by norm_num)
theorem B3142253 : Blo 1861632 3142253 := bbase (se 3 (by rfl) ⟨589172, by rfl⟩ : syracuseStep 3142253 = 1178345) (by norm_num)
theorem B35811989 : Blo 1861632 35811989 := bbase (se 6 (by rfl) ⟨839343, by rfl⟩ : syracuseStep 35811989 = 1678687) (by norm_num)
theorem B4190885 : Blo 1861632 4190885 := bbase (se 4 (by rfl) ⟨392895, by rfl⟩ : syracuseStep 4190885 = 785791) (by norm_num)
theorem B4248229 : Blo 1861632 4248229 := bbase (se 4 (by rfl) ⟨398271, by rfl⟩ : syracuseStep 4248229 = 796543) (by norm_num)
theorem B3535589 : Blo 1861632 3535589 := bbase (se 4 (by rfl) ⟨331461, by rfl⟩ : syracuseStep 3535589 = 662923) (by norm_num)
theorem B3142381 : Blo 1861632 3142381 := bbase (se 3 (by rfl) ⟨589196, by rfl⟩ : syracuseStep 3142381 = 1178393) (by norm_num)
theorem B4190957 : Blo 1861632 4190957 := bbase (se 3 (by rfl) ⟨785804, by rfl⟩ : syracuseStep 4190957 = 1571609) (by norm_num)
theorem B4715293 : Blo 1861632 4715293 := bbase (se 3 (by rfl) ⟨884117, by rfl⟩ : syracuseStep 4715293 = 1768235) (by norm_num)
theorem B4191029 : Blo 1861632 4191029 := bbase (se 5 (by rfl) ⟨196454, by rfl⟩ : syracuseStep 4191029 = 392909) (by norm_num)
theorem B3142469 : Blo 1861632 3142469 := bbase (se 4 (by rfl) ⟨294606, by rfl⟩ : syracuseStep 3142469 = 589213) (by norm_num)
theorem B67982165 : Blo 1861632 67982165 := bbase (se 9 (by rfl) ⟨199166, by rfl⟩ : syracuseStep 67982165 = 398333) (by norm_num)
theorem B5665621 : Blo 1861632 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B3978085 : Blo 1861632 3978085 := bbase (se 4 (by rfl) ⟨372945, by rfl⟩ : syracuseStep 3978085 = 745891) (by norm_num)
theorem B6288245 : Blo 1861632 6288245 := bbase (se 5 (by rfl) ⟨294761, by rfl⟩ : syracuseStep 6288245 = 589523) (by norm_num)
theorem B3535741 : Blo 1861632 3535741 := bbase (se 3 (by rfl) ⟨662951, by rfl⟩ : syracuseStep 3535741 = 1325903) (by norm_num)
theorem B4191101 : Blo 1861632 4191101 := bbase (se 3 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 4191101 = 1571663) (by norm_num)
theorem B4715405 : Blo 1861632 4715405 := bbase (se 3 (by rfl) ⟨884138, by rfl⟩ : syracuseStep 4715405 = 1768277) (by norm_num)
theorem B2651077 : Blo 1861632 2651077 := bbase (se 4 (by rfl) ⟨248538, by rfl⟩ : syracuseStep 2651077 = 497077) (by norm_num)
theorem B3142597 : Blo 1861632 3142597 := bbase (se 4 (by rfl) ⟨294618, by rfl⟩ : syracuseStep 3142597 = 589237) (by norm_num)
theorem B4191173 : Blo 1861632 4191173 := bbase (se 4 (by rfl) ⟨392922, by rfl⟩ : syracuseStep 4191173 = 785845) (by norm_num)
theorem B9434069 : Blo 1861632 9434069 := bbase (se 7 (by rfl) ⟨110555, by rfl⟩ : syracuseStep 9434069 = 221111) (by norm_num)
theorem B2356229 : Blo 1861632 2356229 := bbase (se 4 (by rfl) ⟨220896, by rfl⟩ : syracuseStep 2356229 = 441793) (by norm_num)
theorem B4191245 : Blo 1861632 4191245 := bbase (se 3 (by rfl) ⟨785858, by rfl⟩ : syracuseStep 4191245 = 1571717) (by norm_num)
theorem B3142685 : Blo 1861632 3142685 := bbase (se 3 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 3142685 = 1178507) (by norm_num)
theorem B2356285 : Blo 1861632 2356285 := bbase (se 3 (by rfl) ⟨441803, by rfl⟩ : syracuseStep 2356285 = 883607) (by norm_num)
theorem B6370373 : Blo 1861632 6370373 := bbase (se 4 (by rfl) ⟨597222, by rfl⟩ : syracuseStep 6370373 = 1194445) (by norm_num)
theorem B4715597 : Blo 1861632 4715597 := bbase (se 3 (by rfl) ⟨884174, by rfl⟩ : syracuseStep 4715597 = 1768349) (by norm_num)
theorem B10605653 : Blo 1861632 10605653 := bbase (se 8 (by rfl) ⟨62142, by rfl⟩ : syracuseStep 10605653 = 124285) (by norm_num)
theorem B4191317 : Blo 1861632 4191317 := bbase (se 8 (by rfl) ⟨24558, by rfl⟩ : syracuseStep 4191317 = 49117) (by norm_num)
theorem B2356381 : Blo 1861632 2356381 := bbase (se 3 (by rfl) ⟨441821, by rfl⟩ : syracuseStep 2356381 = 883643) (by norm_num)
theorem B3142813 : Blo 1861632 3142813 := bbase (se 3 (by rfl) ⟨589277, by rfl⟩ : syracuseStep 3142813 = 1178555) (by norm_num)
theorem B4191389 : Blo 1861632 4191389 := bbase (se 3 (by rfl) ⟨785885, by rfl⟩ : syracuseStep 4191389 = 1571771) (by norm_num)
theorem B3536045 : Blo 1861632 3536045 := bbase (se 3 (by rfl) ⟨663008, by rfl⟩ : syracuseStep 3536045 = 1326017) (by norm_num)
theorem B8950981 : Blo 1861632 8950981 := bbase (se 4 (by rfl) ⟨839154, by rfl⟩ : syracuseStep 8950981 = 1678309) (by norm_num)
theorem B4191461 : Blo 1861632 4191461 := bbase (se 4 (by rfl) ⟨392949, by rfl⟩ : syracuseStep 4191461 = 785899) (by norm_num)
theorem B3142901 : Blo 1861632 3142901 := bbase (se 5 (by rfl) ⟨147323, by rfl⟩ : syracuseStep 3142901 = 294647) (by norm_num)
theorem B2094349 : Blo 1861632 2094349 := bbase (se 3 (by rfl) ⟨392690, by rfl⟩ : syracuseStep 2094349 = 785381) (by norm_num)
theorem B3355933 : Blo 1861632 3355933 := bbase (se 3 (by rfl) ⟨629237, by rfl⟩ : syracuseStep 3355933 = 1258475) (by norm_num)
theorem B6288677 : Blo 1861632 6288677 := bbase (se 4 (by rfl) ⟨589563, by rfl⟩ : syracuseStep 6288677 = 1179127) (by norm_num)
theorem B4191533 : Blo 1861632 4191533 := bbase (se 3 (by rfl) ⟨785912, by rfl⟩ : syracuseStep 4191533 = 1571825) (by norm_num)
theorem B2094385 : Blo 1861632 2094385 := bbase (se 2 (by rfl) ⟨785394, by rfl⟩ : syracuseStep 2094385 = 1570789) (by norm_num)
theorem B7165253 : Blo 1861632 7165253 := bbase (se 4 (by rfl) ⟨671742, by rfl⟩ : syracuseStep 7165253 = 1343485) (by norm_num)
theorem B2356553 : Blo 1861632 2356553 := bbase (se 2 (by rfl) ⟨883707, by rfl⟩ : syracuseStep 2356553 = 1767415) (by norm_num)
theorem B2094421 : Blo 1861632 2094421 := bbase (se 13 (by rfl) ⟨383, by rfl⟩ : syracuseStep 2094421 = 767) (by norm_num)
theorem B9426293 : Blo 1861632 9426293 := bbase (se 5 (by rfl) ⟨441857, by rfl⟩ : syracuseStep 9426293 = 883715) (by norm_num)
theorem B3143029 : Blo 1861632 3143029 := bbase (se 5 (by rfl) ⟨147329, by rfl⟩ : syracuseStep 3143029 = 294659) (by norm_num)
theorem B4191605 : Blo 1861632 4191605 := bbase (se 5 (by rfl) ⟨196481, by rfl⟩ : syracuseStep 4191605 = 392963) (by norm_num)
theorem B2094457 : Blo 1861632 2094457 := bbase (se 2 (by rfl) ⟨785421, by rfl⟩ : syracuseStep 2094457 = 1570843) (by norm_num)
theorem B2356609 : Blo 1861632 2356609 := bbase (se 2 (by rfl) ⟨883728, by rfl⟩ : syracuseStep 2356609 = 1767457) (by norm_num)
theorem B2094493 : Blo 1861632 2094493 := bbase (se 3 (by rfl) ⟨392717, by rfl⟩ : syracuseStep 2094493 = 785435) (by norm_num)
theorem B2487709 : Blo 1861632 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B4715941 : Blo 1861632 4715941 := bbase (se 4 (by rfl) ⟨442119, by rfl⟩ : syracuseStep 4715941 = 884239) (by norm_num)
theorem B3356077 : Blo 1861632 3356077 := bbase (se 3 (by rfl) ⟨629264, by rfl⟩ : syracuseStep 3356077 = 1258529) (by norm_num)
theorem B4191677 : Blo 1861632 4191677 := bbase (se 3 (by rfl) ⟨785939, by rfl⟩ : syracuseStep 4191677 = 1571879) (by norm_num)
theorem B2094529 : Blo 1861632 2094529 := bbase (se 2 (by rfl) ⟨785448, by rfl⟩ : syracuseStep 2094529 = 1570897) (by norm_num)
theorem B3143117 : Blo 1861632 3143117 := bbase (se 3 (by rfl) ⟨589334, by rfl⟩ : syracuseStep 3143117 = 1178669) (by norm_num)
theorem B45307349 : Blo 1861632 45307349 := bbase (se 7 (by rfl) ⟨530945, by rfl⟩ : syracuseStep 45307349 = 1061891) (by norm_num)
theorem B2356705 : Blo 1861632 2356705 := bbase (se 2 (by rfl) ⟨883764, by rfl⟩ : syracuseStep 2356705 = 1767529) (by norm_num)
theorem B2094565 : Blo 1861632 2094565 := bbase (se 4 (by rfl) ⟨196365, by rfl⟩ : syracuseStep 2094565 = 392731) (by norm_num)
theorem B15906293 : Blo 1861632 15906293 := bbase (se 5 (by rfl) ⟨745607, by rfl⟩ : syracuseStep 15906293 = 1491215) (by norm_num)
theorem B4191749 : Blo 1861632 4191749 := bbase (se 4 (by rfl) ⟨392976, by rfl⟩ : syracuseStep 4191749 = 785953) (by norm_num)
theorem B2094601 : Blo 1861632 2094601 := bbase (se 2 (by rfl) ⟨785475, by rfl⟩ : syracuseStep 2094601 = 1570951) (by norm_num)
theorem B4716053 : Blo 1861632 4716053 := bbase (se 6 (by rfl) ⟨110532, by rfl⟩ : syracuseStep 4716053 = 221065) (by norm_num)
theorem B2094637 : Blo 1861632 2094637 := bbase (se 3 (by rfl) ⟨392744, by rfl⟩ : syracuseStep 2094637 = 785489) (by norm_num)
theorem B5305925 : Blo 1861632 5305925 := bbase (se 4 (by rfl) ⟨497430, by rfl⟩ : syracuseStep 5305925 = 994861) (by norm_num)
theorem B7960133 : Blo 1861632 7960133 := bbase (se 4 (by rfl) ⟨746262, by rfl⟩ : syracuseStep 7960133 = 1492525) (by norm_num)
theorem B3356237 : Blo 1861632 3356237 := bbase (se 3 (by rfl) ⟨629294, by rfl⟩ : syracuseStep 3356237 = 1258589) (by norm_num)
theorem B3143245 : Blo 1861632 3143245 := bbase (se 3 (by rfl) ⟨589358, by rfl⟩ : syracuseStep 3143245 = 1178717) (by norm_num)
theorem B4191821 : Blo 1861632 4191821 := bbase (se 3 (by rfl) ⟨785966, by rfl⟩ : syracuseStep 4191821 = 1571933) (by norm_num)
theorem B2094673 : Blo 1861632 2094673 := bbase (se 2 (by rfl) ⟨785502, by rfl⟩ : syracuseStep 2094673 = 1571005) (by norm_num)
theorem B2094709 : Blo 1861632 2094709 := bbase (se 5 (by rfl) ⟨98189, by rfl⟩ : syracuseStep 2094709 = 196379) (by norm_num)
theorem B2356877 : Blo 1861632 2356877 := bbase (se 3 (by rfl) ⟨441914, by rfl⟩ : syracuseStep 2356877 = 883829) (by norm_num)
theorem B3356309 : Blo 1861632 3356309 := bbase (se 6 (by rfl) ⟨78663, by rfl⟩ : syracuseStep 3356309 = 157327) (by norm_num)
theorem B4191893 : Blo 1861632 4191893 := bbase (se 6 (by rfl) ⟨98247, by rfl⟩ : syracuseStep 4191893 = 196495) (by norm_num)
theorem B2094745 : Blo 1861632 2094745 := bbase (se 2 (by rfl) ⟨785529, by rfl⟩ : syracuseStep 2094745 = 1571059) (by norm_num)
theorem B3143333 : Blo 1861632 3143333 := bbase (se 4 (by rfl) ⟨294687, by rfl⟩ : syracuseStep 3143333 = 589375) (by norm_num)
theorem B7952053 : Blo 1861632 7952053 := bbase (se 5 (by rfl) ⟨372752, by rfl⟩ : syracuseStep 7952053 = 745505) (by norm_num)
theorem B2094781 : Blo 1861632 2094781 := bbase (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) (by norm_num)
theorem B7952069 : Blo 1861632 7952069 := bbase (se 4 (by rfl) ⟨745506, by rfl⟩ : syracuseStep 7952069 = 1491013) (by norm_num)
theorem B2356933 : Blo 1861632 2356933 := bbase (se 4 (by rfl) ⟨220962, by rfl⟩ : syracuseStep 2356933 = 441925) (by norm_num)
theorem B4716245 : Blo 1861632 4716245 := bbase (se 7 (by rfl) ⟨55268, by rfl⟩ : syracuseStep 4716245 = 110537) (by norm_num)
theorem B6289109 : Blo 1861632 6289109 := bbase (se 7 (by rfl) ⟨73700, by rfl⟩ : syracuseStep 6289109 = 147401) (by norm_num)
theorem B2651869 : Blo 1861632 2651869 := bbase (se 3 (by rfl) ⟨497225, by rfl⟩ : syracuseStep 2651869 = 994451) (by norm_num)
theorem B3978973 : Blo 1861632 3978973 := bbase (se 3 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 3978973 = 1492115) (by norm_num)
theorem B4191965 : Blo 1861632 4191965 := bbase (se 3 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 4191965 = 1571987) (by norm_num)
theorem B2094817 : Blo 1861632 2094817 := bbase (se 2 (by rfl) ⟨785556, by rfl⟩ : syracuseStep 2094817 = 1571113) (by norm_num)
theorem B2094853 : Blo 1861632 2094853 := bbase (se 4 (by rfl) ⟨196392, by rfl⟩ : syracuseStep 2094853 = 392785) (by norm_num)
theorem B2357029 : Blo 1861632 2357029 := bbase (se 4 (by rfl) ⟨220971, by rfl⟩ : syracuseStep 2357029 = 441943) (by norm_num)
theorem B3143461 : Blo 1861632 3143461 := bbase (se 4 (by rfl) ⟨294699, by rfl⟩ : syracuseStep 3143461 = 589399) (by norm_num)
theorem B4192037 : Blo 1861632 4192037 := bbase (se 4 (by rfl) ⟨393003, by rfl⟩ : syracuseStep 4192037 = 786007) (by norm_num)
theorem B1988393 : Blo 1861632 1988393 := bbase (se 2 (by rfl) ⟨745647, by rfl⟩ : syracuseStep 1988393 = 1491295) (by norm_num)
theorem B2094889 : Blo 1861632 2094889 := bbase (se 2 (by rfl) ⟨785583, by rfl⟩ : syracuseStep 2094889 = 1571167) (by norm_num)
theorem B2094925 : Blo 1861632 2094925 := bbase (se 3 (by rfl) ⟨392798, by rfl⟩ : syracuseStep 2094925 = 785597) (by norm_num)
theorem B1914725 : Blo 1861632 1914725 := bbase (se 4 (by rfl) ⟨179505, by rfl⟩ : syracuseStep 1914725 = 359011) (by norm_num)
theorem B4192109 : Blo 1861632 4192109 := bbase (se 3 (by rfl) ⟨786020, by rfl⟩ : syracuseStep 4192109 = 1572041) (by norm_num)
theorem B2094961 : Blo 1861632 2094961 := bbase (se 2 (by rfl) ⟨785610, by rfl⟩ : syracuseStep 2094961 = 1571221) (by norm_num)
theorem B3143549 : Blo 1861632 3143549 := bbase (se 3 (by rfl) ⟨589415, by rfl⟩ : syracuseStep 3143549 = 1178831) (by norm_num)
theorem B2094997 : Blo 1861632 2094997 := bbase (se 6 (by rfl) ⟨49101, by rfl⟩ : syracuseStep 2094997 = 98203) (by norm_num)
theorem B3536797 : Blo 1861632 3536797 := bbase (se 3 (by rfl) ⟨663149, by rfl⟩ : syracuseStep 3536797 = 1326299) (by norm_num)
theorem B4192181 : Blo 1861632 4192181 := bbase (se 5 (by rfl) ⟨196508, by rfl⟩ : syracuseStep 4192181 = 393017) (by norm_num)
theorem B2095033 : Blo 1861632 2095033 := bbase (se 2 (by rfl) ⟨785637, by rfl⟩ : syracuseStep 2095033 = 1571275) (by norm_num)
theorem B7075781 : Blo 1861632 7075781 := bbase (se 4 (by rfl) ⟨663354, by rfl⟩ : syracuseStep 7075781 = 1326709) (by norm_num)
theorem B2357201 : Blo 1861632 2357201 := bbase (se 2 (by rfl) ⟨883950, by rfl⟩ : syracuseStep 2357201 = 1767901) (by norm_num)
theorem B2095069 : Blo 1861632 2095069 := bbase (se 3 (by rfl) ⟨392825, by rfl⟩ : syracuseStep 2095069 = 785651) (by norm_num)
theorem B3143677 : Blo 1861632 3143677 := bbase (se 3 (by rfl) ⟨589439, by rfl⟩ : syracuseStep 3143677 = 1178879) (by norm_num)
theorem B4192253 : Blo 1861632 4192253 := bbase (se 3 (by rfl) ⟨786047, by rfl⟩ : syracuseStep 4192253 = 1572095) (by norm_num)
theorem B2095105 : Blo 1861632 2095105 := bbase (se 2 (by rfl) ⟨785664, by rfl⟩ : syracuseStep 2095105 = 1571329) (by norm_num)
theorem B2357257 : Blo 1861632 2357257 := bbase (se 2 (by rfl) ⟨883971, by rfl⟩ : syracuseStep 2357257 = 1767943) (by norm_num)
theorem B3774485 : Blo 1861632 3774485 := bbase (se 6 (by rfl) ⟨88464, by rfl⟩ : syracuseStep 3774485 = 176929) (by norm_num)
theorem B10065941 : Blo 1861632 10065941 := bbase (se 6 (by rfl) ⟨235920, by rfl⟩ : syracuseStep 10065941 = 471841) (by norm_num)
theorem B1988641 : Blo 1861632 1988641 := bbase (se 2 (by rfl) ⟨745740, by rfl⟩ : syracuseStep 1988641 = 1491481) (by norm_num)
theorem B2095141 : Blo 1861632 2095141 := bbase (se 4 (by rfl) ⟨196419, by rfl⟩ : syracuseStep 2095141 = 392839) (by norm_num)
theorem B2652205 : Blo 1861632 2652205 := bbase (se 3 (by rfl) ⟨497288, by rfl⟩ : syracuseStep 2652205 = 994577) (by norm_num)
theorem B3536941 : Blo 1861632 3536941 := bbase (se 3 (by rfl) ⟨663176, by rfl⟩ : syracuseStep 3536941 = 1326353) (by norm_num)
theorem B4716589 : Blo 1861632 4716589 := bbase (se 3 (by rfl) ⟨884360, by rfl⟩ : syracuseStep 4716589 = 1768721) (by norm_num)
theorem B4192325 : Blo 1861632 4192325 := bbase (se 4 (by rfl) ⟨393030, by rfl⟩ : syracuseStep 4192325 = 786061) (by norm_num)
theorem B2095177 : Blo 1861632 2095177 := bbase (se 2 (by rfl) ⟨785691, by rfl⟩ : syracuseStep 2095177 = 1571383) (by norm_num)
theorem B3143765 : Blo 1861632 3143765 := bbase (se 8 (by rfl) ⟨18420, by rfl⟩ : syracuseStep 3143765 = 36841) (by norm_num)
theorem B2357353 : Blo 1861632 2357353 := bbase (se 2 (by rfl) ⟨884007, by rfl⟩ : syracuseStep 2357353 = 1768015) (by norm_num)
theorem B2095213 : Blo 1861632 2095213 := bbase (se 3 (by rfl) ⟨392852, by rfl⟩ : syracuseStep 2095213 = 785705) (by norm_num)
theorem B6289541 : Blo 1861632 6289541 := bbase (se 4 (by rfl) ⟨589644, by rfl⟩ : syracuseStep 6289541 = 1179289) (by norm_num)
theorem B4192397 : Blo 1861632 4192397 := bbase (se 3 (by rfl) ⟨786074, by rfl⟩ : syracuseStep 4192397 = 1572149) (by norm_num)
theorem B2095249 : Blo 1861632 2095249 := bbase (se 2 (by rfl) ⟨785718, by rfl⟩ : syracuseStep 2095249 = 1571437) (by norm_num)
theorem B4716701 : Blo 1861632 4716701 := bbase (se 3 (by rfl) ⟨884381, by rfl⟩ : syracuseStep 4716701 = 1768763) (by norm_num)
theorem B2095285 : Blo 1861632 2095285 := bbase (se 5 (by rfl) ⟨98216, by rfl⟩ : syracuseStep 2095285 = 196433) (by norm_num)
theorem B3537101 : Blo 1861632 3537101 := bbase (se 3 (by rfl) ⟨663206, by rfl⟩ : syracuseStep 3537101 = 1326413) (by norm_num)
theorem B3979469 : Blo 1861632 3979469 := bbase (se 3 (by rfl) ⟨746150, by rfl⟩ : syracuseStep 3979469 = 1492301) (by norm_num)
theorem B3143893 : Blo 1861632 3143893 := bbase (se 7 (by rfl) ⟨36842, by rfl⟩ : syracuseStep 3143893 = 73685) (by norm_num)
theorem B4192469 : Blo 1861632 4192469 := bbase (se 7 (by rfl) ⟨49130, by rfl⟩ : syracuseStep 4192469 = 98261) (by norm_num)
theorem B2095321 : Blo 1861632 2095321 := bbase (se 2 (by rfl) ⟨785745, by rfl⟩ : syracuseStep 2095321 = 1571491) (by norm_num)
theorem B5306597 : Blo 1861632 5306597 := bbase (se 4 (by rfl) ⟨497493, by rfl⟩ : syracuseStep 5306597 = 994987) (by norm_num)
theorem B13424885 : Blo 1861632 13424885 := bbase (se 5 (by rfl) ⟨629291, by rfl⟩ : syracuseStep 13424885 = 1258583) (by norm_num)
theorem B2095357 : Blo 1861632 2095357 := bbase (se 3 (by rfl) ⟨392879, by rfl⟩ : syracuseStep 2095357 = 785759) (by norm_num)
theorem B2652421 : Blo 1861632 2652421 := bbase (se 4 (by rfl) ⟨248664, by rfl⟩ : syracuseStep 2652421 = 497329) (by norm_num)
theorem B2357525 : Blo 1861632 2357525 := bbase (se 6 (by rfl) ⟨55254, by rfl⟩ : syracuseStep 2357525 = 110509) (by norm_num)
theorem B4192541 : Blo 1861632 4192541 := bbase (se 3 (by rfl) ⟨786101, by rfl⟩ : syracuseStep 4192541 = 1572203) (by norm_num)
theorem B2095393 : Blo 1861632 2095393 := bbase (se 2 (by rfl) ⟨785772, by rfl⟩ : syracuseStep 2095393 = 1571545) (by norm_num)
theorem B3143981 : Blo 1861632 3143981 := bbase (se 3 (by rfl) ⟨589496, by rfl⟩ : syracuseStep 3143981 = 1178993) (by norm_num)
theorem B2095429 : Blo 1861632 2095429 := bbase (se 4 (by rfl) ⟨196446, by rfl⟩ : syracuseStep 2095429 = 392893) (by norm_num)
theorem B2357581 : Blo 1861632 2357581 := bbase (se 3 (by rfl) ⟨442046, by rfl⟩ : syracuseStep 2357581 = 884093) (by norm_num)
theorem B3537245 : Blo 1861632 3537245 := bbase (se 3 (by rfl) ⟨663233, by rfl⟩ : syracuseStep 3537245 = 1326467) (by norm_num)
theorem B4716893 : Blo 1861632 4716893 := bbase (se 3 (by rfl) ⟨884417, by rfl⟩ : syracuseStep 4716893 = 1768835) (by norm_num)
theorem B4192613 : Blo 1861632 4192613 := bbase (se 4 (by rfl) ⟨393057, by rfl⟩ : syracuseStep 4192613 = 786115) (by norm_num)
theorem B2095465 : Blo 1861632 2095465 := bbase (se 2 (by rfl) ⟨785799, by rfl⟩ : syracuseStep 2095465 = 1571599) (by norm_num)
theorem B2095501 : Blo 1861632 2095501 := bbase (se 3 (by rfl) ⟨392906, by rfl⟩ : syracuseStep 2095501 = 785813) (by norm_num)
theorem B2357677 : Blo 1861632 2357677 := bbase (se 3 (by rfl) ⟨442064, by rfl⟩ : syracuseStep 2357677 = 884129) (by norm_num)
theorem B3144109 : Blo 1861632 3144109 := bbase (se 3 (by rfl) ⟨589520, by rfl⟩ : syracuseStep 3144109 = 1179041) (by norm_num)
theorem B4192685 : Blo 1861632 4192685 := bbase (se 3 (by rfl) ⟨786128, by rfl⟩ : syracuseStep 4192685 = 1572257) (by norm_num)
theorem B2095537 : Blo 1861632 2095537 := bbase (se 2 (by rfl) ⟨785826, by rfl⟩ : syracuseStep 2095537 = 1571653) (by norm_num)
theorem B1989073 : Blo 1861632 1989073 := bbase (se 2 (by rfl) ⟨745902, by rfl⟩ : syracuseStep 1989073 = 1491805) (by norm_num)
theorem B2095573 : Blo 1861632 2095573 := bbase (se 7 (by rfl) ⟨24557, by rfl⟩ : syracuseStep 2095573 = 49115) (by norm_num)
theorem B4192757 : Blo 1861632 4192757 := bbase (se 5 (by rfl) ⟨196535, by rfl⟩ : syracuseStep 4192757 = 393071) (by norm_num)
theorem B2095609 : Blo 1861632 2095609 := bbase (se 2 (by rfl) ⟨785853, by rfl⟩ : syracuseStep 2095609 = 1571707) (by norm_num)
theorem B3144197 : Blo 1861632 3144197 := bbase (se 4 (by rfl) ⟨294768, by rfl⟩ : syracuseStep 3144197 = 589537) (by norm_num)
theorem B13425173 : Blo 1861632 13425173 := bbase (se 6 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 13425173 = 629305) (by norm_num)
theorem B1989145 : Blo 1861632 1989145 := bbase (se 2 (by rfl) ⟨745929, by rfl⟩ : syracuseStep 1989145 = 1491859) (by norm_num)
theorem B2095645 : Blo 1861632 2095645 := bbase (se 3 (by rfl) ⟨392933, by rfl⟩ : syracuseStep 2095645 = 785867) (by norm_num)
theorem B4192829 : Blo 1861632 4192829 := bbase (se 3 (by rfl) ⟨786155, by rfl⟩ : syracuseStep 4192829 = 1572311) (by norm_num)
theorem B2095681 : Blo 1861632 2095681 := bbase (se 2 (by rfl) ⟨785880, by rfl⟩ : syracuseStep 2095681 = 1571761) (by norm_num)
theorem B2390609 : Blo 1861632 2390609 := bbase (se 2 (by rfl) ⟨896478, by rfl⟩ : syracuseStep 2390609 = 1792957) (by norm_num)
theorem B2357849 : Blo 1861632 2357849 := bbase (se 2 (by rfl) ⟨884193, by rfl⟩ : syracuseStep 2357849 = 1768387) (by norm_num)
theorem B2095717 : Blo 1861632 2095717 := bbase (se 4 (by rfl) ⟨196473, by rfl⟩ : syracuseStep 2095717 = 392947) (by norm_num)
theorem B2652797 : Blo 1861632 2652797 := bbase (se 3 (by rfl) ⟨497399, by rfl⟩ : syracuseStep 2652797 = 994799) (by norm_num)
theorem B3537533 : Blo 1861632 3537533 := bbase (se 3 (by rfl) ⟨663287, by rfl⟩ : syracuseStep 3537533 = 1326575) (by norm_num)
theorem B9427589 : Blo 1861632 9427589 := bbase (se 4 (by rfl) ⟨883836, by rfl⟩ : syracuseStep 9427589 = 1767673) (by norm_num)
theorem B3357317 : Blo 1861632 3357317 := bbase (se 4 (by rfl) ⟨314748, by rfl⟩ : syracuseStep 3357317 = 629497) (by norm_num)
theorem B3144325 : Blo 1861632 3144325 := bbase (se 4 (by rfl) ⟨294780, by rfl⟩ : syracuseStep 3144325 = 589561) (by norm_num)
theorem B4192901 : Blo 1861632 4192901 := bbase (se 4 (by rfl) ⟨393084, by rfl⟩ : syracuseStep 4192901 = 786169) (by norm_num)
theorem B2095753 : Blo 1861632 2095753 := bbase (se 2 (by rfl) ⟨785907, by rfl⟩ : syracuseStep 2095753 = 1571815) (by norm_num)
theorem B2357905 : Blo 1861632 2357905 := bbase (se 2 (by rfl) ⟨884214, by rfl⟩ : syracuseStep 2357905 = 1768429) (by norm_num)
theorem B2095789 : Blo 1861632 2095789 := bbase (se 3 (by rfl) ⟨392960, by rfl⟩ : syracuseStep 2095789 = 785921) (by norm_num)
theorem B4717237 : Blo 1861632 4717237 := bbase (se 5 (by rfl) ⟨221120, by rfl⟩ : syracuseStep 4717237 = 442241) (by norm_num)
theorem B4192973 : Blo 1861632 4192973 := bbase (se 3 (by rfl) ⟨786182, by rfl⟩ : syracuseStep 4192973 = 1572365) (by norm_num)
theorem B2095825 : Blo 1861632 2095825 := bbase (se 2 (by rfl) ⟨785934, by rfl⟩ : syracuseStep 2095825 = 1571869) (by norm_num)
theorem B3144413 : Blo 1861632 3144413 := bbase (se 3 (by rfl) ⟨589577, by rfl⟩ : syracuseStep 3144413 = 1179155) (by norm_num)
theorem B2358001 : Blo 1861632 2358001 := bbase (se 2 (by rfl) ⟨884250, by rfl⟩ : syracuseStep 2358001 = 1768501) (by norm_num)
theorem B2095861 : Blo 1861632 2095861 := bbase (se 5 (by rfl) ⟨98243, by rfl⟩ : syracuseStep 2095861 = 196487) (by norm_num)
theorem B3357461 : Blo 1861632 3357461 := bbase (se 6 (by rfl) ⟨78690, by rfl⟩ : syracuseStep 3357461 = 157381) (by norm_num)
theorem B3537685 : Blo 1861632 3537685 := bbase (se 6 (by rfl) ⟨82914, by rfl⟩ : syracuseStep 3537685 = 165829) (by norm_num)
theorem B4193045 : Blo 1861632 4193045 := bbase (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) (by norm_num)
theorem B2095897 : Blo 1861632 2095897 := bbase (se 2 (by rfl) ⟨785961, by rfl⟩ : syracuseStep 2095897 = 1571923) (by norm_num)
theorem B2095933 : Blo 1861632 2095933 := bbase (se 3 (by rfl) ⟨392987, by rfl⟩ : syracuseStep 2095933 = 785975) (by norm_num)
theorem B3144541 : Blo 1861632 3144541 := bbase (se 3 (by rfl) ⟨589601, by rfl⟩ : syracuseStep 3144541 = 1179203) (by norm_num)
theorem B4193117 : Blo 1861632 4193117 := bbase (se 3 (by rfl) ⟨786209, by rfl⟩ : syracuseStep 4193117 = 1572419) (by norm_num)
theorem B2095969 : Blo 1861632 2095969 := bbase (se 2 (by rfl) ⟨785988, by rfl⟩ : syracuseStep 2095969 = 1571977) (by norm_num)
theorem B3357541 : Blo 1861632 3357541 := bbase (se 4 (by rfl) ⟨314769, by rfl⟩ : syracuseStep 3357541 = 629539) (by norm_num)
theorem B2096005 : Blo 1861632 2096005 := bbase (se 4 (by rfl) ⟨196500, by rfl⟩ : syracuseStep 2096005 = 393001) (by norm_num)
theorem B1989517 : Blo 1861632 1989517 := bbase (se 3 (by rfl) ⟨373034, by rfl⟩ : syracuseStep 1989517 = 746069) (by norm_num)
theorem B2358173 : Blo 1861632 2358173 := bbase (se 3 (by rfl) ⟨442157, by rfl⟩ : syracuseStep 2358173 = 884315) (by norm_num)
theorem B2096041 : Blo 1861632 2096041 := bbase (se 2 (by rfl) ⟨786015, by rfl⟩ : syracuseStep 2096041 = 1572031) (by norm_num)
theorem B3144629 : Blo 1861632 3144629 := bbase (se 5 (by rfl) ⟨147404, by rfl⟩ : syracuseStep 3144629 = 294809) (by norm_num)
theorem B2096077 : Blo 1861632 2096077 := bbase (se 3 (by rfl) ⟨393014, by rfl⟩ : syracuseStep 2096077 = 786029) (by norm_num)
theorem B2358229 : Blo 1861632 2358229 := bbase (se 7 (by rfl) ⟨27635, by rfl⟩ : syracuseStep 2358229 = 55271) (by norm_num)
theorem B2096113 : Blo 1861632 2096113 := bbase (se 2 (by rfl) ⟨786042, by rfl⟩ : syracuseStep 2096113 = 1572085) (by norm_num)
theorem B2792453 : Blo 1861632 2792453 := bbase (se 4 (by rfl) ⟨261792, by rfl⟩ : syracuseStep 2792453 = 523585) (by norm_num)
theorem B2096149 : Blo 1861632 2096149 := bbase (se 6 (by rfl) ⟨49128, by rfl⟩ : syracuseStep 2096149 = 98257) (by norm_num)
theorem B2792477 : Blo 1861632 2792477 := bbase (se 3 (by rfl) ⟨523589, by rfl⟩ : syracuseStep 2792477 = 1047179) (by norm_num)
theorem B2792501 : Blo 1861632 2792501 := bbase (se 5 (by rfl) ⟨130898, by rfl⟩ : syracuseStep 2792501 = 261797) (by norm_num)
theorem B2358325 : Blo 1861632 2358325 := bbase (se 5 (by rfl) ⟨110546, by rfl⟩ : syracuseStep 2358325 = 221093) (by norm_num)
theorem B3144757 : Blo 1861632 3144757 := bbase (se 5 (by rfl) ⟨147410, by rfl⟩ : syracuseStep 3144757 = 294821) (by norm_num)
theorem B2096185 : Blo 1861632 2096185 := bbase (se 2 (by rfl) ⟨786069, by rfl⟩ : syracuseStep 2096185 = 1572139) (by norm_num)
theorem B3537989 : Blo 1861632 3537989 := bbase (se 4 (by rfl) ⟨331686, by rfl⟩ : syracuseStep 3537989 = 663373) (by norm_num)
theorem B2792525 : Blo 1861632 2792525 := bbase (se 3 (by rfl) ⟨523598, by rfl⟩ : syracuseStep 2792525 = 1047197) (by norm_num)
theorem B2096221 : Blo 1861632 2096221 := bbase (se 3 (by rfl) ⟨393041, by rfl⟩ : syracuseStep 2096221 = 786083) (by norm_num)
theorem B2792549 : Blo 1861632 2792549 := bbase (se 4 (by rfl) ⟨261801, by rfl⟩ : syracuseStep 2792549 = 523603) (by norm_num)
theorem B2792573 : Blo 1861632 2792573 := bbase (se 3 (by rfl) ⟨523607, by rfl⟩ : syracuseStep 2792573 = 1047215) (by norm_num)
theorem B2096257 : Blo 1861632 2096257 := bbase (se 2 (by rfl) ⟨786096, by rfl⟩ : syracuseStep 2096257 = 1572193) (by norm_num)
theorem B3144845 : Blo 1861632 3144845 := bbase (se 3 (by rfl) ⟨589658, by rfl⟩ : syracuseStep 3144845 = 1179317) (by norm_num)
theorem B2792597 : Blo 1861632 2792597 := bbase (se 6 (by rfl) ⟨65451, by rfl⟩ : syracuseStep 2792597 = 130903) (by norm_num)
theorem B2096293 : Blo 1861632 2096293 := bbase (se 4 (by rfl) ⟨196527, by rfl⟩ : syracuseStep 2096293 = 393055) (by norm_num)
theorem B2792621 : Blo 1861632 2792621 := bbase (se 3 (by rfl) ⟨523616, by rfl⟩ : syracuseStep 2792621 = 1047233) (by norm_num)
theorem B2792645 : Blo 1861632 2792645 := bbase (se 4 (by rfl) ⟨261810, by rfl⟩ : syracuseStep 2792645 = 523621) (by norm_num)
theorem B2096329 : Blo 1861632 2096329 := bbase (se 2 (by rfl) ⟨786123, by rfl⟩ : syracuseStep 2096329 = 1572247) (by norm_num)
theorem B2792669 : Blo 1861632 2792669 := bbase (se 3 (by rfl) ⟨523625, by rfl⟩ : syracuseStep 2792669 = 1047251) (by norm_num)
theorem B2358497 : Blo 1861632 2358497 := bbase (se 2 (by rfl) ⟨884436, by rfl⟩ : syracuseStep 2358497 = 1768873) (by norm_num)
theorem B2268397 : Blo 1861632 2268397 := bbase (se 3 (by rfl) ⟨425324, by rfl⟩ : syracuseStep 2268397 = 850649) (by norm_num)
theorem B2096365 : Blo 1861632 2096365 := bbase (se 3 (by rfl) ⟨393068, by rfl⟩ : syracuseStep 2096365 = 786137) (by norm_num)
theorem B2792693 : Blo 1861632 2792693 := bbase (se 5 (by rfl) ⟨130907, by rfl⟩ : syracuseStep 2792693 = 261815) (by norm_num)
theorem B10607861 : Blo 1861632 10607861 := bbase (se 5 (by rfl) ⟨497243, by rfl⟩ : syracuseStep 10607861 = 994487) (by norm_num)
theorem B1989893 : Blo 1861632 1989893 := bbase (se 4 (by rfl) ⟨186552, by rfl⟩ : syracuseStep 1989893 = 373105) (by norm_num)
theorem B2792717 : Blo 1861632 2792717 := bbase (se 3 (by rfl) ⟨523634, by rfl⟩ : syracuseStep 2792717 = 1047269) (by norm_num)
theorem B2096401 : Blo 1861632 2096401 := bbase (se 2 (by rfl) ⟨786150, by rfl⟩ : syracuseStep 2096401 = 1572301) (by norm_num)
theorem B2358553 : Blo 1861632 2358553 := bbase (se 2 (by rfl) ⟨884457, by rfl⟩ : syracuseStep 2358553 = 1768915) (by norm_num)
theorem B2792741 : Blo 1861632 2792741 := bbase (se 4 (by rfl) ⟨261819, by rfl⟩ : syracuseStep 2792741 = 523639) (by norm_num)
theorem B2096437 : Blo 1861632 2096437 := bbase (se 5 (by rfl) ⟨98270, by rfl⟩ : syracuseStep 2096437 = 196541) (by norm_num)
theorem B2792765 : Blo 1861632 2792765 := bbase (se 3 (by rfl) ⟨523643, by rfl⟩ : syracuseStep 2792765 = 1047287) (by norm_num)
theorem B1989965 : Blo 1861632 1989965 := bbase (se 3 (by rfl) ⟨373118, by rfl⟩ : syracuseStep 1989965 = 746237) (by norm_num)
theorem B2792789 : Blo 1861632 2792789 := bbase (se 11 (by rfl) ⟨2045, by rfl⟩ : syracuseStep 2792789 = 4091) (by norm_num)
theorem B2096473 : Blo 1861632 2096473 := bbase (se 2 (by rfl) ⟨786177, by rfl⟩ : syracuseStep 2096473 = 1572355) (by norm_num)
theorem B2792813 : Blo 1861632 2792813 := bbase (se 3 (by rfl) ⟨523652, by rfl⟩ : syracuseStep 2792813 = 1047305) (by norm_num)
theorem B2358649 : Blo 1861632 2358649 := bbase (se 2 (by rfl) ⟨884493, by rfl⟩ : syracuseStep 2358649 = 1768987) (by norm_num)
theorem B2096509 : Blo 1861632 2096509 := bbase (se 3 (by rfl) ⟨393095, by rfl⟩ : syracuseStep 2096509 = 786191) (by norm_num)
theorem B2792837 : Blo 1861632 2792837 := bbase (se 4 (by rfl) ⟨261828, by rfl⟩ : syracuseStep 2792837 = 523657) (by norm_num)
theorem B2792861 : Blo 1861632 2792861 := bbase (se 3 (by rfl) ⟨523661, by rfl⟩ : syracuseStep 2792861 = 1047323) (by norm_num)
theorem B2096545 : Blo 1861632 2096545 := bbase (se 2 (by rfl) ⟨786204, by rfl⟩ : syracuseStep 2096545 = 1572409) (by norm_num)
theorem B2792885 : Blo 1861632 2792885 := bbase (se 5 (by rfl) ⟨130916, by rfl⟩ : syracuseStep 2792885 = 261833) (by norm_num)
theorem B2096581 : Blo 1861632 2096581 := bbase (se 4 (by rfl) ⟨196554, by rfl⟩ : syracuseStep 2096581 = 393109) (by norm_num)
theorem B2792909 : Blo 1861632 2792909 := bbase (se 3 (by rfl) ⟨523670, by rfl⟩ : syracuseStep 2792909 = 1047341) (by norm_num)
theorem B19373525 : Blo 1861632 19373525 := bbase (se 7 (by rfl) ⟨227033, by rfl⟩ : syracuseStep 19373525 = 454067) (by norm_num)
theorem B2792933 : Blo 1861632 2792933 := bbase (se 4 (by rfl) ⟨261837, by rfl⟩ : syracuseStep 2792933 = 523675) (by norm_num)
theorem B2792957 : Blo 1861632 2792957 := bbase (se 3 (by rfl) ⟨523679, by rfl⟩ : syracuseStep 2792957 = 1047359) (by norm_num)
theorem B2792981 : Blo 1861632 2792981 := bbase (se 6 (by rfl) ⟨65460, by rfl⟩ : syracuseStep 2792981 = 130921) (by norm_num)
theorem B6807061 : Blo 1861632 6807061 := bbase (se 6 (by rfl) ⟨159540, by rfl⟩ : syracuseStep 6807061 = 319081) (by norm_num)
theorem B2793005 : Blo 1861632 2793005 := bbase (se 3 (by rfl) ⟨523688, by rfl⟩ : syracuseStep 2793005 = 1047377) (by norm_num)
theorem B2793029 : Blo 1861632 2793029 := bbase (se 4 (by rfl) ⟨261846, by rfl⟩ : syracuseStep 2793029 = 523693) (by norm_num)
theorem B2793053 : Blo 1861632 2793053 := bbase (se 3 (by rfl) ⟨523697, by rfl⟩ : syracuseStep 2793053 = 1047395) (by norm_num)
theorem B2793077 : Blo 1861632 2793077 := bbase (se 5 (by rfl) ⟨130925, by rfl⟩ : syracuseStep 2793077 = 261851) (by norm_num)
theorem B2793101 : Blo 1861632 2793101 := bbase (se 3 (by rfl) ⟨523706, by rfl⟩ : syracuseStep 2793101 = 1047413) (by norm_num)
theorem B2793125 : Blo 1861632 2793125 := bbase (se 4 (by rfl) ⟨261855, by rfl⟩ : syracuseStep 2793125 = 523711) (by norm_num)
theorem B2793149 : Blo 1861632 2793149 := bbase (se 3 (by rfl) ⟨523715, by rfl⟩ : syracuseStep 2793149 = 1047431) (by norm_num)
theorem B2793173 : Blo 1861632 2793173 := bbase (se 7 (by rfl) ⟨32732, by rfl⟩ : syracuseStep 2793173 = 65465) (by norm_num)
theorem B22658773 : Blo 1861632 22658773 := bbase (se 7 (by rfl) ⟨265532, by rfl⟩ : syracuseStep 22658773 = 531065) (by norm_num)
theorem B2793197 : Blo 1861632 2793197 := bbase (se 3 (by rfl) ⟨523724, by rfl⟩ : syracuseStep 2793197 = 1047449) (by norm_num)
theorem B2793221 : Blo 1861632 2793221 := bbase (se 4 (by rfl) ⟨261864, by rfl⟩ : syracuseStep 2793221 = 523729) (by norm_num)
theorem B2793245 : Blo 1861632 2793245 := bbase (se 3 (by rfl) ⟨523733, by rfl⟩ : syracuseStep 2793245 = 1047467) (by norm_num)
theorem B7069477 : Blo 1861632 7069477 := bbase (se 4 (by rfl) ⟨662763, by rfl⟩ : syracuseStep 7069477 = 1325527) (by norm_num)
theorem B6283061 : Blo 1861632 6283061 := bbase (se 5 (by rfl) ⟨294518, by rfl⟩ : syracuseStep 6283061 = 589037) (by norm_num)
theorem B2793269 : Blo 1861632 2793269 := bbase (se 5 (by rfl) ⟨130934, by rfl⟩ : syracuseStep 2793269 = 261869) (by norm_num)
theorem B2793293 : Blo 1861632 2793293 := bbase (se 3 (by rfl) ⟨523742, by rfl⟩ : syracuseStep 2793293 = 1047485) (by norm_num)
theorem B2793317 : Blo 1861632 2793317 := bbase (se 4 (by rfl) ⟨261873, by rfl⟩ : syracuseStep 2793317 = 523747) (by norm_num)
theorem B16342901 : Blo 1861632 16342901 := bbase (se 5 (by rfl) ⟨766073, by rfl⟩ : syracuseStep 16342901 = 1532147) (by norm_num)
theorem B16990069 : Blo 1861632 16990069 := bbase (se 5 (by rfl) ⟨796409, by rfl⟩ : syracuseStep 16990069 = 1592819) (by norm_num)
theorem B2793341 : Blo 1861632 2793341 := bbase (se 3 (by rfl) ⟨523751, by rfl⟩ : syracuseStep 2793341 = 1047503) (by norm_num)
theorem B7954325 : Blo 1861632 7954325 := bbase (se 6 (by rfl) ⟨186429, by rfl⟩ : syracuseStep 7954325 = 372859) (by norm_num)
theorem B2793365 : Blo 1861632 2793365 := bbase (se 6 (by rfl) ⟨65469, by rfl⟩ : syracuseStep 2793365 = 130939) (by norm_num)
theorem B9428885 : Blo 1861632 9428885 := bbase (se 6 (by rfl) ⟨220989, by rfl⟩ : syracuseStep 9428885 = 441979) (by norm_num)
theorem B2793389 : Blo 1861632 2793389 := bbase (se 3 (by rfl) ⟨523760, by rfl⟩ : syracuseStep 2793389 = 1047521) (by norm_num)
theorem B2793413 : Blo 1861632 2793413 := bbase (se 4 (by rfl) ⟨261882, by rfl⟩ : syracuseStep 2793413 = 523765) (by norm_num)
theorem B2793437 : Blo 1861632 2793437 := bbase (se 3 (by rfl) ⟨523769, by rfl⟩ : syracuseStep 2793437 = 1047539) (by norm_num)
theorem B2793461 : Blo 1861632 2793461 := bbase (se 5 (by rfl) ⟨130943, by rfl⟩ : syracuseStep 2793461 = 261887) (by norm_num)
theorem B2793473 : Blo 1861632 2793473 := bstep (se 2 (by rfl) ⟨1047552, by rfl⟩ : syracuseStep 2793473 = 2095105) B2095105
theorem B6283277 : Blo 1861632 6283277 := bstep (se 3 (by rfl) ⟨1178114, by rfl⟩ : syracuseStep 6283277 = 2356229) B2356229
theorem B2793491 : Blo 1861632 2793491 := bstep (se 1 (by rfl) ⟨2095118, by rfl⟩ : syracuseStep 2793491 = 4190237) B4190237
theorem B2793521 : Blo 1861632 2793521 := bstep (se 2 (by rfl) ⟨1047570, by rfl⟩ : syracuseStep 2793521 = 2095141) B2095141
theorem B6283331 : Blo 1861632 6283331 := bstep (se 1 (by rfl) ⟨4712498, by rfl⟩ : syracuseStep 6283331 = 9424997) B9424997
theorem B2793539 : Blo 1861632 2793539 := bstep (se 1 (by rfl) ⟨2095154, by rfl⟩ : syracuseStep 2793539 = 4190309) B4190309
theorem B2793569 : Blo 1861632 2793569 := bstep (se 2 (by rfl) ⟨1047588, by rfl⟩ : syracuseStep 2793569 = 2095177) B2095177
theorem B2793587 : Blo 1861632 2793587 := bstep (se 1 (by rfl) ⟨2095190, by rfl⟩ : syracuseStep 2793587 = 4190381) B4190381
theorem B2793617 : Blo 1861632 2793617 := bstep (se 2 (by rfl) ⟨1047606, by rfl⟩ : syracuseStep 2793617 = 2095213) B2095213
theorem B2793635 : Blo 1861632 2793635 := bstep (se 1 (by rfl) ⟨2095226, by rfl⟩ : syracuseStep 2793635 = 4190453) B4190453
theorem B2793665 : Blo 1861632 2793665 := bstep (se 2 (by rfl) ⟨1047624, by rfl⟩ : syracuseStep 2793665 = 2095249) B2095249
theorem B2793683 : Blo 1861632 2793683 := bstep (se 1 (by rfl) ⟨2095262, by rfl⟩ : syracuseStep 2793683 = 4190525) B4190525
theorem B2793713 : Blo 1861632 2793713 := bstep (se 2 (by rfl) ⟨1047642, by rfl⟩ : syracuseStep 2793713 = 2095285) B2095285
theorem B2793731 : Blo 1861632 2793731 := bstep (se 1 (by rfl) ⟨2095298, by rfl⟩ : syracuseStep 2793731 = 4190597) B4190597
theorem B2793761 : Blo 1861632 2793761 := bstep (se 2 (by rfl) ⟨1047660, by rfl⟩ : syracuseStep 2793761 = 2095321) B2095321
theorem B4473137 : Blo 1861632 4473137 := bstep (se 2 (by rfl) ⟨1677426, by rfl⟩ : syracuseStep 4473137 = 3354853) B3354853
theorem B2793779 : Blo 1861632 2793779 := bstep (se 1 (by rfl) ⟨2095334, by rfl⟩ : syracuseStep 2793779 = 4190669) B4190669
theorem B6283601 : Blo 1861632 6283601 := bstep (se 2 (by rfl) ⟨2356350, by rfl⟩ : syracuseStep 6283601 = 4712701) B4712701
theorem B2793809 : Blo 1861632 2793809 := bstep (se 2 (by rfl) ⟨1047678, by rfl⟩ : syracuseStep 2793809 = 2095357) B2095357
theorem B7954787 : Blo 1861632 7954787 := bstep (se 1 (by rfl) ⟨5966090, by rfl⟩ : syracuseStep 7954787 = 11932181) B11932181
theorem B2793827 : Blo 1861632 2793827 := bstep (se 1 (by rfl) ⟨2095370, by rfl⟩ : syracuseStep 2793827 = 4190741) B4190741
theorem B11936099 : Blo 1861632 11936099 := bstep (se 1 (by rfl) ⟨8952074, by rfl⟩ : syracuseStep 11936099 = 17904149) B17904149
theorem B2793857 : Blo 1861632 2793857 := bstep (se 2 (by rfl) ⟨1047696, by rfl⟩ : syracuseStep 2793857 = 2095393) B2095393
theorem B2793875 : Blo 1861632 2793875 := bstep (se 1 (by rfl) ⟨2095406, by rfl⟩ : syracuseStep 2793875 = 4190813) B4190813
theorem B2793905 : Blo 1861632 2793905 := bstep (se 2 (by rfl) ⟨1047714, by rfl⟩ : syracuseStep 2793905 = 2095429) B2095429
theorem B21209525 : Blo 1861632 21209525 := bstep (se 5 (by rfl) ⟨994196, by rfl⟩ : syracuseStep 21209525 = 1988393) B1988393
theorem B2793923 : Blo 1861632 2793923 := bstep (se 1 (by rfl) ⟨2095442, by rfl⟩ : syracuseStep 2793923 = 4190885) B4190885
theorem B2793953 : Blo 1861632 2793953 := bstep (se 2 (by rfl) ⟨1047732, by rfl⟩ : syracuseStep 2793953 = 2095465) B2095465
theorem B2793971 : Blo 1861632 2793971 := bstep (se 1 (by rfl) ⟨2095478, by rfl⟩ : syracuseStep 2793971 = 4190957) B4190957
theorem B2794001 : Blo 1861632 2794001 := bstep (se 2 (by rfl) ⟨1047750, by rfl⟩ : syracuseStep 2794001 = 2095501) B2095501
theorem B2794019 : Blo 1861632 2794019 := bstep (se 1 (by rfl) ⟨2095514, by rfl⟩ : syracuseStep 2794019 = 4191029) B4191029
theorem B2794049 : Blo 1861632 2794049 := bstep (se 2 (by rfl) ⟨1047768, by rfl⟩ : syracuseStep 2794049 = 2095537) B2095537
theorem B2794067 : Blo 1861632 2794067 := bstep (se 1 (by rfl) ⟨2095550, by rfl⟩ : syracuseStep 2794067 = 4191101) B4191101
theorem B2794097 : Blo 1861632 2794097 := bstep (se 2 (by rfl) ⟨1047786, by rfl⟩ : syracuseStep 2794097 = 2095573) B2095573
theorem B2794115 : Blo 1861632 2794115 := bstep (se 1 (by rfl) ⟨2095586, by rfl⟩ : syracuseStep 2794115 = 4191173) B4191173
theorem B2794145 : Blo 1861632 2794145 := bstep (se 2 (by rfl) ⟨1047804, by rfl⟩ : syracuseStep 2794145 = 2095609) B2095609
theorem B4473521 : Blo 1861632 4473521 := bstep (se 2 (by rfl) ⟨1677570, by rfl⟩ : syracuseStep 4473521 = 3355141) B3355141
theorem B2794163 : Blo 1861632 2794163 := bstep (se 1 (by rfl) ⟨2095622, by rfl⟩ : syracuseStep 2794163 = 4191245) B4191245
theorem B2794193 : Blo 1861632 2794193 := bstep (se 2 (by rfl) ⟨1047822, by rfl⟩ : syracuseStep 2794193 = 2095645) B2095645
theorem B7070435 : Blo 1861632 7070435 := bstep (se 1 (by rfl) ⟨5302826, by rfl⟩ : syracuseStep 7070435 = 10605653) B10605653
theorem B2794211 : Blo 1861632 2794211 := bstep (se 1 (by rfl) ⟨2095658, by rfl⟩ : syracuseStep 2794211 = 4191317) B4191317
theorem B2982641 : Blo 1861632 2982641 := bstep (se 2 (by rfl) ⟨1118490, by rfl⟩ : syracuseStep 2982641 = 2236981) B2236981
theorem B7070449 : Blo 1861632 7070449 := bstep (se 2 (by rfl) ⟨2651418, by rfl⟩ : syracuseStep 7070449 = 5302837) B5302837
theorem B2794241 : Blo 1861632 2794241 := bstep (se 2 (by rfl) ⟨1047840, by rfl⟩ : syracuseStep 2794241 = 2095681) B2095681
theorem B2794259 : Blo 1861632 2794259 := bstep (se 1 (by rfl) ⟨2095694, by rfl⟩ : syracuseStep 2794259 = 4191389) B4191389
theorem B2794289 : Blo 1861632 2794289 := bstep (se 2 (by rfl) ⟨1047858, by rfl⟩ : syracuseStep 2794289 = 2095717) B2095717
theorem B2794307 : Blo 1861632 2794307 := bstep (se 1 (by rfl) ⟨2095730, by rfl⟩ : syracuseStep 2794307 = 4191461) B4191461
theorem B2794337 : Blo 1861632 2794337 := bstep (se 2 (by rfl) ⟨1047876, by rfl⟩ : syracuseStep 2794337 = 2095753) B2095753
theorem B6284141 : Blo 1861632 6284141 := bstep (se 3 (by rfl) ⟨1178276, by rfl⟩ : syracuseStep 6284141 = 2356553) B2356553
theorem B2794355 : Blo 1861632 2794355 := bstep (se 1 (by rfl) ⟨2095766, by rfl⟩ : syracuseStep 2794355 = 4191533) B4191533
theorem B4473731 : Blo 1861632 4473731 := bstep (se 1 (by rfl) ⟨3355298, by rfl⟩ : syracuseStep 4473731 = 6710597) B6710597
theorem B2794385 : Blo 1861632 2794385 := bstep (se 2 (by rfl) ⟨1047894, by rfl⟩ : syracuseStep 2794385 = 2095789) B2095789
theorem B6284195 : Blo 1861632 6284195 := bstep (se 1 (by rfl) ⟨4713146, by rfl⟩ : syracuseStep 6284195 = 9426293) B9426293
theorem B2794403 : Blo 1861632 2794403 := bstep (se 1 (by rfl) ⟨2095802, by rfl⟩ : syracuseStep 2794403 = 4191605) B4191605
theorem B2794433 : Blo 1861632 2794433 := bstep (se 2 (by rfl) ⟨1047912, by rfl⟩ : syracuseStep 2794433 = 2095825) B2095825
theorem B2794451 : Blo 1861632 2794451 := bstep (se 1 (by rfl) ⟨2095838, by rfl⟩ : syracuseStep 2794451 = 4191677) B4191677
theorem B30204899 : Blo 1861632 30204899 := bstep (se 1 (by rfl) ⟨22653674, by rfl⟩ : syracuseStep 30204899 = 45307349) B45307349
theorem B6374371 : Blo 1861632 6374371 := bstep (se 1 (by rfl) ⟨4780778, by rfl⟩ : syracuseStep 6374371 = 9561557) B9561557
theorem B2794481 : Blo 1861632 2794481 := bstep (se 2 (by rfl) ⟨1047930, by rfl⟩ : syracuseStep 2794481 = 2095861) B2095861
theorem B2794499 : Blo 1861632 2794499 := bstep (se 1 (by rfl) ⟨2095874, by rfl⟩ : syracuseStep 2794499 = 4191749) B4191749
theorem B2794529 : Blo 1861632 2794529 := bstep (se 2 (by rfl) ⟨1047948, by rfl⟩ : syracuseStep 2794529 = 2095897) B2095897
theorem B2237491 : Blo 1861632 2237491 := bstep (se 1 (by rfl) ⟨1678118, by rfl⟩ : syracuseStep 2237491 = 3356237) B3356237
theorem B2794547 : Blo 1861632 2794547 := bstep (se 1 (by rfl) ⟨2095910, by rfl⟩ : syracuseStep 2794547 = 4191821) B4191821
theorem B2794577 : Blo 1861632 2794577 := bstep (se 2 (by rfl) ⟨1047966, by rfl⟩ : syracuseStep 2794577 = 2095933) B2095933
theorem B2237539 : Blo 1861632 2237539 := bstep (se 1 (by rfl) ⟨1678154, by rfl⟩ : syracuseStep 2237539 = 3356309) B3356309
theorem B2794595 : Blo 1861632 2794595 := bstep (se 1 (by rfl) ⟨2095946, by rfl⟩ : syracuseStep 2794595 = 4191893) B4191893
theorem B7554161 : Blo 1861632 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B2794625 : Blo 1861632 2794625 := bstep (se 2 (by rfl) ⟨1047984, by rfl⟩ : syracuseStep 2794625 = 2095969) B2095969
theorem B5301379 : Blo 1861632 5301379 := bstep (se 1 (by rfl) ⟨3976034, by rfl⟩ : syracuseStep 5301379 = 7952069) B7952069
theorem B2794643 : Blo 1861632 2794643 := bstep (se 1 (by rfl) ⟨2095982, by rfl⟩ : syracuseStep 2794643 = 4191965) B4191965
theorem B5301425 : Blo 1861632 5301425 := bstep (se 2 (by rfl) ⟨1988034, by rfl⟩ : syracuseStep 5301425 = 3976069) B3976069
theorem B6284465 : Blo 1861632 6284465 := bstep (se 2 (by rfl) ⟨2356674, by rfl⟩ : syracuseStep 6284465 = 4713349) B4713349
theorem B2794673 : Blo 1861632 2794673 := bstep (se 2 (by rfl) ⟨1048002, by rfl⟩ : syracuseStep 2794673 = 2096005) B2096005
theorem B2794691 : Blo 1861632 2794691 := bstep (se 1 (by rfl) ⟨2096018, by rfl⟩ : syracuseStep 2794691 = 4192037) B4192037
theorem B2794721 : Blo 1861632 2794721 := bstep (se 2 (by rfl) ⟨1048020, by rfl⟩ : syracuseStep 2794721 = 2096041) B2096041
theorem B2794739 : Blo 1861632 2794739 := bstep (se 1 (by rfl) ⟨2096054, by rfl⟩ : syracuseStep 2794739 = 4192109) B4192109
theorem B2794769 : Blo 1861632 2794769 := bstep (se 2 (by rfl) ⟨1048038, by rfl⟩ : syracuseStep 2794769 = 2096077) B2096077
theorem B2794787 : Blo 1861632 2794787 := bstep (se 1 (by rfl) ⟨2096090, by rfl⟩ : syracuseStep 2794787 = 4192181) B4192181
theorem B2794817 : Blo 1861632 2794817 := bstep (se 2 (by rfl) ⟨1048056, by rfl⟩ : syracuseStep 2794817 = 2096113) B2096113
theorem B2794835 : Blo 1861632 2794835 := bstep (se 1 (by rfl) ⟨2096126, by rfl⟩ : syracuseStep 2794835 = 4192253) B4192253
theorem B6710627 : Blo 1861632 6710627 := bstep (se 1 (by rfl) ⟨5032970, by rfl⟩ : syracuseStep 6710627 = 10065941) B10065941
theorem B2794865 : Blo 1861632 2794865 := bstep (se 2 (by rfl) ⟨1048074, by rfl⟩ : syracuseStep 2794865 = 2096149) B2096149
theorem B2794883 : Blo 1861632 2794883 := bstep (se 1 (by rfl) ⟨2096162, by rfl⟩ : syracuseStep 2794883 = 4192325) B4192325
theorem B2794913 : Blo 1861632 2794913 := bstep (se 2 (by rfl) ⟨1048092, by rfl⟩ : syracuseStep 2794913 = 2096185) B2096185
theorem B2794931 : Blo 1861632 2794931 := bstep (se 1 (by rfl) ⟨2096198, by rfl⟩ : syracuseStep 2794931 = 4192397) B4192397
theorem B11322821 : Blo 1861632 11322821 := bstep (se 4 (by rfl) ⟨1061514, by rfl⟩ : syracuseStep 11322821 = 2123029) B2123029
theorem B2794961 : Blo 1861632 2794961 := bstep (se 2 (by rfl) ⟨1048110, by rfl⟩ : syracuseStep 2794961 = 2096221) B2096221
theorem B2794979 : Blo 1861632 2794979 := bstep (se 1 (by rfl) ⟨2096234, by rfl⟩ : syracuseStep 2794979 = 4192469) B4192469
theorem B2795009 : Blo 1861632 2795009 := bstep (se 2 (by rfl) ⟨1048128, by rfl⟩ : syracuseStep 2795009 = 2096257) B2096257
theorem B21227021 : Blo 1861632 21227021 := bstep (se 3 (by rfl) ⟨3980066, by rfl⟩ : syracuseStep 21227021 = 7960133) B7960133
theorem B2795027 : Blo 1861632 2795027 := bstep (se 1 (by rfl) ⟨2096270, by rfl⟩ : syracuseStep 2795027 = 4192541) B4192541
theorem B6374957 : Blo 1861632 6374957 := bstep (se 3 (by rfl) ⟨1195304, by rfl⟩ : syracuseStep 6374957 = 2390609) B2390609
theorem B2795057 : Blo 1861632 2795057 := bstep (se 2 (by rfl) ⟨1048146, by rfl⟩ : syracuseStep 2795057 = 2096293) B2096293
theorem B2983475 : Blo 1861632 2983475 := bstep (se 1 (by rfl) ⟨2237606, by rfl⟩ : syracuseStep 2983475 = 4475213) B4475213
theorem B2795075 : Blo 1861632 2795075 := bstep (se 1 (by rfl) ⟨2096306, by rfl⟩ : syracuseStep 2795075 = 4192613) B4192613
theorem B2795105 : Blo 1861632 2795105 := bstep (se 2 (by rfl) ⟨1048164, by rfl⟩ : syracuseStep 2795105 = 2096329) B2096329
theorem B2795123 : Blo 1861632 2795123 := bstep (se 1 (by rfl) ⟨2096342, by rfl⟩ : syracuseStep 2795123 = 4192685) B4192685
theorem B5662349 : Blo 1861632 5662349 := bstep (se 3 (by rfl) ⟨1061690, by rfl⟩ : syracuseStep 5662349 = 2123381) B2123381
theorem B2795153 : Blo 1861632 2795153 := bstep (se 2 (by rfl) ⟨1048182, by rfl⟩ : syracuseStep 2795153 = 2096365) B2096365
theorem B9553571 : Blo 1861632 9553571 := bstep (se 1 (by rfl) ⟨7165178, by rfl⟩ : syracuseStep 9553571 = 14330357) B14330357
theorem B2795171 : Blo 1861632 2795171 := bstep (se 1 (by rfl) ⟨2096378, by rfl⟩ : syracuseStep 2795171 = 4192757) B4192757
theorem B2795201 : Blo 1861632 2795201 := bstep (se 2 (by rfl) ⟨1048200, by rfl⟩ : syracuseStep 2795201 = 2096401) B2096401
theorem B6285005 : Blo 1861632 6285005 := bstep (se 3 (by rfl) ⟨1178438, by rfl⟩ : syracuseStep 6285005 = 2356877) B2356877
theorem B4474577 : Blo 1861632 4474577 := bstep (se 2 (by rfl) ⟨1677966, by rfl⟩ : syracuseStep 4474577 = 3355933) B3355933
theorem B2795219 : Blo 1861632 2795219 := bstep (se 1 (by rfl) ⟨2096414, by rfl⟩ : syracuseStep 2795219 = 4192829) B4192829
theorem B2016995 : Blo 1861632 2016995 := bstep (se 1 (by rfl) ⟨1512746, by rfl⟩ : syracuseStep 2016995 = 3025493) B3025493
theorem B2795249 : Blo 1861632 2795249 := bstep (se 2 (by rfl) ⟨1048218, by rfl⟩ : syracuseStep 2795249 = 2096437) B2096437
theorem B6285059 : Blo 1861632 6285059 := bstep (se 1 (by rfl) ⟨4713794, by rfl⟩ : syracuseStep 6285059 = 9427589) B9427589
theorem B2238211 : Blo 1861632 2238211 := bstep (se 1 (by rfl) ⟨1678658, by rfl⟩ : syracuseStep 2238211 = 3357317) B3357317
theorem B2795267 : Blo 1861632 2795267 := bstep (se 1 (by rfl) ⟨2096450, by rfl⟩ : syracuseStep 2795267 = 4192901) B4192901
theorem B2795297 : Blo 1861632 2795297 := bstep (se 2 (by rfl) ⟨1048236, by rfl⟩ : syracuseStep 2795297 = 2096473) B2096473
theorem B10209059 : Blo 1861632 10209059 := bstep (se 1 (by rfl) ⟨7656794, by rfl⟩ : syracuseStep 10209059 = 15313589) B15313589
theorem B2795315 : Blo 1861632 2795315 := bstep (se 1 (by rfl) ⟨2096486, by rfl⟩ : syracuseStep 2795315 = 4192973) B4192973
theorem B2795345 : Blo 1861632 2795345 := bstep (se 2 (by rfl) ⟨1048254, by rfl⟩ : syracuseStep 2795345 = 2096509) B2096509
theorem B2983763 : Blo 1861632 2983763 := bstep (se 1 (by rfl) ⟨2237822, by rfl⟩ : syracuseStep 2983763 = 4475645) B4475645
theorem B2795363 : Blo 1861632 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B2795393 : Blo 1861632 2795393 := bstep (se 2 (by rfl) ⟨1048272, by rfl⟩ : syracuseStep 2795393 = 2096545) B2096545
theorem B4474769 : Blo 1861632 4474769 := bstep (se 2 (by rfl) ⟨1678038, by rfl⟩ : syracuseStep 4474769 = 3356077) B3356077
theorem B2795411 : Blo 1861632 2795411 := bstep (se 1 (by rfl) ⟨2096558, by rfl⟩ : syracuseStep 2795411 = 4193117) B4193117
theorem B5105585 : Blo 1861632 5105585 := bstep (se 2 (by rfl) ⟨1914594, by rfl⟩ : syracuseStep 5105585 = 3829189) B3829189
theorem B2795441 : Blo 1861632 2795441 := bstep (se 2 (by rfl) ⟨1048290, by rfl⟩ : syracuseStep 2795441 = 2096581) B2096581
theorem B1861635 : Blo 1861632 1861635 := bstep (se 1 (by rfl) ⟨1396226, by rfl⟩ : syracuseStep 1861635 = 2792453) B2792453
theorem B6285329 : Blo 1861632 6285329 := bstep (se 2 (by rfl) ⟨2356998, by rfl⟩ : syracuseStep 6285329 = 4713997) B4713997
theorem B1861651 : Blo 1861632 1861651 := bstep (se 1 (by rfl) ⟨1396238, by rfl⟩ : syracuseStep 1861651 = 2792477) B2792477
theorem B1861667 : Blo 1861632 1861667 := bstep (se 1 (by rfl) ⟨1396250, by rfl⟩ : syracuseStep 1861667 = 2792501) B2792501
theorem B1861683 : Blo 1861632 1861683 := bstep (se 1 (by rfl) ⟨1396262, by rfl⟩ : syracuseStep 1861683 = 2792525) B2792525
theorem B2983987 : Blo 1861632 2983987 := bstep (se 1 (by rfl) ⟨2237990, by rfl⟩ : syracuseStep 2983987 = 4475981) B4475981
theorem B1861699 : Blo 1861632 1861699 := bstep (se 1 (by rfl) ⟨1396274, by rfl⟩ : syracuseStep 1861699 = 2792549) B2792549
theorem B1861715 : Blo 1861632 1861715 := bstep (se 1 (by rfl) ⟨1396286, by rfl⟩ : syracuseStep 1861715 = 2792573) B2792573
theorem B1861731 : Blo 1861632 1861731 := bstep (se 1 (by rfl) ⟨1396298, by rfl⟩ : syracuseStep 1861731 = 2792597) B2792597
theorem B9431153 : Blo 1861632 9431153 := bstep (se 2 (by rfl) ⟨3536682, by rfl⟩ : syracuseStep 9431153 = 7073365) B7073365
theorem B1861747 : Blo 1861632 1861747 := bstep (se 1 (by rfl) ⟨1396310, by rfl⟩ : syracuseStep 1861747 = 2792621) B2792621
theorem B1861763 : Blo 1861632 1861763 := bstep (se 1 (by rfl) ⟨1396322, by rfl⟩ : syracuseStep 1861763 = 2792645) B2792645
theorem B1861779 : Blo 1861632 1861779 := bstep (se 1 (by rfl) ⟨1396334, by rfl⟩ : syracuseStep 1861779 = 2792669) B2792669
theorem B1861795 : Blo 1861632 1861795 := bstep (se 1 (by rfl) ⟨1396346, by rfl⟩ : syracuseStep 1861795 = 2792693) B2792693
theorem B7071907 : Blo 1861632 7071907 := bstep (se 1 (by rfl) ⟨5303930, by rfl⟩ : syracuseStep 7071907 = 10607861) B10607861
theorem B1861811 : Blo 1861632 1861811 := bstep (se 1 (by rfl) ⟨1396358, by rfl⟩ : syracuseStep 1861811 = 2792717) B2792717
theorem B1861827 : Blo 1861632 1861827 := bstep (se 1 (by rfl) ⟨1396370, by rfl⟩ : syracuseStep 1861827 = 2792741) B2792741
theorem B1861843 : Blo 1861632 1861843 := bstep (se 1 (by rfl) ⟨1396382, by rfl⟩ : syracuseStep 1861843 = 2792765) B2792765
theorem B1861859 : Blo 1861632 1861859 := bstep (se 1 (by rfl) ⟨1396394, by rfl⟩ : syracuseStep 1861859 = 2792789) B2792789
theorem B10602737 : Blo 1861632 10602737 := bstep (se 2 (by rfl) ⟨3976026, by rfl⟩ : syracuseStep 10602737 = 7952053) B7952053
theorem B1861875 : Blo 1861632 1861875 := bstep (se 1 (by rfl) ⟨1396406, by rfl⟩ : syracuseStep 1861875 = 2792813) B2792813
theorem B1861891 : Blo 1861632 1861891 := bstep (se 1 (by rfl) ⟨1396418, by rfl⟩ : syracuseStep 1861891 = 2792837) B2792837
theorem B5105933 : Blo 1861632 5105933 := bstep (se 3 (by rfl) ⟨957362, by rfl⟩ : syracuseStep 5105933 = 1914725) B1914725
theorem B5662993 : Blo 1861632 5662993 := bstep (se 2 (by rfl) ⟨2123622, by rfl⟩ : syracuseStep 5662993 = 4247245) B4247245
theorem B1861907 : Blo 1861632 1861907 := bstep (se 1 (by rfl) ⟨1396430, by rfl⟩ : syracuseStep 1861907 = 2792861) B2792861
theorem B1861923 : Blo 1861632 1861923 := bstep (se 1 (by rfl) ⟨1396442, by rfl⟩ : syracuseStep 1861923 = 2792885) B2792885
theorem B5966129 : Blo 1861632 5966129 := bstep (se 2 (by rfl) ⟨2237298, by rfl⟩ : syracuseStep 5966129 = 4474597) B4474597
theorem B7956785 : Blo 1861632 7956785 := bstep (se 2 (by rfl) ⟨2983794, by rfl⟩ : syracuseStep 7956785 = 5967589) B5967589
theorem B1861939 : Blo 1861632 1861939 := bstep (se 1 (by rfl) ⟨1396454, by rfl⟩ : syracuseStep 1861939 = 2792909) B2792909
theorem B1861955 : Blo 1861632 1861955 := bstep (se 1 (by rfl) ⟨1396466, by rfl⟩ : syracuseStep 1861955 = 2792933) B2792933
theorem B1861971 : Blo 1861632 1861971 := bstep (se 1 (by rfl) ⟨1396478, by rfl⟩ : syracuseStep 1861971 = 2792957) B2792957
theorem B1861987 : Blo 1861632 1861987 := bstep (se 1 (by rfl) ⟨1396490, by rfl⟩ : syracuseStep 1861987 = 2792981) B2792981
theorem B1862003 : Blo 1861632 1862003 := bstep (se 1 (by rfl) ⟨1396502, by rfl⟩ : syracuseStep 1862003 = 2793005) B2793005
theorem B1862019 : Blo 1861632 1862019 := bstep (se 1 (by rfl) ⟨1396514, by rfl⟩ : syracuseStep 1862019 = 2793029) B2793029
theorem B1862035 : Blo 1861632 1862035 := bstep (se 1 (by rfl) ⟨1396526, by rfl⟩ : syracuseStep 1862035 = 2793053) B2793053
theorem B1862051 : Blo 1861632 1862051 := bstep (se 1 (by rfl) ⟨1396538, by rfl⟩ : syracuseStep 1862051 = 2793077) B2793077
theorem B5966257 : Blo 1861632 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B1862067 : Blo 1861632 1862067 := bstep (se 1 (by rfl) ⟨1396550, by rfl⟩ : syracuseStep 1862067 = 2793101) B2793101
theorem B1862083 : Blo 1861632 1862083 := bstep (se 1 (by rfl) ⟨1396562, by rfl⟩ : syracuseStep 1862083 = 2793125) B2793125
theorem B1862099 : Blo 1861632 1862099 := bstep (se 1 (by rfl) ⟨1396574, by rfl⟩ : syracuseStep 1862099 = 2793149) B2793149
theorem B1862115 : Blo 1861632 1862115 := bstep (se 1 (by rfl) ⟨1396586, by rfl⟩ : syracuseStep 1862115 = 2793173) B2793173
theorem B3631601 : Blo 1861632 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B22653425 : Blo 1861632 22653425 := bstep (se 2 (by rfl) ⟨8495034, by rfl⟩ : syracuseStep 22653425 = 16990069) B16990069
theorem B1862131 : Blo 1861632 1862131 := bstep (se 1 (by rfl) ⟨1396598, by rfl⟩ : syracuseStep 1862131 = 2793197) B2793197
theorem B1862147 : Blo 1861632 1862147 := bstep (se 1 (by rfl) ⟨1396610, by rfl⟩ : syracuseStep 1862147 = 2793221) B2793221
theorem B4188689 : Blo 1861632 4188689 := bstep (se 2 (by rfl) ⟨1570758, by rfl⟩ : syracuseStep 4188689 = 3141517) B3141517
theorem B1862163 : Blo 1861632 1862163 := bstep (se 1 (by rfl) ⟨1396622, by rfl⟩ : syracuseStep 1862163 = 2793245) B2793245
theorem B4188707 : Blo 1861632 4188707 := bstep (se 1 (by rfl) ⟨3141530, by rfl⟩ : syracuseStep 4188707 = 6283061) B6283061
theorem B1862179 : Blo 1861632 1862179 := bstep (se 1 (by rfl) ⟨1396634, by rfl⟩ : syracuseStep 1862179 = 2793269) B2793269
theorem B6285869 : Blo 1861632 6285869 := bstep (se 3 (by rfl) ⟨1178600, by rfl⟩ : syracuseStep 6285869 = 2357201) B2357201
theorem B1862195 : Blo 1861632 1862195 := bstep (se 1 (by rfl) ⟨1396646, by rfl⟩ : syracuseStep 1862195 = 2793293) B2793293
theorem B1862211 : Blo 1861632 1862211 := bstep (se 1 (by rfl) ⟨1396658, by rfl⟩ : syracuseStep 1862211 = 2793317) B2793317
theorem B1862227 : Blo 1861632 1862227 := bstep (se 1 (by rfl) ⟨1396670, by rfl⟩ : syracuseStep 1862227 = 2793341) B2793341
theorem B5302883 : Blo 1861632 5302883 := bstep (se 1 (by rfl) ⟨3977162, by rfl⟩ : syracuseStep 5302883 = 7954325) B7954325
theorem B1862243 : Blo 1861632 1862243 := bstep (se 1 (by rfl) ⟨1396682, by rfl⟩ : syracuseStep 1862243 = 2793365) B2793365
theorem B6285923 : Blo 1861632 6285923 := bstep (se 1 (by rfl) ⟨4714442, by rfl⟩ : syracuseStep 6285923 = 9428885) B9428885
theorem B1862259 : Blo 1861632 1862259 := bstep (se 1 (by rfl) ⟨1396694, by rfl⟩ : syracuseStep 1862259 = 2793389) B2793389
theorem B1862275 : Blo 1861632 1862275 := bstep (se 1 (by rfl) ⟨1396706, by rfl⟩ : syracuseStep 1862275 = 2793413) B2793413
theorem B1862291 : Blo 1861632 1862291 := bstep (se 1 (by rfl) ⟨1396718, by rfl⟩ : syracuseStep 1862291 = 2793437) B2793437
theorem B1862307 : Blo 1861632 1862307 := bstep (se 1 (by rfl) ⟨1396730, by rfl⟩ : syracuseStep 1862307 = 2793461) B2793461
theorem B4713137 : Blo 1861632 4713137 := bstep (se 2 (by rfl) ⟨1767426, by rfl⟩ : syracuseStep 4713137 = 3534853) B3534853
theorem B5966513 : Blo 1861632 5966513 := bstep (se 2 (by rfl) ⟨2237442, by rfl⟩ : syracuseStep 5966513 = 4474885) B4474885
theorem B1862323 : Blo 1861632 1862323 := bstep (se 1 (by rfl) ⟨1396742, by rfl⟩ : syracuseStep 1862323 = 2793485) B2793485
theorem B1862339 : Blo 1861632 1862339 := bstep (se 1 (by rfl) ⟨1396754, by rfl⟩ : syracuseStep 1862339 = 2793509) B2793509
theorem B1862355 : Blo 1861632 1862355 := bstep (se 1 (by rfl) ⟨1396766, by rfl⟩ : syracuseStep 1862355 = 2793533) B2793533
theorem B4713187 : Blo 1861632 4713187 := bstep (se 1 (by rfl) ⟨3534890, by rfl⟩ : syracuseStep 4713187 = 7069781) B7069781
theorem B1862371 : Blo 1861632 1862371 := bstep (se 1 (by rfl) ⟨1396778, by rfl⟩ : syracuseStep 1862371 = 2793557) B2793557
theorem B1862387 : Blo 1861632 1862387 := bstep (se 1 (by rfl) ⟨1396790, by rfl⟩ : syracuseStep 1862387 = 2793581) B2793581
theorem B2984705 : Blo 1861632 2984705 := bstep (se 2 (by rfl) ⟨1119264, by rfl⟩ : syracuseStep 2984705 = 2238529) B2238529
theorem B1862403 : Blo 1861632 1862403 := bstep (se 1 (by rfl) ⟨1396802, by rfl⟩ : syracuseStep 1862403 = 2793605) B2793605
theorem B1862419 : Blo 1861632 1862419 := bstep (se 1 (by rfl) ⟨1396814, by rfl⟩ : syracuseStep 1862419 = 2793629) B2793629
theorem B1862435 : Blo 1861632 1862435 := bstep (se 1 (by rfl) ⟨1396826, by rfl⟩ : syracuseStep 1862435 = 2793653) B2793653
theorem B4188977 : Blo 1861632 4188977 := bstep (se 2 (by rfl) ⟨1570866, by rfl⟩ : syracuseStep 4188977 = 3141733) B3141733
theorem B1862451 : Blo 1861632 1862451 := bstep (se 1 (by rfl) ⟨1396838, by rfl⟩ : syracuseStep 1862451 = 2793677) B2793677
theorem B4188995 : Blo 1861632 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B1862467 : Blo 1861632 1862467 := bstep (se 1 (by rfl) ⟨1396850, by rfl⟩ : syracuseStep 1862467 = 2793701) B2793701
theorem B1862483 : Blo 1861632 1862483 := bstep (se 1 (by rfl) ⟨1396862, by rfl⟩ : syracuseStep 1862483 = 2793725) B2793725
theorem B1862499 : Blo 1861632 1862499 := bstep (se 1 (by rfl) ⟨1396874, by rfl⟩ : syracuseStep 1862499 = 2793749) B2793749
theorem B4713329 : Blo 1861632 4713329 := bstep (se 2 (by rfl) ⟨1767498, by rfl⟩ : syracuseStep 4713329 = 3534997) B3534997
theorem B6286193 : Blo 1861632 6286193 := bstep (se 2 (by rfl) ⟨2357322, by rfl⟩ : syracuseStep 6286193 = 4714645) B4714645
theorem B1862515 : Blo 1861632 1862515 := bstep (se 1 (by rfl) ⟨1396886, by rfl⟩ : syracuseStep 1862515 = 2793773) B2793773
theorem B1862531 : Blo 1861632 1862531 := bstep (se 1 (by rfl) ⟨1396898, by rfl⟩ : syracuseStep 1862531 = 2793797) B2793797
theorem B1862547 : Blo 1861632 1862547 := bstep (se 1 (by rfl) ⟨1396910, by rfl⟩ : syracuseStep 1862547 = 2793821) B2793821
theorem B1862563 : Blo 1861632 1862563 := bstep (se 1 (by rfl) ⟨1396922, by rfl⟩ : syracuseStep 1862563 = 2793845) B2793845
theorem B1862579 : Blo 1861632 1862579 := bstep (se 1 (by rfl) ⟨1396934, by rfl⟩ : syracuseStep 1862579 = 2793869) B2793869
theorem B2984897 : Blo 1861632 2984897 := bstep (se 2 (by rfl) ⟨1119336, by rfl⟩ : syracuseStep 2984897 = 2238673) B2238673
theorem B1862595 : Blo 1861632 1862595 := bstep (se 1 (by rfl) ⟨1396946, by rfl⟩ : syracuseStep 1862595 = 2793893) B2793893
theorem B11938765 : Blo 1861632 11938765 := bstep (se 3 (by rfl) ⟨2238518, by rfl⟩ : syracuseStep 11938765 = 4477037) B4477037
theorem B1862611 : Blo 1861632 1862611 := bstep (se 1 (by rfl) ⟨1396958, by rfl⟩ : syracuseStep 1862611 = 2793917) B2793917
theorem B1862627 : Blo 1861632 1862627 := bstep (se 1 (by rfl) ⟨1396970, by rfl⟩ : syracuseStep 1862627 = 2793941) B2793941
theorem B1862643 : Blo 1861632 1862643 := bstep (se 1 (by rfl) ⟨1396982, by rfl⟩ : syracuseStep 1862643 = 2793965) B2793965
theorem B4779011 : Blo 1861632 4779011 := bstep (se 1 (by rfl) ⟨3584258, by rfl⟩ : syracuseStep 4779011 = 7168517) B7168517
theorem B1862659 : Blo 1861632 1862659 := bstep (se 1 (by rfl) ⟨1396994, by rfl⟩ : syracuseStep 1862659 = 2793989) B2793989
theorem B1862675 : Blo 1861632 1862675 := bstep (se 1 (by rfl) ⟨1397006, by rfl⟩ : syracuseStep 1862675 = 2794013) B2794013
theorem B1862691 : Blo 1861632 1862691 := bstep (se 1 (by rfl) ⟨1397018, by rfl⟩ : syracuseStep 1862691 = 2794037) B2794037
theorem B1862707 : Blo 1861632 1862707 := bstep (se 1 (by rfl) ⟨1397030, by rfl⟩ : syracuseStep 1862707 = 2794061) B2794061
theorem B2985025 : Blo 1861632 2985025 := bstep (se 2 (by rfl) ⟨1119384, by rfl⟩ : syracuseStep 2985025 = 2238769) B2238769
theorem B1862723 : Blo 1861632 1862723 := bstep (se 1 (by rfl) ⟨1397042, by rfl⟩ : syracuseStep 1862723 = 2794085) B2794085
theorem B4189265 : Blo 1861632 4189265 := bstep (se 2 (by rfl) ⟨1570974, by rfl⟩ : syracuseStep 4189265 = 3141949) B3141949
theorem B1862739 : Blo 1861632 1862739 := bstep (se 1 (by rfl) ⟨1397054, by rfl⟩ : syracuseStep 1862739 = 2794109) B2794109
theorem B4189283 : Blo 1861632 4189283 := bstep (se 1 (by rfl) ⟨3141962, by rfl⟩ : syracuseStep 4189283 = 6283925) B6283925
theorem B1862755 : Blo 1861632 1862755 := bstep (se 1 (by rfl) ⟨1397066, by rfl⟩ : syracuseStep 1862755 = 2794133) B2794133
theorem B17902691 : Blo 1861632 17902691 := bstep (se 1 (by rfl) ⟨13427018, by rfl⟩ : syracuseStep 17902691 = 26854037) B26854037
theorem B23874659 : Blo 1861632 23874659 := bstep (se 1 (by rfl) ⟨17905994, by rfl⟩ : syracuseStep 23874659 = 35811989) B35811989
theorem B1862771 : Blo 1861632 1862771 := bstep (se 1 (by rfl) ⟨1397078, by rfl⟩ : syracuseStep 1862771 = 2794157) B2794157
theorem B1862787 : Blo 1861632 1862787 := bstep (se 1 (by rfl) ⟨1397090, by rfl⟩ : syracuseStep 1862787 = 2794181) B2794181
theorem B1862803 : Blo 1861632 1862803 := bstep (se 1 (by rfl) ⟨1397102, by rfl⟩ : syracuseStep 1862803 = 2794205) B2794205
theorem B1862819 : Blo 1861632 1862819 := bstep (se 1 (by rfl) ⟨1397114, by rfl⟩ : syracuseStep 1862819 = 2794229) B2794229
theorem B1862835 : Blo 1861632 1862835 := bstep (se 1 (by rfl) ⟨1397126, by rfl⟩ : syracuseStep 1862835 = 2794253) B2794253
theorem B1862851 : Blo 1861632 1862851 := bstep (se 1 (by rfl) ⟨1397138, by rfl⟩ : syracuseStep 1862851 = 2794277) B2794277
theorem B13429957 : Blo 1861632 13429957 := bstep (se 4 (by rfl) ⟨1259058, by rfl⟩ : syracuseStep 13429957 = 2518117) B2518117
theorem B7957709 : Blo 1861632 7957709 := bstep (se 3 (by rfl) ⟨1492070, by rfl⟩ : syracuseStep 7957709 = 2984141) B2984141
theorem B10611917 : Blo 1861632 10611917 := bstep (se 3 (by rfl) ⟨1989734, by rfl⟩ : syracuseStep 10611917 = 3979469) B3979469
theorem B1862867 : Blo 1861632 1862867 := bstep (se 1 (by rfl) ⟨1397150, by rfl⟩ : syracuseStep 1862867 = 2794301) B2794301
theorem B1862883 : Blo 1861632 1862883 := bstep (se 1 (by rfl) ⟨1397162, by rfl⟩ : syracuseStep 1862883 = 2794325) B2794325
theorem B45321443 : Blo 1861632 45321443 := bstep (se 1 (by rfl) ⟨33991082, by rfl⟩ : syracuseStep 45321443 = 67982165) B67982165
theorem B1862899 : Blo 1861632 1862899 := bstep (se 1 (by rfl) ⟨1397174, by rfl⟩ : syracuseStep 1862899 = 2794349) B2794349
theorem B1862915 : Blo 1861632 1862915 := bstep (se 1 (by rfl) ⟨1397186, by rfl⟩ : syracuseStep 1862915 = 2794373) B2794373
theorem B1862931 : Blo 1861632 1862931 := bstep (se 1 (by rfl) ⟨1397198, by rfl⟩ : syracuseStep 1862931 = 2794397) B2794397
theorem B1862947 : Blo 1861632 1862947 := bstep (se 1 (by rfl) ⟨1397210, by rfl⟩ : syracuseStep 1862947 = 2794421) B2794421
theorem B8064305 : Blo 1861632 8064305 := bstep (se 2 (by rfl) ⟨3024114, by rfl⟩ : syracuseStep 8064305 = 6048229) B6048229
theorem B1862963 : Blo 1861632 1862963 := bstep (se 1 (by rfl) ⟨1397222, by rfl⟩ : syracuseStep 1862963 = 2794445) B2794445
theorem B1862979 : Blo 1861632 1862979 := bstep (se 1 (by rfl) ⟨1397234, by rfl⟩ : syracuseStep 1862979 = 2794469) B2794469
theorem B1862995 : Blo 1861632 1862995 := bstep (se 1 (by rfl) ⟨1397246, by rfl⟩ : syracuseStep 1862995 = 2794493) B2794493
theorem B1863011 : Blo 1861632 1863011 := bstep (se 1 (by rfl) ⟨1397258, by rfl⟩ : syracuseStep 1863011 = 2794517) B2794517
theorem B4189553 : Blo 1861632 4189553 := bstep (se 2 (by rfl) ⟨1571082, by rfl⟩ : syracuseStep 4189553 = 3142165) B3142165
theorem B1863027 : Blo 1861632 1863027 := bstep (se 1 (by rfl) ⟨1397270, by rfl⟩ : syracuseStep 1863027 = 2794541) B2794541
theorem B4189571 : Blo 1861632 4189571 := bstep (se 1 (by rfl) ⟨3142178, by rfl⟩ : syracuseStep 4189571 = 6284357) B6284357
theorem B4246915 : Blo 1861632 4246915 := bstep (se 1 (by rfl) ⟨3185186, by rfl⟩ : syracuseStep 4246915 = 6370373) B6370373
theorem B1863043 : Blo 1861632 1863043 := bstep (se 1 (by rfl) ⟨1397282, by rfl⟩ : syracuseStep 1863043 = 2794565) B2794565
theorem B6286733 : Blo 1861632 6286733 := bstep (se 3 (by rfl) ⟨1178762, by rfl⟩ : syracuseStep 6286733 = 2357525) B2357525
theorem B1863059 : Blo 1861632 1863059 := bstep (se 1 (by rfl) ⟨1397294, by rfl⟩ : syracuseStep 1863059 = 2794589) B2794589
theorem B1863075 : Blo 1861632 1863075 := bstep (se 1 (by rfl) ⟨1397306, by rfl⟩ : syracuseStep 1863075 = 2794613) B2794613
theorem B1863091 : Blo 1861632 1863091 := bstep (se 1 (by rfl) ⟨1397318, by rfl⟩ : syracuseStep 1863091 = 2794637) B2794637
theorem B6286787 : Blo 1861632 6286787 := bstep (se 1 (by rfl) ⟨4715090, by rfl⟩ : syracuseStep 6286787 = 9430181) B9430181
theorem B1863107 : Blo 1861632 1863107 := bstep (se 1 (by rfl) ⟨1397330, by rfl⟩ : syracuseStep 1863107 = 2794661) B2794661
theorem B11931077 : Blo 1861632 11931077 := bstep (se 4 (by rfl) ⟨1118538, by rfl⟩ : syracuseStep 11931077 = 2237077) B2237077
theorem B1863123 : Blo 1861632 1863123 := bstep (se 1 (by rfl) ⟨1397342, by rfl⟩ : syracuseStep 1863123 = 2794685) B2794685
theorem B1863139 : Blo 1861632 1863139 := bstep (se 1 (by rfl) ⟨1397354, by rfl⟩ : syracuseStep 1863139 = 2794709) B2794709
theorem B1863155 : Blo 1861632 1863155 := bstep (se 1 (by rfl) ⟨1397366, by rfl⟩ : syracuseStep 1863155 = 2794733) B2794733
theorem B1863171 : Blo 1861632 1863171 := bstep (se 1 (by rfl) ⟨1397378, by rfl⟩ : syracuseStep 1863171 = 2794757) B2794757
theorem B19107341 : Blo 1861632 19107341 := bstep (se 3 (by rfl) ⟨3582626, by rfl⟩ : syracuseStep 19107341 = 7165253) B7165253
theorem B1863187 : Blo 1861632 1863187 := bstep (se 1 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 1863187 = 2794781) B2794781
theorem B1863203 : Blo 1861632 1863203 := bstep (se 1 (by rfl) ⟨1397402, by rfl⟩ : syracuseStep 1863203 = 2794805) B2794805
theorem B9432611 : Blo 1861632 9432611 := bstep (se 1 (by rfl) ⟨7074458, by rfl⟩ : syracuseStep 9432611 = 14148917) B14148917
theorem B3681841 : Blo 1861632 3681841 := bstep (se 2 (by rfl) ⟨1380690, by rfl⟩ : syracuseStep 3681841 = 2761381) B2761381
theorem B5664305 : Blo 1861632 5664305 := bstep (se 2 (by rfl) ⟨2124114, by rfl⟩ : syracuseStep 5664305 = 4248229) B4248229
theorem B1863219 : Blo 1861632 1863219 := bstep (se 1 (by rfl) ⟨1397414, by rfl⟩ : syracuseStep 1863219 = 2794829) B2794829
theorem B1863235 : Blo 1861632 1863235 := bstep (se 1 (by rfl) ⟨1397426, by rfl⟩ : syracuseStep 1863235 = 2794853) B2794853
theorem B1863251 : Blo 1861632 1863251 := bstep (se 1 (by rfl) ⟨1397438, by rfl⟩ : syracuseStep 1863251 = 2794877) B2794877
theorem B1863267 : Blo 1861632 1863267 := bstep (se 1 (by rfl) ⟨1397450, by rfl⟩ : syracuseStep 1863267 = 2794901) B2794901
theorem B1863283 : Blo 1861632 1863283 := bstep (se 1 (by rfl) ⟨1397462, by rfl⟩ : syracuseStep 1863283 = 2794925) B2794925
theorem B1863299 : Blo 1861632 1863299 := bstep (se 1 (by rfl) ⟨1397474, by rfl⟩ : syracuseStep 1863299 = 2794949) B2794949
theorem B4189841 : Blo 1861632 4189841 := bstep (se 2 (by rfl) ⟨1571190, by rfl⟩ : syracuseStep 4189841 = 3142381) B3142381
theorem B1863315 : Blo 1861632 1863315 := bstep (se 1 (by rfl) ⟨1397486, by rfl⟩ : syracuseStep 1863315 = 2794973) B2794973
theorem B10604195 : Blo 1861632 10604195 := bstep (se 1 (by rfl) ⟨7953146, by rfl⟩ : syracuseStep 10604195 = 15906293) B15906293
theorem B4189859 : Blo 1861632 4189859 := bstep (se 1 (by rfl) ⟨3142394, by rfl⟩ : syracuseStep 4189859 = 6284789) B6284789
theorem B1863331 : Blo 1861632 1863331 := bstep (se 1 (by rfl) ⟨1397498, by rfl⟩ : syracuseStep 1863331 = 2794997) B2794997
theorem B1863347 : Blo 1861632 1863347 := bstep (se 1 (by rfl) ⟨1397510, by rfl⟩ : syracuseStep 1863347 = 2795021) B2795021
theorem B1863363 : Blo 1861632 1863363 := bstep (se 1 (by rfl) ⟨1397522, by rfl⟩ : syracuseStep 1863363 = 2795045) B2795045
theorem B2518723 : Blo 1861632 2518723 := bstep (se 1 (by rfl) ⟨1889042, by rfl⟩ : syracuseStep 2518723 = 3778085) B3778085
theorem B17231557 : Blo 1861632 17231557 := bstep (se 4 (by rfl) ⟨1615458, by rfl⟩ : syracuseStep 17231557 = 3230917) B3230917
theorem B6287057 : Blo 1861632 6287057 := bstep (se 2 (by rfl) ⟨2357646, by rfl⟩ : syracuseStep 6287057 = 4715293) B4715293
theorem B1863379 : Blo 1861632 1863379 := bstep (se 1 (by rfl) ⟨1397534, by rfl⟩ : syracuseStep 1863379 = 2795069) B2795069
theorem B7548643 : Blo 1861632 7548643 := bstep (se 1 (by rfl) ⟨5661482, by rfl⟩ : syracuseStep 7548643 = 11322965) B11322965
theorem B1863395 : Blo 1861632 1863395 := bstep (se 1 (by rfl) ⟨1397546, by rfl⟩ : syracuseStep 1863395 = 2795093) B2795093
theorem B1863411 : Blo 1861632 1863411 := bstep (se 1 (by rfl) ⟨1397558, by rfl⟩ : syracuseStep 1863411 = 2795117) B2795117
theorem B1863427 : Blo 1861632 1863427 := bstep (se 1 (by rfl) ⟨1397570, by rfl⟩ : syracuseStep 1863427 = 2795141) B2795141
theorem B1863443 : Blo 1861632 1863443 := bstep (se 1 (by rfl) ⟨1397582, by rfl⟩ : syracuseStep 1863443 = 2795165) B2795165
theorem B1863459 : Blo 1861632 1863459 := bstep (se 1 (by rfl) ⟨1397594, by rfl⟩ : syracuseStep 1863459 = 2795189) B2795189
theorem B3977009 : Blo 1861632 3977009 := bstep (se 2 (by rfl) ⟨1491378, by rfl⟩ : syracuseStep 3977009 = 2982757) B2982757
theorem B5304113 : Blo 1861632 5304113 := bstep (se 2 (by rfl) ⟨1989042, by rfl⟩ : syracuseStep 5304113 = 3978085) B3978085
theorem B4476721 : Blo 1861632 4476721 := bstep (se 2 (by rfl) ⟨1678770, by rfl⟩ : syracuseStep 4476721 = 3357541) B3357541
theorem B1863475 : Blo 1861632 1863475 := bstep (se 1 (by rfl) ⟨1397606, by rfl⟩ : syracuseStep 1863475 = 2795213) B2795213
theorem B1863491 : Blo 1861632 1863491 := bstep (se 1 (by rfl) ⟨1397618, by rfl⟩ : syracuseStep 1863491 = 2795237) B2795237
theorem B21221189 : Blo 1861632 21221189 := bstep (se 4 (by rfl) ⟨1989486, by rfl⟩ : syracuseStep 21221189 = 3978973) B3978973
theorem B4714321 : Blo 1861632 4714321 := bstep (se 2 (by rfl) ⟨1767870, by rfl⟩ : syracuseStep 4714321 = 3535741) B3535741
theorem B1863507 : Blo 1861632 1863507 := bstep (se 1 (by rfl) ⟨1397630, by rfl⟩ : syracuseStep 1863507 = 2795261) B2795261
theorem B1863523 : Blo 1861632 1863523 := bstep (se 1 (by rfl) ⟨1397642, by rfl⟩ : syracuseStep 1863523 = 2795285) B2795285
theorem B1863539 : Blo 1861632 1863539 := bstep (se 1 (by rfl) ⟨1397654, by rfl⟩ : syracuseStep 1863539 = 2795309) B2795309
theorem B4534147 : Blo 1861632 4534147 := bstep (se 1 (by rfl) ⟨3400610, by rfl⟩ : syracuseStep 4534147 = 6801221) B6801221
theorem B1863555 : Blo 1861632 1863555 := bstep (se 1 (by rfl) ⟨1397666, by rfl⟩ : syracuseStep 1863555 = 2795333) B2795333
theorem B1863571 : Blo 1861632 1863571 := bstep (se 1 (by rfl) ⟨1397678, by rfl⟩ : syracuseStep 1863571 = 2795357) B2795357
theorem B1863587 : Blo 1861632 1863587 := bstep (se 1 (by rfl) ⟨1397690, by rfl⟩ : syracuseStep 1863587 = 2795381) B2795381
theorem B3534769 : Blo 1861632 3534769 := bstep (se 2 (by rfl) ⟨1325538, by rfl⟩ : syracuseStep 3534769 = 2651077) B2651077
theorem B4190129 : Blo 1861632 4190129 := bstep (se 2 (by rfl) ⟨1571298, by rfl⟩ : syracuseStep 4190129 = 3142597) B3142597
theorem B1863603 : Blo 1861632 1863603 := bstep (se 1 (by rfl) ⟨1397702, by rfl⟩ : syracuseStep 1863603 = 2795405) B2795405
theorem B3141571 : Blo 1861632 3141571 := bstep (se 1 (by rfl) ⟨2356178, by rfl⟩ : syracuseStep 3141571 = 4712357) B4712357
theorem B4190147 : Blo 1861632 4190147 := bstep (se 1 (by rfl) ⟨3142610, by rfl⟩ : syracuseStep 4190147 = 6285221) B6285221
theorem B1863619 : Blo 1861632 1863619 := bstep (se 1 (by rfl) ⟨1397714, by rfl⟩ : syracuseStep 1863619 = 2795429) B2795429
theorem B3141713 : Blo 1861632 3141713 := bstep (se 2 (by rfl) ⟨1178142, by rfl⟩ : syracuseStep 3141713 = 2356285) B2356285
theorem B4714595 : Blo 1861632 4714595 := bstep (se 1 (by rfl) ⟨3535946, by rfl⟩ : syracuseStep 4714595 = 7071893) B7071893
theorem B8949923 : Blo 1861632 8949923 := bstep (se 1 (by rfl) ⟨6712442, by rfl⟩ : syracuseStep 8949923 = 13424885) B13424885
theorem B3141841 : Blo 1861632 3141841 := bstep (se 2 (by rfl) ⟨1178190, by rfl⟩ : syracuseStep 3141841 = 2356381) B2356381
theorem B4190417 : Blo 1861632 4190417 := bstep (se 2 (by rfl) ⟨1571406, by rfl⟩ : syracuseStep 4190417 = 3142813) B3142813
theorem B4190435 : Blo 1861632 4190435 := bstep (se 1 (by rfl) ⟨3142826, by rfl⟩ : syracuseStep 4190435 = 6285653) B6285653
theorem B6287597 : Blo 1861632 6287597 := bstep (se 3 (by rfl) ⟨1178924, by rfl⟩ : syracuseStep 6287597 = 2357849) B2357849
theorem B3141875 : Blo 1861632 3141875 := bstep (se 1 (by rfl) ⟨2356406, by rfl⟩ : syracuseStep 3141875 = 4712813) B4712813
theorem B4714787 : Blo 1861632 4714787 := bstep (se 1 (by rfl) ⟨3536090, by rfl⟩ : syracuseStep 4714787 = 7072181) B7072181
theorem B6287651 : Blo 1861632 6287651 := bstep (se 1 (by rfl) ⟨4715738, by rfl⟩ : syracuseStep 6287651 = 9431477) B9431477
theorem B5968205 : Blo 1861632 5968205 := bstep (se 3 (by rfl) ⟨1119038, by rfl⟩ : syracuseStep 5968205 = 2238077) B2238077
theorem B7074125 : Blo 1861632 7074125 := bstep (se 3 (by rfl) ⟨1326398, by rfl⟩ : syracuseStep 7074125 = 2652797) B2652797
theorem B9433421 : Blo 1861632 9433421 := bstep (se 3 (by rfl) ⟨1768766, by rfl⟩ : syracuseStep 9433421 = 3537533) B3537533
theorem B8950115 : Blo 1861632 8950115 := bstep (se 1 (by rfl) ⟨6712586, by rfl⟩ : syracuseStep 8950115 = 13425173) B13425173
theorem B3142003 : Blo 1861632 3142003 := bstep (se 1 (by rfl) ⟨2356502, by rfl⟩ : syracuseStep 3142003 = 4713005) B4713005
theorem B6713741 : Blo 1861632 6713741 := bstep (se 3 (by rfl) ⟨1258826, by rfl⟩ : syracuseStep 6713741 = 2517653) B2517653
theorem B3355025 : Blo 1861632 3355025 := bstep (se 2 (by rfl) ⟨1258134, by rfl⟩ : syracuseStep 3355025 = 2516269) B2516269
theorem B11481571 : Blo 1861632 11481571 := bstep (se 1 (by rfl) ⟨8611178, by rfl⟩ : syracuseStep 11481571 = 17222357) B17222357
theorem B4190705 : Blo 1861632 4190705 := bstep (se 2 (by rfl) ⟨1571514, by rfl⟩ : syracuseStep 4190705 = 3143029) B3143029
theorem B3142145 : Blo 1861632 3142145 := bstep (se 2 (by rfl) ⟨1178304, by rfl⟩ : syracuseStep 3142145 = 2356609) B2356609
theorem B4190723 : Blo 1861632 4190723 := bstep (se 1 (by rfl) ⟨3143042, by rfl⟩ : syracuseStep 4190723 = 6286085) B6286085
theorem B6287921 : Blo 1861632 6287921 := bstep (se 2 (by rfl) ⟨2357970, by rfl⟩ : syracuseStep 6287921 = 4715941) B4715941
theorem B5739121 : Blo 1861632 5739121 := bstep (se 2 (by rfl) ⟨2152170, by rfl⟩ : syracuseStep 5739121 = 4304341) B4304341
theorem B3142273 : Blo 1861632 3142273 := bstep (se 2 (by rfl) ⟨1178352, by rfl⟩ : syracuseStep 3142273 = 2356705) B2356705
theorem B6460049 : Blo 1861632 6460049 := bstep (se 2 (by rfl) ⟨2422518, by rfl⟩ : syracuseStep 6460049 = 4845037) B4845037
theorem B3142307 : Blo 1861632 3142307 := bstep (se 1 (by rfl) ⟨2356730, by rfl⟩ : syracuseStep 3142307 = 4713461) B4713461
theorem B4190993 : Blo 1861632 4190993 := bstep (se 2 (by rfl) ⟨1571622, by rfl⟩ : syracuseStep 4190993 = 3143245) B3143245
theorem B3142435 : Blo 1861632 3142435 := bstep (se 1 (by rfl) ⟨2356826, by rfl⟩ : syracuseStep 3142435 = 4713653) B4713653
theorem B4191011 : Blo 1861632 4191011 := bstep (se 1 (by rfl) ⟨3143258, by rfl⟩ : syracuseStep 4191011 = 6286517) B6286517
theorem B21517109 : Blo 1861632 21517109 := bstep (se 5 (by rfl) ⟨1008614, by rfl⟩ : syracuseStep 21517109 = 2017229) B2017229
theorem B2650963 : Blo 1861632 2650963 := bstep (se 1 (by rfl) ⟨1988222, by rfl⟩ : syracuseStep 2650963 = 3976445) B3976445
theorem B3142577 : Blo 1861632 3142577 := bstep (se 2 (by rfl) ⟨1178466, by rfl⟩ : syracuseStep 3142577 = 2356933) B2356933
theorem B3535825 : Blo 1861632 3535825 := bstep (se 2 (by rfl) ⟨1325934, by rfl⟩ : syracuseStep 3535825 = 2651869) B2651869
theorem B12915683 : Blo 1861632 12915683 := bstep (se 1 (by rfl) ⟨9686762, by rfl⟩ : syracuseStep 12915683 = 19373525) B19373525
theorem B8950769 : Blo 1861632 8950769 := bstep (se 2 (by rfl) ⟨3356538, by rfl⟩ : syracuseStep 8950769 = 6713077) B6713077
theorem B6370321 : Blo 1861632 6370321 := bstep (se 2 (by rfl) ⟨2388870, by rfl⟩ : syracuseStep 6370321 = 4777741) B4777741
theorem B9425969 : Blo 1861632 9425969 := bstep (se 2 (by rfl) ⟨3534738, by rfl⟩ : syracuseStep 9425969 = 7069477) B7069477
theorem B3142705 : Blo 1861632 3142705 := bstep (se 2 (by rfl) ⟨1178514, by rfl⟩ : syracuseStep 3142705 = 2357029) B2357029
theorem B4191281 : Blo 1861632 4191281 := bstep (se 2 (by rfl) ⟨1571730, by rfl⟩ : syracuseStep 4191281 = 3143461) B3143461
theorem B4191299 : Blo 1861632 4191299 := bstep (se 1 (by rfl) ⟨3143474, by rfl⟩ : syracuseStep 4191299 = 6286949) B6286949
theorem B5968973 : Blo 1861632 5968973 := bstep (se 3 (by rfl) ⟨1119182, by rfl⟩ : syracuseStep 5968973 = 2238365) B2238365
theorem B6288461 : Blo 1861632 6288461 := bstep (se 3 (by rfl) ⟨1179086, by rfl⟩ : syracuseStep 6288461 = 2358173) B2358173
theorem B3142739 : Blo 1861632 3142739 := bstep (se 1 (by rfl) ⟨2357054, by rfl⟩ : syracuseStep 3142739 = 4714109) B4714109
theorem B6288515 : Blo 1861632 6288515 := bstep (se 1 (by rfl) ⟨4716386, by rfl⟩ : syracuseStep 6288515 = 9432773) B9432773
theorem B4715729 : Blo 1861632 4715729 := bstep (se 2 (by rfl) ⟨1768398, by rfl⟩ : syracuseStep 4715729 = 3536797) B3536797
theorem B3142867 : Blo 1861632 3142867 := bstep (se 1 (by rfl) ⟨2357150, by rfl⟩ : syracuseStep 3142867 = 4714301) B4714301
theorem B5305571 : Blo 1861632 5305571 := bstep (se 1 (by rfl) ⟨3979178, by rfl⟩ : syracuseStep 5305571 = 7958357) B7958357
theorem B10073315 : Blo 1861632 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B2831617 : Blo 1861632 2831617 := bstep (se 2 (by rfl) ⟨1061856, by rfl⟩ : syracuseStep 2831617 = 2123713) B2123713
theorem B4715779 : Blo 1861632 4715779 := bstep (se 1 (by rfl) ⟨3536834, by rfl⟩ : syracuseStep 4715779 = 7073669) B7073669
theorem B20133173 : Blo 1861632 20133173 := bstep (se 5 (by rfl) ⟨943742, by rfl⟩ : syracuseStep 20133173 = 1887485) B1887485
theorem B2094403 : Blo 1861632 2094403 := bstep (se 1 (by rfl) ⟨1570802, by rfl⟩ : syracuseStep 2094403 = 3141605) B3141605
theorem B3978563 : Blo 1861632 3978563 := bstep (se 1 (by rfl) ⟨2983922, by rfl⟩ : syracuseStep 3978563 = 5967845) B5967845
theorem B4191569 : Blo 1861632 4191569 := bstep (se 2 (by rfl) ⟨1571838, by rfl⟩ : syracuseStep 4191569 = 3143677) B3143677
theorem B3143009 : Blo 1861632 3143009 := bstep (se 2 (by rfl) ⟨1178628, by rfl⟩ : syracuseStep 3143009 = 2357257) B2357257
theorem B3536227 : Blo 1861632 3536227 := bstep (se 1 (by rfl) ⟨2652170, by rfl⟩ : syracuseStep 3536227 = 5304341) B5304341
theorem B4191587 : Blo 1861632 4191587 := bstep (se 1 (by rfl) ⟨3143690, by rfl⟩ : syracuseStep 4191587 = 6287381) B6287381
theorem B10065293 : Blo 1861632 10065293 := bstep (se 3 (by rfl) ⟨1887242, by rfl⟩ : syracuseStep 10065293 = 3774485) B3774485
theorem B3536273 : Blo 1861632 3536273 := bstep (se 2 (by rfl) ⟨1326102, by rfl⟩ : syracuseStep 3536273 = 2652205) B2652205
theorem B4715921 : Blo 1861632 4715921 := bstep (se 2 (by rfl) ⟨1768470, by rfl⟩ : syracuseStep 4715921 = 3536941) B3536941
theorem B6288785 : Blo 1861632 6288785 := bstep (se 2 (by rfl) ⟨2358294, by rfl⟩ : syracuseStep 6288785 = 4716589) B4716589
theorem B36304325 : Blo 1861632 36304325 := bstep (se 4 (by rfl) ⟨3403530, by rfl⟩ : syracuseStep 36304325 = 6807061) B6807061
theorem B2094547 : Blo 1861632 2094547 := bstep (se 1 (by rfl) ⟨1570910, by rfl⟩ : syracuseStep 2094547 = 3141821) B3141821
theorem B3143137 : Blo 1861632 3143137 := bstep (se 2 (by rfl) ⟨1178676, by rfl⟩ : syracuseStep 3143137 = 2357353) B2357353
theorem B3143171 : Blo 1861632 3143171 := bstep (se 1 (by rfl) ⟨2357378, by rfl⟩ : syracuseStep 3143171 = 4714757) B4714757
theorem B10606085 : Blo 1861632 10606085 := bstep (se 4 (by rfl) ⟨994320, by rfl⟩ : syracuseStep 10606085 = 1988641) B1988641
theorem B3151379 : Blo 1861632 3151379 := bstep (se 1 (by rfl) ⟨2363534, by rfl⟩ : syracuseStep 3151379 = 4727069) B4727069
theorem B2356771 : Blo 1861632 2356771 := bstep (se 1 (by rfl) ⟨1767578, by rfl⟩ : syracuseStep 2356771 = 3535157) B3535157
theorem B5969485 : Blo 1861632 5969485 := bstep (se 3 (by rfl) ⟨1119278, by rfl⟩ : syracuseStep 5969485 = 2238557) B2238557
theorem B2094691 : Blo 1861632 2094691 := bstep (se 1 (by rfl) ⟨1571018, by rfl⟩ : syracuseStep 2094691 = 3142037) B3142037
theorem B5035619 : Blo 1861632 5035619 := bstep (se 1 (by rfl) ⟨3776714, by rfl⟩ : syracuseStep 5035619 = 7553429) B7553429
theorem B4191857 : Blo 1861632 4191857 := bstep (se 2 (by rfl) ⟨1571946, by rfl⟩ : syracuseStep 4191857 = 3143893) B3143893
theorem B2356867 : Blo 1861632 2356867 := bstep (se 1 (by rfl) ⟨1767650, by rfl⟩ : syracuseStep 2356867 = 3535301) B3535301
theorem B3143299 : Blo 1861632 3143299 := bstep (se 1 (by rfl) ⟨2357474, by rfl⟩ : syracuseStep 3143299 = 4714949) B4714949
theorem B4191875 : Blo 1861632 4191875 := bstep (se 1 (by rfl) ⟨3143906, by rfl⟩ : syracuseStep 4191875 = 6287813) B6287813
theorem B5740195 : Blo 1861632 5740195 := bstep (se 1 (by rfl) ⟨4305146, by rfl⟩ : syracuseStep 5740195 = 8610293) B8610293
theorem B3536561 : Blo 1861632 3536561 := bstep (se 2 (by rfl) ⟨1326210, by rfl⟩ : syracuseStep 3536561 = 2652421) B2652421
theorem B2094835 : Blo 1861632 2094835 := bstep (se 1 (by rfl) ⟨1571126, by rfl⟩ : syracuseStep 2094835 = 3142253) B3142253
theorem B3143441 : Blo 1861632 3143441 := bstep (se 2 (by rfl) ⟨1178790, by rfl⟩ : syracuseStep 3143441 = 2357581) B2357581
theorem B2094979 : Blo 1861632 2094979 := bstep (se 1 (by rfl) ⟨1571234, by rfl⟩ : syracuseStep 2094979 = 3142469) B3142469
theorem B3143569 : Blo 1861632 3143569 := bstep (se 2 (by rfl) ⟨1178838, by rfl⟩ : syracuseStep 3143569 = 2357677) B2357677
theorem B4192145 : Blo 1861632 4192145 := bstep (se 2 (by rfl) ⟨1572054, by rfl⟩ : syracuseStep 4192145 = 3144109) B3144109
theorem B4192163 : Blo 1861632 4192163 := bstep (se 1 (by rfl) ⟨3144122, by rfl⟩ : syracuseStep 4192163 = 6288245) B6288245
theorem B6289325 : Blo 1861632 6289325 := bstep (se 3 (by rfl) ⟨1179248, by rfl⟩ : syracuseStep 6289325 = 2358497) B2358497
theorem B3143603 : Blo 1861632 3143603 := bstep (se 1 (by rfl) ⟨2357702, by rfl⟩ : syracuseStep 3143603 = 4715405) B4715405
theorem B2652097 : Blo 1861632 2652097 := bstep (se 2 (by rfl) ⟨994536, by rfl⟩ : syracuseStep 2652097 = 1989073) B1989073
theorem B6289379 : Blo 1861632 6289379 := bstep (se 1 (by rfl) ⟨4717034, by rfl⟩ : syracuseStep 6289379 = 9434069) B9434069
theorem B5306381 : Blo 1861632 5306381 := bstep (se 3 (by rfl) ⟨994946, by rfl⟩ : syracuseStep 5306381 = 1989893) B1989893
theorem B2095123 : Blo 1861632 2095123 := bstep (se 1 (by rfl) ⟨1571342, by rfl⟩ : syracuseStep 2095123 = 3142685) B3142685
theorem B2652193 : Blo 1861632 2652193 := bstep (se 2 (by rfl) ⟨994572, by rfl⟩ : syracuseStep 2652193 = 1989145) B1989145
theorem B3143731 : Blo 1861632 3143731 := bstep (se 1 (by rfl) ⟨2357798, by rfl⟩ : syracuseStep 3143731 = 4715597) B4715597
theorem B5969987 : Blo 1861632 5969987 := bstep (se 1 (by rfl) ⟨4477490, by rfl⟩ : syracuseStep 5969987 = 8954981) B8954981
theorem B2357363 : Blo 1861632 2357363 := bstep (se 1 (by rfl) ⟨1768022, by rfl⟩ : syracuseStep 2357363 = 3536045) B3536045
theorem B2095267 : Blo 1861632 2095267 := bstep (se 1 (by rfl) ⟨1571450, by rfl⟩ : syracuseStep 2095267 = 3142901) B3142901
theorem B3356849 : Blo 1861632 3356849 := bstep (se 2 (by rfl) ⟨1258818, by rfl⟩ : syracuseStep 3356849 = 2517637) B2517637
theorem B4192433 : Blo 1861632 4192433 := bstep (se 2 (by rfl) ⟨1572162, by rfl⟩ : syracuseStep 4192433 = 3144325) B3144325
theorem B3143873 : Blo 1861632 3143873 := bstep (se 2 (by rfl) ⟨1178952, by rfl⟩ : syracuseStep 3143873 = 2357905) B2357905
theorem B4192451 : Blo 1861632 4192451 := bstep (se 1 (by rfl) ⟨3144338, by rfl⟩ : syracuseStep 4192451 = 6288677) B6288677
theorem B5306573 : Blo 1861632 5306573 := bstep (se 3 (by rfl) ⟨994982, by rfl⟩ : syracuseStep 5306573 = 1989965) B1989965
theorem B8493283 : Blo 1861632 8493283 := bstep (se 1 (by rfl) ⟨6369962, by rfl⟩ : syracuseStep 8493283 = 12739925) B12739925
theorem B6289649 : Blo 1861632 6289649 := bstep (se 2 (by rfl) ⟨2358618, by rfl⟩ : syracuseStep 6289649 = 4717237) B4717237
theorem B2095411 : Blo 1861632 2095411 := bstep (se 1 (by rfl) ⟨1571558, by rfl⟩ : syracuseStep 2095411 = 3143117) B3143117
theorem B3144001 : Blo 1861632 3144001 := bstep (se 2 (by rfl) ⟨1179000, by rfl⟩ : syracuseStep 3144001 = 2358001) B2358001
theorem B5036365 : Blo 1861632 5036365 := bstep (se 3 (by rfl) ⟨944318, by rfl⟩ : syracuseStep 5036365 = 1888637) B1888637
theorem B3144035 : Blo 1861632 3144035 := bstep (se 1 (by rfl) ⟨2358026, by rfl⟩ : syracuseStep 3144035 = 4716053) B4716053
theorem B4716913 : Blo 1861632 4716913 := bstep (se 2 (by rfl) ⟨1768842, by rfl⟩ : syracuseStep 4716913 = 3537685) B3537685
theorem B3537283 : Blo 1861632 3537283 := bstep (se 1 (by rfl) ⟨2652962, by rfl⟩ : syracuseStep 3537283 = 5305925) B5305925
theorem B2095555 : Blo 1861632 2095555 := bstep (se 1 (by rfl) ⟨1571666, by rfl⟩ : syracuseStep 2095555 = 3143333) B3143333
theorem B4192721 : Blo 1861632 4192721 := bstep (se 2 (by rfl) ⟨1572270, by rfl⟩ : syracuseStep 4192721 = 3144541) B3144541
theorem B9427427 : Blo 1861632 9427427 := bstep (se 1 (by rfl) ⟨7070570, by rfl⟩ : syracuseStep 9427427 = 14141141) B14141141
theorem B10754531 : Blo 1861632 10754531 := bstep (se 1 (by rfl) ⟨8065898, by rfl⟩ : syracuseStep 10754531 = 16131797) B16131797
theorem B3144163 : Blo 1861632 3144163 := bstep (se 1 (by rfl) ⟨2358122, by rfl⟩ : syracuseStep 3144163 = 4716245) B4716245
theorem B4192739 : Blo 1861632 4192739 := bstep (se 1 (by rfl) ⟨3144554, by rfl⟩ : syracuseStep 4192739 = 6289109) B6289109
theorem B2652689 : Blo 1861632 2652689 := bstep (se 2 (by rfl) ⟨994758, by rfl⟩ : syracuseStep 2652689 = 1989517) B1989517
theorem B12098117 : Blo 1861632 12098117 := bstep (se 4 (by rfl) ⟨1134198, by rfl⟩ : syracuseStep 12098117 = 2268397) B2268397
theorem B2095699 : Blo 1861632 2095699 := bstep (se 1 (by rfl) ⟨1571774, by rfl⟩ : syracuseStep 2095699 = 3143549) B3143549
theorem B3144305 : Blo 1861632 3144305 := bstep (se 2 (by rfl) ⟨1179114, by rfl⟩ : syracuseStep 3144305 = 2358229) B2358229
theorem B4717187 : Blo 1861632 4717187 := bstep (se 1 (by rfl) ⟨3537890, by rfl⟩ : syracuseStep 4717187 = 7075781) B7075781
theorem B1989299 : Blo 1861632 1989299 := bstep (se 1 (by rfl) ⟨1491974, by rfl⟩ : syracuseStep 1989299 = 2983949) B2983949
theorem B2095843 : Blo 1861632 2095843 := bstep (se 1 (by rfl) ⟨1571882, by rfl⟩ : syracuseStep 2095843 = 3143765) B3143765
theorem B3144433 : Blo 1861632 3144433 := bstep (se 2 (by rfl) ⟨1179162, by rfl⟩ : syracuseStep 3144433 = 2358325) B2358325
theorem B4193009 : Blo 1861632 4193009 := bstep (se 2 (by rfl) ⟨1572378, by rfl⟩ : syracuseStep 4193009 = 3144757) B3144757
theorem B4193027 : Blo 1861632 4193027 := bstep (se 1 (by rfl) ⟨3144770, by rfl⟩ : syracuseStep 4193027 = 6289541) B6289541
theorem B3144467 : Blo 1861632 3144467 := bstep (se 1 (by rfl) ⟨2358350, by rfl⟩ : syracuseStep 3144467 = 4716701) B4716701
theorem B2358067 : Blo 1861632 2358067 := bstep (se 1 (by rfl) ⟨1768550, by rfl⟩ : syracuseStep 2358067 = 3537101) B3537101
theorem B3537731 : Blo 1861632 3537731 := bstep (se 1 (by rfl) ⟨2653298, by rfl⟩ : syracuseStep 3537731 = 5306597) B5306597
theorem B14138225 : Blo 1861632 14138225 := bstep (se 2 (by rfl) ⟨5301834, by rfl⟩ : syracuseStep 14138225 = 10603669) B10603669
theorem B2095987 : Blo 1861632 2095987 := bstep (se 1 (by rfl) ⟨1571990, by rfl⟩ : syracuseStep 2095987 = 3143981) B3143981
theorem B2358163 : Blo 1861632 2358163 := bstep (se 1 (by rfl) ⟨1768622, by rfl⟩ : syracuseStep 2358163 = 3537245) B3537245
theorem B3144595 : Blo 1861632 3144595 := bstep (se 1 (by rfl) ⟨2358446, by rfl⟩ : syracuseStep 3144595 = 4716893) B4716893
theorem B11934641 : Blo 1861632 11934641 := bstep (se 2 (by rfl) ⟨4475490, by rfl⟩ : syracuseStep 11934641 = 8950981) B8950981
theorem B2096131 : Blo 1861632 2096131 := bstep (se 1 (by rfl) ⟨1572098, by rfl⟩ : syracuseStep 2096131 = 3144197) B3144197
theorem B2792465 : Blo 1861632 2792465 := bstep (se 2 (by rfl) ⟨1047174, by rfl⟩ : syracuseStep 2792465 = 2094349) B2094349
theorem B3144737 : Blo 1861632 3144737 := bstep (se 2 (by rfl) ⟨1179276, by rfl⟩ : syracuseStep 3144737 = 2358553) B2358553
theorem B2792483 : Blo 1861632 2792483 := bstep (se 1 (by rfl) ⟨2094362, by rfl⟩ : syracuseStep 2792483 = 4188725) B4188725
theorem B2792513 : Blo 1861632 2792513 := bstep (se 2 (by rfl) ⟨1047192, by rfl⟩ : syracuseStep 2792513 = 2094385) B2094385
theorem B2792531 : Blo 1861632 2792531 := bstep (se 1 (by rfl) ⟨2094398, by rfl⟩ : syracuseStep 2792531 = 4188797) B4188797
theorem B2792561 : Blo 1861632 2792561 := bstep (se 2 (by rfl) ⟨1047210, by rfl⟩ : syracuseStep 2792561 = 2094421) B2094421
theorem B2792579 : Blo 1861632 2792579 := bstep (se 1 (by rfl) ⟨2094434, by rfl⟩ : syracuseStep 2792579 = 4188869) B4188869
theorem B3775619 : Blo 1861632 3775619 := bstep (se 1 (by rfl) ⟨2831714, by rfl⟩ : syracuseStep 3775619 = 5663429) B5663429
theorem B2096275 : Blo 1861632 2096275 := bstep (se 1 (by rfl) ⟨1572206, by rfl⟩ : syracuseStep 2096275 = 3144413) B3144413
theorem B2792609 : Blo 1861632 2792609 := bstep (se 2 (by rfl) ⟨1047228, by rfl⟩ : syracuseStep 2792609 = 2094457) B2094457
theorem B3144865 : Blo 1861632 3144865 := bstep (se 2 (by rfl) ⟨1179324, by rfl⟩ : syracuseStep 3144865 = 2358649) B2358649
theorem B2792627 : Blo 1861632 2792627 := bstep (se 1 (by rfl) ⟨2094470, by rfl⟩ : syracuseStep 2792627 = 4188941) B4188941
theorem B2792657 : Blo 1861632 2792657 := bstep (se 2 (by rfl) ⟨1047246, by rfl⟩ : syracuseStep 2792657 = 2094493) B2094493
theorem B3316945 : Blo 1861632 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B2792675 : Blo 1861632 2792675 := bstep (se 1 (by rfl) ⟨2094506, by rfl⟩ : syracuseStep 2792675 = 4189013) B4189013
theorem B90627299 : Blo 1861632 90627299 := bstep (se 1 (by rfl) ⟨67970474, by rfl⟩ : syracuseStep 90627299 = 135940949) B135940949
theorem B2792705 : Blo 1861632 2792705 := bstep (se 2 (by rfl) ⟨1047264, by rfl⟩ : syracuseStep 2792705 = 2094529) B2094529
theorem B9428237 : Blo 1861632 9428237 := bstep (se 3 (by rfl) ⟨1767794, by rfl⟩ : syracuseStep 9428237 = 3535589) B3535589
theorem B2792723 : Blo 1861632 2792723 := bstep (se 1 (by rfl) ⟨2094542, by rfl⟩ : syracuseStep 2792723 = 4189085) B4189085
theorem B2096419 : Blo 1861632 2096419 := bstep (se 1 (by rfl) ⟨1572314, by rfl⟩ : syracuseStep 2096419 = 3144629) B3144629
theorem B7068977 : Blo 1861632 7068977 := bstep (se 2 (by rfl) ⟨2650866, by rfl⟩ : syracuseStep 7068977 = 5301733) B5301733
theorem B2792753 : Blo 1861632 2792753 := bstep (se 2 (by rfl) ⟨1047282, by rfl⟩ : syracuseStep 2792753 = 2094565) B2094565
theorem B2792771 : Blo 1861632 2792771 := bstep (se 1 (by rfl) ⟨2094578, by rfl⟩ : syracuseStep 2792771 = 4189157) B4189157
theorem B2792801 : Blo 1861632 2792801 := bstep (se 2 (by rfl) ⟨1047300, by rfl⟩ : syracuseStep 2792801 = 2094601) B2094601
theorem B2792819 : Blo 1861632 2792819 := bstep (se 1 (by rfl) ⟨2094614, by rfl⟩ : syracuseStep 2792819 = 4189229) B4189229
theorem B2358659 : Blo 1861632 2358659 := bstep (se 1 (by rfl) ⟨1768994, by rfl⟩ : syracuseStep 2358659 = 3537989) B3537989
theorem B8953229 : Blo 1861632 8953229 := bstep (se 3 (by rfl) ⟨1678730, by rfl⟩ : syracuseStep 8953229 = 3357461) B3357461
theorem B2792849 : Blo 1861632 2792849 := bstep (se 2 (by rfl) ⟨1047318, by rfl⟩ : syracuseStep 2792849 = 2094637) B2094637
theorem B2792867 : Blo 1861632 2792867 := bstep (se 1 (by rfl) ⟨2094650, by rfl⟩ : syracuseStep 2792867 = 4189301) B4189301
theorem B2096563 : Blo 1861632 2096563 := bstep (se 1 (by rfl) ⟨1572422, by rfl⟩ : syracuseStep 2096563 = 3144845) B3144845
theorem B2792897 : Blo 1861632 2792897 := bstep (se 2 (by rfl) ⟨1047336, by rfl⟩ : syracuseStep 2792897 = 2094673) B2094673
theorem B2792915 : Blo 1861632 2792915 := bstep (se 1 (by rfl) ⟨2094686, by rfl⟩ : syracuseStep 2792915 = 4189373) B4189373
theorem B2792945 : Blo 1861632 2792945 := bstep (se 2 (by rfl) ⟨1047354, by rfl⟩ : syracuseStep 2792945 = 2094709) B2094709
theorem B2792963 : Blo 1861632 2792963 := bstep (se 1 (by rfl) ⟨2094722, by rfl⟩ : syracuseStep 2792963 = 4189445) B4189445
theorem B2792993 : Blo 1861632 2792993 := bstep (se 2 (by rfl) ⟨1047372, by rfl⟩ : syracuseStep 2792993 = 2094745) B2094745
theorem B2793011 : Blo 1861632 2793011 := bstep (se 1 (by rfl) ⟨2094758, by rfl⟩ : syracuseStep 2793011 = 4189517) B4189517
theorem B2793041 : Blo 1861632 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B2793059 : Blo 1861632 2793059 := bstep (se 1 (by rfl) ⟨2094794, by rfl⟩ : syracuseStep 2793059 = 4189589) B4189589
theorem B30211697 : Blo 1861632 30211697 := bstep (se 2 (by rfl) ⟨11329386, by rfl⟩ : syracuseStep 30211697 = 22658773) B22658773
theorem B2793089 : Blo 1861632 2793089 := bstep (se 2 (by rfl) ⟨1047408, by rfl⟩ : syracuseStep 2793089 = 2094817) B2094817
theorem B2793107 : Blo 1861632 2793107 := bstep (se 1 (by rfl) ⟨2094830, by rfl⟩ : syracuseStep 2793107 = 4189661) B4189661
theorem B2793137 : Blo 1861632 2793137 := bstep (se 2 (by rfl) ⟨1047426, by rfl⟩ : syracuseStep 2793137 = 2094853) B2094853
theorem B2793155 : Blo 1861632 2793155 := bstep (se 1 (by rfl) ⟨2094866, by rfl⟩ : syracuseStep 2793155 = 4189733) B4189733
theorem B2793185 : Blo 1861632 2793185 := bstep (se 2 (by rfl) ⟨1047444, by rfl⟩ : syracuseStep 2793185 = 2094889) B2094889
theorem B2793203 : Blo 1861632 2793203 := bstep (se 1 (by rfl) ⟨2094902, by rfl⟩ : syracuseStep 2793203 = 4189805) B4189805
theorem B2793233 : Blo 1861632 2793233 := bstep (se 2 (by rfl) ⟨1047462, by rfl⟩ : syracuseStep 2793233 = 2094925) B2094925
theorem B2793251 : Blo 1861632 2793251 := bstep (se 1 (by rfl) ⟨2094938, by rfl⟩ : syracuseStep 2793251 = 4189877) B4189877
theorem B2793281 : Blo 1861632 2793281 := bstep (se 2 (by rfl) ⟨1047480, by rfl⟩ : syracuseStep 2793281 = 2094961) B2094961
theorem B2793299 : Blo 1861632 2793299 := bstep (se 1 (by rfl) ⟨2094974, by rfl⟩ : syracuseStep 2793299 = 4189949) B4189949
theorem B2793329 : Blo 1861632 2793329 := bstep (se 2 (by rfl) ⟨1047498, by rfl⟩ : syracuseStep 2793329 = 2094997) B2094997
theorem B2793347 : Blo 1861632 2793347 := bstep (se 1 (by rfl) ⟨2095010, by rfl⟩ : syracuseStep 2793347 = 4190021) B4190021
theorem B2793377 : Blo 1861632 2793377 := bstep (se 2 (by rfl) ⟨1047516, by rfl⟩ : syracuseStep 2793377 = 2095033) B2095033
theorem B10895267 : Blo 1861632 10895267 := bstep (se 1 (by rfl) ⟨8171450, by rfl⟩ : syracuseStep 10895267 = 16342901) B16342901
theorem B6807473 : Blo 1861632 6807473 := bstep (se 2 (by rfl) ⟨2552802, by rfl⟩ : syracuseStep 6807473 = 5105605) B5105605
theorem B2793395 : Blo 1861632 2793395 := bstep (se 1 (by rfl) ⟨2095046, by rfl⟩ : syracuseStep 2793395 = 4190093) B4190093
theorem B2793425 : Blo 1861632 2793425 := bstep (se 2 (by rfl) ⟨1047534, by rfl⟩ : syracuseStep 2793425 = 2095069) B2095069
theorem B2793443 : Blo 1861632 2793443 := bstep (se 1 (by rfl) ⟨2095082, by rfl⟩ : syracuseStep 2793443 = 4190165) B4190165
theorem B2793497 : Blo 1861632 2793497 := bstep (se 2 (by rfl) ⟨1047561, by rfl⟩ : syracuseStep 2793497 = 2095123) B2095123
theorem B2793611 : Blo 1861632 2793611 := bstep (se 1 (by rfl) ⟨2095208, by rfl⟩ : syracuseStep 2793611 = 4190417) B4190417
theorem B2793623 : Blo 1861632 2793623 := bstep (se 1 (by rfl) ⟨2095217, by rfl⟩ : syracuseStep 2793623 = 4190435) B4190435
theorem B2982091 : Blo 1861632 2982091 := bstep (se 1 (by rfl) ⟨2236568, by rfl⟩ : syracuseStep 2982091 = 4473137) B4473137
theorem B2793689 : Blo 1861632 2793689 := bstep (se 2 (by rfl) ⟨1047633, by rfl⟩ : syracuseStep 2793689 = 2095267) B2095267
theorem B9429209 : Blo 1861632 9429209 := bstep (se 2 (by rfl) ⟨3535953, by rfl⟩ : syracuseStep 9429209 = 7071907) B7071907
theorem B14139683 : Blo 1861632 14139683 := bstep (se 1 (by rfl) ⟨10604762, by rfl⟩ : syracuseStep 14139683 = 21209525) B21209525
theorem B2793803 : Blo 1861632 2793803 := bstep (se 1 (by rfl) ⟨2095352, by rfl⟩ : syracuseStep 2793803 = 4190705) B4190705
theorem B2793815 : Blo 1861632 2793815 := bstep (se 1 (by rfl) ⟨2095361, by rfl⟩ : syracuseStep 2793815 = 4190723) B4190723
theorem B10068317 : Blo 1861632 10068317 := bstep (se 3 (by rfl) ⟨1887809, by rfl⟩ : syracuseStep 10068317 = 3775619) B3775619
theorem B2793881 : Blo 1861632 2793881 := bstep (se 2 (by rfl) ⟨1047705, by rfl⟩ : syracuseStep 2793881 = 2095411) B2095411
theorem B2982347 : Blo 1861632 2982347 := bstep (se 1 (by rfl) ⟨2236760, by rfl⟩ : syracuseStep 2982347 = 4473521) B4473521
theorem B2793995 : Blo 1861632 2793995 := bstep (se 1 (by rfl) ⟨2095496, by rfl⟩ : syracuseStep 2793995 = 4190993) B4190993
theorem B2794007 : Blo 1861632 2794007 := bstep (se 1 (by rfl) ⟨2095505, by rfl⟩ : syracuseStep 2794007 = 4191011) B4191011
theorem B14344739 : Blo 1861632 14344739 := bstep (se 1 (by rfl) ⟨10758554, by rfl⟩ : syracuseStep 14344739 = 21517109) B21517109
theorem B7955009 : Blo 1861632 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B2794073 : Blo 1861632 2794073 := bstep (se 2 (by rfl) ⟨1047777, by rfl⟩ : syracuseStep 2794073 = 2095555) B2095555
theorem B8610455 : Blo 1861632 8610455 := bstep (se 1 (by rfl) ⟨6457841, by rfl⟩ : syracuseStep 8610455 = 12915683) B12915683
theorem B20136599 : Blo 1861632 20136599 := bstep (se 1 (by rfl) ⟨15102449, by rfl⟩ : syracuseStep 20136599 = 30204899) B30204899
theorem B6283979 : Blo 1861632 6283979 := bstep (se 1 (by rfl) ⟨4712984, by rfl⟩ : syracuseStep 6283979 = 9425969) B9425969
theorem B2794187 : Blo 1861632 2794187 := bstep (se 1 (by rfl) ⟨2095640, by rfl⟩ : syracuseStep 2794187 = 4191281) B4191281
theorem B2794199 : Blo 1861632 2794199 := bstep (se 1 (by rfl) ⟨2095649, by rfl⟩ : syracuseStep 2794199 = 4191299) B4191299
theorem B2794265 : Blo 1861632 2794265 := bstep (se 2 (by rfl) ⟨1047849, by rfl⟩ : syracuseStep 2794265 = 2095699) B2095699
theorem B7652161 : Blo 1861632 7652161 := bstep (se 2 (by rfl) ⟨2869560, by rfl⟩ : syracuseStep 7652161 = 5739121) B5739121
theorem B10609501 : Blo 1861632 10609501 := bstep (se 3 (by rfl) ⟨1989281, by rfl⟩ : syracuseStep 10609501 = 3978563) B3978563
theorem B2794379 : Blo 1861632 2794379 := bstep (se 1 (by rfl) ⟨2095784, by rfl⟩ : syracuseStep 2794379 = 4191569) B4191569
theorem B2794391 : Blo 1861632 2794391 := bstep (se 1 (by rfl) ⟨2095793, by rfl⟩ : syracuseStep 2794391 = 4191587) B4191587
theorem B6710195 : Blo 1861632 6710195 := bstep (se 1 (by rfl) ⟨5032646, by rfl⟩ : syracuseStep 6710195 = 10065293) B10065293
theorem B6284249 : Blo 1861632 6284249 := bstep (se 2 (by rfl) ⟨2356593, by rfl⟩ : syracuseStep 6284249 = 4713187) B4713187
theorem B2794457 : Blo 1861632 2794457 := bstep (se 2 (by rfl) ⟨1047921, by rfl⟩ : syracuseStep 2794457 = 2095843) B2095843
theorem B7070723 : Blo 1861632 7070723 := bstep (se 1 (by rfl) ⟨5303042, by rfl⟩ : syracuseStep 7070723 = 10606085) B10606085
theorem B8946733 : Blo 1861632 8946733 := bstep (se 3 (by rfl) ⟨1677512, by rfl⟩ : syracuseStep 8946733 = 3355025) B3355025
theorem B2794571 : Blo 1861632 2794571 := bstep (se 1 (by rfl) ⟨2095928, by rfl⟩ : syracuseStep 2794571 = 4191857) B4191857
theorem B2794583 : Blo 1861632 2794583 := bstep (se 1 (by rfl) ⟨2095937, by rfl⟩ : syracuseStep 2794583 = 4191875) B4191875
theorem B2983051 : Blo 1861632 2983051 := bstep (se 1 (by rfl) ⟨2237288, by rfl⟩ : syracuseStep 2983051 = 4474577) B4474577
theorem B2794649 : Blo 1861632 2794649 := bstep (se 2 (by rfl) ⟨1047993, by rfl⟩ : syracuseStep 2794649 = 2095987) B2095987
theorem B2794763 : Blo 1861632 2794763 := bstep (se 1 (by rfl) ⟨2096072, by rfl⟩ : syracuseStep 2794763 = 4192145) B4192145
theorem B15918353 : Blo 1861632 15918353 := bstep (se 2 (by rfl) ⟨5969382, by rfl⟩ : syracuseStep 15918353 = 11938765) B11938765
theorem B2794775 : Blo 1861632 2794775 := bstep (se 1 (by rfl) ⟨2096081, by rfl⟩ : syracuseStep 2794775 = 4192163) B4192163
theorem B2794841 : Blo 1861632 2794841 := bstep (se 2 (by rfl) ⟨1048065, by rfl⟩ : syracuseStep 2794841 = 2096131) B2096131
theorem B11937125 : Blo 1861632 11937125 := bstep (se 4 (by rfl) ⟨1119105, by rfl⟩ : syracuseStep 11937125 = 2238211) B2238211
theorem B2983321 : Blo 1861632 2983321 := bstep (se 2 (by rfl) ⟨1118745, by rfl⟩ : syracuseStep 2983321 = 2237491) B2237491
theorem B2794955 : Blo 1861632 2794955 := bstep (se 1 (by rfl) ⟨2096216, by rfl⟩ : syracuseStep 2794955 = 4192433) B4192433
theorem B16999885 : Blo 1861632 16999885 := bstep (se 3 (by rfl) ⟨3187478, by rfl⟩ : syracuseStep 16999885 = 6374957) B6374957
theorem B2794967 : Blo 1861632 2794967 := bstep (se 1 (by rfl) ⟨2096225, by rfl⟩ : syracuseStep 2794967 = 4192451) B4192451
theorem B2983385 : Blo 1861632 2983385 := bstep (se 2 (by rfl) ⟨1118769, by rfl⟩ : syracuseStep 2983385 = 2237539) B2237539
theorem B32261645 : Blo 1861632 32261645 := bstep (se 3 (by rfl) ⟨6049058, by rfl⟩ : syracuseStep 32261645 = 12098117) B12098117
theorem B2795033 : Blo 1861632 2795033 := bstep (se 2 (by rfl) ⟨1048137, by rfl⟩ : syracuseStep 2795033 = 2096275) B2096275
theorem B13428317 : Blo 1861632 13428317 := bstep (se 3 (by rfl) ⟨2517809, by rfl⟩ : syracuseStep 13428317 = 5035619) B5035619
theorem B2795147 : Blo 1861632 2795147 := bstep (se 1 (by rfl) ⟨2096360, by rfl⟩ : syracuseStep 2795147 = 4192721) B4192721
theorem B6284951 : Blo 1861632 6284951 := bstep (se 1 (by rfl) ⟨4713713, by rfl⟩ : syracuseStep 6284951 = 9427427) B9427427
theorem B7169687 : Blo 1861632 7169687 := bstep (se 1 (by rfl) ⟨5377265, by rfl⟩ : syracuseStep 7169687 = 10754531) B10754531
theorem B2795159 : Blo 1861632 2795159 := bstep (se 1 (by rfl) ⟨2096369, by rfl⟩ : syracuseStep 2795159 = 4192739) B4192739
theorem B2795225 : Blo 1861632 2795225 := bstep (se 2 (by rfl) ⟨1048209, by rfl⟩ : syracuseStep 2795225 = 2096419) B2096419
theorem B9430829 : Blo 1861632 9430829 := bstep (se 3 (by rfl) ⟨1768280, by rfl⟩ : syracuseStep 9430829 = 3536561) B3536561
theorem B2795339 : Blo 1861632 2795339 := bstep (se 1 (by rfl) ⟨2096504, by rfl⟩ : syracuseStep 2795339 = 4193009) B4193009
theorem B2795351 : Blo 1861632 2795351 := bstep (se 1 (by rfl) ⟨2096513, by rfl⟩ : syracuseStep 2795351 = 4193027) B4193027
theorem B5662553 : Blo 1861632 5662553 := bstep (se 2 (by rfl) ⟨2123457, by rfl⟩ : syracuseStep 5662553 = 4246915) B4246915
theorem B2795417 : Blo 1861632 2795417 := bstep (se 2 (by rfl) ⟨1048281, by rfl⟩ : syracuseStep 2795417 = 2096563) B2096563
theorem B7956427 : Blo 1861632 7956427 := bstep (se 1 (by rfl) ⟨5967320, by rfl⟩ : syracuseStep 7956427 = 11934641) B11934641
theorem B1861643 : Blo 1861632 1861643 := bstep (se 1 (by rfl) ⟨1396232, by rfl⟩ : syracuseStep 1861643 = 2792465) B2792465
theorem B1861655 : Blo 1861632 1861655 := bstep (se 1 (by rfl) ⟨1396241, by rfl⟩ : syracuseStep 1861655 = 2792483) B2792483
theorem B1861675 : Blo 1861632 1861675 := bstep (se 1 (by rfl) ⟨1396256, by rfl⟩ : syracuseStep 1861675 = 2792513) B2792513
theorem B1861687 : Blo 1861632 1861687 := bstep (se 1 (by rfl) ⟨1396265, by rfl⟩ : syracuseStep 1861687 = 2792531) B2792531
theorem B4909121 : Blo 1861632 4909121 := bstep (se 2 (by rfl) ⟨1840920, by rfl⟩ : syracuseStep 4909121 = 3681841) B3681841
theorem B1861707 : Blo 1861632 1861707 := bstep (se 1 (by rfl) ⟨1396280, by rfl⟩ : syracuseStep 1861707 = 2792561) B2792561
theorem B1861719 : Blo 1861632 1861719 := bstep (se 1 (by rfl) ⟨1396289, by rfl⟩ : syracuseStep 1861719 = 2792579) B2792579
theorem B1861739 : Blo 1861632 1861739 := bstep (se 1 (by rfl) ⟨1396304, by rfl⟩ : syracuseStep 1861739 = 2792609) B2792609
theorem B1861751 : Blo 1861632 1861751 := bstep (se 1 (by rfl) ⟨1396313, by rfl⟩ : syracuseStep 1861751 = 2792627) B2792627
theorem B1861771 : Blo 1861632 1861771 := bstep (se 1 (by rfl) ⟨1396328, by rfl⟩ : syracuseStep 1861771 = 2792657) B2792657
theorem B1861783 : Blo 1861632 1861783 := bstep (se 1 (by rfl) ⟨1396337, by rfl⟩ : syracuseStep 1861783 = 2792675) B2792675
theorem B60418199 : Blo 1861632 60418199 := bstep (se 1 (by rfl) ⟨45313649, by rfl⟩ : syracuseStep 60418199 = 90627299) B90627299
theorem B30214295 : Blo 1861632 30214295 := bstep (se 1 (by rfl) ⟨22660721, by rfl⟩ : syracuseStep 30214295 = 45321443) B45321443
theorem B1861803 : Blo 1861632 1861803 := bstep (se 1 (by rfl) ⟨1396352, by rfl⟩ : syracuseStep 1861803 = 2792705) B2792705
theorem B6285491 : Blo 1861632 6285491 := bstep (se 1 (by rfl) ⟨4714118, by rfl⟩ : syracuseStep 6285491 = 9428237) B9428237
theorem B1861815 : Blo 1861632 1861815 := bstep (se 1 (by rfl) ⟨1396361, by rfl⟩ : syracuseStep 1861815 = 2792723) B2792723
theorem B4712651 : Blo 1861632 4712651 := bstep (se 1 (by rfl) ⟨3534488, by rfl⟩ : syracuseStep 4712651 = 7068977) B7068977
theorem B1861835 : Blo 1861632 1861835 := bstep (se 1 (by rfl) ⟨1396376, by rfl⟩ : syracuseStep 1861835 = 2792753) B2792753
theorem B5376203 : Blo 1861632 5376203 := bstep (se 1 (by rfl) ⟨4032152, by rfl⟩ : syracuseStep 5376203 = 8064305) B8064305
theorem B1861847 : Blo 1861632 1861847 := bstep (se 1 (by rfl) ⟨1396385, by rfl⟩ : syracuseStep 1861847 = 2792771) B2792771
theorem B7653593 : Blo 1861632 7653593 := bstep (se 2 (by rfl) ⟨2870097, by rfl⟩ : syracuseStep 7653593 = 5740195) B5740195
theorem B7956701 : Blo 1861632 7956701 := bstep (se 3 (by rfl) ⟨1491881, by rfl⟩ : syracuseStep 7956701 = 2983763) B2983763
theorem B1861867 : Blo 1861632 1861867 := bstep (se 1 (by rfl) ⟨1396400, by rfl⟩ : syracuseStep 1861867 = 2792801) B2792801
theorem B1861879 : Blo 1861632 1861879 := bstep (se 1 (by rfl) ⟨1396409, by rfl⟩ : syracuseStep 1861879 = 2792819) B2792819
theorem B1861899 : Blo 1861632 1861899 := bstep (se 1 (by rfl) ⟨1396424, by rfl⟩ : syracuseStep 1861899 = 2792849) B2792849
theorem B1861911 : Blo 1861632 1861911 := bstep (se 1 (by rfl) ⟨1396433, by rfl⟩ : syracuseStep 1861911 = 2792867) B2792867
theorem B1861931 : Blo 1861632 1861931 := bstep (se 1 (by rfl) ⟨1396448, by rfl⟩ : syracuseStep 1861931 = 2792897) B2792897
theorem B1861943 : Blo 1861632 1861943 := bstep (se 1 (by rfl) ⟨1396457, by rfl⟩ : syracuseStep 1861943 = 2792915) B2792915
theorem B1861963 : Blo 1861632 1861963 := bstep (se 1 (by rfl) ⟨1396472, by rfl⟩ : syracuseStep 1861963 = 2792945) B2792945
theorem B1861975 : Blo 1861632 1861975 := bstep (se 1 (by rfl) ⟨1396481, by rfl⟩ : syracuseStep 1861975 = 2792963) B2792963
theorem B11929949 : Blo 1861632 11929949 := bstep (se 3 (by rfl) ⟨2236865, by rfl⟩ : syracuseStep 11929949 = 4473731) B4473731
theorem B1861995 : Blo 1861632 1861995 := bstep (se 1 (by rfl) ⟨1396496, by rfl⟩ : syracuseStep 1861995 = 2792993) B2792993
theorem B1862007 : Blo 1861632 1862007 := bstep (se 1 (by rfl) ⟨1396505, by rfl⟩ : syracuseStep 1862007 = 2793011) B2793011
theorem B1862027 : Blo 1861632 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B1862039 : Blo 1861632 1862039 := bstep (se 1 (by rfl) ⟨1396529, by rfl⟩ : syracuseStep 1862039 = 2793059) B2793059
theorem B1862059 : Blo 1861632 1862059 := bstep (se 1 (by rfl) ⟨1396544, by rfl⟩ : syracuseStep 1862059 = 2793089) B2793089
theorem B1862071 : Blo 1861632 1862071 := bstep (se 1 (by rfl) ⟨1396553, by rfl⟩ : syracuseStep 1862071 = 2793107) B2793107
theorem B6285761 : Blo 1861632 6285761 := bstep (se 2 (by rfl) ⟨2357160, by rfl⟩ : syracuseStep 6285761 = 4714321) B4714321
theorem B1862091 : Blo 1861632 1862091 := bstep (se 1 (by rfl) ⟨1396568, by rfl⟩ : syracuseStep 1862091 = 2793137) B2793137
theorem B1862103 : Blo 1861632 1862103 := bstep (se 1 (by rfl) ⟨1396577, by rfl⟩ : syracuseStep 1862103 = 2793155) B2793155
theorem B1862123 : Blo 1861632 1862123 := bstep (se 1 (by rfl) ⟨1396592, by rfl⟩ : syracuseStep 1862123 = 2793185) B2793185
theorem B1862135 : Blo 1861632 1862135 := bstep (se 1 (by rfl) ⟨1396601, by rfl⟩ : syracuseStep 1862135 = 2793203) B2793203
theorem B1862155 : Blo 1861632 1862155 := bstep (se 1 (by rfl) ⟨1396616, by rfl⟩ : syracuseStep 1862155 = 2793233) B2793233
theorem B1862167 : Blo 1861632 1862167 := bstep (se 1 (by rfl) ⟨1396625, by rfl⟩ : syracuseStep 1862167 = 2793251) B2793251
theorem B1862187 : Blo 1861632 1862187 := bstep (se 1 (by rfl) ⟨1396640, by rfl⟩ : syracuseStep 1862187 = 2793281) B2793281
theorem B1862199 : Blo 1861632 1862199 := bstep (se 1 (by rfl) ⟨1396649, by rfl⟩ : syracuseStep 1862199 = 2793299) B2793299
theorem B4713025 : Blo 1861632 4713025 := bstep (se 2 (by rfl) ⟨1767384, by rfl⟩ : syracuseStep 4713025 = 3534769) B3534769
theorem B1862219 : Blo 1861632 1862219 := bstep (se 1 (by rfl) ⟨1396664, by rfl⟩ : syracuseStep 1862219 = 2793329) B2793329
theorem B1862231 : Blo 1861632 1862231 := bstep (se 1 (by rfl) ⟨1396673, by rfl⟩ : syracuseStep 1862231 = 2793347) B2793347
theorem B4188761 : Blo 1861632 4188761 := bstep (se 2 (by rfl) ⟨1570785, by rfl⟩ : syracuseStep 4188761 = 3141571) B3141571
theorem B1862251 : Blo 1861632 1862251 := bstep (se 1 (by rfl) ⟨1396688, by rfl⟩ : syracuseStep 1862251 = 2793377) B2793377
theorem B1862263 : Blo 1861632 1862263 := bstep (se 1 (by rfl) ⟨1396697, by rfl⟩ : syracuseStep 1862263 = 2793395) B2793395
theorem B1862283 : Blo 1861632 1862283 := bstep (se 1 (by rfl) ⟨1396712, by rfl⟩ : syracuseStep 1862283 = 2793425) B2793425
theorem B1862295 : Blo 1861632 1862295 := bstep (se 1 (by rfl) ⟨1396721, by rfl⟩ : syracuseStep 1862295 = 2793443) B2793443
theorem B1862315 : Blo 1861632 1862315 := bstep (se 1 (by rfl) ⟨1396736, by rfl⟩ : syracuseStep 1862315 = 2793473) B2793473
theorem B4188851 : Blo 1861632 4188851 := bstep (se 1 (by rfl) ⟨3141638, by rfl⟩ : syracuseStep 4188851 = 6283277) B6283277
theorem B1862327 : Blo 1861632 1862327 := bstep (se 1 (by rfl) ⟨1396745, by rfl⟩ : syracuseStep 1862327 = 2793491) B2793491
theorem B1862347 : Blo 1861632 1862347 := bstep (se 1 (by rfl) ⟨1396760, by rfl⟩ : syracuseStep 1862347 = 2793521) B2793521
theorem B4188887 : Blo 1861632 4188887 := bstep (se 1 (by rfl) ⟨3141665, by rfl⟩ : syracuseStep 4188887 = 6283331) B6283331
theorem B1862359 : Blo 1861632 1862359 := bstep (se 1 (by rfl) ⟨1396769, by rfl⟩ : syracuseStep 1862359 = 2793539) B2793539
theorem B1862379 : Blo 1861632 1862379 := bstep (se 1 (by rfl) ⟨1396784, by rfl⟩ : syracuseStep 1862379 = 2793569) B2793569
theorem B1862391 : Blo 1861632 1862391 := bstep (se 1 (by rfl) ⟨1396793, by rfl⟩ : syracuseStep 1862391 = 2793587) B2793587
theorem B1862411 : Blo 1861632 1862411 := bstep (se 1 (by rfl) ⟨1396808, by rfl⟩ : syracuseStep 1862411 = 2793617) B2793617
theorem B1862423 : Blo 1861632 1862423 := bstep (se 1 (by rfl) ⟨1396817, by rfl⟩ : syracuseStep 1862423 = 2793635) B2793635
theorem B5966615 : Blo 1861632 5966615 := bstep (se 1 (by rfl) ⟨4474961, by rfl⟩ : syracuseStep 5966615 = 8949923) B8949923
theorem B1862443 : Blo 1861632 1862443 := bstep (se 1 (by rfl) ⟨1396832, by rfl⟩ : syracuseStep 1862443 = 2793665) B2793665
theorem B1862455 : Blo 1861632 1862455 := bstep (se 1 (by rfl) ⟨1396841, by rfl⟩ : syracuseStep 1862455 = 2793683) B2793683
theorem B1862475 : Blo 1861632 1862475 := bstep (se 1 (by rfl) ⟨1396856, by rfl⟩ : syracuseStep 1862475 = 2793713) B2793713
theorem B1862487 : Blo 1861632 1862487 := bstep (se 1 (by rfl) ⟨1396865, by rfl⟩ : syracuseStep 1862487 = 2793731) B2793731
theorem B1862507 : Blo 1861632 1862507 := bstep (se 1 (by rfl) ⟨1396880, by rfl⟩ : syracuseStep 1862507 = 2793761) B2793761
theorem B1862519 : Blo 1861632 1862519 := bstep (se 1 (by rfl) ⟨1396889, by rfl⟩ : syracuseStep 1862519 = 2793779) B2793779
theorem B4189067 : Blo 1861632 4189067 := bstep (se 1 (by rfl) ⟨3141800, by rfl⟩ : syracuseStep 4189067 = 6283601) B6283601
theorem B1862539 : Blo 1861632 1862539 := bstep (se 1 (by rfl) ⟨1396904, by rfl⟩ : syracuseStep 1862539 = 2793809) B2793809
theorem B5303191 : Blo 1861632 5303191 := bstep (se 1 (by rfl) ⟨3977393, by rfl⟩ : syracuseStep 5303191 = 7954787) B7954787
theorem B1862551 : Blo 1861632 1862551 := bstep (se 1 (by rfl) ⟨1396913, by rfl⟩ : syracuseStep 1862551 = 2793827) B2793827
theorem B1862571 : Blo 1861632 1862571 := bstep (se 1 (by rfl) ⟨1396928, by rfl⟩ : syracuseStep 1862571 = 2793857) B2793857
theorem B4475827 : Blo 1861632 4475827 := bstep (se 1 (by rfl) ⟨3356870, by rfl⟩ : syracuseStep 4475827 = 6713741) B6713741
theorem B1862583 : Blo 1861632 1862583 := bstep (se 1 (by rfl) ⟨1396937, by rfl⟩ : syracuseStep 1862583 = 2793875) B2793875
theorem B4189121 : Blo 1861632 4189121 := bstep (se 2 (by rfl) ⟨1570920, by rfl⟩ : syracuseStep 4189121 = 3141841) B3141841
theorem B1862603 : Blo 1861632 1862603 := bstep (se 1 (by rfl) ⟨1396952, by rfl⟩ : syracuseStep 1862603 = 2793905) B2793905
theorem B1862615 : Blo 1861632 1862615 := bstep (se 1 (by rfl) ⟨1396961, by rfl⟩ : syracuseStep 1862615 = 2793923) B2793923
theorem B11324377 : Blo 1861632 11324377 := bstep (se 2 (by rfl) ⟨4246641, by rfl⟩ : syracuseStep 11324377 = 8493283) B8493283
theorem B6286301 : Blo 1861632 6286301 := bstep (se 3 (by rfl) ⟨1178681, by rfl⟩ : syracuseStep 6286301 = 2357363) B2357363
theorem B1862635 : Blo 1861632 1862635 := bstep (se 1 (by rfl) ⟨1396976, by rfl⟩ : syracuseStep 1862635 = 2793953) B2793953
theorem B1862647 : Blo 1861632 1862647 := bstep (se 1 (by rfl) ⟨1396985, by rfl⟩ : syracuseStep 1862647 = 2793971) B2793971
theorem B1862667 : Blo 1861632 1862667 := bstep (se 1 (by rfl) ⟨1397000, by rfl⟩ : syracuseStep 1862667 = 2794001) B2794001
theorem B1862679 : Blo 1861632 1862679 := bstep (se 1 (by rfl) ⟨1397009, by rfl⟩ : syracuseStep 1862679 = 2794019) B2794019
theorem B1862699 : Blo 1861632 1862699 := bstep (se 1 (by rfl) ⟨1397024, by rfl⟩ : syracuseStep 1862699 = 2794049) B2794049
theorem B1862711 : Blo 1861632 1862711 := bstep (se 1 (by rfl) ⟨1397033, by rfl⟩ : syracuseStep 1862711 = 2794067) B2794067
theorem B1862731 : Blo 1861632 1862731 := bstep (se 1 (by rfl) ⟨1397048, by rfl⟩ : syracuseStep 1862731 = 2794097) B2794097
theorem B1862743 : Blo 1861632 1862743 := bstep (se 1 (by rfl) ⟨1397057, by rfl⟩ : syracuseStep 1862743 = 2794115) B2794115
theorem B1862763 : Blo 1861632 1862763 := bstep (se 1 (by rfl) ⟨1397072, by rfl⟩ : syracuseStep 1862763 = 2794145) B2794145
theorem B1862775 : Blo 1861632 1862775 := bstep (se 1 (by rfl) ⟨1397081, by rfl⟩ : syracuseStep 1862775 = 2794163) B2794163
theorem B1862795 : Blo 1861632 1862795 := bstep (se 1 (by rfl) ⟨1397096, by rfl⟩ : syracuseStep 1862795 = 2794193) B2794193
theorem B4713623 : Blo 1861632 4713623 := bstep (se 1 (by rfl) ⟨3535217, by rfl⟩ : syracuseStep 4713623 = 7070435) B7070435
theorem B1862807 : Blo 1861632 1862807 := bstep (se 1 (by rfl) ⟨1397105, by rfl⟩ : syracuseStep 1862807 = 2794211) B2794211
theorem B4189337 : Blo 1861632 4189337 := bstep (se 2 (by rfl) ⟨1571001, by rfl⟩ : syracuseStep 4189337 = 3142003) B3142003
theorem B1862827 : Blo 1861632 1862827 := bstep (se 1 (by rfl) ⟨1397120, by rfl⟩ : syracuseStep 1862827 = 2794241) B2794241
theorem B1862839 : Blo 1861632 1862839 := bstep (se 1 (by rfl) ⟨1397129, by rfl⟩ : syracuseStep 1862839 = 2794259) B2794259
theorem B1862859 : Blo 1861632 1862859 := bstep (se 1 (by rfl) ⟨1397144, by rfl⟩ : syracuseStep 1862859 = 2794289) B2794289
theorem B14150861 : Blo 1861632 14150861 := bstep (se 3 (by rfl) ⟨2653286, by rfl⟩ : syracuseStep 14150861 = 5306573) B5306573
theorem B1862871 : Blo 1861632 1862871 := bstep (se 1 (by rfl) ⟨1397153, by rfl⟩ : syracuseStep 1862871 = 2794307) B2794307
theorem B1862891 : Blo 1861632 1862891 := bstep (se 1 (by rfl) ⟨1397168, by rfl⟩ : syracuseStep 1862891 = 2794337) B2794337
theorem B4189427 : Blo 1861632 4189427 := bstep (se 1 (by rfl) ⟨3142070, by rfl⟩ : syracuseStep 4189427 = 6284141) B6284141
theorem B1862903 : Blo 1861632 1862903 := bstep (se 1 (by rfl) ⟨1397177, by rfl⟩ : syracuseStep 1862903 = 2794355) B2794355
theorem B1862923 : Blo 1861632 1862923 := bstep (se 1 (by rfl) ⟨1397192, by rfl⟩ : syracuseStep 1862923 = 2794385) B2794385
theorem B4189463 : Blo 1861632 4189463 := bstep (se 1 (by rfl) ⟨3142097, by rfl⟩ : syracuseStep 4189463 = 6284195) B6284195
theorem B1862935 : Blo 1861632 1862935 := bstep (se 1 (by rfl) ⟨1397201, by rfl⟩ : syracuseStep 1862935 = 2794403) B2794403
theorem B1862955 : Blo 1861632 1862955 := bstep (se 1 (by rfl) ⟨1397216, by rfl⟩ : syracuseStep 1862955 = 2794433) B2794433
theorem B1862967 : Blo 1861632 1862967 := bstep (se 1 (by rfl) ⟨1397225, by rfl⟩ : syracuseStep 1862967 = 2794451) B2794451
theorem B5967179 : Blo 1861632 5967179 := bstep (se 1 (by rfl) ⟨4475384, by rfl⟩ : syracuseStep 5967179 = 8950769) B8950769
theorem B1862987 : Blo 1861632 1862987 := bstep (se 1 (by rfl) ⟨1397240, by rfl⟩ : syracuseStep 1862987 = 2794481) B2794481
theorem B1862999 : Blo 1861632 1862999 := bstep (se 1 (by rfl) ⟨1397249, by rfl⟩ : syracuseStep 1862999 = 2794499) B2794499
theorem B1863019 : Blo 1861632 1863019 := bstep (se 1 (by rfl) ⟨1397264, by rfl⟩ : syracuseStep 1863019 = 2794529) B2794529
theorem B1863031 : Blo 1861632 1863031 := bstep (se 1 (by rfl) ⟨1397273, by rfl⟩ : syracuseStep 1863031 = 2794547) B2794547
theorem B1863051 : Blo 1861632 1863051 := bstep (se 1 (by rfl) ⟨1397288, by rfl⟩ : syracuseStep 1863051 = 2794577) B2794577
theorem B1863063 : Blo 1861632 1863063 := bstep (se 1 (by rfl) ⟨1397297, by rfl⟩ : syracuseStep 1863063 = 2794595) B2794595
theorem B1863083 : Blo 1861632 1863083 := bstep (se 1 (by rfl) ⟨1397312, by rfl⟩ : syracuseStep 1863083 = 2794625) B2794625
theorem B1863095 : Blo 1861632 1863095 := bstep (se 1 (by rfl) ⟨1397321, by rfl⟩ : syracuseStep 1863095 = 2794643) B2794643
theorem B3534283 : Blo 1861632 3534283 := bstep (se 1 (by rfl) ⟨2650712, by rfl⟩ : syracuseStep 3534283 = 5301425) B5301425
theorem B4189643 : Blo 1861632 4189643 := bstep (se 1 (by rfl) ⟨3142232, by rfl⟩ : syracuseStep 4189643 = 6284465) B6284465
theorem B1863115 : Blo 1861632 1863115 := bstep (se 1 (by rfl) ⟨1397336, by rfl⟩ : syracuseStep 1863115 = 2794673) B2794673
theorem B1863127 : Blo 1861632 1863127 := bstep (se 1 (by rfl) ⟨1397345, by rfl⟩ : syracuseStep 1863127 = 2794691) B2794691
theorem B1863147 : Blo 1861632 1863147 := bstep (se 1 (by rfl) ⟨1397360, by rfl⟩ : syracuseStep 1863147 = 2794721) B2794721
theorem B1863159 : Blo 1861632 1863159 := bstep (se 1 (by rfl) ⟨1397369, by rfl⟩ : syracuseStep 1863159 = 2794739) B2794739
theorem B4189697 : Blo 1861632 4189697 := bstep (se 2 (by rfl) ⟨1571136, by rfl⟩ : syracuseStep 4189697 = 3142273) B3142273
theorem B1863179 : Blo 1861632 1863179 := bstep (se 1 (by rfl) ⟨1397384, by rfl⟩ : syracuseStep 1863179 = 2794769) B2794769
theorem B1863191 : Blo 1861632 1863191 := bstep (se 1 (by rfl) ⟨1397393, by rfl⟩ : syracuseStep 1863191 = 2794787) B2794787
theorem B13422115 : Blo 1861632 13422115 := bstep (se 1 (by rfl) ⟨10066586, by rfl⟩ : syracuseStep 13422115 = 20133173) B20133173
theorem B1863211 : Blo 1861632 1863211 := bstep (se 1 (by rfl) ⟨1397408, by rfl⟩ : syracuseStep 1863211 = 2794817) B2794817
theorem B1863223 : Blo 1861632 1863223 := bstep (se 1 (by rfl) ⟨1397417, by rfl⟩ : syracuseStep 1863223 = 2794835) B2794835
theorem B1863243 : Blo 1861632 1863243 := bstep (se 1 (by rfl) ⟨1397432, by rfl⟩ : syracuseStep 1863243 = 2794865) B2794865
theorem B1863255 : Blo 1861632 1863255 := bstep (se 1 (by rfl) ⟨1397441, by rfl⟩ : syracuseStep 1863255 = 2794883) B2794883
theorem B17895005 : Blo 1861632 17895005 := bstep (se 3 (by rfl) ⟨3355313, by rfl⟩ : syracuseStep 17895005 = 6710627) B6710627
theorem B23866973 : Blo 1861632 23866973 := bstep (se 3 (by rfl) ⟨4475057, by rfl⟩ : syracuseStep 23866973 = 8950115) B8950115
theorem B31829597 : Blo 1861632 31829597 := bstep (se 3 (by rfl) ⟨5968049, by rfl⟩ : syracuseStep 31829597 = 11936099) B11936099
theorem B1863275 : Blo 1861632 1863275 := bstep (se 1 (by rfl) ⟨1397456, by rfl⟩ : syracuseStep 1863275 = 2794913) B2794913
theorem B1863287 : Blo 1861632 1863287 := bstep (se 1 (by rfl) ⟨1397465, by rfl⟩ : syracuseStep 1863287 = 2794931) B2794931
theorem B7548547 : Blo 1861632 7548547 := bstep (se 1 (by rfl) ⟨5661410, by rfl⟩ : syracuseStep 7548547 = 11322821) B11322821
theorem B24202883 : Blo 1861632 24202883 := bstep (se 1 (by rfl) ⟨18152162, by rfl⟩ : syracuseStep 24202883 = 36304325) B36304325
theorem B1863307 : Blo 1861632 1863307 := bstep (se 1 (by rfl) ⟨1397480, by rfl⟩ : syracuseStep 1863307 = 2794961) B2794961
theorem B1863319 : Blo 1861632 1863319 := bstep (se 1 (by rfl) ⟨1397489, by rfl⟩ : syracuseStep 1863319 = 2794979) B2794979
theorem B1863339 : Blo 1861632 1863339 := bstep (se 1 (by rfl) ⟨1397504, by rfl⟩ : syracuseStep 1863339 = 2795009) B2795009
theorem B14151347 : Blo 1861632 14151347 := bstep (se 1 (by rfl) ⟨10613510, by rfl⟩ : syracuseStep 14151347 = 21227021) B21227021
theorem B1863351 : Blo 1861632 1863351 := bstep (se 1 (by rfl) ⟨1397513, by rfl⟩ : syracuseStep 1863351 = 2795027) B2795027
theorem B2100919 : Blo 1861632 2100919 := bstep (se 1 (by rfl) ⟨1575689, by rfl⟩ : syracuseStep 2100919 = 3151379) B3151379
theorem B1863371 : Blo 1861632 1863371 := bstep (se 1 (by rfl) ⟨1397528, by rfl⟩ : syracuseStep 1863371 = 2795057) B2795057
theorem B1863383 : Blo 1861632 1863383 := bstep (se 1 (by rfl) ⟨1397537, by rfl⟩ : syracuseStep 1863383 = 2795075) B2795075
theorem B4189913 : Blo 1861632 4189913 := bstep (se 2 (by rfl) ⟨1571217, by rfl⟩ : syracuseStep 4189913 = 3142435) B3142435
theorem B1863403 : Blo 1861632 1863403 := bstep (se 1 (by rfl) ⟨1397552, by rfl⟩ : syracuseStep 1863403 = 2795105) B2795105
theorem B1863415 : Blo 1861632 1863415 := bstep (se 1 (by rfl) ⟨1397561, by rfl⟩ : syracuseStep 1863415 = 2795123) B2795123
theorem B1863435 : Blo 1861632 1863435 := bstep (se 1 (by rfl) ⟨1397576, by rfl⟩ : syracuseStep 1863435 = 2795153) B2795153
theorem B6369047 : Blo 1861632 6369047 := bstep (se 1 (by rfl) ⟨4776785, by rfl⟩ : syracuseStep 6369047 = 9553571) B9553571
theorem B1863447 : Blo 1861632 1863447 := bstep (se 1 (by rfl) ⟨1397585, by rfl⟩ : syracuseStep 1863447 = 2795171) B2795171
theorem B3534617 : Blo 1861632 3534617 := bstep (se 2 (by rfl) ⟨1325481, by rfl⟩ : syracuseStep 3534617 = 2650963) B2650963
theorem B1863467 : Blo 1861632 1863467 := bstep (se 1 (by rfl) ⟨1397600, by rfl⟩ : syracuseStep 1863467 = 2795201) B2795201
theorem B4190003 : Blo 1861632 4190003 := bstep (se 1 (by rfl) ⟨3142502, by rfl⟩ : syracuseStep 4190003 = 6285005) B6285005
theorem B1863479 : Blo 1861632 1863479 := bstep (se 1 (by rfl) ⟨1397609, by rfl⟩ : syracuseStep 1863479 = 2795219) B2795219
theorem B1863499 : Blo 1861632 1863499 := bstep (se 1 (by rfl) ⟨1397624, by rfl⟩ : syracuseStep 1863499 = 2795249) B2795249
theorem B4190039 : Blo 1861632 4190039 := bstep (se 1 (by rfl) ⟨3142529, by rfl⟩ : syracuseStep 4190039 = 6285059) B6285059
theorem B1863511 : Blo 1861632 1863511 := bstep (se 1 (by rfl) ⟨1397633, by rfl⟩ : syracuseStep 1863511 = 2795267) B2795267
theorem B1863531 : Blo 1861632 1863531 := bstep (se 1 (by rfl) ⟨1397648, by rfl⟩ : syracuseStep 1863531 = 2795297) B2795297
theorem B1863543 : Blo 1861632 1863543 := bstep (se 1 (by rfl) ⟨1397657, by rfl⟩ : syracuseStep 1863543 = 2795315) B2795315
theorem B1863563 : Blo 1861632 1863563 := bstep (se 1 (by rfl) ⟨1397672, by rfl⟩ : syracuseStep 1863563 = 2795345) B2795345
theorem B1863575 : Blo 1861632 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B1863595 : Blo 1861632 1863595 := bstep (se 1 (by rfl) ⟨1397696, by rfl⟩ : syracuseStep 1863595 = 2795393) B2795393
theorem B1863607 : Blo 1861632 1863607 := bstep (se 1 (by rfl) ⟨1397705, by rfl⟩ : syracuseStep 1863607 = 2795411) B2795411
theorem B4714433 : Blo 1861632 4714433 := bstep (se 2 (by rfl) ⟨1767912, by rfl⟩ : syracuseStep 4714433 = 3535825) B3535825
theorem B3403723 : Blo 1861632 3403723 := bstep (se 1 (by rfl) ⟨2552792, by rfl⟩ : syracuseStep 3403723 = 5105585) B5105585
theorem B1863627 : Blo 1861632 1863627 := bstep (se 1 (by rfl) ⟨1397720, by rfl⟩ : syracuseStep 1863627 = 2795441) B2795441
theorem B8499161 : Blo 1861632 8499161 := bstep (se 2 (by rfl) ⟨3187185, by rfl⟩ : syracuseStep 8499161 = 6374371) B6374371
theorem B15101957 : Blo 1861632 15101957 := bstep (se 4 (by rfl) ⟨1415808, by rfl⟩ : syracuseStep 15101957 = 2831617) B2831617
theorem B4190219 : Blo 1861632 4190219 := bstep (se 1 (by rfl) ⟨3142664, by rfl⟩ : syracuseStep 4190219 = 6285329) B6285329
theorem B7073837 : Blo 1861632 7073837 := bstep (se 3 (by rfl) ⟨1326344, by rfl⟩ : syracuseStep 7073837 = 2652689) B2652689
theorem B4190273 : Blo 1861632 4190273 := bstep (se 2 (by rfl) ⟨1571352, by rfl⟩ : syracuseStep 4190273 = 3142705) B3142705
theorem B6287435 : Blo 1861632 6287435 := bstep (se 1 (by rfl) ⟨4715576, by rfl⟩ : syracuseStep 6287435 = 9431153) B9431153
theorem B3403955 : Blo 1861632 3403955 := bstep (se 1 (by rfl) ⟨2552966, by rfl⟩ : syracuseStep 3403955 = 5105933) B5105933
theorem B3977419 : Blo 1861632 3977419 := bstep (se 1 (by rfl) ⟨2983064, by rfl⟩ : syracuseStep 3977419 = 5966129) B5966129
theorem B5304523 : Blo 1861632 5304523 := bstep (se 1 (by rfl) ⟨3978392, by rfl⟩ : syracuseStep 5304523 = 7956785) B7956785
theorem B4190489 : Blo 1861632 4190489 := bstep (se 2 (by rfl) ⟨1571433, by rfl⟩ : syracuseStep 4190489 = 3142867) B3142867
theorem B2421067 : Blo 1861632 2421067 := bstep (se 1 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 2421067 = 3631601) B3631601
theorem B15102283 : Blo 1861632 15102283 := bstep (se 1 (by rfl) ⟨11326712, by rfl⟩ : syracuseStep 15102283 = 22653425) B22653425
theorem B6287705 : Blo 1861632 6287705 := bstep (se 2 (by rfl) ⟨2357889, by rfl⟩ : syracuseStep 6287705 = 4715779) B4715779
theorem B4190579 : Blo 1861632 4190579 := bstep (se 1 (by rfl) ⟨3142934, by rfl⟩ : syracuseStep 4190579 = 6285869) B6285869
theorem B3535255 : Blo 1861632 3535255 := bstep (se 1 (by rfl) ⟨2651441, by rfl⟩ : syracuseStep 3535255 = 5302883) B5302883
theorem B4190615 : Blo 1861632 4190615 := bstep (se 1 (by rfl) ⟨3142961, by rfl⟩ : syracuseStep 4190615 = 6285923) B6285923
theorem B3142091 : Blo 1861632 3142091 := bstep (se 1 (by rfl) ⟨2356568, by rfl⟩ : syracuseStep 3142091 = 4713137) B4713137
theorem B3977675 : Blo 1861632 3977675 := bstep (se 1 (by rfl) ⟨2983256, by rfl⟩ : syracuseStep 3977675 = 5966513) B5966513
theorem B4714969 : Blo 1861632 4714969 := bstep (se 2 (by rfl) ⟨1768113, by rfl⟩ : syracuseStep 4714969 = 3536227) B3536227
theorem B5304797 : Blo 1861632 5304797 := bstep (se 3 (by rfl) ⟨994649, by rfl⟩ : syracuseStep 5304797 = 1989299) B1989299
theorem B9425483 : Blo 1861632 9425483 := bstep (se 1 (by rfl) ⟨7069112, by rfl⟩ : syracuseStep 9425483 = 14138225) B14138225
theorem B3142219 : Blo 1861632 3142219 := bstep (se 1 (by rfl) ⟨2356664, by rfl⟩ : syracuseStep 3142219 = 4713329) B4713329
theorem B4190795 : Blo 1861632 4190795 := bstep (se 1 (by rfl) ⟨3143096, by rfl⟩ : syracuseStep 4190795 = 6286193) B6286193
theorem B5378653 : Blo 1861632 5378653 := bstep (se 3 (by rfl) ⟨1008497, by rfl⟩ : syracuseStep 5378653 = 2016995) B2016995
theorem B4190849 : Blo 1861632 4190849 := bstep (se 2 (by rfl) ⟨1571568, by rfl⟩ : syracuseStep 4190849 = 3143137) B3143137
theorem B3142361 : Blo 1861632 3142361 := bstep (se 2 (by rfl) ⟨1178385, by rfl⟩ : syracuseStep 3142361 = 2356771) B2356771
theorem B7959313 : Blo 1861632 7959313 := bstep (se 2 (by rfl) ⟨2984742, by rfl⟩ : syracuseStep 7959313 = 5969485) B5969485
theorem B5305139 : Blo 1861632 5305139 := bstep (se 1 (by rfl) ⟨3978854, by rfl⟩ : syracuseStep 5305139 = 7957709) B7957709
theorem B7074611 : Blo 1861632 7074611 := bstep (se 1 (by rfl) ⟨5305958, by rfl⟩ : syracuseStep 7074611 = 10611917) B10611917
theorem B3142489 : Blo 1861632 3142489 := bstep (se 2 (by rfl) ⟨1178433, by rfl⟩ : syracuseStep 3142489 = 2356867) B2356867
theorem B4191065 : Blo 1861632 4191065 := bstep (se 2 (by rfl) ⟨1571649, by rfl⟩ : syracuseStep 4191065 = 3143299) B3143299
theorem B22975409 : Blo 1861632 22975409 := bstep (se 2 (by rfl) ⟨8615778, by rfl⟩ : syracuseStep 22975409 = 17231557) B17231557
theorem B4191155 : Blo 1861632 4191155 := bstep (se 1 (by rfl) ⟨3143366, by rfl⟩ : syracuseStep 4191155 = 6286733) B6286733
theorem B5968819 : Blo 1861632 5968819 := bstep (se 1 (by rfl) ⟨4476614, by rfl⟩ : syracuseStep 5968819 = 8953229) B8953229
theorem B4191191 : Blo 1861632 4191191 := bstep (se 1 (by rfl) ⟨3143393, by rfl⟩ : syracuseStep 4191191 = 6286787) B6286787
theorem B10064857 : Blo 1861632 10064857 := bstep (se 2 (by rfl) ⟨3774321, by rfl⟩ : syracuseStep 10064857 = 7548643) B7548643
theorem B6288407 : Blo 1861632 6288407 := bstep (se 1 (by rfl) ⟨4716305, by rfl⟩ : syracuseStep 6288407 = 9432611) B9432611
theorem B11932717 : Blo 1861632 11932717 := bstep (se 3 (by rfl) ⟨2237384, by rfl⟩ : syracuseStep 11932717 = 4474769) B4474769
theorem B5968961 : Blo 1861632 5968961 := bstep (se 2 (by rfl) ⟨2238360, by rfl⟩ : syracuseStep 5968961 = 4476721) B4476721
theorem B20141131 : Blo 1861632 20141131 := bstep (se 1 (by rfl) ⟨15105848, by rfl⟩ : syracuseStep 20141131 = 30211697) B30211697
theorem B29054045 : Blo 1861632 29054045 := bstep (se 3 (by rfl) ⟨5447633, by rfl⟩ : syracuseStep 29054045 = 10895267) B10895267
theorem B4191371 : Blo 1861632 4191371 := bstep (se 1 (by rfl) ⟨3143528, by rfl⟩ : syracuseStep 4191371 = 6287057) B6287057
theorem B4191425 : Blo 1861632 4191425 := bstep (se 2 (by rfl) ⟨1571784, by rfl⟩ : syracuseStep 4191425 = 3143569) B3143569
theorem B2651339 : Blo 1861632 2651339 := bstep (se 1 (by rfl) ⟨1988504, by rfl⟩ : syracuseStep 2651339 = 3977009) B3977009
theorem B3536075 : Blo 1861632 3536075 := bstep (se 1 (by rfl) ⟨2652056, by rfl⟩ : syracuseStep 3536075 = 5304113) B5304113
theorem B3536129 : Blo 1861632 3536129 := bstep (se 2 (by rfl) ⟨1326048, by rfl⟩ : syracuseStep 3536129 = 2652097) B2652097
theorem B12744029 : Blo 1861632 12744029 := bstep (se 3 (by rfl) ⟨2389505, by rfl⟩ : syracuseStep 12744029 = 4779011) B4779011
theorem B2094475 : Blo 1861632 2094475 := bstep (se 1 (by rfl) ⟨1570856, by rfl⟩ : syracuseStep 2094475 = 3141713) B3141713
theorem B3143063 : Blo 1861632 3143063 := bstep (se 1 (by rfl) ⟨2357297, by rfl⟩ : syracuseStep 3143063 = 4714595) B4714595
theorem B3978649 : Blo 1861632 3978649 := bstep (se 2 (by rfl) ⟨1491993, by rfl⟩ : syracuseStep 3978649 = 2983987) B2983987
theorem B4191641 : Blo 1861632 4191641 := bstep (se 2 (by rfl) ⟨1571865, by rfl⟩ : syracuseStep 4191641 = 3143731) B3143731
theorem B4191731 : Blo 1861632 4191731 := bstep (se 1 (by rfl) ⟨3143798, by rfl⟩ : syracuseStep 4191731 = 6287597) B6287597
theorem B2094583 : Blo 1861632 2094583 := bstep (se 1 (by rfl) ⟨1570937, by rfl⟩ : syracuseStep 2094583 = 3141875) B3141875
theorem B14145029 : Blo 1861632 14145029 := bstep (se 4 (by rfl) ⟨1326096, by rfl⟩ : syracuseStep 14145029 = 2652193) B2652193
theorem B3143191 : Blo 1861632 3143191 := bstep (se 1 (by rfl) ⟨2357393, by rfl⟩ : syracuseStep 3143191 = 4714787) B4714787
theorem B4191767 : Blo 1861632 4191767 := bstep (se 1 (by rfl) ⟨3143825, by rfl⟩ : syracuseStep 4191767 = 6287651) B6287651
theorem B3978803 : Blo 1861632 3978803 := bstep (se 1 (by rfl) ⟨2984102, by rfl⟩ : syracuseStep 3978803 = 5968205) B5968205
theorem B4716083 : Blo 1861632 4716083 := bstep (se 1 (by rfl) ⟨3537062, by rfl⟩ : syracuseStep 4716083 = 7074125) B7074125
theorem B6288947 : Blo 1861632 6288947 := bstep (se 1 (by rfl) ⟨4716710, by rfl⟩ : syracuseStep 6288947 = 9433421) B9433421
theorem B2094763 : Blo 1861632 2094763 := bstep (se 1 (by rfl) ⟨1571072, by rfl⟩ : syracuseStep 2094763 = 3142145) B3142145
theorem B7550657 : Blo 1861632 7550657 := bstep (se 2 (by rfl) ⟨2831496, by rfl⟩ : syracuseStep 7550657 = 5662993) B5662993
theorem B4191947 : Blo 1861632 4191947 := bstep (se 1 (by rfl) ⟨3143960, by rfl⟩ : syracuseStep 4191947 = 6287921) B6287921
theorem B4192001 : Blo 1861632 4192001 := bstep (se 2 (by rfl) ⟨1572000, by rfl⟩ : syracuseStep 4192001 = 3144001) B3144001
theorem B4306699 : Blo 1861632 4306699 := bstep (se 1 (by rfl) ⟨3230024, by rfl⟩ : syracuseStep 4306699 = 6460049) B6460049
theorem B6715153 : Blo 1861632 6715153 := bstep (se 2 (by rfl) ⟨2518182, by rfl⟩ : syracuseStep 6715153 = 5036365) B5036365
theorem B2094871 : Blo 1861632 2094871 := bstep (se 1 (by rfl) ⟨1571153, by rfl⟩ : syracuseStep 2094871 = 3142307) B3142307
theorem B8951597 : Blo 1861632 8951597 := bstep (se 3 (by rfl) ⟨1678424, by rfl⟩ : syracuseStep 8951597 = 3356849) B3356849
theorem B6289217 : Blo 1861632 6289217 := bstep (se 2 (by rfl) ⟨2358456, by rfl⟩ : syracuseStep 6289217 = 4716913) B4716913
theorem B4716377 : Blo 1861632 4716377 := bstep (se 2 (by rfl) ⟨1768641, by rfl⟩ : syracuseStep 4716377 = 3537283) B3537283
theorem B2095051 : Blo 1861632 2095051 := bstep (se 1 (by rfl) ⟨1571288, by rfl⟩ : syracuseStep 2095051 = 3142577) B3142577
theorem B15308761 : Blo 1861632 15308761 := bstep (se 2 (by rfl) ⟨5740785, by rfl⟩ : syracuseStep 15308761 = 11481571) B11481571
theorem B4192217 : Blo 1861632 4192217 := bstep (se 2 (by rfl) ⟨1572081, by rfl⟩ : syracuseStep 4192217 = 3144163) B3144163
theorem B3979315 : Blo 1861632 3979315 := bstep (se 1 (by rfl) ⟨2984486, by rfl⟩ : syracuseStep 3979315 = 5968973) B5968973
theorem B4192307 : Blo 1861632 4192307 := bstep (se 1 (by rfl) ⟨3144230, by rfl⟩ : syracuseStep 4192307 = 6288461) B6288461
theorem B2095159 : Blo 1861632 2095159 := bstep (se 1 (by rfl) ⟨1571369, by rfl⟩ : syracuseStep 2095159 = 3142739) B3142739
theorem B5036107 : Blo 1861632 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B4192343 : Blo 1861632 4192343 := bstep (se 1 (by rfl) ⟨3144257, by rfl⟩ : syracuseStep 4192343 = 6288515) B6288515
theorem B3143819 : Blo 1861632 3143819 := bstep (se 1 (by rfl) ⟨2357864, by rfl⟩ : syracuseStep 3143819 = 4715729) B4715729
theorem B3537047 : Blo 1861632 3537047 := bstep (se 1 (by rfl) ⟨2652785, by rfl⟩ : syracuseStep 3537047 = 5305571) B5305571
theorem B6715543 : Blo 1861632 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B2095339 : Blo 1861632 2095339 := bstep (se 1 (by rfl) ⟨1571504, by rfl⟩ : syracuseStep 2095339 = 3143009) B3143009
theorem B2357515 : Blo 1861632 2357515 := bstep (se 1 (by rfl) ⟨1768136, by rfl⟩ : syracuseStep 2357515 = 3536273) B3536273
theorem B3143947 : Blo 1861632 3143947 := bstep (se 1 (by rfl) ⟨2357960, by rfl⟩ : syracuseStep 3143947 = 4715921) B4715921
theorem B4192523 : Blo 1861632 4192523 := bstep (se 1 (by rfl) ⟨3144392, by rfl⟩ : syracuseStep 4192523 = 6288785) B6288785
theorem B9427265 : Blo 1861632 9427265 := bstep (se 2 (by rfl) ⟨3535224, by rfl⟩ : syracuseStep 9427265 = 7070449) B7070449
theorem B4192577 : Blo 1861632 4192577 := bstep (se 2 (by rfl) ⟨1572216, by rfl⟩ : syracuseStep 4192577 = 3144433) B3144433
theorem B2095447 : Blo 1861632 2095447 := bstep (se 1 (by rfl) ⟨1571585, by rfl⟩ : syracuseStep 2095447 = 3143171) B3143171
theorem B6289757 : Blo 1861632 6289757 := bstep (se 3 (by rfl) ⟨1179329, by rfl⟩ : syracuseStep 6289757 = 2358659) B2358659
theorem B1988983 : Blo 1861632 1988983 := bstep (se 1 (by rfl) ⟨1491737, by rfl⟩ : syracuseStep 1988983 = 2983475) B2983475
theorem B3144089 : Blo 1861632 3144089 := bstep (se 2 (by rfl) ⟨1179033, by rfl⟩ : syracuseStep 3144089 = 2358067) B2358067
theorem B3774899 : Blo 1861632 3774899 := bstep (se 1 (by rfl) ⟨2831174, by rfl⟩ : syracuseStep 3774899 = 5662349) B5662349
theorem B2095627 : Blo 1861632 2095627 := bstep (se 1 (by rfl) ⟨1571720, by rfl⟩ : syracuseStep 2095627 = 3143441) B3143441
theorem B6806039 : Blo 1861632 6806039 := bstep (se 1 (by rfl) ⟨5104529, by rfl⟩ : syracuseStep 6806039 = 10209059) B10209059
theorem B3144217 : Blo 1861632 3144217 := bstep (se 2 (by rfl) ⟨1179081, by rfl⟩ : syracuseStep 3144217 = 2358163) B2358163
theorem B4192793 : Blo 1861632 4192793 := bstep (se 2 (by rfl) ⟨1572297, by rfl⟩ : syracuseStep 4192793 = 3144595) B3144595
theorem B4192883 : Blo 1861632 4192883 := bstep (se 1 (by rfl) ⟨3144662, by rfl⟩ : syracuseStep 4192883 = 6289325) B6289325
theorem B2095735 : Blo 1861632 2095735 := bstep (se 1 (by rfl) ⟨1571801, by rfl⟩ : syracuseStep 2095735 = 3143603) B3143603
theorem B4192919 : Blo 1861632 4192919 := bstep (se 1 (by rfl) ⟨3144689, by rfl⟩ : syracuseStep 4192919 = 6289379) B6289379
theorem B3537587 : Blo 1861632 3537587 := bstep (se 1 (by rfl) ⟨2653190, by rfl⟩ : syracuseStep 3537587 = 5306381) B5306381
theorem B8493761 : Blo 1861632 8493761 := bstep (se 2 (by rfl) ⟨3185160, by rfl⟩ : syracuseStep 8493761 = 6370321) B6370321
theorem B3979991 : Blo 1861632 3979991 := bstep (se 1 (by rfl) ⟨2984993, by rfl⟩ : syracuseStep 3979991 = 5969987) B5969987
theorem B3980033 : Blo 1861632 3980033 := bstep (se 2 (by rfl) ⟨1492512, by rfl⟩ : syracuseStep 3980033 = 2985025) B2985025
theorem B2095915 : Blo 1861632 2095915 := bstep (se 1 (by rfl) ⟨1571936, by rfl⟩ : syracuseStep 2095915 = 3143873) B3143873
theorem B7068491 : Blo 1861632 7068491 := bstep (se 1 (by rfl) ⟨5301368, by rfl⟩ : syracuseStep 7068491 = 10602737) B10602737
theorem B4193099 : Blo 1861632 4193099 := bstep (se 1 (by rfl) ⟨3144824, by rfl⟩ : syracuseStep 4193099 = 6289649) B6289649
theorem B7068505 : Blo 1861632 7068505 := bstep (se 2 (by rfl) ⟨2650689, by rfl⟩ : syracuseStep 7068505 = 5301379) B5301379
theorem B4193153 : Blo 1861632 4193153 := bstep (se 2 (by rfl) ⟨1572432, by rfl⟩ : syracuseStep 4193153 = 3144865) B3144865
theorem B2096023 : Blo 1861632 2096023 := bstep (se 1 (by rfl) ⟨1572017, by rfl⟩ : syracuseStep 2096023 = 3144035) B3144035
theorem B17906609 : Blo 1861632 17906609 := bstep (se 2 (by rfl) ⟨6714978, by rfl⟩ : syracuseStep 17906609 = 13429957) B13429957
theorem B4422593 : Blo 1861632 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B2792459 : Blo 1861632 2792459 := bstep (se 1 (by rfl) ⟨2094344, by rfl⟩ : syracuseStep 2792459 = 4188689) B4188689
theorem B2792471 : Blo 1861632 2792471 := bstep (se 1 (by rfl) ⟨2094353, by rfl⟩ : syracuseStep 2792471 = 4188707) B4188707
theorem B2096203 : Blo 1861632 2096203 := bstep (se 1 (by rfl) ⟨1572152, by rfl⟩ : syracuseStep 2096203 = 3144305) B3144305
theorem B3144791 : Blo 1861632 3144791 := bstep (se 1 (by rfl) ⟨2358593, by rfl⟩ : syracuseStep 3144791 = 4717187) B4717187
theorem B2792537 : Blo 1861632 2792537 := bstep (se 2 (by rfl) ⟨1047201, by rfl⟩ : syracuseStep 2792537 = 2094403) B2094403
theorem B1989803 : Blo 1861632 1989803 := bstep (se 1 (by rfl) ⟨1492352, by rfl⟩ : syracuseStep 1989803 = 2984705) B2984705
theorem B2096311 : Blo 1861632 2096311 := bstep (se 1 (by rfl) ⟨1572233, by rfl⟩ : syracuseStep 2096311 = 3144467) B3144467
theorem B2792651 : Blo 1861632 2792651 := bstep (se 1 (by rfl) ⟨2094488, by rfl⟩ : syracuseStep 2792651 = 4188977) B4188977
theorem B2792663 : Blo 1861632 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B2358487 : Blo 1861632 2358487 := bstep (se 1 (by rfl) ⟨1768865, by rfl⟩ : syracuseStep 2358487 = 3537731) B3537731
theorem B2792729 : Blo 1861632 2792729 := bstep (se 2 (by rfl) ⟨1047273, by rfl⟩ : syracuseStep 2792729 = 2094547) B2094547
theorem B7953709 : Blo 1861632 7953709 := bstep (se 3 (by rfl) ⟨1491320, by rfl⟩ : syracuseStep 7953709 = 2982641) B2982641
theorem B1989931 : Blo 1861632 1989931 := bstep (se 1 (by rfl) ⟨1492448, by rfl⟩ : syracuseStep 1989931 = 2984897) B2984897
theorem B2096491 : Blo 1861632 2096491 := bstep (se 1 (by rfl) ⟨1572368, by rfl⟩ : syracuseStep 2096491 = 3144737) B3144737
theorem B2792843 : Blo 1861632 2792843 := bstep (se 1 (by rfl) ⟨2094632, by rfl⟩ : syracuseStep 2792843 = 4189265) B4189265
theorem B2792855 : Blo 1861632 2792855 := bstep (se 1 (by rfl) ⟨2094641, by rfl⟩ : syracuseStep 2792855 = 4189283) B4189283
theorem B11935127 : Blo 1861632 11935127 := bstep (se 1 (by rfl) ⟨8951345, by rfl⟩ : syracuseStep 11935127 = 17902691) B17902691
theorem B15916439 : Blo 1861632 15916439 := bstep (se 1 (by rfl) ⟨11937329, by rfl⟩ : syracuseStep 15916439 = 23874659) B23874659
theorem B2792921 : Blo 1861632 2792921 := bstep (se 2 (by rfl) ⟨1047345, by rfl⟩ : syracuseStep 2792921 = 2094691) B2094691
theorem B2793035 : Blo 1861632 2793035 := bstep (se 1 (by rfl) ⟨2094776, by rfl⟩ : syracuseStep 2793035 = 4189553) B4189553
theorem B2793047 : Blo 1861632 2793047 := bstep (se 1 (by rfl) ⟨2094785, by rfl⟩ : syracuseStep 2793047 = 4189571) B4189571
theorem B3358297 : Blo 1861632 3358297 := bstep (se 2 (by rfl) ⟨1259361, by rfl⟩ : syracuseStep 3358297 = 2518723) B2518723
theorem B7954051 : Blo 1861632 7954051 := bstep (se 1 (by rfl) ⟨5965538, by rfl⟩ : syracuseStep 7954051 = 11931077) B11931077
theorem B2793113 : Blo 1861632 2793113 := bstep (se 2 (by rfl) ⟨1047417, by rfl⟩ : syracuseStep 2793113 = 2094835) B2094835
theorem B12738227 : Blo 1861632 12738227 := bstep (se 1 (by rfl) ⟨9553670, by rfl⟩ : syracuseStep 12738227 = 19107341) B19107341
theorem B3776203 : Blo 1861632 3776203 := bstep (se 1 (by rfl) ⟨2832152, by rfl⟩ : syracuseStep 3776203 = 5664305) B5664305
theorem B2793227 : Blo 1861632 2793227 := bstep (se 1 (by rfl) ⟨2094920, by rfl⟩ : syracuseStep 2793227 = 4189841) B4189841
theorem B7069463 : Blo 1861632 7069463 := bstep (se 1 (by rfl) ⟨5302097, by rfl⟩ : syracuseStep 7069463 = 10604195) B10604195
theorem B2793239 : Blo 1861632 2793239 := bstep (se 1 (by rfl) ⟨2094929, by rfl⟩ : syracuseStep 2793239 = 4189859) B4189859
theorem B6045529 : Blo 1861632 6045529 := bstep (se 2 (by rfl) ⟨2267073, by rfl⟩ : syracuseStep 6045529 = 4534147) B4534147
theorem B2793305 : Blo 1861632 2793305 := bstep (se 2 (by rfl) ⟨1047489, by rfl⟩ : syracuseStep 2793305 = 2094979) B2094979
theorem B14147459 : Blo 1861632 14147459 := bstep (se 1 (by rfl) ⟨10610594, by rfl⟩ : syracuseStep 14147459 = 21221189) B21221189
theorem B2793419 : Blo 1861632 2793419 := bstep (se 1 (by rfl) ⟨2095064, by rfl⟩ : syracuseStep 2793419 = 4190129) B4190129
theorem B4538315 : Blo 1861632 4538315 := bstep (se 1 (by rfl) ⟨3403736, by rfl⟩ : syracuseStep 4538315 = 6807473) B6807473
theorem B2793431 : Blo 1861632 2793431 := bstep (se 1 (by rfl) ⟨2095073, by rfl⟩ : syracuseStep 2793431 = 4190147) B4190147
theorem B10067971 : Blo 1861632 10067971 := bstep (se 1 (by rfl) ⟨7550978, by rfl⟩ : syracuseStep 10067971 = 15101957) B15101957
theorem B2793479 : Blo 1861632 2793479 := bstep (se 1 (by rfl) ⟨2095109, by rfl⟩ : syracuseStep 2793479 = 4190219) B4190219
theorem B2793515 : Blo 1861632 2793515 := bstep (se 1 (by rfl) ⟨2095136, by rfl⟩ : syracuseStep 2793515 = 4190273) B4190273
theorem B2793545 : Blo 1861632 2793545 := bstep (se 2 (by rfl) ⟨1047579, by rfl⟩ : syracuseStep 2793545 = 2095159) B2095159
theorem B2793659 : Blo 1861632 2793659 := bstep (se 1 (by rfl) ⟨2095244, by rfl⟩ : syracuseStep 2793659 = 4190489) B4190489
theorem B8954057 : Blo 1861632 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B2793719 : Blo 1861632 2793719 := bstep (se 1 (by rfl) ⟨2095289, by rfl⟩ : syracuseStep 2793719 = 4190579) B4190579
theorem B2793743 : Blo 1861632 2793743 := bstep (se 1 (by rfl) ⟨2095307, by rfl⟩ : syracuseStep 2793743 = 4190615) B4190615
theorem B2793785 : Blo 1861632 2793785 := bstep (se 2 (by rfl) ⟨1047669, by rfl⟩ : syracuseStep 2793785 = 2095339) B2095339
theorem B6283655 : Blo 1861632 6283655 := bstep (se 1 (by rfl) ⟨4712741, by rfl⟩ : syracuseStep 6283655 = 9425483) B9425483
theorem B2793863 : Blo 1861632 2793863 := bstep (se 1 (by rfl) ⟨2095397, by rfl⟩ : syracuseStep 2793863 = 4190795) B4190795
theorem B2793899 : Blo 1861632 2793899 := bstep (se 1 (by rfl) ⟨2095424, by rfl⟩ : syracuseStep 2793899 = 4190849) B4190849
theorem B3228089 : Blo 1861632 3228089 := bstep (se 2 (by rfl) ⟨1210533, by rfl⟩ : syracuseStep 3228089 = 2421067) B2421067
theorem B20136377 : Blo 1861632 20136377 := bstep (se 2 (by rfl) ⟨7551141, by rfl⟩ : syracuseStep 20136377 = 15102283) B15102283
theorem B2793929 : Blo 1861632 2793929 := bstep (se 2 (by rfl) ⟨1047723, by rfl⟩ : syracuseStep 2793929 = 2095447) B2095447
theorem B9077213 : Blo 1861632 9077213 := bstep (se 3 (by rfl) ⟨1701977, by rfl⟩ : syracuseStep 9077213 = 3403955) B3403955
theorem B7070237 : Blo 1861632 7070237 := bstep (se 3 (by rfl) ⟨1325669, by rfl⟩ : syracuseStep 7070237 = 2651339) B2651339
theorem B9429533 : Blo 1861632 9429533 := bstep (se 3 (by rfl) ⟨1768037, by rfl⟩ : syracuseStep 9429533 = 3536075) B3536075
theorem B2794043 : Blo 1861632 2794043 := bstep (se 1 (by rfl) ⟨2095532, by rfl⟩ : syracuseStep 2794043 = 4191065) B4191065
theorem B4473463 : Blo 1861632 4473463 := bstep (se 1 (by rfl) ⟨3355097, by rfl⟩ : syracuseStep 4473463 = 6710195) B6710195
theorem B2794103 : Blo 1861632 2794103 := bstep (se 1 (by rfl) ⟨2095577, by rfl⟩ : syracuseStep 2794103 = 4191155) B4191155
theorem B2794127 : Blo 1861632 2794127 := bstep (se 1 (by rfl) ⟨2095595, by rfl⟩ : syracuseStep 2794127 = 4191191) B4191191
theorem B52363957 : Blo 1861632 52363957 := bstep (se 5 (by rfl) ⟨2454560, by rfl⟩ : syracuseStep 52363957 = 4909121) B4909121
theorem B2794169 : Blo 1861632 2794169 := bstep (se 2 (by rfl) ⟨1047813, by rfl⟩ : syracuseStep 2794169 = 2095627) B2095627
theorem B15909605 : Blo 1861632 15909605 := bstep (se 4 (by rfl) ⟨1491525, by rfl⟩ : syracuseStep 15909605 = 2983051) B2983051
theorem B6284033 : Blo 1861632 6284033 := bstep (se 2 (by rfl) ⟨2356512, by rfl⟩ : syracuseStep 6284033 = 4713025) B4713025
theorem B2794247 : Blo 1861632 2794247 := bstep (se 1 (by rfl) ⟨2095685, by rfl⟩ : syracuseStep 2794247 = 4191371) B4191371
theorem B2794283 : Blo 1861632 2794283 := bstep (se 1 (by rfl) ⟨2095712, by rfl⟩ : syracuseStep 2794283 = 4191425) B4191425
theorem B2794313 : Blo 1861632 2794313 := bstep (se 2 (by rfl) ⟨1047867, by rfl⟩ : syracuseStep 2794313 = 2095735) B2095735
theorem B8496019 : Blo 1861632 8496019 := bstep (se 1 (by rfl) ⟨6372014, by rfl⟩ : syracuseStep 8496019 = 12744029) B12744029
theorem B60400565 : Blo 1861632 60400565 := bstep (se 5 (by rfl) ⟨2831276, by rfl⟩ : syracuseStep 60400565 = 5662553) B5662553
theorem B2794427 : Blo 1861632 2794427 := bstep (se 1 (by rfl) ⟨2095820, by rfl⟩ : syracuseStep 2794427 = 4191641) B4191641
theorem B2794487 : Blo 1861632 2794487 := bstep (se 1 (by rfl) ⟨2095865, by rfl⟩ : syracuseStep 2794487 = 4191731) B4191731
theorem B9430019 : Blo 1861632 9430019 := bstep (se 1 (by rfl) ⟨7072514, by rfl⟩ : syracuseStep 9430019 = 14145029) B14145029
theorem B2794511 : Blo 1861632 2794511 := bstep (se 1 (by rfl) ⟨2095883, by rfl⟩ : syracuseStep 2794511 = 4191767) B4191767
theorem B2794553 : Blo 1861632 2794553 := bstep (se 2 (by rfl) ⟨1047957, by rfl⟩ : syracuseStep 2794553 = 2095915) B2095915
theorem B2794631 : Blo 1861632 2794631 := bstep (se 1 (by rfl) ⟨2095973, by rfl⟩ : syracuseStep 2794631 = 4191947) B4191947
theorem B2794667 : Blo 1861632 2794667 := bstep (se 1 (by rfl) ⟨2096000, by rfl⟩ : syracuseStep 2794667 = 4192001) B4192001
theorem B7070921 : Blo 1861632 7070921 := bstep (se 2 (by rfl) ⟨2651595, by rfl⟩ : syracuseStep 7070921 = 5303191) B5303191
theorem B2794697 : Blo 1861632 2794697 := bstep (se 2 (by rfl) ⟨1048011, by rfl⟩ : syracuseStep 2794697 = 2096023) B2096023
theorem B13419809 : Blo 1861632 13419809 := bstep (se 2 (by rfl) ⟨5032428, by rfl⟩ : syracuseStep 13419809 = 10064857) B10064857
theorem B15099169 : Blo 1861632 15099169 := bstep (se 2 (by rfl) ⟨5662188, by rfl⟩ : syracuseStep 15099169 = 11324377) B11324377
theorem B2794811 : Blo 1861632 2794811 := bstep (se 1 (by rfl) ⟨2096108, by rfl⟩ : syracuseStep 2794811 = 4192217) B4192217
theorem B2794871 : Blo 1861632 2794871 := bstep (se 1 (by rfl) ⟨2096153, by rfl⟩ : syracuseStep 2794871 = 4192307) B4192307
theorem B2794895 : Blo 1861632 2794895 := bstep (se 1 (by rfl) ⟨2096171, by rfl⟩ : syracuseStep 2794895 = 4192343) B4192343
theorem B11928977 : Blo 1861632 11928977 := bstep (se 2 (by rfl) ⟨4473366, by rfl⟩ : syracuseStep 11928977 = 8946733) B8946733
theorem B15910289 : Blo 1861632 15910289 := bstep (se 2 (by rfl) ⟨5966358, by rfl⟩ : syracuseStep 15910289 = 11932717) B11932717
theorem B26854841 : Blo 1861632 26854841 := bstep (se 2 (by rfl) ⟨10070565, by rfl⟩ : syracuseStep 26854841 = 20141131) B20141131
theorem B2794937 : Blo 1861632 2794937 := bstep (se 2 (by rfl) ⟨1048101, by rfl⟩ : syracuseStep 2794937 = 2096203) B2096203
theorem B2795015 : Blo 1861632 2795015 := bstep (se 1 (by rfl) ⟨2096261, by rfl⟩ : syracuseStep 2795015 = 4192523) B4192523
theorem B6284843 : Blo 1861632 6284843 := bstep (se 1 (by rfl) ⟨4713632, by rfl⟩ : syracuseStep 6284843 = 9427265) B9427265
theorem B2795051 : Blo 1861632 2795051 := bstep (se 1 (by rfl) ⟨2096288, by rfl⟩ : syracuseStep 2795051 = 4192577) B4192577
theorem B2795081 : Blo 1861632 2795081 := bstep (se 2 (by rfl) ⟨1048155, by rfl⟩ : syracuseStep 2795081 = 2096311) B2096311
theorem B2516599 : Blo 1861632 2516599 := bstep (se 1 (by rfl) ⟨1887449, by rfl⟩ : syracuseStep 2516599 = 3774899) B3774899
theorem B2795195 : Blo 1861632 2795195 := bstep (se 1 (by rfl) ⟨2096396, by rfl⟩ : syracuseStep 2795195 = 4192793) B4192793
theorem B2795255 : Blo 1861632 2795255 := bstep (se 1 (by rfl) ⟨2096441, by rfl⟩ : syracuseStep 2795255 = 4192883) B4192883
theorem B2795279 : Blo 1861632 2795279 := bstep (se 1 (by rfl) ⟨2096459, by rfl⟩ : syracuseStep 2795279 = 4192919) B4192919
theorem B2795321 : Blo 1861632 2795321 := bstep (se 2 (by rfl) ⟨1048245, by rfl⟩ : syracuseStep 2795321 = 2096491) B2096491
theorem B4712327 : Blo 1861632 4712327 := bstep (se 1 (by rfl) ⟨3534245, by rfl⟩ : syracuseStep 4712327 = 7068491) B7068491
theorem B2795399 : Blo 1861632 2795399 := bstep (se 1 (by rfl) ⟨2096549, by rfl⟩ : syracuseStep 2795399 = 4193099) B4193099
theorem B2795435 : Blo 1861632 2795435 := bstep (se 1 (by rfl) ⟨2096576, by rfl⟩ : syracuseStep 2795435 = 4193153) B4193153
theorem B4712377 : Blo 1861632 4712377 := bstep (se 2 (by rfl) ⟨1767141, by rfl⟩ : syracuseStep 4712377 = 3534283) B3534283
theorem B1861639 : Blo 1861632 1861639 := bstep (se 1 (by rfl) ⟨1396229, by rfl⟩ : syracuseStep 1861639 = 2792459) B2792459
theorem B1861647 : Blo 1861632 1861647 := bstep (se 1 (by rfl) ⟨1396235, by rfl⟩ : syracuseStep 1861647 = 2792471) B2792471
theorem B1861691 : Blo 1861632 1861691 := bstep (se 1 (by rfl) ⟨1396268, by rfl⟩ : syracuseStep 1861691 = 2792537) B2792537
theorem B1861767 : Blo 1861632 1861767 := bstep (se 1 (by rfl) ⟨1396325, by rfl⟩ : syracuseStep 1861767 = 2792651) B2792651
theorem B1861775 : Blo 1861632 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B1861819 : Blo 1861632 1861819 := bstep (se 1 (by rfl) ⟨1396364, by rfl⟩ : syracuseStep 1861819 = 2792729) B2792729
theorem B1861895 : Blo 1861632 1861895 := bstep (se 1 (by rfl) ⟨1396421, by rfl⟩ : syracuseStep 1861895 = 2792843) B2792843
theorem B1861903 : Blo 1861632 1861903 := bstep (se 1 (by rfl) ⟨1396427, by rfl⟩ : syracuseStep 1861903 = 2792855) B2792855
theorem B7956751 : Blo 1861632 7956751 := bstep (se 1 (by rfl) ⟨5967563, by rfl⟩ : syracuseStep 7956751 = 11935127) B11935127
theorem B10610959 : Blo 1861632 10610959 := bstep (se 1 (by rfl) ⟨7958219, by rfl⟩ : syracuseStep 10610959 = 15916439) B15916439
theorem B1861947 : Blo 1861632 1861947 := bstep (se 1 (by rfl) ⟨1396460, by rfl⟩ : syracuseStep 1861947 = 2792921) B2792921
theorem B1862023 : Blo 1861632 1862023 := bstep (se 1 (by rfl) ⟨1396517, by rfl⟩ : syracuseStep 1862023 = 2793035) B2793035
theorem B1862031 : Blo 1861632 1862031 := bstep (se 1 (by rfl) ⟨1396523, by rfl⟩ : syracuseStep 1862031 = 2793047) B2793047
theorem B11930003 : Blo 1861632 11930003 := bstep (se 1 (by rfl) ⟨8947502, by rfl⟩ : syracuseStep 11930003 = 17895005) B17895005
theorem B15911315 : Blo 1861632 15911315 := bstep (se 1 (by rfl) ⟨11933486, by rfl⟩ : syracuseStep 15911315 = 23866973) B23866973
theorem B21219731 : Blo 1861632 21219731 := bstep (se 1 (by rfl) ⟨15914798, by rfl⟩ : syracuseStep 21219731 = 31829597) B31829597
theorem B1862075 : Blo 1861632 1862075 := bstep (se 1 (by rfl) ⟨1396556, by rfl⟩ : syracuseStep 1862075 = 2793113) B2793113
theorem B1862151 : Blo 1861632 1862151 := bstep (se 1 (by rfl) ⟨1396613, by rfl⟩ : syracuseStep 1862151 = 2793227) B2793227
theorem B4246031 : Blo 1861632 4246031 := bstep (se 1 (by rfl) ⟨3184523, by rfl⟩ : syracuseStep 4246031 = 6369047) B6369047
theorem B4712975 : Blo 1861632 4712975 := bstep (se 1 (by rfl) ⟨3534731, by rfl⟩ : syracuseStep 4712975 = 7069463) B7069463
theorem B1862159 : Blo 1861632 1862159 := bstep (se 1 (by rfl) ⟨1396619, by rfl⟩ : syracuseStep 1862159 = 2793239) B2793239
theorem B12102173 : Blo 1861632 12102173 := bstep (se 3 (by rfl) ⟨2269157, by rfl⟩ : syracuseStep 12102173 = 4538315) B4538315
theorem B1862203 : Blo 1861632 1862203 := bstep (se 1 (by rfl) ⟨1396652, by rfl⟩ : syracuseStep 1862203 = 2793305) B2793305
theorem B9431639 : Blo 1861632 9431639 := bstep (se 1 (by rfl) ⟨7073729, by rfl⟩ : syracuseStep 9431639 = 14147459) B14147459
theorem B1862279 : Blo 1861632 1862279 := bstep (se 1 (by rfl) ⟨1396709, by rfl⟩ : syracuseStep 1862279 = 2793419) B2793419
theorem B1862287 : Blo 1861632 1862287 := bstep (se 1 (by rfl) ⟨1396715, by rfl⟩ : syracuseStep 1862287 = 2793431) B2793431
theorem B1862331 : Blo 1861632 1862331 := bstep (se 1 (by rfl) ⟨1396748, by rfl⟩ : syracuseStep 1862331 = 2793497) B2793497
theorem B1862407 : Blo 1861632 1862407 := bstep (se 1 (by rfl) ⟨1396805, by rfl⟩ : syracuseStep 1862407 = 2793611) B2793611
theorem B1862415 : Blo 1861632 1862415 := bstep (se 1 (by rfl) ⟨1396811, by rfl⟩ : syracuseStep 1862415 = 2793623) B2793623
theorem B1862459 : Blo 1861632 1862459 := bstep (se 1 (by rfl) ⟨1396844, by rfl⟩ : syracuseStep 1862459 = 2793689) B2793689
theorem B6286139 : Blo 1861632 6286139 := bstep (se 1 (by rfl) ⟨4714604, by rfl⟩ : syracuseStep 6286139 = 9429209) B9429209
theorem B1862535 : Blo 1861632 1862535 := bstep (se 1 (by rfl) ⟨1396901, by rfl⟩ : syracuseStep 1862535 = 2793803) B2793803
theorem B1862543 : Blo 1861632 1862543 := bstep (se 1 (by rfl) ⟨1396907, by rfl⟩ : syracuseStep 1862543 = 2793815) B2793815
theorem B6712211 : Blo 1861632 6712211 := bstep (se 1 (by rfl) ⟨5034158, by rfl⟩ : syracuseStep 6712211 = 10068317) B10068317
theorem B3976121 : Blo 1861632 3976121 := bstep (se 2 (by rfl) ⟨1491045, by rfl⟩ : syracuseStep 3976121 = 2982091) B2982091
theorem B5303225 : Blo 1861632 5303225 := bstep (se 2 (by rfl) ⟨1988709, by rfl⟩ : syracuseStep 5303225 = 3977419) B3977419
theorem B1862587 : Blo 1861632 1862587 := bstep (se 1 (by rfl) ⟨1396940, by rfl⟩ : syracuseStep 1862587 = 2793881) B2793881
theorem B7072697 : Blo 1861632 7072697 := bstep (se 2 (by rfl) ⟨2652261, by rfl⟩ : syracuseStep 7072697 = 5304523) B5304523
theorem B1862663 : Blo 1861632 1862663 := bstep (se 1 (by rfl) ⟨1396997, by rfl⟩ : syracuseStep 1862663 = 2793995) B2793995
theorem B1862671 : Blo 1861632 1862671 := bstep (se 1 (by rfl) ⟨1397003, by rfl⟩ : syracuseStep 1862671 = 2794007) B2794007
theorem B9563159 : Blo 1861632 9563159 := bstep (se 1 (by rfl) ⟨7172369, by rfl⟩ : syracuseStep 9563159 = 14344739) B14344739
theorem B5303339 : Blo 1861632 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B1862715 : Blo 1861632 1862715 := bstep (se 1 (by rfl) ⟨1397036, by rfl⟩ : syracuseStep 1862715 = 2794073) B2794073
theorem B9432125 : Blo 1861632 9432125 := bstep (se 3 (by rfl) ⟨1768523, by rfl⟩ : syracuseStep 9432125 = 3537047) B3537047
theorem B4189319 : Blo 1861632 4189319 := bstep (se 1 (by rfl) ⟨3141989, by rfl⟩ : syracuseStep 4189319 = 6283979) B6283979
theorem B1862791 : Blo 1861632 1862791 := bstep (se 1 (by rfl) ⟨1397093, by rfl⟩ : syracuseStep 1862791 = 2794187) B2794187
theorem B1862799 : Blo 1861632 1862799 := bstep (se 1 (by rfl) ⟨1397099, by rfl⟩ : syracuseStep 1862799 = 2794199) B2794199
theorem B1862843 : Blo 1861632 1862843 := bstep (se 1 (by rfl) ⟨1397132, by rfl⟩ : syracuseStep 1862843 = 2794265) B2794265
theorem B4713673 : Blo 1861632 4713673 := bstep (se 2 (by rfl) ⟨1767627, by rfl⟩ : syracuseStep 4713673 = 3535255) B3535255
theorem B1862919 : Blo 1861632 1862919 := bstep (se 1 (by rfl) ⟨1397189, by rfl⟩ : syracuseStep 1862919 = 2794379) B2794379
theorem B1862927 : Blo 1861632 1862927 := bstep (se 1 (by rfl) ⟨1397195, by rfl⟩ : syracuseStep 1862927 = 2794391) B2794391
theorem B6286625 : Blo 1861632 6286625 := bstep (se 2 (by rfl) ⟨2357484, by rfl⟩ : syracuseStep 6286625 = 4714969) B4714969
theorem B4189499 : Blo 1861632 4189499 := bstep (se 1 (by rfl) ⟨3142124, by rfl⟩ : syracuseStep 4189499 = 6284249) B6284249
theorem B1862971 : Blo 1861632 1862971 := bstep (se 1 (by rfl) ⟨1397228, by rfl⟩ : syracuseStep 1862971 = 2794457) B2794457
theorem B4713815 : Blo 1861632 4713815 := bstep (se 1 (by rfl) ⟨3535361, by rfl⟩ : syracuseStep 4713815 = 7070723) B7070723
theorem B1863047 : Blo 1861632 1863047 := bstep (se 1 (by rfl) ⟨1397285, by rfl⟩ : syracuseStep 1863047 = 2794571) B2794571
theorem B1863055 : Blo 1861632 1863055 := bstep (se 1 (by rfl) ⟨1397291, by rfl⟩ : syracuseStep 1863055 = 2794583) B2794583
theorem B19369363 : Blo 1861632 19369363 := bstep (se 1 (by rfl) ⟨14527022, by rfl⟩ : syracuseStep 19369363 = 29054045) B29054045
theorem B4189625 : Blo 1861632 4189625 := bstep (se 2 (by rfl) ⟨1571109, by rfl⟩ : syracuseStep 4189625 = 3142219) B3142219
theorem B1863099 : Blo 1861632 1863099 := bstep (se 1 (by rfl) ⟨1397324, by rfl⟩ : syracuseStep 1863099 = 2794649) B2794649
theorem B1863175 : Blo 1861632 1863175 := bstep (se 1 (by rfl) ⟨1397381, by rfl⟩ : syracuseStep 1863175 = 2794763) B2794763
theorem B10612235 : Blo 1861632 10612235 := bstep (se 1 (by rfl) ⟨7959176, by rfl⟩ : syracuseStep 10612235 = 15918353) B15918353
theorem B1863183 : Blo 1861632 1863183 := bstep (se 1 (by rfl) ⟨1397387, by rfl⟩ : syracuseStep 1863183 = 2794775) B2794775
theorem B1863227 : Blo 1861632 1863227 := bstep (se 1 (by rfl) ⟨1397420, by rfl⟩ : syracuseStep 1863227 = 2794841) B2794841
theorem B7958083 : Blo 1861632 7958083 := bstep (se 1 (by rfl) ⟨5968562, by rfl⟩ : syracuseStep 7958083 = 11937125) B11937125
theorem B1863303 : Blo 1861632 1863303 := bstep (se 1 (by rfl) ⟨1397477, by rfl⟩ : syracuseStep 1863303 = 2794955) B2794955
theorem B1863311 : Blo 1861632 1863311 := bstep (se 1 (by rfl) ⟨1397483, by rfl⟩ : syracuseStep 1863311 = 2794967) B2794967
theorem B21507763 : Blo 1861632 21507763 := bstep (se 1 (by rfl) ⟨16130822, by rfl⟩ : syracuseStep 21507763 = 32261645) B32261645
theorem B1863355 : Blo 1861632 1863355 := bstep (se 1 (by rfl) ⟨1397516, by rfl⟩ : syracuseStep 1863355 = 2795033) B2795033
theorem B10612417 : Blo 1861632 10612417 := bstep (se 2 (by rfl) ⟨3979656, by rfl⟩ : syracuseStep 10612417 = 7959313) B7959313
theorem B20139749 : Blo 1861632 20139749 := bstep (se 4 (by rfl) ⟨1888101, by rfl⟩ : syracuseStep 20139749 = 3776203) B3776203
theorem B1863431 : Blo 1861632 1863431 := bstep (se 1 (by rfl) ⟨1397573, by rfl⟩ : syracuseStep 1863431 = 2795147) B2795147
theorem B4189967 : Blo 1861632 4189967 := bstep (se 1 (by rfl) ⟨3142475, by rfl⟩ : syracuseStep 4189967 = 6284951) B6284951
theorem B4779791 : Blo 1861632 4779791 := bstep (se 1 (by rfl) ⟨3584843, by rfl⟩ : syracuseStep 4779791 = 7169687) B7169687
theorem B1863439 : Blo 1861632 1863439 := bstep (se 1 (by rfl) ⟨1397579, by rfl⟩ : syracuseStep 1863439 = 2795159) B2795159
theorem B9424673 : Blo 1861632 9424673 := bstep (se 2 (by rfl) ⟨3534252, by rfl⟩ : syracuseStep 9424673 = 7068505) B7068505
theorem B4189985 : Blo 1861632 4189985 := bstep (se 2 (by rfl) ⟨1571244, by rfl⟩ : syracuseStep 4189985 = 3142489) B3142489
theorem B5033771 : Blo 1861632 5033771 := bstep (se 1 (by rfl) ⟨3775328, by rfl⟩ : syracuseStep 5033771 = 7550657) B7550657
theorem B1863483 : Blo 1861632 1863483 := bstep (se 1 (by rfl) ⟨1397612, by rfl⟩ : syracuseStep 1863483 = 2795225) B2795225
theorem B5967731 : Blo 1861632 5967731 := bstep (se 1 (by rfl) ⟨4475798, by rfl⟩ : syracuseStep 5967731 = 8951597) B8951597
theorem B6287219 : Blo 1861632 6287219 := bstep (se 1 (by rfl) ⟨4715414, by rfl⟩ : syracuseStep 6287219 = 9430829) B9430829
theorem B1863559 : Blo 1861632 1863559 := bstep (se 1 (by rfl) ⟨1397669, by rfl⟩ : syracuseStep 1863559 = 2795339) B2795339
theorem B1863567 : Blo 1861632 1863567 := bstep (se 1 (by rfl) ⟨1397675, by rfl⟩ : syracuseStep 1863567 = 2795351) B2795351
theorem B5967769 : Blo 1861632 5967769 := bstep (se 2 (by rfl) ⟨2237913, by rfl⟩ : syracuseStep 5967769 = 4475827) B4475827
theorem B7958425 : Blo 1861632 7958425 := bstep (se 2 (by rfl) ⟨2984409, by rfl⟩ : syracuseStep 7958425 = 5968819) B5968819
theorem B1863611 : Blo 1861632 1863611 := bstep (se 1 (by rfl) ⟨1397708, by rfl⟩ : syracuseStep 1863611 = 2795417) B2795417
theorem B18149437 : Blo 1861632 18149437 := bstep (se 3 (by rfl) ⟨3403019, by rfl⟩ : syracuseStep 18149437 = 6806039) B6806039
theorem B4190327 : Blo 1861632 4190327 := bstep (se 1 (by rfl) ⟨3142745, by rfl⟩ : syracuseStep 4190327 = 6285491) B6285491
theorem B3141767 : Blo 1861632 3141767 := bstep (se 1 (by rfl) ⟨2356325, by rfl⟩ : syracuseStep 3141767 = 4712651) B4712651
theorem B3584135 : Blo 1861632 3584135 := bstep (se 1 (by rfl) ⟨2688101, by rfl⟩ : syracuseStep 3584135 = 5376203) B5376203
theorem B5304467 : Blo 1861632 5304467 := bstep (se 1 (by rfl) ⟨3978350, by rfl⟩ : syracuseStep 5304467 = 7956701) B7956701
theorem B4190507 : Blo 1861632 4190507 := bstep (se 1 (by rfl) ⟨3142880, by rfl⟩ : syracuseStep 4190507 = 6285761) B6285761
theorem B10604945 : Blo 1861632 10604945 := bstep (se 2 (by rfl) ⟨3976854, by rfl⟩ : syracuseStep 10604945 = 7953709) B7953709
theorem B33968605 : Blo 1861632 33968605 := bstep (se 3 (by rfl) ⟨6369113, by rfl⟩ : syracuseStep 33968605 = 12738227) B12738227
theorem B3977743 : Blo 1861632 3977743 := bstep (se 1 (by rfl) ⟨2983307, by rfl⟩ : syracuseStep 3977743 = 5966615) B5966615
theorem B3977761 : Blo 1861632 3977761 := bstep (se 2 (by rfl) ⟨1491660, by rfl⟩ : syracuseStep 3977761 = 2983321) B2983321
theorem B5304865 : Blo 1861632 5304865 := bstep (se 2 (by rfl) ⟨1989324, by rfl⟩ : syracuseStep 5304865 = 3978649) B3978649
theorem B4190867 : Blo 1861632 4190867 := bstep (se 1 (by rfl) ⟨3143150, by rfl⟩ : syracuseStep 4190867 = 6286301) B6286301
theorem B4190921 : Blo 1861632 4190921 := bstep (se 2 (by rfl) ⟨1571595, by rfl⟩ : syracuseStep 4190921 = 3143191) B3143191
theorem B17896153 : Blo 1861632 17896153 := bstep (se 2 (by rfl) ⟨6711057, by rfl⟩ : syracuseStep 17896153 = 13422115) B13422115
theorem B9425645 : Blo 1861632 9425645 := bstep (se 3 (by rfl) ⟨1767308, by rfl⟩ : syracuseStep 9425645 = 3534617) B3534617
theorem B3142415 : Blo 1861632 3142415 := bstep (se 1 (by rfl) ⟨2356811, by rfl⟩ : syracuseStep 3142415 = 4713623) B4713623
theorem B4477729 : Blo 1861632 4477729 := bstep (se 2 (by rfl) ⟨1679148, by rfl⟩ : syracuseStep 4477729 = 3358297) B3358297
theorem B9433907 : Blo 1861632 9433907 := bstep (se 1 (by rfl) ⟨7075430, by rfl⟩ : syracuseStep 9433907 = 14150861) B14150861
theorem B10064729 : Blo 1861632 10064729 := bstep (se 2 (by rfl) ⟨3774273, by rfl⟩ : syracuseStep 10064729 = 7548547) B7548547
theorem B10605401 : Blo 1861632 10605401 := bstep (se 2 (by rfl) ⟨3977025, by rfl⟩ : syracuseStep 10605401 = 7954051) B7954051
theorem B3978119 : Blo 1861632 3978119 := bstep (se 1 (by rfl) ⟨2983589, by rfl⟩ : syracuseStep 3978119 = 5967179) B5967179
theorem B16135255 : Blo 1861632 16135255 := bstep (se 1 (by rfl) ⟨12101441, by rfl⟩ : syracuseStep 16135255 = 24202883) B24202883
theorem B9434231 : Blo 1861632 9434231 := bstep (se 1 (by rfl) ⟨7075673, by rfl⟩ : syracuseStep 9434231 = 14151347) B14151347
theorem B20411681 : Blo 1861632 20411681 := bstep (se 2 (by rfl) ⟨7654380, by rfl⟩ : syracuseStep 20411681 = 15308761) B15308761
theorem B3142955 : Blo 1861632 3142955 := bstep (se 1 (by rfl) ⟨2357216, by rfl⟩ : syracuseStep 3142955 = 4714433) B4714433
theorem B5666107 : Blo 1861632 5666107 := bstep (se 1 (by rfl) ⟨4249580, by rfl⟩ : syracuseStep 5666107 = 8499161) B8499161
theorem B4715891 : Blo 1861632 4715891 := bstep (se 1 (by rfl) ⟨3536918, by rfl⟩ : syracuseStep 4715891 = 7073837) B7073837
theorem B4191623 : Blo 1861632 4191623 := bstep (se 1 (by rfl) ⟨3143717, by rfl⟩ : syracuseStep 4191623 = 6287435) B6287435
theorem B5305753 : Blo 1861632 5305753 := bstep (se 2 (by rfl) ⟨1989657, by rfl⟩ : syracuseStep 5305753 = 3979315) B3979315
theorem B6714809 : Blo 1861632 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B9426455 : Blo 1861632 9426455 := bstep (se 1 (by rfl) ⟨7069841, by rfl⟩ : syracuseStep 9426455 = 14139683) B14139683
theorem B4191803 : Blo 1861632 4191803 := bstep (se 1 (by rfl) ⟨3143852, by rfl⟩ : syracuseStep 4191803 = 6287705) B6287705
theorem B1988231 : Blo 1861632 1988231 := bstep (se 1 (by rfl) ⟨1491173, by rfl⟩ : syracuseStep 1988231 = 2982347) B2982347
theorem B2094727 : Blo 1861632 2094727 := bstep (se 1 (by rfl) ⟨1571045, by rfl⟩ : syracuseStep 2094727 = 3142091) B3142091
theorem B2651783 : Blo 1861632 2651783 := bstep (se 1 (by rfl) ⟨1988837, by rfl⟩ : syracuseStep 2651783 = 3977675) B3977675
theorem B3536531 : Blo 1861632 3536531 := bstep (se 1 (by rfl) ⟨2652398, by rfl⟩ : syracuseStep 3536531 = 5304797) B5304797
theorem B3143353 : Blo 1861632 3143353 := bstep (se 2 (by rfl) ⟨1178757, by rfl⟩ : syracuseStep 3143353 = 2357515) B2357515
theorem B4191929 : Blo 1861632 4191929 := bstep (se 2 (by rfl) ⟨1571973, by rfl⟩ : syracuseStep 4191929 = 3143947) B3143947
theorem B5740303 : Blo 1861632 5740303 := bstep (se 1 (by rfl) ⟨4305227, by rfl⟩ : syracuseStep 5740303 = 8610455) B8610455
theorem B13424399 : Blo 1861632 13424399 := bstep (se 1 (by rfl) ⟨10068299, by rfl⟩ : syracuseStep 13424399 = 20136599) B20136599
theorem B5306141 : Blo 1861632 5306141 := bstep (se 3 (by rfl) ⟨994901, by rfl⟩ : syracuseStep 5306141 = 1989803) B1989803
theorem B2094907 : Blo 1861632 2094907 := bstep (se 1 (by rfl) ⟨1571180, by rfl⟩ : syracuseStep 2094907 = 3142361) B3142361
theorem B28686149 : Blo 1861632 28686149 := bstep (se 4 (by rfl) ⟨2689326, by rfl⟩ : syracuseStep 28686149 = 5378653) B5378653
theorem B2651977 : Blo 1861632 2651977 := bstep (se 2 (by rfl) ⟨994491, by rfl⟩ : syracuseStep 2651977 = 1988983) B1988983
theorem B3536759 : Blo 1861632 3536759 := bstep (se 1 (by rfl) ⟨2652569, by rfl⟩ : syracuseStep 3536759 = 5305139) B5305139
theorem B4716407 : Blo 1861632 4716407 := bstep (se 1 (by rfl) ⟨3537305, by rfl⟩ : syracuseStep 4716407 = 7074611) B7074611
theorem B15316939 : Blo 1861632 15316939 := bstep (se 1 (by rfl) ⟨11487704, by rfl⟩ : syracuseStep 15316939 = 22975409) B22975409
theorem B4192271 : Blo 1861632 4192271 := bstep (se 1 (by rfl) ⟨3144203, by rfl⟩ : syracuseStep 4192271 = 6288407) B6288407
theorem B4192289 : Blo 1861632 4192289 := bstep (se 2 (by rfl) ⟨1572108, by rfl⟩ : syracuseStep 4192289 = 3144217) B3144217
theorem B3979307 : Blo 1861632 3979307 := bstep (se 1 (by rfl) ⟨2984480, by rfl⟩ : syracuseStep 3979307 = 5968961) B5968961
theorem B2357419 : Blo 1861632 2357419 := bstep (se 1 (by rfl) ⟨1768064, by rfl⟩ : syracuseStep 2357419 = 3536129) B3536129
theorem B2095375 : Blo 1861632 2095375 := bstep (se 1 (by rfl) ⟨1571531, by rfl⟩ : syracuseStep 2095375 = 3143063) B3143063
theorem B1988923 : Blo 1861632 1988923 := bstep (se 1 (by rfl) ⟨1491692, by rfl⟩ : syracuseStep 1988923 = 2983385) B2983385
theorem B2652535 : Blo 1861632 2652535 := bstep (se 1 (by rfl) ⟨1989401, by rfl⟩ : syracuseStep 2652535 = 3978803) B3978803
theorem B3144055 : Blo 1861632 3144055 := bstep (se 1 (by rfl) ⟨2358041, by rfl⟩ : syracuseStep 3144055 = 4716083) B4716083
theorem B4192631 : Blo 1861632 4192631 := bstep (se 1 (by rfl) ⟨3144473, by rfl⟩ : syracuseStep 4192631 = 6288947) B6288947
theorem B8952211 : Blo 1861632 8952211 := bstep (se 1 (by rfl) ⟨6714158, by rfl⟩ : syracuseStep 8952211 = 13428317) B13428317
theorem B14146001 : Blo 1861632 14146001 := bstep (se 2 (by rfl) ⟨5304750, by rfl⟩ : syracuseStep 14146001 = 10609501) B10609501
theorem B4192811 : Blo 1861632 4192811 := bstep (se 1 (by rfl) ⟨3144608, by rfl⟩ : syracuseStep 4192811 = 6289217) B6289217
theorem B3144251 : Blo 1861632 3144251 := bstep (se 1 (by rfl) ⟨2358188, by rfl⟩ : syracuseStep 3144251 = 4716377) B4716377
theorem B22969061 : Blo 1861632 22969061 := bstep (se 4 (by rfl) ⟨2153349, by rfl⟩ : syracuseStep 22969061 = 4306699) B4306699
theorem B2095879 : Blo 1861632 2095879 := bstep (se 1 (by rfl) ⟨1571909, by rfl⟩ : syracuseStep 2095879 = 3143819) B3143819
theorem B40278799 : Blo 1861632 40278799 := bstep (se 1 (by rfl) ⟨30209099, by rfl⟩ : syracuseStep 40278799 = 60418199) B60418199
theorem B20142863 : Blo 1861632 20142863 := bstep (se 1 (by rfl) ⟨15107147, by rfl⟩ : syracuseStep 20142863 = 30214295) B30214295
theorem B5102395 : Blo 1861632 5102395 := bstep (se 1 (by rfl) ⟨3826796, by rfl⟩ : syracuseStep 5102395 = 7653593) B7653593
theorem B7953299 : Blo 1861632 7953299 := bstep (se 1 (by rfl) ⟨5964974, by rfl⟩ : syracuseStep 7953299 = 11929949) B11929949
theorem B4193171 : Blo 1861632 4193171 := bstep (se 1 (by rfl) ⟨3144878, by rfl⟩ : syracuseStep 4193171 = 6289757) B6289757
theorem B2096059 : Blo 1861632 2096059 := bstep (se 1 (by rfl) ⟨1572044, by rfl⟩ : syracuseStep 2096059 = 3144089) B3144089
theorem B3144649 : Blo 1861632 3144649 := bstep (se 2 (by rfl) ⟨1179243, by rfl⟩ : syracuseStep 3144649 = 2358487) B2358487
theorem B40811525 : Blo 1861632 40811525 := bstep (se 4 (by rfl) ⟨3826080, by rfl⟩ : syracuseStep 40811525 = 7652161) B7652161
theorem B2792507 : Blo 1861632 2792507 := bstep (se 1 (by rfl) ⟨2094380, by rfl⟩ : syracuseStep 2792507 = 4188761) B4188761
theorem B2653241 : Blo 1861632 2653241 := bstep (se 2 (by rfl) ⟨994965, by rfl⟩ : syracuseStep 2653241 = 1989931) B1989931
theorem B2792567 : Blo 1861632 2792567 := bstep (se 1 (by rfl) ⟨2094425, by rfl⟩ : syracuseStep 2792567 = 4188851) B4188851
theorem B2358391 : Blo 1861632 2358391 := bstep (se 1 (by rfl) ⟨1768793, by rfl⟩ : syracuseStep 2358391 = 3537587) B3537587
theorem B2792591 : Blo 1861632 2792591 := bstep (se 1 (by rfl) ⟨2094443, by rfl⟩ : syracuseStep 2792591 = 4188887) B4188887
theorem B2653327 : Blo 1861632 2653327 := bstep (se 1 (by rfl) ⟨1989995, by rfl⟩ : syracuseStep 2653327 = 3979991) B3979991
theorem B2653355 : Blo 1861632 2653355 := bstep (se 1 (by rfl) ⟨1990016, by rfl⟩ : syracuseStep 2653355 = 3980033) B3980033
theorem B22650029 : Blo 1861632 22650029 := bstep (se 3 (by rfl) ⟨4246880, by rfl⟩ : syracuseStep 22650029 = 8493761) B8493761
theorem B2792633 : Blo 1861632 2792633 := bstep (se 2 (by rfl) ⟨1047237, by rfl⟩ : syracuseStep 2792633 = 2094475) B2094475
theorem B2792711 : Blo 1861632 2792711 := bstep (se 1 (by rfl) ⟨2094533, by rfl⟩ : syracuseStep 2792711 = 4189067) B4189067
theorem B22666513 : Blo 1861632 22666513 := bstep (se 2 (by rfl) ⟨8499942, by rfl⟩ : syracuseStep 22666513 = 16999885) B16999885
theorem B2792747 : Blo 1861632 2792747 := bstep (se 1 (by rfl) ⟨2094560, by rfl⟩ : syracuseStep 2792747 = 4189121) B4189121
theorem B2948395 : Blo 1861632 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B2792777 : Blo 1861632 2792777 := bstep (se 2 (by rfl) ⟨1047291, by rfl⟩ : syracuseStep 2792777 = 2094583) B2094583
theorem B2096527 : Blo 1861632 2096527 := bstep (se 1 (by rfl) ⟨1572395, by rfl⟩ : syracuseStep 2096527 = 3144791) B3144791
theorem B2792891 : Blo 1861632 2792891 := bstep (se 1 (by rfl) ⟨2094668, by rfl⟩ : syracuseStep 2792891 = 4189337) B4189337
theorem B2792951 : Blo 1861632 2792951 := bstep (se 1 (by rfl) ⟨2094713, by rfl⟩ : syracuseStep 2792951 = 4189427) B4189427
theorem B2792975 : Blo 1861632 2792975 := bstep (se 1 (by rfl) ⟨2094731, by rfl⟩ : syracuseStep 2792975 = 4189463) B4189463
theorem B2793017 : Blo 1861632 2793017 := bstep (se 2 (by rfl) ⟨1047381, by rfl⟩ : syracuseStep 2793017 = 2094763) B2094763
theorem B2801225 : Blo 1861632 2801225 := bstep (se 2 (by rfl) ⟨1050459, by rfl⟩ : syracuseStep 2801225 = 2100919) B2100919
theorem B2793095 : Blo 1861632 2793095 := bstep (se 1 (by rfl) ⟨2094821, by rfl⟩ : syracuseStep 2793095 = 4189643) B4189643
theorem B2793131 : Blo 1861632 2793131 := bstep (se 1 (by rfl) ⟨2094848, by rfl⟩ : syracuseStep 2793131 = 4189697) B4189697
theorem B8953537 : Blo 1861632 8953537 := bstep (se 2 (by rfl) ⟨3357576, by rfl⟩ : syracuseStep 8953537 = 6715153) B6715153
theorem B2793161 : Blo 1861632 2793161 := bstep (se 2 (by rfl) ⟨1047435, by rfl⟩ : syracuseStep 2793161 = 2094871) B2094871
theorem B8060705 : Blo 1861632 8060705 := bstep (se 2 (by rfl) ⟨3022764, by rfl⟩ : syracuseStep 8060705 = 6045529) B6045529
theorem B47750957 : Blo 1861632 47750957 := bstep (se 3 (by rfl) ⟨8953304, by rfl⟩ : syracuseStep 47750957 = 17906609) B17906609
theorem B2793275 : Blo 1861632 2793275 := bstep (se 1 (by rfl) ⟨2094956, by rfl⟩ : syracuseStep 2793275 = 4189913) B4189913
theorem B2793335 : Blo 1861632 2793335 := bstep (se 1 (by rfl) ⟨2095001, by rfl⟩ : syracuseStep 2793335 = 4190003) B4190003
theorem B2793359 : Blo 1861632 2793359 := bstep (se 1 (by rfl) ⟨2095019, by rfl⟩ : syracuseStep 2793359 = 4190039) B4190039
theorem B2793401 : Blo 1861632 2793401 := bstep (se 2 (by rfl) ⟨1047525, by rfl⟩ : syracuseStep 2793401 = 2095051) B2095051
theorem B10608569 : Blo 1861632 10608569 := bstep (se 2 (by rfl) ⟨3978213, by rfl⟩ : syracuseStep 10608569 = 7956427) B7956427
theorem B4538297 : Blo 1861632 4538297 := bstep (se 2 (by rfl) ⟨1701861, by rfl⟩ : syracuseStep 4538297 = 3403723) B3403723
theorem B2793551 : Blo 1861632 2793551 := bstep (se 1 (by rfl) ⟨2095163, by rfl⟩ : syracuseStep 2793551 = 4190327) B4190327
theorem B2793671 : Blo 1861632 2793671 := bstep (se 1 (by rfl) ⟨2095253, by rfl⟩ : syracuseStep 2793671 = 4190507) B4190507
theorem B7069963 : Blo 1861632 7069963 := bstep (se 1 (by rfl) ⟨5302472, by rfl⟩ : syracuseStep 7069963 = 10604945) B10604945
theorem B96796997 : Blo 1861632 96796997 := bstep (se 4 (by rfl) ⟨9074718, by rfl⟩ : syracuseStep 96796997 = 18149437) B18149437
theorem B2793833 : Blo 1861632 2793833 := bstep (se 2 (by rfl) ⟨1047687, by rfl⟩ : syracuseStep 2793833 = 2095375) B2095375
theorem B10609001 : Blo 1861632 10609001 := bstep (se 2 (by rfl) ⟨3978375, by rfl⟩ : syracuseStep 10609001 = 7956751) B7956751
theorem B14147945 : Blo 1861632 14147945 := bstep (se 2 (by rfl) ⟨5305479, by rfl⟩ : syracuseStep 14147945 = 10610959) B10610959
theorem B2793911 : Blo 1861632 2793911 := bstep (se 1 (by rfl) ⟨2095433, by rfl⟩ : syracuseStep 2793911 = 4190867) B4190867
theorem B2793947 : Blo 1861632 2793947 := bstep (se 1 (by rfl) ⟨2095460, by rfl⟩ : syracuseStep 2793947 = 4190921) B4190921
theorem B6283763 : Blo 1861632 6283763 := bstep (se 1 (by rfl) ⟨4712822, by rfl⟩ : syracuseStep 6283763 = 9425645) B9425645
theorem B11936281 : Blo 1861632 11936281 := bstep (se 2 (by rfl) ⟨4476105, by rfl⟩ : syracuseStep 11936281 = 8952211) B8952211
theorem B6709819 : Blo 1861632 6709819 := bstep (se 1 (by rfl) ⟨5032364, by rfl⟩ : syracuseStep 6709819 = 10064729) B10064729
theorem B7070267 : Blo 1861632 7070267 := bstep (se 1 (by rfl) ⟨5302700, by rfl⟩ : syracuseStep 7070267 = 10605401) B10605401
theorem B5964617 : Blo 1861632 5964617 := bstep (se 2 (by rfl) ⟨2236731, by rfl⟩ : syracuseStep 5964617 = 4473463) B4473463
theorem B8946539 : Blo 1861632 8946539 := bstep (se 1 (by rfl) ⟨6709904, by rfl⟩ : syracuseStep 8946539 = 13419809) B13419809
theorem B2794415 : Blo 1861632 2794415 := bstep (se 1 (by rfl) ⟨2095811, by rfl⟩ : syracuseStep 2794415 = 4191623) B4191623
theorem B2794505 : Blo 1861632 2794505 := bstep (se 2 (by rfl) ⟨1047939, by rfl⟩ : syracuseStep 2794505 = 2095879) B2095879
theorem B6284303 : Blo 1861632 6284303 := bstep (se 1 (by rfl) ⟨4713227, by rfl⟩ : syracuseStep 6284303 = 9426455) B9426455
theorem B2794535 : Blo 1861632 2794535 := bstep (se 1 (by rfl) ⟨2095901, by rfl⟩ : syracuseStep 2794535 = 4191803) B4191803
theorem B2794619 : Blo 1861632 2794619 := bstep (se 1 (by rfl) ⟨2095964, by rfl⟩ : syracuseStep 2794619 = 4191929) B4191929
theorem B2794745 : Blo 1861632 2794745 := bstep (se 2 (by rfl) ⟨1048029, by rfl⟩ : syracuseStep 2794745 = 2096059) B2096059
theorem B2794847 : Blo 1861632 2794847 := bstep (se 1 (by rfl) ⟨2096135, by rfl⟩ : syracuseStep 2794847 = 4192271) B4192271
theorem B2794859 : Blo 1861632 2794859 := bstep (se 1 (by rfl) ⟨2096144, by rfl⟩ : syracuseStep 2794859 = 4192289) B4192289
theorem B11322749 : Blo 1861632 11322749 := bstep (se 3 (by rfl) ⟨2123015, by rfl⟩ : syracuseStep 11322749 = 4246031) B4246031
theorem B21513673 : Blo 1861632 21513673 := bstep (se 2 (by rfl) ⟨8067627, by rfl⟩ : syracuseStep 21513673 = 16135255) B16135255
theorem B2795087 : Blo 1861632 2795087 := bstep (se 1 (by rfl) ⟨2096315, by rfl⟩ : syracuseStep 2795087 = 4192631) B4192631
theorem B6284897 : Blo 1861632 6284897 := bstep (se 2 (by rfl) ⟨2356836, by rfl⟩ : syracuseStep 6284897 = 4713673) B4713673
theorem B9430667 : Blo 1861632 9430667 := bstep (se 1 (by rfl) ⟨7073000, by rfl⟩ : syracuseStep 9430667 = 14146001) B14146001
theorem B5301949 : Blo 1861632 5301949 := bstep (se 3 (by rfl) ⟨994115, by rfl⟩ : syracuseStep 5301949 = 1988231) B1988231
theorem B7071421 : Blo 1861632 7071421 := bstep (se 3 (by rfl) ⟨1325891, by rfl⟩ : syracuseStep 7071421 = 2651783) B2651783
theorem B30222017 : Blo 1861632 30222017 := bstep (se 2 (by rfl) ⟨11333256, by rfl⟩ : syracuseStep 30222017 = 22666513) B22666513
theorem B2795207 : Blo 1861632 2795207 := bstep (se 1 (by rfl) ⟨2096405, by rfl⟩ : syracuseStep 2795207 = 4192811) B4192811
theorem B7554809 : Blo 1861632 7554809 := bstep (se 2 (by rfl) ⟨2833053, by rfl⟩ : syracuseStep 7554809 = 5666107) B5666107
theorem B15312707 : Blo 1861632 15312707 := bstep (se 1 (by rfl) ⟨11484530, by rfl⟩ : syracuseStep 15312707 = 22969061) B22969061
theorem B13428575 : Blo 1861632 13428575 := bstep (se 1 (by rfl) ⟨10071431, by rfl⟩ : syracuseStep 13428575 = 20142863) B20142863
theorem B2795369 : Blo 1861632 2795369 := bstep (se 2 (by rfl) ⟨1048263, by rfl⟩ : syracuseStep 2795369 = 2096527) B2096527
theorem B5302199 : Blo 1861632 5302199 := bstep (se 1 (by rfl) ⟨3976649, by rfl⟩ : syracuseStep 5302199 = 7953299) B7953299
theorem B4474807 : Blo 1861632 4474807 := bstep (se 1 (by rfl) ⟨3356105, by rfl⟩ : syracuseStep 4474807 = 6712211) B6712211
theorem B2795447 : Blo 1861632 2795447 := bstep (se 1 (by rfl) ⟨2096585, by rfl⟩ : syracuseStep 2795447 = 4193171) B4193171
theorem B27207683 : Blo 1861632 27207683 := bstep (se 1 (by rfl) ⟨20405762, by rfl⟩ : syracuseStep 27207683 = 40811525) B40811525
theorem B6375439 : Blo 1861632 6375439 := bstep (se 1 (by rfl) ⟨4781579, by rfl⟩ : syracuseStep 6375439 = 9563159) B9563159
theorem B1861671 : Blo 1861632 1861671 := bstep (se 1 (by rfl) ⟨1396253, by rfl⟩ : syracuseStep 1861671 = 2792507) B2792507
theorem B1861711 : Blo 1861632 1861711 := bstep (se 1 (by rfl) ⟨1396283, by rfl⟩ : syracuseStep 1861711 = 2792567) B2792567
theorem B10610777 : Blo 1861632 10610777 := bstep (se 2 (by rfl) ⟨3979041, by rfl⟩ : syracuseStep 10610777 = 7958083) B7958083
theorem B1861727 : Blo 1861632 1861727 := bstep (se 1 (by rfl) ⟨1396295, by rfl⟩ : syracuseStep 1861727 = 2792591) B2792591
theorem B15100019 : Blo 1861632 15100019 := bstep (se 1 (by rfl) ⟨11325014, by rfl⟩ : syracuseStep 15100019 = 22650029) B22650029
theorem B1861755 : Blo 1861632 1861755 := bstep (se 1 (by rfl) ⟨1396316, by rfl⟩ : syracuseStep 1861755 = 2792633) B2792633
theorem B1861807 : Blo 1861632 1861807 := bstep (se 1 (by rfl) ⟨1396355, by rfl⟩ : syracuseStep 1861807 = 2792711) B2792711
theorem B1861831 : Blo 1861632 1861831 := bstep (se 1 (by rfl) ⟨1396373, by rfl⟩ : syracuseStep 1861831 = 2792747) B2792747
theorem B1861851 : Blo 1861632 1861851 := bstep (se 1 (by rfl) ⟨1396388, by rfl⟩ : syracuseStep 1861851 = 2792777) B2792777
theorem B11938049 : Blo 1861632 11938049 := bstep (se 2 (by rfl) ⟨4476768, by rfl⟩ : syracuseStep 11938049 = 8953537) B8953537
theorem B14149889 : Blo 1861632 14149889 := bstep (se 2 (by rfl) ⟨5306208, by rfl⟩ : syracuseStep 14149889 = 10612417) B10612417
theorem B1861927 : Blo 1861632 1861927 := bstep (se 1 (by rfl) ⟨1396445, by rfl⟩ : syracuseStep 1861927 = 2792891) B2792891
theorem B1861967 : Blo 1861632 1861967 := bstep (se 1 (by rfl) ⟨1396475, by rfl⟩ : syracuseStep 1861967 = 2792951) B2792951
theorem B1861983 : Blo 1861632 1861983 := bstep (se 1 (by rfl) ⟨1396487, by rfl⟩ : syracuseStep 1861983 = 2792975) B2792975
theorem B7653737 : Blo 1861632 7653737 := bstep (se 2 (by rfl) ⟨2870151, by rfl⟩ : syracuseStep 7653737 = 5740303) B5740303
theorem B1862011 : Blo 1861632 1862011 := bstep (se 1 (by rfl) ⟨1396508, by rfl⟩ : syracuseStep 1862011 = 2793017) B2793017
theorem B1862063 : Blo 1861632 1862063 := bstep (se 1 (by rfl) ⟨1396547, by rfl⟩ : syracuseStep 1862063 = 2793095) B2793095
theorem B1862087 : Blo 1861632 1862087 := bstep (se 1 (by rfl) ⟨1396565, by rfl⟩ : syracuseStep 1862087 = 2793131) B2793131
theorem B1862107 : Blo 1861632 1862107 := bstep (se 1 (by rfl) ⟨1396580, by rfl⟩ : syracuseStep 1862107 = 2793161) B2793161
theorem B7957025 : Blo 1861632 7957025 := bstep (se 2 (by rfl) ⟨2983884, by rfl⟩ : syracuseStep 7957025 = 5967769) B5967769
theorem B10611233 : Blo 1861632 10611233 := bstep (se 2 (by rfl) ⟨3979212, by rfl⟩ : syracuseStep 10611233 = 7958425) B7958425
theorem B1862183 : Blo 1861632 1862183 := bstep (se 1 (by rfl) ⟨1396637, by rfl⟩ : syracuseStep 1862183 = 2793275) B2793275
theorem B1862223 : Blo 1861632 1862223 := bstep (se 1 (by rfl) ⟨1396667, by rfl⟩ : syracuseStep 1862223 = 2793335) B2793335
theorem B1862239 : Blo 1861632 1862239 := bstep (se 1 (by rfl) ⟨1396679, by rfl⟩ : syracuseStep 1862239 = 2793359) B2793359
theorem B1862267 : Blo 1861632 1862267 := bstep (se 1 (by rfl) ⟨1396700, by rfl⟩ : syracuseStep 1862267 = 2793401) B2793401
theorem B7072379 : Blo 1861632 7072379 := bstep (se 1 (by rfl) ⟨5304284, by rfl⟩ : syracuseStep 7072379 = 10608569) B10608569
theorem B3025531 : Blo 1861632 3025531 := bstep (se 1 (by rfl) ⟨2269148, by rfl⟩ : syracuseStep 3025531 = 4538297) B4538297
theorem B1862319 : Blo 1861632 1862319 := bstep (se 1 (by rfl) ⟨1396739, by rfl⟩ : syracuseStep 1862319 = 2793479) B2793479
theorem B1862343 : Blo 1861632 1862343 := bstep (se 1 (by rfl) ⟨1396757, by rfl⟩ : syracuseStep 1862343 = 2793515) B2793515
theorem B1862363 : Blo 1861632 1862363 := bstep (se 1 (by rfl) ⟨1396772, by rfl⟩ : syracuseStep 1862363 = 2793545) B2793545
theorem B10611485 : Blo 1861632 10611485 := bstep (se 3 (by rfl) ⟨1989653, by rfl⟩ : syracuseStep 10611485 = 3979307) B3979307
theorem B1862439 : Blo 1861632 1862439 := bstep (se 1 (by rfl) ⟨1396829, by rfl⟩ : syracuseStep 1862439 = 2793659) B2793659
theorem B1862479 : Blo 1861632 1862479 := bstep (se 1 (by rfl) ⟨1396859, by rfl⟩ : syracuseStep 1862479 = 2793719) B2793719
theorem B1862495 : Blo 1861632 1862495 := bstep (se 1 (by rfl) ⟨1396871, by rfl⟩ : syracuseStep 1862495 = 2793743) B2793743
theorem B1862523 : Blo 1861632 1862523 := bstep (se 1 (by rfl) ⟨1396892, by rfl⟩ : syracuseStep 1862523 = 2793785) B2793785
theorem B4189103 : Blo 1861632 4189103 := bstep (se 1 (by rfl) ⟨3141827, by rfl⟩ : syracuseStep 4189103 = 6283655) B6283655
theorem B1862575 : Blo 1861632 1862575 := bstep (se 1 (by rfl) ⟨1396931, by rfl⟩ : syracuseStep 1862575 = 2793863) B2793863
theorem B1862599 : Blo 1861632 1862599 := bstep (se 1 (by rfl) ⟨1396949, by rfl⟩ : syracuseStep 1862599 = 2793899) B2793899
theorem B1862619 : Blo 1861632 1862619 := bstep (se 1 (by rfl) ⟨1396964, by rfl⟩ : syracuseStep 1862619 = 2793929) B2793929
theorem B4713491 : Blo 1861632 4713491 := bstep (se 1 (by rfl) ⟨3535118, by rfl⟩ : syracuseStep 4713491 = 7070237) B7070237
theorem B6286355 : Blo 1861632 6286355 := bstep (se 1 (by rfl) ⟨4714766, by rfl⟩ : syracuseStep 6286355 = 9429533) B9429533
theorem B1862695 : Blo 1861632 1862695 := bstep (se 1 (by rfl) ⟨1397021, by rfl⟩ : syracuseStep 1862695 = 2794043) B2794043
theorem B1862735 : Blo 1861632 1862735 := bstep (se 1 (by rfl) ⟨1397051, by rfl⟩ : syracuseStep 1862735 = 2794103) B2794103
theorem B1862751 : Blo 1861632 1862751 := bstep (se 1 (by rfl) ⟨1397063, by rfl⟩ : syracuseStep 1862751 = 2794127) B2794127
theorem B1862779 : Blo 1861632 1862779 := bstep (se 1 (by rfl) ⟨1397084, by rfl⟩ : syracuseStep 1862779 = 2794169) B2794169
theorem B4189355 : Blo 1861632 4189355 := bstep (se 1 (by rfl) ⟨3142016, by rfl⟩ : syracuseStep 4189355 = 6284033) B6284033
theorem B1862831 : Blo 1861632 1862831 := bstep (se 1 (by rfl) ⟨1397123, by rfl⟩ : syracuseStep 1862831 = 2794247) B2794247
theorem B1862855 : Blo 1861632 1862855 := bstep (se 1 (by rfl) ⟨1397141, by rfl⟩ : syracuseStep 1862855 = 2794283) B2794283
theorem B1862875 : Blo 1861632 1862875 := bstep (se 1 (by rfl) ⟨1397156, by rfl⟩ : syracuseStep 1862875 = 2794313) B2794313
theorem B40267043 : Blo 1861632 40267043 := bstep (se 1 (by rfl) ⟨30200282, by rfl⟩ : syracuseStep 40267043 = 60400565) B60400565
theorem B13421861 : Blo 1861632 13421861 := bstep (se 4 (by rfl) ⟨1258299, by rfl⟩ : syracuseStep 13421861 = 2516599) B2516599
theorem B1862951 : Blo 1861632 1862951 := bstep (se 1 (by rfl) ⟨1397213, by rfl⟩ : syracuseStep 1862951 = 2794427) B2794427
theorem B1862991 : Blo 1861632 1862991 := bstep (se 1 (by rfl) ⟨1397243, by rfl⟩ : syracuseStep 1862991 = 2794487) B2794487
theorem B6286679 : Blo 1861632 6286679 := bstep (se 1 (by rfl) ⟨4715009, by rfl⟩ : syracuseStep 6286679 = 9430019) B9430019
theorem B1863007 : Blo 1861632 1863007 := bstep (se 1 (by rfl) ⟨1397255, by rfl⟩ : syracuseStep 1863007 = 2794511) B2794511
theorem B5303657 : Blo 1861632 5303657 := bstep (se 2 (by rfl) ⟨1988871, by rfl⟩ : syracuseStep 5303657 = 3977743) B3977743
theorem B1863035 : Blo 1861632 1863035 := bstep (se 1 (by rfl) ⟨1397276, by rfl⟩ : syracuseStep 1863035 = 2794553) B2794553
theorem B5303681 : Blo 1861632 5303681 := bstep (se 2 (by rfl) ⟨1988880, by rfl⟩ : syracuseStep 5303681 = 3977761) B3977761
theorem B7073153 : Blo 1861632 7073153 := bstep (se 2 (by rfl) ⟨2652432, by rfl⟩ : syracuseStep 7073153 = 5304865) B5304865
theorem B54431149 : Blo 1861632 54431149 := bstep (se 3 (by rfl) ⟨10205840, by rfl⟩ : syracuseStep 54431149 = 20411681) B20411681
theorem B1863087 : Blo 1861632 1863087 := bstep (se 1 (by rfl) ⟨1397315, by rfl⟩ : syracuseStep 1863087 = 2794631) B2794631
theorem B1863111 : Blo 1861632 1863111 := bstep (se 1 (by rfl) ⟨1397333, by rfl⟩ : syracuseStep 1863111 = 2794667) B2794667
theorem B4713947 : Blo 1861632 4713947 := bstep (se 1 (by rfl) ⟨3535460, by rfl⟩ : syracuseStep 4713947 = 7070921) B7070921
theorem B1863131 : Blo 1861632 1863131 := bstep (se 1 (by rfl) ⟨1397348, by rfl⟩ : syracuseStep 1863131 = 2794697) B2794697
theorem B1863207 : Blo 1861632 1863207 := bstep (se 1 (by rfl) ⟨1397405, by rfl⟩ : syracuseStep 1863207 = 2794811) B2794811
theorem B1863247 : Blo 1861632 1863247 := bstep (se 1 (by rfl) ⟨1397435, by rfl⟩ : syracuseStep 1863247 = 2794871) B2794871
theorem B1863263 : Blo 1861632 1863263 := bstep (se 1 (by rfl) ⟨1397447, by rfl⟩ : syracuseStep 1863263 = 2794895) B2794895
theorem B17903227 : Blo 1861632 17903227 := bstep (se 1 (by rfl) ⟨13427420, by rfl⟩ : syracuseStep 17903227 = 26854841) B26854841
theorem B4476539 : Blo 1861632 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B1863291 : Blo 1861632 1863291 := bstep (se 1 (by rfl) ⟨1397468, by rfl⟩ : syracuseStep 1863291 = 2794937) B2794937
theorem B1863343 : Blo 1861632 1863343 := bstep (se 1 (by rfl) ⟨1397507, by rfl⟩ : syracuseStep 1863343 = 2795015) B2795015
theorem B4189895 : Blo 1861632 4189895 := bstep (se 1 (by rfl) ⟨3142421, by rfl⟩ : syracuseStep 4189895 = 6284843) B6284843
theorem B1863367 : Blo 1861632 1863367 := bstep (se 1 (by rfl) ⟨1397525, by rfl⟩ : syracuseStep 1863367 = 2795051) B2795051
theorem B1863387 : Blo 1861632 1863387 := bstep (se 1 (by rfl) ⟨1397540, by rfl⟩ : syracuseStep 1863387 = 2795081) B2795081
theorem B1863463 : Blo 1861632 1863463 := bstep (se 1 (by rfl) ⟨1397597, by rfl⟩ : syracuseStep 1863463 = 2795195) B2795195
theorem B1863503 : Blo 1861632 1863503 := bstep (se 1 (by rfl) ⟨1397627, by rfl⟩ : syracuseStep 1863503 = 2795255) B2795255
theorem B8949599 : Blo 1861632 8949599 := bstep (se 1 (by rfl) ⟨6712199, by rfl⟩ : syracuseStep 8949599 = 13424399) B13424399
theorem B1863519 : Blo 1861632 1863519 := bstep (se 1 (by rfl) ⟨1397639, by rfl⟩ : syracuseStep 1863519 = 2795279) B2795279
theorem B1863547 : Blo 1861632 1863547 := bstep (se 1 (by rfl) ⟨1397660, by rfl⟩ : syracuseStep 1863547 = 2795321) B2795321
theorem B19124099 : Blo 1861632 19124099 := bstep (se 1 (by rfl) ⟨14343074, by rfl⟩ : syracuseStep 19124099 = 28686149) B28686149
theorem B3141551 : Blo 1861632 3141551 := bstep (se 1 (by rfl) ⟨2356163, by rfl⟩ : syracuseStep 3141551 = 4712327) B4712327
theorem B1863599 : Blo 1861632 1863599 := bstep (se 1 (by rfl) ⟨1397699, by rfl⟩ : syracuseStep 1863599 = 2795399) B2795399
theorem B1863623 : Blo 1861632 1863623 := bstep (se 1 (by rfl) ⟨1397717, by rfl⟩ : syracuseStep 1863623 = 2795435) B2795435
theorem B3141983 : Blo 1861632 3141983 := bstep (se 1 (by rfl) ⟨2356487, by rfl⟩ : syracuseStep 3141983 = 4712975) B4712975
theorem B20132225 : Blo 1861632 20132225 := bstep (se 2 (by rfl) ⟨7549584, by rfl⟩ : syracuseStep 20132225 = 15099169) B15099169
theorem B6287759 : Blo 1861632 6287759 := bstep (se 1 (by rfl) ⟨4715819, by rfl⟩ : syracuseStep 6287759 = 9431639) B9431639
theorem B25825817 : Blo 1861632 25825817 := bstep (se 2 (by rfl) ⟨9684681, by rfl⟩ : syracuseStep 25825817 = 19369363) B19369363
theorem B7074337 : Blo 1861632 7074337 := bstep (se 2 (by rfl) ⟨2652876, by rfl⟩ : syracuseStep 7074337 = 5305753) B5305753
theorem B4190759 : Blo 1861632 4190759 := bstep (se 1 (by rfl) ⟨3143069, by rfl⟩ : syracuseStep 4190759 = 6286139) B6286139
theorem B2650747 : Blo 1861632 2650747 := bstep (se 1 (by rfl) ⟨1988060, by rfl⟩ : syracuseStep 2650747 = 3976121) B3976121
theorem B3535483 : Blo 1861632 3535483 := bstep (se 1 (by rfl) ⟨2651612, by rfl⟩ : syracuseStep 3535483 = 5303225) B5303225
theorem B4715131 : Blo 1861632 4715131 := bstep (se 1 (by rfl) ⟨3536348, by rfl⟩ : syracuseStep 4715131 = 7072697) B7072697
theorem B3535559 : Blo 1861632 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B6288083 : Blo 1861632 6288083 := bstep (se 1 (by rfl) ⟨4716062, by rfl⟩ : syracuseStep 6288083 = 9432125) B9432125
theorem B4191083 : Blo 1861632 4191083 := bstep (se 1 (by rfl) ⟨3143312, by rfl⟩ : syracuseStep 4191083 = 6286625) B6286625
theorem B3142543 : Blo 1861632 3142543 := bstep (se 1 (by rfl) ⟨2356907, by rfl⟩ : syracuseStep 3142543 = 4713815) B4713815
theorem B28677017 : Blo 1861632 28677017 := bstep (se 2 (by rfl) ⟨10753881, by rfl⟩ : syracuseStep 28677017 = 21507763) B21507763
theorem B4191137 : Blo 1861632 4191137 := bstep (se 2 (by rfl) ⟨1571676, by rfl⟩ : syracuseStep 4191137 = 3143353) B3143353
theorem B7074823 : Blo 1861632 7074823 := bstep (se 1 (by rfl) ⟨5306117, by rfl⟩ : syracuseStep 7074823 = 10612235) B10612235
theorem B3535969 : Blo 1861632 3535969 := bstep (se 2 (by rfl) ⟨1325988, by rfl⟩ : syracuseStep 3535969 = 2651977) B2651977
theorem B3355847 : Blo 1861632 3355847 := bstep (se 1 (by rfl) ⟨2516885, by rfl⟩ : syracuseStep 3355847 = 5033771) B5033771
theorem B3978487 : Blo 1861632 3978487 := bstep (se 1 (by rfl) ⟨2983865, by rfl⟩ : syracuseStep 3978487 = 5967731) B5967731
theorem B4191479 : Blo 1861632 4191479 := bstep (se 1 (by rfl) ⟨3143609, by rfl⟩ : syracuseStep 4191479 = 6287219) B6287219
theorem B13423961 : Blo 1861632 13423961 := bstep (se 2 (by rfl) ⟨5033985, by rfl⟩ : syracuseStep 13423961 = 10067971) B10067971
theorem B2094511 : Blo 1861632 2094511 := bstep (se 1 (by rfl) ⟨1570883, by rfl⟩ : syracuseStep 2094511 = 3141767) B3141767
theorem B3536311 : Blo 1861632 3536311 := bstep (se 1 (by rfl) ⟨2652233, by rfl⟩ : syracuseStep 3536311 = 5304467) B5304467
theorem B5969371 : Blo 1861632 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B7075309 : Blo 1861632 7075309 := bstep (se 3 (by rfl) ⟨1326620, by rfl⟩ : syracuseStep 7075309 = 2653241) B2653241
theorem B3143225 : Blo 1861632 3143225 := bstep (se 2 (by rfl) ⟨1178709, by rfl⟩ : syracuseStep 3143225 = 2357419) B2357419
theorem B13424251 : Blo 1861632 13424251 := bstep (se 1 (by rfl) ⟨10068188, by rfl⟩ : syracuseStep 13424251 = 20136377) B20136377
theorem B6051475 : Blo 1861632 6051475 := bstep (se 1 (by rfl) ⟨4538606, by rfl⟩ : syracuseStep 6051475 = 9077213) B9077213
theorem B9557693 : Blo 1861632 9557693 := bstep (se 3 (by rfl) ⟨1792067, by rfl⟩ : syracuseStep 9557693 = 3584135) B3584135
theorem B2651897 : Blo 1861632 2651897 := bstep (se 2 (by rfl) ⟨994461, by rfl⟩ : syracuseStep 2651897 = 1988923) B1988923
theorem B7075613 : Blo 1861632 7075613 := bstep (se 3 (by rfl) ⟨1326677, by rfl⟩ : syracuseStep 7075613 = 2653355) B2653355
theorem B10606403 : Blo 1861632 10606403 := bstep (se 1 (by rfl) ⟨7954802, by rfl⟩ : syracuseStep 10606403 = 15909605) B15909605
theorem B3536713 : Blo 1861632 3536713 := bstep (se 2 (by rfl) ⟨1326267, by rfl⟩ : syracuseStep 3536713 = 2652535) B2652535
theorem B4192073 : Blo 1861632 4192073 := bstep (se 2 (by rfl) ⟨1572027, by rfl⟩ : syracuseStep 4192073 = 3144055) B3144055
theorem B2094943 : Blo 1861632 2094943 := bstep (se 1 (by rfl) ⟨1571207, by rfl⟩ : syracuseStep 2094943 = 3142415) B3142415
theorem B6289271 : Blo 1861632 6289271 := bstep (se 1 (by rfl) ⟨4716953, by rfl⟩ : syracuseStep 6289271 = 9433907) B9433907
theorem B45291473 : Blo 1861632 45291473 := bstep (se 2 (by rfl) ⟨16984302, by rfl⟩ : syracuseStep 45291473 = 33968605) B33968605
theorem B6289487 : Blo 1861632 6289487 := bstep (se 1 (by rfl) ⟨4717115, by rfl⟩ : syracuseStep 6289487 = 9434231) B9434231
theorem B2095303 : Blo 1861632 2095303 := bstep (se 1 (by rfl) ⟨1571477, by rfl⟩ : syracuseStep 2095303 = 3142955) B3142955
theorem B69818609 : Blo 1861632 69818609 := bstep (se 2 (by rfl) ⟨26181978, by rfl⟩ : syracuseStep 69818609 = 52363957) B52363957
theorem B3143927 : Blo 1861632 3143927 := bstep (se 1 (by rfl) ⟨2357945, by rfl⟩ : syracuseStep 3143927 = 4715891) B4715891
theorem B7952651 : Blo 1861632 7952651 := bstep (se 1 (by rfl) ⟨5964488, by rfl⟩ : syracuseStep 7952651 = 11928977) B11928977
theorem B10606859 : Blo 1861632 10606859 := bstep (se 1 (by rfl) ⟨7955144, by rfl⟩ : syracuseStep 10606859 = 15910289) B15910289
theorem B23861537 : Blo 1861632 23861537 := bstep (se 2 (by rfl) ⟨8948076, by rfl⟩ : syracuseStep 23861537 = 17896153) B17896153
theorem B53705065 : Blo 1861632 53705065 := bstep (se 2 (by rfl) ⟨20139399, by rfl⟩ : syracuseStep 53705065 = 40278799) B40278799
theorem B5970305 : Blo 1861632 5970305 := bstep (se 2 (by rfl) ⟨2238864, by rfl⟩ : syracuseStep 5970305 = 4477729) B4477729
theorem B2357687 : Blo 1861632 2357687 := bstep (se 1 (by rfl) ⟨1768265, by rfl⟩ : syracuseStep 2357687 = 3536531) B3536531
theorem B8608237 : Blo 1861632 8608237 := bstep (se 3 (by rfl) ⟨1614044, by rfl⟩ : syracuseStep 8608237 = 3228089) B3228089
theorem B3537427 : Blo 1861632 3537427 := bstep (se 1 (by rfl) ⟨2653070, by rfl⟩ : syracuseStep 3537427 = 5306141) B5306141
theorem B11328025 : Blo 1861632 11328025 := bstep (se 2 (by rfl) ⟨4248009, by rfl⟩ : syracuseStep 11328025 = 8496019) B8496019
theorem B2357839 : Blo 1861632 2357839 := bstep (se 1 (by rfl) ⟨1768379, by rfl⟩ : syracuseStep 2357839 = 3536759) B3536759
theorem B3144271 : Blo 1861632 3144271 := bstep (se 1 (by rfl) ⟨2358203, by rfl⟩ : syracuseStep 3144271 = 4716407) B4716407
theorem B4192865 : Blo 1861632 4192865 := bstep (se 2 (by rfl) ⟨1572324, by rfl⟩ : syracuseStep 4192865 = 3144649) B3144649
theorem B3144521 : Blo 1861632 3144521 := bstep (se 2 (by rfl) ⟨1179195, by rfl⟩ : syracuseStep 3144521 = 2358391) B2358391
theorem B3537769 : Blo 1861632 3537769 := bstep (se 2 (by rfl) ⟨1326663, by rfl⟩ : syracuseStep 3537769 = 2653327) B2653327
theorem B7953335 : Blo 1861632 7953335 := bstep (se 1 (by rfl) ⟨5965001, by rfl⟩ : syracuseStep 7953335 = 11930003) B11930003
theorem B10607543 : Blo 1861632 10607543 := bstep (se 1 (by rfl) ⟨7955657, by rfl⟩ : syracuseStep 10607543 = 15911315) B15911315
theorem B14146487 : Blo 1861632 14146487 := bstep (se 1 (by rfl) ⟨10609865, by rfl⟩ : syracuseStep 14146487 = 21219731) B21219731
theorem B27212773 : Blo 1861632 27212773 := bstep (se 4 (by rfl) ⟨2551197, by rfl⟩ : syracuseStep 27212773 = 5102395) B5102395
theorem B8068115 : Blo 1861632 8068115 := bstep (se 1 (by rfl) ⟨6051086, by rfl⟩ : syracuseStep 8068115 = 12102173) B12102173
theorem B2096167 : Blo 1861632 2096167 := bstep (se 1 (by rfl) ⟨1572125, by rfl⟩ : syracuseStep 2096167 = 3144251) B3144251
theorem B3931193 : Blo 1861632 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B2792879 : Blo 1861632 2792879 := bstep (se 1 (by rfl) ⟨2094659, by rfl⟩ : syracuseStep 2792879 = 4189319) B4189319
theorem B2792969 : Blo 1861632 2792969 := bstep (se 2 (by rfl) ⟨1047363, by rfl⟩ : syracuseStep 2792969 = 2094727) B2094727
theorem B2792999 : Blo 1861632 2792999 := bstep (se 1 (by rfl) ⟨2094749, by rfl⟩ : syracuseStep 2792999 = 4189499) B4189499
theorem B2793083 : Blo 1861632 2793083 := bstep (se 1 (by rfl) ⟨2094812, by rfl⟩ : syracuseStep 2793083 = 4189625) B4189625
theorem B10608317 : Blo 1861632 10608317 := bstep (se 3 (by rfl) ⟨1989059, by rfl⟩ : syracuseStep 10608317 = 3978119) B3978119
theorem B1867483 : Blo 1861632 1867483 := bstep (se 1 (by rfl) ⟨1400612, by rfl⟩ : syracuseStep 1867483 = 2801225) B2801225
theorem B2793209 : Blo 1861632 2793209 := bstep (se 2 (by rfl) ⟨1047453, by rfl⟩ : syracuseStep 2793209 = 2094907) B2094907
theorem B13426499 : Blo 1861632 13426499 := bstep (se 1 (by rfl) ⟨10069874, by rfl⟩ : syracuseStep 13426499 = 20139749) B20139749
theorem B2793311 : Blo 1861632 2793311 := bstep (se 1 (by rfl) ⟨2094983, by rfl⟩ : syracuseStep 2793311 = 4189967) B4189967
theorem B3186527 : Blo 1861632 3186527 := bstep (se 1 (by rfl) ⟨2389895, by rfl⟩ : syracuseStep 3186527 = 4779791) B4779791
theorem B6283115 : Blo 1861632 6283115 := bstep (se 1 (by rfl) ⟨4712336, by rfl⟩ : syracuseStep 6283115 = 9424673) B9424673
theorem B5373803 : Blo 1861632 5373803 := bstep (se 1 (by rfl) ⟨4030352, by rfl⟩ : syracuseStep 5373803 = 8060705) B8060705
theorem B2793323 : Blo 1861632 2793323 := bstep (se 1 (by rfl) ⟨2094992, by rfl⟩ : syracuseStep 2793323 = 4189985) B4189985
theorem B31833971 : Blo 1861632 31833971 := bstep (se 1 (by rfl) ⟨23875478, by rfl⟩ : syracuseStep 31833971 = 47750957) B47750957
theorem B6283169 : Blo 1861632 6283169 := bstep (se 2 (by rfl) ⟨2356188, by rfl⟩ : syracuseStep 6283169 = 4712377) B4712377
theorem B20422585 : Blo 1861632 20422585 := bstep (se 2 (by rfl) ⟨7658469, by rfl⟩ : syracuseStep 20422585 = 15316939) B15316939
theorem B2793737 : Blo 1861632 2793737 := bstep (se 2 (by rfl) ⟨1047651, by rfl⟩ : syracuseStep 2793737 = 2095303) B2095303
theorem B2793839 : Blo 1861632 2793839 := bstep (se 1 (by rfl) ⟨2095379, by rfl⟩ : syracuseStep 2793839 = 4190759) B4190759
theorem B71606753 : Blo 1861632 71606753 := bstep (se 2 (by rfl) ⟨26852532, by rfl⟩ : syracuseStep 71606753 = 53705065) B53705065
theorem B5964359 : Blo 1861632 5964359 := bstep (se 1 (by rfl) ⟨4473269, by rfl⟩ : syracuseStep 5964359 = 8946539) B8946539
theorem B2794055 : Blo 1861632 2794055 := bstep (se 1 (by rfl) ⟨2095541, by rfl⟩ : syracuseStep 2794055 = 4191083) B4191083
theorem B2794091 : Blo 1861632 2794091 := bstep (se 1 (by rfl) ⟨2095568, by rfl⟩ : syracuseStep 2794091 = 4191137) B4191137
theorem B8946425 : Blo 1861632 8946425 := bstep (se 2 (by rfl) ⟨3354909, by rfl⟩ : syracuseStep 8946425 = 6709819) B6709819
theorem B2237231 : Blo 1861632 2237231 := bstep (se 1 (by rfl) ⟨1677923, by rfl⟩ : syracuseStep 2237231 = 3355847) B3355847
theorem B2794319 : Blo 1861632 2794319 := bstep (se 1 (by rfl) ⟨2095739, by rfl⟩ : syracuseStep 2794319 = 4191479) B4191479
theorem B7070935 : Blo 1861632 7070935 := bstep (se 1 (by rfl) ⟨5303201, by rfl⟩ : syracuseStep 7070935 = 10606403) B10606403
theorem B10208471 : Blo 1861632 10208471 := bstep (se 1 (by rfl) ⟨7656353, by rfl⟩ : syracuseStep 10208471 = 15312707) B15312707
theorem B2794715 : Blo 1861632 2794715 := bstep (se 1 (by rfl) ⟨2096036, by rfl⟩ : syracuseStep 2794715 = 4192073) B4192073
theorem B36283697 : Blo 1861632 36283697 := bstep (se 2 (by rfl) ⟨13606386, by rfl⟩ : syracuseStep 36283697 = 27212773) B27212773
theorem B18138455 : Blo 1861632 18138455 := bstep (se 1 (by rfl) ⟨13603841, by rfl⟩ : syracuseStep 18138455 = 27207683) B27207683
theorem B2794889 : Blo 1861632 2794889 := bstep (se 2 (by rfl) ⟨1048083, by rfl⟩ : syracuseStep 2794889 = 2096167) B2096167
theorem B5301767 : Blo 1861632 5301767 := bstep (se 1 (by rfl) ⟨3976325, by rfl⟩ : syracuseStep 5301767 = 7952651) B7952651
theorem B7071239 : Blo 1861632 7071239 := bstep (se 1 (by rfl) ⟨5303429, by rfl⟩ : syracuseStep 7071239 = 10606859) B10606859
theorem B2795243 : Blo 1861632 2795243 := bstep (se 1 (by rfl) ⟨2096432, by rfl⟩ : syracuseStep 2795243 = 4192865) B4192865
theorem B72574865 : Blo 1861632 72574865 := bstep (se 2 (by rfl) ⟨27215574, by rfl⟩ : syracuseStep 72574865 = 54431149) B54431149
theorem B5302223 : Blo 1861632 5302223 := bstep (se 1 (by rfl) ⟨3976667, by rfl⟩ : syracuseStep 5302223 = 7953335) B7953335
theorem B7071695 : Blo 1861632 7071695 := bstep (se 1 (by rfl) ⟨5303771, by rfl⟩ : syracuseStep 7071695 = 10607543) B10607543
theorem B9430991 : Blo 1861632 9430991 := bstep (se 1 (by rfl) ⟨7073243, by rfl⟩ : syracuseStep 9430991 = 14146487) B14146487
theorem B7071725 : Blo 1861632 7071725 := bstep (se 3 (by rfl) ⟨1325948, by rfl⟩ : syracuseStep 7071725 = 2651897) B2651897
theorem B8947907 : Blo 1861632 8947907 := bstep (se 1 (by rfl) ⟨6710930, by rfl⟩ : syracuseStep 8947907 = 13421861) B13421861
theorem B8497405 : Blo 1861632 8497405 := bstep (se 3 (by rfl) ⟨1593263, by rfl⟩ : syracuseStep 8497405 = 3186527) B3186527
theorem B14330141 : Blo 1861632 14330141 := bstep (se 3 (by rfl) ⟨2686901, by rfl⟩ : syracuseStep 14330141 = 5373803) B5373803
theorem B1861919 : Blo 1861632 1861919 := bstep (se 1 (by rfl) ⟨1396439, by rfl⟩ : syracuseStep 1861919 = 2792879) B2792879
theorem B23865637 : Blo 1861632 23865637 := bstep (se 4 (by rfl) ⟨2237403, by rfl⟩ : syracuseStep 23865637 = 4474807) B4474807
theorem B1861979 : Blo 1861632 1861979 := bstep (se 1 (by rfl) ⟨1396484, by rfl⟩ : syracuseStep 1861979 = 2792969) B2792969
theorem B1861999 : Blo 1861632 1861999 := bstep (se 1 (by rfl) ⟨1396499, by rfl⟩ : syracuseStep 1861999 = 2792999) B2792999
theorem B1862055 : Blo 1861632 1862055 := bstep (se 1 (by rfl) ⟨1396541, by rfl⟩ : syracuseStep 1862055 = 2793083) B2793083
theorem B2984359 : Blo 1861632 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B7072211 : Blo 1861632 7072211 := bstep (se 1 (by rfl) ⟨5304158, by rfl⟩ : syracuseStep 7072211 = 10608317) B10608317
theorem B1862139 : Blo 1861632 1862139 := bstep (se 1 (by rfl) ⟨1396604, by rfl⟩ : syracuseStep 1862139 = 2793209) B2793209
theorem B1862207 : Blo 1861632 1862207 := bstep (se 1 (by rfl) ⟨1396655, by rfl⟩ : syracuseStep 1862207 = 2793311) B2793311
theorem B5966399 : Blo 1861632 5966399 := bstep (se 1 (by rfl) ⟨4474799, by rfl⟩ : syracuseStep 5966399 = 8949599) B8949599
theorem B45910597 : Blo 1861632 45910597 := bstep (se 4 (by rfl) ⟨4304118, by rfl⟩ : syracuseStep 45910597 = 8608237) B8608237
theorem B4188743 : Blo 1861632 4188743 := bstep (se 1 (by rfl) ⟨3141557, by rfl⟩ : syracuseStep 4188743 = 6283115) B6283115
theorem B1862215 : Blo 1861632 1862215 := bstep (se 1 (by rfl) ⟨1396661, by rfl⟩ : syracuseStep 1862215 = 2793323) B2793323
theorem B12749399 : Blo 1861632 12749399 := bstep (se 1 (by rfl) ⟨9562049, by rfl⟩ : syracuseStep 12749399 = 19124099) B19124099
theorem B4188779 : Blo 1861632 4188779 := bstep (se 1 (by rfl) ⟨3141584, by rfl⟩ : syracuseStep 4188779 = 6283169) B6283169
theorem B1862367 : Blo 1861632 1862367 := bstep (se 1 (by rfl) ⟨1396775, by rfl⟩ : syracuseStep 1862367 = 2793551) B2793551
theorem B1862447 : Blo 1861632 1862447 := bstep (se 1 (by rfl) ⟨1396835, by rfl⟩ : syracuseStep 1862447 = 2793671) B2793671
theorem B64531331 : Blo 1861632 64531331 := bstep (se 1 (by rfl) ⟨48398498, by rfl⟩ : syracuseStep 64531331 = 96796997) B96796997
theorem B1862555 : Blo 1861632 1862555 := bstep (se 1 (by rfl) ⟨1396916, by rfl⟩ : syracuseStep 1862555 = 2793833) B2793833
theorem B7072667 : Blo 1861632 7072667 := bstep (se 1 (by rfl) ⟨5304500, by rfl⟩ : syracuseStep 7072667 = 10609001) B10609001
theorem B9431963 : Blo 1861632 9431963 := bstep (se 1 (by rfl) ⟨7073972, by rfl⟩ : syracuseStep 9431963 = 14147945) B14147945
theorem B13421483 : Blo 1861632 13421483 := bstep (se 1 (by rfl) ⟨10066112, by rfl⟩ : syracuseStep 13421483 = 20132225) B20132225
theorem B1862607 : Blo 1861632 1862607 := bstep (se 1 (by rfl) ⟨1396955, by rfl⟩ : syracuseStep 1862607 = 2793911) B2793911
theorem B1862631 : Blo 1861632 1862631 := bstep (se 1 (by rfl) ⟨1396973, by rfl⟩ : syracuseStep 1862631 = 2793947) B2793947
theorem B4189175 : Blo 1861632 4189175 := bstep (se 1 (by rfl) ⟨3141881, by rfl⟩ : syracuseStep 4189175 = 6283763) B6283763
theorem B4713511 : Blo 1861632 4713511 := bstep (se 1 (by rfl) ⟨3535133, by rfl⟩ : syracuseStep 4713511 = 7070267) B7070267
theorem B3976411 : Blo 1861632 3976411 := bstep (se 1 (by rfl) ⟨2982308, by rfl⟩ : syracuseStep 3976411 = 5964617) B5964617
theorem B1862943 : Blo 1861632 1862943 := bstep (se 1 (by rfl) ⟨1397207, by rfl⟩ : syracuseStep 1862943 = 2794415) B2794415
theorem B186182957 : Blo 1861632 186182957 := bstep (se 3 (by rfl) ⟨34909304, by rfl⟩ : syracuseStep 186182957 = 69818609) B69818609
theorem B1863003 : Blo 1861632 1863003 := bstep (se 1 (by rfl) ⟨1397252, by rfl⟩ : syracuseStep 1863003 = 2794505) B2794505
theorem B4189535 : Blo 1861632 4189535 := bstep (se 1 (by rfl) ⟨3142151, by rfl⟩ : syracuseStep 4189535 = 6284303) B6284303
theorem B1863023 : Blo 1861632 1863023 := bstep (se 1 (by rfl) ⟨1397267, by rfl⟩ : syracuseStep 1863023 = 2794535) B2794535
theorem B9432449 : Blo 1861632 9432449 := bstep (se 2 (by rfl) ⟨3537168, by rfl⟩ : syracuseStep 9432449 = 7074337) B7074337
theorem B1863079 : Blo 1861632 1863079 := bstep (se 1 (by rfl) ⟨1397309, by rfl⟩ : syracuseStep 1863079 = 2794619) B2794619
theorem B3534329 : Blo 1861632 3534329 := bstep (se 2 (by rfl) ⟨1325373, by rfl⟩ : syracuseStep 3534329 = 2650747) B2650747
theorem B4713977 : Blo 1861632 4713977 := bstep (se 2 (by rfl) ⟨1767741, by rfl⟩ : syracuseStep 4713977 = 3535483) B3535483
theorem B6286841 : Blo 1861632 6286841 := bstep (se 2 (by rfl) ⟨2357565, by rfl⟩ : syracuseStep 6286841 = 4715131) B4715131
theorem B1863163 : Blo 1861632 1863163 := bstep (se 1 (by rfl) ⟨1397372, by rfl⟩ : syracuseStep 1863163 = 2794745) B2794745
theorem B8949307 : Blo 1861632 8949307 := bstep (se 1 (by rfl) ⟨6711980, by rfl⟩ : syracuseStep 8949307 = 13423961) B13423961
theorem B1863231 : Blo 1861632 1863231 := bstep (se 1 (by rfl) ⟨1397423, by rfl⟩ : syracuseStep 1863231 = 2794847) B2794847
theorem B1863239 : Blo 1861632 1863239 := bstep (se 1 (by rfl) ⟨1397429, by rfl⟩ : syracuseStep 1863239 = 2794859) B2794859
theorem B7548499 : Blo 1861632 7548499 := bstep (se 1 (by rfl) ⟨5661374, by rfl⟩ : syracuseStep 7548499 = 11322749) B11322749
theorem B20409965 : Blo 1861632 20409965 := bstep (se 3 (by rfl) ⟨3826868, by rfl⟩ : syracuseStep 20409965 = 7653737) B7653737
theorem B14143085 : Blo 1861632 14143085 := bstep (se 3 (by rfl) ⟨2651828, by rfl⟩ : syracuseStep 14143085 = 5303657) B5303657
theorem B15920813 : Blo 1861632 15920813 := bstep (se 3 (by rfl) ⟨2985152, by rfl⟩ : syracuseStep 15920813 = 5970305) B5970305
theorem B1863391 : Blo 1861632 1863391 := bstep (se 1 (by rfl) ⟨1397543, by rfl⟩ : syracuseStep 1863391 = 2795087) B2795087
theorem B4189931 : Blo 1861632 4189931 := bstep (se 1 (by rfl) ⟨3142448, by rfl⟩ : syracuseStep 4189931 = 6284897) B6284897
theorem B6287111 : Blo 1861632 6287111 := bstep (se 1 (by rfl) ⟨4715333, by rfl⟩ : syracuseStep 6287111 = 9430667) B9430667
theorem B20148011 : Blo 1861632 20148011 := bstep (se 1 (by rfl) ⟨15111008, by rfl⟩ : syracuseStep 20148011 = 30222017) B30222017
theorem B1863471 : Blo 1861632 1863471 := bstep (se 1 (by rfl) ⟨1397603, by rfl⟩ : syracuseStep 1863471 = 2795207) B2795207
theorem B6287165 : Blo 1861632 6287165 := bstep (se 3 (by rfl) ⟨1178843, by rfl⟩ : syracuseStep 6287165 = 2357687) B2357687
theorem B4190057 : Blo 1861632 4190057 := bstep (se 2 (by rfl) ⟨1571271, by rfl⟩ : syracuseStep 4190057 = 3142543) B3142543
theorem B1863579 : Blo 1861632 1863579 := bstep (se 1 (by rfl) ⟨1397684, by rfl⟩ : syracuseStep 1863579 = 2795369) B2795369
theorem B1863631 : Blo 1861632 1863631 := bstep (se 1 (by rfl) ⟨1397723, by rfl⟩ : syracuseStep 1863631 = 2795447) B2795447
theorem B9433097 : Blo 1861632 9433097 := bstep (se 2 (by rfl) ⟨3537411, by rfl⟩ : syracuseStep 9433097 = 7074823) B7074823
theorem B7073851 : Blo 1861632 7073851 := bstep (se 1 (by rfl) ⟨5305388, by rfl⟩ : syracuseStep 7073851 = 10610777) B10610777
theorem B4714625 : Blo 1861632 4714625 := bstep (se 2 (by rfl) ⟨1767984, by rfl⟩ : syracuseStep 4714625 = 3535969) B3535969
theorem B7958699 : Blo 1861632 7958699 := bstep (se 1 (by rfl) ⟨5969024, by rfl⟩ : syracuseStep 7958699 = 11938049) B11938049
theorem B9433259 : Blo 1861632 9433259 := bstep (se 1 (by rfl) ⟨7074944, by rfl⟩ : syracuseStep 9433259 = 14149889) B14149889
theorem B5304649 : Blo 1861632 5304649 := bstep (se 2 (by rfl) ⟨1989243, by rfl⟩ : syracuseStep 5304649 = 3978487) B3978487
theorem B5304683 : Blo 1861632 5304683 := bstep (se 1 (by rfl) ⟨3978512, by rfl⟩ : syracuseStep 5304683 = 7957025) B7957025
theorem B7074155 : Blo 1861632 7074155 := bstep (se 1 (by rfl) ⟨5305616, by rfl⟩ : syracuseStep 7074155 = 10611233) B10611233
theorem B4714919 : Blo 1861632 4714919 := bstep (se 1 (by rfl) ⟨3536189, by rfl⟩ : syracuseStep 4714919 = 7072379) B7072379
theorem B7074323 : Blo 1861632 7074323 := bstep (se 1 (by rfl) ⟨5305742, by rfl⟩ : syracuseStep 7074323 = 10611485) B10611485
theorem B4715081 : Blo 1861632 4715081 := bstep (se 2 (by rfl) ⟨1768155, by rfl⟩ : syracuseStep 4715081 = 3536311) B3536311
theorem B28684897 : Blo 1861632 28684897 := bstep (se 2 (by rfl) ⟨10756836, by rfl⟩ : syracuseStep 28684897 = 21513673) B21513673
theorem B7959161 : Blo 1861632 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B9433745 : Blo 1861632 9433745 := bstep (se 2 (by rfl) ⟨3537654, by rfl⟩ : syracuseStep 9433745 = 7075309) B7075309
theorem B3142327 : Blo 1861632 3142327 := bstep (se 1 (by rfl) ⟨2356745, by rfl⟩ : syracuseStep 3142327 = 4713491) B4713491
theorem B4190903 : Blo 1861632 4190903 := bstep (se 1 (by rfl) ⟨3143177, by rfl⟩ : syracuseStep 4190903 = 6286355) B6286355
theorem B5378743 : Blo 1861632 5378743 := bstep (se 1 (by rfl) ⟨4034057, by rfl⟩ : syracuseStep 5378743 = 8068115) B8068115
theorem B4191119 : Blo 1861632 4191119 := bstep (se 1 (by rfl) ⟨3143339, by rfl⟩ : syracuseStep 4191119 = 6286679) B6286679
theorem B3535787 : Blo 1861632 3535787 := bstep (se 1 (by rfl) ⟨2651840, by rfl⟩ : syracuseStep 3535787 = 5303681) B5303681
theorem B4715435 : Blo 1861632 4715435 := bstep (se 1 (by rfl) ⟨3536576, by rfl⟩ : syracuseStep 4715435 = 7073153) B7073153
theorem B3142631 : Blo 1861632 3142631 := bstep (se 1 (by rfl) ⟨2356973, by rfl⟩ : syracuseStep 3142631 = 4713947) B4713947
theorem B4715617 : Blo 1861632 4715617 := bstep (se 2 (by rfl) ⟨1768356, by rfl⟩ : syracuseStep 4715617 = 3536713) B3536713
theorem B8950999 : Blo 1861632 8950999 := bstep (se 1 (by rfl) ⟨6713249, by rfl⟩ : syracuseStep 8950999 = 13426499) B13426499
theorem B21222647 : Blo 1861632 21222647 := bstep (se 1 (by rfl) ⟨15916985, by rfl⟩ : syracuseStep 21222647 = 31833971) B31833971
theorem B2094367 : Blo 1861632 2094367 := bstep (se 1 (by rfl) ⟨1570775, by rfl⟩ : syracuseStep 2094367 = 3141551) B3141551
theorem B8500585 : Blo 1861632 8500585 := bstep (se 2 (by rfl) ⟨3187719, by rfl⟩ : syracuseStep 8500585 = 6375439) B6375439
theorem B10483181 : Blo 1861632 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B2094655 : Blo 1861632 2094655 := bstep (se 1 (by rfl) ⟨1570991, by rfl⟩ : syracuseStep 2094655 = 3141983) B3141983
theorem B4191839 : Blo 1861632 4191839 := bstep (se 1 (by rfl) ⟨3143879, by rfl⟩ : syracuseStep 4191839 = 6287759) B6287759
theorem B9426617 : Blo 1861632 9426617 := bstep (se 2 (by rfl) ⟨3534981, by rfl⟩ : syracuseStep 9426617 = 7069963) B7069963
theorem B17217211 : Blo 1861632 17217211 := bstep (se 1 (by rfl) ⟨12912908, by rfl⟩ : syracuseStep 17217211 = 25825817) B25825817
theorem B2357039 : Blo 1861632 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B4192055 : Blo 1861632 4192055 := bstep (se 1 (by rfl) ⟨3144041, by rfl⟩ : syracuseStep 4192055 = 6288083) B6288083
theorem B16136165 : Blo 1861632 16136165 := bstep (se 4 (by rfl) ⟨1512765, by rfl⟩ : syracuseStep 16136165 = 3025531) B3025531
theorem B4716569 : Blo 1861632 4716569 := bstep (se 2 (by rfl) ⟨1768713, by rfl⟩ : syracuseStep 4716569 = 3537427) B3537427
theorem B15104033 : Blo 1861632 15104033 := bstep (se 2 (by rfl) ⟨5664012, by rfl⟩ : syracuseStep 15104033 = 11328025) B11328025
theorem B15915041 : Blo 1861632 15915041 := bstep (se 2 (by rfl) ⟨5968140, by rfl⟩ : syracuseStep 15915041 = 11936281) B11936281
theorem B3143785 : Blo 1861632 3143785 := bstep (se 2 (by rfl) ⟨1178919, by rfl⟩ : syracuseStep 3143785 = 2357839) B2357839
theorem B4192361 : Blo 1861632 4192361 := bstep (se 2 (by rfl) ⟨1572135, by rfl⟩ : syracuseStep 4192361 = 3144271) B3144271
theorem B2095483 : Blo 1861632 2095483 := bstep (se 1 (by rfl) ⟨1571612, by rfl⟩ : syracuseStep 2095483 = 3143225) B3143225
theorem B6371795 : Blo 1861632 6371795 := bstep (se 1 (by rfl) ⟨4778846, by rfl⟩ : syracuseStep 6371795 = 9557693) B9557693
theorem B4717025 : Blo 1861632 4717025 := bstep (se 2 (by rfl) ⟨1768884, by rfl⟩ : syracuseStep 4717025 = 3537769) B3537769
theorem B5036539 : Blo 1861632 5036539 := bstep (se 1 (by rfl) ⟨3777404, by rfl⟩ : syracuseStep 5036539 = 7554809) B7554809
theorem B4717075 : Blo 1861632 4717075 := bstep (se 1 (by rfl) ⟨3537806, by rfl⟩ : syracuseStep 4717075 = 7075613) B7075613
theorem B8952383 : Blo 1861632 8952383 := bstep (se 1 (by rfl) ⟨6714287, by rfl⟩ : syracuseStep 8952383 = 13428575) B13428575
theorem B4192847 : Blo 1861632 4192847 := bstep (se 1 (by rfl) ⟨3144635, by rfl⟩ : syracuseStep 4192847 = 6289271) B6289271
theorem B30194315 : Blo 1861632 30194315 := bstep (se 1 (by rfl) ⟨22645736, by rfl⟩ : syracuseStep 30194315 = 45291473) B45291473
theorem B4192991 : Blo 1861632 4192991 := bstep (se 1 (by rfl) ⟨3144743, by rfl⟩ : syracuseStep 4192991 = 6289487) B6289487
theorem B10066679 : Blo 1861632 10066679 := bstep (se 1 (by rfl) ⟨7550009, by rfl⟩ : syracuseStep 10066679 = 15100019) B15100019
theorem B2095951 : Blo 1861632 2095951 := bstep (se 1 (by rfl) ⟨1571963, by rfl⟩ : syracuseStep 2095951 = 3143927) B3143927
theorem B15907691 : Blo 1861632 15907691 := bstep (se 1 (by rfl) ⟨11930768, by rfl⟩ : syracuseStep 15907691 = 23861537) B23861537
theorem B2096347 : Blo 1861632 2096347 := bstep (se 1 (by rfl) ⟨1572260, by rfl⟩ : syracuseStep 2096347 = 3144521) B3144521
theorem B2792681 : Blo 1861632 2792681 := bstep (se 2 (by rfl) ⟨1047255, by rfl⟩ : syracuseStep 2792681 = 2094511) B2094511
theorem B2792735 : Blo 1861632 2792735 := bstep (se 1 (by rfl) ⟨2094551, by rfl⟩ : syracuseStep 2792735 = 4189103) B4189103
theorem B2792903 : Blo 1861632 2792903 := bstep (se 1 (by rfl) ⟨2094677, by rfl⟩ : syracuseStep 2792903 = 4189355) B4189355
theorem B17899001 : Blo 1861632 17899001 := bstep (se 2 (by rfl) ⟨6712125, by rfl⟩ : syracuseStep 17899001 = 13424251) B13424251
theorem B23870969 : Blo 1861632 23870969 := bstep (se 2 (by rfl) ⟨8951613, by rfl⟩ : syracuseStep 23870969 = 17903227) B17903227
theorem B26844695 : Blo 1861632 26844695 := bstep (se 1 (by rfl) ⟨20133521, by rfl⟩ : syracuseStep 26844695 = 40267043) B40267043
theorem B8068633 : Blo 1861632 8068633 := bstep (se 2 (by rfl) ⟨3025737, by rfl⟩ : syracuseStep 8068633 = 6051475) B6051475
theorem B7069265 : Blo 1861632 7069265 := bstep (se 2 (by rfl) ⟨2650974, by rfl⟩ : syracuseStep 7069265 = 5301949) B5301949
theorem B9428561 : Blo 1861632 9428561 := bstep (se 2 (by rfl) ⟨3535710, by rfl⟩ : syracuseStep 9428561 = 7071421) B7071421
theorem B2489977 : Blo 1861632 2489977 := bstep (se 2 (by rfl) ⟨933741, by rfl⟩ : syracuseStep 2489977 = 1867483) B1867483
theorem B76472045 : Blo 1861632 76472045 := bstep (se 3 (by rfl) ⟨14338508, by rfl⟩ : syracuseStep 76472045 = 28677017) B28677017
theorem B2793257 : Blo 1861632 2793257 := bstep (se 2 (by rfl) ⟨1047471, by rfl⟩ : syracuseStep 2793257 = 2094943) B2094943
theorem B2793263 : Blo 1861632 2793263 := bstep (se 1 (by rfl) ⟨2094947, by rfl⟩ : syracuseStep 2793263 = 4189895) B4189895
theorem B14139197 : Blo 1861632 14139197 := bstep (se 3 (by rfl) ⟨2651099, by rfl⟩ : syracuseStep 14139197 = 5302199) B5302199
theorem B27230113 : Blo 1861632 27230113 := bstep (se 2 (by rfl) ⟨10211292, by rfl⟩ : syracuseStep 27230113 = 20422585) B20422585
theorem B43032709 : Blo 1861632 43032709 := bstep (se 4 (by rfl) ⟨4034316, by rfl⟩ : syracuseStep 43032709 = 8068633) B8068633
theorem B2793935 : Blo 1861632 2793935 := bstep (se 1 (by rfl) ⟨2095451, by rfl⟩ : syracuseStep 2793935 = 4190903) B4190903
theorem B2793977 : Blo 1861632 2793977 := bstep (se 2 (by rfl) ⟨1047741, by rfl⟩ : syracuseStep 2793977 = 2095483) B2095483
theorem B5964283 : Blo 1861632 5964283 := bstep (se 1 (by rfl) ⟨4473212, by rfl⟩ : syracuseStep 5964283 = 8946425) B8946425
theorem B27222589 : Blo 1861632 27222589 := bstep (se 3 (by rfl) ⟨5104235, by rfl⟩ : syracuseStep 27222589 = 10208471) B10208471
theorem B2794079 : Blo 1861632 2794079 := bstep (se 1 (by rfl) ⟨2095559, by rfl⟩ : syracuseStep 2794079 = 4191119) B4191119
theorem B14148431 : Blo 1861632 14148431 := bstep (se 1 (by rfl) ⟨10611323, by rfl⟩ : syracuseStep 14148431 = 21222647) B21222647
theorem B12092303 : Blo 1861632 12092303 := bstep (se 1 (by rfl) ⟨9069227, by rfl⟩ : syracuseStep 12092303 = 18138455) B18138455
theorem B6988787 : Blo 1861632 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B2794559 : Blo 1861632 2794559 := bstep (se 1 (by rfl) ⟨2095919, by rfl⟩ : syracuseStep 2794559 = 4191839) B4191839
theorem B2794601 : Blo 1861632 2794601 := bstep (se 2 (by rfl) ⟨1047975, by rfl⟩ : syracuseStep 2794601 = 2095951) B2095951
theorem B6284411 : Blo 1861632 6284411 := bstep (se 1 (by rfl) ⟨4713308, by rfl⟩ : syracuseStep 6284411 = 9426617) B9426617
theorem B2794703 : Blo 1861632 2794703 := bstep (se 1 (by rfl) ⟨2096027, by rfl⟩ : syracuseStep 2794703 = 4192055) B4192055
theorem B16991453 : Blo 1861632 16991453 := bstep (se 3 (by rfl) ⟨3185897, by rfl⟩ : syracuseStep 16991453 = 6371795) B6371795
theorem B48383243 : Blo 1861632 48383243 := bstep (se 1 (by rfl) ⟨36287432, by rfl⟩ : syracuseStep 48383243 = 72574865) B72574865
theorem B10757443 : Blo 1861632 10757443 := bstep (se 1 (by rfl) ⟨8068082, by rfl⟩ : syracuseStep 10757443 = 16136165) B16136165
theorem B45319493 : Blo 1861632 45319493 := bstep (se 4 (by rfl) ⟨4248702, by rfl⟩ : syracuseStep 45319493 = 8497405) B8497405
theorem B10069355 : Blo 1861632 10069355 := bstep (se 1 (by rfl) ⟨7552016, by rfl⟩ : syracuseStep 10069355 = 15104033) B15104033
theorem B10610027 : Blo 1861632 10610027 := bstep (se 1 (by rfl) ⟨7957520, by rfl⟩ : syracuseStep 10610027 = 15915041) B15915041
theorem B6284681 : Blo 1861632 6284681 := bstep (se 2 (by rfl) ⟨2356755, by rfl⟩ : syracuseStep 6284681 = 4713511) B4713511
theorem B2794907 : Blo 1861632 2794907 := bstep (se 1 (by rfl) ⟨2096180, by rfl⟩ : syracuseStep 2794907 = 4192361) B4192361
theorem B5965271 : Blo 1861632 5965271 := bstep (se 1 (by rfl) ⟨4473953, by rfl⟩ : syracuseStep 5965271 = 8947907) B8947907
theorem B9553427 : Blo 1861632 9553427 := bstep (se 1 (by rfl) ⟨7165070, by rfl⟩ : syracuseStep 9553427 = 14330141) B14330141
theorem B5301881 : Blo 1861632 5301881 := bstep (se 2 (by rfl) ⟨1988205, by rfl⟩ : syracuseStep 5301881 = 3976411) B3976411
theorem B2795129 : Blo 1861632 2795129 := bstep (se 2 (by rfl) ⟨1048173, by rfl⟩ : syracuseStep 2795129 = 2096347) B2096347
theorem B2795231 : Blo 1861632 2795231 := bstep (se 1 (by rfl) ⟨2096423, by rfl⟩ : syracuseStep 2795231 = 4192847) B4192847
theorem B20129543 : Blo 1861632 20129543 := bstep (se 1 (by rfl) ⟨15097157, by rfl⟩ : syracuseStep 20129543 = 30194315) B30194315
theorem B2795327 : Blo 1861632 2795327 := bstep (se 1 (by rfl) ⟨2096495, by rfl⟩ : syracuseStep 2795327 = 4192991) B4192991
theorem B6711119 : Blo 1861632 6711119 := bstep (se 1 (by rfl) ⟨5033339, by rfl⟩ : syracuseStep 6711119 = 10066679) B10066679
theorem B8947655 : Blo 1861632 8947655 := bstep (se 1 (by rfl) ⟨6710741, by rfl⟩ : syracuseStep 8947655 = 13421483) B13421483
theorem B611944469 : Blo 1861632 611944469 := bstep (se 6 (by rfl) ⟨14342448, by rfl⟩ : syracuseStep 611944469 = 28684897) B28684897
theorem B5965949 : Blo 1861632 5965949 := bstep (se 3 (by rfl) ⟨1118615, by rfl⟩ : syracuseStep 5965949 = 2237231) B2237231
theorem B6285437 : Blo 1861632 6285437 := bstep (se 3 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 6285437 = 2357039) B2357039
theorem B1861787 : Blo 1861632 1861787 := bstep (se 1 (by rfl) ⟨1396340, by rfl⟩ : syracuseStep 1861787 = 2792681) B2792681
theorem B3319969 : Blo 1861632 3319969 := bstep (se 2 (by rfl) ⟨1244988, by rfl⟩ : syracuseStep 3319969 = 2489977) B2489977
theorem B1861823 : Blo 1861632 1861823 := bstep (se 1 (by rfl) ⟨1396367, by rfl⟩ : syracuseStep 1861823 = 2792735) B2792735
theorem B22956281 : Blo 1861632 22956281 := bstep (se 2 (by rfl) ⟨8608605, by rfl⟩ : syracuseStep 22956281 = 17217211) B17217211
theorem B1861935 : Blo 1861632 1861935 := bstep (se 1 (by rfl) ⟨1396451, by rfl⟩ : syracuseStep 1861935 = 2792903) B2792903
theorem B4712843 : Blo 1861632 4712843 := bstep (se 1 (by rfl) ⟨3534632, by rfl⟩ : syracuseStep 4712843 = 7069265) B7069265
theorem B6285707 : Blo 1861632 6285707 := bstep (se 1 (by rfl) ⟨4714280, by rfl⟩ : syracuseStep 6285707 = 9428561) B9428561
theorem B50981363 : Blo 1861632 50981363 := bstep (se 1 (by rfl) ⟨38236022, by rfl⟩ : syracuseStep 50981363 = 76472045) B76472045
theorem B1862171 : Blo 1861632 1862171 := bstep (se 1 (by rfl) ⟨1396628, by rfl⟩ : syracuseStep 1862171 = 2793257) B2793257
theorem B1862175 : Blo 1861632 1862175 := bstep (se 1 (by rfl) ⟨1396631, by rfl⟩ : syracuseStep 1862175 = 2793263) B2793263
theorem B9431801 : Blo 1861632 9431801 := bstep (se 2 (by rfl) ⟨3536925, by rfl⟩ : syracuseStep 9431801 = 7073851) B7073851
theorem B1862491 : Blo 1861632 1862491 := bstep (se 1 (by rfl) ⟨1396868, by rfl⟩ : syracuseStep 1862491 = 2793737) B2793737
theorem B1862559 : Blo 1861632 1862559 := bstep (se 1 (by rfl) ⟨1396919, by rfl⟩ : syracuseStep 1862559 = 2793839) B2793839
theorem B47737835 : Blo 1861632 47737835 := bstep (se 1 (by rfl) ⟨35803376, by rfl⟩ : syracuseStep 47737835 = 71606753) B71606753
theorem B1862703 : Blo 1861632 1862703 := bstep (se 1 (by rfl) ⟨1397027, by rfl⟩ : syracuseStep 1862703 = 2794055) B2794055
theorem B31820849 : Blo 1861632 31820849 := bstep (se 2 (by rfl) ⟨11932818, by rfl⟩ : syracuseStep 31820849 = 23865637) B23865637
theorem B1862727 : Blo 1861632 1862727 := bstep (se 1 (by rfl) ⟨1397045, by rfl⟩ : syracuseStep 1862727 = 2794091) B2794091
theorem B7072865 : Blo 1861632 7072865 := bstep (se 2 (by rfl) ⟨2652324, by rfl⟩ : syracuseStep 7072865 = 5304649) B5304649
theorem B1862879 : Blo 1861632 1862879 := bstep (se 1 (by rfl) ⟨1397159, by rfl⟩ : syracuseStep 1862879 = 2794319) B2794319
theorem B61214129 : Blo 1861632 61214129 := bstep (se 2 (by rfl) ⟨22955298, by rfl⟩ : syracuseStep 61214129 = 45910597) B45910597
theorem B496487885 : Blo 1861632 496487885 := bstep (se 3 (by rfl) ⟨93091478, by rfl⟩ : syracuseStep 496487885 = 186182957) B186182957
theorem B1863143 : Blo 1861632 1863143 := bstep (se 1 (by rfl) ⟨1397357, by rfl⟩ : syracuseStep 1863143 = 2794715) B2794715
theorem B4189769 : Blo 1861632 4189769 := bstep (se 2 (by rfl) ⟨1571163, by rfl⟩ : syracuseStep 4189769 = 3142327) B3142327
theorem B1863259 : Blo 1861632 1863259 := bstep (se 1 (by rfl) ⟨1397444, by rfl⟩ : syracuseStep 1863259 = 2794889) B2794889
theorem B3534511 : Blo 1861632 3534511 := bstep (se 1 (by rfl) ⟨2650883, by rfl⟩ : syracuseStep 3534511 = 5301767) B5301767
theorem B4714159 : Blo 1861632 4714159 := bstep (se 1 (by rfl) ⟨3535619, by rfl⟩ : syracuseStep 4714159 = 7071239) B7071239
theorem B1863495 : Blo 1861632 1863495 := bstep (se 1 (by rfl) ⟨1397621, by rfl⟩ : syracuseStep 1863495 = 2795243) B2795243
theorem B3534815 : Blo 1861632 3534815 := bstep (se 1 (by rfl) ⟨2651111, by rfl⟩ : syracuseStep 3534815 = 5302223) B5302223
theorem B4714463 : Blo 1861632 4714463 := bstep (se 1 (by rfl) ⟨3535847, by rfl⟩ : syracuseStep 4714463 = 7071695) B7071695
theorem B6287327 : Blo 1861632 6287327 := bstep (se 1 (by rfl) ⟨4715495, by rfl⟩ : syracuseStep 6287327 = 9430991) B9430991
theorem B4714483 : Blo 1861632 4714483 := bstep (se 1 (by rfl) ⟨3535862, by rfl⟩ : syracuseStep 4714483 = 7071725) B7071725
theorem B6287489 : Blo 1861632 6287489 := bstep (se 2 (by rfl) ⟨2357808, by rfl⟩ : syracuseStep 6287489 = 4715617) B4715617
theorem B15904957 : Blo 1861632 15904957 := bstep (se 3 (by rfl) ⟨2982179, by rfl⟩ : syracuseStep 15904957 = 5964359) B5964359
theorem B4714807 : Blo 1861632 4714807 := bstep (se 1 (by rfl) ⟨3536105, by rfl⟩ : syracuseStep 4714807 = 7072211) B7072211
theorem B3977599 : Blo 1861632 3977599 := bstep (se 1 (by rfl) ⟨2983199, by rfl⟩ : syracuseStep 3977599 = 5966399) B5966399
theorem B5968255 : Blo 1861632 5968255 := bstep (se 1 (by rfl) ⟨4476191, by rfl⟩ : syracuseStep 5968255 = 8952383) B8952383
theorem B8499599 : Blo 1861632 8499599 := bstep (se 1 (by rfl) ⟨6374699, by rfl⟩ : syracuseStep 8499599 = 12749399) B12749399
theorem B11334113 : Blo 1861632 11334113 := bstep (se 2 (by rfl) ⟨4250292, by rfl⟩ : syracuseStep 11334113 = 8500585) B8500585
theorem B10605127 : Blo 1861632 10605127 := bstep (se 1 (by rfl) ⟨7953845, by rfl⟩ : syracuseStep 10605127 = 15907691) B15907691
theorem B43020887 : Blo 1861632 43020887 := bstep (se 1 (by rfl) ⟨32265665, by rfl⟩ : syracuseStep 43020887 = 64531331) B64531331
theorem B4715111 : Blo 1861632 4715111 := bstep (se 1 (by rfl) ⟨3536333, by rfl⟩ : syracuseStep 4715111 = 7072667) B7072667
theorem B6287975 : Blo 1861632 6287975 := bstep (se 1 (by rfl) ⟨4715981, by rfl⟩ : syracuseStep 6287975 = 9431963) B9431963
theorem B11932409 : Blo 1861632 11932409 := bstep (se 2 (by rfl) ⟨4474653, by rfl⟩ : syracuseStep 11932409 = 8949307) B8949307
theorem B10064665 : Blo 1861632 10064665 := bstep (se 2 (by rfl) ⟨3774249, by rfl⟩ : syracuseStep 10064665 = 7548499) B7548499
theorem B6288299 : Blo 1861632 6288299 := bstep (se 1 (by rfl) ⟨4716224, by rfl⟩ : syracuseStep 6288299 = 9432449) B9432449
theorem B2356219 : Blo 1861632 2356219 := bstep (se 1 (by rfl) ⟨1767164, by rfl⟩ : syracuseStep 2356219 = 3534329) B3534329
theorem B3142651 : Blo 1861632 3142651 := bstep (se 1 (by rfl) ⟨2356988, by rfl⟩ : syracuseStep 3142651 = 4713977) B4713977
theorem B11932667 : Blo 1861632 11932667 := bstep (se 1 (by rfl) ⟨8949500, by rfl⟩ : syracuseStep 11932667 = 17899001) B17899001
theorem B4191227 : Blo 1861632 4191227 := bstep (se 1 (by rfl) ⟨3143420, by rfl⟩ : syracuseStep 4191227 = 6286841) B6286841
theorem B15913979 : Blo 1861632 15913979 := bstep (se 1 (by rfl) ⟨11935484, by rfl⟩ : syracuseStep 15913979 = 23870969) B23870969
theorem B17896463 : Blo 1861632 17896463 := bstep (se 1 (by rfl) ⟨13422347, by rfl⟩ : syracuseStep 17896463 = 26844695) B26844695
theorem B10613875 : Blo 1861632 10613875 := bstep (se 1 (by rfl) ⟨7960406, by rfl⟩ : syracuseStep 10613875 = 15920813) B15920813
theorem B4191407 : Blo 1861632 4191407 := bstep (se 1 (by rfl) ⟨3143555, by rfl⟩ : syracuseStep 4191407 = 6287111) B6287111
theorem B13432007 : Blo 1861632 13432007 := bstep (se 1 (by rfl) ⟨10074005, by rfl⟩ : syracuseStep 13432007 = 20148011) B20148011
theorem B9426131 : Blo 1861632 9426131 := bstep (se 1 (by rfl) ⟨7069598, by rfl⟩ : syracuseStep 9426131 = 14139197) B14139197
theorem B4191443 : Blo 1861632 4191443 := bstep (se 1 (by rfl) ⟨3143582, by rfl⟩ : syracuseStep 4191443 = 6287165) B6287165
theorem B6288731 : Blo 1861632 6288731 := bstep (se 1 (by rfl) ⟨4716548, by rfl⟩ : syracuseStep 6288731 = 9433097) B9433097
theorem B3143083 : Blo 1861632 3143083 := bstep (se 1 (by rfl) ⟨2357312, by rfl⟩ : syracuseStep 3143083 = 4714625) B4714625
theorem B5305799 : Blo 1861632 5305799 := bstep (se 1 (by rfl) ⟨3979349, by rfl⟩ : syracuseStep 5305799 = 7958699) B7958699
theorem B6288839 : Blo 1861632 6288839 := bstep (se 1 (by rfl) ⟨4716629, by rfl⟩ : syracuseStep 6288839 = 9433259) B9433259
theorem B4191713 : Blo 1861632 4191713 := bstep (se 2 (by rfl) ⟨1571892, by rfl⟩ : syracuseStep 4191713 = 3143785) B3143785
theorem B3536455 : Blo 1861632 3536455 := bstep (se 1 (by rfl) ⟨2652341, by rfl⟩ : syracuseStep 3536455 = 5304683) B5304683
theorem B4716103 : Blo 1861632 4716103 := bstep (se 1 (by rfl) ⟨3537077, by rfl⟩ : syracuseStep 4716103 = 7074155) B7074155
theorem B3143279 : Blo 1861632 3143279 := bstep (se 1 (by rfl) ⟨2357459, by rfl⟩ : syracuseStep 3143279 = 4714919) B4714919
theorem B4716215 : Blo 1861632 4716215 := bstep (se 1 (by rfl) ⟨3537161, by rfl⟩ : syracuseStep 4716215 = 7074323) B7074323
theorem B3143387 : Blo 1861632 3143387 := bstep (se 1 (by rfl) ⟨2357540, by rfl⟩ : syracuseStep 3143387 = 4715081) B4715081
theorem B5306107 : Blo 1861632 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B6289163 : Blo 1861632 6289163 := bstep (se 1 (by rfl) ⟨4716872, by rfl⟩ : syracuseStep 6289163 = 9433745) B9433745
theorem B3979145 : Blo 1861632 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B2357191 : Blo 1861632 2357191 := bstep (se 1 (by rfl) ⟨1767893, by rfl⟩ : syracuseStep 2357191 = 3535787) B3535787
theorem B3143623 : Blo 1861632 3143623 := bstep (se 1 (by rfl) ⟨2357717, by rfl⟩ : syracuseStep 3143623 = 4715435) B4715435
theorem B2095087 : Blo 1861632 2095087 := bstep (se 1 (by rfl) ⟨1571315, by rfl⟩ : syracuseStep 2095087 = 3142631) B3142631
theorem B6715385 : Blo 1861632 6715385 := bstep (se 2 (by rfl) ⟨2518269, by rfl⟩ : syracuseStep 6715385 = 5036539) B5036539
theorem B6289433 : Blo 1861632 6289433 := bstep (se 2 (by rfl) ⟨2358537, by rfl⟩ : syracuseStep 6289433 = 4717075) B4717075
theorem B24189131 : Blo 1861632 24189131 := bstep (se 1 (by rfl) ⟨18141848, by rfl⟩ : syracuseStep 24189131 = 36283697) B36283697
theorem B28686629 : Blo 1861632 28686629 := bstep (se 4 (by rfl) ⟨2689371, by rfl⟩ : syracuseStep 28686629 = 5378743) B5378743
theorem B3144379 : Blo 1861632 3144379 := bstep (se 1 (by rfl) ⟨2358284, by rfl⟩ : syracuseStep 3144379 = 4716569) B4716569
theorem B9427913 : Blo 1861632 9427913 := bstep (se 2 (by rfl) ⟨3535467, by rfl⟩ : syracuseStep 9427913 = 7070935) B7070935
theorem B11934665 : Blo 1861632 11934665 := bstep (se 2 (by rfl) ⟨4475499, by rfl⟩ : syracuseStep 11934665 = 8950999) B8950999
theorem B3144683 : Blo 1861632 3144683 := bstep (se 1 (by rfl) ⟨2358512, by rfl⟩ : syracuseStep 3144683 = 4717025) B4717025
theorem B2792489 : Blo 1861632 2792489 := bstep (se 2 (by rfl) ⟨1047183, by rfl⟩ : syracuseStep 2792489 = 2094367) B2094367
theorem B2792495 : Blo 1861632 2792495 := bstep (se 1 (by rfl) ⟨2094371, by rfl⟩ : syracuseStep 2792495 = 4188743) B4188743
theorem B2792519 : Blo 1861632 2792519 := bstep (se 1 (by rfl) ⟨2094389, by rfl⟩ : syracuseStep 2792519 = 4188779) B4188779
theorem B2792783 : Blo 1861632 2792783 := bstep (se 1 (by rfl) ⟨2094587, by rfl⟩ : syracuseStep 2792783 = 4189175) B4189175
theorem B2792873 : Blo 1861632 2792873 := bstep (se 2 (by rfl) ⟨1047327, by rfl⟩ : syracuseStep 2792873 = 2094655) B2094655
theorem B145227269 : Blo 1861632 145227269 := bstep (se 4 (by rfl) ⟨13615056, by rfl⟩ : syracuseStep 145227269 = 27230113) B27230113
theorem B2793023 : Blo 1861632 2793023 := bstep (se 1 (by rfl) ⟨2094767, by rfl⟩ : syracuseStep 2793023 = 4189535) B4189535
theorem B13606643 : Blo 1861632 13606643 := bstep (se 1 (by rfl) ⟨10204982, by rfl⟩ : syracuseStep 13606643 = 20409965) B20409965
theorem B9428723 : Blo 1861632 9428723 := bstep (se 1 (by rfl) ⟨7071542, by rfl⟩ : syracuseStep 9428723 = 14143085) B14143085
theorem B2793287 : Blo 1861632 2793287 := bstep (se 1 (by rfl) ⟨2094965, by rfl⟩ : syracuseStep 2793287 = 4189931) B4189931
theorem B2793371 : Blo 1861632 2793371 := bstep (se 1 (by rfl) ⟨2095028, by rfl⟩ : syracuseStep 2793371 = 4190057) B4190057
theorem B57376945 : Blo 1861632 57376945 := bstep (se 2 (by rfl) ⟨21516354, by rfl⟩ : syracuseStep 57376945 = 43032709) B43032709
theorem B7954939 : Blo 1861632 7954939 := bstep (se 1 (by rfl) ⟨5966204, by rfl⟩ : syracuseStep 7954939 = 11932409) B11932409
theorem B64504349 : Blo 1861632 64504349 := bstep (se 3 (by rfl) ⟨12094565, by rfl⟩ : syracuseStep 64504349 = 24189131) B24189131
theorem B8061535 : Blo 1861632 8061535 := bstep (se 1 (by rfl) ⟨6046151, by rfl⟩ : syracuseStep 8061535 = 12092303) B12092303
theorem B7955111 : Blo 1861632 7955111 := bstep (se 1 (by rfl) ⟨5966333, by rfl⟩ : syracuseStep 7955111 = 11932667) B11932667
theorem B2794151 : Blo 1861632 2794151 := bstep (se 1 (by rfl) ⟨2095613, by rfl⟩ : syracuseStep 2794151 = 4191227) B4191227
theorem B10609319 : Blo 1861632 10609319 := bstep (se 1 (by rfl) ⟨7956989, by rfl⟩ : syracuseStep 10609319 = 15913979) B15913979
theorem B14140169 : Blo 1861632 14140169 := bstep (se 2 (by rfl) ⟨5302563, by rfl⟩ : syracuseStep 14140169 = 10605127) B10605127
theorem B2794271 : Blo 1861632 2794271 := bstep (se 1 (by rfl) ⟨2095703, by rfl⟩ : syracuseStep 2794271 = 4191407) B4191407
theorem B6284087 : Blo 1861632 6284087 := bstep (se 1 (by rfl) ⟨4713065, by rfl⟩ : syracuseStep 6284087 = 9426131) B9426131
theorem B2794295 : Blo 1861632 2794295 := bstep (se 1 (by rfl) ⟨2095721, by rfl⟩ : syracuseStep 2794295 = 4191443) B4191443
theorem B30212995 : Blo 1861632 30212995 := bstep (se 1 (by rfl) ⟨22659746, by rfl⟩ : syracuseStep 30212995 = 45319493) B45319493
theorem B2794475 : Blo 1861632 2794475 := bstep (se 1 (by rfl) ⟨2095856, by rfl⟩ : syracuseStep 2794475 = 4191713) B4191713
theorem B13419553 : Blo 1861632 13419553 := bstep (se 2 (by rfl) ⟨5032332, by rfl⟩ : syracuseStep 13419553 = 10064665) B10064665
theorem B13419695 : Blo 1861632 13419695 := bstep (se 1 (by rfl) ⟨10064771, by rfl⟩ : syracuseStep 13419695 = 20129543) B20129543
theorem B1323967693 : Blo 1861632 1323967693 := bstep (se 3 (by rfl) ⟨248243942, by rfl⟩ : syracuseStep 1323967693 = 496487885) B496487885
theorem B4474079 : Blo 1861632 4474079 := bstep (se 1 (by rfl) ⟨3355559, by rfl⟩ : syracuseStep 4474079 = 6711119) B6711119
theorem B5965103 : Blo 1861632 5965103 := bstep (se 1 (by rfl) ⟨4473827, by rfl⟩ : syracuseStep 5965103 = 8947655) B8947655
theorem B407962979 : Blo 1861632 407962979 := bstep (se 1 (by rfl) ⟨305972234, by rfl⟩ : syracuseStep 407962979 = 611944469) B611944469
theorem B15304187 : Blo 1861632 15304187 := bstep (se 1 (by rfl) ⟨11478140, by rfl⟩ : syracuseStep 15304187 = 22956281) B22956281
theorem B6285275 : Blo 1861632 6285275 := bstep (se 1 (by rfl) ⟨4713956, by rfl⟩ : syracuseStep 6285275 = 9427913) B9427913
theorem B7956443 : Blo 1861632 7956443 := bstep (se 1 (by rfl) ⟨5967332, by rfl⟩ : syracuseStep 7956443 = 11934665) B11934665
theorem B36284381 : Blo 1861632 36284381 := bstep (se 3 (by rfl) ⟨6803321, by rfl⟩ : syracuseStep 36284381 = 13606643) B13606643
theorem B1861659 : Blo 1861632 1861659 := bstep (se 1 (by rfl) ⟨1396244, by rfl⟩ : syracuseStep 1861659 = 2792489) B2792489
theorem B1861663 : Blo 1861632 1861663 := bstep (se 1 (by rfl) ⟨1396247, by rfl⟩ : syracuseStep 1861663 = 2792495) B2792495
theorem B1861679 : Blo 1861632 1861679 := bstep (se 1 (by rfl) ⟨1396259, by rfl⟩ : syracuseStep 1861679 = 2792519) B2792519
theorem B1861855 : Blo 1861632 1861855 := bstep (se 1 (by rfl) ⟨1396391, by rfl⟩ : syracuseStep 1861855 = 2792783) B2792783
theorem B4712681 : Blo 1861632 4712681 := bstep (se 2 (by rfl) ⟨1767255, by rfl⟩ : syracuseStep 4712681 = 3534511) B3534511
theorem B6285545 : Blo 1861632 6285545 := bstep (se 2 (by rfl) ⟨2357079, by rfl⟩ : syracuseStep 6285545 = 4714159) B4714159
theorem B1861915 : Blo 1861632 1861915 := bstep (se 1 (by rfl) ⟨1396436, by rfl⟩ : syracuseStep 1861915 = 2792873) B2792873
theorem B1862015 : Blo 1861632 1862015 := bstep (se 1 (by rfl) ⟨1396511, by rfl⟩ : syracuseStep 1862015 = 2793023) B2793023
theorem B6285815 : Blo 1861632 6285815 := bstep (se 1 (by rfl) ⟨4714361, by rfl⟩ : syracuseStep 6285815 = 9428723) B9428723
theorem B1862191 : Blo 1861632 1862191 := bstep (se 1 (by rfl) ⟨1396643, by rfl⟩ : syracuseStep 1862191 = 2793287) B2793287
theorem B1862247 : Blo 1861632 1862247 := bstep (se 1 (by rfl) ⟨1396685, by rfl⟩ : syracuseStep 1862247 = 2793371) B2793371
theorem B6285977 : Blo 1861632 6285977 := bstep (se 2 (by rfl) ⟨2357241, by rfl⟩ : syracuseStep 6285977 = 4714483) B4714483
theorem B4426625 : Blo 1861632 4426625 := bstep (se 2 (by rfl) ⟨1659984, by rfl⟩ : syracuseStep 4426625 = 3319969) B3319969
theorem B1862623 : Blo 1861632 1862623 := bstep (se 1 (by rfl) ⟨1396967, by rfl⟩ : syracuseStep 1862623 = 2793935) B2793935
theorem B7556075 : Blo 1861632 7556075 := bstep (se 1 (by rfl) ⟨5667056, by rfl⟩ : syracuseStep 7556075 = 11334113) B11334113
theorem B1862651 : Blo 1861632 1862651 := bstep (se 1 (by rfl) ⟨1396988, by rfl⟩ : syracuseStep 1862651 = 2793977) B2793977
theorem B1862719 : Blo 1861632 1862719 := bstep (se 1 (by rfl) ⟨1397039, by rfl⟩ : syracuseStep 1862719 = 2794079) B2794079
theorem B6286409 : Blo 1861632 6286409 := bstep (se 2 (by rfl) ⟨2357403, by rfl⟩ : syracuseStep 6286409 = 4714807) B4714807
theorem B5303465 : Blo 1861632 5303465 := bstep (se 2 (by rfl) ⟨1988799, by rfl⟩ : syracuseStep 5303465 = 3977599) B3977599
theorem B7957673 : Blo 1861632 7957673 := bstep (se 2 (by rfl) ⟨2984127, by rfl⟩ : syracuseStep 7957673 = 5968255) B5968255
theorem B35818685 : Blo 1861632 35818685 := bstep (se 3 (by rfl) ⟨6716003, by rfl⟩ : syracuseStep 35818685 = 13432007) B13432007
theorem B9432287 : Blo 1861632 9432287 := bstep (se 1 (by rfl) ⟨7074215, by rfl⟩ : syracuseStep 9432287 = 14148431) B14148431
theorem B11930975 : Blo 1861632 11930975 := bstep (se 1 (by rfl) ⟨8948231, by rfl⟩ : syracuseStep 11930975 = 17896463) B17896463
theorem B1863039 : Blo 1861632 1863039 := bstep (se 1 (by rfl) ⟨1397279, by rfl⟩ : syracuseStep 1863039 = 2794559) B2794559
theorem B1863067 : Blo 1861632 1863067 := bstep (se 1 (by rfl) ⟨1397300, by rfl⟩ : syracuseStep 1863067 = 2794601) B2794601
theorem B4189607 : Blo 1861632 4189607 := bstep (se 1 (by rfl) ⟨3142205, by rfl⟩ : syracuseStep 4189607 = 6284411) B6284411
theorem B1863135 : Blo 1861632 1863135 := bstep (se 1 (by rfl) ⟨1397351, by rfl⟩ : syracuseStep 1863135 = 2794703) B2794703
theorem B32255495 : Blo 1861632 32255495 := bstep (se 1 (by rfl) ⟨24191621, by rfl⟩ : syracuseStep 32255495 = 48383243) B48383243
theorem B6712903 : Blo 1861632 6712903 := bstep (se 1 (by rfl) ⟨5034677, by rfl⟩ : syracuseStep 6712903 = 10069355) B10069355
theorem B7073351 : Blo 1861632 7073351 := bstep (se 1 (by rfl) ⟨5305013, by rfl⟩ : syracuseStep 7073351 = 10610027) B10610027
theorem B4189787 : Blo 1861632 4189787 := bstep (se 1 (by rfl) ⟨3142340, by rfl⟩ : syracuseStep 4189787 = 6284681) B6284681
theorem B1863271 : Blo 1861632 1863271 := bstep (se 1 (by rfl) ⟨1397453, by rfl⟩ : syracuseStep 1863271 = 2794907) B2794907
theorem B3976847 : Blo 1861632 3976847 := bstep (se 1 (by rfl) ⟨2982635, by rfl⟩ : syracuseStep 3976847 = 5965271) B5965271
theorem B6368951 : Blo 1861632 6368951 := bstep (se 1 (by rfl) ⟨4776713, by rfl⟩ : syracuseStep 6368951 = 9553427) B9553427
theorem B3534587 : Blo 1861632 3534587 := bstep (se 1 (by rfl) ⟨2650940, by rfl⟩ : syracuseStep 3534587 = 5301881) B5301881
theorem B1863419 : Blo 1861632 1863419 := bstep (se 1 (by rfl) ⟨1397564, by rfl⟩ : syracuseStep 1863419 = 2795129) B2795129
theorem B1863487 : Blo 1861632 1863487 := bstep (se 1 (by rfl) ⟨1397615, by rfl⟩ : syracuseStep 1863487 = 2795231) B2795231
theorem B1863551 : Blo 1861632 1863551 := bstep (se 1 (by rfl) ⟨1397663, by rfl⟩ : syracuseStep 1863551 = 2795327) B2795327
theorem B3141625 : Blo 1861632 3141625 := bstep (se 2 (by rfl) ⟨1178109, by rfl⟩ : syracuseStep 3141625 = 2356219) B2356219
theorem B4190201 : Blo 1861632 4190201 := bstep (se 2 (by rfl) ⟨1571325, by rfl⟩ : syracuseStep 4190201 = 3142651) B3142651
theorem B4476923 : Blo 1861632 4476923 := bstep (se 1 (by rfl) ⟨3357692, by rfl⟩ : syracuseStep 4476923 = 6715385) B6715385
theorem B3977299 : Blo 1861632 3977299 := bstep (se 1 (by rfl) ⟨2982974, by rfl⟩ : syracuseStep 3977299 = 5965949) B5965949
theorem B4190291 : Blo 1861632 4190291 := bstep (se 1 (by rfl) ⟨3142718, by rfl⟩ : syracuseStep 4190291 = 6285437) B6285437
theorem B14151833 : Blo 1861632 14151833 := bstep (se 2 (by rfl) ⟨5306937, by rfl⟩ : syracuseStep 14151833 = 10613875) B10613875
theorem B19124419 : Blo 1861632 19124419 := bstep (se 1 (by rfl) ⟨14343314, by rfl⟩ : syracuseStep 19124419 = 28686629) B28686629
theorem B3141895 : Blo 1861632 3141895 := bstep (se 1 (by rfl) ⟨2356421, by rfl⟩ : syracuseStep 3141895 = 4712843) B4712843
theorem B4190471 : Blo 1861632 4190471 := bstep (se 1 (by rfl) ⟨3142853, by rfl⟩ : syracuseStep 4190471 = 6285707) B6285707
theorem B6287867 : Blo 1861632 6287867 := bstep (se 1 (by rfl) ⟨4715900, by rfl⟩ : syracuseStep 6287867 = 9431801) B9431801
theorem B4190777 : Blo 1861632 4190777 := bstep (se 2 (by rfl) ⟨1571541, by rfl⟩ : syracuseStep 4190777 = 3143083) B3143083
theorem B21213899 : Blo 1861632 21213899 := bstep (se 1 (by rfl) ⟨15910424, by rfl⟩ : syracuseStep 21213899 = 31820849) B31820849
theorem B4715243 : Blo 1861632 4715243 := bstep (se 1 (by rfl) ⟨3536432, by rfl⟩ : syracuseStep 4715243 = 7072865) B7072865
theorem B4715273 : Blo 1861632 4715273 := bstep (se 2 (by rfl) ⟨1768227, by rfl⟩ : syracuseStep 4715273 = 3536455) B3536455
theorem B6288137 : Blo 1861632 6288137 := bstep (se 2 (by rfl) ⟨2358051, by rfl⟩ : syracuseStep 6288137 = 4716103) B4716103
theorem B40809419 : Blo 1861632 40809419 := bstep (se 1 (by rfl) ⟨30607064, by rfl⟩ : syracuseStep 40809419 = 61214129) B61214129
theorem B7074809 : Blo 1861632 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B96818179 : Blo 1861632 96818179 := bstep (se 1 (by rfl) ⟨72613634, by rfl⟩ : syracuseStep 96818179 = 145227269) B145227269
theorem B3142921 : Blo 1861632 3142921 := bstep (se 2 (by rfl) ⟨1178595, by rfl⟩ : syracuseStep 3142921 = 2357191) B2357191
theorem B4191497 : Blo 1861632 4191497 := bstep (se 2 (by rfl) ⟨1571811, by rfl⟩ : syracuseStep 4191497 = 3143623) B3143623
theorem B2356543 : Blo 1861632 2356543 := bstep (se 1 (by rfl) ⟨1767407, by rfl⟩ : syracuseStep 2356543 = 3534815) B3534815
theorem B3142975 : Blo 1861632 3142975 := bstep (se 1 (by rfl) ⟨2357231, by rfl⟩ : syracuseStep 3142975 = 4714463) B4714463
theorem B4191551 : Blo 1861632 4191551 := bstep (se 1 (by rfl) ⟨3143663, by rfl⟩ : syracuseStep 4191551 = 6287327) B6287327
theorem B4191659 : Blo 1861632 4191659 := bstep (se 1 (by rfl) ⟨3143744, by rfl⟩ : syracuseStep 4191659 = 6287489) B6287489
theorem B21206609 : Blo 1861632 21206609 := bstep (se 2 (by rfl) ⟨7952478, by rfl⟩ : syracuseStep 21206609 = 15904957) B15904957
theorem B5666399 : Blo 1861632 5666399 := bstep (se 1 (by rfl) ⟨4249799, by rfl⟩ : syracuseStep 5666399 = 8499599) B8499599
theorem B3143407 : Blo 1861632 3143407 := bstep (se 1 (by rfl) ⟨2357555, by rfl⟩ : syracuseStep 3143407 = 4715111) B4715111
theorem B4191983 : Blo 1861632 4191983 := bstep (se 1 (by rfl) ⟨3143987, by rfl⟩ : syracuseStep 4191983 = 6287975) B6287975
theorem B4192199 : Blo 1861632 4192199 := bstep (se 1 (by rfl) ⟨3144149, by rfl⟩ : syracuseStep 4192199 = 6288299) B6288299
theorem B4659191 : Blo 1861632 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B7952377 : Blo 1861632 7952377 := bstep (se 2 (by rfl) ⟨2982141, by rfl⟩ : syracuseStep 7952377 = 5964283) B5964283
theorem B36296785 : Blo 1861632 36296785 := bstep (se 2 (by rfl) ⟨13611294, by rfl⟩ : syracuseStep 36296785 = 27222589) B27222589
theorem B11327635 : Blo 1861632 11327635 := bstep (se 1 (by rfl) ⟨8495726, by rfl⟩ : syracuseStep 11327635 = 16991453) B16991453
theorem B4192487 : Blo 1861632 4192487 := bstep (se 1 (by rfl) ⟨3144365, by rfl⟩ : syracuseStep 4192487 = 6288731) B6288731
theorem B458889461 : Blo 1861632 458889461 := bstep (se 5 (by rfl) ⟨21510443, by rfl⟩ : syracuseStep 458889461 = 43020887) B43020887
theorem B4192505 : Blo 1861632 4192505 := bstep (se 2 (by rfl) ⟨1572189, by rfl⟩ : syracuseStep 4192505 = 3144379) B3144379
theorem B3537199 : Blo 1861632 3537199 := bstep (se 1 (by rfl) ⟨2652899, by rfl⟩ : syracuseStep 3537199 = 5305799) B5305799
theorem B4192559 : Blo 1861632 4192559 := bstep (se 1 (by rfl) ⟨3144419, by rfl⟩ : syracuseStep 4192559 = 6288839) B6288839
theorem B2095519 : Blo 1861632 2095519 := bstep (se 1 (by rfl) ⟨1571639, by rfl⟩ : syracuseStep 2095519 = 3143279) B3143279
theorem B3144143 : Blo 1861632 3144143 := bstep (se 1 (by rfl) ⟨2358107, by rfl⟩ : syracuseStep 3144143 = 4716215) B4716215
theorem B2095591 : Blo 1861632 2095591 := bstep (se 1 (by rfl) ⟨1571693, by rfl⟩ : syracuseStep 2095591 = 3143387) B3143387
theorem B4192775 : Blo 1861632 4192775 := bstep (se 1 (by rfl) ⟨3144581, by rfl⟩ : syracuseStep 4192775 = 6289163) B6289163
theorem B2652763 : Blo 1861632 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B4192955 : Blo 1861632 4192955 := bstep (se 1 (by rfl) ⟨3144716, by rfl⟩ : syracuseStep 4192955 = 6289433) B6289433
theorem B33987575 : Blo 1861632 33987575 := bstep (se 1 (by rfl) ⟨25490681, by rfl⟩ : syracuseStep 33987575 = 50981363) B50981363
theorem B14343257 : Blo 1861632 14343257 := bstep (se 2 (by rfl) ⟨5378721, by rfl⟩ : syracuseStep 14343257 = 10757443) B10757443
theorem B31825223 : Blo 1861632 31825223 := bstep (se 1 (by rfl) ⟨23868917, by rfl⟩ : syracuseStep 31825223 = 47737835) B47737835
theorem B2096455 : Blo 1861632 2096455 := bstep (se 1 (by rfl) ⟨1572341, by rfl⟩ : syracuseStep 2096455 = 3144683) B3144683
theorem B2793179 : Blo 1861632 2793179 := bstep (se 1 (by rfl) ⟨2094884, by rfl⟩ : syracuseStep 2793179 = 4189769) B4189769
theorem B2793449 : Blo 1861632 2793449 := bstep (se 2 (by rfl) ⟨1047543, by rfl⟩ : syracuseStep 2793449 = 2095087) B2095087
theorem B2793527 : Blo 1861632 2793527 := bstep (se 1 (by rfl) ⟨2095145, by rfl⟩ : syracuseStep 2793527 = 4190291) B4190291
theorem B2793647 : Blo 1861632 2793647 := bstep (se 1 (by rfl) ⟨2095235, by rfl⟩ : syracuseStep 2793647 = 4190471) B4190471
theorem B38248685 : Blo 1861632 38248685 := bstep (se 3 (by rfl) ⟨7171628, by rfl⟩ : syracuseStep 38248685 = 14343257) B14343257
theorem B2793851 : Blo 1861632 2793851 := bstep (se 1 (by rfl) ⟨2095388, by rfl⟩ : syracuseStep 2793851 = 4190777) B4190777
theorem B2794025 : Blo 1861632 2794025 := bstep (se 2 (by rfl) ⟨1047759, by rfl⟩ : syracuseStep 2794025 = 2095519) B2095519
theorem B27206279 : Blo 1861632 27206279 := bstep (se 1 (by rfl) ⟨20404709, by rfl⟩ : syracuseStep 27206279 = 40809419) B40809419
theorem B2794121 : Blo 1861632 2794121 := bstep (se 2 (by rfl) ⟨1047795, by rfl⟩ : syracuseStep 2794121 = 2095591) B2095591
theorem B8946463 : Blo 1861632 8946463 := bstep (se 1 (by rfl) ⟨6709847, by rfl⟩ : syracuseStep 8946463 = 13419695) B13419695
theorem B10748713 : Blo 1861632 10748713 := bstep (se 2 (by rfl) ⟨4030767, by rfl⟩ : syracuseStep 10748713 = 8061535) B8061535
theorem B2982719 : Blo 1861632 2982719 := bstep (se 1 (by rfl) ⟨2237039, by rfl⟩ : syracuseStep 2982719 = 4474079) B4474079
theorem B2794331 : Blo 1861632 2794331 := bstep (se 1 (by rfl) ⟨2095748, by rfl⟩ : syracuseStep 2794331 = 4191497) B4191497
theorem B2794367 : Blo 1861632 2794367 := bstep (se 1 (by rfl) ⟨2095775, by rfl⟩ : syracuseStep 2794367 = 4191551) B4191551
theorem B271975319 : Blo 1861632 271975319 := bstep (se 1 (by rfl) ⟨203981489, by rfl⟩ : syracuseStep 271975319 = 407962979) B407962979
theorem B2794439 : Blo 1861632 2794439 := bstep (se 1 (by rfl) ⟨2095829, by rfl⟩ : syracuseStep 2794439 = 4191659) B4191659
theorem B3777599 : Blo 1861632 3777599 := bstep (se 1 (by rfl) ⟨2833199, by rfl⟩ : syracuseStep 3777599 = 5666399) B5666399
theorem B2794655 : Blo 1861632 2794655 := bstep (se 1 (by rfl) ⟨2095991, by rfl⟩ : syracuseStep 2794655 = 4191983) B4191983
theorem B2794799 : Blo 1861632 2794799 := bstep (se 1 (by rfl) ⟨2096099, by rfl⟩ : syracuseStep 2794799 = 4192199) B4192199
theorem B3106127 : Blo 1861632 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B129090905 : Blo 1861632 129090905 := bstep (se 2 (by rfl) ⟨48409089, by rfl⟩ : syracuseStep 129090905 = 96818179) B96818179
theorem B17892737 : Blo 1861632 17892737 := bstep (se 2 (by rfl) ⟨6709776, by rfl⟩ : syracuseStep 17892737 = 13419553) B13419553
theorem B2794991 : Blo 1861632 2794991 := bstep (se 1 (by rfl) ⟨2096243, by rfl⟩ : syracuseStep 2794991 = 4192487) B4192487
theorem B2795003 : Blo 1861632 2795003 := bstep (se 1 (by rfl) ⟨2096252, by rfl⟩ : syracuseStep 2795003 = 4192505) B4192505
theorem B2795039 : Blo 1861632 2795039 := bstep (se 1 (by rfl) ⟨2096279, by rfl⟩ : syracuseStep 2795039 = 4192559) B4192559
theorem B2795183 : Blo 1861632 2795183 := bstep (se 1 (by rfl) ⟨2096387, by rfl⟩ : syracuseStep 2795183 = 4192775) B4192775
theorem B2795273 : Blo 1861632 2795273 := bstep (se 2 (by rfl) ⟨1048227, by rfl⟩ : syracuseStep 2795273 = 2096455) B2096455
theorem B2795303 : Blo 1861632 2795303 := bstep (se 1 (by rfl) ⟨2096477, by rfl⟩ : syracuseStep 2795303 = 4192955) B4192955
theorem B2951083 : Blo 1861632 2951083 := bstep (se 1 (by rfl) ⟨2213312, by rfl⟩ : syracuseStep 2951083 = 4426625) B4426625
theorem B4245967 : Blo 1861632 4245967 := bstep (se 1 (by rfl) ⟨3184475, by rfl⟩ : syracuseStep 4245967 = 6368951) B6368951
theorem B1862119 : Blo 1861632 1862119 := bstep (se 1 (by rfl) ⟨1396589, by rfl⟩ : syracuseStep 1862119 = 2793179) B2793179
theorem B1862299 : Blo 1861632 1862299 := bstep (se 1 (by rfl) ⟨1396724, by rfl⟩ : syracuseStep 1862299 = 2793449) B2793449
theorem B4188833 : Blo 1861632 4188833 := bstep (se 2 (by rfl) ⟨1570812, by rfl⟩ : syracuseStep 4188833 = 3141625) B3141625
theorem B10603169 : Blo 1861632 10603169 := bstep (se 2 (by rfl) ⟨3976188, by rfl⟩ : syracuseStep 10603169 = 7952377) B7952377
theorem B2984615 : Blo 1861632 2984615 := bstep (se 1 (by rfl) ⟨2238461, by rfl⟩ : syracuseStep 2984615 = 4476923) B4476923
theorem B5303065 : Blo 1861632 5303065 := bstep (se 2 (by rfl) ⟨1988649, by rfl⟩ : syracuseStep 5303065 = 3977299) B3977299
theorem B4189193 : Blo 1861632 4189193 := bstep (se 2 (by rfl) ⟨1570947, by rfl⟩ : syracuseStep 4189193 = 3141895) B3141895
theorem B43002899 : Blo 1861632 43002899 := bstep (se 1 (by rfl) ⟨32252174, by rfl⟩ : syracuseStep 43002899 = 64504349) B64504349
theorem B5303407 : Blo 1861632 5303407 := bstep (se 1 (by rfl) ⟨3977555, by rfl⟩ : syracuseStep 5303407 = 7955111) B7955111
theorem B1862767 : Blo 1861632 1862767 := bstep (se 1 (by rfl) ⟨1397075, by rfl⟩ : syracuseStep 1862767 = 2794151) B2794151
theorem B7072879 : Blo 1861632 7072879 := bstep (se 1 (by rfl) ⟨5304659, by rfl⟩ : syracuseStep 7072879 = 10609319) B10609319
theorem B14142599 : Blo 1861632 14142599 := bstep (se 1 (by rfl) ⟨10606949, by rfl⟩ : syracuseStep 14142599 = 21213899) B21213899
theorem B1862847 : Blo 1861632 1862847 := bstep (se 1 (by rfl) ⟨1397135, by rfl⟩ : syracuseStep 1862847 = 2794271) B2794271
theorem B4189391 : Blo 1861632 4189391 := bstep (se 1 (by rfl) ⟨3142043, by rfl⟩ : syracuseStep 4189391 = 6284087) B6284087
theorem B1862863 : Blo 1861632 1862863 := bstep (se 1 (by rfl) ⟨1397147, by rfl⟩ : syracuseStep 1862863 = 2794295) B2794295
theorem B1862983 : Blo 1861632 1862983 := bstep (se 1 (by rfl) ⟨1397237, by rfl⟩ : syracuseStep 1862983 = 2794475) B2794475
theorem B10202791 : Blo 1861632 10202791 := bstep (se 1 (by rfl) ⟨7652093, by rfl⟩ : syracuseStep 10202791 = 15304187) B15304187
theorem B40283993 : Blo 1861632 40283993 := bstep (se 2 (by rfl) ⟨15106497, by rfl⟩ : syracuseStep 40283993 = 30212995) B30212995
theorem B4190183 : Blo 1861632 4190183 := bstep (se 1 (by rfl) ⟨3142637, by rfl⟩ : syracuseStep 4190183 = 6285275) B6285275
theorem B5304295 : Blo 1861632 5304295 := bstep (se 1 (by rfl) ⟨3978221, by rfl⟩ : syracuseStep 5304295 = 7956443) B7956443
theorem B3141787 : Blo 1861632 3141787 := bstep (se 1 (by rfl) ⟨2356340, by rfl⟩ : syracuseStep 3141787 = 4712681) B4712681
theorem B4190363 : Blo 1861632 4190363 := bstep (se 1 (by rfl) ⟨3142772, by rfl⟩ : syracuseStep 4190363 = 6285545) B6285545
theorem B305926307 : Blo 1861632 305926307 := bstep (se 1 (by rfl) ⟨229444730, by rfl⟩ : syracuseStep 305926307 = 458889461) B458889461
theorem B1765290257 : Blo 1861632 1765290257 := bstep (se 2 (by rfl) ⟨661983846, by rfl⟩ : syracuseStep 1765290257 = 1323967693) B1323967693
theorem B4190543 : Blo 1861632 4190543 := bstep (se 1 (by rfl) ⟨3142907, by rfl⟩ : syracuseStep 4190543 = 6285815) B6285815
theorem B4190561 : Blo 1861632 4190561 := bstep (se 2 (by rfl) ⟨1571460, by rfl⟩ : syracuseStep 4190561 = 3142921) B3142921
theorem B3142057 : Blo 1861632 3142057 := bstep (se 2 (by rfl) ⟨1178271, by rfl⟩ : syracuseStep 3142057 = 2356543) B2356543
theorem B4190633 : Blo 1861632 4190633 := bstep (se 2 (by rfl) ⟨1571487, by rfl⟩ : syracuseStep 4190633 = 3142975) B3142975
theorem B4190651 : Blo 1861632 4190651 := bstep (se 1 (by rfl) ⟨3142988, by rfl⟩ : syracuseStep 4190651 = 6285977) B6285977
theorem B4190939 : Blo 1861632 4190939 := bstep (se 1 (by rfl) ⟨3143204, by rfl⟩ : syracuseStep 4190939 = 6286409) B6286409
theorem B8950537 : Blo 1861632 8950537 := bstep (se 2 (by rfl) ⟨3356451, by rfl⟩ : syracuseStep 8950537 = 6712903) B6712903
theorem B3535643 : Blo 1861632 3535643 := bstep (se 1 (by rfl) ⟨2651732, by rfl⟩ : syracuseStep 3535643 = 5303465) B5303465
theorem B5305115 : Blo 1861632 5305115 := bstep (se 1 (by rfl) ⟨3978836, by rfl⟩ : syracuseStep 5305115 = 7957673) B7957673
theorem B6288191 : Blo 1861632 6288191 := bstep (se 1 (by rfl) ⟨4716143, by rfl⟩ : syracuseStep 6288191 = 9432287) B9432287
theorem B4191209 : Blo 1861632 4191209 := bstep (se 2 (by rfl) ⟨1571703, by rfl⟩ : syracuseStep 4191209 = 3143407) B3143407
theorem B4715567 : Blo 1861632 4715567 := bstep (se 1 (by rfl) ⟨3536675, by rfl⟩ : syracuseStep 4715567 = 7073351) B7073351
theorem B2651231 : Blo 1861632 2651231 := bstep (se 1 (by rfl) ⟨1988423, by rfl⟩ : syracuseStep 2651231 = 3976847) B3976847
theorem B2356391 : Blo 1861632 2356391 := bstep (se 1 (by rfl) ⟨1767293, by rfl⟩ : syracuseStep 2356391 = 3534587) B3534587
theorem B9434555 : Blo 1861632 9434555 := bstep (se 1 (by rfl) ⟨7075916, by rfl⟩ : syracuseStep 9434555 = 14151833) B14151833
theorem B48395713 : Blo 1861632 48395713 := bstep (se 2 (by rfl) ⟨18148392, by rfl⟩ : syracuseStep 48395713 = 36296785) B36296785
theorem B15103513 : Blo 1861632 15103513 := bstep (se 2 (by rfl) ⟨5663817, by rfl⟩ : syracuseStep 15103513 = 11327635) B11327635
theorem B76502593 : Blo 1861632 76502593 := bstep (se 2 (by rfl) ⟨28688472, by rfl⟩ : syracuseStep 76502593 = 57376945) B57376945
theorem B25499225 : Blo 1861632 25499225 := bstep (se 2 (by rfl) ⟨9562209, by rfl⟩ : syracuseStep 25499225 = 19124419) B19124419
theorem B4191911 : Blo 1861632 4191911 := bstep (se 1 (by rfl) ⟨3143933, by rfl⟩ : syracuseStep 4191911 = 6287867) B6287867
theorem B4716265 : Blo 1861632 4716265 := bstep (se 2 (by rfl) ⟨1768599, by rfl⟩ : syracuseStep 4716265 = 3537199) B3537199
theorem B3143495 : Blo 1861632 3143495 := bstep (se 1 (by rfl) ⟨2357621, by rfl⟩ : syracuseStep 3143495 = 4715243) B4715243
theorem B9426779 : Blo 1861632 9426779 := bstep (se 1 (by rfl) ⟨7070084, by rfl⟩ : syracuseStep 9426779 = 14140169) B14140169
theorem B3143515 : Blo 1861632 3143515 := bstep (se 1 (by rfl) ⟨2357636, by rfl⟩ : syracuseStep 3143515 = 4715273) B4715273
theorem B4192091 : Blo 1861632 4192091 := bstep (se 1 (by rfl) ⟨3144068, by rfl⟩ : syracuseStep 4192091 = 6288137) B6288137
theorem B10606585 : Blo 1861632 10606585 := bstep (se 2 (by rfl) ⟨3977469, by rfl⟩ : syracuseStep 10606585 = 7954939) B7954939
theorem B4716539 : Blo 1861632 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B3537017 : Blo 1861632 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B15906941 : Blo 1861632 15906941 := bstep (se 3 (by rfl) ⟨2982551, by rfl⟩ : syracuseStep 15906941 = 5965103) B5965103
theorem B14137739 : Blo 1861632 14137739 := bstep (se 1 (by rfl) ⟨10603304, by rfl⟩ : syracuseStep 14137739 = 21206609) B21206609
theorem B24189587 : Blo 1861632 24189587 := bstep (se 1 (by rfl) ⟨18142190, by rfl⟩ : syracuseStep 24189587 = 36284381) B36284381
theorem B2096095 : Blo 1861632 2096095 := bstep (se 1 (by rfl) ⟨1572071, by rfl⟩ : syracuseStep 2096095 = 3144143) B3144143
theorem B5037383 : Blo 1861632 5037383 := bstep (se 1 (by rfl) ⟨3778037, by rfl⟩ : syracuseStep 5037383 = 7556075) B7556075
theorem B22658383 : Blo 1861632 22658383 := bstep (se 1 (by rfl) ⟨16993787, by rfl⟩ : syracuseStep 22658383 = 33987575) B33987575
theorem B23879123 : Blo 1861632 23879123 := bstep (se 1 (by rfl) ⟨17909342, by rfl⟩ : syracuseStep 23879123 = 35818685) B35818685
theorem B21216815 : Blo 1861632 21216815 := bstep (se 1 (by rfl) ⟨15912611, by rfl⟩ : syracuseStep 21216815 = 31825223) B31825223
theorem B7953983 : Blo 1861632 7953983 := bstep (se 1 (by rfl) ⟨5965487, by rfl⟩ : syracuseStep 7953983 = 11930975) B11930975
theorem B2793071 : Blo 1861632 2793071 := bstep (se 1 (by rfl) ⟨2094803, by rfl⟩ : syracuseStep 2793071 = 4189607) B4189607
theorem B21503663 : Blo 1861632 21503663 := bstep (se 1 (by rfl) ⟨16127747, by rfl⟩ : syracuseStep 21503663 = 32255495) B32255495
theorem B2793191 : Blo 1861632 2793191 := bstep (se 1 (by rfl) ⟨2094893, by rfl⟩ : syracuseStep 2793191 = 4189787) B4189787
theorem B2793467 : Blo 1861632 2793467 := bstep (se 1 (by rfl) ⟨2095100, by rfl⟩ : syracuseStep 2793467 = 4190201) B4190201
theorem B2793575 : Blo 1861632 2793575 := bstep (se 1 (by rfl) ⟨2095181, by rfl⟩ : syracuseStep 2793575 = 4190363) B4190363
theorem B2793695 : Blo 1861632 2793695 := bstep (se 1 (by rfl) ⟨2095271, by rfl⟩ : syracuseStep 2793695 = 4190543) B4190543
theorem B2793707 : Blo 1861632 2793707 := bstep (se 1 (by rfl) ⟨2095280, by rfl⟩ : syracuseStep 2793707 = 4190561) B4190561
theorem B7069949 : Blo 1861632 7069949 := bstep (se 3 (by rfl) ⟨1325615, by rfl⟩ : syracuseStep 7069949 = 2651231) B2651231
theorem B2793755 : Blo 1861632 2793755 := bstep (se 1 (by rfl) ⟨2095316, by rfl⟩ : syracuseStep 2793755 = 4190633) B4190633
theorem B2793767 : Blo 1861632 2793767 := bstep (se 1 (by rfl) ⟨2095325, by rfl⟩ : syracuseStep 2793767 = 4190651) B4190651
theorem B18137519 : Blo 1861632 18137519 := bstep (se 1 (by rfl) ⟨13603139, by rfl⟩ : syracuseStep 18137519 = 27206279) B27206279
theorem B6283709 : Blo 1861632 6283709 := bstep (se 3 (by rfl) ⟨1178195, by rfl⟩ : syracuseStep 6283709 = 2356391) B2356391
theorem B2793959 : Blo 1861632 2793959 := bstep (se 1 (by rfl) ⟨2095469, by rfl⟩ : syracuseStep 2793959 = 4190939) B4190939
theorem B5661289 : Blo 1861632 5661289 := bstep (se 2 (by rfl) ⟨2122983, by rfl⟩ : syracuseStep 5661289 = 4245967) B4245967
theorem B2794139 : Blo 1861632 2794139 := bstep (se 1 (by rfl) ⟨2095604, by rfl⟩ : syracuseStep 2794139 = 4191209) B4191209
theorem B8283005 : Blo 1861632 8283005 := bstep (se 3 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 8283005 = 3106127) B3106127
theorem B11928491 : Blo 1861632 11928491 := bstep (se 1 (by rfl) ⟨8946368, by rfl⟩ : syracuseStep 11928491 = 17892737) B17892737
theorem B7070753 : Blo 1861632 7070753 := bstep (se 2 (by rfl) ⟨2651532, by rfl⟩ : syracuseStep 7070753 = 5303065) B5303065
theorem B11928617 : Blo 1861632 11928617 := bstep (se 2 (by rfl) ⟨4473231, by rfl⟩ : syracuseStep 11928617 = 8946463) B8946463
theorem B16999483 : Blo 1861632 16999483 := bstep (se 1 (by rfl) ⟨12749612, by rfl⟩ : syracuseStep 16999483 = 25499225) B25499225
theorem B2794607 : Blo 1861632 2794607 := bstep (se 1 (by rfl) ⟨2095955, by rfl⟩ : syracuseStep 2794607 = 4191911) B4191911
theorem B6284519 : Blo 1861632 6284519 := bstep (se 1 (by rfl) ⟨4713389, by rfl⟩ : syracuseStep 6284519 = 9426779) B9426779
theorem B2794727 : Blo 1861632 2794727 := bstep (se 1 (by rfl) ⟨2096045, by rfl⟩ : syracuseStep 2794727 = 4192091) B4192091
theorem B2794793 : Blo 1861632 2794793 := bstep (se 2 (by rfl) ⟨1048047, by rfl⟩ : syracuseStep 2794793 = 2096095) B2096095
theorem B7071209 : Blo 1861632 7071209 := bstep (se 2 (by rfl) ⟨2651703, by rfl⟩ : syracuseStep 7071209 = 5303407) B5303407
theorem B9430505 : Blo 1861632 9430505 := bstep (se 2 (by rfl) ⟨3536439, by rfl⟩ : syracuseStep 9430505 = 7072879) B7072879
theorem B20138017 : Blo 1861632 20138017 := bstep (se 2 (by rfl) ⟨7551756, by rfl⟩ : syracuseStep 20138017 = 15103513) B15103513
theorem B15739109 : Blo 1861632 15739109 := bstep (se 4 (by rfl) ⟨1475541, by rfl⟩ : syracuseStep 15739109 = 2951083) B2951083
theorem B15919415 : Blo 1861632 15919415 := bstep (se 1 (by rfl) ⟨11939561, by rfl⟩ : syracuseStep 15919415 = 23879123) B23879123
theorem B5302655 : Blo 1861632 5302655 := bstep (se 1 (by rfl) ⟨3976991, by rfl⟩ : syracuseStep 5302655 = 7953983) B7953983
theorem B1862047 : Blo 1861632 1862047 := bstep (se 1 (by rfl) ⟨1396535, by rfl⟩ : syracuseStep 1862047 = 2793071) B2793071
theorem B1862127 : Blo 1861632 1862127 := bstep (se 1 (by rfl) ⟨1396595, by rfl⟩ : syracuseStep 1862127 = 2793191) B2793191
theorem B26855995 : Blo 1861632 26855995 := bstep (se 1 (by rfl) ⟨20141996, by rfl⟩ : syracuseStep 26855995 = 40283993) B40283993
theorem B7072393 : Blo 1861632 7072393 := bstep (se 2 (by rfl) ⟨2652147, by rfl⟩ : syracuseStep 7072393 = 5304295) B5304295
theorem B14142113 : Blo 1861632 14142113 := bstep (se 2 (by rfl) ⟨5303292, by rfl⟩ : syracuseStep 14142113 = 10606585) B10606585
theorem B1862311 : Blo 1861632 1862311 := bstep (se 1 (by rfl) ⟨1396733, by rfl⟩ : syracuseStep 1862311 = 2793467) B2793467
theorem B1862351 : Blo 1861632 1862351 := bstep (se 1 (by rfl) ⟨1396763, by rfl⟩ : syracuseStep 1862351 = 2793527) B2793527
theorem B203950871 : Blo 1861632 203950871 := bstep (se 1 (by rfl) ⟨152963153, by rfl⟩ : syracuseStep 203950871 = 305926307) B305926307
theorem B1862431 : Blo 1861632 1862431 := bstep (se 1 (by rfl) ⟨1396823, by rfl⟩ : syracuseStep 1862431 = 2793647) B2793647
theorem B4189049 : Blo 1861632 4189049 := bstep (se 2 (by rfl) ⟨1570893, by rfl⟩ : syracuseStep 4189049 = 3141787) B3141787
theorem B1862567 : Blo 1861632 1862567 := bstep (se 1 (by rfl) ⟨1396925, by rfl⟩ : syracuseStep 1862567 = 2793851) B2793851
theorem B1862683 : Blo 1861632 1862683 := bstep (se 1 (by rfl) ⟨1397012, by rfl⟩ : syracuseStep 1862683 = 2794025) B2794025
theorem B1862747 : Blo 1861632 1862747 := bstep (se 1 (by rfl) ⟨1397060, by rfl⟩ : syracuseStep 1862747 = 2794121) B2794121
theorem B4189409 : Blo 1861632 4189409 := bstep (se 2 (by rfl) ⟨1571028, by rfl⟩ : syracuseStep 4189409 = 3142057) B3142057
theorem B1862887 : Blo 1861632 1862887 := bstep (se 1 (by rfl) ⟨1397165, by rfl⟩ : syracuseStep 1862887 = 2794331) B2794331
theorem B1862911 : Blo 1861632 1862911 := bstep (se 1 (by rfl) ⟨1397183, by rfl⟩ : syracuseStep 1862911 = 2794367) B2794367
theorem B181316879 : Blo 1861632 181316879 := bstep (se 1 (by rfl) ⟨135987659, by rfl⟩ : syracuseStep 181316879 = 271975319) B271975319
theorem B1862959 : Blo 1861632 1862959 := bstep (se 1 (by rfl) ⟨1397219, by rfl⟩ : syracuseStep 1862959 = 2794439) B2794439
theorem B2518399 : Blo 1861632 2518399 := bstep (se 1 (by rfl) ⟨1888799, by rfl⟩ : syracuseStep 2518399 = 3777599) B3777599
theorem B1863103 : Blo 1861632 1863103 := bstep (se 1 (by rfl) ⟨1397327, by rfl⟩ : syracuseStep 1863103 = 2794655) B2794655
theorem B1863199 : Blo 1861632 1863199 := bstep (se 1 (by rfl) ⟨1397399, by rfl⟩ : syracuseStep 1863199 = 2794799) B2794799
theorem B86060603 : Blo 1861632 86060603 := bstep (se 1 (by rfl) ⟨64545452, by rfl⟩ : syracuseStep 86060603 = 129090905) B129090905
theorem B1863327 : Blo 1861632 1863327 := bstep (se 1 (by rfl) ⟨1397495, by rfl⟩ : syracuseStep 1863327 = 2794991) B2794991
theorem B1863335 : Blo 1861632 1863335 := bstep (se 1 (by rfl) ⟨1397501, by rfl⟩ : syracuseStep 1863335 = 2795003) B2795003
theorem B1863359 : Blo 1861632 1863359 := bstep (se 1 (by rfl) ⟨1397519, by rfl⟩ : syracuseStep 1863359 = 2795039) B2795039
theorem B14331617 : Blo 1861632 14331617 := bstep (se 2 (by rfl) ⟨5374356, by rfl⟩ : syracuseStep 14331617 = 10748713) B10748713
theorem B1863455 : Blo 1861632 1863455 := bstep (se 1 (by rfl) ⟨1397591, by rfl⟩ : syracuseStep 1863455 = 2795183) B2795183
theorem B1863515 : Blo 1861632 1863515 := bstep (se 1 (by rfl) ⟨1397636, by rfl⟩ : syracuseStep 1863515 = 2795273) B2795273
theorem B1863535 : Blo 1861632 1863535 := bstep (se 1 (by rfl) ⟨1397651, by rfl⟩ : syracuseStep 1863535 = 2795303) B2795303
theorem B10604627 : Blo 1861632 10604627 := bstep (se 1 (by rfl) ⟨7953470, by rfl⟩ : syracuseStep 10604627 = 15906941) B15906941
theorem B9425159 : Blo 1861632 9425159 := bstep (se 1 (by rfl) ⟨7068869, by rfl⟩ : syracuseStep 9425159 = 14137739) B14137739
theorem B16126391 : Blo 1861632 16126391 := bstep (se 1 (by rfl) ⟨12094793, by rfl⟩ : syracuseStep 16126391 = 24189587) B24189587
theorem B28668599 : Blo 1861632 28668599 := bstep (se 1 (by rfl) ⟨21501449, by rfl⟩ : syracuseStep 28668599 = 43002899) B43002899
theorem B102003457 : Blo 1861632 102003457 := bstep (se 2 (by rfl) ⟨38251296, by rfl⟩ : syracuseStep 102003457 = 76502593) B76502593
theorem B13603721 : Blo 1861632 13603721 := bstep (se 2 (by rfl) ⟨5101395, by rfl⟩ : syracuseStep 13603721 = 10202791) B10202791
theorem B6288353 : Blo 1861632 6288353 := bstep (se 2 (by rfl) ⟨2358132, by rfl⟩ : syracuseStep 6288353 = 4716265) B4716265
theorem B14144543 : Blo 1861632 14144543 := bstep (se 1 (by rfl) ⟨10608407, by rfl⟩ : syracuseStep 14144543 = 21216815) B21216815
theorem B4191353 : Blo 1861632 4191353 := bstep (se 2 (by rfl) ⟨1571757, by rfl⟩ : syracuseStep 4191353 = 3143515) B3143515
theorem B25499123 : Blo 1861632 25499123 := bstep (se 1 (by rfl) ⟨19124342, by rfl⟩ : syracuseStep 25499123 = 38248685) B38248685
theorem B1176860171 : Blo 1861632 1176860171 := bstep (se 1 (by rfl) ⟨882645128, by rfl⟩ : syracuseStep 1176860171 = 1765290257) B1765290257
theorem B2357095 : Blo 1861632 2357095 := bstep (se 1 (by rfl) ⟨1767821, by rfl⟩ : syracuseStep 2357095 = 3535643) B3535643
theorem B1988479 : Blo 1861632 1988479 := bstep (se 1 (by rfl) ⟨1491359, by rfl⟩ : syracuseStep 1988479 = 2982719) B2982719
theorem B4192127 : Blo 1861632 4192127 := bstep (se 1 (by rfl) ⟨3144095, by rfl⟩ : syracuseStep 4192127 = 6288191) B6288191
theorem B3143711 : Blo 1861632 3143711 := bstep (se 1 (by rfl) ⟨2357783, by rfl⟩ : syracuseStep 3143711 = 4715567) B4715567
theorem B6289703 : Blo 1861632 6289703 := bstep (se 1 (by rfl) ⟨4717277, by rfl⟩ : syracuseStep 6289703 = 9434555) B9434555
theorem B11934049 : Blo 1861632 11934049 := bstep (se 2 (by rfl) ⟨4475268, by rfl⟩ : syracuseStep 11934049 = 8950537) B8950537
theorem B2095663 : Blo 1861632 2095663 := bstep (se 1 (by rfl) ⟨1571747, by rfl⟩ : syracuseStep 2095663 = 3143495) B3143495
theorem B3144359 : Blo 1861632 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B2358011 : Blo 1861632 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B30211177 : Blo 1861632 30211177 := bstep (se 2 (by rfl) ⟨11329191, by rfl⟩ : syracuseStep 30211177 = 22658383) B22658383
theorem B2792555 : Blo 1861632 2792555 := bstep (se 1 (by rfl) ⟨2094416, by rfl⟩ : syracuseStep 2792555 = 4188833) B4188833
theorem B7068779 : Blo 1861632 7068779 := bstep (se 1 (by rfl) ⟨5301584, by rfl⟩ : syracuseStep 7068779 = 10603169) B10603169
theorem B1989743 : Blo 1861632 1989743 := bstep (se 1 (by rfl) ⟨1492307, by rfl⟩ : syracuseStep 1989743 = 2984615) B2984615
theorem B64527617 : Blo 1861632 64527617 := bstep (se 2 (by rfl) ⟨24197856, by rfl⟩ : syracuseStep 64527617 = 48395713) B48395713
theorem B2792795 : Blo 1861632 2792795 := bstep (se 1 (by rfl) ⟨2094596, by rfl⟩ : syracuseStep 2792795 = 4189193) B4189193
theorem B14146973 : Blo 1861632 14146973 := bstep (se 3 (by rfl) ⟨2652557, by rfl⟩ : syracuseStep 14146973 = 5305115) B5305115
theorem B9428399 : Blo 1861632 9428399 := bstep (se 1 (by rfl) ⟨7071299, by rfl⟩ : syracuseStep 9428399 = 14142599) B14142599
theorem B2792927 : Blo 1861632 2792927 := bstep (se 1 (by rfl) ⟨2094695, by rfl⟩ : syracuseStep 2792927 = 4189391) B4189391
theorem B3358255 : Blo 1861632 3358255 := bstep (se 1 (by rfl) ⟨2518691, by rfl⟩ : syracuseStep 3358255 = 5037383) B5037383
theorem B14335775 : Blo 1861632 14335775 := bstep (se 1 (by rfl) ⟨10751831, by rfl⟩ : syracuseStep 14335775 = 21503663) B21503663
theorem B2793455 : Blo 1861632 2793455 := bstep (se 1 (by rfl) ⟨2095091, by rfl⟩ : syracuseStep 2793455 = 4190183) B4190183
theorem B7069751 : Blo 1861632 7069751 := bstep (se 1 (by rfl) ⟨5302313, by rfl⟩ : syracuseStep 7069751 = 10604627) B10604627
theorem B6283439 : Blo 1861632 6283439 := bstep (se 1 (by rfl) ⟨4712579, by rfl⟩ : syracuseStep 6283439 = 9425159) B9425159
theorem B12091679 : Blo 1861632 12091679 := bstep (se 1 (by rfl) ⟨9068759, by rfl⟩ : syracuseStep 12091679 = 18137519) B18137519
theorem B19112399 : Blo 1861632 19112399 := bstep (se 1 (by rfl) ⟨14334299, by rfl⟩ : syracuseStep 19112399 = 28668599) B28668599
theorem B5522003 : Blo 1861632 5522003 := bstep (se 1 (by rfl) ⟨4141502, by rfl⟩ : syracuseStep 5522003 = 8283005) B8283005
theorem B9429695 : Blo 1861632 9429695 := bstep (se 1 (by rfl) ⟨7072271, by rfl⟩ : syracuseStep 9429695 = 14144543) B14144543
theorem B2794217 : Blo 1861632 2794217 := bstep (se 2 (by rfl) ⟨1047831, by rfl⟩ : syracuseStep 2794217 = 2095663) B2095663
theorem B35807993 : Blo 1861632 35807993 := bstep (se 2 (by rfl) ⟨13427997, by rfl⟩ : syracuseStep 35807993 = 26855995) B26855995
theorem B2794235 : Blo 1861632 2794235 := bstep (se 1 (by rfl) ⟨2095676, by rfl⟩ : syracuseStep 2794235 = 4191353) B4191353
theorem B9429857 : Blo 1861632 9429857 := bstep (se 2 (by rfl) ⟨3536196, by rfl⟩ : syracuseStep 9429857 = 7072393) B7072393
theorem B16999415 : Blo 1861632 16999415 := bstep (se 1 (by rfl) ⟨12749561, by rfl⟩ : syracuseStep 16999415 = 25499123) B25499123
theorem B136004609 : Blo 1861632 136004609 := bstep (se 2 (by rfl) ⟨51001728, by rfl⟩ : syracuseStep 136004609 = 102003457) B102003457
theorem B784573447 : Blo 1861632 784573447 := bstep (se 1 (by rfl) ⟨588430085, by rfl⟩ : syracuseStep 784573447 = 1176860171) B1176860171
theorem B2794751 : Blo 1861632 2794751 := bstep (se 1 (by rfl) ⟨2096063, by rfl⟩ : syracuseStep 2794751 = 4192127) B4192127
theorem B40281569 : Blo 1861632 40281569 := bstep (se 2 (by rfl) ⟨15105588, by rfl⟩ : syracuseStep 40281569 = 30211177) B30211177
theorem B1861703 : Blo 1861632 1861703 := bstep (se 1 (by rfl) ⟨1396277, by rfl⟩ : syracuseStep 1861703 = 2792555) B2792555
theorem B4712519 : Blo 1861632 4712519 := bstep (se 1 (by rfl) ⟨3534389, by rfl⟩ : syracuseStep 4712519 = 7068779) B7068779
theorem B43018411 : Blo 1861632 43018411 := bstep (se 1 (by rfl) ⟨32263808, by rfl⟩ : syracuseStep 43018411 = 64527617) B64527617
theorem B1861863 : Blo 1861632 1861863 := bstep (se 1 (by rfl) ⟨1396397, by rfl⟩ : syracuseStep 1861863 = 2792795) B2792795
theorem B9431315 : Blo 1861632 9431315 := bstep (se 1 (by rfl) ⟨7073486, by rfl⟩ : syracuseStep 9431315 = 14146973) B14146973
theorem B6285599 : Blo 1861632 6285599 := bstep (se 1 (by rfl) ⟨4714199, by rfl⟩ : syracuseStep 6285599 = 9428399) B9428399
theorem B1861951 : Blo 1861632 1861951 := bstep (se 1 (by rfl) ⟨1396463, by rfl⟩ : syracuseStep 1861951 = 2792927) B2792927
theorem B36276589 : Blo 1861632 36276589 := bstep (se 3 (by rfl) ⟨6801860, by rfl⟩ : syracuseStep 36276589 = 13603721) B13603721
theorem B9554411 : Blo 1861632 9554411 := bstep (se 1 (by rfl) ⟨7165808, by rfl⟩ : syracuseStep 9554411 = 14331617) B14331617
theorem B1862303 : Blo 1861632 1862303 := bstep (se 1 (by rfl) ⟨1396727, by rfl⟩ : syracuseStep 1862303 = 2793455) B2793455
theorem B1862383 : Blo 1861632 1862383 := bstep (se 1 (by rfl) ⟨1396787, by rfl⟩ : syracuseStep 1862383 = 2793575) B2793575
theorem B1862463 : Blo 1861632 1862463 := bstep (se 1 (by rfl) ⟨1396847, by rfl⟩ : syracuseStep 1862463 = 2793695) B2793695
theorem B1862471 : Blo 1861632 1862471 := bstep (se 1 (by rfl) ⟨1396853, by rfl⟩ : syracuseStep 1862471 = 2793707) B2793707
theorem B4713299 : Blo 1861632 4713299 := bstep (se 1 (by rfl) ⟨3534974, by rfl⟩ : syracuseStep 4713299 = 7069949) B7069949
theorem B1862503 : Blo 1861632 1862503 := bstep (se 1 (by rfl) ⟨1396877, by rfl⟩ : syracuseStep 1862503 = 2793755) B2793755
theorem B1862511 : Blo 1861632 1862511 := bstep (se 1 (by rfl) ⟨1396883, by rfl⟩ : syracuseStep 1862511 = 2793767) B2793767
theorem B4189139 : Blo 1861632 4189139 := bstep (se 1 (by rfl) ⟨3141854, by rfl⟩ : syracuseStep 4189139 = 6283709) B6283709
theorem B1862639 : Blo 1861632 1862639 := bstep (se 1 (by rfl) ⟨1396979, by rfl⟩ : syracuseStep 1862639 = 2793959) B2793959
theorem B1862759 : Blo 1861632 1862759 := bstep (se 1 (by rfl) ⟨1397069, by rfl⟩ : syracuseStep 1862759 = 2794139) B2794139
theorem B15912065 : Blo 1861632 15912065 := bstep (se 2 (by rfl) ⟨5967024, by rfl⟩ : syracuseStep 15912065 = 11934049) B11934049
theorem B4713835 : Blo 1861632 4713835 := bstep (se 1 (by rfl) ⟨3535376, by rfl⟩ : syracuseStep 4713835 = 7070753) B7070753
theorem B1863071 : Blo 1861632 1863071 := bstep (se 1 (by rfl) ⟨1397303, by rfl⟩ : syracuseStep 1863071 = 2794607) B2794607
theorem B7548385 : Blo 1861632 7548385 := bstep (se 2 (by rfl) ⟨2830644, by rfl⟩ : syracuseStep 7548385 = 5661289) B5661289
theorem B4189679 : Blo 1861632 4189679 := bstep (se 1 (by rfl) ⟨3142259, by rfl⟩ : syracuseStep 4189679 = 6284519) B6284519
theorem B1863151 : Blo 1861632 1863151 := bstep (se 1 (by rfl) ⟨1397363, by rfl⟩ : syracuseStep 1863151 = 2794727) B2794727
theorem B1863195 : Blo 1861632 1863195 := bstep (se 1 (by rfl) ⟨1397396, by rfl⟩ : syracuseStep 1863195 = 2794793) B2794793
theorem B4714139 : Blo 1861632 4714139 := bstep (se 1 (by rfl) ⟨3535604, by rfl⟩ : syracuseStep 4714139 = 7071209) B7071209
theorem B6287003 : Blo 1861632 6287003 := bstep (se 1 (by rfl) ⟨4715252, by rfl⟩ : syracuseStep 6287003 = 9430505) B9430505
theorem B43003709 : Blo 1861632 43003709 := bstep (se 3 (by rfl) ⟨8063195, by rfl⟩ : syracuseStep 43003709 = 16126391) B16126391
theorem B229494941 : Blo 1861632 229494941 := bstep (se 3 (by rfl) ⟨43030301, by rfl⟩ : syracuseStep 229494941 = 86060603) B86060603
theorem B10612943 : Blo 1861632 10612943 := bstep (se 1 (by rfl) ⟨7959707, by rfl⟩ : syracuseStep 10612943 = 15919415) B15919415
theorem B3535103 : Blo 1861632 3535103 := bstep (se 1 (by rfl) ⟨2651327, by rfl⟩ : syracuseStep 3535103 = 5302655) B5302655
theorem B135967247 : Blo 1861632 135967247 := bstep (se 1 (by rfl) ⟨101975435, by rfl⟩ : syracuseStep 135967247 = 203950871) B203950871
theorem B6288029 : Blo 1861632 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B4477673 : Blo 1861632 4477673 := bstep (se 2 (by rfl) ⟨1679127, by rfl⟩ : syracuseStep 4477673 = 3358255) B3358255
theorem B120877919 : Blo 1861632 120877919 := bstep (se 1 (by rfl) ⟨90658439, by rfl⟩ : syracuseStep 120877919 = 181316879) B181316879
theorem B3142793 : Blo 1861632 3142793 := bstep (se 2 (by rfl) ⟨1178547, by rfl⟩ : syracuseStep 3142793 = 2357095) B2357095
theorem B2651305 : Blo 1861632 2651305 := bstep (se 2 (by rfl) ⟨994239, by rfl⟩ : syracuseStep 2651305 = 1988479) B1988479
theorem B9557183 : Blo 1861632 9557183 := bstep (se 1 (by rfl) ⟨7167887, by rfl⟩ : syracuseStep 9557183 = 14335775) B14335775
theorem B26850689 : Blo 1861632 26850689 := bstep (se 2 (by rfl) ⟨10069008, by rfl⟩ : syracuseStep 26850689 = 20138017) B20138017
theorem B5305981 : Blo 1861632 5305981 := bstep (se 3 (by rfl) ⟨994871, by rfl⟩ : syracuseStep 5305981 = 1989743) B1989743
theorem B7952327 : Blo 1861632 7952327 := bstep (se 1 (by rfl) ⟨5964245, by rfl⟩ : syracuseStep 7952327 = 11928491) B11928491
theorem B4192235 : Blo 1861632 4192235 := bstep (se 1 (by rfl) ⟨3144176, by rfl⟩ : syracuseStep 4192235 = 6288353) B6288353
theorem B7952411 : Blo 1861632 7952411 := bstep (se 1 (by rfl) ⟨5964308, by rfl⟩ : syracuseStep 7952411 = 11928617) B11928617
theorem B2095807 : Blo 1861632 2095807 := bstep (se 1 (by rfl) ⟨1571855, by rfl⟩ : syracuseStep 2095807 = 3143711) B3143711
theorem B22665977 : Blo 1861632 22665977 := bstep (se 2 (by rfl) ⟨8499741, by rfl⟩ : syracuseStep 22665977 = 16999483) B16999483
theorem B10492739 : Blo 1861632 10492739 := bstep (se 1 (by rfl) ⟨7869554, by rfl⟩ : syracuseStep 10492739 = 15739109) B15739109
theorem B4193135 : Blo 1861632 4193135 := bstep (se 1 (by rfl) ⟨3144851, by rfl⟩ : syracuseStep 4193135 = 6289703) B6289703
theorem B9428075 : Blo 1861632 9428075 := bstep (se 1 (by rfl) ⟨7071056, by rfl⟩ : syracuseStep 9428075 = 14142113) B14142113
theorem B2096239 : Blo 1861632 2096239 := bstep (se 1 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 2096239 = 3144359) B3144359
theorem B3357865 : Blo 1861632 3357865 := bstep (se 2 (by rfl) ⟨1259199, by rfl⟩ : syracuseStep 3357865 = 2518399) B2518399
theorem B2792699 : Blo 1861632 2792699 := bstep (se 1 (by rfl) ⟨2094524, by rfl⟩ : syracuseStep 2792699 = 4189049) B4189049
theorem B2792939 : Blo 1861632 2792939 := bstep (se 1 (by rfl) ⟨2094704, by rfl⟩ : syracuseStep 2792939 = 4189409) B4189409
theorem B8061119 : Blo 1861632 8061119 := bstep (se 1 (by rfl) ⟨6045839, by rfl⟩ : syracuseStep 8061119 = 12091679) B12091679
theorem B90644831 : Blo 1861632 90644831 := bstep (se 1 (by rfl) ⟨67983623, by rfl⟩ : syracuseStep 90644831 = 135967247) B135967247
theorem B23871995 : Blo 1861632 23871995 := bstep (se 1 (by rfl) ⟨17903996, by rfl⟩ : syracuseStep 23871995 = 35807993) B35807993
theorem B80585279 : Blo 1861632 80585279 := bstep (se 1 (by rfl) ⟨60438959, by rfl⟩ : syracuseStep 80585279 = 120877919) B120877919
theorem B90669739 : Blo 1861632 90669739 := bstep (se 1 (by rfl) ⟨68002304, by rfl⟩ : syracuseStep 90669739 = 136004609) B136004609
theorem B17908613 : Blo 1861632 17908613 := bstep (se 4 (by rfl) ⟨1678932, by rfl⟩ : syracuseStep 17908613 = 3357865) B3357865
theorem B2794409 : Blo 1861632 2794409 := bstep (se 2 (by rfl) ⟨1047903, by rfl⟩ : syracuseStep 2794409 = 2095807) B2095807
theorem B17900459 : Blo 1861632 17900459 := bstep (se 1 (by rfl) ⟨13425344, by rfl⟩ : syracuseStep 17900459 = 26850689) B26850689
theorem B26854379 : Blo 1861632 26854379 := bstep (se 1 (by rfl) ⟨20140784, by rfl⟩ : syracuseStep 26854379 = 40281569) B40281569
theorem B5301551 : Blo 1861632 5301551 := bstep (se 1 (by rfl) ⟨3976163, by rfl⟩ : syracuseStep 5301551 = 7952327) B7952327
theorem B2794823 : Blo 1861632 2794823 := bstep (se 1 (by rfl) ⟨2096117, by rfl⟩ : syracuseStep 2794823 = 4192235) B4192235
theorem B5301607 : Blo 1861632 5301607 := bstep (se 1 (by rfl) ⟨3976205, by rfl⟩ : syracuseStep 5301607 = 7952411) B7952411
theorem B2794985 : Blo 1861632 2794985 := bstep (se 2 (by rfl) ⟨1048119, by rfl⟩ : syracuseStep 2794985 = 2096239) B2096239
theorem B6285113 : Blo 1861632 6285113 := bstep (se 2 (by rfl) ⟨2356917, by rfl⟩ : syracuseStep 6285113 = 4713835) B4713835
theorem B2795423 : Blo 1861632 2795423 := bstep (se 1 (by rfl) ⟨2096567, by rfl⟩ : syracuseStep 2795423 = 4193135) B4193135
theorem B6285383 : Blo 1861632 6285383 := bstep (se 1 (by rfl) ⟨4714037, by rfl⟩ : syracuseStep 6285383 = 9428075) B9428075
theorem B1861799 : Blo 1861632 1861799 := bstep (se 1 (by rfl) ⟨1396349, by rfl⟩ : syracuseStep 1861799 = 2792699) B2792699
theorem B1861959 : Blo 1861632 1861959 := bstep (se 1 (by rfl) ⟨1396469, by rfl⟩ : syracuseStep 1861959 = 2792939) B2792939
theorem B4713167 : Blo 1861632 4713167 := bstep (se 1 (by rfl) ⟨3534875, by rfl⟩ : syracuseStep 4713167 = 7069751) B7069751
theorem B152996627 : Blo 1861632 152996627 := bstep (se 1 (by rfl) ⟨114747470, by rfl⟩ : syracuseStep 152996627 = 229494941) B229494941
theorem B4188959 : Blo 1861632 4188959 := bstep (se 1 (by rfl) ⟨3141719, by rfl⟩ : syracuseStep 4188959 = 6283439) B6283439
theorem B12741599 : Blo 1861632 12741599 := bstep (se 1 (by rfl) ⟨9556199, by rfl⟩ : syracuseStep 12741599 = 19112399) B19112399
theorem B3681335 : Blo 1861632 3681335 := bstep (se 1 (by rfl) ⟨2761001, by rfl⟩ : syracuseStep 3681335 = 5522003) B5522003
theorem B6286463 : Blo 1861632 6286463 := bstep (se 1 (by rfl) ⟨4714847, by rfl⟩ : syracuseStep 6286463 = 9429695) B9429695
theorem B48368785 : Blo 1861632 48368785 := bstep (se 2 (by rfl) ⟨18138294, by rfl⟩ : syracuseStep 48368785 = 36276589) B36276589
theorem B1862811 : Blo 1861632 1862811 := bstep (se 1 (by rfl) ⟨1397108, by rfl⟩ : syracuseStep 1862811 = 2794217) B2794217
theorem B2985115 : Blo 1861632 2985115 := bstep (se 1 (by rfl) ⟨2238836, by rfl⟩ : syracuseStep 2985115 = 4477673) B4477673
theorem B1862823 : Blo 1861632 1862823 := bstep (se 1 (by rfl) ⟨1397117, by rfl⟩ : syracuseStep 1862823 = 2794235) B2794235
theorem B6286571 : Blo 1861632 6286571 := bstep (se 1 (by rfl) ⟨4714928, by rfl⟩ : syracuseStep 6286571 = 9429857) B9429857
theorem B11332943 : Blo 1861632 11332943 := bstep (se 1 (by rfl) ⟨8499707, by rfl⟩ : syracuseStep 11332943 = 16999415) B16999415
theorem B1863167 : Blo 1861632 1863167 := bstep (se 1 (by rfl) ⟨1397375, by rfl⟩ : syracuseStep 1863167 = 2794751) B2794751
theorem B1046097929 : Blo 1861632 1046097929 := bstep (se 2 (by rfl) ⟨392286723, by rfl⟩ : syracuseStep 1046097929 = 784573447) B784573447
theorem B3141679 : Blo 1861632 3141679 := bstep (se 1 (by rfl) ⟨2356259, by rfl⟩ : syracuseStep 3141679 = 4712519) B4712519
theorem B6287543 : Blo 1861632 6287543 := bstep (se 1 (by rfl) ⟨4715657, by rfl⟩ : syracuseStep 6287543 = 9431315) B9431315
theorem B4190399 : Blo 1861632 4190399 := bstep (se 1 (by rfl) ⟨3142799, by rfl⟩ : syracuseStep 4190399 = 6285599) B6285599
theorem B3535073 : Blo 1861632 3535073 := bstep (se 2 (by rfl) ⟨1325652, by rfl⟩ : syracuseStep 3535073 = 2651305) B2651305
theorem B6369607 : Blo 1861632 6369607 := bstep (se 1 (by rfl) ⟨4777205, by rfl⟩ : syracuseStep 6369607 = 9554411) B9554411
theorem B15110651 : Blo 1861632 15110651 := bstep (se 1 (by rfl) ⟨11332988, by rfl⟩ : syracuseStep 15110651 = 22665977) B22665977
theorem B3142199 : Blo 1861632 3142199 := bstep (se 1 (by rfl) ⟨2356649, by rfl⟩ : syracuseStep 3142199 = 4713299) B4713299
theorem B10064513 : Blo 1861632 10064513 := bstep (se 2 (by rfl) ⟨3774192, by rfl⟩ : syracuseStep 10064513 = 7548385) B7548385
theorem B7074641 : Blo 1861632 7074641 := bstep (se 2 (by rfl) ⟨2652990, by rfl⟩ : syracuseStep 7074641 = 5305981) B5305981
theorem B3142759 : Blo 1861632 3142759 := bstep (se 1 (by rfl) ⟨2357069, by rfl⟩ : syracuseStep 3142759 = 4714139) B4714139
theorem B4191335 : Blo 1861632 4191335 := bstep (se 1 (by rfl) ⟨3143501, by rfl⟩ : syracuseStep 4191335 = 6287003) B6287003
theorem B28669139 : Blo 1861632 28669139 := bstep (se 1 (by rfl) ⟨21501854, by rfl⟩ : syracuseStep 28669139 = 43003709) B43003709
theorem B7075295 : Blo 1861632 7075295 := bstep (se 1 (by rfl) ⟨5306471, by rfl⟩ : syracuseStep 7075295 = 10612943) B10612943
theorem B57357881 : Blo 1861632 57357881 := bstep (se 2 (by rfl) ⟨21509205, by rfl⟩ : syracuseStep 57357881 = 43018411) B43018411
theorem B4192019 : Blo 1861632 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B9426941 : Blo 1861632 9426941 := bstep (se 3 (by rfl) ⟨1767551, by rfl⟩ : syracuseStep 9426941 = 3535103) B3535103
theorem B2095195 : Blo 1861632 2095195 := bstep (se 1 (by rfl) ⟨1571396, by rfl⟩ : syracuseStep 2095195 = 3142793) B3142793
theorem B6371455 : Blo 1861632 6371455 := bstep (se 1 (by rfl) ⟨4778591, by rfl⟩ : syracuseStep 6371455 = 9557183) B9557183
theorem B6995159 : Blo 1861632 6995159 := bstep (se 1 (by rfl) ⟨5246369, by rfl⟩ : syracuseStep 6995159 = 10492739) B10492739
theorem B2792759 : Blo 1861632 2792759 := bstep (se 1 (by rfl) ⟨2094569, by rfl⟩ : syracuseStep 2792759 = 4189139) B4189139
theorem B10608043 : Blo 1861632 10608043 := bstep (se 1 (by rfl) ⟨7956032, by rfl⟩ : syracuseStep 10608043 = 15912065) B15912065
theorem B2793119 : Blo 1861632 2793119 := bstep (se 1 (by rfl) ⟨2094839, by rfl⟩ : syracuseStep 2793119 = 4189679) B4189679
theorem B2793593 : Blo 1861632 2793593 := bstep (se 2 (by rfl) ⟨1047597, by rfl⟩ : syracuseStep 2793593 = 2095195) B2095195
theorem B5374079 : Blo 1861632 5374079 := bstep (se 1 (by rfl) ⟨4030559, by rfl⟩ : syracuseStep 5374079 = 8061119) B8061119
theorem B2793599 : Blo 1861632 2793599 := bstep (se 1 (by rfl) ⟨2095199, by rfl⟩ : syracuseStep 2793599 = 4190399) B4190399
theorem B8495273 : Blo 1861632 8495273 := bstep (se 2 (by rfl) ⟨3185727, by rfl⟩ : syracuseStep 8495273 = 6371455) B6371455
theorem B53723519 : Blo 1861632 53723519 := bstep (se 1 (by rfl) ⟨40292639, by rfl⟩ : syracuseStep 53723519 = 80585279) B80585279
theorem B6709675 : Blo 1861632 6709675 := bstep (se 1 (by rfl) ⟨5032256, by rfl⟩ : syracuseStep 6709675 = 10064513) B10064513
theorem B2794223 : Blo 1861632 2794223 := bstep (se 1 (by rfl) ⟨2095667, by rfl⟩ : syracuseStep 2794223 = 4191335) B4191335
theorem B19112759 : Blo 1861632 19112759 := bstep (se 1 (by rfl) ⟨14334569, by rfl⟩ : syracuseStep 19112759 = 28669139) B28669139
theorem B2794679 : Blo 1861632 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B6284627 : Blo 1861632 6284627 := bstep (se 1 (by rfl) ⟨4713470, by rfl⟩ : syracuseStep 6284627 = 9426941) B9426941
theorem B4663439 : Blo 1861632 4663439 := bstep (se 1 (by rfl) ⟨3497579, by rfl⟩ : syracuseStep 4663439 = 6995159) B6995159
theorem B1861839 : Blo 1861632 1861839 := bstep (se 1 (by rfl) ⟨1396379, by rfl⟩ : syracuseStep 1861839 = 2792759) B2792759
theorem B7555295 : Blo 1861632 7555295 := bstep (se 1 (by rfl) ⟨5666471, by rfl⟩ : syracuseStep 7555295 = 11332943) B11332943
theorem B1862079 : Blo 1861632 1862079 := bstep (se 1 (by rfl) ⟨1396559, by rfl⟩ : syracuseStep 1862079 = 2793119) B2793119
theorem B4188905 : Blo 1861632 4188905 := bstep (se 2 (by rfl) ⟨1570839, by rfl⟩ : syracuseStep 4188905 = 3141679) B3141679
theorem B11939075 : Blo 1861632 11939075 := bstep (se 1 (by rfl) ⟨8954306, by rfl⟩ : syracuseStep 11939075 = 17908613) B17908613
theorem B1862939 : Blo 1861632 1862939 := bstep (se 1 (by rfl) ⟨1397204, by rfl⟩ : syracuseStep 1862939 = 2794409) B2794409
theorem B17902919 : Blo 1861632 17902919 := bstep (se 1 (by rfl) ⟨13427189, by rfl⟩ : syracuseStep 17902919 = 26854379) B26854379
theorem B3534367 : Blo 1861632 3534367 := bstep (se 1 (by rfl) ⟨2650775, by rfl⟩ : syracuseStep 3534367 = 5301551) B5301551
theorem B1863215 : Blo 1861632 1863215 := bstep (se 1 (by rfl) ⟨1397411, by rfl⟩ : syracuseStep 1863215 = 2794823) B2794823
theorem B120892985 : Blo 1861632 120892985 := bstep (se 2 (by rfl) ⟨45334869, by rfl⟩ : syracuseStep 120892985 = 90669739) B90669739
theorem B1863323 : Blo 1861632 1863323 := bstep (se 1 (by rfl) ⟨1397492, by rfl⟩ : syracuseStep 1863323 = 2794985) B2794985
theorem B4190075 : Blo 1861632 4190075 := bstep (se 1 (by rfl) ⟨3142556, by rfl⟩ : syracuseStep 4190075 = 6285113) B6285113
theorem B1863615 : Blo 1861632 1863615 := bstep (se 1 (by rfl) ⟨1397711, by rfl⟩ : syracuseStep 1863615 = 2795423) B2795423
theorem B4190255 : Blo 1861632 4190255 := bstep (se 1 (by rfl) ⟨3142691, by rfl⟩ : syracuseStep 4190255 = 6285383) B6285383
theorem B4190345 : Blo 1861632 4190345 := bstep (se 2 (by rfl) ⟨1571379, by rfl⟩ : syracuseStep 4190345 = 3142759) B3142759
theorem B64491713 : Blo 1861632 64491713 := bstep (se 2 (by rfl) ⟨24184392, by rfl⟩ : syracuseStep 64491713 = 48368785) B48368785
theorem B3142111 : Blo 1861632 3142111 := bstep (se 1 (by rfl) ⟨2356583, by rfl⟩ : syracuseStep 3142111 = 4713167) B4713167
theorem B14144057 : Blo 1861632 14144057 := bstep (se 2 (by rfl) ⟨5304021, by rfl⟩ : syracuseStep 14144057 = 10608043) B10608043
theorem B2454223 : Blo 1861632 2454223 := bstep (se 1 (by rfl) ⟨1840667, by rfl⟩ : syracuseStep 2454223 = 3681335) B3681335
theorem B4190975 : Blo 1861632 4190975 := bstep (se 1 (by rfl) ⟨3143231, by rfl⟩ : syracuseStep 4190975 = 6286463) B6286463
theorem B4191047 : Blo 1861632 4191047 := bstep (se 1 (by rfl) ⟨3143285, by rfl⟩ : syracuseStep 4191047 = 6286571) B6286571
theorem B2789594477 : Blo 1861632 2789594477 := bstep (se 3 (by rfl) ⟨523048964, by rfl⟩ : syracuseStep 2789594477 = 1046097929) B1046097929
theorem B4191695 : Blo 1861632 4191695 := bstep (se 1 (by rfl) ⟨3143771, by rfl⟩ : syracuseStep 4191695 = 6287543) B6287543
theorem B2356715 : Blo 1861632 2356715 := bstep (se 1 (by rfl) ⟨1767536, by rfl⟩ : syracuseStep 2356715 = 3535073) B3535073
theorem B60429887 : Blo 1861632 60429887 := bstep (se 1 (by rfl) ⟨45322415, by rfl⟩ : syracuseStep 60429887 = 90644831) B90644831
theorem B15914663 : Blo 1861632 15914663 := bstep (se 1 (by rfl) ⟨11935997, by rfl⟩ : syracuseStep 15914663 = 23871995) B23871995
theorem B10073767 : Blo 1861632 10073767 := bstep (se 1 (by rfl) ⟨7555325, by rfl⟩ : syracuseStep 10073767 = 15110651) B15110651
theorem B2094799 : Blo 1861632 2094799 := bstep (se 1 (by rfl) ⟨1571099, by rfl⟩ : syracuseStep 2094799 = 3142199) B3142199
theorem B8492809 : Blo 1861632 8492809 := bstep (se 2 (by rfl) ⟨3184803, by rfl⟩ : syracuseStep 8492809 = 6369607) B6369607
theorem B4716427 : Blo 1861632 4716427 := bstep (se 1 (by rfl) ⟨3537320, by rfl⟩ : syracuseStep 4716427 = 7074641) B7074641
theorem B11933639 : Blo 1861632 11933639 := bstep (se 1 (by rfl) ⟨8950229, by rfl⟩ : syracuseStep 11933639 = 17900459) B17900459
theorem B4716863 : Blo 1861632 4716863 := bstep (se 1 (by rfl) ⟨3537647, by rfl⟩ : syracuseStep 4716863 = 7075295) B7075295
theorem B38238587 : Blo 1861632 38238587 := bstep (se 1 (by rfl) ⟨28678940, by rfl⟩ : syracuseStep 38238587 = 57357881) B57357881
theorem B3980153 : Blo 1861632 3980153 := bstep (se 2 (by rfl) ⟨1492557, by rfl⟩ : syracuseStep 3980153 = 2985115) B2985115
theorem B7068809 : Blo 1861632 7068809 := bstep (se 2 (by rfl) ⟨2650803, by rfl⟩ : syracuseStep 7068809 = 5301607) B5301607
theorem B101997751 : Blo 1861632 101997751 := bstep (se 1 (by rfl) ⟨76498313, by rfl⟩ : syracuseStep 101997751 = 152996627) B152996627
theorem B2792639 : Blo 1861632 2792639 := bstep (se 1 (by rfl) ⟨2094479, by rfl⟩ : syracuseStep 2792639 = 4188959) B4188959
theorem B8494399 : Blo 1861632 8494399 := bstep (se 1 (by rfl) ⟨6370799, by rfl⟩ : syracuseStep 8494399 = 12741599) B12741599
theorem B2793503 : Blo 1861632 2793503 := bstep (se 1 (by rfl) ⟨2095127, by rfl⟩ : syracuseStep 2793503 = 4190255) B4190255
theorem B2793563 : Blo 1861632 2793563 := bstep (se 1 (by rfl) ⟨2095172, by rfl⟩ : syracuseStep 2793563 = 4190345) B4190345
theorem B35815679 : Blo 1861632 35815679 := bstep (se 1 (by rfl) ⟨26861759, by rfl⟩ : syracuseStep 35815679 = 53723519) B53723519
theorem B9429371 : Blo 1861632 9429371 := bstep (se 1 (by rfl) ⟨7072028, by rfl⟩ : syracuseStep 9429371 = 14144057) B14144057
theorem B2793983 : Blo 1861632 2793983 := bstep (se 1 (by rfl) ⟨2095487, by rfl⟩ : syracuseStep 2793983 = 4190975) B4190975
theorem B2794031 : Blo 1861632 2794031 := bstep (se 1 (by rfl) ⟨2095523, by rfl⟩ : syracuseStep 2794031 = 4191047) B4191047
theorem B8946233 : Blo 1861632 8946233 := bstep (se 2 (by rfl) ⟨3354837, by rfl⟩ : syracuseStep 8946233 = 6709675) B6709675
theorem B2794463 : Blo 1861632 2794463 := bstep (se 1 (by rfl) ⟨2095847, by rfl⟩ : syracuseStep 2794463 = 4191695) B4191695
theorem B10609775 : Blo 1861632 10609775 := bstep (se 1 (by rfl) ⟨7957331, by rfl⟩ : syracuseStep 10609775 = 15914663) B15914663
theorem B6284573 : Blo 1861632 6284573 := bstep (se 3 (by rfl) ⟨1178357, by rfl⟩ : syracuseStep 6284573 = 2356715) B2356715
theorem B7955759 : Blo 1861632 7955759 := bstep (se 1 (by rfl) ⟨5966819, by rfl⟩ : syracuseStep 7955759 = 11933639) B11933639
theorem B135997001 : Blo 1861632 135997001 := bstep (se 2 (by rfl) ⟨50998875, by rfl⟩ : syracuseStep 135997001 = 101997751) B101997751
theorem B4712489 : Blo 1861632 4712489 := bstep (se 2 (by rfl) ⟨1767183, by rfl⟩ : syracuseStep 4712489 = 3534367) B3534367
theorem B4712539 : Blo 1861632 4712539 := bstep (se 1 (by rfl) ⟨3534404, by rfl⟩ : syracuseStep 4712539 = 7068809) B7068809
theorem B1861759 : Blo 1861632 1861759 := bstep (se 1 (by rfl) ⟨1396319, by rfl⟩ : syracuseStep 1861759 = 2792639) B2792639
theorem B11323745 : Blo 1861632 11323745 := bstep (se 2 (by rfl) ⟨4246404, by rfl⟩ : syracuseStep 11323745 = 8492809) B8492809
theorem B80595323 : Blo 1861632 80595323 := bstep (se 1 (by rfl) ⟨60446492, by rfl⟩ : syracuseStep 80595323 = 120892985) B120892985
theorem B1862395 : Blo 1861632 1862395 := bstep (se 1 (by rfl) ⟨1396796, by rfl⟩ : syracuseStep 1862395 = 2793593) B2793593
theorem B3582719 : Blo 1861632 3582719 := bstep (se 1 (by rfl) ⟨2687039, by rfl⟩ : syracuseStep 3582719 = 5374079) B5374079
theorem B1862399 : Blo 1861632 1862399 := bstep (se 1 (by rfl) ⟨1396799, by rfl⟩ : syracuseStep 1862399 = 2793599) B2793599
theorem B5663515 : Blo 1861632 5663515 := bstep (se 1 (by rfl) ⟨4247636, by rfl⟩ : syracuseStep 5663515 = 8495273) B8495273
theorem B42994475 : Blo 1861632 42994475 := bstep (se 1 (by rfl) ⟨32245856, by rfl⟩ : syracuseStep 42994475 = 64491713) B64491713
theorem B1862815 : Blo 1861632 1862815 := bstep (se 1 (by rfl) ⟨1397111, by rfl⟩ : syracuseStep 1862815 = 2794223) B2794223
theorem B12741839 : Blo 1861632 12741839 := bstep (se 1 (by rfl) ⟨9556379, by rfl⟩ : syracuseStep 12741839 = 19112759) B19112759
theorem B4189481 : Blo 1861632 4189481 := bstep (se 2 (by rfl) ⟨1571055, by rfl⟩ : syracuseStep 4189481 = 3142111) B3142111
theorem B1863119 : Blo 1861632 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B4189751 : Blo 1861632 4189751 := bstep (se 1 (by rfl) ⟨3142313, by rfl⟩ : syracuseStep 4189751 = 6284627) B6284627
theorem B3272297 : Blo 1861632 3272297 := bstep (se 2 (by rfl) ⟨1227111, by rfl⟩ : syracuseStep 3272297 = 2454223) B2454223
theorem B3108959 : Blo 1861632 3108959 := bstep (se 1 (by rfl) ⟨2331719, by rfl⟩ : syracuseStep 3108959 = 4663439) B4663439
theorem B11325865 : Blo 1861632 11325865 := bstep (se 2 (by rfl) ⟨4247199, by rfl⟩ : syracuseStep 11325865 = 8494399) B8494399
theorem B7959383 : Blo 1861632 7959383 := bstep (se 1 (by rfl) ⟨5969537, by rfl⟩ : syracuseStep 7959383 = 11939075) B11939075
theorem B13431689 : Blo 1861632 13431689 := bstep (se 2 (by rfl) ⟨5036883, by rfl⟩ : syracuseStep 13431689 = 10073767) B10073767
theorem B6288569 : Blo 1861632 6288569 := bstep (se 2 (by rfl) ⟨2358213, by rfl⟩ : syracuseStep 6288569 = 4716427) B4716427
theorem B1859729651 : Blo 1861632 1859729651 := bstep (se 1 (by rfl) ⟨1394797238, by rfl⟩ : syracuseStep 1859729651 = 2789594477) B2789594477
theorem B40286591 : Blo 1861632 40286591 := bstep (se 1 (by rfl) ⟨30214943, by rfl⟩ : syracuseStep 40286591 = 60429887) B60429887
theorem B5036863 : Blo 1861632 5036863 := bstep (se 1 (by rfl) ⟨3777647, by rfl⟩ : syracuseStep 5036863 = 7555295) B7555295
theorem B3144575 : Blo 1861632 3144575 := bstep (se 1 (by rfl) ⟨2358431, by rfl⟩ : syracuseStep 3144575 = 4716863) B4716863
theorem B25492391 : Blo 1861632 25492391 := bstep (se 1 (by rfl) ⟨19119293, by rfl⟩ : syracuseStep 25492391 = 38238587) B38238587
theorem B2792603 : Blo 1861632 2792603 := bstep (se 1 (by rfl) ⟨2094452, by rfl⟩ : syracuseStep 2792603 = 4188905) B4188905
theorem B2653435 : Blo 1861632 2653435 := bstep (se 1 (by rfl) ⟨1990076, by rfl⟩ : syracuseStep 2653435 = 3980153) B3980153
theorem B11935279 : Blo 1861632 11935279 := bstep (se 1 (by rfl) ⟨8951459, by rfl⟩ : syracuseStep 11935279 = 17902919) B17902919
theorem B2793065 : Blo 1861632 2793065 := bstep (se 2 (by rfl) ⟨1047399, by rfl⟩ : syracuseStep 2793065 = 2094799) B2094799
theorem B2793383 : Blo 1861632 2793383 := bstep (se 1 (by rfl) ⟨2095037, by rfl⟩ : syracuseStep 2793383 = 4190075) B4190075
theorem B2072639 : Blo 1861632 2072639 := bstep (se 1 (by rfl) ⟨1554479, by rfl⟩ : syracuseStep 2072639 = 3108959) B3108959
theorem B6283385 : Blo 1861632 6283385 := bstep (se 2 (by rfl) ⟨2356269, by rfl⟩ : syracuseStep 6283385 = 4712539) B4712539
theorem B5964155 : Blo 1861632 5964155 := bstep (se 1 (by rfl) ⟨4473116, by rfl⟩ : syracuseStep 5964155 = 8946233) B8946233
theorem B8954459 : Blo 1861632 8954459 := bstep (se 1 (by rfl) ⟨6715844, by rfl⟩ : syracuseStep 8954459 = 13431689) B13431689
theorem B1239819767 : Blo 1861632 1239819767 := bstep (se 1 (by rfl) ⟨929864825, by rfl⟩ : syracuseStep 1239819767 = 1859729651) B1859729651
theorem B8726125 : Blo 1861632 8726125 := bstep (se 3 (by rfl) ⟨1636148, by rfl⟩ : syracuseStep 8726125 = 3272297) B3272297
theorem B1861735 : Blo 1861632 1861735 := bstep (se 1 (by rfl) ⟨1396301, by rfl⟩ : syracuseStep 1861735 = 2792603) B2792603
theorem B1862043 : Blo 1861632 1862043 := bstep (se 1 (by rfl) ⟨1396532, by rfl⟩ : syracuseStep 1862043 = 2793065) B2793065
theorem B1862255 : Blo 1861632 1862255 := bstep (se 1 (by rfl) ⟨1396691, by rfl⟩ : syracuseStep 1862255 = 2793383) B2793383
theorem B1862335 : Blo 1861632 1862335 := bstep (se 1 (by rfl) ⟨1396751, by rfl⟩ : syracuseStep 1862335 = 2793503) B2793503
theorem B1862375 : Blo 1861632 1862375 := bstep (se 1 (by rfl) ⟨1396781, by rfl⟩ : syracuseStep 1862375 = 2793563) B2793563
theorem B6286247 : Blo 1861632 6286247 := bstep (se 1 (by rfl) ⟨4714685, by rfl⟩ : syracuseStep 6286247 = 9429371) B9429371
theorem B1862655 : Blo 1861632 1862655 := bstep (se 1 (by rfl) ⟨1396991, by rfl⟩ : syracuseStep 1862655 = 2793983) B2793983
theorem B1862687 : Blo 1861632 1862687 := bstep (se 1 (by rfl) ⟨1397015, by rfl⟩ : syracuseStep 1862687 = 2794031) B2794031
theorem B15101153 : Blo 1861632 15101153 := bstep (se 2 (by rfl) ⟨5662932, by rfl⟩ : syracuseStep 15101153 = 11325865) B11325865
theorem B1862975 : Blo 1861632 1862975 := bstep (se 1 (by rfl) ⟨1397231, by rfl⟩ : syracuseStep 1862975 = 2794463) B2794463
theorem B7073183 : Blo 1861632 7073183 := bstep (se 1 (by rfl) ⟨5304887, by rfl⟩ : syracuseStep 7073183 = 10609775) B10609775
theorem B4189715 : Blo 1861632 4189715 := bstep (se 1 (by rfl) ⟨3142286, by rfl⟩ : syracuseStep 4189715 = 6284573) B6284573
theorem B90664667 : Blo 1861632 90664667 := bstep (se 1 (by rfl) ⟨67998500, by rfl⟩ : syracuseStep 90664667 = 135997001) B135997001
theorem B3141659 : Blo 1861632 3141659 := bstep (se 1 (by rfl) ⟨2356244, by rfl⟩ : syracuseStep 3141659 = 4712489) B4712489
theorem B7549163 : Blo 1861632 7549163 := bstep (se 1 (by rfl) ⟨5661872, by rfl⟩ : syracuseStep 7549163 = 11323745) B11323745
theorem B26857727 : Blo 1861632 26857727 := bstep (se 1 (by rfl) ⟨20143295, by rfl⟩ : syracuseStep 26857727 = 40286591) B40286591
theorem B2388479 : Blo 1861632 2388479 := bstep (se 1 (by rfl) ⟨1791359, by rfl⟩ : syracuseStep 2388479 = 3582719) B3582719
theorem B16994927 : Blo 1861632 16994927 := bstep (se 1 (by rfl) ⟨12746195, by rfl⟩ : syracuseStep 16994927 = 25492391) B25492391
theorem B15913705 : Blo 1861632 15913705 := bstep (se 2 (by rfl) ⟨5967639, by rfl⟩ : syracuseStep 15913705 = 11935279) B11935279
theorem B23877119 : Blo 1861632 23877119 := bstep (se 1 (by rfl) ⟨17907839, by rfl⟩ : syracuseStep 23877119 = 35815679) B35815679
theorem B5306255 : Blo 1861632 5306255 := bstep (se 1 (by rfl) ⟨3979691, by rfl⟩ : syracuseStep 5306255 = 7959383) B7959383
theorem B4192379 : Blo 1861632 4192379 := bstep (se 1 (by rfl) ⟨3144284, by rfl⟩ : syracuseStep 4192379 = 6288569) B6288569
theorem B21215357 : Blo 1861632 21215357 := bstep (se 3 (by rfl) ⟨3977879, by rfl⟩ : syracuseStep 21215357 = 7955759) B7955759
theorem B7551353 : Blo 1861632 7551353 := bstep (se 2 (by rfl) ⟨2831757, by rfl⟩ : syracuseStep 7551353 = 5663515) B5663515
theorem B6715817 : Blo 1861632 6715817 := bstep (se 2 (by rfl) ⟨2518431, by rfl⟩ : syracuseStep 6715817 = 5036863) B5036863
theorem B53730215 : Blo 1861632 53730215 := bstep (se 1 (by rfl) ⟨40297661, by rfl⟩ : syracuseStep 53730215 = 80595323) B80595323
theorem B3537913 : Blo 1861632 3537913 := bstep (se 2 (by rfl) ⟨1326717, by rfl⟩ : syracuseStep 3537913 = 2653435) B2653435
theorem B28662983 : Blo 1861632 28662983 := bstep (se 1 (by rfl) ⟨21497237, by rfl⟩ : syracuseStep 28662983 = 42994475) B42994475
theorem B2096383 : Blo 1861632 2096383 := bstep (se 1 (by rfl) ⟨1572287, by rfl⟩ : syracuseStep 2096383 = 3144575) B3144575
theorem B8494559 : Blo 1861632 8494559 := bstep (se 1 (by rfl) ⟨6370919, by rfl⟩ : syracuseStep 8494559 = 12741839) B12741839
theorem B2792987 : Blo 1861632 2792987 := bstep (se 1 (by rfl) ⟨2094740, by rfl⟩ : syracuseStep 2792987 = 4189481) B4189481
theorem B2793167 : Blo 1861632 2793167 := bstep (se 1 (by rfl) ⟨2094875, by rfl⟩ : syracuseStep 2793167 = 4189751) B4189751
theorem B11329951 : Blo 1861632 11329951 := bstep (se 1 (by rfl) ⟨8497463, by rfl⟩ : syracuseStep 11329951 = 16994927) B16994927
theorem B21218273 : Blo 1861632 21218273 := bstep (se 2 (by rfl) ⟨7956852, by rfl⟩ : syracuseStep 21218273 = 15913705) B15913705
theorem B15918079 : Blo 1861632 15918079 := bstep (se 1 (by rfl) ⟨11938559, by rfl⟩ : syracuseStep 15918079 = 23877119) B23877119
theorem B2794919 : Blo 1861632 2794919 := bstep (se 1 (by rfl) ⟨2096189, by rfl⟩ : syracuseStep 2794919 = 4192379) B4192379
theorem B2795177 : Blo 1861632 2795177 := bstep (se 2 (by rfl) ⟨1048191, by rfl⟩ : syracuseStep 2795177 = 2096383) B2096383
theorem B11634833 : Blo 1861632 11634833 := bstep (se 2 (by rfl) ⟨4363062, by rfl⟩ : syracuseStep 11634833 = 8726125) B8726125
theorem B5663039 : Blo 1861632 5663039 := bstep (se 1 (by rfl) ⟨4247279, by rfl⟩ : syracuseStep 5663039 = 8494559) B8494559
theorem B1861991 : Blo 1861632 1861991 := bstep (se 1 (by rfl) ⟨1396493, by rfl⟩ : syracuseStep 1861991 = 2792987) B2792987
theorem B1862111 : Blo 1861632 1862111 := bstep (se 1 (by rfl) ⟨1396583, by rfl⟩ : syracuseStep 1862111 = 2793167) B2793167
theorem B60443111 : Blo 1861632 60443111 := bstep (se 1 (by rfl) ⟨45332333, by rfl⟩ : syracuseStep 60443111 = 90664667) B90664667
theorem B4188923 : Blo 1861632 4188923 := bstep (se 1 (by rfl) ⟨3141692, by rfl⟩ : syracuseStep 4188923 = 6283385) B6283385
theorem B5032775 : Blo 1861632 5032775 := bstep (se 1 (by rfl) ⟨3774581, by rfl⟩ : syracuseStep 5032775 = 7549163) B7549163
theorem B3976103 : Blo 1861632 3976103 := bstep (se 1 (by rfl) ⟨2982077, by rfl⟩ : syracuseStep 3976103 = 5964155) B5964155
theorem B6369277 : Blo 1861632 6369277 := bstep (se 3 (by rfl) ⟨1194239, by rfl⟩ : syracuseStep 6369277 = 2388479) B2388479
theorem B14143571 : Blo 1861632 14143571 := bstep (se 1 (by rfl) ⟨10607678, by rfl⟩ : syracuseStep 14143571 = 21215357) B21215357
theorem B5034235 : Blo 1861632 5034235 := bstep (se 1 (by rfl) ⟨3775676, by rfl⟩ : syracuseStep 5034235 = 7551353) B7551353
theorem B4477211 : Blo 1861632 4477211 := bstep (se 1 (by rfl) ⟨3357908, by rfl⟩ : syracuseStep 4477211 = 6715817) B6715817
theorem B4190831 : Blo 1861632 4190831 := bstep (se 1 (by rfl) ⟨3143123, by rfl⟩ : syracuseStep 4190831 = 6286247) B6286247
theorem B35820143 : Blo 1861632 35820143 := bstep (se 1 (by rfl) ⟨26865107, by rfl⟩ : syracuseStep 35820143 = 53730215) B53730215
theorem B19108655 : Blo 1861632 19108655 := bstep (se 1 (by rfl) ⟨14331491, by rfl⟩ : syracuseStep 19108655 = 28662983) B28662983
theorem B4715455 : Blo 1861632 4715455 := bstep (se 1 (by rfl) ⟨3536591, by rfl⟩ : syracuseStep 4715455 = 7073183) B7073183
theorem B2094439 : Blo 1861632 2094439 := bstep (se 1 (by rfl) ⟨1570829, by rfl⟩ : syracuseStep 2094439 = 3141659) B3141659
theorem B5527037 : Blo 1861632 5527037 := bstep (se 3 (by rfl) ⟨1036319, by rfl⟩ : syracuseStep 5527037 = 2072639) B2072639
theorem B17905151 : Blo 1861632 17905151 := bstep (se 1 (by rfl) ⟨13428863, by rfl⟩ : syracuseStep 17905151 = 26857727) B26857727
theorem B5969639 : Blo 1861632 5969639 := bstep (se 1 (by rfl) ⟨4477229, by rfl⟩ : syracuseStep 5969639 = 8954459) B8954459
theorem B826546511 : Blo 1861632 826546511 := bstep (se 1 (by rfl) ⟨619909883, by rfl⟩ : syracuseStep 826546511 = 1239819767) B1239819767
theorem B3537503 : Blo 1861632 3537503 := bstep (se 1 (by rfl) ⟨2653127, by rfl⟩ : syracuseStep 3537503 = 5306255) B5306255
theorem B4717217 : Blo 1861632 4717217 := bstep (se 2 (by rfl) ⟨1768956, by rfl⟩ : syracuseStep 4717217 = 3537913) B3537913
theorem B10067435 : Blo 1861632 10067435 := bstep (se 1 (by rfl) ⟨7550576, by rfl⟩ : syracuseStep 10067435 = 15101153) B15101153
theorem B2793143 : Blo 1861632 2793143 := bstep (se 1 (by rfl) ⟨2094857, by rfl⟩ : syracuseStep 2793143 = 4189715) B4189715
theorem B9429047 : Blo 1861632 9429047 := bstep (se 1 (by rfl) ⟨7071785, by rfl⟩ : syracuseStep 9429047 = 14143571) B14143571
theorem B2793887 : Blo 1861632 2793887 := bstep (se 1 (by rfl) ⟨2095415, by rfl⟩ : syracuseStep 2793887 = 4190831) B4190831
theorem B23880095 : Blo 1861632 23880095 := bstep (se 1 (by rfl) ⟨17910071, by rfl⟩ : syracuseStep 23880095 = 35820143) B35820143
theorem B12739103 : Blo 1861632 12739103 := bstep (se 1 (by rfl) ⟨9554327, by rfl⟩ : syracuseStep 12739103 = 19108655) B19108655
theorem B15106601 : Blo 1861632 15106601 := bstep (se 2 (by rfl) ⟨5664975, by rfl⟩ : syracuseStep 15106601 = 11329951) B11329951
theorem B11936767 : Blo 1861632 11936767 := bstep (se 1 (by rfl) ⟨8952575, by rfl⟩ : syracuseStep 11936767 = 17905151) B17905151
theorem B15919037 : Blo 1861632 15919037 := bstep (se 3 (by rfl) ⟨2984819, by rfl⟩ : syracuseStep 15919037 = 5969639) B5969639
theorem B6711623 : Blo 1861632 6711623 := bstep (se 1 (by rfl) ⟨5033717, by rfl⟩ : syracuseStep 6711623 = 10067435) B10067435
theorem B1862095 : Blo 1861632 1862095 := bstep (se 1 (by rfl) ⟨1396571, by rfl⟩ : syracuseStep 1862095 = 2793143) B2793143
theorem B2984807 : Blo 1861632 2984807 := bstep (se 1 (by rfl) ⟨2238605, by rfl⟩ : syracuseStep 2984807 = 4477211) B4477211
theorem B6712313 : Blo 1861632 6712313 := bstep (se 2 (by rfl) ⟨2517117, by rfl⟩ : syracuseStep 6712313 = 5034235) B5034235
theorem B15101437 : Blo 1861632 15101437 := bstep (se 3 (by rfl) ⟨2831519, by rfl⟩ : syracuseStep 15101437 = 5663039) B5663039
theorem B1863279 : Blo 1861632 1863279 := bstep (se 1 (by rfl) ⟨1397459, by rfl⟩ : syracuseStep 1863279 = 2794919) B2794919
theorem B1863451 : Blo 1861632 1863451 := bstep (se 1 (by rfl) ⟨1397588, by rfl⟩ : syracuseStep 1863451 = 2795177) B2795177
theorem B6287273 : Blo 1861632 6287273 := bstep (se 2 (by rfl) ⟨2357727, by rfl⟩ : syracuseStep 6287273 = 4715455) B4715455
theorem B551031007 : Blo 1861632 551031007 := bstep (se 1 (by rfl) ⟨413273255, by rfl⟩ : syracuseStep 551031007 = 826546511) B826546511
theorem B3355183 : Blo 1861632 3355183 := bstep (se 1 (by rfl) ⟨2516387, by rfl⟩ : syracuseStep 3355183 = 5032775) B5032775
theorem B2650735 : Blo 1861632 2650735 := bstep (se 1 (by rfl) ⟨1988051, by rfl⟩ : syracuseStep 2650735 = 3976103) B3976103
theorem B8492369 : Blo 1861632 8492369 := bstep (se 2 (by rfl) ⟨3184638, by rfl⟩ : syracuseStep 8492369 = 6369277) B6369277
theorem B14145515 : Blo 1861632 14145515 := bstep (se 1 (by rfl) ⟨10609136, by rfl⟩ : syracuseStep 14145515 = 21218273) B21218273
theorem B3684691 : Blo 1861632 3684691 := bstep (se 1 (by rfl) ⟨2763518, by rfl⟩ : syracuseStep 3684691 = 5527037) B5527037
theorem B21224105 : Blo 1861632 21224105 := bstep (se 2 (by rfl) ⟨7959039, by rfl⟩ : syracuseStep 21224105 = 15918079) B15918079
theorem B7756555 : Blo 1861632 7756555 := bstep (se 1 (by rfl) ⟨5817416, by rfl⟩ : syracuseStep 7756555 = 11634833) B11634833
theorem B40295407 : Blo 1861632 40295407 := bstep (se 1 (by rfl) ⟨30221555, by rfl⟩ : syracuseStep 40295407 = 60443111) B60443111
theorem B2358335 : Blo 1861632 2358335 := bstep (se 1 (by rfl) ⟨1768751, by rfl⟩ : syracuseStep 2358335 = 3537503) B3537503
theorem B3144811 : Blo 1861632 3144811 := bstep (se 1 (by rfl) ⟨2358608, by rfl⟩ : syracuseStep 3144811 = 4717217) B4717217
theorem B2792585 : Blo 1861632 2792585 := bstep (se 2 (by rfl) ⟨1047219, by rfl⟩ : syracuseStep 2792585 = 2094439) B2094439
theorem B2792615 : Blo 1861632 2792615 := bstep (se 1 (by rfl) ⟨2094461, by rfl⟩ : syracuseStep 2792615 = 4188923) B4188923
theorem B734708009 : Blo 1861632 734708009 := bstep (se 2 (by rfl) ⟨275515503, by rfl⟩ : syracuseStep 734708009 = 551031007) B551031007
theorem B4473577 : Blo 1861632 4473577 := bstep (se 2 (by rfl) ⟨1677591, by rfl⟩ : syracuseStep 4473577 = 3355183) B3355183
theorem B9430343 : Blo 1861632 9430343 := bstep (se 1 (by rfl) ⟨7072757, by rfl⟩ : syracuseStep 9430343 = 14145515) B14145515
theorem B4474415 : Blo 1861632 4474415 := bstep (se 1 (by rfl) ⟨3355811, by rfl⟩ : syracuseStep 4474415 = 6711623) B6711623
theorem B14149403 : Blo 1861632 14149403 := bstep (se 1 (by rfl) ⟨10612052, by rfl⟩ : syracuseStep 14149403 = 21224105) B21224105
theorem B1861723 : Blo 1861632 1861723 := bstep (se 1 (by rfl) ⟨1396292, by rfl⟩ : syracuseStep 1861723 = 2792585) B2792585
theorem B1861743 : Blo 1861632 1861743 := bstep (se 1 (by rfl) ⟨1396307, by rfl⟩ : syracuseStep 1861743 = 2792615) B2792615
theorem B6286031 : Blo 1861632 6286031 := bstep (se 1 (by rfl) ⟨4714523, by rfl⟩ : syracuseStep 6286031 = 9429047) B9429047
theorem B1862591 : Blo 1861632 1862591 := bstep (se 1 (by rfl) ⟨1396943, by rfl⟩ : syracuseStep 1862591 = 2793887) B2793887
theorem B15920063 : Blo 1861632 15920063 := bstep (se 1 (by rfl) ⟨11940047, by rfl⟩ : syracuseStep 15920063 = 23880095) B23880095
theorem B10071067 : Blo 1861632 10071067 := bstep (se 1 (by rfl) ⟨7553300, by rfl⟩ : syracuseStep 10071067 = 15106601) B15106601
theorem B22646317 : Blo 1861632 22646317 := bstep (se 3 (by rfl) ⟨4246184, by rfl⟩ : syracuseStep 22646317 = 8492369) B8492369
theorem B10342073 : Blo 1861632 10342073 := bstep (se 2 (by rfl) ⟨3878277, by rfl⟩ : syracuseStep 10342073 = 7756555) B7756555
theorem B10612691 : Blo 1861632 10612691 := bstep (se 1 (by rfl) ⟨7959518, by rfl⟩ : syracuseStep 10612691 = 15919037) B15919037
theorem B53727209 : Blo 1861632 53727209 := bstep (se 2 (by rfl) ⟨20147703, by rfl⟩ : syracuseStep 53727209 = 40295407) B40295407
theorem B7959485 : Blo 1861632 7959485 := bstep (se 3 (by rfl) ⟨1492403, by rfl⟩ : syracuseStep 7959485 = 2984807) B2984807
theorem B4191515 : Blo 1861632 4191515 := bstep (se 1 (by rfl) ⟨3143636, by rfl⟩ : syracuseStep 4191515 = 6287273) B6287273
theorem B6288893 : Blo 1861632 6288893 := bstep (se 3 (by rfl) ⟨1179167, by rfl⟩ : syracuseStep 6288893 = 2358335) B2358335
theorem B8492735 : Blo 1861632 8492735 := bstep (se 1 (by rfl) ⟨6369551, by rfl⟩ : syracuseStep 8492735 = 12739103) B12739103
theorem B4912921 : Blo 1861632 4912921 := bstep (se 2 (by rfl) ⟨1842345, by rfl⟩ : syracuseStep 4912921 = 3684691) B3684691
theorem B14137253 : Blo 1861632 14137253 := bstep (se 4 (by rfl) ⟨1325367, by rfl⟩ : syracuseStep 14137253 = 2650735) B2650735
theorem B15915689 : Blo 1861632 15915689 := bstep (se 2 (by rfl) ⟨5968383, by rfl⟩ : syracuseStep 15915689 = 11936767) B11936767
theorem B4193081 : Blo 1861632 4193081 := bstep (se 2 (by rfl) ⟨1572405, by rfl⟩ : syracuseStep 4193081 = 3144811) B3144811
theorem B20135249 : Blo 1861632 20135249 := bstep (se 2 (by rfl) ⟨7550718, by rfl⟩ : syracuseStep 20135249 = 15101437) B15101437
theorem B17899501 : Blo 1861632 17899501 := bstep (se 3 (by rfl) ⟨3356156, by rfl⟩ : syracuseStep 17899501 = 6712313) B6712313
theorem B2794343 : Blo 1861632 2794343 := bstep (se 1 (by rfl) ⟨2095757, by rfl⟩ : syracuseStep 2794343 = 4191515) B4191515
theorem B5964769 : Blo 1861632 5964769 := bstep (se 2 (by rfl) ⟨2236788, by rfl⟩ : syracuseStep 5964769 = 4473577) B4473577
theorem B2982943 : Blo 1861632 2982943 := bstep (se 1 (by rfl) ⟨2237207, by rfl⟩ : syracuseStep 2982943 = 4474415) B4474415
theorem B5661823 : Blo 1861632 5661823 := bstep (se 1 (by rfl) ⟨4246367, by rfl⟩ : syracuseStep 5661823 = 8492735) B8492735
theorem B13428089 : Blo 1861632 13428089 := bstep (se 2 (by rfl) ⟨5035533, by rfl⟩ : syracuseStep 13428089 = 10071067) B10071067
theorem B10610459 : Blo 1861632 10610459 := bstep (se 1 (by rfl) ⟨7957844, by rfl⟩ : syracuseStep 10610459 = 15915689) B15915689
theorem B2795387 : Blo 1861632 2795387 := bstep (se 1 (by rfl) ⟨2096540, by rfl⟩ : syracuseStep 2795387 = 4193081) B4193081
theorem B23866001 : Blo 1861632 23866001 := bstep (se 2 (by rfl) ⟨8949750, by rfl⟩ : syracuseStep 23866001 = 17899501) B17899501
theorem B35818139 : Blo 1861632 35818139 := bstep (se 1 (by rfl) ⟨26863604, by rfl⟩ : syracuseStep 35818139 = 53727209) B53727209
theorem B6286895 : Blo 1861632 6286895 := bstep (se 1 (by rfl) ⟨4715171, by rfl⟩ : syracuseStep 6286895 = 9430343) B9430343
theorem B9432935 : Blo 1861632 9432935 := bstep (se 1 (by rfl) ⟨7074701, by rfl⟩ : syracuseStep 9432935 = 14149403) B14149403
theorem B9424835 : Blo 1861632 9424835 := bstep (se 1 (by rfl) ⟨7068626, by rfl⟩ : syracuseStep 9424835 = 14137253) B14137253
theorem B4190687 : Blo 1861632 4190687 := bstep (se 1 (by rfl) ⟨3143015, by rfl⟩ : syracuseStep 4190687 = 6286031) B6286031
theorem B10613375 : Blo 1861632 10613375 := bstep (se 1 (by rfl) ⟨7960031, by rfl⟩ : syracuseStep 10613375 = 15920063) B15920063
theorem B13423499 : Blo 1861632 13423499 := bstep (se 1 (by rfl) ⟨10067624, by rfl⟩ : syracuseStep 13423499 = 20135249) B20135249
theorem B6550561 : Blo 1861632 6550561 := bstep (se 2 (by rfl) ⟨2456460, by rfl⟩ : syracuseStep 6550561 = 4912921) B4912921
theorem B6894715 : Blo 1861632 6894715 := bstep (se 1 (by rfl) ⟨5171036, by rfl⟩ : syracuseStep 6894715 = 10342073) B10342073
theorem B7075127 : Blo 1861632 7075127 := bstep (se 1 (by rfl) ⟨5306345, by rfl⟩ : syracuseStep 7075127 = 10612691) B10612691
theorem B489805339 : Blo 1861632 489805339 := bstep (se 1 (by rfl) ⟨367354004, by rfl⟩ : syracuseStep 489805339 = 734708009) B734708009
theorem B5306323 : Blo 1861632 5306323 := bstep (se 1 (by rfl) ⟨3979742, by rfl⟩ : syracuseStep 5306323 = 7959485) B7959485
theorem B4192595 : Blo 1861632 4192595 := bstep (se 1 (by rfl) ⟨3144446, by rfl⟩ : syracuseStep 4192595 = 6288893) B6288893
theorem B30195089 : Blo 1861632 30195089 := bstep (se 2 (by rfl) ⟨11323158, by rfl⟩ : syracuseStep 30195089 = 22646317) B22646317
theorem B2793791 : Blo 1861632 2793791 := bstep (se 1 (by rfl) ⟨2095343, by rfl⟩ : syracuseStep 2793791 = 4190687) B4190687
theorem B8734081 : Blo 1861632 8734081 := bstep (se 2 (by rfl) ⟨3275280, by rfl⟩ : syracuseStep 8734081 = 6550561) B6550561
theorem B9192953 : Blo 1861632 9192953 := bstep (se 2 (by rfl) ⟨3447357, by rfl⟩ : syracuseStep 9192953 = 6894715) B6894715
theorem B2795063 : Blo 1861632 2795063 := bstep (se 1 (by rfl) ⟨2096297, by rfl⟩ : syracuseStep 2795063 = 4192595) B4192595
theorem B15910667 : Blo 1861632 15910667 := bstep (se 1 (by rfl) ⟨11933000, by rfl⟩ : syracuseStep 15910667 = 23866001) B23866001
theorem B20130059 : Blo 1861632 20130059 := bstep (se 1 (by rfl) ⟨15097544, by rfl⟩ : syracuseStep 20130059 = 30195089) B30195089
theorem B31812101 : Blo 1861632 31812101 := bstep (se 4 (by rfl) ⟨2982384, by rfl⟩ : syracuseStep 31812101 = 5964769) B5964769
theorem B1862895 : Blo 1861632 1862895 := bstep (se 1 (by rfl) ⟨1397171, by rfl⟩ : syracuseStep 1862895 = 2794343) B2794343
theorem B8948999 : Blo 1861632 8948999 := bstep (se 1 (by rfl) ⟨6711749, by rfl⟩ : syracuseStep 8948999 = 13423499) B13423499
theorem B7073639 : Blo 1861632 7073639 := bstep (se 1 (by rfl) ⟨5305229, by rfl⟩ : syracuseStep 7073639 = 10610459) B10610459
theorem B1863591 : Blo 1861632 1863591 := bstep (se 1 (by rfl) ⟨1397693, by rfl⟩ : syracuseStep 1863591 = 2795387) B2795387
theorem B3977257 : Blo 1861632 3977257 := bstep (se 2 (by rfl) ⟨1491471, by rfl⟩ : syracuseStep 3977257 = 2982943) B2982943
theorem B7549097 : Blo 1861632 7549097 := bstep (se 2 (by rfl) ⟨2830911, by rfl⟩ : syracuseStep 7549097 = 5661823) B5661823
theorem B4191263 : Blo 1861632 4191263 := bstep (se 1 (by rfl) ⟨3143447, by rfl⟩ : syracuseStep 4191263 = 6286895) B6286895
theorem B6288623 : Blo 1861632 6288623 := bstep (se 1 (by rfl) ⟨4716467, by rfl⟩ : syracuseStep 6288623 = 9432935) B9432935
theorem B7075097 : Blo 1861632 7075097 := bstep (se 2 (by rfl) ⟨2653161, by rfl⟩ : syracuseStep 7075097 = 5306323) B5306323
theorem B7075583 : Blo 1861632 7075583 := bstep (se 1 (by rfl) ⟨5306687, by rfl⟩ : syracuseStep 7075583 = 10613375) B10613375
theorem B4716751 : Blo 1861632 4716751 := bstep (se 1 (by rfl) ⟨3537563, by rfl⟩ : syracuseStep 4716751 = 7075127) B7075127
theorem B8952059 : Blo 1861632 8952059 := bstep (se 1 (by rfl) ⟨6714044, by rfl⟩ : syracuseStep 8952059 = 13428089) B13428089
theorem B23878759 : Blo 1861632 23878759 := bstep (se 1 (by rfl) ⟨17909069, by rfl⟩ : syracuseStep 23878759 = 35818139) B35818139
theorem B653073785 : Blo 1861632 653073785 := bstep (se 2 (by rfl) ⟨244902669, by rfl⟩ : syracuseStep 653073785 = 489805339) B489805339
theorem B6283223 : Blo 1861632 6283223 := bstep (se 1 (by rfl) ⟨4712417, by rfl⟩ : syracuseStep 6283223 = 9424835) B9424835
theorem B23863997 : Blo 1861632 23863997 := bstep (se 3 (by rfl) ⟨4474499, by rfl⟩ : syracuseStep 23863997 = 8948999) B8948999
theorem B2794175 : Blo 1861632 2794175 := bstep (se 1 (by rfl) ⟨2095631, by rfl⟩ : syracuseStep 2794175 = 4191263) B4191263
theorem B6128635 : Blo 1861632 6128635 := bstep (se 1 (by rfl) ⟨4596476, by rfl⟩ : syracuseStep 6128635 = 9192953) B9192953
theorem B435382523 : Blo 1861632 435382523 := bstep (se 1 (by rfl) ⟨326536892, by rfl⟩ : syracuseStep 435382523 = 653073785) B653073785
theorem B4188815 : Blo 1861632 4188815 := bstep (se 1 (by rfl) ⟨3141611, by rfl⟩ : syracuseStep 4188815 = 6283223) B6283223
theorem B5303009 : Blo 1861632 5303009 := bstep (se 2 (by rfl) ⟨1988628, by rfl⟩ : syracuseStep 5303009 = 3977257) B3977257
theorem B1862527 : Blo 1861632 1862527 := bstep (se 1 (by rfl) ⟨1396895, by rfl⟩ : syracuseStep 1862527 = 2793791) B2793791
theorem B20130925 : Blo 1861632 20130925 := bstep (se 3 (by rfl) ⟨3774548, by rfl⟩ : syracuseStep 20130925 = 7549097) B7549097
theorem B1863375 : Blo 1861632 1863375 := bstep (se 1 (by rfl) ⟨1397531, by rfl⟩ : syracuseStep 1863375 = 2795063) B2795063
theorem B31838345 : Blo 1861632 31838345 := bstep (se 2 (by rfl) ⟨11939379, by rfl⟩ : syracuseStep 31838345 = 23878759) B23878759
theorem B5968039 : Blo 1861632 5968039 := bstep (se 1 (by rfl) ⟨4476029, by rfl⟩ : syracuseStep 5968039 = 8952059) B8952059
theorem B11645441 : Blo 1861632 11645441 := bstep (se 2 (by rfl) ⟨4367040, by rfl⟩ : syracuseStep 11645441 = 8734081) B8734081
theorem B4715759 : Blo 1861632 4715759 := bstep (se 1 (by rfl) ⟨3536819, by rfl⟩ : syracuseStep 4715759 = 7073639) B7073639
theorem B6289001 : Blo 1861632 6289001 := bstep (se 2 (by rfl) ⟨2358375, by rfl⟩ : syracuseStep 6289001 = 4716751) B4716751
theorem B53680157 : Blo 1861632 53680157 := bstep (se 3 (by rfl) ⟨10065029, by rfl⟩ : syracuseStep 53680157 = 20130059) B20130059
theorem B4192415 : Blo 1861632 4192415 := bstep (se 1 (by rfl) ⟨3144311, by rfl⟩ : syracuseStep 4192415 = 6288623) B6288623
theorem B4716731 : Blo 1861632 4716731 := bstep (se 1 (by rfl) ⟨3537548, by rfl⟩ : syracuseStep 4716731 = 7075097) B7075097
theorem B4717055 : Blo 1861632 4717055 := bstep (se 1 (by rfl) ⟨3537791, by rfl⟩ : syracuseStep 4717055 = 7075583) B7075583
theorem B10607111 : Blo 1861632 10607111 := bstep (se 1 (by rfl) ⟨7955333, by rfl⟩ : syracuseStep 10607111 = 15910667) B15910667
theorem B21208067 : Blo 1861632 21208067 := bstep (se 1 (by rfl) ⟨15906050, by rfl⟩ : syracuseStep 21208067 = 31812101) B31812101
theorem B21225563 : Blo 1861632 21225563 := bstep (se 1 (by rfl) ⟨15919172, by rfl⟩ : syracuseStep 21225563 = 31838345) B31838345
theorem B15909331 : Blo 1861632 15909331 := bstep (se 1 (by rfl) ⟨11931998, by rfl⟩ : syracuseStep 15909331 = 23863997) B23863997
theorem B2794943 : Blo 1861632 2794943 := bstep (se 1 (by rfl) ⟨2096207, by rfl⟩ : syracuseStep 2794943 = 4192415) B4192415
theorem B7071407 : Blo 1861632 7071407 := bstep (se 1 (by rfl) ⟨5303555, by rfl⟩ : syracuseStep 7071407 = 10607111) B10607111
theorem B7957385 : Blo 1861632 7957385 := bstep (se 2 (by rfl) ⟨2984019, by rfl⟩ : syracuseStep 7957385 = 5968039) B5968039
theorem B1862783 : Blo 1861632 1862783 := bstep (se 1 (by rfl) ⟨1397087, by rfl⟩ : syracuseStep 1862783 = 2794175) B2794175
theorem B8171513 : Blo 1861632 8171513 := bstep (se 2 (by rfl) ⟨3064317, by rfl⟩ : syracuseStep 8171513 = 6128635) B6128635
theorem B35786771 : Blo 1861632 35786771 := bstep (se 1 (by rfl) ⟨26840078, by rfl⟩ : syracuseStep 35786771 = 53680157) B53680157
theorem B26841233 : Blo 1861632 26841233 := bstep (se 2 (by rfl) ⟨10065462, by rfl⟩ : syracuseStep 26841233 = 20130925) B20130925
theorem B290255015 : Blo 1861632 290255015 := bstep (se 1 (by rfl) ⟨217691261, by rfl⟩ : syracuseStep 290255015 = 435382523) B435382523
theorem B3535339 : Blo 1861632 3535339 := bstep (se 1 (by rfl) ⟨2651504, by rfl⟩ : syracuseStep 3535339 = 5303009) B5303009
theorem B7763627 : Blo 1861632 7763627 := bstep (se 1 (by rfl) ⟨5822720, by rfl⟩ : syracuseStep 7763627 = 11645441) B11645441
theorem B3143839 : Blo 1861632 3143839 := bstep (se 1 (by rfl) ⟨2357879, by rfl⟩ : syracuseStep 3143839 = 4715759) B4715759
theorem B4192667 : Blo 1861632 4192667 := bstep (se 1 (by rfl) ⟨3144500, by rfl⟩ : syracuseStep 4192667 = 6289001) B6289001
theorem B3144487 : Blo 1861632 3144487 := bstep (se 1 (by rfl) ⟨2358365, by rfl⟩ : syracuseStep 3144487 = 4716731) B4716731
theorem B3144703 : Blo 1861632 3144703 := bstep (se 1 (by rfl) ⟨2358527, by rfl⟩ : syracuseStep 3144703 = 4717055) B4717055
theorem B2792543 : Blo 1861632 2792543 := bstep (se 1 (by rfl) ⟨2094407, by rfl⟩ : syracuseStep 2792543 = 4188815) B4188815
theorem B14138711 : Blo 1861632 14138711 := bstep (se 1 (by rfl) ⟨10604033, by rfl⟩ : syracuseStep 14138711 = 21208067) B21208067
theorem B193503343 : Blo 1861632 193503343 := bstep (se 1 (by rfl) ⟨145127507, by rfl⟩ : syracuseStep 193503343 = 290255015) B290255015
theorem B2795111 : Blo 1861632 2795111 := bstep (se 1 (by rfl) ⟨2096333, by rfl⟩ : syracuseStep 2795111 = 4192667) B4192667
theorem B20703005 : Blo 1861632 20703005 := bstep (se 3 (by rfl) ⟨3881813, by rfl⟩ : syracuseStep 20703005 = 7763627) B7763627
theorem B1861695 : Blo 1861632 1861695 := bstep (se 1 (by rfl) ⟨1396271, by rfl⟩ : syracuseStep 1861695 = 2792543) B2792543
theorem B23857847 : Blo 1861632 23857847 := bstep (se 1 (by rfl) ⟨17893385, by rfl⟩ : syracuseStep 23857847 = 35786771) B35786771
theorem B14150375 : Blo 1861632 14150375 := bstep (se 1 (by rfl) ⟨10612781, by rfl⟩ : syracuseStep 14150375 = 21225563) B21225563
theorem B17894155 : Blo 1861632 17894155 := bstep (se 1 (by rfl) ⟨13420616, by rfl⟩ : syracuseStep 17894155 = 26841233) B26841233
theorem B21212441 : Blo 1861632 21212441 := bstep (se 2 (by rfl) ⟨7954665, by rfl⟩ : syracuseStep 21212441 = 15909331) B15909331
theorem B4713785 : Blo 1861632 4713785 := bstep (se 2 (by rfl) ⟨1767669, by rfl⟩ : syracuseStep 4713785 = 3535339) B3535339
theorem B1863295 : Blo 1861632 1863295 := bstep (se 1 (by rfl) ⟨1397471, by rfl⟩ : syracuseStep 1863295 = 2794943) B2794943
theorem B4714271 : Blo 1861632 4714271 := bstep (se 1 (by rfl) ⟨3535703, by rfl⟩ : syracuseStep 4714271 = 7071407) B7071407
theorem B5304923 : Blo 1861632 5304923 := bstep (se 1 (by rfl) ⟨3978692, by rfl⟩ : syracuseStep 5304923 = 7957385) B7957385
theorem B9425807 : Blo 1861632 9425807 := bstep (se 1 (by rfl) ⟨7069355, by rfl⟩ : syracuseStep 9425807 = 14138711) B14138711
theorem B4191785 : Blo 1861632 4191785 := bstep (se 2 (by rfl) ⟨1571919, by rfl⟩ : syracuseStep 4191785 = 3143839) B3143839
theorem B5447675 : Blo 1861632 5447675 := bstep (se 1 (by rfl) ⟨4085756, by rfl⟩ : syracuseStep 5447675 = 8171513) B8171513
theorem B4192649 : Blo 1861632 4192649 := bstep (se 2 (by rfl) ⟨1572243, by rfl⟩ : syracuseStep 4192649 = 3144487) B3144487
theorem B4192937 : Blo 1861632 4192937 := bstep (se 2 (by rfl) ⟨1572351, by rfl⟩ : syracuseStep 4192937 = 3144703) B3144703
theorem B6283871 : Blo 1861632 6283871 := bstep (se 1 (by rfl) ⟨4712903, by rfl⟩ : syracuseStep 6283871 = 9425807) B9425807
theorem B2794523 : Blo 1861632 2794523 := bstep (se 1 (by rfl) ⟨2095892, by rfl⟩ : syracuseStep 2794523 = 4191785) B4191785
theorem B2795099 : Blo 1861632 2795099 := bstep (se 1 (by rfl) ⟨2096324, by rfl⟩ : syracuseStep 2795099 = 4192649) B4192649
theorem B2795291 : Blo 1861632 2795291 := bstep (se 1 (by rfl) ⟨2096468, by rfl⟩ : syracuseStep 2795291 = 4192937) B4192937
theorem B14141627 : Blo 1861632 14141627 := bstep (se 1 (by rfl) ⟨10606220, by rfl⟩ : syracuseStep 14141627 = 21212441) B21212441
theorem B14527133 : Blo 1861632 14527133 := bstep (se 3 (by rfl) ⟨2723837, by rfl⟩ : syracuseStep 14527133 = 5447675) B5447675
theorem B23858873 : Blo 1861632 23858873 := bstep (se 2 (by rfl) ⟨8947077, by rfl⟩ : syracuseStep 23858873 = 17894155) B17894155
theorem B1863407 : Blo 1861632 1863407 := bstep (se 1 (by rfl) ⟨1397555, by rfl⟩ : syracuseStep 1863407 = 2795111) B2795111
theorem B15905231 : Blo 1861632 15905231 := bstep (se 1 (by rfl) ⟨11928923, by rfl⟩ : syracuseStep 15905231 = 23857847) B23857847
theorem B9433583 : Blo 1861632 9433583 := bstep (se 1 (by rfl) ⟨7075187, by rfl⟩ : syracuseStep 9433583 = 14150375) B14150375
theorem B3142523 : Blo 1861632 3142523 := bstep (se 1 (by rfl) ⟨2356892, by rfl⟩ : syracuseStep 3142523 = 4713785) B4713785
theorem B3142847 : Blo 1861632 3142847 := bstep (se 1 (by rfl) ⟨2357135, by rfl⟩ : syracuseStep 3142847 = 4714271) B4714271
theorem B258004457 : Blo 1861632 258004457 := bstep (se 2 (by rfl) ⟨96751671, by rfl⟩ : syracuseStep 258004457 = 193503343) B193503343
theorem B3536615 : Blo 1861632 3536615 := bstep (se 1 (by rfl) ⟨2652461, by rfl⟩ : syracuseStep 3536615 = 5304923) B5304923
theorem B13802003 : Blo 1861632 13802003 := bstep (se 1 (by rfl) ⟨10351502, by rfl⟩ : syracuseStep 13802003 = 20703005) B20703005
theorem B9201335 : Blo 1861632 9201335 := bstep (se 1 (by rfl) ⟨6901001, by rfl⟩ : syracuseStep 9201335 = 13802003) B13802003
theorem B9684755 : Blo 1861632 9684755 := bstep (se 1 (by rfl) ⟨7263566, by rfl⟩ : syracuseStep 9684755 = 14527133) B14527133
theorem B10603487 : Blo 1861632 10603487 := bstep (se 1 (by rfl) ⟨7952615, by rfl⟩ : syracuseStep 10603487 = 15905231) B15905231
theorem B4189247 : Blo 1861632 4189247 := bstep (se 1 (by rfl) ⟨3141935, by rfl⟩ : syracuseStep 4189247 = 6283871) B6283871
theorem B1863015 : Blo 1861632 1863015 := bstep (se 1 (by rfl) ⟨1397261, by rfl⟩ : syracuseStep 1863015 = 2794523) B2794523
theorem B172002971 : Blo 1861632 172002971 := bstep (se 1 (by rfl) ⟨129002228, by rfl⟩ : syracuseStep 172002971 = 258004457) B258004457
theorem B1863399 : Blo 1861632 1863399 := bstep (se 1 (by rfl) ⟨1397549, by rfl⟩ : syracuseStep 1863399 = 2795099) B2795099
theorem B1863527 : Blo 1861632 1863527 := bstep (se 1 (by rfl) ⟨1397645, by rfl⟩ : syracuseStep 1863527 = 2795291) B2795291
theorem B15905915 : Blo 1861632 15905915 := bstep (se 1 (by rfl) ⟨11929436, by rfl⟩ : syracuseStep 15905915 = 23858873) B23858873
theorem B6289055 : Blo 1861632 6289055 := bstep (se 1 (by rfl) ⟨4716791, by rfl⟩ : syracuseStep 6289055 = 9433583) B9433583
theorem B2095015 : Blo 1861632 2095015 := bstep (se 1 (by rfl) ⟨1571261, by rfl⟩ : syracuseStep 2095015 = 3142523) B3142523
theorem B2095231 : Blo 1861632 2095231 := bstep (se 1 (by rfl) ⟨1571423, by rfl⟩ : syracuseStep 2095231 = 3142847) B3142847
theorem B2357743 : Blo 1861632 2357743 := bstep (se 1 (by rfl) ⟨1768307, by rfl⟩ : syracuseStep 2357743 = 3536615) B3536615
theorem B9427751 : Blo 1861632 9427751 := bstep (se 1 (by rfl) ⟨7070813, by rfl⟩ : syracuseStep 9427751 = 14141627) B14141627
theorem B2793641 : Blo 1861632 2793641 := bstep (se 2 (by rfl) ⟨1047615, by rfl⟩ : syracuseStep 2793641 = 2095231) B2095231
theorem B6456503 : Blo 1861632 6456503 := bstep (se 1 (by rfl) ⟨4842377, by rfl⟩ : syracuseStep 6456503 = 9684755) B9684755
theorem B24536893 : Blo 1861632 24536893 := bstep (se 3 (by rfl) ⟨4600667, by rfl⟩ : syracuseStep 24536893 = 9201335) B9201335
theorem B6285167 : Blo 1861632 6285167 := bstep (se 1 (by rfl) ⟨4713875, by rfl⟩ : syracuseStep 6285167 = 9427751) B9427751
theorem B10603943 : Blo 1861632 10603943 := bstep (se 1 (by rfl) ⟨7952957, by rfl⟩ : syracuseStep 10603943 = 15905915) B15905915
theorem B458674589 : Blo 1861632 458674589 := bstep (se 3 (by rfl) ⟨86001485, by rfl⟩ : syracuseStep 458674589 = 172002971) B172002971
theorem B3143657 : Blo 1861632 3143657 := bstep (se 2 (by rfl) ⟨1178871, by rfl⟩ : syracuseStep 3143657 = 2357743) B2357743
theorem B4192703 : Blo 1861632 4192703 := bstep (se 1 (by rfl) ⟨3144527, by rfl⟩ : syracuseStep 4192703 = 6289055) B6289055
theorem B7068991 : Blo 1861632 7068991 := bstep (se 1 (by rfl) ⟨5301743, by rfl⟩ : syracuseStep 7068991 = 10603487) B10603487
theorem B2792831 : Blo 1861632 2792831 := bstep (se 1 (by rfl) ⟨2094623, by rfl⟩ : syracuseStep 2792831 = 4189247) B4189247
theorem B2793353 : Blo 1861632 2793353 := bstep (se 2 (by rfl) ⟨1047507, by rfl⟩ : syracuseStep 2793353 = 2095015) B2095015
theorem B305783059 : Blo 1861632 305783059 := bstep (se 1 (by rfl) ⟨229337294, by rfl⟩ : syracuseStep 305783059 = 458674589) B458674589
theorem B2795135 : Blo 1861632 2795135 := bstep (se 1 (by rfl) ⟨2096351, by rfl⟩ : syracuseStep 2795135 = 4192703) B4192703
theorem B1861887 : Blo 1861632 1861887 := bstep (se 1 (by rfl) ⟨1396415, by rfl⟩ : syracuseStep 1861887 = 2792831) B2792831
theorem B1862235 : Blo 1861632 1862235 := bstep (se 1 (by rfl) ⟨1396676, by rfl⟩ : syracuseStep 1862235 = 2793353) B2793353
theorem B1862427 : Blo 1861632 1862427 := bstep (se 1 (by rfl) ⟨1396820, by rfl⟩ : syracuseStep 1862427 = 2793641) B2793641
theorem B4304335 : Blo 1861632 4304335 := bstep (se 1 (by rfl) ⟨3228251, by rfl⟩ : syracuseStep 4304335 = 6456503) B6456503
theorem B4190111 : Blo 1861632 4190111 := bstep (se 1 (by rfl) ⟨3142583, by rfl⟩ : syracuseStep 4190111 = 6285167) B6285167
theorem B9425321 : Blo 1861632 9425321 := bstep (se 2 (by rfl) ⟨3534495, by rfl⟩ : syracuseStep 9425321 = 7068991) B7068991
theorem B32715857 : Blo 1861632 32715857 := bstep (se 2 (by rfl) ⟨12268446, by rfl⟩ : syracuseStep 32715857 = 24536893) B24536893
theorem B2095771 : Blo 1861632 2095771 := bstep (se 1 (by rfl) ⟨1571828, by rfl⟩ : syracuseStep 2095771 = 3143657) B3143657
theorem B7069295 : Blo 1861632 7069295 := bstep (se 1 (by rfl) ⟨5301971, by rfl⟩ : syracuseStep 7069295 = 10603943) B10603943
theorem B6283547 : Blo 1861632 6283547 := bstep (se 1 (by rfl) ⟨4712660, by rfl⟩ : syracuseStep 6283547 = 9425321) B9425321
theorem B2794361 : Blo 1861632 2794361 := bstep (se 2 (by rfl) ⟨1047885, by rfl⟩ : syracuseStep 2794361 = 2095771) B2095771
theorem B4712863 : Blo 1861632 4712863 := bstep (se 1 (by rfl) ⟨3534647, by rfl⟩ : syracuseStep 4712863 = 7069295) B7069295
theorem B407710745 : Blo 1861632 407710745 := bstep (se 2 (by rfl) ⟨152891529, by rfl⟩ : syracuseStep 407710745 = 305783059) B305783059
theorem B1863423 : Blo 1861632 1863423 := bstep (se 1 (by rfl) ⟨1397567, by rfl⟩ : syracuseStep 1863423 = 2795135) B2795135
theorem B5739113 : Blo 1861632 5739113 := bstep (se 2 (by rfl) ⟨2152167, by rfl⟩ : syracuseStep 5739113 = 4304335) B4304335
theorem B87242285 : Blo 1861632 87242285 := bstep (se 3 (by rfl) ⟨16357928, by rfl⟩ : syracuseStep 87242285 = 32715857) B32715857
theorem B2793407 : Blo 1861632 2793407 := bstep (se 1 (by rfl) ⟨2095055, by rfl⟩ : syracuseStep 2793407 = 4190111) B4190111
theorem B3826075 : Blo 1861632 3826075 := bstep (se 1 (by rfl) ⟨2869556, by rfl⟩ : syracuseStep 3826075 = 5739113) B5739113
theorem B6283817 : Blo 1861632 6283817 := bstep (se 2 (by rfl) ⟨2356431, by rfl⟩ : syracuseStep 6283817 = 4712863) B4712863
theorem B1862271 : Blo 1861632 1862271 := bstep (se 1 (by rfl) ⟨1396703, by rfl⟩ : syracuseStep 1862271 = 2793407) B2793407
theorem B4189031 : Blo 1861632 4189031 := bstep (se 1 (by rfl) ⟨3141773, by rfl⟩ : syracuseStep 4189031 = 6283547) B6283547
theorem B1862907 : Blo 1861632 1862907 := bstep (se 1 (by rfl) ⟨1397180, by rfl⟩ : syracuseStep 1862907 = 2794361) B2794361
theorem B271807163 : Blo 1861632 271807163 := bstep (se 1 (by rfl) ⟨203855372, by rfl⟩ : syracuseStep 271807163 = 407710745) B407710745
theorem B58161523 : Blo 1861632 58161523 := bstep (se 1 (by rfl) ⟨43621142, by rfl⟩ : syracuseStep 58161523 = 87242285) B87242285
theorem B4189211 : Blo 1861632 4189211 := bstep (se 1 (by rfl) ⟨3141908, by rfl⟩ : syracuseStep 4189211 = 6283817) B6283817
theorem B77548697 : Blo 1861632 77548697 := bstep (se 2 (by rfl) ⟨29080761, by rfl⟩ : syracuseStep 77548697 = 58161523) B58161523
theorem B181204775 : Blo 1861632 181204775 := bstep (se 1 (by rfl) ⟨135903581, by rfl⟩ : syracuseStep 181204775 = 271807163) B271807163
theorem B5101433 : Blo 1861632 5101433 := bstep (se 2 (by rfl) ⟨1913037, by rfl⟩ : syracuseStep 5101433 = 3826075) B3826075
theorem B2792687 : Blo 1861632 2792687 := bstep (se 1 (by rfl) ⟨2094515, by rfl⟩ : syracuseStep 2792687 = 4189031) B4189031
theorem B3400955 : Blo 1861632 3400955 := bstep (se 1 (by rfl) ⟨2550716, by rfl⟩ : syracuseStep 3400955 = 5101433) B5101433
theorem B1861791 : Blo 1861632 1861791 := bstep (se 1 (by rfl) ⟨1396343, by rfl⟩ : syracuseStep 1861791 = 2792687) B2792687
theorem B120803183 : Blo 1861632 120803183 := bstep (se 1 (by rfl) ⟨90602387, by rfl⟩ : syracuseStep 120803183 = 181204775) B181204775
theorem B2792807 : Blo 1861632 2792807 := bstep (se 1 (by rfl) ⟨2094605, by rfl⟩ : syracuseStep 2792807 = 4189211) B4189211
theorem B51699131 : Blo 1861632 51699131 := bstep (se 1 (by rfl) ⟨38774348, by rfl⟩ : syracuseStep 51699131 = 77548697) B77548697
theorem B1861871 : Blo 1861632 1861871 := bstep (se 1 (by rfl) ⟨1396403, by rfl⟩ : syracuseStep 1861871 = 2792807) B2792807
theorem B34466087 : Blo 1861632 34466087 := bstep (se 1 (by rfl) ⟨25849565, by rfl⟩ : syracuseStep 34466087 = 51699131) B51699131
theorem B2267303 : Blo 1861632 2267303 := bstep (se 1 (by rfl) ⟨1700477, by rfl⟩ : syracuseStep 2267303 = 3400955) B3400955
theorem B80535455 : Blo 1861632 80535455 := bstep (se 1 (by rfl) ⟨60401591, by rfl⟩ : syracuseStep 80535455 = 120803183) B120803183
theorem B24184565 : Blo 1861632 24184565 := bstep (se 5 (by rfl) ⟨1133651, by rfl⟩ : syracuseStep 24184565 = 2267303) B2267303
theorem B91909565 : Blo 1861632 91909565 := bstep (se 3 (by rfl) ⟨17233043, by rfl⟩ : syracuseStep 91909565 = 34466087) B34466087
theorem B53690303 : Blo 1861632 53690303 := bstep (se 1 (by rfl) ⟨40267727, by rfl⟩ : syracuseStep 53690303 = 80535455) B80535455
theorem B16123043 : Blo 1861632 16123043 := bstep (se 1 (by rfl) ⟨12092282, by rfl⟩ : syracuseStep 16123043 = 24184565) B24184565
theorem B35793535 : Blo 1861632 35793535 := bstep (se 1 (by rfl) ⟨26845151, by rfl⟩ : syracuseStep 35793535 = 53690303) B53690303
theorem B61273043 : Blo 1861632 61273043 := bstep (se 1 (by rfl) ⟨45954782, by rfl⟩ : syracuseStep 61273043 = 91909565) B91909565
theorem B10748695 : Blo 1861632 10748695 := bstep (se 1 (by rfl) ⟨8061521, by rfl⟩ : syracuseStep 10748695 = 16123043) B16123043
theorem B40848695 : Blo 1861632 40848695 := bstep (se 1 (by rfl) ⟨30636521, by rfl⟩ : syracuseStep 40848695 = 61273043) B61273043
theorem B47724713 : Blo 1861632 47724713 := bstep (se 2 (by rfl) ⟨17896767, by rfl⟩ : syracuseStep 47724713 = 35793535) B35793535
theorem B27232463 : Blo 1861632 27232463 := bstep (se 1 (by rfl) ⟨20424347, by rfl⟩ : syracuseStep 27232463 = 40848695) B40848695
theorem B14331593 : Blo 1861632 14331593 := bstep (se 2 (by rfl) ⟨5374347, by rfl⟩ : syracuseStep 14331593 = 10748695) B10748695
theorem B31816475 : Blo 1861632 31816475 := bstep (se 1 (by rfl) ⟨23862356, by rfl⟩ : syracuseStep 31816475 = 47724713) B47724713
theorem B18154975 : Blo 1861632 18154975 := bstep (se 1 (by rfl) ⟨13616231, by rfl⟩ : syracuseStep 18154975 = 27232463) B27232463
theorem B21210983 : Blo 1861632 21210983 := bstep (se 1 (by rfl) ⟨15908237, by rfl⟩ : syracuseStep 21210983 = 31816475) B31816475
theorem B9554395 : Blo 1861632 9554395 := bstep (se 1 (by rfl) ⟨7165796, by rfl⟩ : syracuseStep 9554395 = 14331593) B14331593
theorem B12739193 : Blo 1861632 12739193 := bstep (se 2 (by rfl) ⟨4777197, by rfl⟩ : syracuseStep 12739193 = 9554395) B9554395
theorem B14140655 : Blo 1861632 14140655 := bstep (se 1 (by rfl) ⟨10605491, by rfl⟩ : syracuseStep 14140655 = 21210983) B21210983
theorem B24206633 : Blo 1861632 24206633 := bstep (se 2 (by rfl) ⟨9077487, by rfl⟩ : syracuseStep 24206633 = 18154975) B18154975
theorem B8492795 : Blo 1861632 8492795 := bstep (se 1 (by rfl) ⟨6369596, by rfl⟩ : syracuseStep 8492795 = 12739193) B12739193
theorem B9427103 : Blo 1861632 9427103 := bstep (se 1 (by rfl) ⟨7070327, by rfl⟩ : syracuseStep 9427103 = 14140655) B14140655
theorem B16137755 : Blo 1861632 16137755 := bstep (se 1 (by rfl) ⟨12103316, by rfl⟩ : syracuseStep 16137755 = 24206633) B24206633
theorem B5661863 : Blo 1861632 5661863 := bstep (se 1 (by rfl) ⟨4246397, by rfl⟩ : syracuseStep 5661863 = 8492795) B8492795
theorem B6284735 : Blo 1861632 6284735 := bstep (se 1 (by rfl) ⟨4713551, by rfl⟩ : syracuseStep 6284735 = 9427103) B9427103
theorem B10758503 : Blo 1861632 10758503 := bstep (se 1 (by rfl) ⟨8068877, by rfl⟩ : syracuseStep 10758503 = 16137755) B16137755
theorem B4189823 : Blo 1861632 4189823 := bstep (se 1 (by rfl) ⟨3142367, by rfl⟩ : syracuseStep 4189823 = 6284735) B6284735
theorem B7172335 : Blo 1861632 7172335 := bstep (se 1 (by rfl) ⟨5379251, by rfl⟩ : syracuseStep 7172335 = 10758503) B10758503
theorem B3774575 : Blo 1861632 3774575 := bstep (se 1 (by rfl) ⟨2830931, by rfl⟩ : syracuseStep 3774575 = 5661863) B5661863
theorem B2516383 : Blo 1861632 2516383 := bstep (se 1 (by rfl) ⟨1887287, by rfl⟩ : syracuseStep 2516383 = 3774575) B3774575
theorem B9563113 : Blo 1861632 9563113 := bstep (se 2 (by rfl) ⟨3586167, by rfl⟩ : syracuseStep 9563113 = 7172335) B7172335
theorem B2793215 : Blo 1861632 2793215 := bstep (se 1 (by rfl) ⟨2094911, by rfl⟩ : syracuseStep 2793215 = 4189823) B4189823
theorem B1862143 : Blo 1861632 1862143 := bstep (se 1 (by rfl) ⟨1396607, by rfl⟩ : syracuseStep 1862143 = 2793215) B2793215
theorem B3355177 : Blo 1861632 3355177 := bstep (se 2 (by rfl) ⟨1258191, by rfl⟩ : syracuseStep 3355177 = 2516383) B2516383
theorem B51003269 : Blo 1861632 51003269 := bstep (se 4 (by rfl) ⟨4781556, by rfl⟩ : syracuseStep 51003269 = 9563113) B9563113
theorem B4473569 : Blo 1861632 4473569 := bstep (se 2 (by rfl) ⟨1677588, by rfl⟩ : syracuseStep 4473569 = 3355177) B3355177
theorem B34002179 : Blo 1861632 34002179 := bstep (se 1 (by rfl) ⟨25501634, by rfl⟩ : syracuseStep 34002179 = 51003269) B51003269
theorem B22668119 : Blo 1861632 22668119 := bstep (se 1 (by rfl) ⟨17001089, by rfl⟩ : syracuseStep 22668119 = 34002179) B34002179
theorem B11929517 : Blo 1861632 11929517 := bstep (se 3 (by rfl) ⟨2236784, by rfl⟩ : syracuseStep 11929517 = 4473569) B4473569
theorem B15112079 : Blo 1861632 15112079 := bstep (se 1 (by rfl) ⟨11334059, by rfl⟩ : syracuseStep 15112079 = 22668119) B22668119
theorem B7953011 : Blo 1861632 7953011 := bstep (se 1 (by rfl) ⟨5964758, by rfl⟩ : syracuseStep 7953011 = 11929517) B11929517
theorem B5302007 : Blo 1861632 5302007 := bstep (se 1 (by rfl) ⟨3976505, by rfl⟩ : syracuseStep 5302007 = 7953011) B7953011
theorem B10074719 : Blo 1861632 10074719 := bstep (se 1 (by rfl) ⟨7556039, by rfl⟩ : syracuseStep 10074719 = 15112079) B15112079
theorem B3534671 : Blo 1861632 3534671 := bstep (se 1 (by rfl) ⟨2651003, by rfl⟩ : syracuseStep 3534671 = 5302007) B5302007
theorem B6716479 : Blo 1861632 6716479 := bstep (se 1 (by rfl) ⟨5037359, by rfl⟩ : syracuseStep 6716479 = 10074719) B10074719
theorem B8955305 : Blo 1861632 8955305 := bstep (se 2 (by rfl) ⟨3358239, by rfl⟩ : syracuseStep 8955305 = 6716479) B6716479
theorem B2356447 : Blo 1861632 2356447 := bstep (se 1 (by rfl) ⟨1767335, by rfl⟩ : syracuseStep 2356447 = 3534671) B3534671
theorem B3141929 : Blo 1861632 3141929 := bstep (se 2 (by rfl) ⟨1178223, by rfl⟩ : syracuseStep 3141929 = 2356447) B2356447
theorem B5970203 : Blo 1861632 5970203 := bstep (se 1 (by rfl) ⟨4477652, by rfl⟩ : syracuseStep 5970203 = 8955305) B8955305
theorem B2094619 : Blo 1861632 2094619 := bstep (se 1 (by rfl) ⟨1570964, by rfl⟩ : syracuseStep 2094619 = 3141929) B3141929
theorem B3980135 : Blo 1861632 3980135 := bstep (se 1 (by rfl) ⟨2985101, by rfl⟩ : syracuseStep 3980135 = 5970203) B5970203
theorem B10613693 : Blo 1861632 10613693 := bstep (se 3 (by rfl) ⟨1990067, by rfl⟩ : syracuseStep 10613693 = 3980135) B3980135
theorem B2792825 : Blo 1861632 2792825 := bstep (se 2 (by rfl) ⟨1047309, by rfl⟩ : syracuseStep 2792825 = 2094619) B2094619
theorem B1861883 : Blo 1861632 1861883 := bstep (se 1 (by rfl) ⟨1396412, by rfl⟩ : syracuseStep 1861883 = 2792825) B2792825
theorem B7075795 : Blo 1861632 7075795 := bstep (se 1 (by rfl) ⟨5306846, by rfl⟩ : syracuseStep 7075795 = 10613693) B10613693
theorem B9434393 : Blo 1861632 9434393 := bstep (se 2 (by rfl) ⟨3537897, by rfl⟩ : syracuseStep 9434393 = 7075795) B7075795
theorem B6289595 : Blo 1861632 6289595 := bstep (se 1 (by rfl) ⟨4717196, by rfl⟩ : syracuseStep 6289595 = 9434393) B9434393
theorem B4193063 : Blo 1861632 4193063 := bstep (se 1 (by rfl) ⟨3144797, by rfl⟩ : syracuseStep 4193063 = 6289595) B6289595
theorem B2795375 : Blo 1861632 2795375 := bstep (se 1 (by rfl) ⟨2096531, by rfl⟩ : syracuseStep 2795375 = 4193063) B4193063
theorem B1863583 : Blo 1861632 1863583 := bstep (se 1 (by rfl) ⟨1397687, by rfl⟩ : syracuseStep 1863583 = 2795375) B2795375

theorem C0 (j : ℕ) (h1 : 465408 ≤ j) (h2 : j ≤ 465907) : Blo 1861632 (4 * j + 3) := by
  interval_cases j
  · exact B1861635
  · exact B1861639
  · exact B1861643
  · exact B1861647
  · exact B1861651
  · exact B1861655
  · exact B1861659
  · exact B1861663
  · exact B1861667
  · exact B1861671
  · exact B1861675
  · exact B1861679
  · exact B1861683
  · exact B1861687
  · exact B1861691
  · exact B1861695
  · exact B1861699
  · exact B1861703
  · exact B1861707
  · exact B1861711
  · exact B1861715
  · exact B1861719
  · exact B1861723
  · exact B1861727
  · exact B1861731
  · exact B1861735
  · exact B1861739
  · exact B1861743
  · exact B1861747
  · exact B1861751
  · exact B1861755
  · exact B1861759
  · exact B1861763
  · exact B1861767
  · exact B1861771
  · exact B1861775
  · exact B1861779
  · exact B1861783
  · exact B1861787
  · exact B1861791
  · exact B1861795
  · exact B1861799
  · exact B1861803
  · exact B1861807
  · exact B1861811
  · exact B1861815
  · exact B1861819
  · exact B1861823
  · exact B1861827
  · exact B1861831
  · exact B1861835
  · exact B1861839
  · exact B1861843
  · exact B1861847
  · exact B1861851
  · exact B1861855
  · exact B1861859
  · exact B1861863
  · exact B1861867
  · exact B1861871
  · exact B1861875
  · exact B1861879
  · exact B1861883
  · exact B1861887
  · exact B1861891
  · exact B1861895
  · exact B1861899
  · exact B1861903
  · exact B1861907
  · exact B1861911
  · exact B1861915
  · exact B1861919
  · exact B1861923
  · exact B1861927
  · exact B1861931
  · exact B1861935
  · exact B1861939
  · exact B1861943
  · exact B1861947
  · exact B1861951
  · exact B1861955
  · exact B1861959
  · exact B1861963
  · exact B1861967
  · exact B1861971
  · exact B1861975
  · exact B1861979
  · exact B1861983
  · exact B1861987
  · exact B1861991
  · exact B1861995
  · exact B1861999
  · exact B1862003
  · exact B1862007
  · exact B1862011
  · exact B1862015
  · exact B1862019
  · exact B1862023
  · exact B1862027
  · exact B1862031
  · exact B1862035
  · exact B1862039
  · exact B1862043
  · exact B1862047
  · exact B1862051
  · exact B1862055
  · exact B1862059
  · exact B1862063
  · exact B1862067
  · exact B1862071
  · exact B1862075
  · exact B1862079
  · exact B1862083
  · exact B1862087
  · exact B1862091
  · exact B1862095
  · exact B1862099
  · exact B1862103
  · exact B1862107
  · exact B1862111
  · exact B1862115
  · exact B1862119
  · exact B1862123
  · exact B1862127
  · exact B1862131
  · exact B1862135
  · exact B1862139
  · exact B1862143
  · exact B1862147
  · exact B1862151
  · exact B1862155
  · exact B1862159
  · exact B1862163
  · exact B1862167
  · exact B1862171
  · exact B1862175
  · exact B1862179
  · exact B1862183
  · exact B1862187
  · exact B1862191
  · exact B1862195
  · exact B1862199
  · exact B1862203
  · exact B1862207
  · exact B1862211
  · exact B1862215
  · exact B1862219
  · exact B1862223
  · exact B1862227
  · exact B1862231
  · exact B1862235
  · exact B1862239
  · exact B1862243
  · exact B1862247
  · exact B1862251
  · exact B1862255
  · exact B1862259
  · exact B1862263
  · exact B1862267
  · exact B1862271
  · exact B1862275
  · exact B1862279
  · exact B1862283
  · exact B1862287
  · exact B1862291
  · exact B1862295
  · exact B1862299
  · exact B1862303
  · exact B1862307
  · exact B1862311
  · exact B1862315
  · exact B1862319
  · exact B1862323
  · exact B1862327
  · exact B1862331
  · exact B1862335
  · exact B1862339
  · exact B1862343
  · exact B1862347
  · exact B1862351
  · exact B1862355
  · exact B1862359
  · exact B1862363
  · exact B1862367
  · exact B1862371
  · exact B1862375
  · exact B1862379
  · exact B1862383
  · exact B1862387
  · exact B1862391
  · exact B1862395
  · exact B1862399
  · exact B1862403
  · exact B1862407
  · exact B1862411
  · exact B1862415
  · exact B1862419
  · exact B1862423
  · exact B1862427
  · exact B1862431
  · exact B1862435
  · exact B1862439
  · exact B1862443
  · exact B1862447
  · exact B1862451
  · exact B1862455
  · exact B1862459
  · exact B1862463
  · exact B1862467
  · exact B1862471
  · exact B1862475
  · exact B1862479
  · exact B1862483
  · exact B1862487
  · exact B1862491
  · exact B1862495
  · exact B1862499
  · exact B1862503
  · exact B1862507
  · exact B1862511
  · exact B1862515
  · exact B1862519
  · exact B1862523
  · exact B1862527
  · exact B1862531
  · exact B1862535
  · exact B1862539
  · exact B1862543
  · exact B1862547
  · exact B1862551
  · exact B1862555
  · exact B1862559
  · exact B1862563
  · exact B1862567
  · exact B1862571
  · exact B1862575
  · exact B1862579
  · exact B1862583
  · exact B1862587
  · exact B1862591
  · exact B1862595
  · exact B1862599
  · exact B1862603
  · exact B1862607
  · exact B1862611
  · exact B1862615
  · exact B1862619
  · exact B1862623
  · exact B1862627
  · exact B1862631
  · exact B1862635
  · exact B1862639
  · exact B1862643
  · exact B1862647
  · exact B1862651
  · exact B1862655
  · exact B1862659
  · exact B1862663
  · exact B1862667
  · exact B1862671
  · exact B1862675
  · exact B1862679
  · exact B1862683
  · exact B1862687
  · exact B1862691
  · exact B1862695
  · exact B1862699
  · exact B1862703
  · exact B1862707
  · exact B1862711
  · exact B1862715
  · exact B1862719
  · exact B1862723
  · exact B1862727
  · exact B1862731
  · exact B1862735
  · exact B1862739
  · exact B1862743
  · exact B1862747
  · exact B1862751
  · exact B1862755
  · exact B1862759
  · exact B1862763
  · exact B1862767
  · exact B1862771
  · exact B1862775
  · exact B1862779
  · exact B1862783
  · exact B1862787
  · exact B1862791
  · exact B1862795
  · exact B1862799
  · exact B1862803
  · exact B1862807
  · exact B1862811
  · exact B1862815
  · exact B1862819
  · exact B1862823
  · exact B1862827
  · exact B1862831
  · exact B1862835
  · exact B1862839
  · exact B1862843
  · exact B1862847
  · exact B1862851
  · exact B1862855
  · exact B1862859
  · exact B1862863
  · exact B1862867
  · exact B1862871
  · exact B1862875
  · exact B1862879
  · exact B1862883
  · exact B1862887
  · exact B1862891
  · exact B1862895
  · exact B1862899
  · exact B1862903
  · exact B1862907
  · exact B1862911
  · exact B1862915
  · exact B1862919
  · exact B1862923
  · exact B1862927
  · exact B1862931
  · exact B1862935
  · exact B1862939
  · exact B1862943
  · exact B1862947
  · exact B1862951
  · exact B1862955
  · exact B1862959
  · exact B1862963
  · exact B1862967
  · exact B1862971
  · exact B1862975
  · exact B1862979
  · exact B1862983
  · exact B1862987
  · exact B1862991
  · exact B1862995
  · exact B1862999
  · exact B1863003
  · exact B1863007
  · exact B1863011
  · exact B1863015
  · exact B1863019
  · exact B1863023
  · exact B1863027
  · exact B1863031
  · exact B1863035
  · exact B1863039
  · exact B1863043
  · exact B1863047
  · exact B1863051
  · exact B1863055
  · exact B1863059
  · exact B1863063
  · exact B1863067
  · exact B1863071
  · exact B1863075
  · exact B1863079
  · exact B1863083
  · exact B1863087
  · exact B1863091
  · exact B1863095
  · exact B1863099
  · exact B1863103
  · exact B1863107
  · exact B1863111
  · exact B1863115
  · exact B1863119
  · exact B1863123
  · exact B1863127
  · exact B1863131
  · exact B1863135
  · exact B1863139
  · exact B1863143
  · exact B1863147
  · exact B1863151
  · exact B1863155
  · exact B1863159
  · exact B1863163
  · exact B1863167
  · exact B1863171
  · exact B1863175
  · exact B1863179
  · exact B1863183
  · exact B1863187
  · exact B1863191
  · exact B1863195
  · exact B1863199
  · exact B1863203
  · exact B1863207
  · exact B1863211
  · exact B1863215
  · exact B1863219
  · exact B1863223
  · exact B1863227
  · exact B1863231
  · exact B1863235
  · exact B1863239
  · exact B1863243
  · exact B1863247
  · exact B1863251
  · exact B1863255
  · exact B1863259
  · exact B1863263
  · exact B1863267
  · exact B1863271
  · exact B1863275
  · exact B1863279
  · exact B1863283
  · exact B1863287
  · exact B1863291
  · exact B1863295
  · exact B1863299
  · exact B1863303
  · exact B1863307
  · exact B1863311
  · exact B1863315
  · exact B1863319
  · exact B1863323
  · exact B1863327
  · exact B1863331
  · exact B1863335
  · exact B1863339
  · exact B1863343
  · exact B1863347
  · exact B1863351
  · exact B1863355
  · exact B1863359
  · exact B1863363
  · exact B1863367
  · exact B1863371
  · exact B1863375
  · exact B1863379
  · exact B1863383
  · exact B1863387
  · exact B1863391
  · exact B1863395
  · exact B1863399
  · exact B1863403
  · exact B1863407
  · exact B1863411
  · exact B1863415
  · exact B1863419
  · exact B1863423
  · exact B1863427
  · exact B1863431
  · exact B1863435
  · exact B1863439
  · exact B1863443
  · exact B1863447
  · exact B1863451
  · exact B1863455
  · exact B1863459
  · exact B1863463
  · exact B1863467
  · exact B1863471
  · exact B1863475
  · exact B1863479
  · exact B1863483
  · exact B1863487
  · exact B1863491
  · exact B1863495
  · exact B1863499
  · exact B1863503
  · exact B1863507
  · exact B1863511
  · exact B1863515
  · exact B1863519
  · exact B1863523
  · exact B1863527
  · exact B1863531
  · exact B1863535
  · exact B1863539
  · exact B1863543
  · exact B1863547
  · exact B1863551
  · exact B1863555
  · exact B1863559
  · exact B1863563
  · exact B1863567
  · exact B1863571
  · exact B1863575
  · exact B1863579
  · exact B1863583
  · exact B1863587
  · exact B1863591
  · exact B1863595
  · exact B1863599
  · exact B1863603
  · exact B1863607
  · exact B1863611
  · exact B1863615
  · exact B1863619
  · exact B1863623
  · exact B1863627
  · exact B1863631

theorem solution (m : ℕ) (hlo : 1861632 ≤ m) (hhi : m ≤ 1863632) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 465408 ≤ j := by omega
    have hj2 : j ≤ 465907 := by omega
    have hb : Blo 1861632 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
