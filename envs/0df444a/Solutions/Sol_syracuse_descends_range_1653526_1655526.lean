-- Prove2me | solution 1 for syracuse_descends_range_1653526_1655526
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:18:06.996321+00:00
-- url     : https://prove2.me/submissions/b7122bf9-a2a6-410b-a5b7-814c62dde1d5

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


theorem B2482181 : Blo 1653526 2482181 := bbase (se 4 (by rfl) ⟨232704, by rfl⟩ : syracuseStep 2482181 = 465409) (by norm_num)
theorem B8380421 : Blo 1653526 8380421 := bbase (se 4 (by rfl) ⟨785664, by rfl⟩ : syracuseStep 8380421 = 1571329) (by norm_num)
theorem B3579917 : Blo 1653526 3579917 := bbase (se 3 (by rfl) ⟨671234, by rfl⟩ : syracuseStep 3579917 = 1342469) (by norm_num)
theorem B3973141 : Blo 1653526 3973141 := bbase (se 6 (by rfl) ⟨93120, by rfl⟩ : syracuseStep 3973141 = 186241) (by norm_num)
theorem B2482205 : Blo 1653526 2482205 := bbase (se 3 (by rfl) ⟨465413, by rfl⟩ : syracuseStep 2482205 = 930827) (by norm_num)
theorem B2482229 : Blo 1653526 2482229 := bbase (se 5 (by rfl) ⟨116354, by rfl⟩ : syracuseStep 2482229 = 232709) (by norm_num)
theorem B4186181 : Blo 1653526 4186181 := bbase (se 4 (by rfl) ⟨392454, by rfl⟩ : syracuseStep 4186181 = 784909) (by norm_num)
theorem B2793541 : Blo 1653526 2793541 := bbase (se 4 (by rfl) ⟨261894, by rfl⟩ : syracuseStep 2793541 = 523789) (by norm_num)
theorem B2482253 : Blo 1653526 2482253 := bbase (se 3 (by rfl) ⟨465422, by rfl⟩ : syracuseStep 2482253 = 930845) (by norm_num)
theorem B2482277 : Blo 1653526 2482277 := bbase (se 4 (by rfl) ⟨232713, by rfl⟩ : syracuseStep 2482277 = 465427) (by norm_num)
theorem B2482301 : Blo 1653526 2482301 := bbase (se 3 (by rfl) ⟨465431, by rfl⟩ : syracuseStep 2482301 = 930863) (by norm_num)
theorem B2482325 : Blo 1653526 2482325 := bbase (se 6 (by rfl) ⟨58179, by rfl⟩ : syracuseStep 2482325 = 116359) (by norm_num)
theorem B2793629 : Blo 1653526 2793629 := bbase (se 3 (by rfl) ⟨523805, by rfl⟩ : syracuseStep 2793629 = 1047611) (by norm_num)
theorem B5587109 : Blo 1653526 5587109 := bbase (se 4 (by rfl) ⟨523791, by rfl⟩ : syracuseStep 5587109 = 1047583) (by norm_num)
theorem B2482349 : Blo 1653526 2482349 := bbase (se 3 (by rfl) ⟨465440, by rfl⟩ : syracuseStep 2482349 = 930881) (by norm_num)
theorem B2482373 : Blo 1653526 2482373 := bbase (se 4 (by rfl) ⟨232722, by rfl⟩ : syracuseStep 2482373 = 465445) (by norm_num)
theorem B2482397 : Blo 1653526 2482397 := bbase (se 3 (by rfl) ⟨465449, by rfl⟩ : syracuseStep 2482397 = 930899) (by norm_num)
theorem B8945909 : Blo 1653526 8945909 := bbase (se 5 (by rfl) ⟨419339, by rfl⟩ : syracuseStep 8945909 = 838679) (by norm_num)
theorem B2482421 : Blo 1653526 2482421 := bbase (se 5 (by rfl) ⟨116363, by rfl⟩ : syracuseStep 2482421 = 232727) (by norm_num)
theorem B2482445 : Blo 1653526 2482445 := bbase (se 3 (by rfl) ⟨465458, by rfl⟩ : syracuseStep 2482445 = 930917) (by norm_num)
theorem B2482469 : Blo 1653526 2482469 := bbase (se 4 (by rfl) ⟨232731, by rfl⟩ : syracuseStep 2482469 = 465463) (by norm_num)
theorem B2482493 : Blo 1653526 2482493 := bbase (se 3 (by rfl) ⟨465467, by rfl⟩ : syracuseStep 2482493 = 930935) (by norm_num)
theorem B2482517 : Blo 1653526 2482517 := bbase (se 10 (by rfl) ⟨3636, by rfl⟩ : syracuseStep 2482517 = 7273) (by norm_num)
theorem B2482541 : Blo 1653526 2482541 := bbase (se 3 (by rfl) ⟨465476, by rfl⟩ : syracuseStep 2482541 = 930953) (by norm_num)
theorem B2482565 : Blo 1653526 2482565 := bbase (se 4 (by rfl) ⟨232740, by rfl⟩ : syracuseStep 2482565 = 465481) (by norm_num)
theorem B4186525 : Blo 1653526 4186525 := bbase (se 3 (by rfl) ⟨784973, by rfl⟩ : syracuseStep 4186525 = 1569947) (by norm_num)
theorem B2482589 : Blo 1653526 2482589 := bbase (se 3 (by rfl) ⟨465485, by rfl⟩ : syracuseStep 2482589 = 930971) (by norm_num)
theorem B8372645 : Blo 1653526 8372645 := bbase (se 4 (by rfl) ⟨784935, by rfl⟩ : syracuseStep 8372645 = 1569871) (by norm_num)
theorem B2482613 : Blo 1653526 2482613 := bbase (se 5 (by rfl) ⟨116372, by rfl⟩ : syracuseStep 2482613 = 232745) (by norm_num)
theorem B2482637 : Blo 1653526 2482637 := bbase (se 3 (by rfl) ⟨465494, by rfl⟩ : syracuseStep 2482637 = 930989) (by norm_num)
theorem B2482661 : Blo 1653526 2482661 := bbase (se 4 (by rfl) ⟨232749, by rfl⟩ : syracuseStep 2482661 = 465499) (by norm_num)
theorem B2482685 : Blo 1653526 2482685 := bbase (se 3 (by rfl) ⟨465503, by rfl⟩ : syracuseStep 2482685 = 931007) (by norm_num)
theorem B4186637 : Blo 1653526 4186637 := bbase (se 3 (by rfl) ⟨784994, by rfl⟩ : syracuseStep 4186637 = 1569989) (by norm_num)
theorem B2482709 : Blo 1653526 2482709 := bbase (se 6 (by rfl) ⟨58188, by rfl⟩ : syracuseStep 2482709 = 116377) (by norm_num)
theorem B3973661 : Blo 1653526 3973661 := bbase (se 3 (by rfl) ⟨745061, by rfl⟩ : syracuseStep 3973661 = 1490123) (by norm_num)
theorem B2482733 : Blo 1653526 2482733 := bbase (se 3 (by rfl) ⟨465512, by rfl⟩ : syracuseStep 2482733 = 931025) (by norm_num)
theorem B6365765 : Blo 1653526 6365765 := bbase (se 4 (by rfl) ⟨596790, by rfl⟩ : syracuseStep 6365765 = 1193581) (by norm_num)
theorem B2482757 : Blo 1653526 2482757 := bbase (se 4 (by rfl) ⟨232758, by rfl⟩ : syracuseStep 2482757 = 465517) (by norm_num)
theorem B2482781 : Blo 1653526 2482781 := bbase (se 3 (by rfl) ⟨465521, by rfl⟩ : syracuseStep 2482781 = 931043) (by norm_num)
theorem B2482805 : Blo 1653526 2482805 := bbase (se 5 (by rfl) ⟨116381, by rfl⟩ : syracuseStep 2482805 = 232763) (by norm_num)
theorem B3580541 : Blo 1653526 3580541 := bbase (se 3 (by rfl) ⟨671351, by rfl⟩ : syracuseStep 3580541 = 1342703) (by norm_num)
theorem B2482829 : Blo 1653526 2482829 := bbase (se 3 (by rfl) ⟨465530, by rfl⟩ : syracuseStep 2482829 = 931061) (by norm_num)
theorem B1860241 : Blo 1653526 1860241 := bbase (se 2 (by rfl) ⟨697590, by rfl⟩ : syracuseStep 1860241 = 1395181) (by norm_num)
theorem B4711061 : Blo 1653526 4711061 := bbase (se 6 (by rfl) ⟨110415, by rfl⟩ : syracuseStep 4711061 = 220831) (by norm_num)
theorem B2482853 : Blo 1653526 2482853 := bbase (se 4 (by rfl) ⟨232767, by rfl⟩ : syracuseStep 2482853 = 465535) (by norm_num)
theorem B1860277 : Blo 1653526 1860277 := bbase (se 5 (by rfl) ⟨87200, by rfl⟩ : syracuseStep 1860277 = 174401) (by norm_num)
theorem B10060469 : Blo 1653526 10060469 := bbase (se 5 (by rfl) ⟨471584, by rfl⟩ : syracuseStep 10060469 = 943169) (by norm_num)
theorem B2482877 : Blo 1653526 2482877 := bbase (se 3 (by rfl) ⟨465539, by rfl⟩ : syracuseStep 2482877 = 931079) (by norm_num)
theorem B4186829 : Blo 1653526 4186829 := bbase (se 3 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 4186829 = 1570061) (by norm_num)
theorem B2482901 : Blo 1653526 2482901 := bbase (se 7 (by rfl) ⟨29096, by rfl⟩ : syracuseStep 2482901 = 58193) (by norm_num)
theorem B1860313 : Blo 1653526 1860313 := bbase (se 2 (by rfl) ⟨697617, by rfl⟩ : syracuseStep 1860313 = 1395235) (by norm_num)
theorem B2482925 : Blo 1653526 2482925 := bbase (se 3 (by rfl) ⟨465548, by rfl⟩ : syracuseStep 2482925 = 931097) (by norm_num)
theorem B5300981 : Blo 1653526 5300981 := bbase (se 5 (by rfl) ⟨248483, by rfl⟩ : syracuseStep 5300981 = 496967) (by norm_num)
theorem B1860349 : Blo 1653526 1860349 := bbase (se 3 (by rfl) ⟨348815, by rfl⟩ : syracuseStep 1860349 = 697631) (by norm_num)
theorem B2482949 : Blo 1653526 2482949 := bbase (se 4 (by rfl) ⟨232776, by rfl⟩ : syracuseStep 2482949 = 465553) (by norm_num)
theorem B2482973 : Blo 1653526 2482973 := bbase (se 3 (by rfl) ⟨465557, by rfl⟩ : syracuseStep 2482973 = 931115) (by norm_num)
theorem B1860385 : Blo 1653526 1860385 := bbase (se 2 (by rfl) ⟨697644, by rfl⟩ : syracuseStep 1860385 = 1395289) (by norm_num)
theorem B2482997 : Blo 1653526 2482997 := bbase (se 5 (by rfl) ⟨116390, by rfl⟩ : syracuseStep 2482997 = 232781) (by norm_num)
theorem B1860421 : Blo 1653526 1860421 := bbase (se 4 (by rfl) ⟨174414, by rfl⟩ : syracuseStep 1860421 = 348829) (by norm_num)
theorem B6284101 : Blo 1653526 6284101 := bbase (se 4 (by rfl) ⟨589134, by rfl⟩ : syracuseStep 6284101 = 1178269) (by norm_num)
theorem B2982725 : Blo 1653526 2982725 := bbase (se 4 (by rfl) ⟨279630, by rfl⟩ : syracuseStep 2982725 = 559261) (by norm_num)
theorem B2483021 : Blo 1653526 2483021 := bbase (se 3 (by rfl) ⟨465566, by rfl⟩ : syracuseStep 2483021 = 931133) (by norm_num)
theorem B3531613 : Blo 1653526 3531613 := bbase (se 3 (by rfl) ⟨662177, by rfl⟩ : syracuseStep 3531613 = 1324355) (by norm_num)
theorem B2483045 : Blo 1653526 2483045 := bbase (se 4 (by rfl) ⟨232785, by rfl⟩ : syracuseStep 2483045 = 465571) (by norm_num)
theorem B1860457 : Blo 1653526 1860457 := bbase (se 2 (by rfl) ⟨697671, by rfl⟩ : syracuseStep 1860457 = 1395343) (by norm_num)
theorem B2483069 : Blo 1653526 2483069 := bbase (se 3 (by rfl) ⟨465575, by rfl⟩ : syracuseStep 2483069 = 931151) (by norm_num)
theorem B1860493 : Blo 1653526 1860493 := bbase (se 3 (by rfl) ⟨348842, by rfl⟩ : syracuseStep 1860493 = 697685) (by norm_num)
theorem B4776853 : Blo 1653526 4776853 := bbase (se 6 (by rfl) ⟨111957, by rfl⟩ : syracuseStep 4776853 = 223915) (by norm_num)
theorem B2483093 : Blo 1653526 2483093 := bbase (se 6 (by rfl) ⟨58197, by rfl⟩ : syracuseStep 2483093 = 116395) (by norm_num)
theorem B2483117 : Blo 1653526 2483117 := bbase (se 3 (by rfl) ⟨465584, by rfl⟩ : syracuseStep 2483117 = 931169) (by norm_num)
theorem B1860529 : Blo 1653526 1860529 := bbase (se 2 (by rfl) ⟨697698, by rfl⟩ : syracuseStep 1860529 = 1395397) (by norm_num)
theorem B2483141 : Blo 1653526 2483141 := bbase (se 4 (by rfl) ⟨232794, by rfl⟩ : syracuseStep 2483141 = 465589) (by norm_num)
theorem B1860565 : Blo 1653526 1860565 := bbase (se 7 (by rfl) ⟨21803, by rfl⟩ : syracuseStep 1860565 = 43607) (by norm_num)
theorem B2483165 : Blo 1653526 2483165 := bbase (se 3 (by rfl) ⟨465593, by rfl⟩ : syracuseStep 2483165 = 931187) (by norm_num)
theorem B2483189 : Blo 1653526 2483189 := bbase (se 5 (by rfl) ⟨116399, by rfl⟩ : syracuseStep 2483189 = 232799) (by norm_num)
theorem B1860601 : Blo 1653526 1860601 := bbase (se 2 (by rfl) ⟨697725, by rfl⟩ : syracuseStep 1860601 = 1395451) (by norm_num)
theorem B2483213 : Blo 1653526 2483213 := bbase (se 3 (by rfl) ⟨465602, by rfl⟩ : syracuseStep 2483213 = 931205) (by norm_num)
theorem B1860637 : Blo 1653526 1860637 := bbase (se 3 (by rfl) ⟨348869, by rfl⟩ : syracuseStep 1860637 = 697739) (by norm_num)
theorem B4187173 : Blo 1653526 4187173 := bbase (se 4 (by rfl) ⟨392547, by rfl⟩ : syracuseStep 4187173 = 785095) (by norm_num)
theorem B2483237 : Blo 1653526 2483237 := bbase (se 4 (by rfl) ⟨232803, by rfl⟩ : syracuseStep 2483237 = 465607) (by norm_num)
theorem B3974189 : Blo 1653526 3974189 := bbase (se 3 (by rfl) ⟨745160, by rfl⟩ : syracuseStep 3974189 = 1490321) (by norm_num)
theorem B2483261 : Blo 1653526 2483261 := bbase (se 3 (by rfl) ⟨465611, by rfl⟩ : syracuseStep 2483261 = 931223) (by norm_num)
theorem B1860673 : Blo 1653526 1860673 := bbase (se 2 (by rfl) ⟨697752, by rfl⟩ : syracuseStep 1860673 = 1395505) (by norm_num)
theorem B8946773 : Blo 1653526 8946773 := bbase (se 8 (by rfl) ⟨52422, by rfl⟩ : syracuseStep 8946773 = 104845) (by norm_num)
theorem B2483285 : Blo 1653526 2483285 := bbase (se 8 (by rfl) ⟨14550, by rfl⟩ : syracuseStep 2483285 = 29101) (by norm_num)
theorem B1860709 : Blo 1653526 1860709 := bbase (se 4 (by rfl) ⟨174441, by rfl⟩ : syracuseStep 1860709 = 348883) (by norm_num)
theorem B5031013 : Blo 1653526 5031013 := bbase (se 4 (by rfl) ⟨471657, by rfl⟩ : syracuseStep 5031013 = 943315) (by norm_num)
theorem B6284405 : Blo 1653526 6284405 := bbase (se 5 (by rfl) ⟨294581, by rfl⟩ : syracuseStep 6284405 = 589163) (by norm_num)
theorem B1860745 : Blo 1653526 1860745 := bbase (se 2 (by rfl) ⟨697779, by rfl⟩ : syracuseStep 1860745 = 1395559) (by norm_num)
theorem B4187285 : Blo 1653526 4187285 := bbase (se 6 (by rfl) ⟨98139, by rfl⟩ : syracuseStep 4187285 = 196279) (by norm_num)
theorem B1860781 : Blo 1653526 1860781 := bbase (se 3 (by rfl) ⟨348896, by rfl⟩ : syracuseStep 1860781 = 697793) (by norm_num)
theorem B1860817 : Blo 1653526 1860817 := bbase (se 2 (by rfl) ⟨697806, by rfl⟩ : syracuseStep 1860817 = 1395613) (by norm_num)
theorem B3720437 : Blo 1653526 3720437 := bbase (se 5 (by rfl) ⟨174395, by rfl⟩ : syracuseStep 3720437 = 348791) (by norm_num)
theorem B1860853 : Blo 1653526 1860853 := bbase (se 5 (by rfl) ⟨87227, by rfl⟩ : syracuseStep 1860853 = 174455) (by norm_num)
theorem B2123029 : Blo 1653526 2123029 := bbase (se 6 (by rfl) ⟨49758, by rfl⟩ : syracuseStep 2123029 = 99517) (by norm_num)
theorem B1860889 : Blo 1653526 1860889 := bbase (se 2 (by rfl) ⟨697833, by rfl⟩ : syracuseStep 1860889 = 1395667) (by norm_num)
theorem B3974429 : Blo 1653526 3974429 := bbase (se 3 (by rfl) ⟨745205, by rfl⟩ : syracuseStep 3974429 = 1490411) (by norm_num)
theorem B4711733 : Blo 1653526 4711733 := bbase (se 5 (by rfl) ⟨220862, by rfl⟩ : syracuseStep 4711733 = 441725) (by norm_num)
theorem B3720509 : Blo 1653526 3720509 := bbase (se 3 (by rfl) ⟨697595, by rfl⟩ : syracuseStep 3720509 = 1395191) (by norm_num)
theorem B1860925 : Blo 1653526 1860925 := bbase (se 3 (by rfl) ⟨348923, by rfl⟩ : syracuseStep 1860925 = 697847) (by norm_num)
theorem B2516285 : Blo 1653526 2516285 := bbase (se 3 (by rfl) ⟨471803, by rfl⟩ : syracuseStep 2516285 = 943607) (by norm_num)
theorem B6710597 : Blo 1653526 6710597 := bbase (se 4 (by rfl) ⟨629118, by rfl⟩ : syracuseStep 6710597 = 1258237) (by norm_num)
theorem B4187477 : Blo 1653526 4187477 := bbase (se 12 (by rfl) ⟨1533, by rfl⟩ : syracuseStep 4187477 = 3067) (by norm_num)
theorem B12739925 : Blo 1653526 12739925 := bbase (se 12 (by rfl) ⟨4665, by rfl⟩ : syracuseStep 12739925 = 9331) (by norm_num)
theorem B1860961 : Blo 1653526 1860961 := bbase (se 2 (by rfl) ⟨697860, by rfl⟩ : syracuseStep 1860961 = 1395721) (by norm_num)
theorem B3720581 : Blo 1653526 3720581 := bbase (se 4 (by rfl) ⟨348804, by rfl⟩ : syracuseStep 3720581 = 697609) (by norm_num)
theorem B1860997 : Blo 1653526 1860997 := bbase (se 4 (by rfl) ⟨174468, by rfl⟩ : syracuseStep 1860997 = 348937) (by norm_num)
theorem B1885609 : Blo 1653526 1885609 := bbase (se 2 (by rfl) ⟨707103, by rfl⟩ : syracuseStep 1885609 = 1414207) (by norm_num)
theorem B1861033 : Blo 1653526 1861033 := bbase (se 2 (by rfl) ⟨697887, by rfl⟩ : syracuseStep 1861033 = 1395775) (by norm_num)
theorem B3720653 : Blo 1653526 3720653 := bbase (se 3 (by rfl) ⟨697622, by rfl⟩ : syracuseStep 3720653 = 1395245) (by norm_num)
theorem B1861069 : Blo 1653526 1861069 := bbase (se 3 (by rfl) ⟨348950, by rfl⟩ : syracuseStep 1861069 = 697901) (by norm_num)
theorem B1861105 : Blo 1653526 1861105 := bbase (se 2 (by rfl) ⟨697914, by rfl⟩ : syracuseStep 1861105 = 1395829) (by norm_num)
theorem B3720725 : Blo 1653526 3720725 := bbase (se 6 (by rfl) ⟨87204, by rfl⟩ : syracuseStep 3720725 = 174409) (by norm_num)
theorem B1861141 : Blo 1653526 1861141 := bbase (se 6 (by rfl) ⟨43620, by rfl⟩ : syracuseStep 1861141 = 87241) (by norm_num)
theorem B1861177 : Blo 1653526 1861177 := bbase (se 2 (by rfl) ⟨697941, by rfl⟩ : syracuseStep 1861177 = 1395883) (by norm_num)
theorem B3139165 : Blo 1653526 3139165 := bbase (se 3 (by rfl) ⟨588593, by rfl⟩ : syracuseStep 3139165 = 1177187) (by norm_num)
theorem B3720797 : Blo 1653526 3720797 := bbase (se 3 (by rfl) ⟨697649, by rfl⟩ : syracuseStep 3720797 = 1395299) (by norm_num)
theorem B1861213 : Blo 1653526 1861213 := bbase (se 3 (by rfl) ⟨348977, by rfl⟩ : syracuseStep 1861213 = 697955) (by norm_num)
theorem B1861249 : Blo 1653526 1861249 := bbase (se 2 (by rfl) ⟨697968, by rfl⟩ : syracuseStep 1861249 = 1395937) (by norm_num)
theorem B3720869 : Blo 1653526 3720869 := bbase (se 4 (by rfl) ⟨348831, by rfl⟩ : syracuseStep 3720869 = 697663) (by norm_num)
theorem B1861285 : Blo 1653526 1861285 := bbase (se 4 (by rfl) ⟨174495, by rfl⟩ : syracuseStep 1861285 = 348991) (by norm_num)
theorem B4187821 : Blo 1653526 4187821 := bbase (se 3 (by rfl) ⟨785216, by rfl⟩ : syracuseStep 4187821 = 1570433) (by norm_num)
theorem B8373941 : Blo 1653526 8373941 := bbase (se 5 (by rfl) ⟨392528, by rfl⟩ : syracuseStep 8373941 = 785057) (by norm_num)
theorem B1861321 : Blo 1653526 1861321 := bbase (se 2 (by rfl) ⟨697995, by rfl⟩ : syracuseStep 1861321 = 1395991) (by norm_num)
theorem B3532501 : Blo 1653526 3532501 := bbase (se 7 (by rfl) ⟨41396, by rfl⟩ : syracuseStep 3532501 = 82793) (by norm_num)
theorem B2041573 : Blo 1653526 2041573 := bbase (se 4 (by rfl) ⟨191397, by rfl⟩ : syracuseStep 2041573 = 382795) (by norm_num)
theorem B4712165 : Blo 1653526 4712165 := bbase (se 4 (by rfl) ⟨441765, by rfl⟩ : syracuseStep 4712165 = 883531) (by norm_num)
theorem B4474597 : Blo 1653526 4474597 := bbase (se 4 (by rfl) ⟨419493, by rfl⟩ : syracuseStep 4474597 = 838987) (by norm_num)
theorem B7071461 : Blo 1653526 7071461 := bbase (se 4 (by rfl) ⟨662949, by rfl⟩ : syracuseStep 7071461 = 1325899) (by norm_num)
theorem B3720941 : Blo 1653526 3720941 := bbase (se 3 (by rfl) ⟨697676, by rfl⟩ : syracuseStep 3720941 = 1395353) (by norm_num)
theorem B1861357 : Blo 1653526 1861357 := bbase (se 3 (by rfl) ⟨349004, by rfl⟩ : syracuseStep 1861357 = 698009) (by norm_num)
theorem B1861393 : Blo 1653526 1861393 := bbase (se 2 (by rfl) ⟨698022, by rfl⟩ : syracuseStep 1861393 = 1396045) (by norm_num)
theorem B4187933 : Blo 1653526 4187933 := bbase (se 3 (by rfl) ⟨785237, by rfl⟩ : syracuseStep 4187933 = 1570475) (by norm_num)
theorem B3721013 : Blo 1653526 3721013 := bbase (se 5 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 3721013 = 348845) (by norm_num)
theorem B1861429 : Blo 1653526 1861429 := bbase (se 5 (by rfl) ⟨87254, by rfl⟩ : syracuseStep 1861429 = 174509) (by norm_num)
theorem B1861465 : Blo 1653526 1861465 := bbase (se 2 (by rfl) ⟨698049, by rfl⟩ : syracuseStep 1861465 = 1396099) (by norm_num)
theorem B11921269 : Blo 1653526 11921269 := bbase (se 5 (by rfl) ⟨558809, by rfl⟩ : syracuseStep 11921269 = 1117619) (by norm_num)
theorem B3721085 : Blo 1653526 3721085 := bbase (se 3 (by rfl) ⟨697703, by rfl⟩ : syracuseStep 3721085 = 1395407) (by norm_num)
theorem B1861501 : Blo 1653526 1861501 := bbase (se 3 (by rfl) ⟨349031, by rfl⟩ : syracuseStep 1861501 = 698063) (by norm_num)
theorem B3139469 : Blo 1653526 3139469 := bbase (se 3 (by rfl) ⟨588650, by rfl⟩ : syracuseStep 3139469 = 1177301) (by norm_num)
theorem B1861537 : Blo 1653526 1861537 := bbase (se 2 (by rfl) ⟨698076, by rfl⟩ : syracuseStep 1861537 = 1396153) (by norm_num)
theorem B3721157 : Blo 1653526 3721157 := bbase (se 4 (by rfl) ⟨348858, by rfl⟩ : syracuseStep 3721157 = 697717) (by norm_num)
theorem B1861573 : Blo 1653526 1861573 := bbase (se 4 (by rfl) ⟨174522, by rfl⟩ : syracuseStep 1861573 = 349045) (by norm_num)
theorem B4188125 : Blo 1653526 4188125 := bbase (se 3 (by rfl) ⟨785273, by rfl⟩ : syracuseStep 4188125 = 1570547) (by norm_num)
theorem B1861609 : Blo 1653526 1861609 := bbase (se 2 (by rfl) ⟨698103, by rfl⟩ : syracuseStep 1861609 = 1396207) (by norm_num)
theorem B3721229 : Blo 1653526 3721229 := bbase (se 3 (by rfl) ⟨697730, by rfl⟩ : syracuseStep 3721229 = 1395461) (by norm_num)
theorem B1861645 : Blo 1653526 1861645 := bbase (se 3 (by rfl) ⟨349058, by rfl⟩ : syracuseStep 1861645 = 698117) (by norm_num)
theorem B6801445 : Blo 1653526 6801445 := bbase (se 4 (by rfl) ⟨637635, by rfl⟩ : syracuseStep 6801445 = 1275271) (by norm_num)
theorem B1861681 : Blo 1653526 1861681 := bbase (se 2 (by rfl) ⟨698130, by rfl⟩ : syracuseStep 1861681 = 1396261) (by norm_num)
theorem B3721301 : Blo 1653526 3721301 := bbase (se 8 (by rfl) ⟨21804, by rfl⟩ : syracuseStep 3721301 = 43609) (by norm_num)
theorem B1861717 : Blo 1653526 1861717 := bbase (se 8 (by rfl) ⟨10908, by rfl⟩ : syracuseStep 1861717 = 21817) (by norm_num)
theorem B5032037 : Blo 1653526 5032037 := bbase (se 4 (by rfl) ⟨471753, by rfl⟩ : syracuseStep 5032037 = 943507) (by norm_num)
theorem B1861753 : Blo 1653526 1861753 := bbase (se 2 (by rfl) ⟨698157, by rfl⟩ : syracuseStep 1861753 = 1396315) (by norm_num)
theorem B3721373 : Blo 1653526 3721373 := bbase (se 3 (by rfl) ⟨697757, by rfl⟩ : syracuseStep 3721373 = 1395515) (by norm_num)
theorem B1861789 : Blo 1653526 1861789 := bbase (se 3 (by rfl) ⟨349085, by rfl⟩ : syracuseStep 1861789 = 698171) (by norm_num)
theorem B1861825 : Blo 1653526 1861825 := bbase (se 2 (by rfl) ⟨698184, by rfl⟩ : syracuseStep 1861825 = 1396369) (by norm_num)
theorem B3532997 : Blo 1653526 3532997 := bbase (se 4 (by rfl) ⟨331218, by rfl⟩ : syracuseStep 3532997 = 662437) (by norm_num)
theorem B3721445 : Blo 1653526 3721445 := bbase (se 4 (by rfl) ⟨348885, by rfl⟩ : syracuseStep 3721445 = 697771) (by norm_num)
theorem B1861861 : Blo 1653526 1861861 := bbase (se 4 (by rfl) ⟨174549, by rfl⟩ : syracuseStep 1861861 = 349099) (by norm_num)
theorem B5032181 : Blo 1653526 5032181 := bbase (se 5 (by rfl) ⟨235883, by rfl⟩ : syracuseStep 5032181 = 471767) (by norm_num)
theorem B5581061 : Blo 1653526 5581061 := bbase (se 4 (by rfl) ⟨523224, by rfl⟩ : syracuseStep 5581061 = 1046449) (by norm_num)
theorem B1861897 : Blo 1653526 1861897 := bbase (se 2 (by rfl) ⟨698211, by rfl⟩ : syracuseStep 1861897 = 1396423) (by norm_num)
theorem B3721517 : Blo 1653526 3721517 := bbase (se 3 (by rfl) ⟨697784, by rfl⟩ : syracuseStep 3721517 = 1395569) (by norm_num)
theorem B1861933 : Blo 1653526 1861933 := bbase (se 3 (by rfl) ⟨349112, by rfl⟩ : syracuseStep 1861933 = 698225) (by norm_num)
theorem B4188469 : Blo 1653526 4188469 := bbase (se 5 (by rfl) ⟨196334, by rfl⟩ : syracuseStep 4188469 = 392669) (by norm_num)
theorem B1861969 : Blo 1653526 1861969 := bbase (se 2 (by rfl) ⟨698238, by rfl⟩ : syracuseStep 1861969 = 1396477) (by norm_num)
theorem B3721589 : Blo 1653526 3721589 := bbase (se 5 (by rfl) ⟨174449, by rfl⟩ : syracuseStep 3721589 = 348899) (by norm_num)
theorem B1862005 : Blo 1653526 1862005 := bbase (se 5 (by rfl) ⟨87281, by rfl⟩ : syracuseStep 1862005 = 174563) (by norm_num)
theorem B1862041 : Blo 1653526 1862041 := bbase (se 2 (by rfl) ⟨698265, by rfl⟩ : syracuseStep 1862041 = 1396531) (by norm_num)
theorem B4188581 : Blo 1653526 4188581 := bbase (se 4 (by rfl) ⟨392679, by rfl⟩ : syracuseStep 4188581 = 785359) (by norm_num)
theorem B3721661 : Blo 1653526 3721661 := bbase (se 3 (by rfl) ⟨697811, by rfl⟩ : syracuseStep 3721661 = 1395623) (by norm_num)
theorem B1862077 : Blo 1653526 1862077 := bbase (se 3 (by rfl) ⟨349139, by rfl⟩ : syracuseStep 1862077 = 698279) (by norm_num)
theorem B4712917 : Blo 1653526 4712917 := bbase (se 7 (by rfl) ⟨55229, by rfl⟩ : syracuseStep 4712917 = 110459) (by norm_num)
theorem B1862113 : Blo 1653526 1862113 := bbase (se 2 (by rfl) ⟨698292, by rfl⟩ : syracuseStep 1862113 = 1396585) (by norm_num)
theorem B3721733 : Blo 1653526 3721733 := bbase (se 4 (by rfl) ⟨348912, by rfl⟩ : syracuseStep 3721733 = 697825) (by norm_num)
theorem B1862149 : Blo 1653526 1862149 := bbase (se 4 (by rfl) ⟨174576, by rfl⟩ : syracuseStep 1862149 = 349153) (by norm_num)
theorem B1862185 : Blo 1653526 1862185 := bbase (se 2 (by rfl) ⟨698319, by rfl⟩ : syracuseStep 1862185 = 1396639) (by norm_num)
theorem B5302853 : Blo 1653526 5302853 := bbase (se 4 (by rfl) ⟨497142, by rfl⟩ : syracuseStep 5302853 = 994285) (by norm_num)
theorem B3353165 : Blo 1653526 3353165 := bbase (se 3 (by rfl) ⟨628718, by rfl⟩ : syracuseStep 3353165 = 1257437) (by norm_num)
theorem B3721805 : Blo 1653526 3721805 := bbase (se 3 (by rfl) ⟨697838, by rfl⟩ : syracuseStep 3721805 = 1395677) (by norm_num)
theorem B1862221 : Blo 1653526 1862221 := bbase (se 3 (by rfl) ⟨349166, by rfl⟩ : syracuseStep 1862221 = 698333) (by norm_num)
theorem B4188773 : Blo 1653526 4188773 := bbase (se 4 (by rfl) ⟨392697, by rfl⟩ : syracuseStep 4188773 = 785395) (by norm_num)
theorem B1862257 : Blo 1653526 1862257 := bbase (se 2 (by rfl) ⟨698346, by rfl⟩ : syracuseStep 1862257 = 1396693) (by norm_num)
theorem B3140221 : Blo 1653526 3140221 := bbase (se 3 (by rfl) ⟨588791, by rfl⟩ : syracuseStep 3140221 = 1177583) (by norm_num)
theorem B3721877 : Blo 1653526 3721877 := bbase (se 6 (by rfl) ⟨87231, by rfl⟩ : syracuseStep 3721877 = 174463) (by norm_num)
theorem B1862293 : Blo 1653526 1862293 := bbase (se 6 (by rfl) ⟨43647, by rfl⟩ : syracuseStep 1862293 = 87295) (by norm_num)
theorem B5581493 : Blo 1653526 5581493 := bbase (se 5 (by rfl) ⟨261632, by rfl⟩ : syracuseStep 5581493 = 523265) (by norm_num)
theorem B1862329 : Blo 1653526 1862329 := bbase (se 2 (by rfl) ⟨698373, by rfl⟩ : syracuseStep 1862329 = 1396747) (by norm_num)
theorem B15895253 : Blo 1653526 15895253 := bbase (se 7 (by rfl) ⟨186272, by rfl⟩ : syracuseStep 15895253 = 372545) (by norm_num)
theorem B3721949 : Blo 1653526 3721949 := bbase (se 3 (by rfl) ⟨697865, by rfl⟩ : syracuseStep 3721949 = 1395731) (by norm_num)
theorem B1862365 : Blo 1653526 1862365 := bbase (se 3 (by rfl) ⟨349193, by rfl⟩ : syracuseStep 1862365 = 698387) (by norm_num)
theorem B4246253 : Blo 1653526 4246253 := bbase (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) (by norm_num)
theorem B1862401 : Blo 1653526 1862401 := bbase (se 2 (by rfl) ⟨698400, by rfl⟩ : syracuseStep 1862401 = 1396801) (by norm_num)
theorem B3140365 : Blo 1653526 3140365 := bbase (se 3 (by rfl) ⟨588818, by rfl⟩ : syracuseStep 3140365 = 1177637) (by norm_num)
theorem B3722021 : Blo 1653526 3722021 := bbase (se 4 (by rfl) ⟨348939, by rfl⟩ : syracuseStep 3722021 = 697879) (by norm_num)
theorem B1862437 : Blo 1653526 1862437 := bbase (se 4 (by rfl) ⟨174603, by rfl⟩ : syracuseStep 1862437 = 349207) (by norm_num)
theorem B7064405 : Blo 1653526 7064405 := bbase (se 9 (by rfl) ⟨20696, by rfl⟩ : syracuseStep 7064405 = 41393) (by norm_num)
theorem B3722093 : Blo 1653526 3722093 := bbase (se 3 (by rfl) ⟨697892, by rfl⟩ : syracuseStep 3722093 = 1395785) (by norm_num)
theorem B4533157 : Blo 1653526 4533157 := bbase (se 4 (by rfl) ⟨424983, by rfl⟩ : syracuseStep 4533157 = 849967) (by norm_num)
theorem B3140525 : Blo 1653526 3140525 := bbase (se 3 (by rfl) ⟨588848, by rfl⟩ : syracuseStep 3140525 = 1177697) (by norm_num)
theorem B3722165 : Blo 1653526 3722165 := bbase (se 5 (by rfl) ⟨174476, by rfl⟩ : syracuseStep 3722165 = 348953) (by norm_num)
theorem B4189117 : Blo 1653526 4189117 := bbase (se 3 (by rfl) ⟨785459, by rfl⟩ : syracuseStep 4189117 = 1570919) (by norm_num)
theorem B8375237 : Blo 1653526 8375237 := bbase (se 4 (by rfl) ⟨785178, by rfl⟩ : syracuseStep 8375237 = 1570357) (by norm_num)
theorem B3976141 : Blo 1653526 3976141 := bbase (se 3 (by rfl) ⟨745526, by rfl⟩ : syracuseStep 3976141 = 1491053) (by norm_num)
theorem B9428021 : Blo 1653526 9428021 := bbase (se 5 (by rfl) ⟨441938, by rfl⟩ : syracuseStep 9428021 = 883877) (by norm_num)
theorem B3722237 : Blo 1653526 3722237 := bbase (se 3 (by rfl) ⟨697919, by rfl⟩ : syracuseStep 3722237 = 1395839) (by norm_num)
theorem B4189229 : Blo 1653526 4189229 := bbase (se 3 (by rfl) ⟨785480, by rfl⟩ : syracuseStep 4189229 = 1570961) (by norm_num)
theorem B3140669 : Blo 1653526 3140669 := bbase (se 3 (by rfl) ⟨588875, by rfl⟩ : syracuseStep 3140669 = 1177751) (by norm_num)
theorem B3533885 : Blo 1653526 3533885 := bbase (se 3 (by rfl) ⟨662603, by rfl⟩ : syracuseStep 3533885 = 1325207) (by norm_num)
theorem B3722309 : Blo 1653526 3722309 := bbase (se 4 (by rfl) ⟨348966, by rfl⟩ : syracuseStep 3722309 = 697933) (by norm_num)
theorem B1887305 : Blo 1653526 1887305 := bbase (se 2 (by rfl) ⟨707739, by rfl⟩ : syracuseStep 1887305 = 1415479) (by norm_num)
theorem B5581925 : Blo 1653526 5581925 := bbase (se 4 (by rfl) ⟨523305, by rfl⟩ : syracuseStep 5581925 = 1046611) (by norm_num)
theorem B3722381 : Blo 1653526 3722381 := bbase (se 3 (by rfl) ⟨697946, by rfl⟩ : syracuseStep 3722381 = 1395893) (by norm_num)
theorem B3534005 : Blo 1653526 3534005 := bbase (se 5 (by rfl) ⟨165656, by rfl⟩ : syracuseStep 3534005 = 331313) (by norm_num)
theorem B3722453 : Blo 1653526 3722453 := bbase (se 7 (by rfl) ⟨43622, by rfl⟩ : syracuseStep 3722453 = 87245) (by norm_num)
theorem B6368485 : Blo 1653526 6368485 := bbase (se 4 (by rfl) ⟨597045, by rfl⟩ : syracuseStep 6368485 = 1194091) (by norm_num)
theorem B4189421 : Blo 1653526 4189421 := bbase (se 3 (by rfl) ⟨785516, by rfl⟩ : syracuseStep 4189421 = 1571033) (by norm_num)
theorem B2354437 : Blo 1653526 2354437 := bbase (se 4 (by rfl) ⟨220728, by rfl⟩ : syracuseStep 2354437 = 441457) (by norm_num)
theorem B10595605 : Blo 1653526 10595605 := bbase (se 6 (by rfl) ⟨248334, by rfl⟩ : syracuseStep 10595605 = 496669) (by norm_num)
theorem B3722525 : Blo 1653526 3722525 := bbase (se 3 (by rfl) ⟨697973, by rfl⟩ : syracuseStep 3722525 = 1395947) (by norm_num)
theorem B3140957 : Blo 1653526 3140957 := bbase (se 3 (by rfl) ⟨588929, by rfl⟩ : syracuseStep 3140957 = 1177859) (by norm_num)
theorem B3722597 : Blo 1653526 3722597 := bbase (se 4 (by rfl) ⟨348993, by rfl⟩ : syracuseStep 3722597 = 697987) (by norm_num)
theorem B3722669 : Blo 1653526 3722669 := bbase (se 3 (by rfl) ⟨698000, by rfl⟩ : syracuseStep 3722669 = 1396001) (by norm_num)
theorem B3722741 : Blo 1653526 3722741 := bbase (se 5 (by rfl) ⟨174503, by rfl⟩ : syracuseStep 3722741 = 349007) (by norm_num)
theorem B3141109 : Blo 1653526 3141109 := bbase (se 5 (by rfl) ⟨147239, by rfl⟩ : syracuseStep 3141109 = 294479) (by norm_num)
theorem B2043389 : Blo 1653526 2043389 := bbase (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) (by norm_num)
theorem B5582357 : Blo 1653526 5582357 := bbase (se 6 (by rfl) ⟨130836, by rfl⟩ : syracuseStep 5582357 = 261673) (by norm_num)
theorem B18853397 : Blo 1653526 18853397 := bbase (se 6 (by rfl) ⟨441876, by rfl⟩ : syracuseStep 18853397 = 883753) (by norm_num)
theorem B3722813 : Blo 1653526 3722813 := bbase (se 3 (by rfl) ⟨698027, by rfl⟩ : syracuseStep 3722813 = 1396055) (by norm_num)
theorem B4189765 : Blo 1653526 4189765 := bbase (se 4 (by rfl) ⟨392790, by rfl⟩ : syracuseStep 4189765 = 785581) (by norm_num)
theorem B6278741 : Blo 1653526 6278741 := bbase (se 8 (by rfl) ⟨36789, by rfl⟩ : syracuseStep 6278741 = 73579) (by norm_num)
theorem B2354773 : Blo 1653526 2354773 := bbase (se 8 (by rfl) ⟨13797, by rfl⟩ : syracuseStep 2354773 = 27595) (by norm_num)
theorem B3722885 : Blo 1653526 3722885 := bbase (se 4 (by rfl) ⟨349020, by rfl⟩ : syracuseStep 3722885 = 698041) (by norm_num)
theorem B2649773 : Blo 1653526 2649773 := bbase (se 3 (by rfl) ⟨496832, by rfl⟩ : syracuseStep 2649773 = 993665) (by norm_num)
theorem B4189877 : Blo 1653526 4189877 := bbase (se 5 (by rfl) ⟨196400, by rfl⟩ : syracuseStep 4189877 = 392801) (by norm_num)
theorem B3722957 : Blo 1653526 3722957 := bbase (se 3 (by rfl) ⟨698054, by rfl⟩ : syracuseStep 3722957 = 1396109) (by norm_num)
theorem B2092817 : Blo 1653526 2092817 := bbase (se 2 (by rfl) ⟨784806, by rfl⟩ : syracuseStep 2092817 = 1569613) (by norm_num)
theorem B3723029 : Blo 1653526 3723029 := bbase (se 6 (by rfl) ⟨87258, by rfl⟩ : syracuseStep 3723029 = 174517) (by norm_num)
theorem B12570389 : Blo 1653526 12570389 := bbase (se 6 (by rfl) ⟨294618, by rfl⟩ : syracuseStep 12570389 = 589237) (by norm_num)
theorem B3141413 : Blo 1653526 3141413 := bbase (se 4 (by rfl) ⟨294507, by rfl⟩ : syracuseStep 3141413 = 589015) (by norm_num)
theorem B2354989 : Blo 1653526 2354989 := bbase (se 3 (by rfl) ⟨441560, by rfl⟩ : syracuseStep 2354989 = 883121) (by norm_num)
theorem B3534637 : Blo 1653526 3534637 := bbase (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) (by norm_num)
theorem B7065413 : Blo 1653526 7065413 := bbase (se 4 (by rfl) ⟨662382, by rfl⟩ : syracuseStep 7065413 = 1324765) (by norm_num)
theorem B2092873 : Blo 1653526 2092873 := bbase (se 2 (by rfl) ⟨784827, by rfl⟩ : syracuseStep 2092873 = 1569655) (by norm_num)
theorem B3723101 : Blo 1653526 3723101 := bbase (se 3 (by rfl) ⟨698081, by rfl⟩ : syracuseStep 3723101 = 1396163) (by norm_num)
theorem B6279029 : Blo 1653526 6279029 := bbase (se 5 (by rfl) ⟨294329, by rfl⟩ : syracuseStep 6279029 = 588659) (by norm_num)
theorem B4190069 : Blo 1653526 4190069 := bbase (se 5 (by rfl) ⟨196409, by rfl⟩ : syracuseStep 4190069 = 392819) (by norm_num)
theorem B3723173 : Blo 1653526 3723173 := bbase (se 4 (by rfl) ⟨349047, by rfl⟩ : syracuseStep 3723173 = 698095) (by norm_num)
theorem B2092969 : Blo 1653526 2092969 := bbase (se 2 (by rfl) ⟨784863, by rfl⟩ : syracuseStep 2092969 = 1569727) (by norm_num)
theorem B5582789 : Blo 1653526 5582789 := bbase (se 4 (by rfl) ⟨523386, by rfl⟩ : syracuseStep 5582789 = 1046773) (by norm_num)
theorem B22630357 : Blo 1653526 22630357 := bbase (se 7 (by rfl) ⟨265199, by rfl⟩ : syracuseStep 22630357 = 530399) (by norm_num)
theorem B6041573 : Blo 1653526 6041573 := bbase (se 4 (by rfl) ⟨566397, by rfl⟩ : syracuseStep 6041573 = 1132795) (by norm_num)
theorem B3723245 : Blo 1653526 3723245 := bbase (se 3 (by rfl) ⟨698108, by rfl⟩ : syracuseStep 3723245 = 1396217) (by norm_num)
theorem B3723317 : Blo 1653526 3723317 := bbase (se 5 (by rfl) ⟨174530, by rfl⟩ : syracuseStep 3723317 = 349061) (by norm_num)
theorem B2093141 : Blo 1653526 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B3682397 : Blo 1653526 3682397 := bbase (se 3 (by rfl) ⟨690449, by rfl⟩ : syracuseStep 3682397 = 1380899) (by norm_num)
theorem B2650229 : Blo 1653526 2650229 := bbase (se 5 (by rfl) ⟨124229, by rfl⟩ : syracuseStep 2650229 = 248459) (by norm_num)
theorem B3723389 : Blo 1653526 3723389 := bbase (se 3 (by rfl) ⟨698135, by rfl⟩ : syracuseStep 3723389 = 1396271) (by norm_num)
theorem B2093197 : Blo 1653526 2093197 := bbase (se 3 (by rfl) ⟨392474, by rfl⟩ : syracuseStep 2093197 = 784949) (by norm_num)
theorem B2355365 : Blo 1653526 2355365 := bbase (se 4 (by rfl) ⟨220815, by rfl⟩ : syracuseStep 2355365 = 441631) (by norm_num)
theorem B12562613 : Blo 1653526 12562613 := bbase (se 5 (by rfl) ⟨588872, by rfl⟩ : syracuseStep 12562613 = 1177745) (by norm_num)
theorem B3723461 : Blo 1653526 3723461 := bbase (se 4 (by rfl) ⟨349074, by rfl⟩ : syracuseStep 3723461 = 698149) (by norm_num)
theorem B4190413 : Blo 1653526 4190413 := bbase (se 3 (by rfl) ⟨785702, by rfl⟩ : syracuseStep 4190413 = 1571405) (by norm_num)
theorem B35778773 : Blo 1653526 35778773 := bbase (se 7 (by rfl) ⟨419282, by rfl⟩ : syracuseStep 35778773 = 838565) (by norm_num)
theorem B8376533 : Blo 1653526 8376533 := bbase (se 7 (by rfl) ⟨98162, by rfl⟩ : syracuseStep 8376533 = 196325) (by norm_num)
theorem B3354853 : Blo 1653526 3354853 := bbase (se 4 (by rfl) ⟨314517, by rfl⟩ : syracuseStep 3354853 = 629035) (by norm_num)
theorem B2093293 : Blo 1653526 2093293 := bbase (se 3 (by rfl) ⟨392492, by rfl⟩ : syracuseStep 2093293 = 784985) (by norm_num)
theorem B3723533 : Blo 1653526 3723533 := bbase (se 3 (by rfl) ⟨698162, by rfl⟩ : syracuseStep 3723533 = 1396325) (by norm_num)
theorem B4190525 : Blo 1653526 4190525 := bbase (se 3 (by rfl) ⟨785723, by rfl⟩ : syracuseStep 4190525 = 1571447) (by norm_num)
theorem B3723605 : Blo 1653526 3723605 := bbase (se 10 (by rfl) ⟨5454, by rfl⟩ : syracuseStep 3723605 = 10909) (by norm_num)
theorem B3977581 : Blo 1653526 3977581 := bbase (se 3 (by rfl) ⟨745796, by rfl⟩ : syracuseStep 3977581 = 1491593) (by norm_num)
theorem B5583221 : Blo 1653526 5583221 := bbase (se 5 (by rfl) ⟨261713, by rfl⟩ : syracuseStep 5583221 = 523427) (by norm_num)
theorem B1986941 : Blo 1653526 1986941 := bbase (se 3 (by rfl) ⟨372551, by rfl⟩ : syracuseStep 1986941 = 745103) (by norm_num)
theorem B3182981 : Blo 1653526 3182981 := bbase (se 4 (by rfl) ⟨298404, by rfl⟩ : syracuseStep 3182981 = 596809) (by norm_num)
theorem B2093465 : Blo 1653526 2093465 := bbase (se 2 (by rfl) ⟨785049, by rfl⟩ : syracuseStep 2093465 = 1570099) (by norm_num)
theorem B3723677 : Blo 1653526 3723677 := bbase (se 3 (by rfl) ⟨698189, by rfl⟩ : syracuseStep 3723677 = 1396379) (by norm_num)
theorem B2093521 : Blo 1653526 2093521 := bbase (se 2 (by rfl) ⟨785070, by rfl⟩ : syracuseStep 2093521 = 1570141) (by norm_num)
theorem B9818581 : Blo 1653526 9818581 := bbase (se 7 (by rfl) ⟨115061, by rfl⟩ : syracuseStep 9818581 = 230123) (by norm_num)
theorem B1765849 : Blo 1653526 1765849 := bbase (se 2 (by rfl) ⟨662193, by rfl⟩ : syracuseStep 1765849 = 1324387) (by norm_num)
theorem B3723749 : Blo 1653526 3723749 := bbase (se 4 (by rfl) ⟨349101, by rfl⟩ : syracuseStep 3723749 = 698203) (by norm_num)
theorem B1765909 : Blo 1653526 1765909 := bbase (se 6 (by rfl) ⟨41388, by rfl⟩ : syracuseStep 1765909 = 82777) (by norm_num)
theorem B12087829 : Blo 1653526 12087829 := bbase (se 6 (by rfl) ⟨283308, by rfl⟩ : syracuseStep 12087829 = 566617) (by norm_num)
theorem B3142165 : Blo 1653526 3142165 := bbase (se 6 (by rfl) ⟨73644, by rfl⟩ : syracuseStep 3142165 = 147289) (by norm_num)
theorem B3723821 : Blo 1653526 3723821 := bbase (se 3 (by rfl) ⟨698216, by rfl⟩ : syracuseStep 3723821 = 1396433) (by norm_num)
theorem B2093617 : Blo 1653526 2093617 := bbase (se 2 (by rfl) ⟨785106, by rfl⟩ : syracuseStep 2093617 = 1570213) (by norm_num)
theorem B13414997 : Blo 1653526 13414997 := bbase (se 8 (by rfl) ⟨78603, by rfl⟩ : syracuseStep 13414997 = 157207) (by norm_num)
theorem B3723893 : Blo 1653526 3723893 := bbase (se 5 (by rfl) ⟨174557, by rfl⟩ : syracuseStep 3723893 = 349115) (by norm_num)
theorem B3142309 : Blo 1653526 3142309 := bbase (se 4 (by rfl) ⟨294591, by rfl⟩ : syracuseStep 3142309 = 589183) (by norm_num)
theorem B3535525 : Blo 1653526 3535525 := bbase (se 4 (by rfl) ⟨331455, by rfl⟩ : syracuseStep 3535525 = 662911) (by norm_num)
theorem B1987249 : Blo 1653526 1987249 := bbase (se 2 (by rfl) ⟨745218, by rfl⟩ : syracuseStep 1987249 = 1490437) (by norm_num)
theorem B3723965 : Blo 1653526 3723965 := bbase (se 3 (by rfl) ⟨698243, by rfl⟩ : syracuseStep 3723965 = 1396487) (by norm_num)
theorem B2093789 : Blo 1653526 2093789 := bbase (se 3 (by rfl) ⟨392585, by rfl⟩ : syracuseStep 2093789 = 785171) (by norm_num)
theorem B3724037 : Blo 1653526 3724037 := bbase (se 4 (by rfl) ⟨349128, by rfl⟩ : syracuseStep 3724037 = 698257) (by norm_num)
theorem B1987349 : Blo 1653526 1987349 := bbase (se 6 (by rfl) ⟨46578, by rfl⟩ : syracuseStep 1987349 = 93157) (by norm_num)
theorem B2093845 : Blo 1653526 2093845 := bbase (se 6 (by rfl) ⟨49074, by rfl⟩ : syracuseStep 2093845 = 98149) (by norm_num)
theorem B3535645 : Blo 1653526 3535645 := bbase (se 3 (by rfl) ⟨662933, by rfl⟩ : syracuseStep 3535645 = 1325867) (by norm_num)
theorem B5583653 : Blo 1653526 5583653 := bbase (se 4 (by rfl) ⟨523467, by rfl⟩ : syracuseStep 5583653 = 1046935) (by norm_num)
theorem B4723525 : Blo 1653526 4723525 := bbase (se 4 (by rfl) ⟨442830, by rfl⟩ : syracuseStep 4723525 = 885661) (by norm_num)
theorem B3142469 : Blo 1653526 3142469 := bbase (se 4 (by rfl) ⟨294606, by rfl⟩ : syracuseStep 3142469 = 589213) (by norm_num)
theorem B3724109 : Blo 1653526 3724109 := bbase (se 3 (by rfl) ⟨698270, by rfl⟩ : syracuseStep 3724109 = 1396541) (by norm_num)
theorem B1766225 : Blo 1653526 1766225 := bbase (se 2 (by rfl) ⟨662334, by rfl⟩ : syracuseStep 1766225 = 1324669) (by norm_num)
theorem B2093941 : Blo 1653526 2093941 := bbase (se 5 (by rfl) ⟨98153, by rfl⟩ : syracuseStep 2093941 = 196307) (by norm_num)
theorem B3773333 : Blo 1653526 3773333 := bbase (se 6 (by rfl) ⟨88437, by rfl⟩ : syracuseStep 3773333 = 176875) (by norm_num)
theorem B3724181 : Blo 1653526 3724181 := bbase (se 6 (by rfl) ⟨87285, by rfl⟩ : syracuseStep 3724181 = 174571) (by norm_num)
theorem B3142613 : Blo 1653526 3142613 := bbase (se 7 (by rfl) ⟨36827, by rfl⟩ : syracuseStep 3142613 = 73655) (by norm_num)
theorem B3724253 : Blo 1653526 3724253 := bbase (se 3 (by rfl) ⟨698297, by rfl⟩ : syracuseStep 3724253 = 1396595) (by norm_num)
theorem B2790389 : Blo 1653526 2790389 := bbase (se 5 (by rfl) ⟨130799, by rfl⟩ : syracuseStep 2790389 = 261599) (by norm_num)
theorem B6280213 : Blo 1653526 6280213 := bbase (se 6 (by rfl) ⟨147192, by rfl⟩ : syracuseStep 6280213 = 294385) (by norm_num)
theorem B2094113 : Blo 1653526 2094113 := bbase (se 2 (by rfl) ⟨785292, by rfl⟩ : syracuseStep 2094113 = 1570585) (by norm_num)
theorem B3724325 : Blo 1653526 3724325 := bbase (se 4 (by rfl) ⟨349155, by rfl⟩ : syracuseStep 3724325 = 698311) (by norm_num)
theorem B1791041 : Blo 1653526 1791041 := bbase (se 2 (by rfl) ⟨671640, by rfl⟩ : syracuseStep 1791041 = 1343281) (by norm_num)
theorem B3822661 : Blo 1653526 3822661 := bbase (se 4 (by rfl) ⟨358374, by rfl⟩ : syracuseStep 3822661 = 716749) (by norm_num)
theorem B2241605 : Blo 1653526 2241605 := bbase (se 4 (by rfl) ⟨210150, by rfl⟩ : syracuseStep 2241605 = 420301) (by norm_num)
theorem B2651221 : Blo 1653526 2651221 := bbase (se 8 (by rfl) ⟨15534, by rfl⟩ : syracuseStep 2651221 = 31069) (by norm_num)
theorem B10605653 : Blo 1653526 10605653 := bbase (se 8 (by rfl) ⟨62142, by rfl⟩ : syracuseStep 10605653 = 124285) (by norm_num)
theorem B2094169 : Blo 1653526 2094169 := bbase (se 2 (by rfl) ⟨785313, by rfl⟩ : syracuseStep 2094169 = 1570627) (by norm_num)
theorem B5657701 : Blo 1653526 5657701 := bbase (se 4 (by rfl) ⟨530409, by rfl⟩ : syracuseStep 5657701 = 1060819) (by norm_num)
theorem B3724397 : Blo 1653526 3724397 := bbase (se 3 (by rfl) ⟨698324, by rfl⟩ : syracuseStep 3724397 = 1396649) (by norm_num)
theorem B2790517 : Blo 1653526 2790517 := bbase (se 5 (by rfl) ⟨130805, by rfl⟩ : syracuseStep 2790517 = 261611) (by norm_num)
theorem B1987753 : Blo 1653526 1987753 := bbase (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) (by norm_num)
theorem B3724469 : Blo 1653526 3724469 := bbase (se 5 (by rfl) ⟨174584, by rfl⟩ : syracuseStep 3724469 = 349169) (by norm_num)
theorem B2094265 : Blo 1653526 2094265 := bbase (se 2 (by rfl) ⟨785349, by rfl⟩ : syracuseStep 2094265 = 1570699) (by norm_num)
theorem B2790605 : Blo 1653526 2790605 := bbase (se 3 (by rfl) ⟨523238, by rfl⟩ : syracuseStep 2790605 = 1046477) (by norm_num)
theorem B5584085 : Blo 1653526 5584085 := bbase (se 7 (by rfl) ⟨65438, by rfl⟩ : syracuseStep 5584085 = 130877) (by norm_num)
theorem B3142901 : Blo 1653526 3142901 := bbase (se 5 (by rfl) ⟨147323, by rfl⟩ : syracuseStep 3142901 = 294647) (by norm_num)
theorem B3724541 : Blo 1653526 3724541 := bbase (se 3 (by rfl) ⟨698351, by rfl⟩ : syracuseStep 3724541 = 1396703) (by norm_num)
theorem B1766669 : Blo 1653526 1766669 := bbase (se 3 (by rfl) ⟨331250, by rfl⟩ : syracuseStep 1766669 = 662501) (by norm_num)
theorem B6280517 : Blo 1653526 6280517 := bbase (se 4 (by rfl) ⟨588798, by rfl⟩ : syracuseStep 6280517 = 1177597) (by norm_num)
theorem B3724613 : Blo 1653526 3724613 := bbase (se 4 (by rfl) ⟨349182, by rfl⟩ : syracuseStep 3724613 = 698365) (by norm_num)
theorem B1766729 : Blo 1653526 1766729 := bbase (se 2 (by rfl) ⟨662523, by rfl⟩ : syracuseStep 1766729 = 1325047) (by norm_num)
theorem B2790733 : Blo 1653526 2790733 := bbase (se 3 (by rfl) ⟨523262, by rfl⟩ : syracuseStep 2790733 = 1046525) (by norm_num)
theorem B33961301 : Blo 1653526 33961301 := bbase (se 13 (by rfl) ⟨6218, by rfl⟩ : syracuseStep 33961301 = 12437) (by norm_num)
theorem B2094437 : Blo 1653526 2094437 := bbase (se 4 (by rfl) ⟨196353, by rfl⟩ : syracuseStep 2094437 = 392707) (by norm_num)
theorem B3724685 : Blo 1653526 3724685 := bbase (se 3 (by rfl) ⟨698378, by rfl⟩ : syracuseStep 3724685 = 1396757) (by norm_num)
theorem B9418133 : Blo 1653526 9418133 := bbase (se 6 (by rfl) ⟨220737, by rfl⟩ : syracuseStep 9418133 = 441475) (by norm_num)
theorem B2094493 : Blo 1653526 2094493 := bbase (se 3 (by rfl) ⟨392717, by rfl⟩ : syracuseStep 2094493 = 785435) (by norm_num)
theorem B2487709 : Blo 1653526 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B2790821 : Blo 1653526 2790821 := bbase (se 4 (by rfl) ⟨261639, by rfl⟩ : syracuseStep 2790821 = 523279) (by norm_num)
theorem B3356077 : Blo 1653526 3356077 := bbase (se 3 (by rfl) ⟨629264, by rfl⟩ : syracuseStep 3356077 = 1258529) (by norm_num)
theorem B1766857 : Blo 1653526 1766857 := bbase (se 2 (by rfl) ⟨662571, by rfl⟩ : syracuseStep 1766857 = 1325143) (by norm_num)
theorem B3724757 : Blo 1653526 3724757 := bbase (se 7 (by rfl) ⟨43649, by rfl⟩ : syracuseStep 3724757 = 87299) (by norm_num)
theorem B8377829 : Blo 1653526 8377829 := bbase (se 4 (by rfl) ⟨785421, by rfl⟩ : syracuseStep 8377829 = 1570843) (by norm_num)
theorem B1676777 : Blo 1653526 1676777 := bbase (se 2 (by rfl) ⟨628791, by rfl⟩ : syracuseStep 1676777 = 1257583) (by norm_num)
theorem B15906293 : Blo 1653526 15906293 := bbase (se 5 (by rfl) ⟨745607, by rfl⟩ : syracuseStep 15906293 = 1491215) (by norm_num)
theorem B2094589 : Blo 1653526 2094589 := bbase (se 3 (by rfl) ⟨392735, by rfl⟩ : syracuseStep 2094589 = 785471) (by norm_num)
theorem B3724829 : Blo 1653526 3724829 := bbase (se 3 (by rfl) ⟨698405, by rfl⟩ : syracuseStep 3724829 = 1396811) (by norm_num)
theorem B2790949 : Blo 1653526 2790949 := bbase (se 4 (by rfl) ⟨261651, by rfl⟩ : syracuseStep 2790949 = 523303) (by norm_num)
theorem B1988137 : Blo 1653526 1988137 := bbase (se 2 (by rfl) ⟨745551, by rfl⟩ : syracuseStep 1988137 = 1491103) (by norm_num)
theorem B7067189 : Blo 1653526 7067189 := bbase (se 5 (by rfl) ⟨331274, by rfl⟩ : syracuseStep 7067189 = 662549) (by norm_num)
theorem B2356789 : Blo 1653526 2356789 := bbase (se 5 (by rfl) ⟨110474, by rfl⟩ : syracuseStep 2356789 = 220949) (by norm_num)
theorem B3724901 : Blo 1653526 3724901 := bbase (se 4 (by rfl) ⟨349209, by rfl⟩ : syracuseStep 3724901 = 698419) (by norm_num)
theorem B2791037 : Blo 1653526 2791037 := bbase (se 3 (by rfl) ⟨523319, by rfl⟩ : syracuseStep 2791037 = 1046639) (by norm_num)
theorem B5584517 : Blo 1653526 5584517 := bbase (se 4 (by rfl) ⟨523548, by rfl⟩ : syracuseStep 5584517 = 1047097) (by norm_num)
theorem B1791653 : Blo 1653526 1791653 := bbase (se 4 (by rfl) ⟨167967, by rfl⟩ : syracuseStep 1791653 = 335935) (by norm_num)
theorem B2094761 : Blo 1653526 2094761 := bbase (se 2 (by rfl) ⟨785535, by rfl⟩ : syracuseStep 2094761 = 1571071) (by norm_num)
theorem B5961413 : Blo 1653526 5961413 := bbase (se 4 (by rfl) ⟨558882, by rfl⟩ : syracuseStep 5961413 = 1117765) (by norm_num)
theorem B7952069 : Blo 1653526 7952069 := bbase (se 4 (by rfl) ⟨745506, by rfl⟩ : syracuseStep 7952069 = 1491013) (by norm_num)
theorem B2094817 : Blo 1653526 2094817 := bbase (se 2 (by rfl) ⟨785556, by rfl⟩ : syracuseStep 2094817 = 1571113) (by norm_num)
theorem B2791165 : Blo 1653526 2791165 := bbase (se 3 (by rfl) ⟨523343, by rfl⟩ : syracuseStep 2791165 = 1046687) (by norm_num)
theorem B5297957 : Blo 1653526 5297957 := bbase (se 4 (by rfl) ⟨496683, by rfl⟩ : syracuseStep 5297957 = 993367) (by norm_num)
theorem B7952165 : Blo 1653526 7952165 := bbase (se 4 (by rfl) ⟨745515, by rfl⟩ : syracuseStep 7952165 = 1491031) (by norm_num)
theorem B14718773 : Blo 1653526 14718773 := bbase (se 5 (by rfl) ⟨689942, by rfl⟩ : syracuseStep 14718773 = 1379885) (by norm_num)
theorem B2094913 : Blo 1653526 2094913 := bbase (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) (by norm_num)
theorem B2791253 : Blo 1653526 2791253 := bbase (se 9 (by rfl) ⟨8177, by rfl⟩ : syracuseStep 2791253 = 16355) (by norm_num)
theorem B5961557 : Blo 1653526 5961557 := bbase (se 9 (by rfl) ⟨17465, by rfl⟩ : syracuseStep 5961557 = 34931) (by norm_num)
theorem B1767301 : Blo 1653526 1767301 := bbase (se 4 (by rfl) ⟨165684, by rfl⟩ : syracuseStep 1767301 = 331369) (by norm_num)
theorem B2791381 : Blo 1653526 2791381 := bbase (se 7 (by rfl) ⟨32711, by rfl⟩ : syracuseStep 2791381 = 65423) (by norm_num)
theorem B2095085 : Blo 1653526 2095085 := bbase (se 3 (by rfl) ⟨392828, by rfl⟩ : syracuseStep 2095085 = 785657) (by norm_num)
theorem B1767421 : Blo 1653526 1767421 := bbase (se 3 (by rfl) ⟨331391, by rfl⟩ : syracuseStep 1767421 = 662783) (by norm_num)
theorem B2095141 : Blo 1653526 2095141 := bbase (se 4 (by rfl) ⟨196419, by rfl⟩ : syracuseStep 2095141 = 392839) (by norm_num)
theorem B2791469 : Blo 1653526 2791469 := bbase (se 3 (by rfl) ⟨523400, by rfl⟩ : syracuseStep 2791469 = 1046801) (by norm_num)
theorem B5584949 : Blo 1653526 5584949 := bbase (se 5 (by rfl) ⟨261794, by rfl⟩ : syracuseStep 5584949 = 523589) (by norm_num)
theorem B3446885 : Blo 1653526 3446885 := bbase (se 4 (by rfl) ⟨323145, by rfl⟩ : syracuseStep 3446885 = 646291) (by norm_num)
theorem B2095237 : Blo 1653526 2095237 := bbase (se 4 (by rfl) ⟨196428, by rfl⟩ : syracuseStep 2095237 = 392857) (by norm_num)
theorem B2791597 : Blo 1653526 2791597 := bbase (se 3 (by rfl) ⟨523424, by rfl⟩ : syracuseStep 2791597 = 1046849) (by norm_num)
theorem B2480309 : Blo 1653526 2480309 := bbase (se 5 (by rfl) ⟨116264, by rfl⟩ : syracuseStep 2480309 = 232529) (by norm_num)
theorem B2480333 : Blo 1653526 2480333 := bbase (se 3 (by rfl) ⟨465062, by rfl⟩ : syracuseStep 2480333 = 930125) (by norm_num)
theorem B2480357 : Blo 1653526 2480357 := bbase (se 4 (by rfl) ⟨232533, by rfl⟩ : syracuseStep 2480357 = 465067) (by norm_num)
theorem B1767673 : Blo 1653526 1767673 := bbase (se 2 (by rfl) ⟨662877, by rfl⟩ : syracuseStep 1767673 = 1325755) (by norm_num)
theorem B2480381 : Blo 1653526 2480381 := bbase (se 3 (by rfl) ⟨465071, by rfl⟩ : syracuseStep 2480381 = 930143) (by norm_num)
theorem B1767677 : Blo 1653526 1767677 := bbase (se 3 (by rfl) ⟨331439, by rfl⟩ : syracuseStep 1767677 = 662879) (by norm_num)
theorem B2791685 : Blo 1653526 2791685 := bbase (se 4 (by rfl) ⟨261720, by rfl⟩ : syracuseStep 2791685 = 523441) (by norm_num)
theorem B2480405 : Blo 1653526 2480405 := bbase (se 6 (by rfl) ⟨58134, by rfl⟩ : syracuseStep 2480405 = 116269) (by norm_num)
theorem B2480429 : Blo 1653526 2480429 := bbase (se 3 (by rfl) ⟨465080, by rfl⟩ : syracuseStep 2480429 = 930161) (by norm_num)
theorem B2480453 : Blo 1653526 2480453 := bbase (se 4 (by rfl) ⟨232542, by rfl⟩ : syracuseStep 2480453 = 465085) (by norm_num)
theorem B2980181 : Blo 1653526 2980181 := bbase (se 10 (by rfl) ⟨4365, by rfl⟩ : syracuseStep 2980181 = 8731) (by norm_num)
theorem B2480477 : Blo 1653526 2480477 := bbase (se 3 (by rfl) ⟨465089, by rfl⟩ : syracuseStep 2480477 = 930179) (by norm_num)
theorem B2480501 : Blo 1653526 2480501 := bbase (se 5 (by rfl) ⟨116273, by rfl⟩ : syracuseStep 2480501 = 232547) (by norm_num)
theorem B2791813 : Blo 1653526 2791813 := bbase (se 4 (by rfl) ⟨261732, by rfl⟩ : syracuseStep 2791813 = 523465) (by norm_num)
theorem B2480525 : Blo 1653526 2480525 := bbase (se 3 (by rfl) ⟨465098, by rfl⟩ : syracuseStep 2480525 = 930197) (by norm_num)
theorem B2480549 : Blo 1653526 2480549 := bbase (se 4 (by rfl) ⟨232551, by rfl⟩ : syracuseStep 2480549 = 465103) (by norm_num)
theorem B2480573 : Blo 1653526 2480573 := bbase (se 3 (by rfl) ⟨465107, by rfl⟩ : syracuseStep 2480573 = 930215) (by norm_num)
theorem B2480597 : Blo 1653526 2480597 := bbase (se 7 (by rfl) ⟨29069, by rfl⟩ : syracuseStep 2480597 = 58139) (by norm_num)
theorem B2791901 : Blo 1653526 2791901 := bbase (se 3 (by rfl) ⟨523481, by rfl⟩ : syracuseStep 2791901 = 1046963) (by norm_num)
theorem B5585381 : Blo 1653526 5585381 := bbase (se 4 (by rfl) ⟨523629, by rfl⟩ : syracuseStep 5585381 = 1047259) (by norm_num)
theorem B2480621 : Blo 1653526 2480621 := bbase (se 3 (by rfl) ⟨465116, by rfl⟩ : syracuseStep 2480621 = 930233) (by norm_num)
theorem B2480645 : Blo 1653526 2480645 := bbase (se 4 (by rfl) ⟨232560, by rfl⟩ : syracuseStep 2480645 = 465121) (by norm_num)
theorem B2480669 : Blo 1653526 2480669 := bbase (se 3 (by rfl) ⟨465125, by rfl⟩ : syracuseStep 2480669 = 930251) (by norm_num)
theorem B2480693 : Blo 1653526 2480693 := bbase (se 5 (by rfl) ⟨116282, by rfl⟩ : syracuseStep 2480693 = 232565) (by norm_num)
theorem B2480717 : Blo 1653526 2480717 := bbase (se 3 (by rfl) ⟨465134, by rfl⟩ : syracuseStep 2480717 = 930269) (by norm_num)
theorem B2792029 : Blo 1653526 2792029 := bbase (se 3 (by rfl) ⟨523505, by rfl⟩ : syracuseStep 2792029 = 1047011) (by norm_num)
theorem B2480741 : Blo 1653526 2480741 := bbase (se 4 (by rfl) ⟨232569, by rfl⟩ : syracuseStep 2480741 = 465139) (by norm_num)
theorem B1677929 : Blo 1653526 1677929 := bbase (se 2 (by rfl) ⟨629223, by rfl⟩ : syracuseStep 1677929 = 1258447) (by norm_num)
theorem B2480765 : Blo 1653526 2480765 := bbase (se 3 (by rfl) ⟨465143, by rfl⟩ : syracuseStep 2480765 = 930287) (by norm_num)
theorem B2480789 : Blo 1653526 2480789 := bbase (se 6 (by rfl) ⟨58143, by rfl⟩ : syracuseStep 2480789 = 116287) (by norm_num)
theorem B2480813 : Blo 1653526 2480813 := bbase (se 3 (by rfl) ⟨465152, by rfl⟩ : syracuseStep 2480813 = 930305) (by norm_num)
theorem B2792117 : Blo 1653526 2792117 := bbase (se 5 (by rfl) ⟨130880, by rfl⟩ : syracuseStep 2792117 = 261761) (by norm_num)
theorem B2480837 : Blo 1653526 2480837 := bbase (se 4 (by rfl) ⟨232578, by rfl⟩ : syracuseStep 2480837 = 465157) (by norm_num)
theorem B2480861 : Blo 1653526 2480861 := bbase (se 3 (by rfl) ⟨465161, by rfl⟩ : syracuseStep 2480861 = 930323) (by norm_num)
theorem B2480885 : Blo 1653526 2480885 := bbase (se 5 (by rfl) ⟨116291, by rfl⟩ : syracuseStep 2480885 = 232583) (by norm_num)
theorem B8379125 : Blo 1653526 8379125 := bbase (se 5 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 8379125 = 785543) (by norm_num)
theorem B2480909 : Blo 1653526 2480909 := bbase (se 3 (by rfl) ⟨465170, by rfl⟩ : syracuseStep 2480909 = 930341) (by norm_num)
theorem B2480933 : Blo 1653526 2480933 := bbase (se 4 (by rfl) ⟨232587, by rfl⟩ : syracuseStep 2480933 = 465175) (by norm_num)
theorem B2013997 : Blo 1653526 2013997 := bbase (se 3 (by rfl) ⟨377624, by rfl⟩ : syracuseStep 2013997 = 755249) (by norm_num)
theorem B3824437 : Blo 1653526 3824437 := bbase (se 5 (by rfl) ⟨179270, by rfl⟩ : syracuseStep 3824437 = 358541) (by norm_num)
theorem B2792245 : Blo 1653526 2792245 := bbase (se 5 (by rfl) ⟨130886, by rfl⟩ : syracuseStep 2792245 = 261773) (by norm_num)
theorem B2480957 : Blo 1653526 2480957 := bbase (se 3 (by rfl) ⟨465179, by rfl⟩ : syracuseStep 2480957 = 930359) (by norm_num)
theorem B2480981 : Blo 1653526 2480981 := bbase (se 9 (by rfl) ⟨7268, by rfl⟩ : syracuseStep 2480981 = 14537) (by norm_num)
theorem B2481005 : Blo 1653526 2481005 := bbase (se 3 (by rfl) ⟨465188, by rfl⟩ : syracuseStep 2481005 = 930377) (by norm_num)
theorem B2481029 : Blo 1653526 2481029 := bbase (se 4 (by rfl) ⟨232596, by rfl⟩ : syracuseStep 2481029 = 465193) (by norm_num)
theorem B2792333 : Blo 1653526 2792333 := bbase (se 3 (by rfl) ⟨523562, by rfl⟩ : syracuseStep 2792333 = 1047125) (by norm_num)
theorem B5585813 : Blo 1653526 5585813 := bbase (se 6 (by rfl) ⟨130917, by rfl⟩ : syracuseStep 5585813 = 261835) (by norm_num)
theorem B2481053 : Blo 1653526 2481053 := bbase (se 3 (by rfl) ⟨465197, by rfl⟩ : syracuseStep 2481053 = 930395) (by norm_num)
theorem B2481077 : Blo 1653526 2481077 := bbase (se 5 (by rfl) ⟨116300, by rfl⟩ : syracuseStep 2481077 = 232601) (by norm_num)
theorem B2235325 : Blo 1653526 2235325 := bbase (se 3 (by rfl) ⟨419123, by rfl⟩ : syracuseStep 2235325 = 838247) (by norm_num)
theorem B2481101 : Blo 1653526 2481101 := bbase (se 3 (by rfl) ⟨465206, by rfl⟩ : syracuseStep 2481101 = 930413) (by norm_num)
theorem B2481125 : Blo 1653526 2481125 := bbase (se 4 (by rfl) ⟨232605, by rfl⟩ : syracuseStep 2481125 = 465211) (by norm_num)
theorem B2481149 : Blo 1653526 2481149 := bbase (se 3 (by rfl) ⟨465215, by rfl⟩ : syracuseStep 2481149 = 930431) (by norm_num)
theorem B2792461 : Blo 1653526 2792461 := bbase (se 3 (by rfl) ⟨523586, by rfl⟩ : syracuseStep 2792461 = 1047173) (by norm_num)
theorem B2481173 : Blo 1653526 2481173 := bbase (se 6 (by rfl) ⟨58152, by rfl⟩ : syracuseStep 2481173 = 116305) (by norm_num)
theorem B2481197 : Blo 1653526 2481197 := bbase (se 3 (by rfl) ⟨465224, by rfl⟩ : syracuseStep 2481197 = 930449) (by norm_num)
theorem B4471861 : Blo 1653526 4471861 := bbase (se 5 (by rfl) ⟨209618, by rfl⟩ : syracuseStep 4471861 = 419237) (by norm_num)
theorem B2481221 : Blo 1653526 2481221 := bbase (se 4 (by rfl) ⟨232614, by rfl⟩ : syracuseStep 2481221 = 465229) (by norm_num)
theorem B2481245 : Blo 1653526 2481245 := bbase (se 3 (by rfl) ⟨465233, by rfl⟩ : syracuseStep 2481245 = 930467) (by norm_num)
theorem B4709477 : Blo 1653526 4709477 := bbase (se 4 (by rfl) ⟨441513, by rfl⟩ : syracuseStep 4709477 = 883027) (by norm_num)
theorem B2792549 : Blo 1653526 2792549 := bbase (se 4 (by rfl) ⟨261801, by rfl⟩ : syracuseStep 2792549 = 523603) (by norm_num)
theorem B2481269 : Blo 1653526 2481269 := bbase (se 5 (by rfl) ⟨116309, by rfl⟩ : syracuseStep 2481269 = 232619) (by norm_num)
theorem B2481293 : Blo 1653526 2481293 := bbase (se 3 (by rfl) ⟨465242, by rfl⟩ : syracuseStep 2481293 = 930485) (by norm_num)
theorem B8371349 : Blo 1653526 8371349 := bbase (se 6 (by rfl) ⟨196203, by rfl⟩ : syracuseStep 8371349 = 392407) (by norm_num)
theorem B28277909 : Blo 1653526 28277909 := bbase (se 6 (by rfl) ⟨662763, by rfl⟩ : syracuseStep 28277909 = 1325527) (by norm_num)
theorem B2481317 : Blo 1653526 2481317 := bbase (se 4 (by rfl) ⟨232623, by rfl⟩ : syracuseStep 2481317 = 465247) (by norm_num)
theorem B10599605 : Blo 1653526 10599605 := bbase (se 5 (by rfl) ⟨496856, by rfl⟩ : syracuseStep 10599605 = 993713) (by norm_num)
theorem B2481341 : Blo 1653526 2481341 := bbase (se 3 (by rfl) ⟨465251, by rfl⟩ : syracuseStep 2481341 = 930503) (by norm_num)
theorem B2481365 : Blo 1653526 2481365 := bbase (se 7 (by rfl) ⟨29078, by rfl⟩ : syracuseStep 2481365 = 58157) (by norm_num)
theorem B2792677 : Blo 1653526 2792677 := bbase (se 4 (by rfl) ⟨261813, by rfl⟩ : syracuseStep 2792677 = 523627) (by norm_num)
theorem B2481389 : Blo 1653526 2481389 := bbase (se 3 (by rfl) ⟨465260, by rfl⟩ : syracuseStep 2481389 = 930521) (by norm_num)
theorem B2481413 : Blo 1653526 2481413 := bbase (se 4 (by rfl) ⟨232632, by rfl⟩ : syracuseStep 2481413 = 465265) (by norm_num)
theorem B2481437 : Blo 1653526 2481437 := bbase (se 3 (by rfl) ⟨465269, by rfl⟩ : syracuseStep 2481437 = 930539) (by norm_num)
theorem B2481461 : Blo 1653526 2481461 := bbase (se 5 (by rfl) ⟨116318, by rfl⟩ : syracuseStep 2481461 = 232637) (by norm_num)
theorem B2792765 : Blo 1653526 2792765 := bbase (se 3 (by rfl) ⟨523643, by rfl⟩ : syracuseStep 2792765 = 1047287) (by norm_num)
theorem B5586245 : Blo 1653526 5586245 := bbase (se 4 (by rfl) ⟨523710, by rfl⟩ : syracuseStep 5586245 = 1047421) (by norm_num)
theorem B2481485 : Blo 1653526 2481485 := bbase (se 3 (by rfl) ⟨465278, by rfl⟩ : syracuseStep 2481485 = 930557) (by norm_num)
theorem B2481509 : Blo 1653526 2481509 := bbase (se 4 (by rfl) ⟨232641, by rfl⟩ : syracuseStep 2481509 = 465283) (by norm_num)
theorem B2481533 : Blo 1653526 2481533 := bbase (se 3 (by rfl) ⟨465287, by rfl⟩ : syracuseStep 2481533 = 930575) (by norm_num)
theorem B6282629 : Blo 1653526 6282629 := bbase (se 4 (by rfl) ⟨588996, by rfl⟩ : syracuseStep 6282629 = 1177993) (by norm_num)
theorem B2481557 : Blo 1653526 2481557 := bbase (se 6 (by rfl) ⟨58161, by rfl⟩ : syracuseStep 2481557 = 116323) (by norm_num)
theorem B2481581 : Blo 1653526 2481581 := bbase (se 3 (by rfl) ⟨465296, by rfl⟩ : syracuseStep 2481581 = 930593) (by norm_num)
theorem B4185533 : Blo 1653526 4185533 := bbase (se 3 (by rfl) ⟨784787, by rfl⟩ : syracuseStep 4185533 = 1569575) (by norm_num)
theorem B2792893 : Blo 1653526 2792893 := bbase (se 3 (by rfl) ⟨523667, by rfl⟩ : syracuseStep 2792893 = 1047335) (by norm_num)
theorem B2481605 : Blo 1653526 2481605 := bbase (se 4 (by rfl) ⟨232650, by rfl⟩ : syracuseStep 2481605 = 465301) (by norm_num)
theorem B2481629 : Blo 1653526 2481629 := bbase (se 3 (by rfl) ⟨465305, by rfl⟩ : syracuseStep 2481629 = 930611) (by norm_num)
theorem B2481653 : Blo 1653526 2481653 := bbase (se 5 (by rfl) ⟨116327, by rfl⟩ : syracuseStep 2481653 = 232655) (by norm_num)
theorem B2481677 : Blo 1653526 2481677 := bbase (se 3 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 2481677 = 930629) (by norm_num)
theorem B31792661 : Blo 1653526 31792661 := bbase (se 6 (by rfl) ⟨745140, by rfl⟩ : syracuseStep 31792661 = 1490281) (by norm_num)
theorem B2792981 : Blo 1653526 2792981 := bbase (se 6 (by rfl) ⟨65460, by rfl⟩ : syracuseStep 2792981 = 130921) (by norm_num)
theorem B2481701 : Blo 1653526 2481701 := bbase (se 4 (by rfl) ⟨232659, by rfl⟩ : syracuseStep 2481701 = 465319) (by norm_num)
theorem B2481725 : Blo 1653526 2481725 := bbase (se 3 (by rfl) ⟨465323, by rfl⟩ : syracuseStep 2481725 = 930647) (by norm_num)
theorem B2481749 : Blo 1653526 2481749 := bbase (se 8 (by rfl) ⟨14541, by rfl⟩ : syracuseStep 2481749 = 29083) (by norm_num)
theorem B2981485 : Blo 1653526 2981485 := bbase (se 3 (by rfl) ⟨559028, by rfl⟩ : syracuseStep 2981485 = 1118057) (by norm_num)
theorem B2481773 : Blo 1653526 2481773 := bbase (se 3 (by rfl) ⟨465332, by rfl⟩ : syracuseStep 2481773 = 930665) (by norm_num)
theorem B2481797 : Blo 1653526 2481797 := bbase (se 4 (by rfl) ⟨232668, by rfl⟩ : syracuseStep 2481797 = 465337) (by norm_num)
theorem B2793109 : Blo 1653526 2793109 := bbase (se 6 (by rfl) ⟨65463, by rfl⟩ : syracuseStep 2793109 = 130927) (by norm_num)
theorem B2481821 : Blo 1653526 2481821 := bbase (se 3 (by rfl) ⟨465341, by rfl⟩ : syracuseStep 2481821 = 930683) (by norm_num)
theorem B6282917 : Blo 1653526 6282917 := bbase (se 4 (by rfl) ⟨589023, by rfl⟩ : syracuseStep 6282917 = 1178047) (by norm_num)
theorem B7954085 : Blo 1653526 7954085 := bbase (se 4 (by rfl) ⟨745695, by rfl⟩ : syracuseStep 7954085 = 1491391) (by norm_num)
theorem B2481845 : Blo 1653526 2481845 := bbase (se 5 (by rfl) ⟨116336, by rfl⟩ : syracuseStep 2481845 = 232673) (by norm_num)
theorem B2481869 : Blo 1653526 2481869 := bbase (se 3 (by rfl) ⟨465350, by rfl⟩ : syracuseStep 2481869 = 930701) (by norm_num)
theorem B2481893 : Blo 1653526 2481893 := bbase (se 4 (by rfl) ⟨232677, by rfl⟩ : syracuseStep 2481893 = 465355) (by norm_num)
theorem B2793197 : Blo 1653526 2793197 := bbase (se 3 (by rfl) ⟨523724, by rfl⟩ : syracuseStep 2793197 = 1047449) (by norm_num)
theorem B5586677 : Blo 1653526 5586677 := bbase (se 5 (by rfl) ⟨261875, by rfl⟩ : syracuseStep 5586677 = 523751) (by norm_num)
theorem B2481917 : Blo 1653526 2481917 := bbase (se 3 (by rfl) ⟨465359, by rfl⟩ : syracuseStep 2481917 = 930719) (by norm_num)
theorem B4185877 : Blo 1653526 4185877 := bbase (se 6 (by rfl) ⟨98106, by rfl⟩ : syracuseStep 4185877 = 196213) (by norm_num)
theorem B2481941 : Blo 1653526 2481941 := bbase (se 6 (by rfl) ⟨58170, by rfl⟩ : syracuseStep 2481941 = 116341) (by norm_num)
theorem B2481965 : Blo 1653526 2481965 := bbase (se 3 (by rfl) ⟨465368, by rfl⟩ : syracuseStep 2481965 = 930737) (by norm_num)
theorem B2481989 : Blo 1653526 2481989 := bbase (se 4 (by rfl) ⟨232686, by rfl⟩ : syracuseStep 2481989 = 465373) (by norm_num)
theorem B2121557 : Blo 1653526 2121557 := bbase (se 9 (by rfl) ⟨6215, by rfl⟩ : syracuseStep 2121557 = 12431) (by norm_num)
theorem B2482013 : Blo 1653526 2482013 := bbase (se 3 (by rfl) ⟨465377, by rfl⟩ : syracuseStep 2482013 = 930755) (by norm_num)
theorem B2236261 : Blo 1653526 2236261 := bbase (se 4 (by rfl) ⟨209649, by rfl⟩ : syracuseStep 2236261 = 419299) (by norm_num)
theorem B2793325 : Blo 1653526 2793325 := bbase (se 3 (by rfl) ⟨523748, by rfl⟩ : syracuseStep 2793325 = 1047497) (by norm_num)
theorem B2482037 : Blo 1653526 2482037 := bbase (se 5 (by rfl) ⟨116345, by rfl⟩ : syracuseStep 2482037 = 232691) (by norm_num)
theorem B4185989 : Blo 1653526 4185989 := bbase (se 4 (by rfl) ⟨392436, by rfl⟩ : syracuseStep 4185989 = 784873) (by norm_num)
theorem B2482061 : Blo 1653526 2482061 := bbase (se 3 (by rfl) ⟨465386, by rfl⟩ : syracuseStep 2482061 = 930773) (by norm_num)
theorem B2482085 : Blo 1653526 2482085 := bbase (se 4 (by rfl) ⟨232695, by rfl⟩ : syracuseStep 2482085 = 465391) (by norm_num)
theorem B3973045 : Blo 1653526 3973045 := bbase (se 5 (by rfl) ⟨186236, by rfl⟩ : syracuseStep 3973045 = 372473) (by norm_num)
theorem B5300149 : Blo 1653526 5300149 := bbase (se 5 (by rfl) ⟨248444, by rfl⟩ : syracuseStep 5300149 = 496889) (by norm_num)
theorem B2482109 : Blo 1653526 2482109 := bbase (se 3 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 2482109 = 930791) (by norm_num)
theorem B2793413 : Blo 1653526 2793413 := bbase (se 4 (by rfl) ⟨261882, by rfl⟩ : syracuseStep 2793413 = 523765) (by norm_num)
theorem B16981973 : Blo 1653526 16981973 := bbase (se 7 (by rfl) ⟨199007, by rfl⟩ : syracuseStep 16981973 = 398015) (by norm_num)
theorem B2482133 : Blo 1653526 2482133 := bbase (se 7 (by rfl) ⟨29087, by rfl⟩ : syracuseStep 2482133 = 58175) (by norm_num)
theorem B2482157 : Blo 1653526 2482157 := bbase (se 3 (by rfl) ⟨465404, by rfl⟩ : syracuseStep 2482157 = 930809) (by norm_num)
theorem B1654787 : Blo 1653526 1654787 := bstep (se 1 (by rfl) ⟨1241090, by rfl⟩ : syracuseStep 1654787 = 2482181) B2482181
theorem B5586947 : Blo 1653526 5586947 := bstep (se 1 (by rfl) ⟨4190210, by rfl⟩ : syracuseStep 5586947 = 8380421) B8380421
theorem B2482193 : Blo 1653526 2482193 := bstep (se 2 (by rfl) ⟨930822, by rfl⟩ : syracuseStep 2482193 = 1861645) B1861645
theorem B1654803 : Blo 1653526 1654803 := bstep (se 1 (by rfl) ⟨1241102, by rfl⟩ : syracuseStep 1654803 = 2482205) B2482205
theorem B2482211 : Blo 1653526 2482211 := bstep (se 1 (by rfl) ⟨1861658, by rfl⟩ : syracuseStep 2482211 = 3723317) B3723317
theorem B1654819 : Blo 1653526 1654819 := bstep (se 1 (by rfl) ⟨1241114, by rfl⟩ : syracuseStep 1654819 = 2482229) B2482229
theorem B9068593 : Blo 1653526 9068593 := bstep (se 2 (by rfl) ⟨3400722, by rfl⟩ : syracuseStep 9068593 = 6801445) B6801445
theorem B2793521 : Blo 1653526 2793521 := bstep (se 2 (by rfl) ⟨1047570, by rfl⟩ : syracuseStep 2793521 = 2095141) B2095141
theorem B1654835 : Blo 1653526 1654835 := bstep (se 1 (by rfl) ⟨1241126, by rfl⟩ : syracuseStep 1654835 = 2482253) B2482253
theorem B2482241 : Blo 1653526 2482241 := bstep (se 2 (by rfl) ⟨930840, by rfl⟩ : syracuseStep 2482241 = 1861681) B1861681
theorem B1654851 : Blo 1653526 1654851 := bstep (se 1 (by rfl) ⟨1241138, by rfl⟩ : syracuseStep 1654851 = 2482277) B2482277
theorem B2482259 : Blo 1653526 2482259 := bstep (se 1 (by rfl) ⟨1861694, by rfl⟩ : syracuseStep 2482259 = 3723389) B3723389
theorem B1654867 : Blo 1653526 1654867 := bstep (se 1 (by rfl) ⟨1241150, by rfl⟩ : syracuseStep 1654867 = 2482301) B2482301
theorem B1654883 : Blo 1653526 1654883 := bstep (se 1 (by rfl) ⟨1241162, by rfl⟩ : syracuseStep 1654883 = 2482325) B2482325
theorem B2482289 : Blo 1653526 2482289 := bstep (se 2 (by rfl) ⟨930858, by rfl⟩ : syracuseStep 2482289 = 1861717) B1861717
theorem B1654899 : Blo 1653526 1654899 := bstep (se 1 (by rfl) ⟨1241174, by rfl⟩ : syracuseStep 1654899 = 2482349) B2482349
theorem B2482307 : Blo 1653526 2482307 := bstep (se 1 (by rfl) ⟨1861730, by rfl⟩ : syracuseStep 2482307 = 3723461) B3723461
theorem B1654915 : Blo 1653526 1654915 := bstep (se 1 (by rfl) ⟨1241186, by rfl⟩ : syracuseStep 1654915 = 2482373) B2482373
theorem B1654931 : Blo 1653526 1654931 := bstep (se 1 (by rfl) ⟨1241198, by rfl⟩ : syracuseStep 1654931 = 2482397) B2482397
theorem B2482337 : Blo 1653526 2482337 := bstep (se 2 (by rfl) ⟨930876, by rfl⟩ : syracuseStep 2482337 = 1861753) B1861753
theorem B5963939 : Blo 1653526 5963939 := bstep (se 1 (by rfl) ⟨4472954, by rfl⟩ : syracuseStep 5963939 = 8945909) B8945909
theorem B1654947 : Blo 1653526 1654947 := bstep (se 1 (by rfl) ⟨1241210, by rfl⟩ : syracuseStep 1654947 = 2482421) B2482421
theorem B2793649 : Blo 1653526 2793649 := bstep (se 2 (by rfl) ⟨1047618, by rfl⟩ : syracuseStep 2793649 = 2095237) B2095237
theorem B2482355 : Blo 1653526 2482355 := bstep (se 1 (by rfl) ⟨1861766, by rfl⟩ : syracuseStep 2482355 = 3723533) B3723533
theorem B1654963 : Blo 1653526 1654963 := bstep (se 1 (by rfl) ⟨1241222, by rfl⟩ : syracuseStep 1654963 = 2482445) B2482445
theorem B1654979 : Blo 1653526 1654979 := bstep (se 1 (by rfl) ⟨1241234, by rfl⟩ : syracuseStep 1654979 = 2482469) B2482469
theorem B2482385 : Blo 1653526 2482385 := bstep (se 2 (by rfl) ⟨930894, by rfl⟩ : syracuseStep 2482385 = 1861789) B1861789
theorem B1654995 : Blo 1653526 1654995 := bstep (se 1 (by rfl) ⟨1241246, by rfl⟩ : syracuseStep 1654995 = 2482493) B2482493
theorem B2793683 : Blo 1653526 2793683 := bstep (se 1 (by rfl) ⟨2095262, by rfl⟩ : syracuseStep 2793683 = 4190525) B4190525
theorem B2482403 : Blo 1653526 2482403 := bstep (se 1 (by rfl) ⟨1861802, by rfl⟩ : syracuseStep 2482403 = 3723605) B3723605
theorem B1655011 : Blo 1653526 1655011 := bstep (se 1 (by rfl) ⟨1241258, by rfl⟩ : syracuseStep 1655011 = 2482517) B2482517
theorem B1655027 : Blo 1653526 1655027 := bstep (se 1 (by rfl) ⟨1241270, by rfl⟩ : syracuseStep 1655027 = 2482541) B2482541
theorem B2482433 : Blo 1653526 2482433 := bstep (se 2 (by rfl) ⟨930912, by rfl⟩ : syracuseStep 2482433 = 1861825) B1861825
theorem B1655043 : Blo 1653526 1655043 := bstep (se 1 (by rfl) ⟨1241282, by rfl⟩ : syracuseStep 1655043 = 2482565) B2482565
theorem B9191693 : Blo 1653526 9191693 := bstep (se 3 (by rfl) ⟨1723442, by rfl⟩ : syracuseStep 9191693 = 3446885) B3446885
theorem B5587217 : Blo 1653526 5587217 := bstep (se 2 (by rfl) ⟨2095206, by rfl⟩ : syracuseStep 5587217 = 4190413) B4190413
theorem B2482451 : Blo 1653526 2482451 := bstep (se 1 (by rfl) ⟨1861838, by rfl⟩ : syracuseStep 2482451 = 3723677) B3723677
theorem B1655059 : Blo 1653526 1655059 := bstep (se 1 (by rfl) ⟨1241294, by rfl⟩ : syracuseStep 1655059 = 2482589) B2482589
theorem B1655075 : Blo 1653526 1655075 := bstep (se 1 (by rfl) ⟨1241306, by rfl⟩ : syracuseStep 1655075 = 2482613) B2482613
theorem B4473137 : Blo 1653526 4473137 := bstep (se 2 (by rfl) ⟨1677426, by rfl⟩ : syracuseStep 4473137 = 3354853) B3354853
theorem B2482481 : Blo 1653526 2482481 := bstep (se 2 (by rfl) ⟨930930, by rfl⟩ : syracuseStep 2482481 = 1861861) B1861861
theorem B1655091 : Blo 1653526 1655091 := bstep (se 1 (by rfl) ⟨1241318, by rfl⟩ : syracuseStep 1655091 = 2482637) B2482637
theorem B2482499 : Blo 1653526 2482499 := bstep (se 1 (by rfl) ⟨1861874, by rfl⟩ : syracuseStep 2482499 = 3723749) B3723749
theorem B1655107 : Blo 1653526 1655107 := bstep (se 1 (by rfl) ⟨1241330, by rfl⟩ : syracuseStep 1655107 = 2482661) B2482661
theorem B1655123 : Blo 1653526 1655123 := bstep (se 1 (by rfl) ⟨1241342, by rfl⟩ : syracuseStep 1655123 = 2482685) B2482685
theorem B2482529 : Blo 1653526 2482529 := bstep (se 2 (by rfl) ⟨930948, by rfl⟩ : syracuseStep 2482529 = 1861897) B1861897
theorem B1655139 : Blo 1653526 1655139 := bstep (se 1 (by rfl) ⟨1241354, by rfl⟩ : syracuseStep 1655139 = 2482709) B2482709
theorem B2482547 : Blo 1653526 2482547 := bstep (se 1 (by rfl) ⟨1861910, by rfl⟩ : syracuseStep 2482547 = 3723821) B3723821
theorem B1655155 : Blo 1653526 1655155 := bstep (se 1 (by rfl) ⟨1241366, by rfl⟩ : syracuseStep 1655155 = 2482733) B2482733
theorem B4243843 : Blo 1653526 4243843 := bstep (se 1 (by rfl) ⟨3182882, by rfl⟩ : syracuseStep 4243843 = 6365765) B6365765
theorem B1655171 : Blo 1653526 1655171 := bstep (se 1 (by rfl) ⟨1241378, by rfl⟩ : syracuseStep 1655171 = 2482757) B2482757
theorem B2482577 : Blo 1653526 2482577 := bstep (se 2 (by rfl) ⟨930966, by rfl⟩ : syracuseStep 2482577 = 1861933) B1861933
theorem B1655187 : Blo 1653526 1655187 := bstep (se 1 (by rfl) ⟨1241390, by rfl⟩ : syracuseStep 1655187 = 2482781) B2482781
theorem B2482595 : Blo 1653526 2482595 := bstep (se 1 (by rfl) ⟨1861946, by rfl⟩ : syracuseStep 2482595 = 3723893) B3723893
theorem B1655203 : Blo 1653526 1655203 := bstep (se 1 (by rfl) ⟨1241402, by rfl⟩ : syracuseStep 1655203 = 2482805) B2482805
theorem B1655219 : Blo 1653526 1655219 := bstep (se 1 (by rfl) ⟨1241414, by rfl⟩ : syracuseStep 1655219 = 2482829) B2482829
theorem B2482625 : Blo 1653526 2482625 := bstep (se 2 (by rfl) ⟨930984, by rfl⟩ : syracuseStep 2482625 = 1861969) B1861969
theorem B1655235 : Blo 1653526 1655235 := bstep (se 1 (by rfl) ⟨1241426, by rfl⟩ : syracuseStep 1655235 = 2482853) B2482853
theorem B14139845 : Blo 1653526 14139845 := bstep (se 4 (by rfl) ⟨1325610, by rfl⟩ : syracuseStep 14139845 = 2651221) B2651221
theorem B2482643 : Blo 1653526 2482643 := bstep (se 1 (by rfl) ⟨1861982, by rfl⟩ : syracuseStep 2482643 = 3723965) B3723965
theorem B1655251 : Blo 1653526 1655251 := bstep (se 1 (by rfl) ⟨1241438, by rfl⟩ : syracuseStep 1655251 = 2482877) B2482877
theorem B1655267 : Blo 1653526 1655267 := bstep (se 1 (by rfl) ⟨1241450, by rfl⟩ : syracuseStep 1655267 = 2482901) B2482901
theorem B2482673 : Blo 1653526 2482673 := bstep (se 2 (by rfl) ⟨931002, by rfl⟩ : syracuseStep 2482673 = 1862005) B1862005
theorem B1655283 : Blo 1653526 1655283 := bstep (se 1 (by rfl) ⟨1241462, by rfl⟩ : syracuseStep 1655283 = 2482925) B2482925
theorem B2482691 : Blo 1653526 2482691 := bstep (se 1 (by rfl) ⟨1862018, by rfl⟩ : syracuseStep 2482691 = 3724037) B3724037
theorem B1655299 : Blo 1653526 1655299 := bstep (se 1 (by rfl) ⟨1241474, by rfl⟩ : syracuseStep 1655299 = 2482949) B2482949
theorem B1655315 : Blo 1653526 1655315 := bstep (se 1 (by rfl) ⟨1241486, by rfl⟩ : syracuseStep 1655315 = 2482973) B2482973
theorem B2482721 : Blo 1653526 2482721 := bstep (se 2 (by rfl) ⟨931020, by rfl⟩ : syracuseStep 2482721 = 1862041) B1862041
theorem B1655331 : Blo 1653526 1655331 := bstep (se 1 (by rfl) ⟨1241498, by rfl⟩ : syracuseStep 1655331 = 2482997) B2482997
theorem B2482739 : Blo 1653526 2482739 := bstep (se 1 (by rfl) ⟨1862054, by rfl⟩ : syracuseStep 2482739 = 3724109) B3724109
theorem B1655347 : Blo 1653526 1655347 := bstep (se 1 (by rfl) ⟨1241510, by rfl⟩ : syracuseStep 1655347 = 2483021) B2483021
theorem B1655363 : Blo 1653526 1655363 := bstep (se 1 (by rfl) ⟨1241522, by rfl⟩ : syracuseStep 1655363 = 2483045) B2483045
theorem B2482769 : Blo 1653526 2482769 := bstep (se 2 (by rfl) ⟨931038, by rfl⟩ : syracuseStep 2482769 = 1862077) B1862077
theorem B1655379 : Blo 1653526 1655379 := bstep (se 1 (by rfl) ⟨1241534, by rfl⟩ : syracuseStep 1655379 = 2483069) B2483069
theorem B2515555 : Blo 1653526 2515555 := bstep (se 1 (by rfl) ⟨1886666, by rfl⟩ : syracuseStep 2515555 = 3773333) B3773333
theorem B2482787 : Blo 1653526 2482787 := bstep (se 1 (by rfl) ⟨1862090, by rfl⟩ : syracuseStep 2482787 = 3724181) B3724181
theorem B1655395 : Blo 1653526 1655395 := bstep (se 1 (by rfl) ⟨1241546, by rfl⟩ : syracuseStep 1655395 = 2483093) B2483093
theorem B6283889 : Blo 1653526 6283889 := bstep (se 2 (by rfl) ⟨2356458, by rfl⟩ : syracuseStep 6283889 = 4712917) B4712917
theorem B13091441 : Blo 1653526 13091441 := bstep (se 2 (by rfl) ⟨4909290, by rfl⟩ : syracuseStep 13091441 = 9818581) B9818581
theorem B1655411 : Blo 1653526 1655411 := bstep (se 1 (by rfl) ⟨1241558, by rfl⟩ : syracuseStep 1655411 = 2483117) B2483117
theorem B2482817 : Blo 1653526 2482817 := bstep (se 2 (by rfl) ⟨931056, by rfl⟩ : syracuseStep 2482817 = 1862113) B1862113
theorem B1655427 : Blo 1653526 1655427 := bstep (se 1 (by rfl) ⟨1241570, by rfl⟩ : syracuseStep 1655427 = 2483141) B2483141
theorem B8381069 : Blo 1653526 8381069 := bstep (se 3 (by rfl) ⟨1571450, by rfl⟩ : syracuseStep 8381069 = 3142901) B3142901
theorem B2482835 : Blo 1653526 2482835 := bstep (se 1 (by rfl) ⟨1862126, by rfl⟩ : syracuseStep 2482835 = 3724253) B3724253
theorem B1655443 : Blo 1653526 1655443 := bstep (se 1 (by rfl) ⟨1241582, by rfl⟩ : syracuseStep 1655443 = 2483165) B2483165
theorem B1860259 : Blo 1653526 1860259 := bstep (se 1 (by rfl) ⟨1395194, by rfl⟩ : syracuseStep 1860259 = 2790389) B2790389
theorem B1655459 : Blo 1653526 1655459 := bstep (se 1 (by rfl) ⟨1241594, by rfl⟩ : syracuseStep 1655459 = 2483189) B2483189
theorem B2482865 : Blo 1653526 2482865 := bstep (se 2 (by rfl) ⟨931074, by rfl⟩ : syracuseStep 2482865 = 1862149) B1862149
theorem B1655475 : Blo 1653526 1655475 := bstep (se 1 (by rfl) ⟨1241606, by rfl⟩ : syracuseStep 1655475 = 2483213) B2483213
theorem B19104437 : Blo 1653526 19104437 := bstep (se 5 (by rfl) ⟨895520, by rfl⟩ : syracuseStep 19104437 = 1791041) B1791041
theorem B2482883 : Blo 1653526 2482883 := bstep (se 1 (by rfl) ⟨1862162, by rfl⟩ : syracuseStep 2482883 = 3724325) B3724325
theorem B1655491 : Blo 1653526 1655491 := bstep (se 1 (by rfl) ⟨1241618, by rfl⟩ : syracuseStep 1655491 = 2483237) B2483237
theorem B4711117 : Blo 1653526 4711117 := bstep (se 3 (by rfl) ⟨883334, by rfl⟩ : syracuseStep 4711117 = 1766669) B1766669
theorem B1655507 : Blo 1653526 1655507 := bstep (se 1 (by rfl) ⟨1241630, by rfl⟩ : syracuseStep 1655507 = 2483261) B2483261
theorem B5964515 : Blo 1653526 5964515 := bstep (se 1 (by rfl) ⟨4473386, by rfl⟩ : syracuseStep 5964515 = 8946773) B8946773
theorem B7070435 : Blo 1653526 7070435 := bstep (se 1 (by rfl) ⟨5302826, by rfl⟩ : syracuseStep 7070435 = 10605653) B10605653
theorem B2482913 : Blo 1653526 2482913 := bstep (se 2 (by rfl) ⟨931092, by rfl⟩ : syracuseStep 2482913 = 1862185) B1862185
theorem B1655523 : Blo 1653526 1655523 := bstep (se 1 (by rfl) ⟨1241642, by rfl⟩ : syracuseStep 1655523 = 2483285) B2483285
theorem B2482931 : Blo 1653526 2482931 := bstep (se 1 (by rfl) ⟨1862198, by rfl⟩ : syracuseStep 2482931 = 3724397) B3724397
theorem B2482961 : Blo 1653526 2482961 := bstep (se 2 (by rfl) ⟨931110, by rfl⟩ : syracuseStep 2482961 = 1862221) B1862221
theorem B2482979 : Blo 1653526 2482979 := bstep (se 1 (by rfl) ⟨1862234, by rfl⟩ : syracuseStep 2482979 = 3724469) B3724469
theorem B1860403 : Blo 1653526 1860403 := bstep (se 1 (by rfl) ⟨1395302, by rfl⟩ : syracuseStep 1860403 = 2790605) B2790605
theorem B2483009 : Blo 1653526 2483009 := bstep (se 2 (by rfl) ⟨931128, by rfl⟩ : syracuseStep 2483009 = 1862257) B1862257
theorem B6710093 : Blo 1653526 6710093 := bstep (se 3 (by rfl) ⟨1258142, by rfl⟩ : syracuseStep 6710093 = 2516285) B2516285
theorem B4186961 : Blo 1653526 4186961 := bstep (se 2 (by rfl) ⟨1570110, by rfl⟩ : syracuseStep 4186961 = 3140221) B3140221
theorem B2483027 : Blo 1653526 2483027 := bstep (se 1 (by rfl) ⟨1862270, by rfl⟩ : syracuseStep 2483027 = 3724541) B3724541
theorem B4711277 : Blo 1653526 4711277 := bstep (se 3 (by rfl) ⟨883364, by rfl⟩ : syracuseStep 4711277 = 1766729) B1766729
theorem B2483057 : Blo 1653526 2483057 := bstep (se 2 (by rfl) ⟨931146, by rfl⟩ : syracuseStep 2483057 = 1862293) B1862293
theorem B4187011 : Blo 1653526 4187011 := bstep (se 1 (by rfl) ⟨3140258, by rfl⟩ : syracuseStep 4187011 = 6280517) B6280517
theorem B4473731 : Blo 1653526 4473731 := bstep (se 1 (by rfl) ⟨3355298, by rfl⟩ : syracuseStep 4473731 = 6710597) B6710597
theorem B2483075 : Blo 1653526 2483075 := bstep (se 1 (by rfl) ⟨1862306, by rfl⟩ : syracuseStep 2483075 = 3724613) B3724613
theorem B2483105 : Blo 1653526 2483105 := bstep (se 2 (by rfl) ⟨931164, by rfl⟩ : syracuseStep 2483105 = 1862329) B1862329
theorem B2483123 : Blo 1653526 2483123 := bstep (se 1 (by rfl) ⟨1862342, by rfl⟩ : syracuseStep 2483123 = 3724685) B3724685
theorem B1860547 : Blo 1653526 1860547 := bstep (se 1 (by rfl) ⟨1395410, by rfl⟩ : syracuseStep 1860547 = 2790821) B2790821
theorem B2483153 : Blo 1653526 2483153 := bstep (se 2 (by rfl) ⟨931182, by rfl⟩ : syracuseStep 2483153 = 1862365) B1862365
theorem B2483171 : Blo 1653526 2483171 := bstep (se 1 (by rfl) ⟨1862378, by rfl⟩ : syracuseStep 2483171 = 3724757) B3724757
theorem B2483201 : Blo 1653526 2483201 := bstep (se 2 (by rfl) ⟨931200, by rfl⟩ : syracuseStep 2483201 = 1862401) B1862401
theorem B8487949 : Blo 1653526 8487949 := bstep (se 3 (by rfl) ⟨1591490, by rfl⟩ : syracuseStep 8487949 = 3182981) B3182981
theorem B4187153 : Blo 1653526 4187153 := bstep (se 2 (by rfl) ⟨1570182, by rfl⟩ : syracuseStep 4187153 = 3140365) B3140365
theorem B2483219 : Blo 1653526 2483219 := bstep (se 1 (by rfl) ⟨1862414, by rfl⟩ : syracuseStep 2483219 = 3724829) B3724829
theorem B4711459 : Blo 1653526 4711459 := bstep (se 1 (by rfl) ⟨3533594, by rfl⟩ : syracuseStep 4711459 = 7067189) B7067189
theorem B2483249 : Blo 1653526 2483249 := bstep (se 2 (by rfl) ⟨931218, by rfl⟩ : syracuseStep 2483249 = 1862437) B1862437
theorem B2483267 : Blo 1653526 2483267 := bstep (se 1 (by rfl) ⟨1862450, by rfl⟩ : syracuseStep 2483267 = 3724901) B3724901
theorem B1860691 : Blo 1653526 1860691 := bstep (se 1 (by rfl) ⟨1395518, by rfl⟩ : syracuseStep 1860691 = 2791037) B2791037
theorem B3974275 : Blo 1653526 3974275 := bstep (se 1 (by rfl) ⟨2980706, by rfl⟩ : syracuseStep 3974275 = 5961413) B5961413
theorem B5301379 : Blo 1653526 5301379 := bstep (se 1 (by rfl) ⟨3976034, by rfl⟩ : syracuseStep 5301379 = 7952069) B7952069
theorem B3531971 : Blo 1653526 3531971 := bstep (se 1 (by rfl) ⟨2648978, by rfl⟩ : syracuseStep 3531971 = 5297957) B5297957
theorem B5301443 : Blo 1653526 5301443 := bstep (se 1 (by rfl) ⟨3976082, by rfl⟩ : syracuseStep 5301443 = 7952165) B7952165
theorem B1860835 : Blo 1653526 1860835 := bstep (se 1 (by rfl) ⟨1395626, by rfl⟩ : syracuseStep 1860835 = 2791253) B2791253
theorem B5301521 : Blo 1653526 5301521 := bstep (se 2 (by rfl) ⟨1988070, by rfl⟩ : syracuseStep 5301521 = 3976141) B3976141
theorem B5449037 : Blo 1653526 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B8373617 : Blo 1653526 8373617 := bstep (se 2 (by rfl) ⟨3140106, by rfl⟩ : syracuseStep 8373617 = 6280213) B6280213
theorem B1860979 : Blo 1653526 1860979 := bstep (se 1 (by rfl) ⟨1395734, by rfl⟩ : syracuseStep 1860979 = 2791469) B2791469
theorem B5096881 : Blo 1653526 5096881 := bstep (se 2 (by rfl) ⟨1911330, by rfl⟩ : syracuseStep 5096881 = 3822661) B3822661
theorem B11322821 : Blo 1653526 11322821 := bstep (se 4 (by rfl) ⟨1061514, by rfl⟩ : syracuseStep 11322821 = 2123029) B2123029
theorem B3720689 : Blo 1653526 3720689 := bstep (se 2 (by rfl) ⟨1395258, by rfl⟩ : syracuseStep 3720689 = 2790517) B2790517
theorem B3720707 : Blo 1653526 3720707 := bstep (se 1 (by rfl) ⟨2790530, by rfl⟩ : syracuseStep 3720707 = 5581061) B5581061
theorem B1861123 : Blo 1653526 1861123 := bstep (se 1 (by rfl) ⟨1395842, by rfl⟩ : syracuseStep 1861123 = 2791685) B2791685
theorem B4474477 : Blo 1653526 4474477 := bstep (se 3 (by rfl) ⟨838964, by rfl⟩ : syracuseStep 4474477 = 1677929) B1677929
theorem B1861267 : Blo 1653526 1861267 := bstep (se 1 (by rfl) ⟨1395950, by rfl⟩ : syracuseStep 1861267 = 2791901) B2791901
theorem B3139249 : Blo 1653526 3139249 := bstep (se 2 (by rfl) ⟨1177218, by rfl⟩ : syracuseStep 3139249 = 2354437) B2354437
theorem B25192133 : Blo 1653526 25192133 := bstep (se 4 (by rfl) ⟨2361762, by rfl⟩ : syracuseStep 25192133 = 4723525) B4723525
theorem B4777741 : Blo 1653526 4777741 := bstep (se 3 (by rfl) ⟨895826, by rfl⟩ : syracuseStep 4777741 = 1791653) B1791653
theorem B21210893 : Blo 1653526 21210893 := bstep (se 3 (by rfl) ⟨3977042, by rfl⟩ : syracuseStep 21210893 = 7954085) B7954085
theorem B3720977 : Blo 1653526 3720977 := bstep (se 2 (by rfl) ⟨1395366, by rfl⟩ : syracuseStep 3720977 = 2790733) B2790733
theorem B3720995 : Blo 1653526 3720995 := bstep (se 1 (by rfl) ⟨2790746, by rfl⟩ : syracuseStep 3720995 = 5581493) B5581493
theorem B1861411 : Blo 1653526 1861411 := bstep (se 1 (by rfl) ⟨1396058, by rfl⟩ : syracuseStep 1861411 = 2792117) B2792117
theorem B4474769 : Blo 1653526 4474769 := bstep (se 2 (by rfl) ⟨1678038, by rfl⟩ : syracuseStep 4474769 = 3356077) B3356077
theorem B1861555 : Blo 1653526 1861555 := bstep (se 1 (by rfl) ⟨1396166, by rfl⟩ : syracuseStep 1861555 = 2792333) B2792333
theorem B4188145 : Blo 1653526 4188145 := bstep (se 2 (by rfl) ⟨1570554, by rfl⟩ : syracuseStep 4188145 = 3141109) B3141109
theorem B6285347 : Blo 1653526 6285347 := bstep (se 1 (by rfl) ⟨4714010, by rfl⟩ : syracuseStep 6285347 = 9428021) B9428021
theorem B5580845 : Blo 1653526 5580845 := bstep (se 3 (by rfl) ⟨1046408, by rfl⟩ : syracuseStep 5580845 = 2092817) B2092817
theorem B3721265 : Blo 1653526 3721265 := bstep (se 2 (by rfl) ⟨1395474, by rfl⟩ : syracuseStep 3721265 = 2790949) B2790949
theorem B3139651 : Blo 1653526 3139651 := bstep (se 1 (by rfl) ⟨2354738, by rfl⟩ : syracuseStep 3139651 = 4709477) B4709477
theorem B3721283 : Blo 1653526 3721283 := bstep (se 1 (by rfl) ⟨2790962, by rfl⟩ : syracuseStep 3721283 = 5581925) B5581925
theorem B1861699 : Blo 1653526 1861699 := bstep (se 1 (by rfl) ⟨1396274, by rfl⟩ : syracuseStep 1861699 = 2792549) B2792549
theorem B5580899 : Blo 1653526 5580899 := bstep (se 1 (by rfl) ⟨4185674, by rfl⟩ : syracuseStep 5580899 = 8371349) B8371349
theorem B18851939 : Blo 1653526 18851939 := bstep (se 1 (by rfl) ⟨14138954, by rfl⟩ : syracuseStep 18851939 = 28277909) B28277909
theorem B3139697 : Blo 1653526 3139697 := bstep (se 2 (by rfl) ⟨1177386, by rfl⟩ : syracuseStep 3139697 = 2354773) B2354773
theorem B3975313 : Blo 1653526 3975313 := bstep (se 2 (by rfl) ⟨1490742, by rfl⟩ : syracuseStep 3975313 = 2981485) B2981485
theorem B24176837 : Blo 1653526 24176837 := bstep (se 4 (by rfl) ⟨2266578, by rfl⟩ : syracuseStep 24176837 = 4533157) B4533157
theorem B1861843 : Blo 1653526 1861843 := bstep (se 1 (by rfl) ⟨1396382, by rfl⟩ : syracuseStep 1861843 = 2792765) B2792765
theorem B4188419 : Blo 1653526 4188419 := bstep (se 1 (by rfl) ⟨3141314, by rfl⟩ : syracuseStep 4188419 = 6282629) B6282629
theorem B2722097 : Blo 1653526 2722097 := bstep (se 2 (by rfl) ⟨1020786, by rfl⟩ : syracuseStep 2722097 = 2041573) B2041573
theorem B5966129 : Blo 1653526 5966129 := bstep (se 2 (by rfl) ⟨2237298, by rfl⟩ : syracuseStep 5966129 = 4474597) B4474597
theorem B3721553 : Blo 1653526 3721553 := bstep (se 2 (by rfl) ⟨1395582, by rfl⟩ : syracuseStep 3721553 = 2791165) B2791165
theorem B21195107 : Blo 1653526 21195107 := bstep (se 1 (by rfl) ⟨15896330, by rfl⟩ : syracuseStep 21195107 = 31792661) B31792661
theorem B3721571 : Blo 1653526 3721571 := bstep (se 1 (by rfl) ⟨2791178, by rfl⟩ : syracuseStep 3721571 = 5582357) B5582357
theorem B1861987 : Blo 1653526 1861987 := bstep (se 1 (by rfl) ⟨1396490, by rfl⟩ : syracuseStep 1861987 = 2792981) B2792981
theorem B12568931 : Blo 1653526 12568931 := bstep (se 1 (by rfl) ⟨9426698, by rfl⟩ : syracuseStep 12568931 = 18853397) B18853397
theorem B5581169 : Blo 1653526 5581169 := bstep (se 2 (by rfl) ⟨2092938, by rfl⟩ : syracuseStep 5581169 = 4185877) B4185877
theorem B3139985 : Blo 1653526 3139985 := bstep (se 2 (by rfl) ⟨1177494, by rfl⟩ : syracuseStep 3139985 = 2354989) B2354989
theorem B4712849 : Blo 1653526 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B4188611 : Blo 1653526 4188611 := bstep (se 1 (by rfl) ⟨3141458, by rfl⟩ : syracuseStep 4188611 = 6282917) B6282917
theorem B15895025 : Blo 1653526 15895025 := bstep (se 2 (by rfl) ⟨5960634, by rfl⟩ : syracuseStep 15895025 = 11921269) B11921269
theorem B1862131 : Blo 1653526 1862131 := bstep (se 1 (by rfl) ⟨1396598, by rfl⟩ : syracuseStep 1862131 = 2793197) B2793197
theorem B30173809 : Blo 1653526 30173809 := bstep (se 2 (by rfl) ⟨11315178, by rfl⟩ : syracuseStep 30173809 = 22630357) B22630357
theorem B3721841 : Blo 1653526 3721841 := bstep (se 2 (by rfl) ⟨1395690, by rfl⟩ : syracuseStep 3721841 = 2791381) B2791381
theorem B3721859 : Blo 1653526 3721859 := bstep (se 1 (by rfl) ⟨2791394, by rfl⟩ : syracuseStep 3721859 = 5582789) B5582789
theorem B1862275 : Blo 1653526 1862275 := bstep (se 1 (by rfl) ⟨1396706, by rfl⟩ : syracuseStep 1862275 = 2793413) B2793413
theorem B9546445 : Blo 1653526 9546445 := bstep (se 3 (by rfl) ⟨1789958, by rfl⟩ : syracuseStep 9546445 = 3579917) B3579917
theorem B1862419 : Blo 1653526 1862419 := bstep (se 1 (by rfl) ⟨1396814, by rfl⟩ : syracuseStep 1862419 = 2793629) B2793629
theorem B8375075 : Blo 1653526 8375075 := bstep (se 1 (by rfl) ⟨6281306, by rfl⟩ : syracuseStep 8375075 = 12562613) B12562613
theorem B5581709 : Blo 1653526 5581709 := bstep (se 3 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 5581709 = 2093141) B2093141
theorem B3722129 : Blo 1653526 3722129 := bstep (se 2 (by rfl) ⟨1395798, by rfl⟩ : syracuseStep 3722129 = 2791597) B2791597
theorem B3722147 : Blo 1653526 3722147 := bstep (se 1 (by rfl) ⟨2791610, by rfl⟩ : syracuseStep 3722147 = 5583221) B5583221
theorem B5581763 : Blo 1653526 5581763 := bstep (se 1 (by rfl) ⟨4186322, by rfl⟩ : syracuseStep 5581763 = 8372645) B8372645
theorem B2649107 : Blo 1653526 2649107 := bstep (se 1 (by rfl) ⟨1986830, by rfl⟩ : syracuseStep 2649107 = 3973661) B3973661
theorem B2387027 : Blo 1653526 2387027 := bstep (se 1 (by rfl) ⟨1790270, by rfl⟩ : syracuseStep 2387027 = 3580541) B3580541
theorem B3140707 : Blo 1653526 3140707 := bstep (se 1 (by rfl) ⟨2355530, by rfl⟩ : syracuseStep 3140707 = 4711061) B4711061
theorem B5303441 : Blo 1653526 5303441 := bstep (se 2 (by rfl) ⟨1988790, by rfl⟩ : syracuseStep 5303441 = 3977581) B3977581
theorem B3533987 : Blo 1653526 3533987 := bstep (se 1 (by rfl) ⟨2650490, by rfl⟩ : syracuseStep 3533987 = 5300981) B5300981
theorem B3722417 : Blo 1653526 3722417 := bstep (se 2 (by rfl) ⟨1395906, by rfl⟩ : syracuseStep 3722417 = 2791813) B2791813
theorem B3722435 : Blo 1653526 3722435 := bstep (se 1 (by rfl) ⟨2791826, by rfl⟩ : syracuseStep 3722435 = 5583653) B5583653
theorem B5582033 : Blo 1653526 5582033 := bstep (se 2 (by rfl) ⟨2093262, by rfl⟩ : syracuseStep 5582033 = 4186525) B4186525
theorem B2354465 : Blo 1653526 2354465 := bstep (se 2 (by rfl) ⟨882924, by rfl⟩ : syracuseStep 2354465 = 1765849) B1765849
theorem B4713805 : Blo 1653526 4713805 := bstep (se 3 (by rfl) ⟨883838, by rfl⟩ : syracuseStep 4713805 = 1767677) B1767677
theorem B2354545 : Blo 1653526 2354545 := bstep (se 2 (by rfl) ⟨882954, by rfl⟩ : syracuseStep 2354545 = 1765909) B1765909
theorem B16117105 : Blo 1653526 16117105 := bstep (se 2 (by rfl) ⟨6043914, by rfl⟩ : syracuseStep 16117105 = 12087829) B12087829
theorem B4189553 : Blo 1653526 4189553 := bstep (se 2 (by rfl) ⟨1571082, by rfl⟩ : syracuseStep 4189553 = 3142165) B3142165
theorem B4189603 : Blo 1653526 4189603 := bstep (se 1 (by rfl) ⟨3142202, by rfl⟩ : syracuseStep 4189603 = 6284405) B6284405
theorem B20131253 : Blo 1653526 20131253 := bstep (se 5 (by rfl) ⟨943652, by rfl⟩ : syracuseStep 20131253 = 1887305) B1887305
theorem B3722705 : Blo 1653526 3722705 := bstep (se 2 (by rfl) ⟨1396014, by rfl⟩ : syracuseStep 3722705 = 2792029) B2792029
theorem B3722723 : Blo 1653526 3722723 := bstep (se 1 (by rfl) ⟨2792042, by rfl⟩ : syracuseStep 3722723 = 5584085) B5584085
theorem B2649619 : Blo 1653526 2649619 := bstep (se 1 (by rfl) ⟨1987214, by rfl⟩ : syracuseStep 2649619 = 3974429) B3974429
theorem B3141155 : Blo 1653526 3141155 := bstep (se 1 (by rfl) ⟨2355866, by rfl⟩ : syracuseStep 3141155 = 4711733) B4711733
theorem B4189745 : Blo 1653526 4189745 := bstep (se 2 (by rfl) ⟨1571154, by rfl⟩ : syracuseStep 4189745 = 3142309) B3142309
theorem B4714033 : Blo 1653526 4714033 := bstep (se 2 (by rfl) ⟨1767762, by rfl⟩ : syracuseStep 4714033 = 3535525) B3535525
theorem B2649665 : Blo 1653526 2649665 := bstep (se 2 (by rfl) ⟨993624, by rfl⟩ : syracuseStep 2649665 = 1987249) B1987249
theorem B8375885 : Blo 1653526 8375885 := bstep (se 3 (by rfl) ⟨1570478, by rfl⟩ : syracuseStep 8375885 = 3140957) B3140957
theorem B6278755 : Blo 1653526 6278755 := bstep (se 1 (by rfl) ⟨4709066, by rfl⟩ : syracuseStep 6278755 = 9418133) B9418133
theorem B10604195 : Blo 1653526 10604195 := bstep (se 1 (by rfl) ⟨7953146, by rfl⟩ : syracuseStep 10604195 = 15906293) B15906293
theorem B4714193 : Blo 1653526 4714193 := bstep (se 2 (by rfl) ⟨1767822, by rfl⟩ : syracuseStep 4714193 = 3535645) B3535645
theorem B5582573 : Blo 1653526 5582573 := bstep (se 3 (by rfl) ⟨1046732, by rfl⟩ : syracuseStep 5582573 = 2093465) B2093465
theorem B5099249 : Blo 1653526 5099249 := bstep (se 2 (by rfl) ⟨1912218, by rfl⟩ : syracuseStep 5099249 = 3824437) B3824437
theorem B3722993 : Blo 1653526 3722993 := bstep (se 2 (by rfl) ⟨1396122, by rfl⟩ : syracuseStep 3722993 = 2792245) B2792245
theorem B3723011 : Blo 1653526 3723011 := bstep (se 1 (by rfl) ⟨2792258, by rfl⟩ : syracuseStep 3723011 = 5584517) B5584517
theorem B5582627 : Blo 1653526 5582627 := bstep (se 1 (by rfl) ⟨4186970, by rfl⟩ : syracuseStep 5582627 = 8373941) B8373941
theorem B3141443 : Blo 1653526 3141443 := bstep (se 1 (by rfl) ⟨2356082, by rfl⟩ : syracuseStep 3141443 = 4712165) B4712165
theorem B4714307 : Blo 1653526 4714307 := bstep (se 1 (by rfl) ⟨3535730, by rfl⟩ : syracuseStep 4714307 = 7071461) B7071461
theorem B6369137 : Blo 1653526 6369137 := bstep (se 2 (by rfl) ⟨2388426, by rfl⟩ : syracuseStep 6369137 = 4776853) B4776853
theorem B2092979 : Blo 1653526 2092979 := bstep (se 1 (by rfl) ⟨1569734, by rfl⟩ : syracuseStep 2092979 = 3139469) B3139469
theorem B3723281 : Blo 1653526 3723281 := bstep (se 2 (by rfl) ⟨1396230, by rfl⟩ : syracuseStep 3723281 = 2792461) B2792461
theorem B3723299 : Blo 1653526 3723299 := bstep (se 1 (by rfl) ⟨2792474, by rfl⟩ : syracuseStep 3723299 = 5584949) B5584949
theorem B5582897 : Blo 1653526 5582897 := bstep (se 2 (by rfl) ⟨2093586, by rfl⟩ : syracuseStep 5582897 = 4187173) B4187173
theorem B3354691 : Blo 1653526 3354691 := bstep (se 1 (by rfl) ⟨2516018, by rfl⟩ : syracuseStep 3354691 = 5032037) B5032037
theorem B2355331 : Blo 1653526 2355331 := bstep (se 1 (by rfl) ⟨1766498, by rfl⟩ : syracuseStep 2355331 = 3532997) B3532997
theorem B3354787 : Blo 1653526 3354787 := bstep (se 1 (by rfl) ⟨2516090, by rfl⟩ : syracuseStep 3354787 = 5032181) B5032181
theorem B2650337 : Blo 1653526 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B1986787 : Blo 1653526 1986787 := bstep (se 1 (by rfl) ⟨1490090, by rfl⟩ : syracuseStep 1986787 = 2980181) B2980181
theorem B8491313 : Blo 1653526 8491313 := bstep (se 2 (by rfl) ⟨3184242, by rfl⟩ : syracuseStep 8491313 = 6368485) B6368485
theorem B3723569 : Blo 1653526 3723569 := bstep (se 2 (by rfl) ⟨1396338, by rfl⟩ : syracuseStep 3723569 = 2792677) B2792677
theorem B3723587 : Blo 1653526 3723587 := bstep (se 1 (by rfl) ⟨2792690, by rfl⟩ : syracuseStep 3723587 = 5585381) B5585381
theorem B14127473 : Blo 1653526 14127473 := bstep (se 2 (by rfl) ⟨5297802, by rfl⟩ : syracuseStep 14127473 = 10595605) B10595605
theorem B3535235 : Blo 1653526 3535235 := bstep (se 1 (by rfl) ⟨2651426, by rfl⟩ : syracuseStep 3535235 = 5302853) B5302853
theorem B7066061 : Blo 1653526 7066061 := bstep (se 3 (by rfl) ⟨1324886, by rfl⟩ : syracuseStep 7066061 = 2649773) B2649773
theorem B10596835 : Blo 1653526 10596835 := bstep (se 1 (by rfl) ⟨7947626, by rfl⟩ : syracuseStep 10596835 = 15895253) B15895253
theorem B2830835 : Blo 1653526 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B5583437 : Blo 1653526 5583437 := bstep (se 3 (by rfl) ⟨1046894, by rfl⟩ : syracuseStep 5583437 = 2093789) B2093789
theorem B3723857 : Blo 1653526 3723857 := bstep (se 2 (by rfl) ⟨1396446, by rfl⟩ : syracuseStep 3723857 = 2792893) B2792893
theorem B2355809 : Blo 1653526 2355809 := bstep (se 2 (by rfl) ⟨883428, by rfl⟩ : syracuseStep 2355809 = 1766857) B1766857
theorem B3723875 : Blo 1653526 3723875 := bstep (se 1 (by rfl) ⟨2792906, by rfl⟩ : syracuseStep 3723875 = 5585813) B5585813
theorem B2093683 : Blo 1653526 2093683 := bstep (se 1 (by rfl) ⟨1570262, by rfl⟩ : syracuseStep 2093683 = 3140525) B3140525
theorem B5583491 : Blo 1653526 5583491 := bstep (se 1 (by rfl) ⟨4187618, by rfl⟩ : syracuseStep 5583491 = 8375237) B8375237
theorem B9425605 : Blo 1653526 9425605 := bstep (se 4 (by rfl) ⟨883650, by rfl⟩ : syracuseStep 9425605 = 1767301) B1767301
theorem B2093779 : Blo 1653526 2093779 := bstep (se 1 (by rfl) ⟨1570334, by rfl⟩ : syracuseStep 2093779 = 3140669) B3140669
theorem B2355923 : Blo 1653526 2355923 := bstep (se 1 (by rfl) ⟨1766942, by rfl⟩ : syracuseStep 2355923 = 3533885) B3533885
theorem B2650849 : Blo 1653526 2650849 := bstep (se 2 (by rfl) ⟨994068, by rfl⟩ : syracuseStep 2650849 = 1988137) B1988137
theorem B3142385 : Blo 1653526 3142385 := bstep (se 2 (by rfl) ⟨1178394, by rfl⟩ : syracuseStep 3142385 = 2356789) B2356789
theorem B7066403 : Blo 1653526 7066403 := bstep (se 1 (by rfl) ⟨5299802, by rfl⟩ : syracuseStep 7066403 = 10599605) B10599605
theorem B2356003 : Blo 1653526 2356003 := bstep (se 1 (by rfl) ⟨1767002, by rfl⟩ : syracuseStep 2356003 = 3534005) B3534005
theorem B3724145 : Blo 1653526 3724145 := bstep (se 2 (by rfl) ⟨1396554, by rfl⟩ : syracuseStep 3724145 = 2793109) B2793109
theorem B3724163 : Blo 1653526 3724163 := bstep (se 1 (by rfl) ⟨2793122, by rfl⟩ : syracuseStep 3724163 = 5586245) B5586245
theorem B5657485 : Blo 1653526 5657485 := bstep (se 3 (by rfl) ⟨1060778, by rfl⟩ : syracuseStep 5657485 = 2121557) B2121557
theorem B15897485 : Blo 1653526 15897485 := bstep (se 3 (by rfl) ⟨2980778, by rfl⟩ : syracuseStep 15897485 = 5961557) B5961557
theorem B5583761 : Blo 1653526 5583761 := bstep (se 2 (by rfl) ⟨2093910, by rfl⟩ : syracuseStep 5583761 = 4187821) B4187821
theorem B2790355 : Blo 1653526 2790355 := bstep (se 1 (by rfl) ⟨2092766, by rfl⟩ : syracuseStep 2790355 = 4185533) B4185533
theorem B2790497 : Blo 1653526 2790497 := bstep (se 2 (by rfl) ⟨1046436, by rfl⟩ : syracuseStep 2790497 = 2092873) B2092873
theorem B3724433 : Blo 1653526 3724433 := bstep (se 2 (by rfl) ⟨1396662, by rfl⟩ : syracuseStep 3724433 = 2793325) B2793325
theorem B3724451 : Blo 1653526 3724451 := bstep (se 1 (by rfl) ⟨2793338, by rfl⟩ : syracuseStep 3724451 = 5586677) B5586677
theorem B2094275 : Blo 1653526 2094275 := bstep (se 1 (by rfl) ⟨1570706, by rfl⟩ : syracuseStep 2094275 = 3141413) B3141413
theorem B2790625 : Blo 1653526 2790625 := bstep (se 2 (by rfl) ⟨1046484, by rfl⟩ : syracuseStep 2790625 = 2092969) B2092969
theorem B5297393 : Blo 1653526 5297393 := bstep (se 2 (by rfl) ⟨1986522, by rfl⟩ : syracuseStep 5297393 = 3973045) B3973045
theorem B7066865 : Blo 1653526 7066865 := bstep (se 2 (by rfl) ⟨2650074, by rfl⟩ : syracuseStep 7066865 = 5300149) B5300149
theorem B2790659 : Blo 1653526 2790659 := bstep (se 1 (by rfl) ⟨2092994, by rfl⟩ : syracuseStep 2790659 = 4185989) B4185989
theorem B4027715 : Blo 1653526 4027715 := bstep (se 1 (by rfl) ⟨3020786, by rfl⟩ : syracuseStep 4027715 = 6041573) B6041573
theorem B2356561 : Blo 1653526 2356561 := bstep (se 2 (by rfl) ⟨883710, by rfl⟩ : syracuseStep 2356561 = 1767421) B1767421
theorem B2790787 : Blo 1653526 2790787 := bstep (se 1 (by rfl) ⟨2093090, by rfl⟩ : syracuseStep 2790787 = 4186181) B4186181
theorem B2454931 : Blo 1653526 2454931 := bstep (se 1 (by rfl) ⟨1841198, by rfl⟩ : syracuseStep 2454931 = 3682397) B3682397
theorem B1766819 : Blo 1653526 1766819 := bstep (se 1 (by rfl) ⟨1325114, by rfl⟩ : syracuseStep 1766819 = 2650229) B2650229
theorem B5584301 : Blo 1653526 5584301 := bstep (se 3 (by rfl) ⟨1047056, by rfl⟩ : syracuseStep 5584301 = 2094113) B2094113
theorem B3724721 : Blo 1653526 3724721 := bstep (se 2 (by rfl) ⟨1396770, by rfl⟩ : syracuseStep 3724721 = 2793541) B2793541
theorem B3724739 : Blo 1653526 3724739 := bstep (se 1 (by rfl) ⟨2793554, by rfl⟩ : syracuseStep 3724739 = 5587109) B5587109
theorem B21190085 : Blo 1653526 21190085 := bstep (se 4 (by rfl) ⟨1986570, by rfl⟩ : syracuseStep 21190085 = 3973141) B3973141
theorem B10597837 : Blo 1653526 10597837 := bstep (se 3 (by rfl) ⟨1987094, by rfl⟩ : syracuseStep 10597837 = 3974189) B3974189
theorem B23852515 : Blo 1653526 23852515 := bstep (se 1 (by rfl) ⟨17889386, by rfl⟩ : syracuseStep 23852515 = 35778773) B35778773
theorem B5584355 : Blo 1653526 5584355 := bstep (se 1 (by rfl) ⟨4188266, by rfl⟩ : syracuseStep 5584355 = 8376533) B8376533
theorem B5977613 : Blo 1653526 5977613 := bstep (se 3 (by rfl) ⟨1120802, by rfl⟩ : syracuseStep 5977613 = 2241605) B2241605
theorem B2790929 : Blo 1653526 2790929 := bstep (se 2 (by rfl) ⟨1046598, by rfl⟩ : syracuseStep 2790929 = 2093197) B2093197
theorem B2791057 : Blo 1653526 2791057 := bstep (se 2 (by rfl) ⟨1046646, by rfl⟩ : syracuseStep 2791057 = 2093293) B2093293
theorem B2791091 : Blo 1653526 2791091 := bstep (se 1 (by rfl) ⟨2093318, by rfl⟩ : syracuseStep 2791091 = 4186637) B4186637
theorem B8943331 : Blo 1653526 8943331 := bstep (se 1 (by rfl) ⟨6707498, by rfl⟩ : syracuseStep 8943331 = 13414997) B13414997
theorem B5584625 : Blo 1653526 5584625 := bstep (se 2 (by rfl) ⟨2094234, by rfl⟩ : syracuseStep 5584625 = 4188469) B4188469
theorem B6280973 : Blo 1653526 6280973 := bstep (se 3 (by rfl) ⟨1177682, by rfl⟩ : syracuseStep 6280973 = 2355365) B2355365
theorem B6706979 : Blo 1653526 6706979 := bstep (se 1 (by rfl) ⟨5030234, by rfl⟩ : syracuseStep 6706979 = 10060469) B10060469
theorem B2791219 : Blo 1653526 2791219 := bstep (se 1 (by rfl) ⟨2093414, by rfl⟩ : syracuseStep 2791219 = 4186829) B4186829
theorem B1988483 : Blo 1653526 1988483 := bstep (se 1 (by rfl) ⟨1491362, by rfl⟩ : syracuseStep 1988483 = 2982725) B2982725
theorem B2094979 : Blo 1653526 2094979 := bstep (se 1 (by rfl) ⟨1571234, by rfl⟩ : syracuseStep 2094979 = 3142469) B3142469
theorem B2791361 : Blo 1653526 2791361 := bstep (se 2 (by rfl) ⟨1046760, by rfl⟩ : syracuseStep 2791361 = 2093521) B2093521
theorem B2095075 : Blo 1653526 2095075 := bstep (se 1 (by rfl) ⟨1571306, by rfl⟩ : syracuseStep 2095075 = 3142613) B3142613
theorem B2791489 : Blo 1653526 2791489 := bstep (se 2 (by rfl) ⟨1046808, by rfl⟩ : syracuseStep 2791489 = 2093617) B2093617
theorem B2791523 : Blo 1653526 2791523 := bstep (se 1 (by rfl) ⟨2093642, by rfl⟩ : syracuseStep 2791523 = 4187285) B4187285
theorem B2480291 : Blo 1653526 2480291 := bstep (se 1 (by rfl) ⟨1860218, by rfl⟩ : syracuseStep 2480291 = 3720437) B3720437
theorem B2480321 : Blo 1653526 2480321 := bstep (se 2 (by rfl) ⟨930120, by rfl⟩ : syracuseStep 2480321 = 1860241) B1860241
theorem B2480339 : Blo 1653526 2480339 := bstep (se 1 (by rfl) ⟨1860254, by rfl⟩ : syracuseStep 2480339 = 3720509) B3720509
theorem B2791651 : Blo 1653526 2791651 := bstep (se 1 (by rfl) ⟨2093738, by rfl⟩ : syracuseStep 2791651 = 4187477) B4187477
theorem B22640867 : Blo 1653526 22640867 := bstep (se 1 (by rfl) ⟨16980650, by rfl⟩ : syracuseStep 22640867 = 33961301) B33961301
theorem B8493283 : Blo 1653526 8493283 := bstep (se 1 (by rfl) ⟨6369962, by rfl⟩ : syracuseStep 8493283 = 12739925) B12739925
theorem B2480369 : Blo 1653526 2480369 := bstep (se 2 (by rfl) ⟨930138, by rfl⟩ : syracuseStep 2480369 = 1860277) B1860277
theorem B2480387 : Blo 1653526 2480387 := bstep (se 1 (by rfl) ⟨1860290, by rfl⟩ : syracuseStep 2480387 = 3720581) B3720581
theorem B5585165 : Blo 1653526 5585165 := bstep (se 3 (by rfl) ⟨1047218, by rfl⟩ : syracuseStep 5585165 = 2094437) B2094437
theorem B2480417 : Blo 1653526 2480417 := bstep (se 2 (by rfl) ⟨930156, by rfl⟩ : syracuseStep 2480417 = 1860313) B1860313
theorem B2480435 : Blo 1653526 2480435 := bstep (se 1 (by rfl) ⟨1860326, by rfl⟩ : syracuseStep 2480435 = 3720653) B3720653
theorem B5585219 : Blo 1653526 5585219 := bstep (se 1 (by rfl) ⟨4188914, by rfl⟩ : syracuseStep 5585219 = 8377829) B8377829
theorem B5298509 : Blo 1653526 5298509 := bstep (se 3 (by rfl) ⟨993470, by rfl⟩ : syracuseStep 5298509 = 1986941) B1986941
theorem B2480465 : Blo 1653526 2480465 := bstep (se 2 (by rfl) ⟨930174, by rfl⟩ : syracuseStep 2480465 = 1860349) B1860349
theorem B2480483 : Blo 1653526 2480483 := bstep (se 1 (by rfl) ⟨1860362, by rfl⟩ : syracuseStep 2480483 = 3720725) B3720725
theorem B2791793 : Blo 1653526 2791793 := bstep (se 2 (by rfl) ⟨1046922, by rfl⟩ : syracuseStep 2791793 = 2093845) B2093845
theorem B2480513 : Blo 1653526 2480513 := bstep (se 2 (by rfl) ⟨930192, by rfl⟩ : syracuseStep 2480513 = 1860385) B1860385
theorem B2685329 : Blo 1653526 2685329 := bstep (se 2 (by rfl) ⟨1006998, by rfl⟩ : syracuseStep 2685329 = 2013997) B2013997
theorem B2480531 : Blo 1653526 2480531 := bstep (se 1 (by rfl) ⟨1860398, by rfl⟩ : syracuseStep 2480531 = 3720797) B3720797
theorem B2480561 : Blo 1653526 2480561 := bstep (se 2 (by rfl) ⟨930210, by rfl⟩ : syracuseStep 2480561 = 1860421) B1860421
theorem B8378801 : Blo 1653526 8378801 := bstep (se 2 (by rfl) ⟨3142050, by rfl⟩ : syracuseStep 8378801 = 6284101) B6284101
theorem B2480579 : Blo 1653526 2480579 := bstep (se 1 (by rfl) ⟨1860434, by rfl⟩ : syracuseStep 2480579 = 3720869) B3720869
theorem B4708817 : Blo 1653526 4708817 := bstep (se 2 (by rfl) ⟨1765806, by rfl⟩ : syracuseStep 4708817 = 3531613) B3531613
theorem B2480609 : Blo 1653526 2480609 := bstep (se 2 (by rfl) ⟨930228, by rfl⟩ : syracuseStep 2480609 = 1860457) B1860457
theorem B2791921 : Blo 1653526 2791921 := bstep (se 2 (by rfl) ⟨1046970, by rfl⟩ : syracuseStep 2791921 = 2093941) B2093941
theorem B2480627 : Blo 1653526 2480627 := bstep (se 1 (by rfl) ⟨1860470, by rfl⟩ : syracuseStep 2480627 = 3720941) B3720941
theorem B2480657 : Blo 1653526 2480657 := bstep (se 2 (by rfl) ⟨930246, by rfl⟩ : syracuseStep 2480657 = 1860493) B1860493
theorem B2791955 : Blo 1653526 2791955 := bstep (se 1 (by rfl) ⟨2093966, by rfl⟩ : syracuseStep 2791955 = 4187933) B4187933
theorem B2480675 : Blo 1653526 2480675 := bstep (se 1 (by rfl) ⟨1860506, by rfl⟩ : syracuseStep 2480675 = 3721013) B3721013
theorem B9812515 : Blo 1653526 9812515 := bstep (se 1 (by rfl) ⟨7359386, by rfl⟩ : syracuseStep 9812515 = 14718773) B14718773
theorem B2480705 : Blo 1653526 2480705 := bstep (se 2 (by rfl) ⟨930264, by rfl⟩ : syracuseStep 2480705 = 1860529) B1860529
theorem B2980433 : Blo 1653526 2980433 := bstep (se 2 (by rfl) ⟨1117662, by rfl⟩ : syracuseStep 2980433 = 2235325) B2235325
theorem B5585489 : Blo 1653526 5585489 := bstep (se 2 (by rfl) ⟨2094558, by rfl⟩ : syracuseStep 5585489 = 4189117) B4189117
theorem B2480723 : Blo 1653526 2480723 := bstep (se 1 (by rfl) ⟨1860542, by rfl⟩ : syracuseStep 2480723 = 3721085) B3721085
theorem B4471405 : Blo 1653526 4471405 := bstep (se 3 (by rfl) ⟨838388, by rfl⟩ : syracuseStep 4471405 = 1676777) B1676777
theorem B2480753 : Blo 1653526 2480753 := bstep (se 2 (by rfl) ⟨930282, by rfl⟩ : syracuseStep 2480753 = 1860565) B1860565
theorem B2480771 : Blo 1653526 2480771 := bstep (se 1 (by rfl) ⟨1860578, by rfl⟩ : syracuseStep 2480771 = 3721157) B3721157
theorem B9427589 : Blo 1653526 9427589 := bstep (se 4 (by rfl) ⟨883836, by rfl⟩ : syracuseStep 9427589 = 1767673) B1767673
theorem B2792083 : Blo 1653526 2792083 := bstep (se 1 (by rfl) ⟨2094062, by rfl⟩ : syracuseStep 2792083 = 4188125) B4188125
theorem B2480801 : Blo 1653526 2480801 := bstep (se 2 (by rfl) ⟨930300, by rfl⟩ : syracuseStep 2480801 = 1860601) B1860601
theorem B2480819 : Blo 1653526 2480819 := bstep (se 1 (by rfl) ⟨1860614, by rfl⟩ : syracuseStep 2480819 = 3721229) B3721229
theorem B2480849 : Blo 1653526 2480849 := bstep (se 2 (by rfl) ⟨930318, by rfl⟩ : syracuseStep 2480849 = 1860637) B1860637
theorem B2480867 : Blo 1653526 2480867 := bstep (se 1 (by rfl) ⟨1860650, by rfl⟩ : syracuseStep 2480867 = 3721301) B3721301
theorem B5962481 : Blo 1653526 5962481 := bstep (se 2 (by rfl) ⟨2235930, by rfl⟩ : syracuseStep 5962481 = 4471861) B4471861
theorem B2480897 : Blo 1653526 2480897 := bstep (se 2 (by rfl) ⟨930336, by rfl⟩ : syracuseStep 2480897 = 1860673) B1860673
theorem B2480915 : Blo 1653526 2480915 := bstep (se 1 (by rfl) ⟨1860686, by rfl⟩ : syracuseStep 2480915 = 3721373) B3721373
theorem B2792225 : Blo 1653526 2792225 := bstep (se 2 (by rfl) ⟨1047084, by rfl⟩ : syracuseStep 2792225 = 2094169) B2094169
theorem B1653539 : Blo 1653526 1653539 := bstep (se 1 (by rfl) ⟨1240154, by rfl⟩ : syracuseStep 1653539 = 2480309) B2480309
theorem B7543601 : Blo 1653526 7543601 := bstep (se 2 (by rfl) ⟨2828850, by rfl⟩ : syracuseStep 7543601 = 5657701) B5657701
theorem B2480945 : Blo 1653526 2480945 := bstep (se 2 (by rfl) ⟨930354, by rfl⟩ : syracuseStep 2480945 = 1860709) B1860709
theorem B1653555 : Blo 1653526 1653555 := bstep (se 1 (by rfl) ⟨1240166, by rfl⟩ : syracuseStep 1653555 = 2480333) B2480333
theorem B6708017 : Blo 1653526 6708017 := bstep (se 2 (by rfl) ⟨2515506, by rfl⟩ : syracuseStep 6708017 = 5031013) B5031013
theorem B1653571 : Blo 1653526 1653571 := bstep (se 1 (by rfl) ⟨1240178, by rfl⟩ : syracuseStep 1653571 = 2480357) B2480357
theorem B2480963 : Blo 1653526 2480963 := bstep (se 1 (by rfl) ⟨1860722, by rfl⟩ : syracuseStep 2480963 = 3721445) B3721445
theorem B1653587 : Blo 1653526 1653587 := bstep (se 1 (by rfl) ⟨1240190, by rfl⟩ : syracuseStep 1653587 = 2480381) B2480381
theorem B2480993 : Blo 1653526 2480993 := bstep (se 2 (by rfl) ⟨930372, by rfl⟩ : syracuseStep 2480993 = 1860745) B1860745
theorem B1653603 : Blo 1653526 1653603 := bstep (se 1 (by rfl) ⟨1240202, by rfl⟩ : syracuseStep 1653603 = 2480405) B2480405
theorem B1653619 : Blo 1653526 1653619 := bstep (se 1 (by rfl) ⟨1240214, by rfl⟩ : syracuseStep 1653619 = 2480429) B2480429
theorem B2481011 : Blo 1653526 2481011 := bstep (se 1 (by rfl) ⟨1860758, by rfl⟩ : syracuseStep 2481011 = 3721517) B3721517
theorem B1653635 : Blo 1653526 1653635 := bstep (se 1 (by rfl) ⟨1240226, by rfl⟩ : syracuseStep 1653635 = 2480453) B2480453
theorem B2481041 : Blo 1653526 2481041 := bstep (se 2 (by rfl) ⟨930390, by rfl⟩ : syracuseStep 2481041 = 1860781) B1860781
theorem B1653651 : Blo 1653526 1653651 := bstep (se 1 (by rfl) ⟨1240238, by rfl⟩ : syracuseStep 1653651 = 2480477) B2480477
theorem B2792353 : Blo 1653526 2792353 := bstep (se 2 (by rfl) ⟨1047132, by rfl⟩ : syracuseStep 2792353 = 2094265) B2094265
theorem B1653667 : Blo 1653526 1653667 := bstep (se 1 (by rfl) ⟨1240250, by rfl⟩ : syracuseStep 1653667 = 2480501) B2480501
theorem B2481059 : Blo 1653526 2481059 := bstep (se 1 (by rfl) ⟨1860794, by rfl⟩ : syracuseStep 2481059 = 3721589) B3721589
theorem B1653683 : Blo 1653526 1653683 := bstep (se 1 (by rfl) ⟨1240262, by rfl⟩ : syracuseStep 1653683 = 2480525) B2480525
theorem B2481089 : Blo 1653526 2481089 := bstep (se 2 (by rfl) ⟨930408, by rfl⟩ : syracuseStep 2481089 = 1860817) B1860817
theorem B1653699 : Blo 1653526 1653699 := bstep (se 1 (by rfl) ⟨1240274, by rfl⟩ : syracuseStep 1653699 = 2480549) B2480549
theorem B2792387 : Blo 1653526 2792387 := bstep (se 1 (by rfl) ⟨2094290, by rfl⟩ : syracuseStep 2792387 = 4188581) B4188581
theorem B1653715 : Blo 1653526 1653715 := bstep (se 1 (by rfl) ⟨1240286, by rfl⟩ : syracuseStep 1653715 = 2480573) B2480573
theorem B2481107 : Blo 1653526 2481107 := bstep (se 1 (by rfl) ⟨1860830, by rfl⟩ : syracuseStep 2481107 = 3721661) B3721661
theorem B1653731 : Blo 1653526 1653731 := bstep (se 1 (by rfl) ⟨1240298, by rfl⟩ : syracuseStep 1653731 = 2480597) B2480597
theorem B2481137 : Blo 1653526 2481137 := bstep (se 2 (by rfl) ⟨930426, by rfl⟩ : syracuseStep 2481137 = 1860853) B1860853
theorem B1653747 : Blo 1653526 1653747 := bstep (se 1 (by rfl) ⟨1240310, by rfl⟩ : syracuseStep 1653747 = 2480621) B2480621
theorem B1653763 : Blo 1653526 1653763 := bstep (se 1 (by rfl) ⟨1240322, by rfl⟩ : syracuseStep 1653763 = 2480645) B2480645
theorem B2481155 : Blo 1653526 2481155 := bstep (se 1 (by rfl) ⟨1860866, by rfl⟩ : syracuseStep 2481155 = 3721733) B3721733
theorem B1653779 : Blo 1653526 1653779 := bstep (se 1 (by rfl) ⟨1240334, by rfl⟩ : syracuseStep 1653779 = 2480669) B2480669
theorem B2481185 : Blo 1653526 2481185 := bstep (se 2 (by rfl) ⟨930444, by rfl⟩ : syracuseStep 2481185 = 1860889) B1860889
theorem B1653795 : Blo 1653526 1653795 := bstep (se 1 (by rfl) ⟨1240346, by rfl⟩ : syracuseStep 1653795 = 2480693) B2480693
theorem B1653811 : Blo 1653526 1653811 := bstep (se 1 (by rfl) ⟨1240358, by rfl⟩ : syracuseStep 1653811 = 2480717) B2480717
theorem B2235443 : Blo 1653526 2235443 := bstep (se 1 (by rfl) ⟨1676582, by rfl⟩ : syracuseStep 2235443 = 3353165) B3353165
theorem B2481203 : Blo 1653526 2481203 := bstep (se 1 (by rfl) ⟨1860902, by rfl⟩ : syracuseStep 2481203 = 3721805) B3721805
theorem B1653827 : Blo 1653526 1653827 := bstep (se 1 (by rfl) ⟨1240370, by rfl⟩ : syracuseStep 1653827 = 2480741) B2480741
theorem B2792515 : Blo 1653526 2792515 := bstep (se 1 (by rfl) ⟨2094386, by rfl⟩ : syracuseStep 2792515 = 4188773) B4188773
theorem B2481233 : Blo 1653526 2481233 := bstep (se 2 (by rfl) ⟨930462, by rfl⟩ : syracuseStep 2481233 = 1860925) B1860925
theorem B1653843 : Blo 1653526 1653843 := bstep (se 1 (by rfl) ⟨1240382, by rfl⟩ : syracuseStep 1653843 = 2480765) B2480765
theorem B1653859 : Blo 1653526 1653859 := bstep (se 1 (by rfl) ⟨1240394, by rfl⟩ : syracuseStep 1653859 = 2480789) B2480789
theorem B2481251 : Blo 1653526 2481251 := bstep (se 1 (by rfl) ⟨1860938, by rfl⟩ : syracuseStep 2481251 = 3721877) B3721877
theorem B5586029 : Blo 1653526 5586029 := bstep (se 3 (by rfl) ⟨1047380, by rfl⟩ : syracuseStep 5586029 = 2094761) B2094761
theorem B1653875 : Blo 1653526 1653875 := bstep (se 1 (by rfl) ⟨1240406, by rfl⟩ : syracuseStep 1653875 = 2480813) B2480813
theorem B2481281 : Blo 1653526 2481281 := bstep (se 2 (by rfl) ⟨930480, by rfl⟩ : syracuseStep 2481281 = 1860961) B1860961
theorem B1653891 : Blo 1653526 1653891 := bstep (se 1 (by rfl) ⟨1240418, by rfl⟩ : syracuseStep 1653891 = 2480837) B2480837
theorem B1653907 : Blo 1653526 1653907 := bstep (se 1 (by rfl) ⟨1240430, by rfl⟩ : syracuseStep 1653907 = 2480861) B2480861
theorem B2481299 : Blo 1653526 2481299 := bstep (se 1 (by rfl) ⟨1860974, by rfl⟩ : syracuseStep 2481299 = 3721949) B3721949
theorem B1653923 : Blo 1653526 1653923 := bstep (se 1 (by rfl) ⟨1240442, by rfl⟩ : syracuseStep 1653923 = 2480885) B2480885
theorem B5586083 : Blo 1653526 5586083 := bstep (se 1 (by rfl) ⟨4189562, by rfl⟩ : syracuseStep 5586083 = 8379125) B8379125
theorem B2481329 : Blo 1653526 2481329 := bstep (se 2 (by rfl) ⟨930498, by rfl⟩ : syracuseStep 2481329 = 1860997) B1860997
theorem B1653939 : Blo 1653526 1653939 := bstep (se 1 (by rfl) ⟨1240454, by rfl⟩ : syracuseStep 1653939 = 2480909) B2480909
theorem B1653955 : Blo 1653526 1653955 := bstep (se 1 (by rfl) ⟨1240466, by rfl⟩ : syracuseStep 1653955 = 2480933) B2480933
theorem B2481347 : Blo 1653526 2481347 := bstep (se 1 (by rfl) ⟨1861010, by rfl⟩ : syracuseStep 2481347 = 3722021) B3722021
theorem B2792657 : Blo 1653526 2792657 := bstep (se 2 (by rfl) ⟨1047246, by rfl⟩ : syracuseStep 2792657 = 2094493) B2094493
theorem B3316945 : Blo 1653526 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B1653971 : Blo 1653526 1653971 := bstep (se 1 (by rfl) ⟨1240478, by rfl⟩ : syracuseStep 1653971 = 2480957) B2480957
theorem B2514145 : Blo 1653526 2514145 := bstep (se 2 (by rfl) ⟨942804, by rfl⟩ : syracuseStep 2514145 = 1885609) B1885609
theorem B2481377 : Blo 1653526 2481377 := bstep (se 2 (by rfl) ⟨930516, by rfl⟩ : syracuseStep 2481377 = 1861033) B1861033
theorem B4709603 : Blo 1653526 4709603 := bstep (se 1 (by rfl) ⟨3532202, by rfl⟩ : syracuseStep 4709603 = 7064405) B7064405
theorem B1653987 : Blo 1653526 1653987 := bstep (se 1 (by rfl) ⟨1240490, by rfl⟩ : syracuseStep 1653987 = 2480981) B2480981
theorem B1654003 : Blo 1653526 1654003 := bstep (se 1 (by rfl) ⟨1240502, by rfl⟩ : syracuseStep 1654003 = 2481005) B2481005
theorem B2481395 : Blo 1653526 2481395 := bstep (se 1 (by rfl) ⟨1861046, by rfl⟩ : syracuseStep 2481395 = 3722093) B3722093
theorem B1654019 : Blo 1653526 1654019 := bstep (se 1 (by rfl) ⟨1240514, by rfl⟩ : syracuseStep 1654019 = 2481029) B2481029
theorem B2481425 : Blo 1653526 2481425 := bstep (se 2 (by rfl) ⟨930534, by rfl⟩ : syracuseStep 2481425 = 1861069) B1861069
theorem B1654035 : Blo 1653526 1654035 := bstep (se 1 (by rfl) ⟨1240526, by rfl⟩ : syracuseStep 1654035 = 2481053) B2481053
theorem B1654051 : Blo 1653526 1654051 := bstep (se 1 (by rfl) ⟨1240538, by rfl⟩ : syracuseStep 1654051 = 2481077) B2481077
theorem B2481443 : Blo 1653526 2481443 := bstep (se 1 (by rfl) ⟨1861082, by rfl⟩ : syracuseStep 2481443 = 3722165) B3722165
theorem B1654067 : Blo 1653526 1654067 := bstep (se 1 (by rfl) ⟨1240550, by rfl⟩ : syracuseStep 1654067 = 2481101) B2481101
theorem B2481473 : Blo 1653526 2481473 := bstep (se 2 (by rfl) ⟨930552, by rfl⟩ : syracuseStep 2481473 = 1861105) B1861105
theorem B1654083 : Blo 1653526 1654083 := bstep (se 1 (by rfl) ⟨1240562, by rfl⟩ : syracuseStep 1654083 = 2481125) B2481125
theorem B2792785 : Blo 1653526 2792785 := bstep (se 2 (by rfl) ⟨1047294, by rfl⟩ : syracuseStep 2792785 = 2094589) B2094589
theorem B1654099 : Blo 1653526 1654099 := bstep (se 1 (by rfl) ⟨1240574, by rfl⟩ : syracuseStep 1654099 = 2481149) B2481149
theorem B2481491 : Blo 1653526 2481491 := bstep (se 1 (by rfl) ⟨1861118, by rfl⟩ : syracuseStep 2481491 = 3722237) B3722237
theorem B1654115 : Blo 1653526 1654115 := bstep (se 1 (by rfl) ⟨1240586, by rfl⟩ : syracuseStep 1654115 = 2481173) B2481173
theorem B2481521 : Blo 1653526 2481521 := bstep (se 2 (by rfl) ⟨930570, by rfl⟩ : syracuseStep 2481521 = 1861141) B1861141
theorem B1654131 : Blo 1653526 1654131 := bstep (se 1 (by rfl) ⟨1240598, by rfl⟩ : syracuseStep 1654131 = 2481197) B2481197
theorem B2792819 : Blo 1653526 2792819 := bstep (se 1 (by rfl) ⟨2094614, by rfl⟩ : syracuseStep 2792819 = 4189229) B4189229
theorem B1654147 : Blo 1653526 1654147 := bstep (se 1 (by rfl) ⟨1240610, by rfl⟩ : syracuseStep 1654147 = 2481221) B2481221
theorem B2481539 : Blo 1653526 2481539 := bstep (se 1 (by rfl) ⟨1861154, by rfl⟩ : syracuseStep 2481539 = 3722309) B3722309
theorem B5299597 : Blo 1653526 5299597 := bstep (se 3 (by rfl) ⟨993674, by rfl⟩ : syracuseStep 5299597 = 1987349) B1987349
theorem B1654163 : Blo 1653526 1654163 := bstep (se 1 (by rfl) ⟨1240622, by rfl⟩ : syracuseStep 1654163 = 2481245) B2481245
theorem B2481569 : Blo 1653526 2481569 := bstep (se 2 (by rfl) ⟨930588, by rfl⟩ : syracuseStep 2481569 = 1861177) B1861177
theorem B1654179 : Blo 1653526 1654179 := bstep (se 1 (by rfl) ⟨1240634, by rfl⟩ : syracuseStep 1654179 = 2481269) B2481269
theorem B5586353 : Blo 1653526 5586353 := bstep (se 2 (by rfl) ⟨2094882, by rfl⟩ : syracuseStep 5586353 = 4189765) B4189765
theorem B1654195 : Blo 1653526 1654195 := bstep (se 1 (by rfl) ⟨1240646, by rfl⟩ : syracuseStep 1654195 = 2481293) B2481293
theorem B2481587 : Blo 1653526 2481587 := bstep (se 1 (by rfl) ⟨1861190, by rfl⟩ : syracuseStep 2481587 = 3722381) B3722381
theorem B1654211 : Blo 1653526 1654211 := bstep (se 1 (by rfl) ⟨1240658, by rfl⟩ : syracuseStep 1654211 = 2481317) B2481317
theorem B4185553 : Blo 1653526 4185553 := bstep (se 2 (by rfl) ⟨1569582, by rfl⟩ : syracuseStep 4185553 = 3139165) B3139165
theorem B2481617 : Blo 1653526 2481617 := bstep (se 2 (by rfl) ⟨930606, by rfl⟩ : syracuseStep 2481617 = 1861213) B1861213
theorem B1654227 : Blo 1653526 1654227 := bstep (se 1 (by rfl) ⟨1240670, by rfl⟩ : syracuseStep 1654227 = 2481341) B2481341
theorem B1654243 : Blo 1653526 1654243 := bstep (se 1 (by rfl) ⟨1240682, by rfl⟩ : syracuseStep 1654243 = 2481365) B2481365
theorem B2481635 : Blo 1653526 2481635 := bstep (se 1 (by rfl) ⟨1861226, by rfl⟩ : syracuseStep 2481635 = 3722453) B3722453
theorem B1654259 : Blo 1653526 1654259 := bstep (se 1 (by rfl) ⟨1240694, by rfl⟩ : syracuseStep 1654259 = 2481389) B2481389
theorem B2792947 : Blo 1653526 2792947 := bstep (se 1 (by rfl) ⟨2094710, by rfl⟩ : syracuseStep 2792947 = 4189421) B4189421
theorem B2481665 : Blo 1653526 2481665 := bstep (se 2 (by rfl) ⟨930624, by rfl⟩ : syracuseStep 2481665 = 1861249) B1861249
theorem B1654275 : Blo 1653526 1654275 := bstep (se 1 (by rfl) ⟨1240706, by rfl⟩ : syracuseStep 1654275 = 2481413) B2481413
theorem B1654291 : Blo 1653526 1654291 := bstep (se 1 (by rfl) ⟨1240718, by rfl⟩ : syracuseStep 1654291 = 2481437) B2481437
theorem B2481683 : Blo 1653526 2481683 := bstep (se 1 (by rfl) ⟨1861262, by rfl⟩ : syracuseStep 2481683 = 3722525) B3722525
theorem B1654307 : Blo 1653526 1654307 := bstep (se 1 (by rfl) ⟨1240730, by rfl⟩ : syracuseStep 1654307 = 2481461) B2481461
theorem B4709933 : Blo 1653526 4709933 := bstep (se 3 (by rfl) ⟨883112, by rfl⟩ : syracuseStep 4709933 = 1766225) B1766225
theorem B2481713 : Blo 1653526 2481713 := bstep (se 2 (by rfl) ⟨930642, by rfl⟩ : syracuseStep 2481713 = 1861285) B1861285
theorem B1654323 : Blo 1653526 1654323 := bstep (se 1 (by rfl) ⟨1240742, by rfl⟩ : syracuseStep 1654323 = 2481485) B2481485
theorem B1654339 : Blo 1653526 1654339 := bstep (se 1 (by rfl) ⟨1240754, by rfl⟩ : syracuseStep 1654339 = 2481509) B2481509
theorem B2481731 : Blo 1653526 2481731 := bstep (se 1 (by rfl) ⟨1861298, by rfl⟩ : syracuseStep 2481731 = 3722597) B3722597
theorem B1654355 : Blo 1653526 1654355 := bstep (se 1 (by rfl) ⟨1240766, by rfl⟩ : syracuseStep 1654355 = 2481533) B2481533
theorem B2481761 : Blo 1653526 2481761 := bstep (se 2 (by rfl) ⟨930660, by rfl⟩ : syracuseStep 2481761 = 1861321) B1861321
theorem B1654371 : Blo 1653526 1654371 := bstep (se 1 (by rfl) ⟨1240778, by rfl⟩ : syracuseStep 1654371 = 2481557) B2481557
theorem B4710001 : Blo 1653526 4710001 := bstep (se 2 (by rfl) ⟨1766250, by rfl⟩ : syracuseStep 4710001 = 3532501) B3532501
theorem B1654387 : Blo 1653526 1654387 := bstep (se 1 (by rfl) ⟨1240790, by rfl⟩ : syracuseStep 1654387 = 2481581) B2481581
theorem B2481779 : Blo 1653526 2481779 := bstep (se 1 (by rfl) ⟨1861334, by rfl⟩ : syracuseStep 2481779 = 3722669) B3722669
theorem B2793089 : Blo 1653526 2793089 := bstep (se 2 (by rfl) ⟨1047408, by rfl⟩ : syracuseStep 2793089 = 2094817) B2094817
theorem B1654403 : Blo 1653526 1654403 := bstep (se 1 (by rfl) ⟨1240802, by rfl⟩ : syracuseStep 1654403 = 2481605) B2481605
theorem B2481809 : Blo 1653526 2481809 := bstep (se 2 (by rfl) ⟨930678, by rfl⟩ : syracuseStep 2481809 = 1861357) B1861357
theorem B1654419 : Blo 1653526 1654419 := bstep (se 1 (by rfl) ⟨1240814, by rfl⟩ : syracuseStep 1654419 = 2481629) B2481629
theorem B1654435 : Blo 1653526 1654435 := bstep (se 1 (by rfl) ⟨1240826, by rfl⟩ : syracuseStep 1654435 = 2481653) B2481653
theorem B2481827 : Blo 1653526 2481827 := bstep (se 1 (by rfl) ⟨1861370, by rfl⟩ : syracuseStep 2481827 = 3722741) B3722741
theorem B1654451 : Blo 1653526 1654451 := bstep (se 1 (by rfl) ⟨1240838, by rfl⟩ : syracuseStep 1654451 = 2481677) B2481677
theorem B2481857 : Blo 1653526 2481857 := bstep (se 2 (by rfl) ⟨930696, by rfl⟩ : syracuseStep 2481857 = 1861393) B1861393
theorem B1654467 : Blo 1653526 1654467 := bstep (se 1 (by rfl) ⟨1240850, by rfl⟩ : syracuseStep 1654467 = 2481701) B2481701
theorem B1654483 : Blo 1653526 1654483 := bstep (se 1 (by rfl) ⟨1240862, by rfl⟩ : syracuseStep 1654483 = 2481725) B2481725
theorem B2481875 : Blo 1653526 2481875 := bstep (se 1 (by rfl) ⟨1861406, by rfl⟩ : syracuseStep 2481875 = 3722813) B3722813
theorem B4185827 : Blo 1653526 4185827 := bstep (se 1 (by rfl) ⟨3139370, by rfl⟩ : syracuseStep 4185827 = 6278741) B6278741
theorem B1654499 : Blo 1653526 1654499 := bstep (se 1 (by rfl) ⟨1240874, by rfl⟩ : syracuseStep 1654499 = 2481749) B2481749
theorem B2481905 : Blo 1653526 2481905 := bstep (se 2 (by rfl) ⟨930714, by rfl⟩ : syracuseStep 2481905 = 1861429) B1861429
theorem B1654515 : Blo 1653526 1654515 := bstep (se 1 (by rfl) ⟨1240886, by rfl⟩ : syracuseStep 1654515 = 2481773) B2481773
theorem B2793217 : Blo 1653526 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B1654531 : Blo 1653526 1654531 := bstep (se 1 (by rfl) ⟨1240898, by rfl⟩ : syracuseStep 1654531 = 2481797) B2481797
theorem B2481923 : Blo 1653526 2481923 := bstep (se 1 (by rfl) ⟨1861442, by rfl⟩ : syracuseStep 2481923 = 3722885) B3722885
theorem B1654547 : Blo 1653526 1654547 := bstep (se 1 (by rfl) ⟨1240910, by rfl⟩ : syracuseStep 1654547 = 2481821) B2481821
theorem B2481953 : Blo 1653526 2481953 := bstep (se 2 (by rfl) ⟨930732, by rfl⟩ : syracuseStep 2481953 = 1861465) B1861465
theorem B1654563 : Blo 1653526 1654563 := bstep (se 1 (by rfl) ⟨1240922, by rfl⟩ : syracuseStep 1654563 = 2481845) B2481845
theorem B2793251 : Blo 1653526 2793251 := bstep (se 1 (by rfl) ⟨2094938, by rfl⟩ : syracuseStep 2793251 = 4189877) B4189877
theorem B2981681 : Blo 1653526 2981681 := bstep (se 2 (by rfl) ⟨1118130, by rfl⟩ : syracuseStep 2981681 = 2236261) B2236261
theorem B1654579 : Blo 1653526 1654579 := bstep (se 1 (by rfl) ⟨1240934, by rfl⟩ : syracuseStep 1654579 = 2481869) B2481869
theorem B2481971 : Blo 1653526 2481971 := bstep (se 1 (by rfl) ⟨1861478, by rfl⟩ : syracuseStep 2481971 = 3722957) B3722957
theorem B1654595 : Blo 1653526 1654595 := bstep (se 1 (by rfl) ⟨1240946, by rfl⟩ : syracuseStep 1654595 = 2481893) B2481893
theorem B2482001 : Blo 1653526 2482001 := bstep (se 2 (by rfl) ⟨930750, by rfl⟩ : syracuseStep 2482001 = 1861501) B1861501
theorem B1654611 : Blo 1653526 1654611 := bstep (se 1 (by rfl) ⟨1240958, by rfl⟩ : syracuseStep 1654611 = 2481917) B2481917
theorem B1654627 : Blo 1653526 1654627 := bstep (se 1 (by rfl) ⟨1240970, by rfl⟩ : syracuseStep 1654627 = 2481941) B2481941
theorem B2482019 : Blo 1653526 2482019 := bstep (se 1 (by rfl) ⟨1861514, by rfl⟩ : syracuseStep 2482019 = 3723029) B3723029
theorem B8380259 : Blo 1653526 8380259 := bstep (se 1 (by rfl) ⟨6285194, by rfl⟩ : syracuseStep 8380259 = 12570389) B12570389
theorem B1654643 : Blo 1653526 1654643 := bstep (se 1 (by rfl) ⟨1240982, by rfl⟩ : syracuseStep 1654643 = 2481965) B2481965
theorem B2482049 : Blo 1653526 2482049 := bstep (se 2 (by rfl) ⟨930768, by rfl⟩ : syracuseStep 2482049 = 1861537) B1861537
theorem B4710275 : Blo 1653526 4710275 := bstep (se 1 (by rfl) ⟨3532706, by rfl⟩ : syracuseStep 4710275 = 7065413) B7065413
theorem B1654659 : Blo 1653526 1654659 := bstep (se 1 (by rfl) ⟨1240994, by rfl⟩ : syracuseStep 1654659 = 2481989) B2481989
theorem B1654675 : Blo 1653526 1654675 := bstep (se 1 (by rfl) ⟨1241006, by rfl⟩ : syracuseStep 1654675 = 2482013) B2482013
theorem B2482067 : Blo 1653526 2482067 := bstep (se 1 (by rfl) ⟨1861550, by rfl⟩ : syracuseStep 2482067 = 3723101) B3723101
theorem B4186019 : Blo 1653526 4186019 := bstep (se 1 (by rfl) ⟨3139514, by rfl⟩ : syracuseStep 4186019 = 6279029) B6279029
theorem B1654691 : Blo 1653526 1654691 := bstep (se 1 (by rfl) ⟨1241018, by rfl⟩ : syracuseStep 1654691 = 2482037) B2482037
theorem B2793379 : Blo 1653526 2793379 := bstep (se 1 (by rfl) ⟨2095034, by rfl⟩ : syracuseStep 2793379 = 4190069) B4190069
theorem B2482097 : Blo 1653526 2482097 := bstep (se 2 (by rfl) ⟨930786, by rfl⟩ : syracuseStep 2482097 = 1861573) B1861573
theorem B1654707 : Blo 1653526 1654707 := bstep (se 1 (by rfl) ⟨1241030, by rfl⟩ : syracuseStep 1654707 = 2482061) B2482061
theorem B1654723 : Blo 1653526 1654723 := bstep (se 1 (by rfl) ⟨1241042, by rfl⟩ : syracuseStep 1654723 = 2482085) B2482085
theorem B2482115 : Blo 1653526 2482115 := bstep (se 1 (by rfl) ⟨1861586, by rfl⟩ : syracuseStep 2482115 = 3723173) B3723173
theorem B5586893 : Blo 1653526 5586893 := bstep (se 3 (by rfl) ⟨1047542, by rfl⟩ : syracuseStep 5586893 = 2095085) B2095085
theorem B1654739 : Blo 1653526 1654739 := bstep (se 1 (by rfl) ⟨1241054, by rfl⟩ : syracuseStep 1654739 = 2482109) B2482109
theorem B2482145 : Blo 1653526 2482145 := bstep (se 2 (by rfl) ⟨930804, by rfl⟩ : syracuseStep 2482145 = 1861609) B1861609
theorem B11321315 : Blo 1653526 11321315 := bstep (se 1 (by rfl) ⟨8490986, by rfl⟩ : syracuseStep 11321315 = 16981973) B16981973
theorem B1654755 : Blo 1653526 1654755 := bstep (se 1 (by rfl) ⟨1241066, by rfl⟩ : syracuseStep 1654755 = 2482133) B2482133
theorem B1654771 : Blo 1653526 1654771 := bstep (se 1 (by rfl) ⟨1241078, by rfl⟩ : syracuseStep 1654771 = 2482157) B2482157
theorem B2482163 : Blo 1653526 2482163 := bstep (se 1 (by rfl) ⟨1861622, by rfl⟩ : syracuseStep 2482163 = 3723245) B3723245
theorem B2482187 : Blo 1653526 2482187 := bstep (se 1 (by rfl) ⟨1861640, by rfl⟩ : syracuseStep 2482187 = 3723281) B3723281
theorem B1654795 : Blo 1653526 1654795 := bstep (se 1 (by rfl) ⟨1241096, by rfl⟩ : syracuseStep 1654795 = 2482193) B2482193
theorem B2482199 : Blo 1653526 2482199 := bstep (se 1 (by rfl) ⟨1861649, by rfl⟩ : syracuseStep 2482199 = 3723299) B3723299
theorem B1654807 : Blo 1653526 1654807 := bstep (se 1 (by rfl) ⟨1241105, by rfl⟩ : syracuseStep 1654807 = 2482211) B2482211
theorem B1654827 : Blo 1653526 1654827 := bstep (se 1 (by rfl) ⟨1241120, by rfl⟩ : syracuseStep 1654827 = 2482241) B2482241
theorem B1654839 : Blo 1653526 1654839 := bstep (se 1 (by rfl) ⟨1241129, by rfl⟩ : syracuseStep 1654839 = 2482259) B2482259
theorem B12091457 : Blo 1653526 12091457 := bstep (se 2 (by rfl) ⟨4534296, by rfl⟩ : syracuseStep 12091457 = 9068593) B9068593
theorem B1654859 : Blo 1653526 1654859 := bstep (se 1 (by rfl) ⟨1241144, by rfl⟩ : syracuseStep 1654859 = 2482289) B2482289
theorem B1654871 : Blo 1653526 1654871 := bstep (se 1 (by rfl) ⟨1241153, by rfl⟩ : syracuseStep 1654871 = 2482307) B2482307
theorem B4186201 : Blo 1653526 4186201 := bstep (se 2 (by rfl) ⟨1569825, by rfl⟩ : syracuseStep 4186201 = 3139651) B3139651
theorem B4472921 : Blo 1653526 4472921 := bstep (se 2 (by rfl) ⟨1677345, by rfl⟩ : syracuseStep 4472921 = 3354691) B3354691
theorem B2482265 : Blo 1653526 2482265 := bstep (se 2 (by rfl) ⟨930849, by rfl⟩ : syracuseStep 2482265 = 1861699) B1861699
theorem B1654891 : Blo 1653526 1654891 := bstep (se 1 (by rfl) ⟨1241168, by rfl⟩ : syracuseStep 1654891 = 2482337) B2482337
theorem B1654903 : Blo 1653526 1654903 := bstep (se 1 (by rfl) ⟨1241177, by rfl⟩ : syracuseStep 1654903 = 2482355) B2482355
theorem B1654923 : Blo 1653526 1654923 := bstep (se 1 (by rfl) ⟨1241192, by rfl⟩ : syracuseStep 1654923 = 2482385) B2482385
theorem B1654935 : Blo 1653526 1654935 := bstep (se 1 (by rfl) ⟨1241201, by rfl⟩ : syracuseStep 1654935 = 2482403) B2482403
theorem B1654955 : Blo 1653526 1654955 := bstep (se 1 (by rfl) ⟨1241216, by rfl⟩ : syracuseStep 1654955 = 2482433) B2482433
theorem B6127795 : Blo 1653526 6127795 := bstep (se 1 (by rfl) ⟨4595846, by rfl⟩ : syracuseStep 6127795 = 9191693) B9191693
theorem B1654967 : Blo 1653526 1654967 := bstep (se 1 (by rfl) ⟨1241225, by rfl⟩ : syracuseStep 1654967 = 2482451) B2482451
theorem B5300417 : Blo 1653526 5300417 := bstep (se 2 (by rfl) ⟨1987656, by rfl⟩ : syracuseStep 5300417 = 3975313) B3975313
theorem B5660875 : Blo 1653526 5660875 := bstep (se 1 (by rfl) ⟨4245656, by rfl⟩ : syracuseStep 5660875 = 8491313) B8491313
theorem B2982091 : Blo 1653526 2982091 := bstep (se 1 (by rfl) ⟨2236568, by rfl⟩ : syracuseStep 2982091 = 4473137) B4473137
theorem B2482379 : Blo 1653526 2482379 := bstep (se 1 (by rfl) ⟨1861784, by rfl⟩ : syracuseStep 2482379 = 3723569) B3723569
theorem B1654987 : Blo 1653526 1654987 := bstep (se 1 (by rfl) ⟨1241240, by rfl⟩ : syracuseStep 1654987 = 2482481) B2482481
theorem B2482391 : Blo 1653526 2482391 := bstep (se 1 (by rfl) ⟨1861793, by rfl⟩ : syracuseStep 2482391 = 3723587) B3723587
theorem B1654999 : Blo 1653526 1654999 := bstep (se 1 (by rfl) ⟨1241249, by rfl⟩ : syracuseStep 1654999 = 2482499) B2482499
theorem B6365405 : Blo 1653526 6365405 := bstep (se 3 (by rfl) ⟨1193513, by rfl⟩ : syracuseStep 6365405 = 2387027) B2387027
theorem B1655019 : Blo 1653526 1655019 := bstep (se 1 (by rfl) ⟨1241264, by rfl⟩ : syracuseStep 1655019 = 2482529) B2482529
theorem B1655031 : Blo 1653526 1655031 := bstep (se 1 (by rfl) ⟨1241273, by rfl⟩ : syracuseStep 1655031 = 2482547) B2482547
theorem B1655051 : Blo 1653526 1655051 := bstep (se 1 (by rfl) ⟨1241288, by rfl⟩ : syracuseStep 1655051 = 2482577) B2482577
theorem B1655063 : Blo 1653526 1655063 := bstep (se 1 (by rfl) ⟨1241297, by rfl⟩ : syracuseStep 1655063 = 2482595) B2482595
theorem B2482457 : Blo 1653526 2482457 := bstep (se 2 (by rfl) ⟨930921, by rfl⟩ : syracuseStep 2482457 = 1861843) B1861843
theorem B1655083 : Blo 1653526 1655083 := bstep (se 1 (by rfl) ⟨1241312, by rfl⟩ : syracuseStep 1655083 = 2482625) B2482625
theorem B4710707 : Blo 1653526 4710707 := bstep (se 1 (by rfl) ⟨3533030, by rfl⟩ : syracuseStep 4710707 = 7066061) B7066061
theorem B1655095 : Blo 1653526 1655095 := bstep (se 1 (by rfl) ⟨1241321, by rfl⟩ : syracuseStep 1655095 = 2482643) B2482643
theorem B1655115 : Blo 1653526 1655115 := bstep (se 1 (by rfl) ⟨1241336, by rfl⟩ : syracuseStep 1655115 = 2482673) B2482673
theorem B1655127 : Blo 1653526 1655127 := bstep (se 1 (by rfl) ⟨1241345, by rfl⟩ : syracuseStep 1655127 = 2482691) B2482691
theorem B1655147 : Blo 1653526 1655147 := bstep (se 1 (by rfl) ⟨1241360, by rfl⟩ : syracuseStep 1655147 = 2482721) B2482721
theorem B1655159 : Blo 1653526 1655159 := bstep (se 1 (by rfl) ⟨1241369, by rfl⟩ : syracuseStep 1655159 = 2482739) B2482739
theorem B2482571 : Blo 1653526 2482571 := bstep (se 1 (by rfl) ⟨1861928, by rfl⟩ : syracuseStep 2482571 = 3723857) B3723857
theorem B1655179 : Blo 1653526 1655179 := bstep (se 1 (by rfl) ⟨1241384, by rfl⟩ : syracuseStep 1655179 = 2482769) B2482769
theorem B2482583 : Blo 1653526 2482583 := bstep (se 1 (by rfl) ⟨1861937, by rfl⟩ : syracuseStep 2482583 = 3723875) B3723875
theorem B1655191 : Blo 1653526 1655191 := bstep (se 1 (by rfl) ⟨1241393, by rfl⟩ : syracuseStep 1655191 = 2482787) B2482787
theorem B1655211 : Blo 1653526 1655211 := bstep (se 1 (by rfl) ⟨1241408, by rfl⟩ : syracuseStep 1655211 = 2482817) B2482817
theorem B5587379 : Blo 1653526 5587379 := bstep (se 1 (by rfl) ⟨4190534, by rfl⟩ : syracuseStep 5587379 = 8381069) B8381069
theorem B1655223 : Blo 1653526 1655223 := bstep (se 1 (by rfl) ⟨1241417, by rfl⟩ : syracuseStep 1655223 = 2482835) B2482835
theorem B1655243 : Blo 1653526 1655243 := bstep (se 1 (by rfl) ⟨1241432, by rfl⟩ : syracuseStep 1655243 = 2482865) B2482865
theorem B1655255 : Blo 1653526 1655255 := bstep (se 1 (by rfl) ⟨1241441, by rfl⟩ : syracuseStep 1655255 = 2482883) B2482883
theorem B2482649 : Blo 1653526 2482649 := bstep (se 2 (by rfl) ⟨930993, by rfl⟩ : syracuseStep 2482649 = 1861987) B1861987
theorem B1655275 : Blo 1653526 1655275 := bstep (se 1 (by rfl) ⟨1241456, by rfl⟩ : syracuseStep 1655275 = 2482913) B2482913
theorem B1655287 : Blo 1653526 1655287 := bstep (se 1 (by rfl) ⟨1241465, by rfl⟩ : syracuseStep 1655287 = 2482931) B2482931
theorem B1655307 : Blo 1653526 1655307 := bstep (se 1 (by rfl) ⟨1241480, by rfl⟩ : syracuseStep 1655307 = 2482961) B2482961
theorem B64471565 : Blo 1653526 64471565 := bstep (se 3 (by rfl) ⟨12088418, by rfl⟩ : syracuseStep 64471565 = 24176837) B24176837
theorem B4710935 : Blo 1653526 4710935 := bstep (se 1 (by rfl) ⟨3533201, by rfl⟩ : syracuseStep 4710935 = 7066403) B7066403
theorem B1655319 : Blo 1653526 1655319 := bstep (se 1 (by rfl) ⟨1241489, by rfl⟩ : syracuseStep 1655319 = 2482979) B2482979
theorem B1655339 : Blo 1653526 1655339 := bstep (se 1 (by rfl) ⟨1241504, by rfl⟩ : syracuseStep 1655339 = 2483009) B2483009
theorem B4473395 : Blo 1653526 4473395 := bstep (se 1 (by rfl) ⟨3355046, by rfl⟩ : syracuseStep 4473395 = 6710093) B6710093
theorem B1655351 : Blo 1653526 1655351 := bstep (se 1 (by rfl) ⟨1241513, by rfl⟩ : syracuseStep 1655351 = 2483027) B2483027
theorem B23847493 : Blo 1653526 23847493 := bstep (se 4 (by rfl) ⟨2235702, by rfl⟩ : syracuseStep 23847493 = 4471405) B4471405
theorem B2482763 : Blo 1653526 2482763 := bstep (se 1 (by rfl) ⟨1862072, by rfl⟩ : syracuseStep 2482763 = 3724145) B3724145
theorem B1655371 : Blo 1653526 1655371 := bstep (se 1 (by rfl) ⟨1241528, by rfl⟩ : syracuseStep 1655371 = 2483057) B2483057
theorem B2482775 : Blo 1653526 2482775 := bstep (se 1 (by rfl) ⟨1862081, by rfl⟩ : syracuseStep 2482775 = 3724163) B3724163
theorem B1655383 : Blo 1653526 1655383 := bstep (se 1 (by rfl) ⟨1241537, by rfl⟩ : syracuseStep 1655383 = 2483075) B2483075
theorem B1655403 : Blo 1653526 1655403 := bstep (se 1 (by rfl) ⟨1241552, by rfl⟩ : syracuseStep 1655403 = 2483105) B2483105
theorem B1655415 : Blo 1653526 1655415 := bstep (se 1 (by rfl) ⟨1241561, by rfl⟩ : syracuseStep 1655415 = 2483123) B2483123
theorem B1655435 : Blo 1653526 1655435 := bstep (se 1 (by rfl) ⟨1241576, by rfl⟩ : syracuseStep 1655435 = 2483153) B2483153
theorem B1655447 : Blo 1653526 1655447 := bstep (se 1 (by rfl) ⟨1241585, by rfl⟩ : syracuseStep 1655447 = 2483171) B2483171
theorem B2482841 : Blo 1653526 2482841 := bstep (se 2 (by rfl) ⟨931065, by rfl⟩ : syracuseStep 2482841 = 1862131) B1862131
theorem B1655467 : Blo 1653526 1655467 := bstep (se 1 (by rfl) ⟨1241600, by rfl⟩ : syracuseStep 1655467 = 2483201) B2483201
theorem B1655479 : Blo 1653526 1655479 := bstep (se 1 (by rfl) ⟨1241609, by rfl⟩ : syracuseStep 1655479 = 2483219) B2483219
theorem B1655499 : Blo 1653526 1655499 := bstep (se 1 (by rfl) ⟨1241624, by rfl⟩ : syracuseStep 1655499 = 2483249) B2483249
theorem B1655511 : Blo 1653526 1655511 := bstep (se 1 (by rfl) ⟨1241633, by rfl⟩ : syracuseStep 1655511 = 2483267) B2483267
theorem B13083353 : Blo 1653526 13083353 := bstep (se 2 (by rfl) ⟨4906257, by rfl⟩ : syracuseStep 13083353 = 9812515) B9812515
theorem B1860331 : Blo 1653526 1860331 := bstep (se 1 (by rfl) ⟨1395248, by rfl⟩ : syracuseStep 1860331 = 2790497) B2790497
theorem B2482955 : Blo 1653526 2482955 := bstep (se 1 (by rfl) ⟨1862216, by rfl⟩ : syracuseStep 2482955 = 3724433) B3724433
theorem B2482967 : Blo 1653526 2482967 := bstep (se 1 (by rfl) ⟨1862225, by rfl⟩ : syracuseStep 2482967 = 3724451) B3724451
theorem B40231745 : Blo 1653526 40231745 := bstep (se 2 (by rfl) ⟨15086904, by rfl⟩ : syracuseStep 40231745 = 30173809) B30173809
theorem B3531595 : Blo 1653526 3531595 := bstep (se 1 (by rfl) ⟨2648696, by rfl⟩ : syracuseStep 3531595 = 5297393) B5297393
theorem B4711243 : Blo 1653526 4711243 := bstep (se 1 (by rfl) ⟨3533432, by rfl⟩ : syracuseStep 4711243 = 7066865) B7066865
theorem B1860439 : Blo 1653526 1860439 := bstep (se 1 (by rfl) ⟨1395329, by rfl⟩ : syracuseStep 1860439 = 2790659) B2790659
theorem B2483033 : Blo 1653526 2483033 := bstep (se 2 (by rfl) ⟨931137, by rfl⟩ : syracuseStep 2483033 = 1862275) B1862275
theorem B17892197 : Blo 1653526 17892197 := bstep (se 4 (by rfl) ⟨1677393, by rfl⟩ : syracuseStep 17892197 = 3354787) B3354787
theorem B12567473 : Blo 1653526 12567473 := bstep (se 2 (by rfl) ⟨4712802, by rfl⟩ : syracuseStep 12567473 = 9425605) B9425605
theorem B2483147 : Blo 1653526 2483147 := bstep (se 1 (by rfl) ⟨1862360, by rfl⟩ : syracuseStep 2483147 = 3724721) B3724721
theorem B2483159 : Blo 1653526 2483159 := bstep (se 1 (by rfl) ⟨1862369, by rfl⟩ : syracuseStep 2483159 = 3724739) B3724739
theorem B1860619 : Blo 1653526 1860619 := bstep (se 1 (by rfl) ⟨1395464, by rfl⟩ : syracuseStep 1860619 = 2790929) B2790929
theorem B2483225 : Blo 1653526 2483225 := bstep (se 2 (by rfl) ⟨931209, by rfl⟩ : syracuseStep 2483225 = 1862419) B1862419
theorem B8373293 : Blo 1653526 8373293 := bstep (se 3 (by rfl) ⟨1569992, by rfl⟩ : syracuseStep 8373293 = 3139985) B3139985
theorem B4711517 : Blo 1653526 4711517 := bstep (se 3 (by rfl) ⟨883409, by rfl⟩ : syracuseStep 4711517 = 1766819) B1766819
theorem B1860727 : Blo 1653526 1860727 := bstep (se 1 (by rfl) ⟨1395545, by rfl⟩ : syracuseStep 1860727 = 2791091) B2791091
theorem B16794755 : Blo 1653526 16794755 := bstep (se 1 (by rfl) ⟨12596066, by rfl⟩ : syracuseStep 16794755 = 25192133) B25192133
theorem B4187315 : Blo 1653526 4187315 := bstep (se 1 (by rfl) ⟨3140486, by rfl⟩ : syracuseStep 4187315 = 6280973) B6280973
theorem B14140595 : Blo 1653526 14140595 := bstep (se 1 (by rfl) ⟨10605446, by rfl⟩ : syracuseStep 14140595 = 21210893) B21210893
theorem B3720473 : Blo 1653526 3720473 := bstep (se 2 (by rfl) ⟨1395177, by rfl⟩ : syracuseStep 3720473 = 2790355) B2790355
theorem B1860907 : Blo 1653526 1860907 := bstep (se 1 (by rfl) ⟨1395680, by rfl⟩ : syracuseStep 1860907 = 2791361) B2791361
theorem B3720563 : Blo 1653526 3720563 := bstep (se 1 (by rfl) ⟨2790422, by rfl⟩ : syracuseStep 3720563 = 5580845) B5580845
theorem B3720599 : Blo 1653526 3720599 := bstep (se 1 (by rfl) ⟨2790449, by rfl⟩ : syracuseStep 3720599 = 5580899) B5580899
theorem B1861015 : Blo 1653526 1861015 := bstep (se 1 (by rfl) ⟨1395761, by rfl⟩ : syracuseStep 1861015 = 2791523) B2791523
theorem B12567959 : Blo 1653526 12567959 := bstep (se 1 (by rfl) ⟨9425969, by rfl⟩ : syracuseStep 12567959 = 18851939) B18851939
theorem B4187609 : Blo 1653526 4187609 := bstep (se 2 (by rfl) ⟨1570353, by rfl⟩ : syracuseStep 4187609 = 3140707) B3140707
theorem B7947821 : Blo 1653526 7947821 := bstep (se 3 (by rfl) ⟨1490216, by rfl⟩ : syracuseStep 7947821 = 2980433) B2980433
theorem B3532339 : Blo 1653526 3532339 := bstep (se 1 (by rfl) ⟨2649254, by rfl⟩ : syracuseStep 3532339 = 5298509) B5298509
theorem B3720779 : Blo 1653526 3720779 := bstep (se 1 (by rfl) ⟨2790584, by rfl⟩ : syracuseStep 3720779 = 5581169) B5581169
theorem B1861195 : Blo 1653526 1861195 := bstep (se 1 (by rfl) ⟨1395896, by rfl⟩ : syracuseStep 1861195 = 2791793) B2791793
theorem B3352193 : Blo 1653526 3352193 := bstep (se 2 (by rfl) ⟨1257072, by rfl⟩ : syracuseStep 3352193 = 2514145) B2514145
theorem B3720833 : Blo 1653526 3720833 := bstep (se 2 (by rfl) ⟨1395312, by rfl⟩ : syracuseStep 3720833 = 2790625) B2790625
theorem B3139211 : Blo 1653526 3139211 := bstep (se 1 (by rfl) ⟨2354408, by rfl⟩ : syracuseStep 3139211 = 4708817) B4708817
theorem B1861303 : Blo 1653526 1861303 := bstep (se 1 (by rfl) ⟨1395977, by rfl⟩ : syracuseStep 1861303 = 2791955) B2791955
theorem B6285059 : Blo 1653526 6285059 := bstep (se 1 (by rfl) ⟨4713794, by rfl⟩ : syracuseStep 6285059 = 9427589) B9427589
theorem B6285073 : Blo 1653526 6285073 := bstep (se 2 (by rfl) ⟨2356902, by rfl⟩ : syracuseStep 6285073 = 4713805) B4713805
theorem B3139393 : Blo 1653526 3139393 := bstep (se 2 (by rfl) ⟨1177272, by rfl⟩ : syracuseStep 3139393 = 2354545) B2354545
theorem B21489473 : Blo 1653526 21489473 := bstep (se 2 (by rfl) ⟨8058552, by rfl⟩ : syracuseStep 21489473 = 16117105) B16117105
theorem B3974987 : Blo 1653526 3974987 := bstep (se 1 (by rfl) ⟨2981240, by rfl⟩ : syracuseStep 3974987 = 5962481) B5962481
theorem B3721049 : Blo 1653526 3721049 := bstep (se 2 (by rfl) ⟨1395393, by rfl⟩ : syracuseStep 3721049 = 2790787) B2790787
theorem B1861483 : Blo 1653526 1861483 := bstep (se 1 (by rfl) ⟨1396112, by rfl⟩ : syracuseStep 1861483 = 2792225) B2792225
theorem B3721139 : Blo 1653526 3721139 := bstep (se 1 (by rfl) ⟨2790854, by rfl⟩ : syracuseStep 3721139 = 5581709) B5581709
theorem B5580737 : Blo 1653526 5580737 := bstep (se 2 (by rfl) ⟨2092776, by rfl⟩ : syracuseStep 5580737 = 4185553) B4185553
theorem B3721175 : Blo 1653526 3721175 := bstep (se 1 (by rfl) ⟨2790881, by rfl⟩ : syracuseStep 3721175 = 5581763) B5581763
theorem B1861591 : Blo 1653526 1861591 := bstep (se 1 (by rfl) ⟨1396193, by rfl⟩ : syracuseStep 1861591 = 2792387) B2792387
theorem B31803353 : Blo 1653526 31803353 := bstep (se 2 (by rfl) ⟨11926257, by rfl⟩ : syracuseStep 31803353 = 23852515) B23852515
theorem B3532825 : Blo 1653526 3532825 := bstep (se 2 (by rfl) ⟨1324809, by rfl⟩ : syracuseStep 3532825 = 2649619) B2649619
theorem B6285377 : Blo 1653526 6285377 := bstep (se 2 (by rfl) ⟨2357016, by rfl⟩ : syracuseStep 6285377 = 4714033) B4714033
theorem B3721355 : Blo 1653526 3721355 := bstep (se 1 (by rfl) ⟨2791016, by rfl⟩ : syracuseStep 3721355 = 5582033) B5582033
theorem B1861771 : Blo 1653526 1861771 := bstep (se 1 (by rfl) ⟨1396328, by rfl⟩ : syracuseStep 1861771 = 2792657) B2792657
theorem B5965969 : Blo 1653526 5965969 := bstep (se 2 (by rfl) ⟨2237238, by rfl⟩ : syracuseStep 5965969 = 4474477) B4474477
theorem B3139735 : Blo 1653526 3139735 := bstep (se 1 (by rfl) ⟨2354801, by rfl⟩ : syracuseStep 3139735 = 4709603) B4709603
theorem B3721409 : Blo 1653526 3721409 := bstep (se 2 (by rfl) ⟨1395528, by rfl⟩ : syracuseStep 3721409 = 2791057) B2791057
theorem B1861879 : Blo 1653526 1861879 := bstep (se 1 (by rfl) ⟨1396409, by rfl⟩ : syracuseStep 1861879 = 2792819) B2792819
theorem B13420835 : Blo 1653526 13420835 := bstep (se 1 (by rfl) ⟨10065626, by rfl⟩ : syracuseStep 13420835 = 20131253) B20131253
theorem B11929949 : Blo 1653526 11929949 := bstep (se 3 (by rfl) ⟨2236865, by rfl⟩ : syracuseStep 11929949 = 4473731) B4473731
theorem B5302621 : Blo 1653526 5302621 := bstep (se 3 (by rfl) ⟨994241, by rfl⟩ : syracuseStep 5302621 = 1988483) B1988483
theorem B3139955 : Blo 1653526 3139955 := bstep (se 1 (by rfl) ⟨2354966, by rfl⟩ : syracuseStep 3139955 = 4709933) B4709933
theorem B3721625 : Blo 1653526 3721625 := bstep (se 2 (by rfl) ⟨1395609, by rfl⟩ : syracuseStep 3721625 = 2791219) B2791219
theorem B1862059 : Blo 1653526 1862059 := bstep (se 1 (by rfl) ⟨1396544, by rfl⟩ : syracuseStep 1862059 = 2793089) B2793089
theorem B5581277 : Blo 1653526 5581277 := bstep (se 3 (by rfl) ⟨1046489, by rfl⟩ : syracuseStep 5581277 = 2092979) B2092979
theorem B3721715 : Blo 1653526 3721715 := bstep (se 1 (by rfl) ⟨2791286, by rfl⟩ : syracuseStep 3721715 = 5582573) B5582573
theorem B3721751 : Blo 1653526 3721751 := bstep (se 1 (by rfl) ⟨2791313, by rfl⟩ : syracuseStep 3721751 = 5582627) B5582627
theorem B1862167 : Blo 1653526 1862167 := bstep (se 1 (by rfl) ⟨1396625, by rfl⟩ : syracuseStep 1862167 = 2793251) B2793251
theorem B4246091 : Blo 1653526 4246091 := bstep (se 1 (by rfl) ⟨3184568, by rfl⟩ : syracuseStep 4246091 = 6369137) B6369137
theorem B3140183 : Blo 1653526 3140183 := bstep (se 1 (by rfl) ⟨2355137, by rfl⟩ : syracuseStep 3140183 = 4710275) B4710275
theorem B7547543 : Blo 1653526 7547543 := bstep (se 1 (by rfl) ⟨5660657, by rfl⟩ : syracuseStep 7547543 = 11321315) B11321315
theorem B3721931 : Blo 1653526 3721931 := bstep (se 1 (by rfl) ⟨2791448, by rfl⟩ : syracuseStep 3721931 = 5582897) B5582897
theorem B1862347 : Blo 1653526 1862347 := bstep (se 1 (by rfl) ⟨1396760, by rfl⟩ : syracuseStep 1862347 = 2793521) B2793521
theorem B3721985 : Blo 1653526 3721985 := bstep (se 2 (by rfl) ⟨1395744, by rfl⟩ : syracuseStep 3721985 = 2791489) B2791489
theorem B3975959 : Blo 1653526 3975959 := bstep (se 1 (by rfl) ⟨2981969, by rfl⟩ : syracuseStep 3975959 = 5963939) B5963939
theorem B1862455 : Blo 1653526 1862455 := bstep (se 1 (by rfl) ⟨1396841, by rfl⟩ : syracuseStep 1862455 = 2793683) B2793683
theorem B3140441 : Blo 1653526 3140441 := bstep (se 2 (by rfl) ⟨1177665, by rfl⟩ : syracuseStep 3140441 = 2355331) B2355331
theorem B3722201 : Blo 1653526 3722201 := bstep (se 2 (by rfl) ⟨1395825, by rfl⟩ : syracuseStep 3722201 = 2791651) B2791651
theorem B11324377 : Blo 1653526 11324377 := bstep (se 2 (by rfl) ⟨4246641, by rfl⟩ : syracuseStep 11324377 = 8493283) B8493283
theorem B14142509 : Blo 1653526 14142509 := bstep (se 3 (by rfl) ⟨2651720, by rfl⟩ : syracuseStep 14142509 = 5303441) B5303441
theorem B3722291 : Blo 1653526 3722291 := bstep (se 1 (by rfl) ⟨2791718, by rfl⟩ : syracuseStep 3722291 = 5583437) B5583437
theorem B4189259 : Blo 1653526 4189259 := bstep (se 1 (by rfl) ⟨3141944, by rfl⟩ : syracuseStep 4189259 = 6283889) B6283889
theorem B3722327 : Blo 1653526 3722327 := bstep (se 1 (by rfl) ⟨2791745, by rfl⟩ : syracuseStep 3722327 = 5583491) B5583491
theorem B9423965 : Blo 1653526 9423965 := bstep (se 3 (by rfl) ⟨1766993, by rfl⟩ : syracuseStep 9423965 = 3533987) B3533987
theorem B3976343 : Blo 1653526 3976343 := bstep (se 1 (by rfl) ⟨2982257, by rfl⟩ : syracuseStep 3976343 = 5964515) B5964515
theorem B4713623 : Blo 1653526 4713623 := bstep (se 1 (by rfl) ⟨3535217, by rfl⟩ : syracuseStep 4713623 = 7070435) B7070435
theorem B3140851 : Blo 1653526 3140851 := bstep (se 1 (by rfl) ⟨2355638, by rfl⟩ : syracuseStep 3140851 = 4711277) B4711277
theorem B3722507 : Blo 1653526 3722507 := bstep (se 1 (by rfl) ⟨2791880, by rfl⟩ : syracuseStep 3722507 = 5583761) B5583761
theorem B3722561 : Blo 1653526 3722561 := bstep (se 2 (by rfl) ⟨1395960, by rfl⟩ : syracuseStep 3722561 = 2791921) B2791921
theorem B6278573 : Blo 1653526 6278573 := bstep (se 3 (by rfl) ⟨1177232, by rfl⟩ : syracuseStep 6278573 = 2354465) B2354465
theorem B3534295 : Blo 1653526 3534295 := bstep (se 1 (by rfl) ⟨2650721, by rfl⟩ : syracuseStep 3534295 = 5301443) B5301443
theorem B3534347 : Blo 1653526 3534347 := bstep (se 1 (by rfl) ⟨2650760, by rfl⟩ : syracuseStep 3534347 = 5301521) B5301521
theorem B3722777 : Blo 1653526 3722777 := bstep (se 2 (by rfl) ⟨1396041, by rfl⟩ : syracuseStep 3722777 = 2792083) B2792083
theorem B5582411 : Blo 1653526 5582411 := bstep (se 1 (by rfl) ⟨4186808, by rfl⟩ : syracuseStep 5582411 = 8373617) B8373617
theorem B3722867 : Blo 1653526 3722867 := bstep (se 1 (by rfl) ⟨2792150, by rfl⟩ : syracuseStep 3722867 = 5584301) B5584301
theorem B14126723 : Blo 1653526 14126723 := bstep (se 1 (by rfl) ⟨10595042, by rfl⟩ : syracuseStep 14126723 = 21190085) B21190085
theorem B7548547 : Blo 1653526 7548547 := bstep (se 1 (by rfl) ⟨5661410, by rfl⟩ : syracuseStep 7548547 = 11322821) B11322821
theorem B3722903 : Blo 1653526 3722903 := bstep (se 1 (by rfl) ⟨2792177, by rfl⟩ : syracuseStep 3722903 = 5584355) B5584355
theorem B3985075 : Blo 1653526 3985075 := bstep (se 1 (by rfl) ⟨2988806, by rfl⟩ : syracuseStep 3985075 = 5977613) B5977613
theorem B3141337 : Blo 1653526 3141337 := bstep (se 2 (by rfl) ⟨1178001, by rfl⟩ : syracuseStep 3141337 = 2356003) B2356003
theorem B3723083 : Blo 1653526 3723083 := bstep (se 1 (by rfl) ⟨2792312, by rfl⟩ : syracuseStep 3723083 = 5584625) B5584625
theorem B5582681 : Blo 1653526 5582681 := bstep (se 2 (by rfl) ⟨2093505, by rfl⟩ : syracuseStep 5582681 = 4187011) B4187011
theorem B10596197 : Blo 1653526 10596197 := bstep (se 4 (by rfl) ⟨993393, by rfl⟩ : syracuseStep 10596197 = 1986787) B1986787
theorem B3723137 : Blo 1653526 3723137 := bstep (se 2 (by rfl) ⟨1396176, by rfl⟩ : syracuseStep 3723137 = 2792353) B2792353
theorem B7548893 : Blo 1653526 7548893 := bstep (se 3 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 7548893 = 2830835) B2830835
theorem B11317265 : Blo 1653526 11317265 := bstep (se 2 (by rfl) ⟨4243974, by rfl⟩ : syracuseStep 11317265 = 8487949) B8487949
theorem B4190231 : Blo 1653526 4190231 := bstep (se 1 (by rfl) ⟨3142673, by rfl⟩ : syracuseStep 4190231 = 6285347) B6285347
theorem B2093131 : Blo 1653526 2093131 := bstep (se 1 (by rfl) ⟨1569848, by rfl⟩ : syracuseStep 2093131 = 3139697) B3139697
theorem B3723353 : Blo 1653526 3723353 := bstep (se 2 (by rfl) ⟨1396257, by rfl⟩ : syracuseStep 3723353 = 2792515) B2792515
theorem B15093911 : Blo 1653526 15093911 := bstep (se 1 (by rfl) ⟨11320433, by rfl⟩ : syracuseStep 15093911 = 22640867) B22640867
theorem B3723443 : Blo 1653526 3723443 := bstep (se 1 (by rfl) ⟨2792582, by rfl⟩ : syracuseStep 3723443 = 5585165) B5585165
theorem B1814731 : Blo 1653526 1814731 := bstep (se 1 (by rfl) ⟨1361048, by rfl⟩ : syracuseStep 1814731 = 2722097) B2722097
theorem B3977419 : Blo 1653526 3977419 := bstep (se 1 (by rfl) ⟨2983064, by rfl⟩ : syracuseStep 3977419 = 5966129) B5966129
theorem B3723479 : Blo 1653526 3723479 := bstep (se 1 (by rfl) ⟨2792609, by rfl⟩ : syracuseStep 3723479 = 5585219) B5585219
theorem B1790219 : Blo 1653526 1790219 := bstep (se 1 (by rfl) ⟨1342664, by rfl⟩ : syracuseStep 1790219 = 2685329) B2685329
theorem B3141899 : Blo 1653526 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B34910509 : Blo 1653526 34910509 := bstep (se 3 (by rfl) ⟨6545720, by rfl⟩ : syracuseStep 34910509 = 13091441) B13091441
theorem B10596683 : Blo 1653526 10596683 := bstep (se 1 (by rfl) ⟨7947512, by rfl⟩ : syracuseStep 10596683 = 15895025) B15895025
theorem B3723659 : Blo 1653526 3723659 := bstep (se 1 (by rfl) ⟨2792744, by rfl⟩ : syracuseStep 3723659 = 5585489) B5585489
theorem B3723713 : Blo 1653526 3723713 := bstep (se 2 (by rfl) ⟨1396392, by rfl⟩ : syracuseStep 3723713 = 2792785) B2792785
theorem B3142081 : Blo 1653526 3142081 := bstep (se 2 (by rfl) ⟨1178280, by rfl⟩ : syracuseStep 3142081 = 2356561) B2356561
theorem B7066129 : Blo 1653526 7066129 := bstep (se 2 (by rfl) ⟨2649798, by rfl⟩ : syracuseStep 7066129 = 5299597) B5299597
theorem B5583383 : Blo 1653526 5583383 := bstep (se 1 (by rfl) ⟨4187537, by rfl⟩ : syracuseStep 5583383 = 8375075) B8375075
theorem B3273241 : Blo 1653526 3273241 := bstep (se 2 (by rfl) ⟨1227465, by rfl⟩ : syracuseStep 3273241 = 2454931) B2454931
theorem B6795841 : Blo 1653526 6795841 := bstep (se 2 (by rfl) ⟨2548440, by rfl⟩ : syracuseStep 6795841 = 5096881) B5096881
theorem B3723929 : Blo 1653526 3723929 := bstep (se 2 (by rfl) ⟨1396473, by rfl⟩ : syracuseStep 3723929 = 2792947) B2792947
theorem B1766071 : Blo 1653526 1766071 := bstep (se 1 (by rfl) ⟨1324553, by rfl⟩ : syracuseStep 1766071 = 2649107) B2649107
theorem B3724019 : Blo 1653526 3724019 := bstep (se 1 (by rfl) ⟨2793014, by rfl⟩ : syracuseStep 3724019 = 5586029) B5586029
theorem B3724055 : Blo 1653526 3724055 := bstep (se 1 (by rfl) ⟨2793041, by rfl⟩ : syracuseStep 3724055 = 5586083) B5586083
theorem B6280001 : Blo 1653526 6280001 := bstep (se 2 (by rfl) ⟨2355000, by rfl⟩ : syracuseStep 6280001 = 4710001) B4710001
theorem B8377181 : Blo 1653526 8377181 := bstep (se 3 (by rfl) ⟨1570721, by rfl⟩ : syracuseStep 8377181 = 3141443) B3141443
theorem B3724235 : Blo 1653526 3724235 := bstep (se 1 (by rfl) ⟨2793176, by rfl⟩ : syracuseStep 3724235 = 5586353) B5586353
theorem B11924441 : Blo 1653526 11924441 := bstep (se 2 (by rfl) ⟨4471665, by rfl⟩ : syracuseStep 11924441 = 8943331) B8943331
theorem B3724289 : Blo 1653526 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B6370321 : Blo 1653526 6370321 := bstep (se 2 (by rfl) ⟨2388870, by rfl⟩ : syracuseStep 6370321 = 4777741) B4777741
theorem B2094103 : Blo 1653526 2094103 := bstep (se 1 (by rfl) ⟨1570577, by rfl⟩ : syracuseStep 2094103 = 3141155) B3141155
theorem B1766443 : Blo 1653526 1766443 := bstep (se 1 (by rfl) ⟨1324832, by rfl⟩ : syracuseStep 1766443 = 2649665) B2649665
theorem B11932717 : Blo 1653526 11932717 := bstep (se 3 (by rfl) ⟨2237384, by rfl⟩ : syracuseStep 11932717 = 4474769) B4474769
theorem B5583923 : Blo 1653526 5583923 := bstep (se 1 (by rfl) ⟨4187942, by rfl⟩ : syracuseStep 5583923 = 8375885) B8375885
theorem B3142795 : Blo 1653526 3142795 := bstep (se 1 (by rfl) ⟨2357096, by rfl⟩ : syracuseStep 3142795 = 4714193) B4714193
theorem B2790551 : Blo 1653526 2790551 := bstep (se 1 (by rfl) ⟨2092913, by rfl⟩ : syracuseStep 2790551 = 4185827) B4185827
theorem B1987787 : Blo 1653526 1987787 := bstep (se 1 (by rfl) ⟨1490840, by rfl⟩ : syracuseStep 1987787 = 2981681) B2981681
theorem B3142871 : Blo 1653526 3142871 := bstep (se 1 (by rfl) ⟨2357153, by rfl⟩ : syracuseStep 3142871 = 4714307) B4714307
theorem B3724505 : Blo 1653526 3724505 := bstep (se 2 (by rfl) ⟨1396689, by rfl⟩ : syracuseStep 3724505 = 2793379) B2793379
theorem B2790679 : Blo 1653526 2790679 := bstep (se 1 (by rfl) ⟨2093009, by rfl⟩ : syracuseStep 2790679 = 4186019) B4186019
theorem B3724595 : Blo 1653526 3724595 := bstep (se 1 (by rfl) ⟨2793446, by rfl⟩ : syracuseStep 3724595 = 5586893) B5586893
theorem B5584193 : Blo 1653526 5584193 := bstep (se 2 (by rfl) ⟨2094072, by rfl⟩ : syracuseStep 5584193 = 4188145) B4188145
theorem B3724631 : Blo 1653526 3724631 := bstep (se 1 (by rfl) ⟨2793473, by rfl⟩ : syracuseStep 3724631 = 5586947) B5586947
theorem B1766891 : Blo 1653526 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B3724811 : Blo 1653526 3724811 := bstep (se 1 (by rfl) ⟨2793608, by rfl⟩ : syracuseStep 3724811 = 5587217) B5587217
theorem B3724865 : Blo 1653526 3724865 := bstep (se 2 (by rfl) ⟨1396824, by rfl⟩ : syracuseStep 3724865 = 2793649) B2793649
theorem B9418315 : Blo 1653526 9418315 := bstep (se 1 (by rfl) ⟨7063736, by rfl⟩ : syracuseStep 9418315 = 14127473) B14127473
theorem B2356823 : Blo 1653526 2356823 := bstep (se 1 (by rfl) ⟨1767617, by rfl⟩ : syracuseStep 2356823 = 3535235) B3535235
theorem B9426563 : Blo 1653526 9426563 := bstep (se 1 (by rfl) ⟨7069922, by rfl⟩ : syracuseStep 9426563 = 14139845) B14139845
theorem B12736291 : Blo 1653526 12736291 := bstep (se 1 (by rfl) ⟨9552218, by rfl⟩ : syracuseStep 12736291 = 19104437) B19104437
theorem B2094923 : Blo 1653526 2094923 := bstep (se 1 (by rfl) ⟨1571192, by rfl⟩ : syracuseStep 2094923 = 3142385) B3142385
theorem B5658457 : Blo 1653526 5658457 := bstep (se 2 (by rfl) ⟨2121921, by rfl⟩ : syracuseStep 5658457 = 4243843) B4243843
theorem B9418589 : Blo 1653526 9418589 := bstep (se 3 (by rfl) ⟨1765985, by rfl⟩ : syracuseStep 9418589 = 3531971) B3531971
theorem B5584733 : Blo 1653526 5584733 := bstep (se 3 (by rfl) ⟨1047137, by rfl⟩ : syracuseStep 5584733 = 2094275) B2094275
theorem B13416293 : Blo 1653526 13416293 := bstep (se 4 (by rfl) ⟨1257777, by rfl⟩ : syracuseStep 13416293 = 2515555) B2515555
theorem B23844725 : Blo 1653526 23844725 := bstep (se 5 (by rfl) ⟨1117721, by rfl⟩ : syracuseStep 23844725 = 2235443) B2235443
theorem B2791307 : Blo 1653526 2791307 := bstep (se 1 (by rfl) ⟨2093480, by rfl⟩ : syracuseStep 2791307 = 4186961) B4186961
theorem B10598323 : Blo 1653526 10598323 := bstep (se 1 (by rfl) ⟨7948742, by rfl⟩ : syracuseStep 10598323 = 15897485) B15897485
theorem B14129113 : Blo 1653526 14129113 := bstep (se 2 (by rfl) ⟨5298417, by rfl⟩ : syracuseStep 14129113 = 10596835) B10596835
theorem B2791435 : Blo 1653526 2791435 := bstep (se 1 (by rfl) ⟨2093576, by rfl⟩ : syracuseStep 2791435 = 4187153) B4187153
theorem B2791577 : Blo 1653526 2791577 := bstep (se 2 (by rfl) ⟨1046841, by rfl⟩ : syracuseStep 2791577 = 2093683) B2093683
theorem B14530765 : Blo 1653526 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B2685143 : Blo 1653526 2685143 := bstep (se 1 (by rfl) ⟨2013857, by rfl⟩ : syracuseStep 2685143 = 4027715) B4027715
theorem B2480345 : Blo 1653526 2480345 := bstep (se 2 (by rfl) ⟨930129, by rfl⟩ : syracuseStep 2480345 = 1860259) B1860259
theorem B12728593 : Blo 1653526 12728593 := bstep (se 2 (by rfl) ⟨4773222, by rfl⟩ : syracuseStep 12728593 = 9546445) B9546445
theorem B6281489 : Blo 1653526 6281489 := bstep (se 2 (by rfl) ⟨2355558, by rfl⟩ : syracuseStep 6281489 = 4711117) B4711117
theorem B2791705 : Blo 1653526 2791705 := bstep (se 2 (by rfl) ⟨1046889, by rfl⟩ : syracuseStep 2791705 = 2093779) B2093779
theorem B2480459 : Blo 1653526 2480459 := bstep (se 1 (by rfl) ⟨1860344, by rfl⟩ : syracuseStep 2480459 = 3720689) B3720689
theorem B2480471 : Blo 1653526 2480471 := bstep (se 1 (by rfl) ⟨1860353, by rfl⟩ : syracuseStep 2480471 = 3720707) B3720707
theorem B2480537 : Blo 1653526 2480537 := bstep (se 2 (by rfl) ⟨930201, by rfl⟩ : syracuseStep 2480537 = 1860403) B1860403
theorem B14137861 : Blo 1653526 14137861 := bstep (se 4 (by rfl) ⟨1325424, by rfl⟩ : syracuseStep 14137861 = 2650849) B2650849
theorem B2480651 : Blo 1653526 2480651 := bstep (se 1 (by rfl) ⟨1860488, by rfl⟩ : syracuseStep 2480651 = 3720977) B3720977
theorem B7543313 : Blo 1653526 7543313 := bstep (se 2 (by rfl) ⟨2828742, by rfl⟩ : syracuseStep 7543313 = 5657485) B5657485
theorem B2480663 : Blo 1653526 2480663 := bstep (se 1 (by rfl) ⟨1860497, by rfl⟩ : syracuseStep 2480663 = 3720995) B3720995
theorem B4471319 : Blo 1653526 4471319 := bstep (se 1 (by rfl) ⟨3353489, by rfl⟩ : syracuseStep 4471319 = 6706979) B6706979
theorem B2480729 : Blo 1653526 2480729 := bstep (se 2 (by rfl) ⟨930273, by rfl⟩ : syracuseStep 2480729 = 1860547) B1860547
theorem B2480843 : Blo 1653526 2480843 := bstep (se 1 (by rfl) ⟨1860632, by rfl⟩ : syracuseStep 2480843 = 3721265) B3721265
theorem B2480855 : Blo 1653526 2480855 := bstep (se 1 (by rfl) ⟨1860641, by rfl⟩ : syracuseStep 2480855 = 3721283) B3721283
theorem B6281945 : Blo 1653526 6281945 := bstep (se 2 (by rfl) ⟨2355729, by rfl⟩ : syracuseStep 6281945 = 4711459) B4711459
theorem B1653527 : Blo 1653526 1653527 := bstep (se 1 (by rfl) ⟨1240145, by rfl⟩ : syracuseStep 1653527 = 2480291) B2480291
theorem B2480921 : Blo 1653526 2480921 := bstep (se 2 (by rfl) ⟨930345, by rfl⟩ : syracuseStep 2480921 = 1860691) B1860691
theorem B1653547 : Blo 1653526 1653547 := bstep (se 1 (by rfl) ⟨1240160, by rfl⟩ : syracuseStep 1653547 = 2480321) B2480321
theorem B1653559 : Blo 1653526 1653559 := bstep (se 1 (by rfl) ⟨1240169, by rfl⟩ : syracuseStep 1653559 = 2480339) B2480339
theorem B1653579 : Blo 1653526 1653579 := bstep (se 1 (by rfl) ⟨1240184, by rfl⟩ : syracuseStep 1653579 = 2480369) B2480369
theorem B1653591 : Blo 1653526 1653591 := bstep (se 1 (by rfl) ⟨1240193, by rfl⟩ : syracuseStep 1653591 = 2480387) B2480387
theorem B2792279 : Blo 1653526 2792279 := bstep (se 1 (by rfl) ⟨2094209, by rfl⟩ : syracuseStep 2792279 = 4188419) B4188419
theorem B5299033 : Blo 1653526 5299033 := bstep (se 2 (by rfl) ⟨1987137, by rfl⟩ : syracuseStep 5299033 = 3974275) B3974275
theorem B7068505 : Blo 1653526 7068505 := bstep (se 2 (by rfl) ⟨2650689, by rfl⟩ : syracuseStep 7068505 = 5301379) B5301379
theorem B1653611 : Blo 1653526 1653611 := bstep (se 1 (by rfl) ⟨1240208, by rfl⟩ : syracuseStep 1653611 = 2480417) B2480417
theorem B1653623 : Blo 1653526 1653623 := bstep (se 1 (by rfl) ⟨1240217, by rfl⟩ : syracuseStep 1653623 = 2480435) B2480435
theorem B1653643 : Blo 1653526 1653643 := bstep (se 1 (by rfl) ⟨1240232, by rfl⟩ : syracuseStep 1653643 = 2480465) B2480465
theorem B2481035 : Blo 1653526 2481035 := bstep (se 1 (by rfl) ⟨1860776, by rfl⟩ : syracuseStep 2481035 = 3721553) B3721553
theorem B1653655 : Blo 1653526 1653655 := bstep (se 1 (by rfl) ⟨1240241, by rfl⟩ : syracuseStep 1653655 = 2480483) B2480483
theorem B14130071 : Blo 1653526 14130071 := bstep (se 1 (by rfl) ⟨10597553, by rfl⟩ : syracuseStep 14130071 = 21195107) B21195107
theorem B2481047 : Blo 1653526 2481047 := bstep (se 1 (by rfl) ⟨1860785, by rfl⟩ : syracuseStep 2481047 = 3721571) B3721571
theorem B8379287 : Blo 1653526 8379287 := bstep (se 1 (by rfl) ⟨6284465, by rfl⟩ : syracuseStep 8379287 = 12568931) B12568931
theorem B1653675 : Blo 1653526 1653675 := bstep (se 1 (by rfl) ⟨1240256, by rfl⟩ : syracuseStep 1653675 = 2480513) B2480513
theorem B6282157 : Blo 1653526 6282157 := bstep (se 3 (by rfl) ⟨1177904, by rfl⟩ : syracuseStep 6282157 = 2355809) B2355809
theorem B1653687 : Blo 1653526 1653687 := bstep (se 1 (by rfl) ⟨1240265, by rfl⟩ : syracuseStep 1653687 = 2480531) B2480531
theorem B4422593 : Blo 1653526 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B1653707 : Blo 1653526 1653707 := bstep (se 1 (by rfl) ⟨1240280, by rfl⟩ : syracuseStep 1653707 = 2480561) B2480561
theorem B5585867 : Blo 1653526 5585867 := bstep (se 1 (by rfl) ⟨4189400, by rfl⟩ : syracuseStep 5585867 = 8378801) B8378801
theorem B1653719 : Blo 1653526 1653719 := bstep (se 1 (by rfl) ⟨1240289, by rfl⟩ : syracuseStep 1653719 = 2480579) B2480579
theorem B2792407 : Blo 1653526 2792407 := bstep (se 1 (by rfl) ⟨2094305, by rfl⟩ : syracuseStep 2792407 = 4188611) B4188611
theorem B2481113 : Blo 1653526 2481113 := bstep (se 2 (by rfl) ⟨930417, by rfl⟩ : syracuseStep 2481113 = 1860835) B1860835
theorem B1653739 : Blo 1653526 1653739 := bstep (se 1 (by rfl) ⟨1240304, by rfl⟩ : syracuseStep 1653739 = 2480609) B2480609
theorem B1653751 : Blo 1653526 1653751 := bstep (se 1 (by rfl) ⟨1240313, by rfl⟩ : syracuseStep 1653751 = 2480627) B2480627
theorem B1653771 : Blo 1653526 1653771 := bstep (se 1 (by rfl) ⟨1240328, by rfl⟩ : syracuseStep 1653771 = 2480657) B2480657
theorem B1653783 : Blo 1653526 1653783 := bstep (se 1 (by rfl) ⟨1240337, by rfl⟩ : syracuseStep 1653783 = 2480675) B2480675
theorem B1653803 : Blo 1653526 1653803 := bstep (se 1 (by rfl) ⟨1240352, by rfl⟩ : syracuseStep 1653803 = 2480705) B2480705
theorem B1653815 : Blo 1653526 1653815 := bstep (se 1 (by rfl) ⟨1240361, by rfl⟩ : syracuseStep 1653815 = 2480723) B2480723
theorem B1653835 : Blo 1653526 1653835 := bstep (se 1 (by rfl) ⟨1240376, by rfl⟩ : syracuseStep 1653835 = 2480753) B2480753
theorem B2481227 : Blo 1653526 2481227 := bstep (se 1 (by rfl) ⟨1860920, by rfl⟩ : syracuseStep 2481227 = 3721841) B3721841
theorem B1653847 : Blo 1653526 1653847 := bstep (se 1 (by rfl) ⟨1240385, by rfl⟩ : syracuseStep 1653847 = 2480771) B2480771
theorem B2481239 : Blo 1653526 2481239 := bstep (se 1 (by rfl) ⟨1860929, by rfl⟩ : syracuseStep 2481239 = 3721859) B3721859
theorem B1653867 : Blo 1653526 1653867 := bstep (se 1 (by rfl) ⟨1240400, by rfl⟩ : syracuseStep 1653867 = 2480801) B2480801
theorem B1653879 : Blo 1653526 1653879 := bstep (se 1 (by rfl) ⟨1240409, by rfl⟩ : syracuseStep 1653879 = 2480819) B2480819
theorem B1653899 : Blo 1653526 1653899 := bstep (se 1 (by rfl) ⟨1240424, by rfl⟩ : syracuseStep 1653899 = 2480849) B2480849
theorem B1653911 : Blo 1653526 1653911 := bstep (se 1 (by rfl) ⟨1240433, by rfl⟩ : syracuseStep 1653911 = 2480867) B2480867
theorem B2481305 : Blo 1653526 2481305 := bstep (se 2 (by rfl) ⟨930489, by rfl⟩ : syracuseStep 2481305 = 1860979) B1860979
theorem B1653931 : Blo 1653526 1653931 := bstep (se 1 (by rfl) ⟨1240448, by rfl⟩ : syracuseStep 1653931 = 2480897) B2480897
theorem B1653943 : Blo 1653526 1653943 := bstep (se 1 (by rfl) ⟨1240457, by rfl⟩ : syracuseStep 1653943 = 2480915) B2480915
theorem B5029067 : Blo 1653526 5029067 := bstep (se 1 (by rfl) ⟨3771800, by rfl⟩ : syracuseStep 5029067 = 7543601) B7543601
theorem B1653963 : Blo 1653526 1653963 := bstep (se 1 (by rfl) ⟨1240472, by rfl⟩ : syracuseStep 1653963 = 2480945) B2480945
theorem B4472011 : Blo 1653526 4472011 := bstep (se 1 (by rfl) ⟨3354008, by rfl⟩ : syracuseStep 4472011 = 6708017) B6708017
theorem B1653975 : Blo 1653526 1653975 := bstep (se 1 (by rfl) ⟨1240481, by rfl⟩ : syracuseStep 1653975 = 2480963) B2480963
theorem B5586137 : Blo 1653526 5586137 := bstep (se 2 (by rfl) ⟨2094801, by rfl⟩ : syracuseStep 5586137 = 4189603) B4189603
theorem B6282461 : Blo 1653526 6282461 := bstep (se 3 (by rfl) ⟨1177961, by rfl⟩ : syracuseStep 6282461 = 2355923) B2355923
theorem B1653995 : Blo 1653526 1653995 := bstep (se 1 (by rfl) ⟨1240496, by rfl⟩ : syracuseStep 1653995 = 2480993) B2480993
theorem B1654007 : Blo 1653526 1654007 := bstep (se 1 (by rfl) ⟨1240505, by rfl⟩ : syracuseStep 1654007 = 2481011) B2481011
theorem B1654027 : Blo 1653526 1654027 := bstep (se 1 (by rfl) ⟨1240520, by rfl⟩ : syracuseStep 1654027 = 2481041) B2481041
theorem B2481419 : Blo 1653526 2481419 := bstep (se 1 (by rfl) ⟨1861064, by rfl⟩ : syracuseStep 2481419 = 3722129) B3722129
theorem B14130449 : Blo 1653526 14130449 := bstep (se 2 (by rfl) ⟨5298918, by rfl⟩ : syracuseStep 14130449 = 10597837) B10597837
theorem B2481431 : Blo 1653526 2481431 := bstep (se 1 (by rfl) ⟨1861073, by rfl⟩ : syracuseStep 2481431 = 3722147) B3722147
theorem B1654039 : Blo 1653526 1654039 := bstep (se 1 (by rfl) ⟨1240529, by rfl⟩ : syracuseStep 1654039 = 2481059) B2481059
theorem B1654059 : Blo 1653526 1654059 := bstep (se 1 (by rfl) ⟨1240544, by rfl⟩ : syracuseStep 1654059 = 2481089) B2481089
theorem B1654071 : Blo 1653526 1654071 := bstep (se 1 (by rfl) ⟨1240553, by rfl⟩ : syracuseStep 1654071 = 2481107) B2481107
theorem B1654091 : Blo 1653526 1654091 := bstep (se 1 (by rfl) ⟨1240568, by rfl⟩ : syracuseStep 1654091 = 2481137) B2481137
theorem B1654103 : Blo 1653526 1654103 := bstep (se 1 (by rfl) ⟨1240577, by rfl⟩ : syracuseStep 1654103 = 2481155) B2481155
theorem B2481497 : Blo 1653526 2481497 := bstep (se 2 (by rfl) ⟨930561, by rfl⟩ : syracuseStep 2481497 = 1861123) B1861123
theorem B1654123 : Blo 1653526 1654123 := bstep (se 1 (by rfl) ⟨1240592, by rfl⟩ : syracuseStep 1654123 = 2481185) B2481185
theorem B1654135 : Blo 1653526 1654135 := bstep (se 1 (by rfl) ⟨1240601, by rfl⟩ : syracuseStep 1654135 = 2481203) B2481203
theorem B1654155 : Blo 1653526 1654155 := bstep (se 1 (by rfl) ⟨1240616, by rfl⟩ : syracuseStep 1654155 = 2481233) B2481233
theorem B1654167 : Blo 1653526 1654167 := bstep (se 1 (by rfl) ⟨1240625, by rfl⟩ : syracuseStep 1654167 = 2481251) B2481251
theorem B1654187 : Blo 1653526 1654187 := bstep (se 1 (by rfl) ⟨1240640, by rfl⟩ : syracuseStep 1654187 = 2481281) B2481281
theorem B1654199 : Blo 1653526 1654199 := bstep (se 1 (by rfl) ⟨1240649, by rfl⟩ : syracuseStep 1654199 = 2481299) B2481299
theorem B1654219 : Blo 1653526 1654219 := bstep (se 1 (by rfl) ⟨1240664, by rfl⟩ : syracuseStep 1654219 = 2481329) B2481329
theorem B2481611 : Blo 1653526 2481611 := bstep (se 1 (by rfl) ⟨1861208, by rfl⟩ : syracuseStep 2481611 = 3722417) B3722417
theorem B1654231 : Blo 1653526 1654231 := bstep (se 1 (by rfl) ⟨1240673, by rfl⟩ : syracuseStep 1654231 = 2481347) B2481347
theorem B2481623 : Blo 1653526 2481623 := bstep (se 1 (by rfl) ⟨1861217, by rfl⟩ : syracuseStep 2481623 = 3722435) B3722435
theorem B8371673 : Blo 1653526 8371673 := bstep (se 2 (by rfl) ⟨3139377, by rfl⟩ : syracuseStep 8371673 = 6278755) B6278755
theorem B1654251 : Blo 1653526 1654251 := bstep (se 1 (by rfl) ⟨1240688, by rfl⟩ : syracuseStep 1654251 = 2481377) B2481377
theorem B1654263 : Blo 1653526 1654263 := bstep (se 1 (by rfl) ⟨1240697, by rfl⟩ : syracuseStep 1654263 = 2481395) B2481395
theorem B1654283 : Blo 1653526 1654283 := bstep (se 1 (by rfl) ⟨1240712, by rfl⟩ : syracuseStep 1654283 = 2481425) B2481425
theorem B1654295 : Blo 1653526 1654295 := bstep (se 1 (by rfl) ⟨1240721, by rfl⟩ : syracuseStep 1654295 = 2481443) B2481443
theorem B2481689 : Blo 1653526 2481689 := bstep (se 2 (by rfl) ⟨930633, by rfl⟩ : syracuseStep 2481689 = 1861267) B1861267
theorem B1654315 : Blo 1653526 1654315 := bstep (se 1 (by rfl) ⟨1240736, by rfl⟩ : syracuseStep 1654315 = 2481473) B2481473
theorem B1654327 : Blo 1653526 1654327 := bstep (se 1 (by rfl) ⟨1240745, by rfl⟩ : syracuseStep 1654327 = 2481491) B2481491
theorem B4185665 : Blo 1653526 4185665 := bstep (se 2 (by rfl) ⟨1569624, by rfl⟩ : syracuseStep 4185665 = 3139249) B3139249
theorem B1654347 : Blo 1653526 1654347 := bstep (se 1 (by rfl) ⟨1240760, by rfl⟩ : syracuseStep 1654347 = 2481521) B2481521
theorem B2793035 : Blo 1653526 2793035 := bstep (se 1 (by rfl) ⟨2094776, by rfl⟩ : syracuseStep 2793035 = 4189553) B4189553
theorem B1654359 : Blo 1653526 1654359 := bstep (se 1 (by rfl) ⟨1240769, by rfl⟩ : syracuseStep 1654359 = 2481539) B2481539
theorem B1654379 : Blo 1653526 1654379 := bstep (se 1 (by rfl) ⟨1240784, by rfl⟩ : syracuseStep 1654379 = 2481569) B2481569
theorem B1654391 : Blo 1653526 1654391 := bstep (se 1 (by rfl) ⟨1240793, by rfl⟩ : syracuseStep 1654391 = 2481587) B2481587
theorem B1654411 : Blo 1653526 1654411 := bstep (se 1 (by rfl) ⟨1240808, by rfl⟩ : syracuseStep 1654411 = 2481617) B2481617
theorem B2481803 : Blo 1653526 2481803 := bstep (se 1 (by rfl) ⟨1861352, by rfl⟩ : syracuseStep 2481803 = 3722705) B3722705
theorem B1654423 : Blo 1653526 1654423 := bstep (se 1 (by rfl) ⟨1240817, by rfl⟩ : syracuseStep 1654423 = 2481635) B2481635
theorem B2481815 : Blo 1653526 2481815 := bstep (se 1 (by rfl) ⟨1861361, by rfl⟩ : syracuseStep 2481815 = 3722723) B3722723
theorem B1654443 : Blo 1653526 1654443 := bstep (se 1 (by rfl) ⟨1240832, by rfl⟩ : syracuseStep 1654443 = 2481665) B2481665
theorem B1654455 : Blo 1653526 1654455 := bstep (se 1 (by rfl) ⟨1240841, by rfl⟩ : syracuseStep 1654455 = 2481683) B2481683
theorem B1654475 : Blo 1653526 1654475 := bstep (se 1 (by rfl) ⟨1240856, by rfl⟩ : syracuseStep 1654475 = 2481713) B2481713
theorem B2793163 : Blo 1653526 2793163 := bstep (se 1 (by rfl) ⟨2094872, by rfl⟩ : syracuseStep 2793163 = 4189745) B4189745
theorem B1654487 : Blo 1653526 1654487 := bstep (se 1 (by rfl) ⟨1240865, by rfl⟩ : syracuseStep 1654487 = 2481731) B2481731
theorem B2481881 : Blo 1653526 2481881 := bstep (se 2 (by rfl) ⟨930705, by rfl⟩ : syracuseStep 2481881 = 1861411) B1861411
theorem B1654507 : Blo 1653526 1654507 := bstep (se 1 (by rfl) ⟨1240880, by rfl⟩ : syracuseStep 1654507 = 2481761) B2481761
theorem B1654519 : Blo 1653526 1654519 := bstep (se 1 (by rfl) ⟨1240889, by rfl⟩ : syracuseStep 1654519 = 2481779) B2481779
theorem B1654539 : Blo 1653526 1654539 := bstep (se 1 (by rfl) ⟨1240904, by rfl⟩ : syracuseStep 1654539 = 2481809) B2481809
theorem B1654551 : Blo 1653526 1654551 := bstep (se 1 (by rfl) ⟨1240913, by rfl⟩ : syracuseStep 1654551 = 2481827) B2481827
theorem B7069463 : Blo 1653526 7069463 := bstep (se 1 (by rfl) ⟨5302097, by rfl⟩ : syracuseStep 7069463 = 10604195) B10604195
theorem B1654571 : Blo 1653526 1654571 := bstep (se 1 (by rfl) ⟨1240928, by rfl⟩ : syracuseStep 1654571 = 2481857) B2481857
theorem B1654583 : Blo 1653526 1654583 := bstep (se 1 (by rfl) ⟨1240937, by rfl⟩ : syracuseStep 1654583 = 2481875) B2481875
theorem B3399499 : Blo 1653526 3399499 := bstep (se 1 (by rfl) ⟨2549624, by rfl⟩ : syracuseStep 3399499 = 5099249) B5099249
theorem B1654603 : Blo 1653526 1654603 := bstep (se 1 (by rfl) ⟨1240952, by rfl⟩ : syracuseStep 1654603 = 2481905) B2481905
theorem B2481995 : Blo 1653526 2481995 := bstep (se 1 (by rfl) ⟨1861496, by rfl⟩ : syracuseStep 2481995 = 3722993) B3722993
theorem B1654615 : Blo 1653526 1654615 := bstep (se 1 (by rfl) ⟨1240961, by rfl⟩ : syracuseStep 1654615 = 2481923) B2481923
theorem B2482007 : Blo 1653526 2482007 := bstep (se 1 (by rfl) ⟨1861505, by rfl⟩ : syracuseStep 2482007 = 3723011) B3723011
theorem B2793305 : Blo 1653526 2793305 := bstep (se 2 (by rfl) ⟨1047489, by rfl⟩ : syracuseStep 2793305 = 2094979) B2094979
theorem B1654635 : Blo 1653526 1654635 := bstep (se 1 (by rfl) ⟨1240976, by rfl⟩ : syracuseStep 1654635 = 2481953) B2481953
theorem B1654647 : Blo 1653526 1654647 := bstep (se 1 (by rfl) ⟨1240985, by rfl⟩ : syracuseStep 1654647 = 2481971) B2481971
theorem B1654667 : Blo 1653526 1654667 := bstep (se 1 (by rfl) ⟨1241000, by rfl⟩ : syracuseStep 1654667 = 2482001) B2482001
theorem B1654679 : Blo 1653526 1654679 := bstep (se 1 (by rfl) ⟨1241009, by rfl⟩ : syracuseStep 1654679 = 2482019) B2482019
theorem B5586839 : Blo 1653526 5586839 := bstep (se 1 (by rfl) ⟨4190129, by rfl⟩ : syracuseStep 5586839 = 8380259) B8380259
theorem B2482073 : Blo 1653526 2482073 := bstep (se 2 (by rfl) ⟨930777, by rfl⟩ : syracuseStep 2482073 = 1861555) B1861555
theorem B1654699 : Blo 1653526 1654699 := bstep (se 1 (by rfl) ⟨1241024, by rfl⟩ : syracuseStep 1654699 = 2482049) B2482049
theorem B1654711 : Blo 1653526 1654711 := bstep (se 1 (by rfl) ⟨1241033, by rfl⟩ : syracuseStep 1654711 = 2482067) B2482067
theorem B1654731 : Blo 1653526 1654731 := bstep (se 1 (by rfl) ⟨1241048, by rfl⟩ : syracuseStep 1654731 = 2482097) B2482097
theorem B1654743 : Blo 1653526 1654743 := bstep (se 1 (by rfl) ⟨1241057, by rfl⟩ : syracuseStep 1654743 = 2482115) B2482115
theorem B2793433 : Blo 1653526 2793433 := bstep (se 2 (by rfl) ⟨1047537, by rfl⟩ : syracuseStep 2793433 = 2095075) B2095075
theorem B1654763 : Blo 1653526 1654763 := bstep (se 1 (by rfl) ⟨1241072, by rfl⟩ : syracuseStep 1654763 = 2482145) B2482145
theorem B1654775 : Blo 1653526 1654775 := bstep (se 1 (by rfl) ⟨1241081, by rfl⟩ : syracuseStep 1654775 = 2482163) B2482163
theorem B1654791 : Blo 1653526 1654791 := bstep (se 1 (by rfl) ⟨1241093, by rfl⟩ : syracuseStep 1654791 = 2482187) B2482187
theorem B7544843 : Blo 1653526 7544843 := bstep (se 1 (by rfl) ⟨5658632, by rfl⟩ : syracuseStep 7544843 = 11317265) B11317265
theorem B1654799 : Blo 1653526 1654799 := bstep (se 1 (by rfl) ⟨1241099, by rfl⟩ : syracuseStep 1654799 = 2482199) B2482199
theorem B2793487 : Blo 1653526 2793487 := bstep (se 1 (by rfl) ⟨2095115, by rfl⟩ : syracuseStep 2793487 = 4190231) B4190231
theorem B8060971 : Blo 1653526 8060971 := bstep (se 1 (by rfl) ⟨6045728, by rfl⟩ : syracuseStep 8060971 = 12091457) B12091457
theorem B2981947 : Blo 1653526 2981947 := bstep (se 1 (by rfl) ⟨2236460, by rfl⟩ : syracuseStep 2981947 = 4472921) B4472921
theorem B2482235 : Blo 1653526 2482235 := bstep (se 1 (by rfl) ⟨1861676, by rfl⟩ : syracuseStep 2482235 = 3723353) B3723353
theorem B1654843 : Blo 1653526 1654843 := bstep (se 1 (by rfl) ⟨1241132, by rfl⟩ : syracuseStep 1654843 = 2482265) B2482265
theorem B2482295 : Blo 1653526 2482295 := bstep (se 1 (by rfl) ⟨1861721, by rfl⟩ : syracuseStep 2482295 = 3723443) B3723443
theorem B18841733 : Blo 1653526 18841733 := bstep (se 4 (by rfl) ⟨1766412, by rfl⟩ : syracuseStep 18841733 = 3532825) B3532825
theorem B1654919 : Blo 1653526 1654919 := bstep (se 1 (by rfl) ⟨1241189, by rfl⟩ : syracuseStep 1654919 = 2482379) B2482379
theorem B2482319 : Blo 1653526 2482319 := bstep (se 1 (by rfl) ⟨1861739, by rfl⟩ : syracuseStep 2482319 = 3723479) B3723479
theorem B1654927 : Blo 1653526 1654927 := bstep (se 1 (by rfl) ⟨1241195, by rfl⟩ : syracuseStep 1654927 = 2482391) B2482391
theorem B2482361 : Blo 1653526 2482361 := bstep (se 2 (by rfl) ⟨930885, by rfl⟩ : syracuseStep 2482361 = 1861771) B1861771
theorem B1654971 : Blo 1653526 1654971 := bstep (se 1 (by rfl) ⟨1241228, by rfl⟩ : syracuseStep 1654971 = 2482457) B2482457
theorem B7954625 : Blo 1653526 7954625 := bstep (se 2 (by rfl) ⟨2982984, by rfl⟩ : syracuseStep 7954625 = 5965969) B5965969
theorem B4186313 : Blo 1653526 4186313 := bstep (se 2 (by rfl) ⟨1569867, by rfl⟩ : syracuseStep 4186313 = 3139735) B3139735
theorem B2482439 : Blo 1653526 2482439 := bstep (se 1 (by rfl) ⟨1861829, by rfl⟩ : syracuseStep 2482439 = 3723659) B3723659
theorem B1655047 : Blo 1653526 1655047 := bstep (se 1 (by rfl) ⟨1241285, by rfl⟩ : syracuseStep 1655047 = 2482571) B2482571
theorem B1655055 : Blo 1653526 1655055 := bstep (se 1 (by rfl) ⟨1241291, by rfl⟩ : syracuseStep 1655055 = 2482583) B2482583
theorem B19374353 : Blo 1653526 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B2482475 : Blo 1653526 2482475 := bstep (se 1 (by rfl) ⟨1861856, by rfl⟩ : syracuseStep 2482475 = 3723713) B3723713
theorem B1655099 : Blo 1653526 1655099 := bstep (se 1 (by rfl) ⟨1241324, by rfl⟩ : syracuseStep 1655099 = 2482649) B2482649
theorem B2482505 : Blo 1653526 2482505 := bstep (se 2 (by rfl) ⟨930939, by rfl⟩ : syracuseStep 2482505 = 1861879) B1861879
theorem B2982263 : Blo 1653526 2982263 := bstep (se 1 (by rfl) ⟨2236697, by rfl⟩ : syracuseStep 2982263 = 4473395) B4473395
theorem B1655175 : Blo 1653526 1655175 := bstep (se 1 (by rfl) ⟨1241381, by rfl⟩ : syracuseStep 1655175 = 2482763) B2482763
theorem B1655183 : Blo 1653526 1655183 := bstep (se 1 (by rfl) ⟨1241387, by rfl⟩ : syracuseStep 1655183 = 2482775) B2482775
theorem B46547345 : Blo 1653526 46547345 := bstep (se 2 (by rfl) ⟨17455254, by rfl⟩ : syracuseStep 46547345 = 34910509) B34910509
theorem B2482619 : Blo 1653526 2482619 := bstep (se 1 (by rfl) ⟨1861964, by rfl⟩ : syracuseStep 2482619 = 3723929) B3723929
theorem B1655227 : Blo 1653526 1655227 := bstep (se 1 (by rfl) ⟨1241420, by rfl⟩ : syracuseStep 1655227 = 2482841) B2482841
theorem B7070161 : Blo 1653526 7070161 := bstep (se 2 (by rfl) ⟨2651310, by rfl⟩ : syracuseStep 7070161 = 5302621) B5302621
theorem B2482679 : Blo 1653526 2482679 := bstep (se 1 (by rfl) ⟨1862009, by rfl⟩ : syracuseStep 2482679 = 3724019) B3724019
theorem B1655303 : Blo 1653526 1655303 := bstep (se 1 (by rfl) ⟨1241477, by rfl⟩ : syracuseStep 1655303 = 2482955) B2482955
theorem B2482703 : Blo 1653526 2482703 := bstep (se 1 (by rfl) ⟨1862027, by rfl⟩ : syracuseStep 2482703 = 3724055) B3724055
theorem B1655311 : Blo 1653526 1655311 := bstep (se 1 (by rfl) ⟨1241483, by rfl⟩ : syracuseStep 1655311 = 2482967) B2482967
theorem B13410845 : Blo 1653526 13410845 := bstep (se 3 (by rfl) ⟨2514533, by rfl⟩ : syracuseStep 13410845 = 5029067) B5029067
theorem B5300765 : Blo 1653526 5300765 := bstep (se 3 (by rfl) ⟨993893, by rfl⟩ : syracuseStep 5300765 = 1987787) B1987787
theorem B26821163 : Blo 1653526 26821163 := bstep (se 1 (by rfl) ⟨20115872, by rfl⟩ : syracuseStep 26821163 = 40231745) B40231745
theorem B4186667 : Blo 1653526 4186667 := bstep (se 1 (by rfl) ⟨3140000, by rfl⟩ : syracuseStep 4186667 = 6280001) B6280001
theorem B2482745 : Blo 1653526 2482745 := bstep (se 2 (by rfl) ⟨931029, by rfl⟩ : syracuseStep 2482745 = 1862059) B1862059
theorem B1655355 : Blo 1653526 1655355 := bstep (se 1 (by rfl) ⟨1241516, by rfl⟩ : syracuseStep 1655355 = 2483033) B2483033
theorem B11928131 : Blo 1653526 11928131 := bstep (se 1 (by rfl) ⟨8946098, by rfl⟩ : syracuseStep 11928131 = 17892197) B17892197
theorem B16974413 : Blo 1653526 16974413 := bstep (se 3 (by rfl) ⟨3182702, by rfl⟩ : syracuseStep 16974413 = 6365405) B6365405
theorem B2482823 : Blo 1653526 2482823 := bstep (se 1 (by rfl) ⟨1862117, by rfl⟩ : syracuseStep 2482823 = 3724235) B3724235
theorem B1655431 : Blo 1653526 1655431 := bstep (se 1 (by rfl) ⟨1241573, by rfl⟩ : syracuseStep 1655431 = 2483147) B2483147
theorem B1655439 : Blo 1653526 1655439 := bstep (se 1 (by rfl) ⟨1241579, by rfl⟩ : syracuseStep 1655439 = 2483159) B2483159
theorem B2482859 : Blo 1653526 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B18850481 : Blo 1653526 18850481 := bstep (se 2 (by rfl) ⟨7068930, by rfl⟩ : syracuseStep 18850481 = 14137861) B14137861
theorem B1655483 : Blo 1653526 1655483 := bstep (se 1 (by rfl) ⟨1241612, by rfl⟩ : syracuseStep 1655483 = 2483225) B2483225
theorem B9421505 : Blo 1653526 9421505 := bstep (se 2 (by rfl) ⟨3533064, by rfl⟩ : syracuseStep 9421505 = 7066129) B7066129
theorem B2482889 : Blo 1653526 2482889 := bstep (se 2 (by rfl) ⟨931083, by rfl⟩ : syracuseStep 2482889 = 1862167) B1862167
theorem B9061121 : Blo 1653526 9061121 := bstep (se 2 (by rfl) ⟨3397920, by rfl⟩ : syracuseStep 9061121 = 6795841) B6795841
theorem B1860367 : Blo 1653526 1860367 := bstep (se 1 (by rfl) ⟨1395275, by rfl⟩ : syracuseStep 1860367 = 2790551) B2790551
theorem B2483003 : Blo 1653526 2483003 := bstep (se 1 (by rfl) ⟨1862252, by rfl⟩ : syracuseStep 2483003 = 3724505) B3724505
theorem B2483063 : Blo 1653526 2483063 := bstep (se 1 (by rfl) ⟨1862297, by rfl⟩ : syracuseStep 2483063 = 3724595) B3724595
theorem B2483087 : Blo 1653526 2483087 := bstep (se 1 (by rfl) ⟨1862315, by rfl⟩ : syracuseStep 2483087 = 3724631) B3724631
theorem B2483129 : Blo 1653526 2483129 := bstep (se 2 (by rfl) ⟨931173, by rfl⟩ : syracuseStep 2483129 = 1862347) B1862347
theorem B2483207 : Blo 1653526 2483207 := bstep (se 1 (by rfl) ⟨1862405, by rfl⟩ : syracuseStep 2483207 = 3724811) B3724811
theorem B2483243 : Blo 1653526 2483243 := bstep (se 1 (by rfl) ⟨1862432, by rfl⟩ : syracuseStep 2483243 = 3724865) B3724865
theorem B2483273 : Blo 1653526 2483273 := bstep (se 2 (by rfl) ⟨931227, by rfl⟩ : syracuseStep 2483273 = 1862455) B1862455
theorem B6284375 : Blo 1653526 6284375 := bstep (se 1 (by rfl) ⟨4713281, by rfl⟩ : syracuseStep 6284375 = 9426563) B9426563
theorem B1860871 : Blo 1653526 1860871 := bstep (se 1 (by rfl) ⟨1395653, by rfl⟩ : syracuseStep 1860871 = 2791307) B2791307
theorem B4711709 : Blo 1653526 4711709 := bstep (se 3 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 4711709 = 1766891) B1766891
theorem B15099169 : Blo 1653526 15099169 := bstep (se 2 (by rfl) ⟨5662188, by rfl⟩ : syracuseStep 15099169 = 11324377) B11324377
theorem B3720491 : Blo 1653526 3720491 := bstep (se 1 (by rfl) ⟨2790368, by rfl⟩ : syracuseStep 3720491 = 5580737) B5580737
theorem B21202235 : Blo 1653526 21202235 := bstep (se 1 (by rfl) ⟨15901676, by rfl⟩ : syracuseStep 21202235 = 31803353) B31803353
theorem B15910289 : Blo 1653526 15910289 := bstep (se 2 (by rfl) ⟨5966358, by rfl⟩ : syracuseStep 15910289 = 11932717) B11932717
theorem B1861051 : Blo 1653526 1861051 := bstep (se 1 (by rfl) ⟨1395788, by rfl⟩ : syracuseStep 1861051 = 2791577) B2791577
theorem B4187659 : Blo 1653526 4187659 := bstep (se 1 (by rfl) ⟨3140744, by rfl⟩ : syracuseStep 4187659 = 6281489) B6281489
theorem B8947223 : Blo 1653526 8947223 := bstep (se 1 (by rfl) ⟨6710417, by rfl⟩ : syracuseStep 8947223 = 13420835) B13420835
theorem B6284861 : Blo 1653526 6284861 := bstep (se 3 (by rfl) ⟨1178411, by rfl⟩ : syracuseStep 6284861 = 2356823) B2356823
theorem B3720851 : Blo 1653526 3720851 := bstep (se 1 (by rfl) ⟨2790638, by rfl⟩ : syracuseStep 3720851 = 5581277) B5581277
theorem B4187801 : Blo 1653526 4187801 := bstep (se 2 (by rfl) ⟨1570425, by rfl⟩ : syracuseStep 4187801 = 3140851) B3140851
theorem B3720905 : Blo 1653526 3720905 := bstep (se 2 (by rfl) ⟨1395339, by rfl⟩ : syracuseStep 3720905 = 2790679) B2790679
theorem B5031695 : Blo 1653526 5031695 := bstep (se 1 (by rfl) ⟨3773771, by rfl⟩ : syracuseStep 5031695 = 7547543) B7547543
theorem B4187963 : Blo 1653526 4187963 := bstep (se 1 (by rfl) ⟨3140972, by rfl⟩ : syracuseStep 4187963 = 6281945) B6281945
theorem B1861519 : Blo 1653526 1861519 := bstep (se 1 (by rfl) ⟨1396139, by rfl⟩ : syracuseStep 1861519 = 2792279) B2792279
theorem B4712393 : Blo 1653526 4712393 := bstep (se 2 (by rfl) ⟨1767147, by rfl⟩ : syracuseStep 4712393 = 3534295) B3534295
theorem B4188307 : Blo 1653526 4188307 := bstep (se 1 (by rfl) ⟨3141230, by rfl⟩ : syracuseStep 4188307 = 6282461) B6282461
theorem B57305261 : Blo 1653526 57305261 := bstep (se 3 (by rfl) ⟨10744736, by rfl⟩ : syracuseStep 57305261 = 21489473) B21489473
theorem B4188449 : Blo 1653526 4188449 := bstep (se 2 (by rfl) ⟨1570668, by rfl⟩ : syracuseStep 4188449 = 3141337) B3141337
theorem B5581115 : Blo 1653526 5581115 := bstep (se 1 (by rfl) ⟨4185836, by rfl⟩ : syracuseStep 5581115 = 8371673) B8371673
theorem B3721607 : Blo 1653526 3721607 := bstep (se 1 (by rfl) ⟨2791205, by rfl⟩ : syracuseStep 3721607 = 5582411) B5582411
theorem B1862023 : Blo 1653526 1862023 := bstep (se 1 (by rfl) ⟨1396517, by rfl⟩ : syracuseStep 1862023 = 2793035) B2793035
theorem B4532665 : Blo 1653526 4532665 := bstep (se 2 (by rfl) ⟨1699749, by rfl⟩ : syracuseStep 4532665 = 3399499) B3399499
theorem B4712975 : Blo 1653526 4712975 := bstep (se 1 (by rfl) ⟨3534731, by rfl⟩ : syracuseStep 4712975 = 7069463) B7069463
theorem B3721787 : Blo 1653526 3721787 := bstep (se 1 (by rfl) ⟨2791340, by rfl⟩ : syracuseStep 3721787 = 5582681) B5582681
theorem B1862203 : Blo 1653526 1862203 := bstep (se 1 (by rfl) ⟨1396652, by rfl⟩ : syracuseStep 1862203 = 2793305) B2793305
theorem B7064131 : Blo 1653526 7064131 := bstep (se 1 (by rfl) ⟨5298098, by rfl⟩ : syracuseStep 7064131 = 10596197) B10596197
theorem B5032595 : Blo 1653526 5032595 := bstep (se 1 (by rfl) ⟨3774446, by rfl⟩ : syracuseStep 5032595 = 7548893) B7548893
theorem B3721913 : Blo 1653526 3721913 := bstep (se 2 (by rfl) ⟨1395717, by rfl⟩ : syracuseStep 3721913 = 2791435) B2791435
theorem B5581601 : Blo 1653526 5581601 := bstep (se 2 (by rfl) ⟨2093100, by rfl⟩ : syracuseStep 5581601 = 4186201) B4186201
theorem B3140471 : Blo 1653526 3140471 := bstep (se 1 (by rfl) ⟨2355353, by rfl⟩ : syracuseStep 3140471 = 4710707) B4710707
theorem B7064455 : Blo 1653526 7064455 := bstep (se 1 (by rfl) ⟨5298341, by rfl⟩ : syracuseStep 7064455 = 10596683) B10596683
theorem B7547833 : Blo 1653526 7547833 := bstep (se 2 (by rfl) ⟨2830437, by rfl⟩ : syracuseStep 7547833 = 5660875) B5660875
theorem B3976121 : Blo 1653526 3976121 := bstep (se 2 (by rfl) ⟨1491045, by rfl⟩ : syracuseStep 3976121 = 2982091) B2982091
theorem B5303225 : Blo 1653526 5303225 := bstep (se 2 (by rfl) ⟨1988709, by rfl⟩ : syracuseStep 5303225 = 3977419) B3977419
theorem B3722255 : Blo 1653526 3722255 := bstep (se 1 (by rfl) ⟨2791691, by rfl⟩ : syracuseStep 3722255 = 5583383) B5583383
theorem B3140623 : Blo 1653526 3140623 := bstep (se 1 (by rfl) ⟨2355467, by rfl⟩ : syracuseStep 3140623 = 4710935) B4710935
theorem B3722273 : Blo 1653526 3722273 := bstep (se 2 (by rfl) ⟨1395852, by rfl⟩ : syracuseStep 3722273 = 2791705) B2791705
theorem B40250429 : Blo 1653526 40250429 := bstep (se 3 (by rfl) ⟨7546955, by rfl⟩ : syracuseStep 40250429 = 15093911) B15093911
theorem B14134445 : Blo 1653526 14134445 := bstep (se 3 (by rfl) ⟨2650208, by rfl⟩ : syracuseStep 14134445 = 5300417) B5300417
theorem B4189441 : Blo 1653526 4189441 := bstep (se 2 (by rfl) ⟨1571040, by rfl⟩ : syracuseStep 4189441 = 3142081) B3142081
theorem B7949627 : Blo 1653526 7949627 := bstep (se 1 (by rfl) ⟨5962220, by rfl⟩ : syracuseStep 7949627 = 11924441) B11924441
theorem B5582195 : Blo 1653526 5582195 := bstep (se 1 (by rfl) ⟨4186646, by rfl⟩ : syracuseStep 5582195 = 8373293) B8373293
theorem B3722615 : Blo 1653526 3722615 := bstep (se 1 (by rfl) ⟨2791961, by rfl⟩ : syracuseStep 3722615 = 5583923) B5583923
theorem B3141011 : Blo 1653526 3141011 := bstep (se 1 (by rfl) ⟨2355758, by rfl⟩ : syracuseStep 3141011 = 4711517) B4711517
theorem B31796657 : Blo 1653526 31796657 := bstep (se 2 (by rfl) ⟨11923746, by rfl⟩ : syracuseStep 31796657 = 23847493) B23847493
theorem B3722795 : Blo 1653526 3722795 := bstep (se 1 (by rfl) ⟨2792096, by rfl⟩ : syracuseStep 3722795 = 5584193) B5584193
theorem B2354761 : Blo 1653526 2354761 := bstep (se 2 (by rfl) ⟨883035, by rfl⟩ : syracuseStep 2354761 = 1766071) B1766071
theorem B32681573 : Blo 1653526 32681573 := bstep (se 4 (by rfl) ⟨3063897, by rfl⟩ : syracuseStep 32681573 = 6127795) B6127795
theorem B9678565 : Blo 1653526 9678565 := bstep (se 4 (by rfl) ⟨907365, by rfl⟩ : syracuseStep 9678565 = 1814731) B1814731
theorem B2092807 : Blo 1653526 2092807 := bstep (se 1 (by rfl) ⟨1569605, by rfl⟩ : syracuseStep 2092807 = 3139211) B3139211
theorem B7065377 : Blo 1653526 7065377 := bstep (se 2 (by rfl) ⟨2649516, by rfl⟩ : syracuseStep 7065377 = 5299033) B5299033
theorem B9424673 : Blo 1653526 9424673 := bstep (se 2 (by rfl) ⟨3534252, by rfl⟩ : syracuseStep 9424673 = 7068505) B7068505
theorem B4190039 : Blo 1653526 4190039 := bstep (se 1 (by rfl) ⟨3142529, by rfl⟩ : syracuseStep 4190039 = 6285059) B6285059
theorem B2649991 : Blo 1653526 2649991 := bstep (se 1 (by rfl) ⟨1987493, by rfl⟩ : syracuseStep 2649991 = 3974987) B3974987
theorem B8376209 : Blo 1653526 8376209 := bstep (se 2 (by rfl) ⟨3141078, by rfl⟩ : syracuseStep 8376209 = 6282157) B6282157
theorem B6279059 : Blo 1653526 6279059 := bstep (se 1 (by rfl) ⟨4709294, by rfl⟩ : syracuseStep 6279059 = 9418589) B9418589
theorem B3723155 : Blo 1653526 3723155 := bstep (se 1 (by rfl) ⟨2792366, by rfl⟩ : syracuseStep 3723155 = 5584733) B5584733
theorem B15896483 : Blo 1653526 15896483 := bstep (se 1 (by rfl) ⟨11922362, by rfl⟩ : syracuseStep 15896483 = 23844725) B23844725
theorem B3723209 : Blo 1653526 3723209 := bstep (se 2 (by rfl) ⟨1396203, by rfl⟩ : syracuseStep 3723209 = 2792407) B2792407
theorem B4190251 : Blo 1653526 4190251 := bstep (se 1 (by rfl) ⟨3142688, by rfl⟩ : syracuseStep 4190251 = 6285377) B6285377
theorem B2355257 : Blo 1653526 2355257 := bstep (se 2 (by rfl) ⟨883221, by rfl⟩ : syracuseStep 2355257 = 1766443) B1766443
theorem B11923517 : Blo 1653526 11923517 := bstep (se 3 (by rfl) ⟨2235659, by rfl⟩ : syracuseStep 11923517 = 4471319) B4471319
theorem B1790095 : Blo 1653526 1790095 := bstep (se 1 (by rfl) ⟨1342571, by rfl⟩ : syracuseStep 1790095 = 2685143) B2685143
theorem B4190393 : Blo 1653526 4190393 := bstep (se 2 (by rfl) ⟨1571397, by rfl⟩ : syracuseStep 4190393 = 3142795) B3142795
theorem B2093303 : Blo 1653526 2093303 := bstep (se 1 (by rfl) ⟨1569977, by rfl⟩ : syracuseStep 2093303 = 3139955) B3139955
theorem B2830727 : Blo 1653526 2830727 := bstep (se 1 (by rfl) ⟨2123045, by rfl⟩ : syracuseStep 2830727 = 4246091) B4246091
theorem B2093455 : Blo 1653526 2093455 := bstep (se 1 (by rfl) ⟨1570091, by rfl⟩ : syracuseStep 2093455 = 3140183) B3140183
theorem B2650639 : Blo 1653526 2650639 := bstep (se 1 (by rfl) ⟨1987979, by rfl⟩ : syracuseStep 2650639 = 3975959) B3975959
theorem B2093627 : Blo 1653526 2093627 := bstep (se 1 (by rfl) ⟨1570220, by rfl⟩ : syracuseStep 2093627 = 3140441) B3140441
theorem B3723911 : Blo 1653526 3723911 := bstep (se 1 (by rfl) ⟨2792933, by rfl⟩ : syracuseStep 3723911 = 5585867) B5585867
theorem B2650895 : Blo 1653526 2650895 := bstep (se 1 (by rfl) ⟨1988171, by rfl⟩ : syracuseStep 2650895 = 3976343) B3976343
theorem B3142415 : Blo 1653526 3142415 := bstep (se 1 (by rfl) ⟨2356811, by rfl⟩ : syracuseStep 3142415 = 4713623) B4713623
theorem B3724091 : Blo 1653526 3724091 := bstep (se 1 (by rfl) ⟨2793068, by rfl⟩ : syracuseStep 3724091 = 5586137) B5586137
theorem B10064729 : Blo 1653526 10064729 := bstep (se 2 (by rfl) ⟨3774273, by rfl⟩ : syracuseStep 10064729 = 7548547) B7548547
theorem B5313433 : Blo 1653526 5313433 := bstep (se 2 (by rfl) ⟨1992537, by rfl⟩ : syracuseStep 5313433 = 3985075) B3985075
theorem B3724217 : Blo 1653526 3724217 := bstep (se 2 (by rfl) ⟨1396581, by rfl⟩ : syracuseStep 3724217 = 2793163) B2793163
theorem B2356231 : Blo 1653526 2356231 := bstep (se 1 (by rfl) ⟨1767173, by rfl⟩ : syracuseStep 2356231 = 3534347) B3534347
theorem B2790443 : Blo 1653526 2790443 := bstep (se 1 (by rfl) ⟨2092832, by rfl⟩ : syracuseStep 2790443 = 4185665) B4185665
theorem B9417815 : Blo 1653526 9417815 := bstep (se 1 (by rfl) ⟨7063361, by rfl⟩ : syracuseStep 9417815 = 14126723) B14126723
theorem B3724559 : Blo 1653526 3724559 := bstep (se 1 (by rfl) ⟨2793419, by rfl⟩ : syracuseStep 3724559 = 5586839) B5586839
theorem B18838817 : Blo 1653526 18838817 := bstep (se 2 (by rfl) ⟨7064556, by rfl⟩ : syracuseStep 18838817 = 14129113) B14129113
theorem B3724577 : Blo 1653526 3724577 := bstep (se 2 (by rfl) ⟨1396716, by rfl⟩ : syracuseStep 3724577 = 2793433) B2793433
theorem B2790841 : Blo 1653526 2790841 := bstep (se 2 (by rfl) ⟨1046565, by rfl⟩ : syracuseStep 2790841 = 2093131) B2093131
theorem B2094599 : Blo 1653526 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B3724919 : Blo 1653526 3724919 := bstep (se 1 (by rfl) ⟨2793689, by rfl⟩ : syracuseStep 3724919 = 5587379) B5587379
theorem B42981043 : Blo 1653526 42981043 := bstep (se 1 (by rfl) ⟨32235782, by rfl⟩ : syracuseStep 42981043 = 64471565) B64471565
theorem B16971457 : Blo 1653526 16971457 := bstep (se 2 (by rfl) ⟨6364296, by rfl⟩ : syracuseStep 16971457 = 12728593) B12728593
theorem B8722235 : Blo 1653526 8722235 := bstep (se 1 (by rfl) ⟨6541676, by rfl⟩ : syracuseStep 8722235 = 13083353) B13083353
theorem B5584787 : Blo 1653526 5584787 := bstep (se 1 (by rfl) ⟨4188590, by rfl⟩ : syracuseStep 5584787 = 8377181) B8377181
theorem B8378315 : Blo 1653526 8378315 := bstep (se 1 (by rfl) ⟨6283736, by rfl⟩ : syracuseStep 8378315 = 12567473) B12567473
theorem B4773917 : Blo 1653526 4773917 := bstep (se 3 (by rfl) ⟨895109, by rfl⟩ : syracuseStep 4773917 = 1790219) B1790219
theorem B4364321 : Blo 1653526 4364321 := bstep (se 2 (by rfl) ⟨1636620, by rfl⟩ : syracuseStep 4364321 = 3273241) B3273241
theorem B11196503 : Blo 1653526 11196503 := bstep (se 1 (by rfl) ⟨8397377, by rfl⟩ : syracuseStep 11196503 = 16794755) B16794755
theorem B2791543 : Blo 1653526 2791543 := bstep (se 1 (by rfl) ⟨2093657, by rfl⟩ : syracuseStep 2791543 = 4187315) B4187315
theorem B9427063 : Blo 1653526 9427063 := bstep (se 1 (by rfl) ⟨7070297, by rfl⟩ : syracuseStep 9427063 = 14140595) B14140595
theorem B2095247 : Blo 1653526 2095247 := bstep (se 1 (by rfl) ⟨1571435, by rfl⟩ : syracuseStep 2095247 = 3142871) B3142871
theorem B2480315 : Blo 1653526 2480315 := bstep (se 1 (by rfl) ⟨1860236, by rfl⟩ : syracuseStep 2480315 = 3720473) B3720473
theorem B2480375 : Blo 1653526 2480375 := bstep (se 1 (by rfl) ⟨1860281, by rfl⟩ : syracuseStep 2480375 = 3720563) B3720563
theorem B2480399 : Blo 1653526 2480399 := bstep (se 1 (by rfl) ⟨1860299, by rfl⟩ : syracuseStep 2480399 = 3720599) B3720599
theorem B8378639 : Blo 1653526 8378639 := bstep (se 1 (by rfl) ⟨6283979, by rfl⟩ : syracuseStep 8378639 = 12567959) B12567959
theorem B2480441 : Blo 1653526 2480441 := bstep (se 2 (by rfl) ⟨930165, by rfl⟩ : syracuseStep 2480441 = 1860331) B1860331
theorem B2791739 : Blo 1653526 2791739 := bstep (se 1 (by rfl) ⟨2093804, by rfl⟩ : syracuseStep 2791739 = 4187609) B4187609
theorem B5298547 : Blo 1653526 5298547 := bstep (se 1 (by rfl) ⟨3973910, by rfl⟩ : syracuseStep 5298547 = 7947821) B7947821
theorem B2480519 : Blo 1653526 2480519 := bstep (se 1 (by rfl) ⟨1860389, by rfl⟩ : syracuseStep 2480519 = 3720779) B3720779
theorem B2234795 : Blo 1653526 2234795 := bstep (se 1 (by rfl) ⟨1676096, by rfl⟩ : syracuseStep 2234795 = 3352193) B3352193
theorem B2480555 : Blo 1653526 2480555 := bstep (se 1 (by rfl) ⟨1860416, by rfl⟩ : syracuseStep 2480555 = 3720833) B3720833
theorem B4708793 : Blo 1653526 4708793 := bstep (se 2 (by rfl) ⟨1765797, by rfl⟩ : syracuseStep 4708793 = 3531595) B3531595
theorem B6281657 : Blo 1653526 6281657 := bstep (se 2 (by rfl) ⟨2355621, by rfl⟩ : syracuseStep 6281657 = 4711243) B4711243
theorem B2480585 : Blo 1653526 2480585 := bstep (se 2 (by rfl) ⟨930219, by rfl⟩ : syracuseStep 2480585 = 1860439) B1860439
theorem B2480699 : Blo 1653526 2480699 := bstep (se 1 (by rfl) ⟨1860524, by rfl⟩ : syracuseStep 2480699 = 3721049) B3721049
theorem B8944195 : Blo 1653526 8944195 := bstep (se 1 (by rfl) ⟨6708146, by rfl⟩ : syracuseStep 8944195 = 13416293) B13416293
theorem B2480759 : Blo 1653526 2480759 := bstep (se 1 (by rfl) ⟨1860569, by rfl⟩ : syracuseStep 2480759 = 3721139) B3721139
theorem B2480783 : Blo 1653526 2480783 := bstep (se 1 (by rfl) ⟨1860587, by rfl⟩ : syracuseStep 2480783 = 3721175) B3721175
theorem B2480825 : Blo 1653526 2480825 := bstep (se 2 (by rfl) ⟨930309, by rfl⟩ : syracuseStep 2480825 = 1860619) B1860619
theorem B8493761 : Blo 1653526 8493761 := bstep (se 2 (by rfl) ⟨3185160, by rfl⟩ : syracuseStep 8493761 = 6370321) B6370321
theorem B2792137 : Blo 1653526 2792137 := bstep (se 2 (by rfl) ⟨1047051, by rfl⟩ : syracuseStep 2792137 = 2094103) B2094103
theorem B2480903 : Blo 1653526 2480903 := bstep (se 1 (by rfl) ⟨1860677, by rfl⟩ : syracuseStep 2480903 = 3721355) B3721355
theorem B2480939 : Blo 1653526 2480939 := bstep (se 1 (by rfl) ⟨1860704, by rfl⟩ : syracuseStep 2480939 = 3721409) B3721409
theorem B1653563 : Blo 1653526 1653563 := bstep (se 1 (by rfl) ⟨1240172, by rfl⟩ : syracuseStep 1653563 = 2480345) B2480345
theorem B2480969 : Blo 1653526 2480969 := bstep (se 2 (by rfl) ⟨930363, by rfl⟩ : syracuseStep 2480969 = 1860727) B1860727
theorem B1653639 : Blo 1653526 1653639 := bstep (se 1 (by rfl) ⟨1240229, by rfl⟩ : syracuseStep 1653639 = 2480459) B2480459
theorem B1653647 : Blo 1653526 1653647 := bstep (se 1 (by rfl) ⟨1240235, by rfl⟩ : syracuseStep 1653647 = 2480471) B2480471
theorem B7953299 : Blo 1653526 7953299 := bstep (se 1 (by rfl) ⟨5964974, by rfl⟩ : syracuseStep 7953299 = 11929949) B11929949
theorem B5962681 : Blo 1653526 5962681 := bstep (se 2 (by rfl) ⟨2236005, by rfl⟩ : syracuseStep 5962681 = 4472011) B4472011
theorem B1653691 : Blo 1653526 1653691 := bstep (se 1 (by rfl) ⟨1240268, by rfl⟩ : syracuseStep 1653691 = 2480537) B2480537
theorem B2481083 : Blo 1653526 2481083 := bstep (se 1 (by rfl) ⟨1860812, by rfl⟩ : syracuseStep 2481083 = 3721625) B3721625
theorem B2481143 : Blo 1653526 2481143 := bstep (se 1 (by rfl) ⟨1860857, by rfl⟩ : syracuseStep 2481143 = 3721715) B3721715
theorem B1653767 : Blo 1653526 1653767 := bstep (se 1 (by rfl) ⟨1240325, by rfl⟩ : syracuseStep 1653767 = 2480651) B2480651
theorem B5028875 : Blo 1653526 5028875 := bstep (se 1 (by rfl) ⟨3771656, by rfl⟩ : syracuseStep 5028875 = 7543313) B7543313
theorem B1653775 : Blo 1653526 1653775 := bstep (se 1 (by rfl) ⟨1240331, by rfl⟩ : syracuseStep 1653775 = 2480663) B2480663
theorem B2481167 : Blo 1653526 2481167 := bstep (se 1 (by rfl) ⟨1860875, by rfl⟩ : syracuseStep 2481167 = 3721751) B3721751
theorem B2481209 : Blo 1653526 2481209 := bstep (se 2 (by rfl) ⟨930453, by rfl⟩ : syracuseStep 2481209 = 1860907) B1860907
theorem B1653819 : Blo 1653526 1653819 := bstep (se 1 (by rfl) ⟨1240364, by rfl⟩ : syracuseStep 1653819 = 2480729) B2480729
theorem B1653895 : Blo 1653526 1653895 := bstep (se 1 (by rfl) ⟨1240421, by rfl⟩ : syracuseStep 1653895 = 2480843) B2480843
theorem B2481287 : Blo 1653526 2481287 := bstep (se 1 (by rfl) ⟨1860965, by rfl⟩ : syracuseStep 2481287 = 3721931) B3721931
theorem B1653903 : Blo 1653526 1653903 := bstep (se 1 (by rfl) ⟨1240427, by rfl⟩ : syracuseStep 1653903 = 2480855) B2480855
theorem B2481323 : Blo 1653526 2481323 := bstep (se 1 (by rfl) ⟨1860992, by rfl⟩ : syracuseStep 2481323 = 3721985) B3721985
theorem B1653947 : Blo 1653526 1653947 := bstep (se 1 (by rfl) ⟨1240460, by rfl⟩ : syracuseStep 1653947 = 2480921) B2480921
theorem B2481353 : Blo 1653526 2481353 := bstep (se 2 (by rfl) ⟨930507, by rfl⟩ : syracuseStep 2481353 = 1861015) B1861015
theorem B1654023 : Blo 1653526 1654023 := bstep (se 1 (by rfl) ⟨1240517, by rfl⟩ : syracuseStep 1654023 = 2481035) B2481035
theorem B9420047 : Blo 1653526 9420047 := bstep (se 1 (by rfl) ⟨7065035, by rfl⟩ : syracuseStep 9420047 = 14130071) B14130071
theorem B1654031 : Blo 1653526 1654031 := bstep (se 1 (by rfl) ⟨1240523, by rfl⟩ : syracuseStep 1654031 = 2481047) B2481047
theorem B5586191 : Blo 1653526 5586191 := bstep (se 1 (by rfl) ⟨4189643, by rfl⟩ : syracuseStep 5586191 = 8379287) B8379287
theorem B2948395 : Blo 1653526 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B1654075 : Blo 1653526 1654075 := bstep (se 1 (by rfl) ⟨1240556, by rfl⟩ : syracuseStep 1654075 = 2481113) B2481113
theorem B2481467 : Blo 1653526 2481467 := bstep (se 1 (by rfl) ⟨1861100, by rfl⟩ : syracuseStep 2481467 = 3722201) B3722201
theorem B9428339 : Blo 1653526 9428339 := bstep (se 1 (by rfl) ⟨7071254, by rfl⟩ : syracuseStep 9428339 = 14142509) B14142509
theorem B2481527 : Blo 1653526 2481527 := bstep (se 1 (by rfl) ⟨1861145, by rfl⟩ : syracuseStep 2481527 = 3722291) B3722291
theorem B1654151 : Blo 1653526 1654151 := bstep (se 1 (by rfl) ⟨1240613, by rfl⟩ : syracuseStep 1654151 = 2481227) B2481227
theorem B2792839 : Blo 1653526 2792839 := bstep (se 1 (by rfl) ⟨2094629, by rfl⟩ : syracuseStep 2792839 = 4189259) B4189259
theorem B1654159 : Blo 1653526 1654159 := bstep (se 1 (by rfl) ⟨1240619, by rfl⟩ : syracuseStep 1654159 = 2481239) B2481239
theorem B2481551 : Blo 1653526 2481551 := bstep (se 1 (by rfl) ⟨1861163, by rfl⟩ : syracuseStep 2481551 = 3722327) B3722327
theorem B6282643 : Blo 1653526 6282643 := bstep (se 1 (by rfl) ⟨4711982, by rfl⟩ : syracuseStep 6282643 = 9423965) B9423965
theorem B4709785 : Blo 1653526 4709785 := bstep (se 2 (by rfl) ⟨1766169, by rfl⟩ : syracuseStep 4709785 = 3532339) B3532339
theorem B12557753 : Blo 1653526 12557753 := bstep (se 2 (by rfl) ⟨4709157, by rfl⟩ : syracuseStep 12557753 = 9418315) B9418315
theorem B2481593 : Blo 1653526 2481593 := bstep (se 2 (by rfl) ⟨930597, by rfl⟩ : syracuseStep 2481593 = 1861195) B1861195
theorem B1654203 : Blo 1653526 1654203 := bstep (se 1 (by rfl) ⟨1240652, by rfl⟩ : syracuseStep 1654203 = 2481305) B2481305
theorem B1654279 : Blo 1653526 1654279 := bstep (se 1 (by rfl) ⟨1240709, by rfl⟩ : syracuseStep 1654279 = 2481419) B2481419
theorem B2481671 : Blo 1653526 2481671 := bstep (se 1 (by rfl) ⟨1861253, by rfl⟩ : syracuseStep 2481671 = 3722507) B3722507
theorem B9420299 : Blo 1653526 9420299 := bstep (se 1 (by rfl) ⟨7065224, by rfl⟩ : syracuseStep 9420299 = 14130449) B14130449
theorem B1654287 : Blo 1653526 1654287 := bstep (se 1 (by rfl) ⟨1240715, by rfl⟩ : syracuseStep 1654287 = 2481431) B2481431
theorem B5586461 : Blo 1653526 5586461 := bstep (se 3 (by rfl) ⟨1047461, by rfl⟩ : syracuseStep 5586461 = 2094923) B2094923
theorem B2481707 : Blo 1653526 2481707 := bstep (se 1 (by rfl) ⟨1861280, by rfl⟩ : syracuseStep 2481707 = 3722561) B3722561
theorem B1654331 : Blo 1653526 1654331 := bstep (se 1 (by rfl) ⟨1240748, by rfl⟩ : syracuseStep 1654331 = 2481497) B2481497
theorem B2481737 : Blo 1653526 2481737 := bstep (se 2 (by rfl) ⟨930651, by rfl⟩ : syracuseStep 2481737 = 1861303) B1861303
theorem B4185715 : Blo 1653526 4185715 := bstep (se 1 (by rfl) ⟨3139286, by rfl⟩ : syracuseStep 4185715 = 6278573) B6278573
theorem B1654407 : Blo 1653526 1654407 := bstep (se 1 (by rfl) ⟨1240805, by rfl⟩ : syracuseStep 1654407 = 2481611) B2481611
theorem B1654415 : Blo 1653526 1654415 := bstep (se 1 (by rfl) ⟨1240811, by rfl⟩ : syracuseStep 1654415 = 2481623) B2481623
theorem B1654459 : Blo 1653526 1654459 := bstep (se 1 (by rfl) ⟨1240844, by rfl⟩ : syracuseStep 1654459 = 2481689) B2481689
theorem B2481851 : Blo 1653526 2481851 := bstep (se 1 (by rfl) ⟨1861388, by rfl⟩ : syracuseStep 2481851 = 3722777) B3722777
theorem B8380097 : Blo 1653526 8380097 := bstep (se 2 (by rfl) ⟨3142536, by rfl⟩ : syracuseStep 8380097 = 6285073) B6285073
theorem B16981721 : Blo 1653526 16981721 := bstep (se 2 (by rfl) ⟨6368145, by rfl⟩ : syracuseStep 16981721 = 12736291) B12736291
theorem B2481911 : Blo 1653526 2481911 := bstep (se 1 (by rfl) ⟨1861433, by rfl⟩ : syracuseStep 2481911 = 3722867) B3722867
theorem B4185857 : Blo 1653526 4185857 := bstep (se 2 (by rfl) ⟨1569696, by rfl⟩ : syracuseStep 4185857 = 3139393) B3139393
theorem B1654535 : Blo 1653526 1654535 := bstep (se 1 (by rfl) ⟨1240901, by rfl⟩ : syracuseStep 1654535 = 2481803) B2481803
theorem B1654543 : Blo 1653526 1654543 := bstep (se 1 (by rfl) ⟨1240907, by rfl⟩ : syracuseStep 1654543 = 2481815) B2481815
theorem B2481935 : Blo 1653526 2481935 := bstep (se 1 (by rfl) ⟨1861451, by rfl⟩ : syracuseStep 2481935 = 3722903) B3722903
theorem B7544609 : Blo 1653526 7544609 := bstep (se 2 (by rfl) ⟨2829228, by rfl⟩ : syracuseStep 7544609 = 5658457) B5658457
theorem B2481977 : Blo 1653526 2481977 := bstep (se 2 (by rfl) ⟨930741, by rfl⟩ : syracuseStep 2481977 = 1861483) B1861483
theorem B1654587 : Blo 1653526 1654587 := bstep (se 1 (by rfl) ⟨1240940, by rfl⟩ : syracuseStep 1654587 = 2481881) B2481881
theorem B1654663 : Blo 1653526 1654663 := bstep (se 1 (by rfl) ⟨1240997, by rfl⟩ : syracuseStep 1654663 = 2481995) B2481995
theorem B2482055 : Blo 1653526 2482055 := bstep (se 1 (by rfl) ⟨1861541, by rfl⟩ : syracuseStep 2482055 = 3723083) B3723083
theorem B1654671 : Blo 1653526 1654671 := bstep (se 1 (by rfl) ⟨1241003, by rfl⟩ : syracuseStep 1654671 = 2482007) B2482007
theorem B14131097 : Blo 1653526 14131097 := bstep (se 2 (by rfl) ⟨5299161, by rfl⟩ : syracuseStep 14131097 = 10598323) B10598323
theorem B2482091 : Blo 1653526 2482091 := bstep (se 1 (by rfl) ⟨1861568, by rfl⟩ : syracuseStep 2482091 = 3723137) B3723137
theorem B1654715 : Blo 1653526 1654715 := bstep (se 1 (by rfl) ⟨1241036, by rfl⟩ : syracuseStep 1654715 = 2482073) B2482073
theorem B2482121 : Blo 1653526 2482121 := bstep (se 2 (by rfl) ⟨930795, by rfl⟩ : syracuseStep 2482121 = 1861591) B1861591
theorem B5029895 : Blo 1653526 5029895 := bstep (se 1 (by rfl) ⟨3772421, by rfl⟩ : syracuseStep 5029895 = 7544843) B7544843
theorem B1654823 : Blo 1653526 1654823 := bstep (se 1 (by rfl) ⟨1241117, by rfl⟩ : syracuseStep 1654823 = 2482235) B2482235
theorem B10747961 : Blo 1653526 10747961 := bstep (se 2 (by rfl) ⟨4030485, by rfl⟩ : syracuseStep 10747961 = 8060971) B8060971
theorem B5587001 : Blo 1653526 5587001 := bstep (se 2 (by rfl) ⟨2095125, by rfl⟩ : syracuseStep 5587001 = 4190251) B4190251
theorem B1654863 : Blo 1653526 1654863 := bstep (se 1 (by rfl) ⟨1241147, by rfl⟩ : syracuseStep 1654863 = 2482295) B2482295
theorem B1654879 : Blo 1653526 1654879 := bstep (se 1 (by rfl) ⟨1241159, by rfl⟩ : syracuseStep 1654879 = 2482319) B2482319
theorem B1654907 : Blo 1653526 1654907 := bstep (se 1 (by rfl) ⟨1241180, by rfl⟩ : syracuseStep 1654907 = 2482361) B2482361
theorem B2793595 : Blo 1653526 2793595 := bstep (se 1 (by rfl) ⟨2095196, by rfl⟩ : syracuseStep 2793595 = 4190393) B4190393
theorem B1654959 : Blo 1653526 1654959 := bstep (se 1 (by rfl) ⟨1241219, by rfl⟩ : syracuseStep 1654959 = 2482439) B2482439
theorem B1654983 : Blo 1653526 1654983 := bstep (se 1 (by rfl) ⟨1241237, by rfl⟩ : syracuseStep 1654983 = 2482475) B2482475
theorem B1655003 : Blo 1653526 1655003 := bstep (se 1 (by rfl) ⟨1241252, by rfl⟩ : syracuseStep 1655003 = 2482505) B2482505
theorem B1655079 : Blo 1653526 1655079 := bstep (se 1 (by rfl) ⟨1241309, by rfl⟩ : syracuseStep 1655079 = 2482619) B2482619
theorem B1655119 : Blo 1653526 1655119 := bstep (se 1 (by rfl) ⟨1241339, by rfl⟩ : syracuseStep 1655119 = 2482679) B2482679
theorem B1655135 : Blo 1653526 1655135 := bstep (se 1 (by rfl) ⟨1241351, by rfl⟩ : syracuseStep 1655135 = 2482703) B2482703
theorem B1655163 : Blo 1653526 1655163 := bstep (se 1 (by rfl) ⟨1241372, by rfl⟩ : syracuseStep 1655163 = 2482745) B2482745
theorem B5587325 : Blo 1653526 5587325 := bstep (se 3 (by rfl) ⟨1047623, by rfl⟩ : syracuseStep 5587325 = 2095247) B2095247
theorem B12558725 : Blo 1653526 12558725 := bstep (se 4 (by rfl) ⟨1177380, by rfl⟩ : syracuseStep 12558725 = 2354761) B2354761
theorem B2482607 : Blo 1653526 2482607 := bstep (se 1 (by rfl) ⟨1861955, by rfl⟩ : syracuseStep 2482607 = 3723911) B3723911
theorem B1655215 : Blo 1653526 1655215 := bstep (se 1 (by rfl) ⟨1241411, by rfl⟩ : syracuseStep 1655215 = 2482823) B2482823
theorem B1655239 : Blo 1653526 1655239 := bstep (se 1 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 1655239 = 2482859) B2482859
theorem B12566987 : Blo 1653526 12566987 := bstep (se 1 (by rfl) ⟨9425240, by rfl⟩ : syracuseStep 12566987 = 18850481) B18850481
theorem B1655259 : Blo 1653526 1655259 := bstep (se 1 (by rfl) ⟨1241444, by rfl⟩ : syracuseStep 1655259 = 2482889) B2482889
theorem B2482697 : Blo 1653526 2482697 := bstep (se 2 (by rfl) ⟨931011, by rfl⟩ : syracuseStep 2482697 = 1862023) B1862023
theorem B2482727 : Blo 1653526 2482727 := bstep (se 1 (by rfl) ⟨1862045, by rfl⟩ : syracuseStep 2482727 = 3724091) B3724091
theorem B1655335 : Blo 1653526 1655335 := bstep (se 1 (by rfl) ⟨1241501, by rfl⟩ : syracuseStep 1655335 = 2483003) B2483003
theorem B6709819 : Blo 1653526 6709819 := bstep (se 1 (by rfl) ⟨5032364, by rfl⟩ : syracuseStep 6709819 = 10064729) B10064729
theorem B1655375 : Blo 1653526 1655375 := bstep (se 1 (by rfl) ⟨1241531, by rfl⟩ : syracuseStep 1655375 = 2483063) B2483063
theorem B1655391 : Blo 1653526 1655391 := bstep (se 1 (by rfl) ⟨1241543, by rfl⟩ : syracuseStep 1655391 = 2483087) B2483087
theorem B2482811 : Blo 1653526 2482811 := bstep (se 1 (by rfl) ⟨1862108, by rfl⟩ : syracuseStep 2482811 = 3724217) B3724217
theorem B1655419 : Blo 1653526 1655419 := bstep (se 1 (by rfl) ⟨1241564, by rfl⟩ : syracuseStep 1655419 = 2483129) B2483129
theorem B1655471 : Blo 1653526 1655471 := bstep (se 1 (by rfl) ⟨1241603, by rfl⟩ : syracuseStep 1655471 = 2483207) B2483207
theorem B1860295 : Blo 1653526 1860295 := bstep (se 1 (by rfl) ⟨1395221, by rfl⟩ : syracuseStep 1860295 = 2790443) B2790443
theorem B1655495 : Blo 1653526 1655495 := bstep (se 1 (by rfl) ⟨1241621, by rfl⟩ : syracuseStep 1655495 = 2483243) B2483243
theorem B1655515 : Blo 1653526 1655515 := bstep (se 1 (by rfl) ⟨1241636, by rfl⟩ : syracuseStep 1655515 = 2483273) B2483273
theorem B2482937 : Blo 1653526 2482937 := bstep (se 2 (by rfl) ⟨931101, by rfl⟩ : syracuseStep 2482937 = 1862203) B1862203
theorem B2483039 : Blo 1653526 2483039 := bstep (se 1 (by rfl) ⟨1862279, by rfl⟩ : syracuseStep 2483039 = 3724559) B3724559
theorem B12559211 : Blo 1653526 12559211 := bstep (se 1 (by rfl) ⟨9419408, by rfl⟩ : syracuseStep 12559211 = 18838817) B18838817
theorem B2483051 : Blo 1653526 2483051 := bstep (se 1 (by rfl) ⟨1862288, by rfl⟩ : syracuseStep 2483051 = 3724577) B3724577
theorem B5964815 : Blo 1653526 5964815 := bstep (se 1 (by rfl) ⟨4473611, by rfl⟩ : syracuseStep 5964815 = 8947223) B8947223
theorem B124126253 : Blo 1653526 124126253 := bstep (se 3 (by rfl) ⟨23273672, by rfl⟩ : syracuseStep 124126253 = 46547345) B46547345
theorem B2483279 : Blo 1653526 2483279 := bstep (se 1 (by rfl) ⟨1862459, by rfl⟩ : syracuseStep 2483279 = 3724919) B3724919
theorem B31810805 : Blo 1653526 31810805 := bstep (se 5 (by rfl) ⟨1491131, by rfl⟩ : syracuseStep 31810805 = 2982263) B2982263
theorem B4187497 : Blo 1653526 4187497 := bstep (se 2 (by rfl) ⟨1570311, by rfl⟩ : syracuseStep 4187497 = 3140623) B3140623
theorem B7464335 : Blo 1653526 7464335 := bstep (se 1 (by rfl) ⟨5598251, by rfl⟩ : syracuseStep 7464335 = 11196503) B11196503
theorem B3720743 : Blo 1653526 3720743 := bstep (se 1 (by rfl) ⟨2790557, by rfl⟩ : syracuseStep 3720743 = 5581115) B5581115
theorem B1861159 : Blo 1653526 1861159 := bstep (se 1 (by rfl) ⟨1395869, by rfl⟩ : syracuseStep 1861159 = 2791739) B2791739
theorem B4187771 : Blo 1653526 4187771 := bstep (se 1 (by rfl) ⟨3140828, by rfl⟩ : syracuseStep 4187771 = 6281657) B6281657
theorem B3721067 : Blo 1653526 3721067 := bstep (se 1 (by rfl) ⟨2790800, by rfl⟩ : syracuseStep 3721067 = 5581601) B5581601
theorem B3721121 : Blo 1653526 3721121 := bstep (se 2 (by rfl) ⟨1395420, by rfl⟩ : syracuseStep 3721121 = 2790841) B2790841
theorem B5302199 : Blo 1653526 5302199 := bstep (se 1 (by rfl) ⟨3976649, by rfl⟩ : syracuseStep 5302199 = 7953299) B7953299
theorem B3352583 : Blo 1653526 3352583 := bstep (se 1 (by rfl) ⟨2514437, by rfl⟩ : syracuseStep 3352583 = 5028875) B5028875
theorem B9422963 : Blo 1653526 9422963 := bstep (se 1 (by rfl) ⟨7067222, by rfl⟩ : syracuseStep 9422963 = 14134445) B14134445
theorem B5580953 : Blo 1653526 5580953 := bstep (se 2 (by rfl) ⟨2092857, by rfl⟩ : syracuseStep 5580953 = 4185715) B4185715
theorem B3721463 : Blo 1653526 3721463 := bstep (se 1 (by rfl) ⟨2791097, by rfl⟩ : syracuseStep 3721463 = 5582195) B5582195
theorem B6285559 : Blo 1653526 6285559 := bstep (se 1 (by rfl) ⟨4714169, by rfl⟩ : syracuseStep 6285559 = 9428339) B9428339
theorem B22628609 : Blo 1653526 22628609 := bstep (se 2 (by rfl) ⟨8485728, by rfl⟩ : syracuseStep 22628609 = 16971457) B16971457
theorem B12904753 : Blo 1653526 12904753 := bstep (se 2 (by rfl) ⟨4839282, by rfl⟩ : syracuseStep 12904753 = 9678565) B9678565
theorem B8374589 : Blo 1653526 8374589 := bstep (se 3 (by rfl) ⟨1570235, by rfl⟩ : syracuseStep 8374589 = 3140471) B3140471
theorem B3533321 : Blo 1653526 3533321 := bstep (se 2 (by rfl) ⟨1324995, by rfl⟩ : syracuseStep 3533321 = 2649991) B2649991
theorem B7949011 : Blo 1653526 7949011 := bstep (se 1 (by rfl) ⟨5961758, by rfl⟩ : syracuseStep 7949011 = 11923517) B11923517
theorem B3975929 : Blo 1653526 3975929 := bstep (se 2 (by rfl) ⟨1490973, by rfl⟩ : syracuseStep 3975929 = 2981947) B2981947
theorem B12561155 : Blo 1653526 12561155 := bstep (se 1 (by rfl) ⟨9420866, by rfl⟩ : syracuseStep 12561155 = 18841733) B18841733
theorem B5303083 : Blo 1653526 5303083 := bstep (se 1 (by rfl) ⟨3977312, by rfl⟩ : syracuseStep 5303083 = 7954625) B7954625
theorem B3722057 : Blo 1653526 3722057 := bstep (se 2 (by rfl) ⟨1395771, by rfl⟩ : syracuseStep 3722057 = 2791543) B2791543
theorem B12569417 : Blo 1653526 12569417 := bstep (se 2 (by rfl) ⟨4713531, by rfl⟩ : syracuseStep 12569417 = 9427063) B9427063
theorem B2386793 : Blo 1653526 2386793 := bstep (se 2 (by rfl) ⟨895047, by rfl⟩ : syracuseStep 2386793 = 1790095) B1790095
theorem B1887151 : Blo 1653526 1887151 := bstep (se 1 (by rfl) ⟨1415363, by rfl⟩ : syracuseStep 1887151 = 2830727) B2830727
theorem B8940563 : Blo 1653526 8940563 := bstep (se 1 (by rfl) ⟨6705422, by rfl⟩ : syracuseStep 8940563 = 13410845) B13410845
theorem B3533843 : Blo 1653526 3533843 := bstep (se 1 (by rfl) ⟨2650382, by rfl⟩ : syracuseStep 3533843 = 5300765) B5300765
theorem B11316275 : Blo 1653526 11316275 := bstep (se 1 (by rfl) ⟨8487206, by rfl⟩ : syracuseStep 11316275 = 16974413) B16974413
theorem B7064729 : Blo 1653526 7064729 := bstep (se 2 (by rfl) ⟨2649273, by rfl⟩ : syracuseStep 7064729 = 5298547) B5298547
theorem B6040747 : Blo 1653526 6040747 := bstep (se 1 (by rfl) ⟨4530560, by rfl⟩ : syracuseStep 6040747 = 9061121) B9061121
theorem B5582141 : Blo 1653526 5582141 := bstep (se 3 (by rfl) ⟨1046651, by rfl⟩ : syracuseStep 5582141 = 2093303) B2093303
theorem B3534185 : Blo 1653526 3534185 := bstep (se 2 (by rfl) ⟨1325319, by rfl⟩ : syracuseStep 3534185 = 2650639) B2650639
theorem B6278543 : Blo 1653526 6278543 := bstep (se 1 (by rfl) ⟨4708907, by rfl⟩ : syracuseStep 6278543 = 9417815) B9417815
theorem B4189583 : Blo 1653526 4189583 := bstep (se 1 (by rfl) ⟨3142187, by rfl⟩ : syracuseStep 4189583 = 6284375) B6284375
theorem B14134823 : Blo 1653526 14134823 := bstep (se 1 (by rfl) ⟨10601117, by rfl⟩ : syracuseStep 14134823 = 21202235) B21202235
theorem B3722849 : Blo 1653526 3722849 := bstep (se 2 (by rfl) ⟨1396068, by rfl⟩ : syracuseStep 3722849 = 2792137) B2792137
theorem B4189907 : Blo 1653526 4189907 := bstep (se 1 (by rfl) ⟨3142430, by rfl⟩ : syracuseStep 4189907 = 6284861) B6284861
theorem B5959453 : Blo 1653526 5959453 := bstep (se 3 (by rfl) ⟨1117397, by rfl⟩ : syracuseStep 5959453 = 2234795) B2234795
theorem B3354463 : Blo 1653526 3354463 := bstep (se 1 (by rfl) ⟨2515847, by rfl⟩ : syracuseStep 3354463 = 5031695) B5031695
theorem B7950241 : Blo 1653526 7950241 := bstep (se 2 (by rfl) ⟨2981340, by rfl⟩ : syracuseStep 7950241 = 5962681) B5962681
theorem B10063777 : Blo 1653526 10063777 := bstep (se 2 (by rfl) ⟨3773916, by rfl⟩ : syracuseStep 10063777 = 7547833) B7547833
theorem B3723191 : Blo 1653526 3723191 := bstep (se 1 (by rfl) ⟨2792393, by rfl⟩ : syracuseStep 3723191 = 5584787) B5584787
theorem B3141595 : Blo 1653526 3141595 := bstep (se 1 (by rfl) ⟨2356196, by rfl⟩ : syracuseStep 3141595 = 4712393) B4712393
theorem B3141641 : Blo 1653526 3141641 := bstep (se 2 (by rfl) ⟨1178115, by rfl⟩ : syracuseStep 3141641 = 2356231) B2356231
theorem B3182611 : Blo 1653526 3182611 := bstep (se 1 (by rfl) ⟨2386958, by rfl⟩ : syracuseStep 3182611 = 4773917) B4773917
theorem B38203507 : Blo 1653526 38203507 := bstep (se 1 (by rfl) ⟨28652630, by rfl⟩ : syracuseStep 38203507 = 57305261) B57305261
theorem B5583005 : Blo 1653526 5583005 := bstep (se 3 (by rfl) ⟨1046813, by rfl⟩ : syracuseStep 5583005 = 2093627) B2093627
theorem B3141983 : Blo 1653526 3141983 := bstep (se 1 (by rfl) ⟨2356487, by rfl⟩ : syracuseStep 3141983 = 4712975) B4712975
theorem B20132225 : Blo 1653526 20132225 := bstep (se 2 (by rfl) ⟨7549584, by rfl⟩ : syracuseStep 20132225 = 15099169) B15099169
theorem B3355063 : Blo 1653526 3355063 := bstep (se 1 (by rfl) ⟨2516297, by rfl⟩ : syracuseStep 3355063 = 5032595) B5032595
theorem B3723785 : Blo 1653526 3723785 := bstep (se 2 (by rfl) ⟨1396419, by rfl⟩ : syracuseStep 3723785 = 2792839) B2792839
theorem B8376857 : Blo 1653526 8376857 := bstep (se 2 (by rfl) ⟨3141321, by rfl⟩ : syracuseStep 8376857 = 6282643) B6282643
theorem B6279713 : Blo 1653526 6279713 := bstep (se 2 (by rfl) ⟨2354892, by rfl⟩ : syracuseStep 6279713 = 4709785) B4709785
theorem B2650747 : Blo 1653526 2650747 := bstep (se 1 (by rfl) ⟨1988060, by rfl⟩ : syracuseStep 2650747 = 3976121) B3976121
theorem B3535483 : Blo 1653526 3535483 := bstep (se 1 (by rfl) ⟨2651612, by rfl⟩ : syracuseStep 3535483 = 5303225) B5303225
theorem B5583545 : Blo 1653526 5583545 := bstep (se 2 (by rfl) ⟨2093829, by rfl⟩ : syracuseStep 5583545 = 4187659) B4187659
theorem B26833619 : Blo 1653526 26833619 := bstep (se 1 (by rfl) ⟨20125214, by rfl⟩ : syracuseStep 26833619 = 40250429) B40250429
theorem B6280031 : Blo 1653526 6280031 := bstep (se 1 (by rfl) ⟨4710023, by rfl⟩ : syracuseStep 6280031 = 9420047) B9420047
theorem B3724127 : Blo 1653526 3724127 := bstep (se 1 (by rfl) ⟨2793095, by rfl⟩ : syracuseStep 3724127 = 5586191) B5586191
theorem B57308057 : Blo 1653526 57308057 := bstep (se 2 (by rfl) ⟨21490521, by rfl⟩ : syracuseStep 57308057 = 42981043) B42981043
theorem B2094007 : Blo 1653526 2094007 := bstep (se 1 (by rfl) ⟨1570505, by rfl⟩ : syracuseStep 2094007 = 3141011) B3141011
theorem B21197771 : Blo 1653526 21197771 := bstep (se 1 (by rfl) ⟨15898328, by rfl⟩ : syracuseStep 21197771 = 31796657) B31796657
theorem B6280199 : Blo 1653526 6280199 := bstep (se 1 (by rfl) ⟨4710149, by rfl⟩ : syracuseStep 6280199 = 9420299) B9420299
theorem B2790409 : Blo 1653526 2790409 := bstep (se 2 (by rfl) ⟨1046403, by rfl⟩ : syracuseStep 2790409 = 2092807) B2092807
theorem B3724307 : Blo 1653526 3724307 := bstep (se 1 (by rfl) ⟨2793230, by rfl⟩ : syracuseStep 3724307 = 5586461) B5586461
theorem B21787715 : Blo 1653526 21787715 := bstep (se 1 (by rfl) ⟨16340786, by rfl⟩ : syracuseStep 21787715 = 32681573) B32681573
theorem B2790571 : Blo 1653526 2790571 := bstep (se 1 (by rfl) ⟨2092928, by rfl⟩ : syracuseStep 2790571 = 4185857) B4185857
theorem B5584139 : Blo 1653526 5584139 := bstep (se 1 (by rfl) ⟨4188104, by rfl⟩ : syracuseStep 5584139 = 8376209) B8376209
theorem B10597655 : Blo 1653526 10597655 := bstep (se 1 (by rfl) ⟨7948241, by rfl⟩ : syracuseStep 10597655 = 15896483) B15896483
theorem B3724649 : Blo 1653526 3724649 := bstep (se 2 (by rfl) ⟨1396743, by rfl⟩ : syracuseStep 3724649 = 2793487) B2793487
theorem B11638189 : Blo 1653526 11638189 := bstep (se 3 (by rfl) ⟨2182160, by rfl⟩ : syracuseStep 11638189 = 4364321) B4364321
theorem B2790875 : Blo 1653526 2790875 := bstep (se 1 (by rfl) ⟨2093156, by rfl⟩ : syracuseStep 2790875 = 4186313) B4186313
theorem B6280685 : Blo 1653526 6280685 := bstep (se 3 (by rfl) ⟨1177628, by rfl⟩ : syracuseStep 6280685 = 2355257) B2355257
theorem B12916235 : Blo 1653526 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B5584409 : Blo 1653526 5584409 := bstep (se 2 (by rfl) ⟨2094153, by rfl⟩ : syracuseStep 5584409 = 4188307) B4188307
theorem B2791111 : Blo 1653526 2791111 := bstep (se 1 (by rfl) ⟨2093333, by rfl⟩ : syracuseStep 2791111 = 4186667) B4186667
theorem B7952087 : Blo 1653526 7952087 := bstep (se 1 (by rfl) ⟨5964065, by rfl⟩ : syracuseStep 7952087 = 11928131) B11928131
theorem B6281003 : Blo 1653526 6281003 := bstep (se 1 (by rfl) ⟨4710752, by rfl⟩ : syracuseStep 6281003 = 9421505) B9421505
theorem B1767263 : Blo 1653526 1767263 := bstep (se 1 (by rfl) ⟨1325447, by rfl⟩ : syracuseStep 1767263 = 2650895) B2650895
theorem B2791273 : Blo 1653526 2791273 := bstep (se 2 (by rfl) ⟨1046727, by rfl⟩ : syracuseStep 2791273 = 2093455) B2093455
theorem B6043553 : Blo 1653526 6043553 := bstep (se 2 (by rfl) ⟨2266332, by rfl⟩ : syracuseStep 6043553 = 4532665) B4532665
theorem B9426881 : Blo 1653526 9426881 := bstep (se 2 (by rfl) ⟨3535080, by rfl⟩ : syracuseStep 9426881 = 7070161) B7070161
theorem B12564557 : Blo 1653526 12564557 := bstep (se 3 (by rfl) ⟨2355854, by rfl⟩ : syracuseStep 12564557 = 4711709) B4711709
theorem B9418841 : Blo 1653526 9418841 := bstep (se 2 (by rfl) ⟨3532065, by rfl⟩ : syracuseStep 9418841 = 7064131) B7064131
theorem B11925593 : Blo 1653526 11925593 := bstep (se 2 (by rfl) ⟨4472097, by rfl⟩ : syracuseStep 11925593 = 8944195) B8944195
theorem B2480327 : Blo 1653526 2480327 := bstep (se 1 (by rfl) ⟨1860245, by rfl⟩ : syracuseStep 2480327 = 3720491) B3720491
theorem B10606859 : Blo 1653526 10606859 := bstep (se 1 (by rfl) ⟨7955144, by rfl⟩ : syracuseStep 10606859 = 15910289) B15910289
theorem B2480489 : Blo 1653526 2480489 := bstep (se 2 (by rfl) ⟨930183, by rfl⟩ : syracuseStep 2480489 = 1860367) B1860367
theorem B2480567 : Blo 1653526 2480567 := bstep (se 1 (by rfl) ⟨1860425, by rfl⟩ : syracuseStep 2480567 = 3720851) B3720851
theorem B2791867 : Blo 1653526 2791867 := bstep (se 1 (by rfl) ⟨2093900, by rfl⟩ : syracuseStep 2791867 = 4187801) B4187801
theorem B2480603 : Blo 1653526 2480603 := bstep (se 1 (by rfl) ⟨1860452, by rfl⟩ : syracuseStep 2480603 = 3720905) B3720905
theorem B12556781 : Blo 1653526 12556781 := bstep (se 3 (by rfl) ⟨2354396, by rfl⟩ : syracuseStep 12556781 = 4708793) B4708793
theorem B9419273 : Blo 1653526 9419273 := bstep (se 2 (by rfl) ⟨3532227, by rfl⟩ : syracuseStep 9419273 = 7064455) B7064455
theorem B7084577 : Blo 1653526 7084577 := bstep (se 2 (by rfl) ⟨2656716, by rfl⟩ : syracuseStep 7084577 = 5313433) B5313433
theorem B5814823 : Blo 1653526 5814823 := bstep (se 1 (by rfl) ⟨4361117, by rfl⟩ : syracuseStep 5814823 = 8722235) B8722235
theorem B2791975 : Blo 1653526 2791975 := bstep (se 1 (by rfl) ⟨2093981, by rfl⟩ : syracuseStep 2791975 = 4187963) B4187963
theorem B5585543 : Blo 1653526 5585543 := bstep (se 1 (by rfl) ⟨4189157, by rfl⟩ : syracuseStep 5585543 = 8378315) B8378315
theorem B5585597 : Blo 1653526 5585597 := bstep (se 3 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 5585597 = 2094599) B2094599
theorem B71523101 : Blo 1653526 71523101 := bstep (se 3 (by rfl) ⟨13410581, by rfl⟩ : syracuseStep 71523101 = 26821163) B26821163
theorem B1653543 : Blo 1653526 1653543 := bstep (se 1 (by rfl) ⟨1240157, by rfl⟩ : syracuseStep 1653543 = 2480315) B2480315
theorem B1653583 : Blo 1653526 1653583 := bstep (se 1 (by rfl) ⟨1240187, by rfl⟩ : syracuseStep 1653583 = 2480375) B2480375
theorem B1653599 : Blo 1653526 1653599 := bstep (se 1 (by rfl) ⟨1240199, by rfl⟩ : syracuseStep 1653599 = 2480399) B2480399
theorem B5585759 : Blo 1653526 5585759 := bstep (se 1 (by rfl) ⟨4189319, by rfl⟩ : syracuseStep 5585759 = 8378639) B8378639
theorem B2792299 : Blo 1653526 2792299 := bstep (se 1 (by rfl) ⟨2094224, by rfl⟩ : syracuseStep 2792299 = 4188449) B4188449
theorem B1653627 : Blo 1653526 1653627 := bstep (se 1 (by rfl) ⟨1240220, by rfl⟩ : syracuseStep 1653627 = 2480441) B2480441
theorem B1653679 : Blo 1653526 1653679 := bstep (se 1 (by rfl) ⟨1240259, by rfl⟩ : syracuseStep 1653679 = 2480519) B2480519
theorem B2481071 : Blo 1653526 2481071 := bstep (se 1 (by rfl) ⟨1860803, by rfl⟩ : syracuseStep 2481071 = 3721607) B3721607
theorem B1653703 : Blo 1653526 1653703 := bstep (se 1 (by rfl) ⟨1240277, by rfl⟩ : syracuseStep 1653703 = 2480555) B2480555
theorem B1653723 : Blo 1653526 1653723 := bstep (se 1 (by rfl) ⟨1240292, by rfl⟩ : syracuseStep 1653723 = 2480585) B2480585
theorem B5585921 : Blo 1653526 5585921 := bstep (se 2 (by rfl) ⟨2094720, by rfl⟩ : syracuseStep 5585921 = 4189441) B4189441
theorem B2481161 : Blo 1653526 2481161 := bstep (se 2 (by rfl) ⟨930435, by rfl⟩ : syracuseStep 2481161 = 1860871) B1860871
theorem B1653799 : Blo 1653526 1653799 := bstep (se 1 (by rfl) ⟨1240349, by rfl⟩ : syracuseStep 1653799 = 2480699) B2480699
theorem B2481191 : Blo 1653526 2481191 := bstep (se 1 (by rfl) ⟨1860893, by rfl⟩ : syracuseStep 2481191 = 3721787) B3721787
theorem B3931193 : Blo 1653526 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B1653839 : Blo 1653526 1653839 := bstep (se 1 (by rfl) ⟨1240379, by rfl⟩ : syracuseStep 1653839 = 2480759) B2480759
theorem B1653855 : Blo 1653526 1653855 := bstep (se 1 (by rfl) ⟨1240391, by rfl⟩ : syracuseStep 1653855 = 2480783) B2480783
theorem B1653883 : Blo 1653526 1653883 := bstep (se 1 (by rfl) ⟨1240412, by rfl⟩ : syracuseStep 1653883 = 2480825) B2480825
theorem B2481275 : Blo 1653526 2481275 := bstep (se 1 (by rfl) ⟨1860956, by rfl⟩ : syracuseStep 2481275 = 3721913) B3721913
theorem B22650029 : Blo 1653526 22650029 := bstep (se 3 (by rfl) ⟨4246880, by rfl⟩ : syracuseStep 22650029 = 8493761) B8493761
theorem B1653935 : Blo 1653526 1653935 := bstep (se 1 (by rfl) ⟨1240451, by rfl⟩ : syracuseStep 1653935 = 2480903) B2480903
theorem B1653959 : Blo 1653526 1653959 := bstep (se 1 (by rfl) ⟨1240469, by rfl⟩ : syracuseStep 1653959 = 2480939) B2480939
theorem B1653979 : Blo 1653526 1653979 := bstep (se 1 (by rfl) ⟨1240484, by rfl⟩ : syracuseStep 1653979 = 2480969) B2480969
theorem B2481401 : Blo 1653526 2481401 := bstep (se 2 (by rfl) ⟨930525, by rfl⟩ : syracuseStep 2481401 = 1861051) B1861051
theorem B1654055 : Blo 1653526 1654055 := bstep (se 1 (by rfl) ⟨1240541, by rfl⟩ : syracuseStep 1654055 = 2481083) B2481083
theorem B1654095 : Blo 1653526 1654095 := bstep (se 1 (by rfl) ⟨1240571, by rfl⟩ : syracuseStep 1654095 = 2481143) B2481143
theorem B1654111 : Blo 1653526 1654111 := bstep (se 1 (by rfl) ⟨1240583, by rfl⟩ : syracuseStep 1654111 = 2481167) B2481167
theorem B2481503 : Blo 1653526 2481503 := bstep (se 1 (by rfl) ⟨1861127, by rfl⟩ : syracuseStep 2481503 = 3722255) B3722255
theorem B2481515 : Blo 1653526 2481515 := bstep (se 1 (by rfl) ⟨1861136, by rfl⟩ : syracuseStep 2481515 = 3722273) B3722273
theorem B1654139 : Blo 1653526 1654139 := bstep (se 1 (by rfl) ⟨1240604, by rfl⟩ : syracuseStep 1654139 = 2481209) B2481209
theorem B8379773 : Blo 1653526 8379773 := bstep (se 3 (by rfl) ⟨1571207, by rfl⟩ : syracuseStep 8379773 = 3142415) B3142415
theorem B1654191 : Blo 1653526 1654191 := bstep (se 1 (by rfl) ⟨1240643, by rfl⟩ : syracuseStep 1654191 = 2481287) B2481287
theorem B1654215 : Blo 1653526 1654215 := bstep (se 1 (by rfl) ⟨1240661, by rfl⟩ : syracuseStep 1654215 = 2481323) B2481323
theorem B1654235 : Blo 1653526 1654235 := bstep (se 1 (by rfl) ⟨1240676, by rfl⟩ : syracuseStep 1654235 = 2481353) B2481353
theorem B5299751 : Blo 1653526 5299751 := bstep (se 1 (by rfl) ⟨3974813, by rfl⟩ : syracuseStep 5299751 = 7949627) B7949627
theorem B1654311 : Blo 1653526 1654311 := bstep (se 1 (by rfl) ⟨1240733, by rfl⟩ : syracuseStep 1654311 = 2481467) B2481467
theorem B1654351 : Blo 1653526 1654351 := bstep (se 1 (by rfl) ⟨1240763, by rfl⟩ : syracuseStep 1654351 = 2481527) B2481527
theorem B2481743 : Blo 1653526 2481743 := bstep (se 1 (by rfl) ⟨1861307, by rfl⟩ : syracuseStep 2481743 = 3722615) B3722615
theorem B1654367 : Blo 1653526 1654367 := bstep (se 1 (by rfl) ⟨1240775, by rfl⟩ : syracuseStep 1654367 = 2481551) B2481551
theorem B8371835 : Blo 1653526 8371835 := bstep (se 1 (by rfl) ⟨6278876, by rfl⟩ : syracuseStep 8371835 = 12557753) B12557753
theorem B1654395 : Blo 1653526 1654395 := bstep (se 1 (by rfl) ⟨1240796, by rfl⟩ : syracuseStep 1654395 = 2481593) B2481593
theorem B1654447 : Blo 1653526 1654447 := bstep (se 1 (by rfl) ⟨1240835, by rfl⟩ : syracuseStep 1654447 = 2481671) B2481671
theorem B1654471 : Blo 1653526 1654471 := bstep (se 1 (by rfl) ⟨1240853, by rfl⟩ : syracuseStep 1654471 = 2481707) B2481707
theorem B2481863 : Blo 1653526 2481863 := bstep (se 1 (by rfl) ⟨1861397, by rfl⟩ : syracuseStep 2481863 = 3722795) B3722795
theorem B1654491 : Blo 1653526 1654491 := bstep (se 1 (by rfl) ⟨1240868, by rfl⟩ : syracuseStep 1654491 = 2481737) B2481737
theorem B1654567 : Blo 1653526 1654567 := bstep (se 1 (by rfl) ⟨1240925, by rfl⟩ : syracuseStep 1654567 = 2481851) B2481851
theorem B5586731 : Blo 1653526 5586731 := bstep (se 1 (by rfl) ⟨4190048, by rfl⟩ : syracuseStep 5586731 = 8380097) B8380097
theorem B11321147 : Blo 1653526 11321147 := bstep (se 1 (by rfl) ⟨8490860, by rfl⟩ : syracuseStep 11321147 = 16981721) B16981721
theorem B1654607 : Blo 1653526 1654607 := bstep (se 1 (by rfl) ⟨1240955, by rfl⟩ : syracuseStep 1654607 = 2481911) B2481911
theorem B1654623 : Blo 1653526 1654623 := bstep (se 1 (by rfl) ⟨1240967, by rfl⟩ : syracuseStep 1654623 = 2481935) B2481935
theorem B2482025 : Blo 1653526 2482025 := bstep (se 2 (by rfl) ⟨930759, by rfl⟩ : syracuseStep 2482025 = 1861519) B1861519
theorem B5029739 : Blo 1653526 5029739 := bstep (se 1 (by rfl) ⟨3772304, by rfl⟩ : syracuseStep 5029739 = 7544609) B7544609
theorem B4710251 : Blo 1653526 4710251 := bstep (se 1 (by rfl) ⟨3532688, by rfl⟩ : syracuseStep 4710251 = 7065377) B7065377
theorem B6283115 : Blo 1653526 6283115 := bstep (se 1 (by rfl) ⟨4712336, by rfl⟩ : syracuseStep 6283115 = 9424673) B9424673
theorem B1654651 : Blo 1653526 1654651 := bstep (se 1 (by rfl) ⟨1240988, by rfl⟩ : syracuseStep 1654651 = 2481977) B2481977
theorem B2793359 : Blo 1653526 2793359 := bstep (se 1 (by rfl) ⟨2095019, by rfl⟩ : syracuseStep 2793359 = 4190039) B4190039
theorem B1654703 : Blo 1653526 1654703 := bstep (se 1 (by rfl) ⟨1241027, by rfl⟩ : syracuseStep 1654703 = 2482055) B2482055
theorem B4186039 : Blo 1653526 4186039 := bstep (se 1 (by rfl) ⟨3139529, by rfl⟩ : syracuseStep 4186039 = 6279059) B6279059
theorem B2482103 : Blo 1653526 2482103 := bstep (se 1 (by rfl) ⟨1861577, by rfl⟩ : syracuseStep 2482103 = 3723155) B3723155
theorem B9420731 : Blo 1653526 9420731 := bstep (se 1 (by rfl) ⟨7065548, by rfl⟩ : syracuseStep 9420731 = 14131097) B14131097
theorem B1654727 : Blo 1653526 1654727 := bstep (se 1 (by rfl) ⟨1241045, by rfl⟩ : syracuseStep 1654727 = 2482091) B2482091
theorem B1654747 : Blo 1653526 1654747 := bstep (se 1 (by rfl) ⟨1241060, by rfl⟩ : syracuseStep 1654747 = 2482121) B2482121
theorem B2482139 : Blo 1653526 2482139 := bstep (se 1 (by rfl) ⟨1861604, by rfl⟩ : syracuseStep 2482139 = 3723209) B3723209
theorem B4243481 : Blo 1653526 4243481 := bstep (se 2 (by rfl) ⟨1591305, by rfl⟩ : syracuseStep 4243481 = 3182611) B3182611
theorem B8372483 : Blo 1653526 8372483 := bstep (se 1 (by rfl) ⟨6279362, by rfl⟩ : syracuseStep 8372483 = 12558725) B12558725
theorem B1655071 : Blo 1653526 1655071 := bstep (se 1 (by rfl) ⟨1241303, by rfl⟩ : syracuseStep 1655071 = 2482607) B2482607
theorem B8380745 : Blo 1653526 8380745 := bstep (se 2 (by rfl) ⟨3142779, by rfl⟩ : syracuseStep 8380745 = 6285559) B6285559
theorem B2482523 : Blo 1653526 2482523 := bstep (se 1 (by rfl) ⟨1861892, by rfl⟩ : syracuseStep 2482523 = 3723785) B3723785
theorem B1655131 : Blo 1653526 1655131 := bstep (se 1 (by rfl) ⟨1241348, by rfl⟩ : syracuseStep 1655131 = 2482697) B2482697
theorem B4186475 : Blo 1653526 4186475 := bstep (se 1 (by rfl) ⟨3139856, by rfl⟩ : syracuseStep 4186475 = 6279713) B6279713
theorem B1655151 : Blo 1653526 1655151 := bstep (se 1 (by rfl) ⟨1241363, by rfl⟩ : syracuseStep 1655151 = 2482727) B2482727
theorem B1655207 : Blo 1653526 1655207 := bstep (se 1 (by rfl) ⟨1241405, by rfl⟩ : syracuseStep 1655207 = 2482811) B2482811
theorem B1655291 : Blo 1653526 1655291 := bstep (se 1 (by rfl) ⟨1241468, by rfl⟩ : syracuseStep 1655291 = 2482937) B2482937
theorem B4186687 : Blo 1653526 4186687 := bstep (se 1 (by rfl) ⟨3140015, by rfl⟩ : syracuseStep 4186687 = 6280031) B6280031
theorem B2482751 : Blo 1653526 2482751 := bstep (se 1 (by rfl) ⟨1862063, by rfl⟩ : syracuseStep 2482751 = 3724127) B3724127
theorem B1655359 : Blo 1653526 1655359 := bstep (se 1 (by rfl) ⟨1241519, by rfl⟩ : syracuseStep 1655359 = 2483039) B2483039
theorem B8372807 : Blo 1653526 8372807 := bstep (se 1 (by rfl) ⟨6279605, by rfl⟩ : syracuseStep 8372807 = 12559211) B12559211
theorem B1655367 : Blo 1653526 1655367 := bstep (se 1 (by rfl) ⟨1241525, by rfl⟩ : syracuseStep 1655367 = 2483051) B2483051
theorem B203752037 : Blo 1653526 203752037 := bstep (se 4 (by rfl) ⟨19101753, by rfl⟩ : syracuseStep 203752037 = 38203507) B38203507
theorem B14131847 : Blo 1653526 14131847 := bstep (se 1 (by rfl) ⟨10598885, by rfl⟩ : syracuseStep 14131847 = 21197771) B21197771
theorem B4186799 : Blo 1653526 4186799 := bstep (se 1 (by rfl) ⟨3140099, by rfl⟩ : syracuseStep 4186799 = 6280199) B6280199
theorem B2482871 : Blo 1653526 2482871 := bstep (se 1 (by rfl) ⟨1862153, by rfl⟩ : syracuseStep 2482871 = 3724307) B3724307
theorem B1655519 : Blo 1653526 1655519 := bstep (se 1 (by rfl) ⟨1241639, by rfl⟩ : syracuseStep 1655519 = 2483279) B2483279
theorem B8946425 : Blo 1653526 8946425 := bstep (se 2 (by rfl) ⟨3354909, by rfl⟩ : syracuseStep 8946425 = 6709819) B6709819
theorem B2483099 : Blo 1653526 2483099 := bstep (se 1 (by rfl) ⟨1862324, by rfl⟩ : syracuseStep 2483099 = 3724649) B3724649
theorem B1860583 : Blo 1653526 1860583 := bstep (se 1 (by rfl) ⟨1395437, by rfl⟩ : syracuseStep 1860583 = 2790875) B2790875
theorem B4187123 : Blo 1653526 4187123 := bstep (se 1 (by rfl) ⟨3140342, by rfl⟩ : syracuseStep 4187123 = 6280685) B6280685
theorem B8610823 : Blo 1653526 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B7070777 : Blo 1653526 7070777 := bstep (se 2 (by rfl) ⟨2651541, by rfl⟩ : syracuseStep 7070777 = 5303083) B5303083
theorem B5301391 : Blo 1653526 5301391 := bstep (se 1 (by rfl) ⟨3976043, by rfl⟩ : syracuseStep 5301391 = 7952087) B7952087
theorem B4187335 : Blo 1653526 4187335 := bstep (se 1 (by rfl) ⟨3140501, by rfl⟩ : syracuseStep 4187335 = 6281003) B6281003
theorem B2516201 : Blo 1653526 2516201 := bstep (se 2 (by rfl) ⟨943575, by rfl⟩ : syracuseStep 2516201 = 1887151) B1887151
theorem B6284587 : Blo 1653526 6284587 := bstep (se 1 (by rfl) ⟨4713440, by rfl⟩ : syracuseStep 6284587 = 9426881) B9426881
theorem B3720545 : Blo 1653526 3720545 := bstep (se 2 (by rfl) ⟨1395204, by rfl⟩ : syracuseStep 3720545 = 2790409) B2790409
theorem B9422189 : Blo 1653526 9422189 := bstep (se 3 (by rfl) ⟨1766660, by rfl⟩ : syracuseStep 9422189 = 3533321) B3533321
theorem B3720635 : Blo 1653526 3720635 := bstep (se 1 (by rfl) ⟨2790476, by rfl⟩ : syracuseStep 3720635 = 5580953) B5580953
theorem B79619573 : Blo 1653526 79619573 := bstep (se 5 (by rfl) ⟨3732167, by rfl⟩ : syracuseStep 79619573 = 7464335) B7464335
theorem B7071239 : Blo 1653526 7071239 := bstep (se 1 (by rfl) ⟨5303429, by rfl⟩ : syracuseStep 7071239 = 10606859) B10606859
theorem B8054329 : Blo 1653526 8054329 := bstep (se 2 (by rfl) ⟨3020373, by rfl⟩ : syracuseStep 8054329 = 6040747) B6040747
theorem B3720761 : Blo 1653526 3720761 := bstep (se 2 (by rfl) ⟨1395285, by rfl⟩ : syracuseStep 3720761 = 2790571) B2790571
theorem B8374103 : Blo 1653526 8374103 := bstep (se 1 (by rfl) ⟨6280577, by rfl⟩ : syracuseStep 8374103 = 12561155) B12561155
theorem B15517585 : Blo 1653526 15517585 := bstep (se 2 (by rfl) ⟨5819094, by rfl⟩ : syracuseStep 15517585 = 11638189) B11638189
theorem B15100019 : Blo 1653526 15100019 := bstep (se 1 (by rfl) ⟨11325014, by rfl⟩ : syracuseStep 15100019 = 22650029) B22650029
theorem B30189725 : Blo 1653526 30189725 := bstep (se 3 (by rfl) ⟨5660573, by rfl⟩ : syracuseStep 30189725 = 11321147) B11321147
theorem B3721427 : Blo 1653526 3721427 := bstep (se 1 (by rfl) ⟨2791070, by rfl⟩ : syracuseStep 3721427 = 5582141) B5582141
theorem B4712701 : Blo 1653526 4712701 := bstep (se 3 (by rfl) ⟨883631, by rfl⟩ : syracuseStep 4712701 = 1767263) B1767263
theorem B3721481 : Blo 1653526 3721481 := bstep (se 2 (by rfl) ⟨1395555, by rfl⟩ : syracuseStep 3721481 = 2791111) B2791111
theorem B12560669 : Blo 1653526 12560669 := bstep (se 3 (by rfl) ⟨2355125, by rfl⟩ : syracuseStep 12560669 = 4710251) B4710251
theorem B17893669 : Blo 1653526 17893669 := bstep (se 4 (by rfl) ⟨1677531, by rfl⟩ : syracuseStep 17893669 = 3355063) B3355063
theorem B3533167 : Blo 1653526 3533167 := bstep (se 1 (by rfl) ⟨2649875, by rfl⟩ : syracuseStep 3533167 = 5299751) B5299751
theorem B9423215 : Blo 1653526 9423215 := bstep (se 1 (by rfl) ⟨7067411, by rfl⟩ : syracuseStep 9423215 = 14134823) B14134823
theorem B5581223 : Blo 1653526 5581223 := bstep (se 1 (by rfl) ⟨4185917, by rfl⟩ : syracuseStep 5581223 = 8371835) B8371835
theorem B3721697 : Blo 1653526 3721697 := bstep (se 2 (by rfl) ⟨1395636, by rfl⟩ : syracuseStep 3721697 = 2791273) B2791273
theorem B3353159 : Blo 1653526 3353159 := bstep (se 1 (by rfl) ⟨2514869, by rfl⟩ : syracuseStep 3353159 = 5029739) B5029739
theorem B4188743 : Blo 1653526 4188743 := bstep (se 1 (by rfl) ⟨3141557, by rfl⟩ : syracuseStep 4188743 = 6283115) B6283115
theorem B5581385 : Blo 1653526 5581385 := bstep (se 2 (by rfl) ⟨2093019, by rfl⟩ : syracuseStep 5581385 = 4186039) B4186039
theorem B1862239 : Blo 1653526 1862239 := bstep (se 1 (by rfl) ⟨1396679, by rfl⟩ : syracuseStep 1862239 = 2793359) B2793359
theorem B4188793 : Blo 1653526 4188793 := bstep (se 2 (by rfl) ⟨1570797, by rfl⟩ : syracuseStep 4188793 = 3141595) B3141595
theorem B13413053 : Blo 1653526 13413053 := bstep (se 3 (by rfl) ⟨2514947, by rfl⟩ : syracuseStep 13413053 = 5029895) B5029895
theorem B3722003 : Blo 1653526 3722003 := bstep (se 1 (by rfl) ⟨2791502, by rfl⟩ : syracuseStep 3722003 = 5583005) B5583005
theorem B58100573 : Blo 1653526 58100573 := bstep (se 3 (by rfl) ⟨10893857, by rfl⟩ : syracuseStep 58100573 = 21787715) B21787715
theorem B13421483 : Blo 1653526 13421483 := bstep (se 1 (by rfl) ⟨10066112, by rfl⟩ : syracuseStep 13421483 = 20132225) B20132225
theorem B17206337 : Blo 1653526 17206337 := bstep (se 2 (by rfl) ⟨6452376, by rfl⟩ : syracuseStep 17206337 = 12904753) B12904753
theorem B3722363 : Blo 1653526 3722363 := bstep (se 1 (by rfl) ⟨2791772, by rfl⟩ : syracuseStep 3722363 = 5583545) B5583545
theorem B3722489 : Blo 1653526 3722489 := bstep (se 2 (by rfl) ⟨1395933, by rfl⟩ : syracuseStep 3722489 = 2791867) B2791867
theorem B3976543 : Blo 1653526 3976543 := bstep (se 1 (by rfl) ⟨2982407, by rfl⟩ : syracuseStep 3976543 = 5964815) B5964815
theorem B82750835 : Blo 1653526 82750835 := bstep (se 1 (by rfl) ⟨62063126, by rfl⟩ : syracuseStep 82750835 = 124126253) B124126253
theorem B7753097 : Blo 1653526 7753097 := bstep (se 2 (by rfl) ⟨2907411, by rfl⟩ : syracuseStep 7753097 = 5814823) B5814823
theorem B3722633 : Blo 1653526 3722633 := bstep (se 2 (by rfl) ⟨1395987, by rfl⟩ : syracuseStep 3722633 = 2791975) B2791975
theorem B3534329 : Blo 1653526 3534329 := bstep (se 2 (by rfl) ⟨1325373, by rfl⟩ : syracuseStep 3534329 = 2650747) B2650747
theorem B4713977 : Blo 1653526 4713977 := bstep (se 2 (by rfl) ⟨1767741, by rfl⟩ : syracuseStep 4713977 = 3535483) B3535483
theorem B3722759 : Blo 1653526 3722759 := bstep (se 1 (by rfl) ⟨2792069, by rfl⟩ : syracuseStep 3722759 = 5584139) B5584139
theorem B3722939 : Blo 1653526 3722939 := bstep (se 1 (by rfl) ⟨2792204, by rfl⟩ : syracuseStep 3722939 = 5584409) B5584409
theorem B3723065 : Blo 1653526 3723065 := bstep (se 2 (by rfl) ⟨1396149, by rfl⟩ : syracuseStep 3723065 = 2792299) B2792299
theorem B8376371 : Blo 1653526 8376371 := bstep (se 1 (by rfl) ⟨6282278, by rfl⟩ : syracuseStep 8376371 = 12564557) B12564557
theorem B6279227 : Blo 1653526 6279227 := bstep (se 1 (by rfl) ⟨4709420, by rfl⟩ : syracuseStep 6279227 = 9418841) B9418841
theorem B7950395 : Blo 1653526 7950395 := bstep (se 1 (by rfl) ⟨5962796, by rfl⟩ : syracuseStep 7950395 = 11925593) B11925593
theorem B15085739 : Blo 1653526 15085739 := bstep (se 1 (by rfl) ⟨11314304, by rfl⟩ : syracuseStep 15085739 = 22628609) B22628609
theorem B5583059 : Blo 1653526 5583059 := bstep (se 1 (by rfl) ⟨4187294, by rfl⟩ : syracuseStep 5583059 = 8374589) B8374589
theorem B6279515 : Blo 1653526 6279515 := bstep (se 1 (by rfl) ⟨4709636, by rfl⟩ : syracuseStep 6279515 = 9419273) B9419273
theorem B4723051 : Blo 1653526 4723051 := bstep (se 1 (by rfl) ⟨3542288, by rfl⟩ : syracuseStep 4723051 = 7084577) B7084577
theorem B3723695 : Blo 1653526 3723695 := bstep (se 1 (by rfl) ⟨2792771, by rfl⟩ : syracuseStep 3723695 = 5585543) B5585543
theorem B3723731 : Blo 1653526 3723731 := bstep (se 1 (by rfl) ⟨2792798, by rfl⟩ : syracuseStep 3723731 = 5585597) B5585597
theorem B5583329 : Blo 1653526 5583329 := bstep (se 2 (by rfl) ⟨2093748, by rfl⟩ : syracuseStep 5583329 = 4187497) B4187497
theorem B2650619 : Blo 1653526 2650619 := bstep (se 1 (by rfl) ⟨1987964, by rfl⟩ : syracuseStep 2650619 = 3975929) B3975929
theorem B47682067 : Blo 1653526 47682067 := bstep (se 1 (by rfl) ⟨35761550, by rfl⟩ : syracuseStep 47682067 = 71523101) B71523101
theorem B3723839 : Blo 1653526 3723839 := bstep (se 1 (by rfl) ⟨2792879, by rfl⟩ : syracuseStep 3723839 = 5585759) B5585759
theorem B3723947 : Blo 1653526 3723947 := bstep (se 1 (by rfl) ⟨2792960, by rfl⟩ : syracuseStep 3723947 = 5585921) B5585921
theorem B5960375 : Blo 1653526 5960375 := bstep (se 1 (by rfl) ⟨4470281, by rfl⟩ : syracuseStep 5960375 = 8940563) B8940563
theorem B2355895 : Blo 1653526 2355895 := bstep (se 1 (by rfl) ⟨1766921, by rfl⟩ : syracuseStep 2355895 = 3533843) B3533843
theorem B2356123 : Blo 1653526 2356123 := bstep (se 1 (by rfl) ⟨1767092, by rfl⟩ : syracuseStep 2356123 = 3534185) B3534185
theorem B3724487 : Blo 1653526 3724487 := bstep (se 1 (by rfl) ⟨2793365, by rfl⟩ : syracuseStep 3724487 = 5586731) B5586731
theorem B6280487 : Blo 1653526 6280487 := bstep (se 1 (by rfl) ⟨4710365, by rfl⟩ : syracuseStep 6280487 = 9420731) B9420731
theorem B2094427 : Blo 1653526 2094427 := bstep (se 1 (by rfl) ⟨1570820, by rfl⟩ : syracuseStep 2094427 = 3141641) B3141641
theorem B7165307 : Blo 1653526 7165307 := bstep (se 1 (by rfl) ⟨5373980, by rfl⟩ : syracuseStep 7165307 = 10747961) B10747961
theorem B3724667 : Blo 1653526 3724667 := bstep (se 1 (by rfl) ⟨2793500, by rfl⟩ : syracuseStep 3724667 = 5587001) B5587001
theorem B10483181 : Blo 1653526 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B3724793 : Blo 1653526 3724793 := bstep (se 2 (by rfl) ⟨1396797, by rfl⟩ : syracuseStep 3724793 = 2793595) B2793595
theorem B2094655 : Blo 1653526 2094655 := bstep (se 1 (by rfl) ⟨1570991, by rfl⟩ : syracuseStep 2094655 = 3141983) B3141983
theorem B3724883 : Blo 1653526 3724883 := bstep (se 1 (by rfl) ⟨2793662, by rfl⟩ : syracuseStep 3724883 = 5587325) B5587325
theorem B8377991 : Blo 1653526 8377991 := bstep (se 1 (by rfl) ⟨6283493, by rfl⟩ : syracuseStep 8377991 = 12566987) B12566987
theorem B5584571 : Blo 1653526 5584571 := bstep (se 1 (by rfl) ⟨4188428, by rfl⟩ : syracuseStep 5584571 = 8376857) B8376857
theorem B38205371 : Blo 1653526 38205371 := bstep (se 1 (by rfl) ⟨28654028, by rfl⟩ : syracuseStep 38205371 = 57308057) B57308057
theorem B28260413 : Blo 1653526 28260413 := bstep (se 3 (by rfl) ⟨5298827, by rfl⟩ : syracuseStep 28260413 = 10597655) B10597655
theorem B21207203 : Blo 1653526 21207203 := bstep (se 1 (by rfl) ⟨15905402, by rfl⟩ : syracuseStep 21207203 = 31810805) B31810805
theorem B2480393 : Blo 1653526 2480393 := bstep (se 2 (by rfl) ⟨930147, by rfl⟩ : syracuseStep 2480393 = 1860295) B1860295
theorem B10598681 : Blo 1653526 10598681 := bstep (se 2 (by rfl) ⟨3974505, by rfl⟩ : syracuseStep 10598681 = 7949011) B7949011
theorem B2480495 : Blo 1653526 2480495 := bstep (se 1 (by rfl) ⟨1860371, by rfl⟩ : syracuseStep 2480495 = 3720743) B3720743
theorem B2791847 : Blo 1653526 2791847 := bstep (se 1 (by rfl) ⟨2093885, by rfl⟩ : syracuseStep 2791847 = 4187771) B4187771
theorem B2480711 : Blo 1653526 2480711 := bstep (se 1 (by rfl) ⟨1860533, by rfl⟩ : syracuseStep 2480711 = 3721067) B3721067
theorem B2792009 : Blo 1653526 2792009 := bstep (se 2 (by rfl) ⟨1047003, by rfl⟩ : syracuseStep 2792009 = 2094007) B2094007
theorem B2480747 : Blo 1653526 2480747 := bstep (se 1 (by rfl) ⟨1860560, by rfl⟩ : syracuseStep 2480747 = 3721121) B3721121
theorem B4029035 : Blo 1653526 4029035 := bstep (se 1 (by rfl) ⟨3021776, by rfl⟩ : syracuseStep 4029035 = 6043553) B6043553
theorem B2235055 : Blo 1653526 2235055 := bstep (se 1 (by rfl) ⟨1676291, by rfl⟩ : syracuseStep 2235055 = 3352583) B3352583
theorem B6281975 : Blo 1653526 6281975 := bstep (se 1 (by rfl) ⟨4711481, by rfl⟩ : syracuseStep 6281975 = 9422963) B9422963
theorem B1653551 : Blo 1653526 1653551 := bstep (se 1 (by rfl) ⟨1240163, by rfl⟩ : syracuseStep 1653551 = 2480327) B2480327
theorem B2480975 : Blo 1653526 2480975 := bstep (se 1 (by rfl) ⟨1860731, by rfl⟩ : syracuseStep 2480975 = 3721463) B3721463
theorem B1653659 : Blo 1653526 1653659 := bstep (se 1 (by rfl) ⟨1240244, by rfl⟩ : syracuseStep 1653659 = 2480489) B2480489
theorem B1653711 : Blo 1653526 1653711 := bstep (se 1 (by rfl) ⟨1240283, by rfl⟩ : syracuseStep 1653711 = 2480567) B2480567
theorem B1653735 : Blo 1653526 1653735 := bstep (se 1 (by rfl) ⟨1240301, by rfl⟩ : syracuseStep 1653735 = 2480603) B2480603
theorem B8371187 : Blo 1653526 8371187 := bstep (se 1 (by rfl) ⟨6278390, by rfl⟩ : syracuseStep 8371187 = 12556781) B12556781
theorem B2481371 : Blo 1653526 2481371 := bstep (se 1 (by rfl) ⟨1861028, by rfl⟩ : syracuseStep 2481371 = 3722057) B3722057
theorem B71556317 : Blo 1653526 71556317 := bstep (se 3 (by rfl) ⟨13416809, by rfl⟩ : syracuseStep 71556317 = 26833619) B26833619
theorem B8379611 : Blo 1653526 8379611 := bstep (se 1 (by rfl) ⟨6284708, by rfl⟩ : syracuseStep 8379611 = 12569417) B12569417
theorem B1654047 : Blo 1653526 1654047 := bstep (se 1 (by rfl) ⟨1240535, by rfl⟩ : syracuseStep 1654047 = 2481071) B2481071
theorem B1654107 : Blo 1653526 1654107 := bstep (se 1 (by rfl) ⟨1240580, by rfl⟩ : syracuseStep 1654107 = 2481161) B2481161
theorem B1654127 : Blo 1653526 1654127 := bstep (se 1 (by rfl) ⟨1240595, by rfl⟩ : syracuseStep 1654127 = 2481191) B2481191
theorem B7544183 : Blo 1653526 7544183 := bstep (se 1 (by rfl) ⟨5658137, by rfl⟩ : syracuseStep 7544183 = 11316275) B11316275
theorem B2481545 : Blo 1653526 2481545 := bstep (se 2 (by rfl) ⟨930579, by rfl⟩ : syracuseStep 2481545 = 1861159) B1861159
theorem B1654183 : Blo 1653526 1654183 := bstep (se 1 (by rfl) ⟨1240637, by rfl⟩ : syracuseStep 1654183 = 2481275) B2481275
theorem B4709819 : Blo 1653526 4709819 := bstep (se 1 (by rfl) ⟨3532364, by rfl⟩ : syracuseStep 4709819 = 7064729) B7064729
theorem B1654267 : Blo 1653526 1654267 := bstep (se 1 (by rfl) ⟨1240700, by rfl⟩ : syracuseStep 1654267 = 2481401) B2481401
theorem B1654335 : Blo 1653526 1654335 := bstep (se 1 (by rfl) ⟨1240751, by rfl⟩ : syracuseStep 1654335 = 2481503) B2481503
theorem B1654343 : Blo 1653526 1654343 := bstep (se 1 (by rfl) ⟨1240757, by rfl⟩ : syracuseStep 1654343 = 2481515) B2481515
theorem B5586515 : Blo 1653526 5586515 := bstep (se 1 (by rfl) ⟨4189886, by rfl⟩ : syracuseStep 5586515 = 8379773) B8379773
theorem B4185695 : Blo 1653526 4185695 := bstep (se 1 (by rfl) ⟨3139271, by rfl⟩ : syracuseStep 4185695 = 6278543) B6278543
theorem B2793055 : Blo 1653526 2793055 := bstep (se 1 (by rfl) ⟨2094791, by rfl⟩ : syracuseStep 2793055 = 4189583) B4189583
theorem B6364781 : Blo 1653526 6364781 := bstep (se 3 (by rfl) ⟨1193396, by rfl⟩ : syracuseStep 6364781 = 2386793) B2386793
theorem B7945937 : Blo 1653526 7945937 := bstep (se 2 (by rfl) ⟨2979726, by rfl⟩ : syracuseStep 7945937 = 5959453) B5959453
theorem B1654495 : Blo 1653526 1654495 := bstep (se 1 (by rfl) ⟨1240871, by rfl⟩ : syracuseStep 1654495 = 2481743) B2481743
theorem B2481899 : Blo 1653526 2481899 := bstep (se 1 (by rfl) ⟨1861424, by rfl⟩ : syracuseStep 2481899 = 3722849) B3722849
theorem B4472617 : Blo 1653526 4472617 := bstep (se 2 (by rfl) ⟨1677231, by rfl⟩ : syracuseStep 4472617 = 3354463) B3354463
theorem B1654575 : Blo 1653526 1654575 := bstep (se 1 (by rfl) ⟨1240931, by rfl⟩ : syracuseStep 1654575 = 2481863) B2481863
theorem B2793271 : Blo 1653526 2793271 := bstep (se 1 (by rfl) ⟨2094953, by rfl⟩ : syracuseStep 2793271 = 4189907) B4189907
theorem B14139197 : Blo 1653526 14139197 := bstep (se 3 (by rfl) ⟨2651099, by rfl⟩ : syracuseStep 14139197 = 5302199) B5302199
theorem B10600321 : Blo 1653526 10600321 := bstep (se 2 (by rfl) ⟨3975120, by rfl⟩ : syracuseStep 10600321 = 7950241) B7950241
theorem B13418369 : Blo 1653526 13418369 := bstep (se 2 (by rfl) ⟨5031888, by rfl⟩ : syracuseStep 13418369 = 10063777) B10063777
theorem B1654683 : Blo 1653526 1654683 := bstep (se 1 (by rfl) ⟨1241012, by rfl⟩ : syracuseStep 1654683 = 2482025) B2482025
theorem B1654735 : Blo 1653526 1654735 := bstep (se 1 (by rfl) ⟨1241051, by rfl⟩ : syracuseStep 1654735 = 2482103) B2482103
theorem B2482127 : Blo 1653526 2482127 := bstep (se 1 (by rfl) ⟨1861595, by rfl⟩ : syracuseStep 2482127 = 3723191) B3723191
theorem B1654759 : Blo 1653526 1654759 := bstep (se 1 (by rfl) ⟨1241069, by rfl⟩ : syracuseStep 1654759 = 2482139) B2482139
theorem B4186151 : Blo 1653526 4186151 := bstep (se 1 (by rfl) ⟨3139613, by rfl⟩ : syracuseStep 4186151 = 6279227) B6279227
theorem B5300263 : Blo 1653526 5300263 := bstep (se 1 (by rfl) ⟨3975197, by rfl⟩ : syracuseStep 5300263 = 7950395) B7950395
theorem B5587163 : Blo 1653526 5587163 := bstep (se 1 (by rfl) ⟨4190372, by rfl⟩ : syracuseStep 5587163 = 8380745) B8380745
theorem B4186343 : Blo 1653526 4186343 := bstep (se 1 (by rfl) ⟨3139757, by rfl⟩ : syracuseStep 4186343 = 6279515) B6279515
theorem B1655015 : Blo 1653526 1655015 := bstep (se 1 (by rfl) ⟨1241261, by rfl⟩ : syracuseStep 1655015 = 2482523) B2482523
theorem B2482463 : Blo 1653526 2482463 := bstep (se 1 (by rfl) ⟨1861847, by rfl⟩ : syracuseStep 2482463 = 3723695) B3723695
theorem B2482487 : Blo 1653526 2482487 := bstep (se 1 (by rfl) ⟨1861865, by rfl⟩ : syracuseStep 2482487 = 3723731) B3723731
theorem B6283601 : Blo 1653526 6283601 := bstep (se 2 (by rfl) ⟨2356350, by rfl⟩ : syracuseStep 6283601 = 4712701) B4712701
theorem B2482559 : Blo 1653526 2482559 := bstep (se 1 (by rfl) ⟨1861919, by rfl⟩ : syracuseStep 2482559 = 3723839) B3723839
theorem B1655167 : Blo 1653526 1655167 := bstep (se 1 (by rfl) ⟨1241375, by rfl⟩ : syracuseStep 1655167 = 2482751) B2482751
theorem B9421231 : Blo 1653526 9421231 := bstep (se 1 (by rfl) ⟨7065923, by rfl⟩ : syracuseStep 9421231 = 14131847) B14131847
theorem B2482631 : Blo 1653526 2482631 := bstep (se 1 (by rfl) ⟨1861973, by rfl⟩ : syracuseStep 2482631 = 3723947) B3723947
theorem B3973583 : Blo 1653526 3973583 := bstep (se 1 (by rfl) ⟨2980187, by rfl⟩ : syracuseStep 3973583 = 5960375) B5960375
theorem B1655247 : Blo 1653526 1655247 := bstep (se 1 (by rfl) ⟨1241435, by rfl⟩ : syracuseStep 1655247 = 2482871) B2482871
theorem B4710889 : Blo 1653526 4710889 := bstep (se 2 (by rfl) ⟨1766583, by rfl⟩ : syracuseStep 4710889 = 3533167) B3533167
theorem B5964283 : Blo 1653526 5964283 := bstep (se 1 (by rfl) ⟨4473212, by rfl⟩ : syracuseStep 5964283 = 8946425) B8946425
theorem B1655399 : Blo 1653526 1655399 := bstep (se 1 (by rfl) ⟨1241549, by rfl⟩ : syracuseStep 1655399 = 2483099) B2483099
theorem B2482985 : Blo 1653526 2482985 := bstep (se 2 (by rfl) ⟨931119, by rfl⟩ : syracuseStep 2482985 = 1862239) B1862239
theorem B2482991 : Blo 1653526 2482991 := bstep (se 1 (by rfl) ⟨1862243, by rfl⟩ : syracuseStep 2482991 = 3724487) B3724487
theorem B4186991 : Blo 1653526 4186991 := bstep (se 1 (by rfl) ⟨3140243, by rfl⟩ : syracuseStep 4186991 = 6280487) B6280487
theorem B2483111 : Blo 1653526 2483111 := bstep (se 1 (by rfl) ⟨1862333, by rfl⟩ : syracuseStep 2483111 = 3724667) B3724667
theorem B220668893 : Blo 1653526 220668893 := bstep (se 3 (by rfl) ⟨41375417, by rfl⟩ : syracuseStep 220668893 = 82750835) B82750835
theorem B6988787 : Blo 1653526 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B2483195 : Blo 1653526 2483195 := bstep (se 1 (by rfl) ⟨1862396, by rfl⟩ : syracuseStep 2483195 = 3724793) B3724793
theorem B2483255 : Blo 1653526 2483255 := bstep (se 1 (by rfl) ⟨1862441, by rfl⟩ : syracuseStep 2483255 = 3724883) B3724883
theorem B25470247 : Blo 1653526 25470247 := bstep (se 1 (by rfl) ⟨19102685, by rfl⟩ : syracuseStep 25470247 = 38205371) B38205371
theorem B8373779 : Blo 1653526 8373779 := bstep (se 1 (by rfl) ⟨6280334, by rfl⟩ : syracuseStep 8373779 = 12560669) B12560669
theorem B3720815 : Blo 1653526 3720815 := bstep (se 1 (by rfl) ⟨2790611, by rfl⟩ : syracuseStep 3720815 = 5581223) B5581223
theorem B1861231 : Blo 1653526 1861231 := bstep (se 1 (by rfl) ⟨1395923, by rfl⟩ : syracuseStep 1861231 = 2791847) B2791847
theorem B3720923 : Blo 1653526 3720923 := bstep (se 1 (by rfl) ⟨2790692, by rfl⟩ : syracuseStep 3720923 = 5581385) B5581385
theorem B1861339 : Blo 1653526 1861339 := bstep (se 1 (by rfl) ⟨1396004, by rfl⟩ : syracuseStep 1861339 = 2792009) B2792009
theorem B4187983 : Blo 1653526 4187983 := bstep (se 1 (by rfl) ⟨3140987, by rfl⟩ : syracuseStep 4187983 = 6281975) B6281975
theorem B38733715 : Blo 1653526 38733715 := bstep (se 1 (by rfl) ⟨29050286, by rfl⟩ : syracuseStep 38733715 = 58100573) B58100573
theorem B8947655 : Blo 1653526 8947655 := bstep (se 1 (by rfl) ⟨6710741, by rfl⟩ : syracuseStep 8947655 = 13421483) B13421483
theorem B5580791 : Blo 1653526 5580791 := bstep (se 1 (by rfl) ⟨4185593, by rfl⟩ : syracuseStep 5580791 = 8371187) B8371187
theorem B11470891 : Blo 1653526 11470891 := bstep (se 1 (by rfl) ⟨8603168, by rfl⟩ : syracuseStep 11470891 = 17206337) B17206337
theorem B47704211 : Blo 1653526 47704211 := bstep (se 1 (by rfl) ⟨35778158, by rfl⟩ : syracuseStep 47704211 = 71556317) B71556317
theorem B3139879 : Blo 1653526 3139879 := bstep (se 1 (by rfl) ⟨2354909, by rfl⟩ : syracuseStep 3139879 = 4709819) B4709819
theorem B14133761 : Blo 1653526 14133761 := bstep (se 2 (by rfl) ⟨5300160, by rfl⟩ : syracuseStep 14133761 = 10600321) B10600321
theorem B2828987 : Blo 1653526 2828987 := bstep (se 1 (by rfl) ⟨2121740, by rfl⟩ : syracuseStep 2828987 = 4243481) B4243481
theorem B3722039 : Blo 1653526 3722039 := bstep (se 1 (by rfl) ⟨2791529, by rfl⟩ : syracuseStep 3722039 = 5583059) B5583059
theorem B5581655 : Blo 1653526 5581655 := bstep (se 1 (by rfl) ⟨4186241, by rfl⟩ : syracuseStep 5581655 = 8372483) B8372483
theorem B3722219 : Blo 1653526 3722219 := bstep (se 1 (by rfl) ⟨2791664, by rfl⟩ : syracuseStep 3722219 = 5583329) B5583329
theorem B5581871 : Blo 1653526 5581871 := bstep (se 1 (by rfl) ⟨4186403, by rfl⟩ : syracuseStep 5581871 = 8372807) B8372807
theorem B23858225 : Blo 1653526 23858225 := bstep (se 2 (by rfl) ⟨8946834, by rfl⟩ : syracuseStep 23858225 = 17893669) B17893669
theorem B135834691 : Blo 1653526 135834691 := bstep (se 1 (by rfl) ⟨101876018, by rfl⟩ : syracuseStep 135834691 = 203752037) B203752037
theorem B4713851 : Blo 1653526 4713851 := bstep (se 1 (by rfl) ⟨3535388, by rfl⟩ : syracuseStep 4713851 = 7070777) B7070777
theorem B5582249 : Blo 1653526 5582249 := bstep (se 2 (by rfl) ⟨2093343, by rfl⟩ : syracuseStep 5582249 = 4186687) B4186687
theorem B3141193 : Blo 1653526 3141193 := bstep (se 2 (by rfl) ⟨1177947, by rfl⟩ : syracuseStep 3141193 = 2355895) B2355895
theorem B19107485 : Blo 1653526 19107485 := bstep (se 3 (by rfl) ⟨3582653, by rfl⟩ : syracuseStep 19107485 = 7165307) B7165307
theorem B53079715 : Blo 1653526 53079715 := bstep (se 1 (by rfl) ⟨39809786, by rfl⟩ : syracuseStep 53079715 = 79619573) B79619573
theorem B4714159 : Blo 1653526 4714159 := bstep (se 1 (by rfl) ⟨3535619, by rfl⟩ : syracuseStep 4714159 = 7071239) B7071239
theorem B3723047 : Blo 1653526 3723047 := bstep (se 1 (by rfl) ⟨2792285, by rfl⟩ : syracuseStep 3723047 = 5584571) B5584571
theorem B3141497 : Blo 1653526 3141497 := bstep (se 2 (by rfl) ⟨1178061, by rfl⟩ : syracuseStep 3141497 = 2356123) B2356123
theorem B5582735 : Blo 1653526 5582735 := bstep (se 1 (by rfl) ⟨4187051, by rfl⟩ : syracuseStep 5582735 = 8374103) B8374103
theorem B11481097 : Blo 1653526 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B7065787 : Blo 1653526 7065787 := bstep (se 1 (by rfl) ⟨5299340, by rfl⟩ : syracuseStep 7065787 = 10598681) B10598681
theorem B5583113 : Blo 1653526 5583113 := bstep (se 2 (by rfl) ⟨2093667, by rfl⟩ : syracuseStep 5583113 = 4187335) B4187335
theorem B10744093 : Blo 1653526 10744093 := bstep (se 3 (by rfl) ⟨2014517, by rfl⟩ : syracuseStep 10744093 = 4029035) B4029035
theorem B8942035 : Blo 1653526 8942035 := bstep (se 1 (by rfl) ⟨6706526, by rfl⟩ : syracuseStep 8942035 = 13413053) B13413053
theorem B82760453 : Blo 1653526 82760453 := bstep (se 4 (by rfl) ⟨7758792, by rfl⟩ : syracuseStep 82760453 = 15517585) B15517585
theorem B3724073 : Blo 1653526 3724073 := bstep (se 2 (by rfl) ⟨1396527, by rfl⟩ : syracuseStep 3724073 = 2793055) B2793055
theorem B2356219 : Blo 1653526 2356219 := bstep (se 1 (by rfl) ⟨1767164, by rfl⟩ : syracuseStep 2356219 = 3534329) B3534329
theorem B3142651 : Blo 1653526 3142651 := bstep (se 1 (by rfl) ⟨2356988, by rfl⟩ : syracuseStep 3142651 = 4713977) B4713977
theorem B3724343 : Blo 1653526 3724343 := bstep (se 1 (by rfl) ⟨2793257, by rfl⟩ : syracuseStep 3724343 = 5586515) B5586515
theorem B2790463 : Blo 1653526 2790463 := bstep (se 1 (by rfl) ⟨2092847, by rfl⟩ : syracuseStep 2790463 = 4185695) B4185695
theorem B3724361 : Blo 1653526 3724361 := bstep (se 2 (by rfl) ⟨1396635, by rfl⟩ : syracuseStep 3724361 = 2793271) B2793271
theorem B5297291 : Blo 1653526 5297291 := bstep (se 1 (by rfl) ⟨3972968, by rfl⟩ : syracuseStep 5297291 = 7945937) B7945937
theorem B9426131 : Blo 1653526 9426131 := bstep (se 1 (by rfl) ⟨7069598, by rfl⟩ : syracuseStep 9426131 = 14139197) B14139197
theorem B5584247 : Blo 1653526 5584247 := bstep (se 1 (by rfl) ⟨4188185, by rfl⟩ : syracuseStep 5584247 = 8376371) B8376371
theorem B10057159 : Blo 1653526 10057159 := bstep (se 1 (by rfl) ⟨7542869, by rfl⟩ : syracuseStep 10057159 = 15085739) B15085739
theorem B2790983 : Blo 1653526 2790983 := bstep (se 1 (by rfl) ⟨2093237, by rfl⟩ : syracuseStep 2790983 = 4186475) B4186475
theorem B1767079 : Blo 1653526 1767079 := bstep (se 1 (by rfl) ⟨1325309, by rfl⟩ : syracuseStep 1767079 = 2650619) B2650619
theorem B2791199 : Blo 1653526 2791199 := bstep (se 1 (by rfl) ⟨2093399, by rfl⟩ : syracuseStep 2791199 = 4186799) B4186799
theorem B6297401 : Blo 1653526 6297401 := bstep (se 2 (by rfl) ⟨2361525, by rfl⟩ : syracuseStep 6297401 = 4723051) B4723051
theorem B2791415 : Blo 1653526 2791415 := bstep (se 1 (by rfl) ⟨2093561, by rfl⟩ : syracuseStep 2791415 = 4187123) B4187123
theorem B63576089 : Blo 1653526 63576089 := bstep (se 2 (by rfl) ⟨23841033, by rfl⟩ : syracuseStep 63576089 = 47682067) B47682067
theorem B1677467 : Blo 1653526 1677467 := bstep (se 1 (by rfl) ⟨1258100, by rfl⟩ : syracuseStep 1677467 = 2516201) B2516201
theorem B5585057 : Blo 1653526 5585057 := bstep (se 2 (by rfl) ⟨2094396, by rfl⟩ : syracuseStep 5585057 = 4188793) B4188793
theorem B2980073 : Blo 1653526 2980073 := bstep (se 2 (by rfl) ⟨1117527, by rfl⟩ : syracuseStep 2980073 = 2235055) B2235055
theorem B2480363 : Blo 1653526 2480363 := bstep (se 1 (by rfl) ⟨1860272, by rfl⟩ : syracuseStep 2480363 = 3720545) B3720545
theorem B6281459 : Blo 1653526 6281459 := bstep (se 1 (by rfl) ⟨4711094, by rfl⟩ : syracuseStep 6281459 = 9422189) B9422189
theorem B2480423 : Blo 1653526 2480423 := bstep (se 1 (by rfl) ⟨1860317, by rfl⟩ : syracuseStep 2480423 = 3720635) B3720635
theorem B20117821 : Blo 1653526 20117821 := bstep (se 3 (by rfl) ⟨3772091, by rfl⟩ : syracuseStep 20117821 = 7544183) B7544183
theorem B2480507 : Blo 1653526 2480507 := bstep (se 1 (by rfl) ⟨1860380, by rfl⟩ : syracuseStep 2480507 = 3720761) B3720761
theorem B5585327 : Blo 1653526 5585327 := bstep (se 1 (by rfl) ⟨4188995, by rfl⟩ : syracuseStep 5585327 = 8377991) B8377991
theorem B2480777 : Blo 1653526 2480777 := bstep (se 2 (by rfl) ⟨930291, by rfl⟩ : syracuseStep 2480777 = 1860583) B1860583
theorem B18840275 : Blo 1653526 18840275 := bstep (se 1 (by rfl) ⟨14130206, by rfl⟩ : syracuseStep 18840275 = 28260413) B28260413
theorem B10066679 : Blo 1653526 10066679 := bstep (se 1 (by rfl) ⟨7550009, by rfl⟩ : syracuseStep 10066679 = 15100019) B15100019
theorem B20126483 : Blo 1653526 20126483 := bstep (se 1 (by rfl) ⟨15094862, by rfl⟩ : syracuseStep 20126483 = 30189725) B30189725
theorem B14138135 : Blo 1653526 14138135 := bstep (se 1 (by rfl) ⟨10603601, by rfl⟩ : syracuseStep 14138135 = 21207203) B21207203
theorem B2480951 : Blo 1653526 2480951 := bstep (se 1 (by rfl) ⟨1860713, by rfl⟩ : syracuseStep 2480951 = 3721427) B3721427
theorem B1653595 : Blo 1653526 1653595 := bstep (se 1 (by rfl) ⟨1240196, by rfl⟩ : syracuseStep 1653595 = 2480393) B2480393
theorem B2480987 : Blo 1653526 2480987 := bstep (se 1 (by rfl) ⟨1860740, by rfl⟩ : syracuseStep 2480987 = 3721481) B3721481
theorem B7068521 : Blo 1653526 7068521 := bstep (se 2 (by rfl) ⟨2650695, by rfl⟩ : syracuseStep 7068521 = 5301391) B5301391
theorem B1653663 : Blo 1653526 1653663 := bstep (se 1 (by rfl) ⟨1240247, by rfl⟩ : syracuseStep 1653663 = 2480495) B2480495
theorem B6282143 : Blo 1653526 6282143 := bstep (se 1 (by rfl) ⟨4711607, by rfl⟩ : syracuseStep 6282143 = 9423215) B9423215
theorem B2481131 : Blo 1653526 2481131 := bstep (se 1 (by rfl) ⟨1860848, by rfl⟩ : syracuseStep 2481131 = 3721697) B3721697
theorem B1653807 : Blo 1653526 1653807 := bstep (se 1 (by rfl) ⟨1240355, by rfl⟩ : syracuseStep 1653807 = 2480711) B2480711
theorem B2235439 : Blo 1653526 2235439 := bstep (se 1 (by rfl) ⟨1676579, by rfl⟩ : syracuseStep 2235439 = 3353159) B3353159
theorem B2792495 : Blo 1653526 2792495 := bstep (se 1 (by rfl) ⟨2094371, by rfl⟩ : syracuseStep 2792495 = 4188743) B4188743
theorem B8379449 : Blo 1653526 8379449 := bstep (se 2 (by rfl) ⟨3142293, by rfl⟩ : syracuseStep 8379449 = 6284587) B6284587
theorem B1653831 : Blo 1653526 1653831 := bstep (se 1 (by rfl) ⟨1240373, by rfl⟩ : syracuseStep 1653831 = 2480747) B2480747
theorem B2792569 : Blo 1653526 2792569 := bstep (se 2 (by rfl) ⟨1047213, by rfl⟩ : syracuseStep 2792569 = 2094427) B2094427
theorem B21208229 : Blo 1653526 21208229 := bstep (se 4 (by rfl) ⟨1988271, by rfl⟩ : syracuseStep 21208229 = 3976543) B3976543
theorem B2481335 : Blo 1653526 2481335 := bstep (se 1 (by rfl) ⟨1861001, by rfl⟩ : syracuseStep 2481335 = 3722003) B3722003
theorem B1653983 : Blo 1653526 1653983 := bstep (se 1 (by rfl) ⟨1240487, by rfl⟩ : syracuseStep 1653983 = 2480975) B2480975
theorem B10739105 : Blo 1653526 10739105 := bstep (se 2 (by rfl) ⟨4027164, by rfl⟩ : syracuseStep 10739105 = 8054329) B8054329
theorem B2481575 : Blo 1653526 2481575 := bstep (se 1 (by rfl) ⟨1861181, by rfl⟩ : syracuseStep 2481575 = 3722363) B3722363
theorem B2792873 : Blo 1653526 2792873 := bstep (se 2 (by rfl) ⟨1047327, by rfl⟩ : syracuseStep 2792873 = 2094655) B2094655
theorem B1654247 : Blo 1653526 1654247 := bstep (se 1 (by rfl) ⟨1240685, by rfl⟩ : syracuseStep 1654247 = 2481371) B2481371
theorem B5586407 : Blo 1653526 5586407 := bstep (se 1 (by rfl) ⟨4189805, by rfl⟩ : syracuseStep 5586407 = 8379611) B8379611
theorem B2481659 : Blo 1653526 2481659 := bstep (se 1 (by rfl) ⟨1861244, by rfl⟩ : syracuseStep 2481659 = 3722489) B3722489
theorem B5168731 : Blo 1653526 5168731 := bstep (se 1 (by rfl) ⟨3876548, by rfl⟩ : syracuseStep 5168731 = 7753097) B7753097
theorem B1654363 : Blo 1653526 1654363 := bstep (se 1 (by rfl) ⟨1240772, by rfl⟩ : syracuseStep 1654363 = 2481545) B2481545
theorem B2481755 : Blo 1653526 2481755 := bstep (se 1 (by rfl) ⟨1861316, by rfl⟩ : syracuseStep 2481755 = 3722633) B3722633
theorem B2481839 : Blo 1653526 2481839 := bstep (se 1 (by rfl) ⟨1861379, by rfl⟩ : syracuseStep 2481839 = 3722759) B3722759
theorem B5963489 : Blo 1653526 5963489 := bstep (se 2 (by rfl) ⟨2236308, by rfl⟩ : syracuseStep 5963489 = 4472617) B4472617
theorem B4243187 : Blo 1653526 4243187 := bstep (se 1 (by rfl) ⟨3182390, by rfl⟩ : syracuseStep 4243187 = 6364781) B6364781
theorem B2481959 : Blo 1653526 2481959 := bstep (se 1 (by rfl) ⟨1861469, by rfl⟩ : syracuseStep 2481959 = 3722939) B3722939
theorem B1654599 : Blo 1653526 1654599 := bstep (se 1 (by rfl) ⟨1240949, by rfl⟩ : syracuseStep 1654599 = 2481899) B2481899
theorem B2482043 : Blo 1653526 2482043 := bstep (se 1 (by rfl) ⟨1861532, by rfl⟩ : syracuseStep 2482043 = 3723065) B3723065
theorem B8945579 : Blo 1653526 8945579 := bstep (se 1 (by rfl) ⟨6709184, by rfl⟩ : syracuseStep 8945579 = 13418369) B13418369
theorem B1654751 : Blo 1653526 1654751 := bstep (se 1 (by rfl) ⟨1241063, by rfl⟩ : syracuseStep 1654751 = 2482127) B2482127
theorem B15294521 : Blo 1653526 15294521 := bstep (se 2 (by rfl) ⟨5735445, by rfl⟩ : syracuseStep 15294521 = 11470891) B11470891
theorem B1654975 : Blo 1653526 1654975 := bstep (se 1 (by rfl) ⟨1241231, by rfl⟩ : syracuseStep 1654975 = 2482463) B2482463
theorem B1654991 : Blo 1653526 1654991 := bstep (se 1 (by rfl) ⟨1241243, by rfl⟩ : syracuseStep 1654991 = 2482487) B2482487
theorem B9421049 : Blo 1653526 9421049 := bstep (se 2 (by rfl) ⟨3532893, by rfl⟩ : syracuseStep 9421049 = 7065787) B7065787
theorem B1655039 : Blo 1653526 1655039 := bstep (se 1 (by rfl) ⟨1241279, by rfl⟩ : syracuseStep 1655039 = 2482559) B2482559
theorem B1655087 : Blo 1653526 1655087 := bstep (se 1 (by rfl) ⟨1241315, by rfl⟩ : syracuseStep 1655087 = 2482631) B2482631
theorem B4186505 : Blo 1653526 4186505 := bstep (se 2 (by rfl) ⟨1569939, by rfl⟩ : syracuseStep 4186505 = 3139879) B3139879
theorem B4473245 : Blo 1653526 4473245 := bstep (se 3 (by rfl) ⟨838733, by rfl⟩ : syracuseStep 4473245 = 1677467) B1677467
theorem B55173635 : Blo 1653526 55173635 := bstep (se 1 (by rfl) ⟨41380226, by rfl⟩ : syracuseStep 55173635 = 82760453) B82760453
theorem B2482715 : Blo 1653526 2482715 := bstep (se 1 (by rfl) ⟨1862036, by rfl⟩ : syracuseStep 2482715 = 3724073) B3724073
theorem B1655323 : Blo 1653526 1655323 := bstep (se 1 (by rfl) ⟨1241492, by rfl⟩ : syracuseStep 1655323 = 2482985) B2482985
theorem B1655327 : Blo 1653526 1655327 := bstep (se 1 (by rfl) ⟨1241495, by rfl⟩ : syracuseStep 1655327 = 2482991) B2482991
theorem B1655407 : Blo 1653526 1655407 := bstep (se 1 (by rfl) ⟨1241555, by rfl⟩ : syracuseStep 1655407 = 2483111) B2483111
theorem B147112595 : Blo 1653526 147112595 := bstep (se 1 (by rfl) ⟨110334446, by rfl⟩ : syracuseStep 147112595 = 220668893) B220668893
theorem B1655463 : Blo 1653526 1655463 := bstep (se 1 (by rfl) ⟨1241597, by rfl⟩ : syracuseStep 1655463 = 2483195) B2483195
theorem B2482895 : Blo 1653526 2482895 := bstep (se 1 (by rfl) ⟨1862171, by rfl⟩ : syracuseStep 2482895 = 3724343) B3724343
theorem B1655503 : Blo 1653526 1655503 := bstep (se 1 (by rfl) ⟨1241627, by rfl⟩ : syracuseStep 1655503 = 2483255) B2483255
theorem B2482907 : Blo 1653526 2482907 := bstep (se 1 (by rfl) ⟨1862180, by rfl⟩ : syracuseStep 2482907 = 3724361) B3724361
theorem B3531527 : Blo 1653526 3531527 := bstep (se 1 (by rfl) ⟨2648645, by rfl⟩ : syracuseStep 3531527 = 5297291) B5297291
theorem B6284087 : Blo 1653526 6284087 := bstep (se 1 (by rfl) ⟨4713065, by rfl⟩ : syracuseStep 6284087 = 9426131) B9426131
theorem B1860655 : Blo 1653526 1860655 := bstep (se 1 (by rfl) ⟨1395491, by rfl⟩ : syracuseStep 1860655 = 2790983) B2790983
theorem B1860799 : Blo 1653526 1860799 := bstep (se 1 (by rfl) ⟨1395599, by rfl⟩ : syracuseStep 1860799 = 2791199) B2791199
theorem B5965103 : Blo 1653526 5965103 := bstep (se 1 (by rfl) ⟨4473827, by rfl⟩ : syracuseStep 5965103 = 8947655) B8947655
theorem B3720527 : Blo 1653526 3720527 := bstep (se 1 (by rfl) ⟨2790395, by rfl⟩ : syracuseStep 3720527 = 5580791) B5580791
theorem B1860943 : Blo 1653526 1860943 := bstep (se 1 (by rfl) ⟨1395707, by rfl⟩ : syracuseStep 1860943 = 2791415) B2791415
theorem B3720617 : Blo 1653526 3720617 := bstep (se 2 (by rfl) ⟨1395231, by rfl⟩ : syracuseStep 3720617 = 2790463) B2790463
theorem B31802807 : Blo 1653526 31802807 := bstep (se 1 (by rfl) ⟨23852105, by rfl⟩ : syracuseStep 31802807 = 47704211) B47704211
theorem B4187639 : Blo 1653526 4187639 := bstep (se 1 (by rfl) ⟨3140729, by rfl⟩ : syracuseStep 4187639 = 6281459) B6281459
theorem B9422507 : Blo 1653526 9422507 := bstep (se 1 (by rfl) ⟨7066880, by rfl⟩ : syracuseStep 9422507 = 14133761) B14133761
theorem B12560183 : Blo 1653526 12560183 := bstep (se 1 (by rfl) ⟨9420137, by rfl⟩ : syracuseStep 12560183 = 18840275) B18840275
theorem B6711119 : Blo 1653526 6711119 := bstep (se 1 (by rfl) ⟨5033339, by rfl⟩ : syracuseStep 6711119 = 10066679) B10066679
theorem B3721103 : Blo 1653526 3721103 := bstep (se 1 (by rfl) ⟨2790827, by rfl⟩ : syracuseStep 3721103 = 5581655) B5581655
theorem B4712347 : Blo 1653526 4712347 := bstep (se 1 (by rfl) ⟨3534260, by rfl⟩ : syracuseStep 4712347 = 7068521) B7068521
theorem B4188095 : Blo 1653526 4188095 := bstep (se 1 (by rfl) ⟨3141071, by rfl⟩ : syracuseStep 4188095 = 6282143) B6282143
theorem B3721247 : Blo 1653526 3721247 := bstep (se 1 (by rfl) ⟨2790935, by rfl⟩ : syracuseStep 3721247 = 5581871) B5581871
theorem B1861663 : Blo 1653526 1861663 := bstep (se 1 (by rfl) ⟨1396247, by rfl⟩ : syracuseStep 1861663 = 2792495) B2792495
theorem B4188257 : Blo 1653526 4188257 := bstep (se 2 (by rfl) ⟨1570596, by rfl⟩ : syracuseStep 4188257 = 3141193) B3141193
theorem B206579813 : Blo 1653526 206579813 := bstep (se 4 (by rfl) ⟨19366857, by rfl⟩ : syracuseStep 206579813 = 38733715) B38733715
theorem B6891641 : Blo 1653526 6891641 := bstep (se 2 (by rfl) ⟨2584365, by rfl⟩ : syracuseStep 6891641 = 5168731) B5168731
theorem B70772953 : Blo 1653526 70772953 := bstep (se 2 (by rfl) ⟨26539857, by rfl⟩ : syracuseStep 70772953 = 53079715) B53079715
theorem B6285545 : Blo 1653526 6285545 := bstep (se 2 (by rfl) ⟨2357079, by rfl⟩ : syracuseStep 6285545 = 4714159) B4714159
theorem B3721499 : Blo 1653526 3721499 := bstep (se 1 (by rfl) ⟨2791124, by rfl⟩ : syracuseStep 3721499 = 5582249) B5582249
theorem B1861915 : Blo 1653526 1861915 := bstep (se 1 (by rfl) ⟨1396436, by rfl⟩ : syracuseStep 1861915 = 2792873) B2792873
theorem B3975659 : Blo 1653526 3975659 := bstep (se 1 (by rfl) ⟨2981744, by rfl⟩ : syracuseStep 3975659 = 5963489) B5963489
theorem B2828791 : Blo 1653526 2828791 := bstep (se 1 (by rfl) ⟨2121593, by rfl⟩ : syracuseStep 2828791 = 4243187) B4243187
theorem B3721823 : Blo 1653526 3721823 := bstep (se 1 (by rfl) ⟨2791367, by rfl⟩ : syracuseStep 3721823 = 5582735) B5582735
theorem B3722075 : Blo 1653526 3722075 := bstep (se 1 (by rfl) ⟨2791556, by rfl⟩ : syracuseStep 3722075 = 5583113) B5583113
theorem B4189067 : Blo 1653526 4189067 := bstep (se 1 (by rfl) ⟨3141800, by rfl⟩ : syracuseStep 4189067 = 6283601) B6283601
theorem B26823761 : Blo 1653526 26823761 := bstep (se 2 (by rfl) ⟨10058910, by rfl⟩ : syracuseStep 26823761 = 20117821) B20117821
theorem B12561641 : Blo 1653526 12561641 := bstep (se 2 (by rfl) ⟨4710615, by rfl⟩ : syracuseStep 12561641 = 9421231) B9421231
theorem B11922713 : Blo 1653526 11922713 := bstep (se 2 (by rfl) ⟨4471017, by rfl⟩ : syracuseStep 11922713 = 8942035) B8942035
theorem B9424421 : Blo 1653526 9424421 := bstep (se 4 (by rfl) ⟨883539, by rfl⟩ : syracuseStep 9424421 = 1767079) B1767079
theorem B3722831 : Blo 1653526 3722831 := bstep (se 1 (by rfl) ⟨2792123, by rfl⟩ : syracuseStep 3722831 = 5584247) B5584247
theorem B5582519 : Blo 1653526 5582519 := bstep (se 1 (by rfl) ⟨4186889, by rfl⟩ : syracuseStep 5582519 = 8373779) B8373779
theorem B4198267 : Blo 1653526 4198267 := bstep (se 1 (by rfl) ⟨3148700, by rfl⟩ : syracuseStep 4198267 = 6297401) B6297401
theorem B10596221 : Blo 1653526 10596221 := bstep (se 3 (by rfl) ⟨1986791, by rfl⟩ : syracuseStep 10596221 = 3973583) B3973583
theorem B4190201 : Blo 1653526 4190201 := bstep (se 2 (by rfl) ⟨1571325, by rfl⟩ : syracuseStep 4190201 = 3142651) B3142651
theorem B181112921 : Blo 1653526 181112921 := bstep (se 2 (by rfl) ⟨67917345, by rfl⟩ : syracuseStep 181112921 = 135834691) B135834691
theorem B3723371 : Blo 1653526 3723371 := bstep (se 1 (by rfl) ⟨2792528, by rfl⟩ : syracuseStep 3723371 = 5585057) B5585057
theorem B1986715 : Blo 1653526 1986715 := bstep (se 1 (by rfl) ⟨1490036, by rfl⟩ : syracuseStep 1986715 = 2980073) B2980073
theorem B3723425 : Blo 1653526 3723425 := bstep (se 2 (by rfl) ⟨1396284, by rfl⟩ : syracuseStep 3723425 = 2792569) B2792569
theorem B3723551 : Blo 1653526 3723551 := bstep (se 1 (by rfl) ⟨2792663, by rfl⟩ : syracuseStep 3723551 = 5585327) B5585327
theorem B33960329 : Blo 1653526 33960329 := bstep (se 2 (by rfl) ⟨12735123, by rfl⟩ : syracuseStep 33960329 = 25470247) B25470247
theorem B9425423 : Blo 1653526 9425423 := bstep (se 1 (by rfl) ⟨7069067, by rfl⟩ : syracuseStep 9425423 = 14138135) B14138135
theorem B30175861 : Blo 1653526 30175861 := bstep (se 5 (by rfl) ⟨1414493, by rfl⟩ : syracuseStep 30175861 = 2828987) B2828987
theorem B15905483 : Blo 1653526 15905483 := bstep (se 1 (by rfl) ⟨11929112, by rfl⟩ : syracuseStep 15905483 = 23858225) B23858225
theorem B3142567 : Blo 1653526 3142567 := bstep (se 1 (by rfl) ⟨2356925, by rfl⟩ : syracuseStep 3142567 = 4713851) B4713851
theorem B3724271 : Blo 1653526 3724271 := bstep (se 1 (by rfl) ⟨2793203, by rfl⟩ : syracuseStep 3724271 = 5586407) B5586407
theorem B5583977 : Blo 1653526 5583977 := bstep (se 2 (by rfl) ⟨2093991, by rfl⟩ : syracuseStep 5583977 = 4187983) B4187983
theorem B2094331 : Blo 1653526 2094331 := bstep (se 1 (by rfl) ⟨1570748, by rfl⟩ : syracuseStep 2094331 = 3141497) B3141497
theorem B15308129 : Blo 1653526 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B2790767 : Blo 1653526 2790767 := bstep (se 1 (by rfl) ⟨2093075, by rfl⟩ : syracuseStep 2790767 = 4186151) B4186151
theorem B7067017 : Blo 1653526 7067017 := bstep (se 2 (by rfl) ⟨2650131, by rfl⟩ : syracuseStep 7067017 = 5300263) B5300263
theorem B3724775 : Blo 1653526 3724775 := bstep (se 1 (by rfl) ⟨2793581, by rfl⟩ : syracuseStep 3724775 = 5587163) B5587163
theorem B2790895 : Blo 1653526 2790895 := bstep (se 1 (by rfl) ⟨2093171, by rfl⟩ : syracuseStep 2790895 = 4186343) B4186343
theorem B2791327 : Blo 1653526 2791327 := bstep (se 1 (by rfl) ⟨2093495, by rfl⟩ : syracuseStep 2791327 = 4186991) B4186991
theorem B6281185 : Blo 1653526 6281185 := bstep (se 2 (by rfl) ⟨2355444, by rfl⟩ : syracuseStep 6281185 = 4710889) B4710889
theorem B4659191 : Blo 1653526 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B7952377 : Blo 1653526 7952377 := bstep (se 2 (by rfl) ⟨2982141, by rfl⟩ : syracuseStep 7952377 = 5964283) B5964283
theorem B2480543 : Blo 1653526 2480543 := bstep (se 1 (by rfl) ⟨1860407, by rfl⟩ : syracuseStep 2480543 = 3720815) B3720815
theorem B2480615 : Blo 1653526 2480615 := bstep (se 1 (by rfl) ⟨1860461, by rfl⟩ : syracuseStep 2480615 = 3720923) B3720923
theorem B42384059 : Blo 1653526 42384059 := bstep (se 1 (by rfl) ⟨31788044, by rfl⟩ : syracuseStep 42384059 = 63576089) B63576089
theorem B2980585 : Blo 1653526 2980585 := bstep (se 2 (by rfl) ⟨1117719, by rfl⟩ : syracuseStep 2980585 = 2235439) B2235439
theorem B57301829 : Blo 1653526 57301829 := bstep (se 4 (by rfl) ⟨5372046, by rfl⟩ : syracuseStep 57301829 = 10744093) B10744093
theorem B1653575 : Blo 1653526 1653575 := bstep (se 1 (by rfl) ⟨1240181, by rfl⟩ : syracuseStep 1653575 = 2480363) B2480363
theorem B1653615 : Blo 1653526 1653615 := bstep (se 1 (by rfl) ⟨1240211, by rfl⟩ : syracuseStep 1653615 = 2480423) B2480423
theorem B1653671 : Blo 1653526 1653671 := bstep (se 1 (by rfl) ⟨1240253, by rfl⟩ : syracuseStep 1653671 = 2480507) B2480507
theorem B1653851 : Blo 1653526 1653851 := bstep (se 1 (by rfl) ⟨1240388, by rfl⟩ : syracuseStep 1653851 = 2480777) B2480777
theorem B13417655 : Blo 1653526 13417655 := bstep (se 1 (by rfl) ⟨10063241, by rfl⟩ : syracuseStep 13417655 = 20126483) B20126483
theorem B1653967 : Blo 1653526 1653967 := bstep (se 1 (by rfl) ⟨1240475, by rfl⟩ : syracuseStep 1653967 = 2480951) B2480951
theorem B2481359 : Blo 1653526 2481359 := bstep (se 1 (by rfl) ⟨1861019, by rfl⟩ : syracuseStep 2481359 = 3722039) B3722039
theorem B1653991 : Blo 1653526 1653991 := bstep (se 1 (by rfl) ⟨1240493, by rfl⟩ : syracuseStep 1653991 = 2480987) B2480987
theorem B13409545 : Blo 1653526 13409545 := bstep (se 2 (by rfl) ⟨5028579, by rfl⟩ : syracuseStep 13409545 = 10057159) B10057159
theorem B1654087 : Blo 1653526 1654087 := bstep (se 1 (by rfl) ⟨1240565, by rfl⟩ : syracuseStep 1654087 = 2481131) B2481131
theorem B2481479 : Blo 1653526 2481479 := bstep (se 1 (by rfl) ⟨1861109, by rfl⟩ : syracuseStep 2481479 = 3722219) B3722219
theorem B5586299 : Blo 1653526 5586299 := bstep (se 1 (by rfl) ⟨4189724, by rfl⟩ : syracuseStep 5586299 = 8379449) B8379449
theorem B14138819 : Blo 1653526 14138819 := bstep (se 1 (by rfl) ⟨10604114, by rfl⟩ : syracuseStep 14138819 = 21208229) B21208229
theorem B1654223 : Blo 1653526 1654223 := bstep (se 1 (by rfl) ⟨1240667, by rfl⟩ : syracuseStep 1654223 = 2481335) B2481335
theorem B2481641 : Blo 1653526 2481641 := bstep (se 2 (by rfl) ⟨930615, by rfl⟩ : syracuseStep 2481641 = 1861231) B1861231
theorem B7159403 : Blo 1653526 7159403 := bstep (se 1 (by rfl) ⟨5369552, by rfl⟩ : syracuseStep 7159403 = 10739105) B10739105
theorem B1654383 : Blo 1653526 1654383 := bstep (se 1 (by rfl) ⟨1240787, by rfl⟩ : syracuseStep 1654383 = 2481575) B2481575
theorem B2481785 : Blo 1653526 2481785 := bstep (se 2 (by rfl) ⟨930669, by rfl⟩ : syracuseStep 2481785 = 1861339) B1861339
theorem B1654439 : Blo 1653526 1654439 := bstep (se 1 (by rfl) ⟨1240829, by rfl⟩ : syracuseStep 1654439 = 2481659) B2481659
theorem B1654503 : Blo 1653526 1654503 := bstep (se 1 (by rfl) ⟨1240877, by rfl⟩ : syracuseStep 1654503 = 2481755) B2481755
theorem B12738323 : Blo 1653526 12738323 := bstep (se 1 (by rfl) ⟨9553742, by rfl⟩ : syracuseStep 12738323 = 19107485) B19107485
theorem B1654559 : Blo 1653526 1654559 := bstep (se 1 (by rfl) ⟨1240919, by rfl⟩ : syracuseStep 1654559 = 2481839) B2481839
theorem B1654639 : Blo 1653526 1654639 := bstep (se 1 (by rfl) ⟨1240979, by rfl⟩ : syracuseStep 1654639 = 2481959) B2481959
theorem B2482031 : Blo 1653526 2482031 := bstep (se 1 (by rfl) ⟨1861523, by rfl⟩ : syracuseStep 2482031 = 3723047) B3723047
theorem B1654695 : Blo 1653526 1654695 := bstep (se 1 (by rfl) ⟨1241021, by rfl⟩ : syracuseStep 1654695 = 2482043) B2482043
theorem B5963719 : Blo 1653526 5963719 := bstep (se 1 (by rfl) ⟨4472789, by rfl⟩ : syracuseStep 5963719 = 8945579) B8945579
theorem B12566501 : Blo 1653526 12566501 := bstep (se 4 (by rfl) ⟨1178109, by rfl⟩ : syracuseStep 12566501 = 2356219) B2356219
theorem B2482217 : Blo 1653526 2482217 := bstep (se 2 (by rfl) ⟨930831, by rfl⟩ : syracuseStep 2482217 = 1861663) B1861663
theorem B120741947 : Blo 1653526 120741947 := bstep (se 1 (by rfl) ⟨90556460, by rfl⟩ : syracuseStep 120741947 = 181112921) B181112921
theorem B2482247 : Blo 1653526 2482247 := bstep (se 1 (by rfl) ⟨1861685, by rfl⟩ : syracuseStep 2482247 = 3723371) B3723371
theorem B2482283 : Blo 1653526 2482283 := bstep (se 1 (by rfl) ⟨1861712, by rfl⟩ : syracuseStep 2482283 = 3723425) B3723425
theorem B2482367 : Blo 1653526 2482367 := bstep (se 1 (by rfl) ⟨1861775, by rfl⟩ : syracuseStep 2482367 = 3723551) B3723551
theorem B550879501 : Blo 1653526 550879501 := bstep (se 3 (by rfl) ⟨103289906, by rfl⟩ : syracuseStep 550879501 = 206579813) B206579813
theorem B2982163 : Blo 1653526 2982163 := bstep (se 1 (by rfl) ⟨2236622, by rfl⟩ : syracuseStep 2982163 = 4473245) B4473245
theorem B94363937 : Blo 1653526 94363937 := bstep (se 2 (by rfl) ⟨35386476, by rfl⟩ : syracuseStep 94363937 = 70772953) B70772953
theorem B36782423 : Blo 1653526 36782423 := bstep (se 1 (by rfl) ⟨27586817, by rfl⟩ : syracuseStep 36782423 = 55173635) B55173635
theorem B6283615 : Blo 1653526 6283615 := bstep (se 1 (by rfl) ⟨4712711, by rfl⟩ : syracuseStep 6283615 = 9425423) B9425423
theorem B1655143 : Blo 1653526 1655143 := bstep (se 1 (by rfl) ⟨1241357, by rfl⟩ : syracuseStep 1655143 = 2482715) B2482715
theorem B2482553 : Blo 1653526 2482553 := bstep (se 2 (by rfl) ⟨930957, by rfl⟩ : syracuseStep 2482553 = 1861915) B1861915
theorem B98075063 : Blo 1653526 98075063 := bstep (se 1 (by rfl) ⟨73556297, by rfl⟩ : syracuseStep 98075063 = 147112595) B147112595
theorem B1655263 : Blo 1653526 1655263 := bstep (se 1 (by rfl) ⟨1241447, by rfl⟩ : syracuseStep 1655263 = 2482895) B2482895
theorem B1655271 : Blo 1653526 1655271 := bstep (se 1 (by rfl) ⟨1241453, by rfl⟩ : syracuseStep 1655271 = 2482907) B2482907
theorem B2482847 : Blo 1653526 2482847 := bstep (se 1 (by rfl) ⟨1862135, by rfl⟩ : syracuseStep 2482847 = 3724271) B3724271
theorem B1860511 : Blo 1653526 1860511 := bstep (se 1 (by rfl) ⟨1395383, by rfl⟩ : syracuseStep 1860511 = 2790767) B2790767
theorem B40821677 : Blo 1653526 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B21201871 : Blo 1653526 21201871 := bstep (se 1 (by rfl) ⟨15901403, by rfl⟩ : syracuseStep 21201871 = 31802807) B31802807
theorem B3974113 : Blo 1653526 3974113 := bstep (se 2 (by rfl) ⟨1490292, by rfl⟩ : syracuseStep 3974113 = 2980585) B2980585
theorem B2483183 : Blo 1653526 2483183 := bstep (se 1 (by rfl) ⟨1862387, by rfl⟩ : syracuseStep 2483183 = 3724775) B3724775
theorem B8373455 : Blo 1653526 8373455 := bstep (se 1 (by rfl) ⟨6280091, by rfl⟩ : syracuseStep 8373455 = 12560183) B12560183
theorem B4474079 : Blo 1653526 4474079 := bstep (se 1 (by rfl) ⟨3355559, by rfl⟩ : syracuseStep 4474079 = 6711119) B6711119
theorem B3106127 : Blo 1653526 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B28256039 : Blo 1653526 28256039 := bstep (se 1 (by rfl) ⟨21192029, by rfl⟩ : syracuseStep 28256039 = 42384059) B42384059
theorem B9422689 : Blo 1653526 9422689 := bstep (se 2 (by rfl) ⟨3533508, by rfl⟩ : syracuseStep 9422689 = 7067017) B7067017
theorem B38201219 : Blo 1653526 38201219 := bstep (se 1 (by rfl) ⟨28650914, by rfl⟩ : syracuseStep 38201219 = 57301829) B57301829
theorem B22390757 : Blo 1653526 22390757 := bstep (se 4 (by rfl) ⟨2099133, by rfl⟩ : syracuseStep 22390757 = 4198267) B4198267
theorem B3721193 : Blo 1653526 3721193 := bstep (se 2 (by rfl) ⟨1395447, by rfl⟩ : syracuseStep 3721193 = 2790895) B2790895
theorem B8374427 : Blo 1653526 8374427 := bstep (se 1 (by rfl) ⟨6280820, by rfl⟩ : syracuseStep 8374427 = 12561641) B12561641
theorem B7948475 : Blo 1653526 7948475 := bstep (se 1 (by rfl) ⟨5961356, by rfl⟩ : syracuseStep 7948475 = 11922713) B11922713
theorem B3721679 : Blo 1653526 3721679 := bstep (se 1 (by rfl) ⟨2791259, by rfl⟩ : syracuseStep 3721679 = 5582519) B5582519
theorem B3721769 : Blo 1653526 3721769 := bstep (se 2 (by rfl) ⟨1395663, by rfl⟩ : syracuseStep 3721769 = 2791327) B2791327
theorem B7064147 : Blo 1653526 7064147 := bstep (se 1 (by rfl) ⟨5298110, by rfl⟩ : syracuseStep 7064147 = 10596221) B10596221
theorem B8374913 : Blo 1653526 8374913 := bstep (se 2 (by rfl) ⟨3140592, by rfl⟩ : syracuseStep 8374913 = 6281185) B6281185
theorem B10603169 : Blo 1653526 10603169 := bstep (se 2 (by rfl) ⟨3976188, by rfl⟩ : syracuseStep 10603169 = 7952377) B7952377
theorem B2648953 : Blo 1653526 2648953 := bstep (se 2 (by rfl) ⟨993357, by rfl⟩ : syracuseStep 2648953 = 1986715) B1986715
theorem B10603655 : Blo 1653526 10603655 := bstep (se 1 (by rfl) ⟨7952741, by rfl⟩ : syracuseStep 10603655 = 15905483) B15905483
theorem B2354351 : Blo 1653526 2354351 := bstep (se 1 (by rfl) ⟨1765763, by rfl⟩ : syracuseStep 2354351 = 3531527) B3531527
theorem B4189391 : Blo 1653526 4189391 := bstep (se 1 (by rfl) ⟨3142043, by rfl⟩ : syracuseStep 4189391 = 6284087) B6284087
theorem B3771721 : Blo 1653526 3771721 := bstep (se 2 (by rfl) ⟨1414395, by rfl⟩ : syracuseStep 3771721 = 2828791) B2828791
theorem B3722651 : Blo 1653526 3722651 := bstep (se 1 (by rfl) ⟨2791988, by rfl⟩ : syracuseStep 3722651 = 5583977) B5583977
theorem B40234481 : Blo 1653526 40234481 := bstep (se 2 (by rfl) ⟨15087930, by rfl⟩ : syracuseStep 40234481 = 30175861) B30175861
theorem B4190089 : Blo 1653526 4190089 := bstep (se 2 (by rfl) ⟨1571283, by rfl⟩ : syracuseStep 4190089 = 3142567) B3142567
theorem B4190363 : Blo 1653526 4190363 := bstep (se 1 (by rfl) ⟨3142772, by rfl⟩ : syracuseStep 4190363 = 6285545) B6285545
theorem B2650439 : Blo 1653526 2650439 := bstep (se 1 (by rfl) ⟨1987829, by rfl⟩ : syracuseStep 2650439 = 3975659) B3975659
theorem B17879393 : Blo 1653526 17879393 := bstep (se 2 (by rfl) ⟨6704772, by rfl⟩ : syracuseStep 17879393 = 13409545) B13409545
theorem B33968861 : Blo 1653526 33968861 := bstep (se 3 (by rfl) ⟨6369161, by rfl⟩ : syracuseStep 33968861 = 12738323) B12738323
theorem B3724199 : Blo 1653526 3724199 := bstep (se 1 (by rfl) ⟨2793149, by rfl⟩ : syracuseStep 3724199 = 5586299) B5586299
theorem B9425879 : Blo 1653526 9425879 := bstep (se 1 (by rfl) ⟨7069409, by rfl⟩ : syracuseStep 9425879 = 14138819) B14138819
theorem B4772935 : Blo 1653526 4772935 := bstep (se 1 (by rfl) ⟨3579701, by rfl⟩ : syracuseStep 4772935 = 7159403) B7159403
theorem B2793467 : Blo 1653526 2793467 := bstep (se 1 (by rfl) ⟨2095100, by rfl⟩ : syracuseStep 2793467 = 4190201) B4190201
theorem B7951625 : Blo 1653526 7951625 := bstep (se 2 (by rfl) ⟨2981859, by rfl⟩ : syracuseStep 7951625 = 5963719) B5963719
theorem B8377667 : Blo 1653526 8377667 := bstep (se 1 (by rfl) ⟨6283250, by rfl⟩ : syracuseStep 8377667 = 12566501) B12566501
theorem B10196347 : Blo 1653526 10196347 := bstep (se 1 (by rfl) ⟨7647260, by rfl⟩ : syracuseStep 10196347 = 15294521) B15294521
theorem B6280699 : Blo 1653526 6280699 := bstep (se 1 (by rfl) ⟨4710524, by rfl⟩ : syracuseStep 6280699 = 9421049) B9421049
theorem B2791003 : Blo 1653526 2791003 := bstep (se 1 (by rfl) ⟨2093252, by rfl⟩ : syracuseStep 2791003 = 4186505) B4186505
theorem B22640219 : Blo 1653526 22640219 := bstep (se 1 (by rfl) ⟨16980164, by rfl⟩ : syracuseStep 22640219 = 33960329) B33960329
theorem B35780413 : Blo 1653526 35780413 := bstep (se 3 (by rfl) ⟨6708827, by rfl⟩ : syracuseStep 35780413 = 13417655) B13417655
theorem B15906941 : Blo 1653526 15906941 := bstep (se 3 (by rfl) ⟨2982551, by rfl⟩ : syracuseStep 15906941 = 5965103) B5965103
theorem B2480351 : Blo 1653526 2480351 := bstep (se 1 (by rfl) ⟨1860263, by rfl⟩ : syracuseStep 2480351 = 3720527) B3720527
theorem B2480411 : Blo 1653526 2480411 := bstep (se 1 (by rfl) ⟨1860308, by rfl⟩ : syracuseStep 2480411 = 3720617) B3720617
theorem B2791759 : Blo 1653526 2791759 := bstep (se 1 (by rfl) ⟨2093819, by rfl⟩ : syracuseStep 2791759 = 4187639) B4187639
theorem B6281671 : Blo 1653526 6281671 := bstep (se 1 (by rfl) ⟨4711253, by rfl⟩ : syracuseStep 6281671 = 9422507) B9422507
theorem B2480735 : Blo 1653526 2480735 := bstep (se 1 (by rfl) ⟨1860551, by rfl⟩ : syracuseStep 2480735 = 3721103) B3721103
theorem B2792063 : Blo 1653526 2792063 := bstep (se 1 (by rfl) ⟨2094047, by rfl⟩ : syracuseStep 2792063 = 4188095) B4188095
theorem B2480831 : Blo 1653526 2480831 := bstep (se 1 (by rfl) ⟨1860623, by rfl⟩ : syracuseStep 2480831 = 3721247) B3721247
theorem B2480873 : Blo 1653526 2480873 := bstep (se 2 (by rfl) ⟨930327, by rfl⟩ : syracuseStep 2480873 = 1860655) B1860655
theorem B2792171 : Blo 1653526 2792171 := bstep (se 1 (by rfl) ⟨2094128, by rfl⟩ : syracuseStep 2792171 = 4188257) B4188257
theorem B4594427 : Blo 1653526 4594427 := bstep (se 1 (by rfl) ⟨3445820, by rfl⟩ : syracuseStep 4594427 = 6891641) B6891641
theorem B2480999 : Blo 1653526 2480999 := bstep (se 1 (by rfl) ⟨1860749, by rfl⟩ : syracuseStep 2480999 = 3721499) B3721499
theorem B2481065 : Blo 1653526 2481065 := bstep (se 2 (by rfl) ⟨930399, by rfl⟩ : syracuseStep 2481065 = 1860799) B1860799
theorem B1653695 : Blo 1653526 1653695 := bstep (se 1 (by rfl) ⟨1240271, by rfl⟩ : syracuseStep 1653695 = 2480543) B2480543
theorem B1653743 : Blo 1653526 1653743 := bstep (se 1 (by rfl) ⟨1240307, by rfl⟩ : syracuseStep 1653743 = 2480615) B2480615
theorem B2792441 : Blo 1653526 2792441 := bstep (se 2 (by rfl) ⟨1047165, by rfl⟩ : syracuseStep 2792441 = 2094331) B2094331
theorem B2481215 : Blo 1653526 2481215 := bstep (se 1 (by rfl) ⟨1860911, by rfl⟩ : syracuseStep 2481215 = 3721823) B3721823
theorem B2481257 : Blo 1653526 2481257 := bstep (se 2 (by rfl) ⟨930471, by rfl⟩ : syracuseStep 2481257 = 1860943) B1860943
theorem B2481383 : Blo 1653526 2481383 := bstep (se 1 (by rfl) ⟨1861037, by rfl⟩ : syracuseStep 2481383 = 3722075) B3722075
theorem B2792711 : Blo 1653526 2792711 := bstep (se 1 (by rfl) ⟨2094533, by rfl⟩ : syracuseStep 2792711 = 4189067) B4189067
theorem B17882507 : Blo 1653526 17882507 := bstep (se 1 (by rfl) ⟨13411880, by rfl⟩ : syracuseStep 17882507 = 26823761) B26823761
theorem B1654239 : Blo 1653526 1654239 := bstep (se 1 (by rfl) ⟨1240679, by rfl⟩ : syracuseStep 1654239 = 2481359) B2481359
theorem B1654319 : Blo 1653526 1654319 := bstep (se 1 (by rfl) ⟨1240739, by rfl⟩ : syracuseStep 1654319 = 2481479) B2481479
theorem B1654427 : Blo 1653526 1654427 := bstep (se 1 (by rfl) ⟨1240820, by rfl⟩ : syracuseStep 1654427 = 2481641) B2481641
theorem B6282947 : Blo 1653526 6282947 := bstep (se 1 (by rfl) ⟨4712210, by rfl⟩ : syracuseStep 6282947 = 9424421) B9424421
theorem B2481887 : Blo 1653526 2481887 := bstep (se 1 (by rfl) ⟨1861415, by rfl⟩ : syracuseStep 2481887 = 3722831) B3722831
theorem B1654523 : Blo 1653526 1654523 := bstep (se 1 (by rfl) ⟨1240892, by rfl⟩ : syracuseStep 1654523 = 2481785) B2481785
theorem B6283129 : Blo 1653526 6283129 := bstep (se 2 (by rfl) ⟨2356173, by rfl⟩ : syracuseStep 6283129 = 4712347) B4712347
theorem B1654687 : Blo 1653526 1654687 := bstep (se 1 (by rfl) ⟨1241015, by rfl⟩ : syracuseStep 1654687 = 2482031) B2482031
theorem B1654811 : Blo 1653526 1654811 := bstep (se 1 (by rfl) ⟨1241108, by rfl⟩ : syracuseStep 1654811 = 2482217) B2482217
theorem B80494631 : Blo 1653526 80494631 := bstep (se 1 (by rfl) ⟨60370973, by rfl⟩ : syracuseStep 80494631 = 120741947) B120741947
theorem B1654831 : Blo 1653526 1654831 := bstep (se 1 (by rfl) ⟨1241123, by rfl⟩ : syracuseStep 1654831 = 2482247) B2482247
theorem B1654855 : Blo 1653526 1654855 := bstep (se 1 (by rfl) ⟨1241141, by rfl⟩ : syracuseStep 1654855 = 2482283) B2482283
theorem B2793575 : Blo 1653526 2793575 := bstep (se 1 (by rfl) ⟨2095181, by rfl⟩ : syracuseStep 2793575 = 4190363) B4190363
theorem B1654911 : Blo 1653526 1654911 := bstep (se 1 (by rfl) ⟨1241183, by rfl⟩ : syracuseStep 1654911 = 2482367) B2482367
theorem B11919595 : Blo 1653526 11919595 := bstep (se 1 (by rfl) ⟨8939696, by rfl⟩ : syracuseStep 11919595 = 17879393) B17879393
theorem B1655035 : Blo 1653526 1655035 := bstep (se 1 (by rfl) ⟨1241276, by rfl⟩ : syracuseStep 1655035 = 2482553) B2482553
theorem B1655231 : Blo 1653526 1655231 := bstep (se 1 (by rfl) ⟨1241423, by rfl⟩ : syracuseStep 1655231 = 2482847) B2482847
theorem B2482799 : Blo 1653526 2482799 := bstep (se 1 (by rfl) ⟨1862099, by rfl⟩ : syracuseStep 2482799 = 3724199) B3724199
theorem B27214451 : Blo 1653526 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B6283919 : Blo 1653526 6283919 := bstep (se 1 (by rfl) ⟨4712939, by rfl⟩ : syracuseStep 6283919 = 9425879) B9425879
theorem B1655455 : Blo 1653526 1655455 := bstep (se 1 (by rfl) ⟨1241591, by rfl⟩ : syracuseStep 1655455 = 2483183) B2483183
theorem B2982719 : Blo 1653526 2982719 := bstep (se 1 (by rfl) ⟨2237039, by rfl⟩ : syracuseStep 2982719 = 4474079) B4474079
theorem B5301083 : Blo 1653526 5301083 := bstep (se 1 (by rfl) ⟨3975812, by rfl⟩ : syracuseStep 5301083 = 7951625) B7951625
theorem B8283005 : Blo 1653526 8283005 := bstep (se 3 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 8283005 = 3106127) B3106127
theorem B3531937 : Blo 1653526 3531937 := bstep (se 2 (by rfl) ⟨1324476, by rfl⟩ : syracuseStep 3531937 = 2648953) B2648953
theorem B14927171 : Blo 1653526 14927171 := bstep (se 1 (by rfl) ⟨11195378, by rfl⟩ : syracuseStep 14927171 = 22390757) B22390757
theorem B1861375 : Blo 1653526 1861375 := bstep (se 1 (by rfl) ⟨1396031, by rfl⟩ : syracuseStep 1861375 = 2792063) B2792063
theorem B1861447 : Blo 1653526 1861447 := bstep (se 1 (by rfl) ⟨1396085, by rfl⟩ : syracuseStep 1861447 = 2792171) B2792171
theorem B8374265 : Blo 1653526 8374265 := bstep (se 2 (by rfl) ⟨3140349, by rfl⟩ : syracuseStep 8374265 = 6280699) B6280699
theorem B1861627 : Blo 1653526 1861627 := bstep (se 1 (by rfl) ⟨1396220, by rfl⟩ : syracuseStep 1861627 = 2792441) B2792441
theorem B3721337 : Blo 1653526 3721337 := bstep (se 2 (by rfl) ⟨1395501, by rfl⟩ : syracuseStep 3721337 = 2791003) B2791003
theorem B1861807 : Blo 1653526 1861807 := bstep (se 1 (by rfl) ⟨1396355, by rfl⟩ : syracuseStep 1861807 = 2792711) B2792711
theorem B11921671 : Blo 1653526 11921671 := bstep (se 1 (by rfl) ⟨8941253, by rfl⟩ : syracuseStep 11921671 = 17882507) B17882507
theorem B26822987 : Blo 1653526 26822987 := bstep (se 1 (by rfl) ⟨20117240, by rfl⟩ : syracuseStep 26822987 = 40234481) B40234481
theorem B4188631 : Blo 1653526 4188631 := bstep (se 1 (by rfl) ⟨3141473, by rfl⟩ : syracuseStep 4188631 = 6282947) B6282947
theorem B1862311 : Blo 1653526 1862311 := bstep (se 1 (by rfl) ⟨1396733, by rfl⟩ : syracuseStep 1862311 = 2793467) B2793467
theorem B62909291 : Blo 1653526 62909291 := bstep (se 1 (by rfl) ⟨47181968, by rfl⟩ : syracuseStep 62909291 = 94363937) B94363937
theorem B24521615 : Blo 1653526 24521615 := bstep (se 1 (by rfl) ⟨18391211, by rfl⟩ : syracuseStep 24521615 = 36782423) B36782423
theorem B734506001 : Blo 1653526 734506001 := bstep (se 2 (by rfl) ⟨275439750, by rfl⟩ : syracuseStep 734506001 = 550879501) B550879501
theorem B3976217 : Blo 1653526 3976217 := bstep (se 2 (by rfl) ⟨1491081, by rfl⟩ : syracuseStep 3976217 = 2982163) B2982163
theorem B3722345 : Blo 1653526 3722345 := bstep (se 2 (by rfl) ⟨1395879, by rfl⟩ : syracuseStep 3722345 = 2791759) B2791759
theorem B6278269 : Blo 1653526 6278269 := bstep (se 3 (by rfl) ⟨1177175, by rfl⟩ : syracuseStep 6278269 = 2354351) B2354351
theorem B22645907 : Blo 1653526 22645907 := bstep (se 1 (by rfl) ⟨16984430, by rfl⟩ : syracuseStep 22645907 = 33968861) B33968861
theorem B8375561 : Blo 1653526 8375561 := bstep (se 2 (by rfl) ⟨3140835, by rfl⟩ : syracuseStep 8375561 = 6281671) B6281671
theorem B5582303 : Blo 1653526 5582303 := bstep (se 1 (by rfl) ⟨4186727, by rfl⟩ : syracuseStep 5582303 = 8373455) B8373455
theorem B15093479 : Blo 1653526 15093479 := bstep (se 1 (by rfl) ⟨11320109, by rfl⟩ : syracuseStep 15093479 = 22640219) B22640219
theorem B261533501 : Blo 1653526 261533501 := bstep (se 3 (by rfl) ⟨49037531, by rfl⟩ : syracuseStep 261533501 = 98075063) B98075063
theorem B18837359 : Blo 1653526 18837359 := bstep (se 1 (by rfl) ⟨14128019, by rfl⟩ : syracuseStep 18837359 = 28256039) B28256039
theorem B10604627 : Blo 1653526 10604627 := bstep (se 1 (by rfl) ⟨7953470, by rfl⟩ : syracuseStep 10604627 = 15906941) B15906941
theorem B5582951 : Blo 1653526 5582951 := bstep (se 1 (by rfl) ⟨4187213, by rfl⟩ : syracuseStep 5582951 = 8374427) B8374427
theorem B5583275 : Blo 1653526 5583275 := bstep (se 1 (by rfl) ⟨4187456, by rfl⟩ : syracuseStep 5583275 = 8374913) B8374913
theorem B13595129 : Blo 1653526 13595129 := bstep (se 2 (by rfl) ⟨5098173, by rfl⟩ : syracuseStep 13595129 = 10196347) B10196347
theorem B47707217 : Blo 1653526 47707217 := bstep (se 2 (by rfl) ⟨17890206, by rfl⟩ : syracuseStep 47707217 = 35780413) B35780413
theorem B12563585 : Blo 1653526 12563585 := bstep (se 2 (by rfl) ⟨4711344, by rfl⟩ : syracuseStep 12563585 = 9422689) B9422689
theorem B8377505 : Blo 1653526 8377505 := bstep (se 2 (by rfl) ⟨3141564, by rfl⟩ : syracuseStep 8377505 = 6283129) B6283129
theorem B8378153 : Blo 1653526 8378153 := bstep (se 2 (by rfl) ⟨3141807, by rfl⟩ : syracuseStep 8378153 = 6283615) B6283615
theorem B7067837 : Blo 1653526 7067837 := bstep (se 3 (by rfl) ⟨1325219, by rfl⟩ : syracuseStep 7067837 = 2650439) B2650439
theorem B5585111 : Blo 1653526 5585111 := bstep (se 1 (by rfl) ⟨4188833, by rfl⟩ : syracuseStep 5585111 = 8377667) B8377667
theorem B2480681 : Blo 1653526 2480681 := bstep (se 2 (by rfl) ⟨930255, by rfl⟩ : syracuseStep 2480681 = 1860511) B1860511
theorem B25467479 : Blo 1653526 25467479 := bstep (se 1 (by rfl) ⟨19100609, by rfl⟩ : syracuseStep 25467479 = 38201219) B38201219
theorem B28269161 : Blo 1653526 28269161 := bstep (se 2 (by rfl) ⟨10600935, by rfl⟩ : syracuseStep 28269161 = 21201871) B21201871
theorem B5298817 : Blo 1653526 5298817 := bstep (se 2 (by rfl) ⟨1987056, by rfl⟩ : syracuseStep 5298817 = 3974113) B3974113
theorem B2480795 : Blo 1653526 2480795 := bstep (se 1 (by rfl) ⟨1860596, by rfl⟩ : syracuseStep 2480795 = 3721193) B3721193
theorem B6363913 : Blo 1653526 6363913 := bstep (se 2 (by rfl) ⟨2386467, by rfl⟩ : syracuseStep 6363913 = 4772935) B4772935
theorem B5298983 : Blo 1653526 5298983 := bstep (se 1 (by rfl) ⟨3974237, by rfl⟩ : syracuseStep 5298983 = 7948475) B7948475
theorem B1653567 : Blo 1653526 1653567 := bstep (se 1 (by rfl) ⟨1240175, by rfl⟩ : syracuseStep 1653567 = 2480351) B2480351
theorem B1653607 : Blo 1653526 1653607 := bstep (se 1 (by rfl) ⟨1240205, by rfl⟩ : syracuseStep 1653607 = 2480411) B2480411
theorem B2481119 : Blo 1653526 2481119 := bstep (se 1 (by rfl) ⟨1860839, by rfl⟩ : syracuseStep 2481119 = 3721679) B3721679
theorem B2481179 : Blo 1653526 2481179 := bstep (se 1 (by rfl) ⟨1860884, by rfl⟩ : syracuseStep 2481179 = 3721769) B3721769
theorem B4709431 : Blo 1653526 4709431 := bstep (se 1 (by rfl) ⟨3532073, by rfl⟩ : syracuseStep 4709431 = 7064147) B7064147
theorem B1653823 : Blo 1653526 1653823 := bstep (se 1 (by rfl) ⟨1240367, by rfl⟩ : syracuseStep 1653823 = 2480735) B2480735
theorem B5028961 : Blo 1653526 5028961 := bstep (se 2 (by rfl) ⟨1885860, by rfl⟩ : syracuseStep 5028961 = 3771721) B3771721
theorem B7068779 : Blo 1653526 7068779 := bstep (se 1 (by rfl) ⟨5301584, by rfl⟩ : syracuseStep 7068779 = 10603169) B10603169
theorem B1653887 : Blo 1653526 1653887 := bstep (se 1 (by rfl) ⟨1240415, by rfl⟩ : syracuseStep 1653887 = 2480831) B2480831
theorem B1653915 : Blo 1653526 1653915 := bstep (se 1 (by rfl) ⟨1240436, by rfl⟩ : syracuseStep 1653915 = 2480873) B2480873
theorem B3062951 : Blo 1653526 3062951 := bstep (se 1 (by rfl) ⟨2297213, by rfl⟩ : syracuseStep 3062951 = 4594427) B4594427
theorem B1653999 : Blo 1653526 1653999 := bstep (se 1 (by rfl) ⟨1240499, by rfl⟩ : syracuseStep 1653999 = 2480999) B2480999
theorem B1654043 : Blo 1653526 1654043 := bstep (se 1 (by rfl) ⟨1240532, by rfl⟩ : syracuseStep 1654043 = 2481065) B2481065
theorem B1654143 : Blo 1653526 1654143 := bstep (se 1 (by rfl) ⟨1240607, by rfl⟩ : syracuseStep 1654143 = 2481215) B2481215
theorem B1654171 : Blo 1653526 1654171 := bstep (se 1 (by rfl) ⟨1240628, by rfl⟩ : syracuseStep 1654171 = 2481257) B2481257
theorem B7069103 : Blo 1653526 7069103 := bstep (se 1 (by rfl) ⟨5301827, by rfl⟩ : syracuseStep 7069103 = 10603655) B10603655
theorem B2792927 : Blo 1653526 2792927 := bstep (se 1 (by rfl) ⟨2094695, by rfl⟩ : syracuseStep 2792927 = 4189391) B4189391
theorem B1654255 : Blo 1653526 1654255 := bstep (se 1 (by rfl) ⟨1240691, by rfl⟩ : syracuseStep 1654255 = 2481383) B2481383
theorem B2481767 : Blo 1653526 2481767 := bstep (se 1 (by rfl) ⟨1861325, by rfl⟩ : syracuseStep 2481767 = 3722651) B3722651
theorem B1654591 : Blo 1653526 1654591 := bstep (se 1 (by rfl) ⟨1240943, by rfl⟩ : syracuseStep 1654591 = 2481887) B2481887
theorem B5586785 : Blo 1653526 5586785 := bstep (se 2 (by rfl) ⟨2095044, by rfl⟩ : syracuseStep 5586785 = 4190089) B4190089
theorem B7069751 : Blo 1653526 7069751 := bstep (se 1 (by rfl) ⟨5302313, by rfl⟩ : syracuseStep 7069751 = 10604627) B10604627
theorem B2482409 : Blo 1653526 2482409 := bstep (se 2 (by rfl) ⟨930903, by rfl⟩ : syracuseStep 2482409 = 1861807) B1861807
theorem B15892793 : Blo 1653526 15892793 := bstep (se 2 (by rfl) ⟨5959797, by rfl⟩ : syracuseStep 15892793 = 11919595) B11919595
theorem B1655199 : Blo 1653526 1655199 := bstep (se 1 (by rfl) ⟨1241399, by rfl⟩ : syracuseStep 1655199 = 2482799) B2482799
theorem B5522003 : Blo 1653526 5522003 := bstep (se 1 (by rfl) ⟨4141502, by rfl⟩ : syracuseStep 5522003 = 8283005) B8283005
theorem B39805789 : Blo 1653526 39805789 := bstep (se 3 (by rfl) ⟨7463585, by rfl⟩ : syracuseStep 39805789 = 14927171) B14927171
theorem B2483081 : Blo 1653526 2483081 := bstep (se 2 (by rfl) ⟨931155, by rfl⟩ : syracuseStep 2483081 = 1862311) B1862311
theorem B3532655 : Blo 1653526 3532655 := bstep (se 1 (by rfl) ⟨2649491, by rfl⟩ : syracuseStep 3532655 = 5298983) B5298983
theorem B489670667 : Blo 1653526 489670667 := bstep (se 1 (by rfl) ⟨367253000, by rfl⟩ : syracuseStep 489670667 = 734506001) B734506001
theorem B4712519 : Blo 1653526 4712519 := bstep (se 1 (by rfl) ⟨3534389, by rfl⟩ : syracuseStep 4712519 = 7068779) B7068779
theorem B2041967 : Blo 1653526 2041967 := bstep (se 1 (by rfl) ⟨1531475, by rfl⟩ : syracuseStep 2041967 = 3062951) B3062951
theorem B4712735 : Blo 1653526 4712735 := bstep (se 1 (by rfl) ⟨3534551, by rfl⟩ : syracuseStep 4712735 = 7069103) B7069103
theorem B3721535 : Blo 1653526 3721535 := bstep (se 1 (by rfl) ⟨2791151, by rfl⟩ : syracuseStep 3721535 = 5582303) B5582303
theorem B1861951 : Blo 1653526 1861951 := bstep (se 1 (by rfl) ⟨1396463, by rfl⟩ : syracuseStep 1861951 = 2792927) B2792927
theorem B10062319 : Blo 1653526 10062319 := bstep (se 1 (by rfl) ⟨7546739, by rfl⟩ : syracuseStep 10062319 = 15093479) B15093479
theorem B3721967 : Blo 1653526 3721967 := bstep (se 1 (by rfl) ⟨2791475, by rfl⟩ : syracuseStep 3721967 = 5582951) B5582951
theorem B1862383 : Blo 1653526 1862383 := bstep (se 1 (by rfl) ⟨1396787, by rfl⟩ : syracuseStep 1862383 = 2793575) B2793575
theorem B3722183 : Blo 1653526 3722183 := bstep (se 1 (by rfl) ⟨2791637, by rfl⟩ : syracuseStep 3722183 = 5583275) B5583275
theorem B9063419 : Blo 1653526 9063419 := bstep (se 1 (by rfl) ⟨6797564, by rfl⟩ : syracuseStep 9063419 = 13595129) B13595129
theorem B15895561 : Blo 1653526 15895561 := bstep (se 2 (by rfl) ⟨5960835, by rfl⟩ : syracuseStep 15895561 = 11921671) B11921671
theorem B4189279 : Blo 1653526 4189279 := bstep (se 1 (by rfl) ⟨3141959, by rfl⟩ : syracuseStep 4189279 = 6283919) B6283919
theorem B31804811 : Blo 1653526 31804811 := bstep (se 1 (by rfl) ⟨23853608, by rfl⟩ : syracuseStep 31804811 = 47707217) B47707217
theorem B8375723 : Blo 1653526 8375723 := bstep (se 1 (by rfl) ⟨6281792, by rfl⟩ : syracuseStep 8375723 = 12563585) B12563585
theorem B7065089 : Blo 1653526 7065089 := bstep (se 2 (by rfl) ⟨2649408, by rfl⟩ : syracuseStep 7065089 = 5298817) B5298817
theorem B5582843 : Blo 1653526 5582843 := bstep (se 1 (by rfl) ⟨4187132, by rfl⟩ : syracuseStep 5582843 = 8374265) B8374265
theorem B6279241 : Blo 1653526 6279241 := bstep (se 2 (by rfl) ⟨2354715, by rfl⟩ : syracuseStep 6279241 = 4709431) B4709431
theorem B6705281 : Blo 1653526 6705281 := bstep (se 2 (by rfl) ⟨2514480, by rfl⟩ : syracuseStep 6705281 = 5028961) B5028961
theorem B3723407 : Blo 1653526 3723407 := bstep (se 1 (by rfl) ⟨2792555, by rfl⟩ : syracuseStep 3723407 = 5585111) B5585111
theorem B16978319 : Blo 1653526 16978319 := bstep (se 1 (by rfl) ⟨12733739, by rfl⟩ : syracuseStep 16978319 = 25467479) B25467479
theorem B18846107 : Blo 1653526 18846107 := bstep (se 1 (by rfl) ⟨14134580, by rfl⟩ : syracuseStep 18846107 = 28269161) B28269161
theorem B41939527 : Blo 1653526 41939527 := bstep (se 1 (by rfl) ⟨31454645, by rfl⟩ : syracuseStep 41939527 = 62909291) B62909291
theorem B16347743 : Blo 1653526 16347743 := bstep (se 1 (by rfl) ⟨12260807, by rfl⟩ : syracuseStep 16347743 = 24521615) B24521615
theorem B2650811 : Blo 1653526 2650811 := bstep (se 1 (by rfl) ⟨1988108, by rfl⟩ : syracuseStep 2650811 = 3976217) B3976217
theorem B5583707 : Blo 1653526 5583707 := bstep (se 1 (by rfl) ⟨4187780, by rfl⟩ : syracuseStep 5583707 = 8375561) B8375561
theorem B14136221 : Blo 1653526 14136221 := bstep (se 3 (by rfl) ⟨2650541, by rfl⟩ : syracuseStep 14136221 = 5301083) B5301083
theorem B174355667 : Blo 1653526 174355667 := bstep (se 1 (by rfl) ⟨130766750, by rfl⟩ : syracuseStep 174355667 = 261533501) B261533501
theorem B3724523 : Blo 1653526 3724523 := bstep (se 1 (by rfl) ⟨2793392, by rfl⟩ : syracuseStep 3724523 = 5586785) B5586785
theorem B53663087 : Blo 1653526 53663087 := bstep (se 1 (by rfl) ⟨40247315, by rfl⟩ : syracuseStep 53663087 = 80494631) B80494631
theorem B18142967 : Blo 1653526 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B18847565 : Blo 1653526 18847565 := bstep (se 3 (by rfl) ⟨3533918, by rfl⟩ : syracuseStep 18847565 = 7067837) B7067837
theorem B1988479 : Blo 1653526 1988479 := bstep (se 1 (by rfl) ⟨1491359, by rfl⟩ : syracuseStep 1988479 = 2982719) B2982719
theorem B5584841 : Blo 1653526 5584841 := bstep (se 2 (by rfl) ⟨2094315, by rfl⟩ : syracuseStep 5584841 = 4188631) B4188631
theorem B5585003 : Blo 1653526 5585003 := bstep (se 1 (by rfl) ⟨4188752, by rfl⟩ : syracuseStep 5585003 = 8377505) B8377505
theorem B8485217 : Blo 1653526 8485217 := bstep (se 2 (by rfl) ⟨3181956, by rfl⟩ : syracuseStep 8485217 = 6363913) B6363913
theorem B5585435 : Blo 1653526 5585435 := bstep (se 1 (by rfl) ⟨4189076, by rfl⟩ : syracuseStep 5585435 = 8378153) B8378153
theorem B2480891 : Blo 1653526 2480891 := bstep (se 1 (by rfl) ⟨1860668, by rfl⟩ : syracuseStep 2480891 = 3721337) B3721337
theorem B8371025 : Blo 1653526 8371025 := bstep (se 2 (by rfl) ⟨3139134, by rfl⟩ : syracuseStep 8371025 = 6278269) B6278269
theorem B4709249 : Blo 1653526 4709249 := bstep (se 2 (by rfl) ⟨1765968, by rfl⟩ : syracuseStep 4709249 = 3531937) B3531937
theorem B17881991 : Blo 1653526 17881991 := bstep (se 1 (by rfl) ⟨13411493, by rfl⟩ : syracuseStep 17881991 = 26822987) B26822987
theorem B1653787 : Blo 1653526 1653787 := bstep (se 1 (by rfl) ⟨1240340, by rfl⟩ : syracuseStep 1653787 = 2480681) B2480681
theorem B1653863 : Blo 1653526 1653863 := bstep (se 1 (by rfl) ⟨1240397, by rfl⟩ : syracuseStep 1653863 = 2480795) B2480795
theorem B1654079 : Blo 1653526 1654079 := bstep (se 1 (by rfl) ⟨1240559, by rfl⟩ : syracuseStep 1654079 = 2481119) B2481119
theorem B1654119 : Blo 1653526 1654119 := bstep (se 1 (by rfl) ⟨1240589, by rfl⟩ : syracuseStep 1654119 = 2481179) B2481179
theorem B2481563 : Blo 1653526 2481563 := bstep (se 1 (by rfl) ⟨1861172, by rfl⟩ : syracuseStep 2481563 = 3722345) B3722345
theorem B15097271 : Blo 1653526 15097271 := bstep (se 1 (by rfl) ⟨11322953, by rfl⟩ : syracuseStep 15097271 = 22645907) B22645907
theorem B2481833 : Blo 1653526 2481833 := bstep (se 2 (by rfl) ⟨930687, by rfl⟩ : syracuseStep 2481833 = 1861375) B1861375
theorem B1654511 : Blo 1653526 1654511 := bstep (se 1 (by rfl) ⟨1240883, by rfl⟩ : syracuseStep 1654511 = 2481767) B2481767
theorem B2481929 : Blo 1653526 2481929 := bstep (se 2 (by rfl) ⟨930723, by rfl⟩ : syracuseStep 2481929 = 1861447) B1861447
theorem B12558239 : Blo 1653526 12558239 := bstep (se 1 (by rfl) ⟨9418679, by rfl⟩ : syracuseStep 12558239 = 18837359) B18837359
theorem B2482169 : Blo 1653526 2482169 := bstep (se 2 (by rfl) ⟨930813, by rfl⟩ : syracuseStep 2482169 = 1861627) B1861627
theorem B2482271 : Blo 1653526 2482271 := bstep (se 1 (by rfl) ⟨1861703, by rfl⟩ : syracuseStep 2482271 = 3723407) B3723407
theorem B8372321 : Blo 1653526 8372321 := bstep (se 2 (by rfl) ⟨3139620, by rfl⟩ : syracuseStep 8372321 = 6279241) B6279241
theorem B1654939 : Blo 1653526 1654939 := bstep (se 1 (by rfl) ⟨1241204, by rfl⟩ : syracuseStep 1654939 = 2482409) B2482409
theorem B2482601 : Blo 1653526 2482601 := bstep (se 2 (by rfl) ⟨930975, by rfl⟩ : syracuseStep 2482601 = 1861951) B1861951
theorem B1655387 : Blo 1653526 1655387 := bstep (se 1 (by rfl) ⟨1241540, by rfl⟩ : syracuseStep 1655387 = 2483081) B2483081
theorem B55919369 : Blo 1653526 55919369 := bstep (se 2 (by rfl) ⟨20969763, by rfl⟩ : syracuseStep 55919369 = 41939527) B41939527
theorem B116237111 : Blo 1653526 116237111 := bstep (se 1 (by rfl) ⟨87177833, by rfl⟩ : syracuseStep 116237111 = 174355667) B174355667
theorem B2483015 : Blo 1653526 2483015 := bstep (se 1 (by rfl) ⟨1862261, by rfl⟩ : syracuseStep 2483015 = 3724523) B3724523
theorem B35775391 : Blo 1653526 35775391 := bstep (se 1 (by rfl) ⟨26831543, by rfl⟩ : syracuseStep 35775391 = 53663087) B53663087
theorem B2483177 : Blo 1653526 2483177 := bstep (se 2 (by rfl) ⟨931191, by rfl⟩ : syracuseStep 2483177 = 1862383) B1862383
theorem B21194081 : Blo 1653526 21194081 := bstep (se 2 (by rfl) ⟨7947780, by rfl⟩ : syracuseStep 21194081 = 15895561) B15895561
theorem B5580683 : Blo 1653526 5580683 := bstep (se 1 (by rfl) ⟨4185512, by rfl⟩ : syracuseStep 5580683 = 8371025) B8371025
theorem B3139499 : Blo 1653526 3139499 := bstep (se 1 (by rfl) ⟨2354624, by rfl⟩ : syracuseStep 3139499 = 4709249) B4709249
theorem B11921327 : Blo 1653526 11921327 := bstep (se 1 (by rfl) ⟨8940995, by rfl⟩ : syracuseStep 11921327 = 17881991) B17881991
theorem B21203207 : Blo 1653526 21203207 := bstep (se 1 (by rfl) ⟨15902405, by rfl⟩ : syracuseStep 21203207 = 31804811) B31804811
theorem B24169117 : Blo 1653526 24169117 := bstep (se 3 (by rfl) ⟨4531709, by rfl⟩ : syracuseStep 24169117 = 9063419) B9063419
theorem B3721895 : Blo 1653526 3721895 := bstep (se 1 (by rfl) ⟨2791421, by rfl⟩ : syracuseStep 3721895 = 5582843) B5582843
theorem B4713167 : Blo 1653526 4713167 := bstep (se 1 (by rfl) ⟨3534875, by rfl⟩ : syracuseStep 4713167 = 7069751) B7069751
theorem B10595195 : Blo 1653526 10595195 := bstep (se 1 (by rfl) ⟨7946396, by rfl⟩ : syracuseStep 10595195 = 15892793) B15892793
theorem B3681335 : Blo 1653526 3681335 := bstep (se 1 (by rfl) ⟨2761001, by rfl⟩ : syracuseStep 3681335 = 5522003) B5522003
theorem B10898495 : Blo 1653526 10898495 := bstep (se 1 (by rfl) ⟨8173871, by rfl⟩ : syracuseStep 10898495 = 16347743) B16347743
theorem B3722471 : Blo 1653526 3722471 := bstep (se 1 (by rfl) ⟨2791853, by rfl⟩ : syracuseStep 3722471 = 5583707) B5583707
theorem B9424147 : Blo 1653526 9424147 := bstep (se 1 (by rfl) ⟨7068110, by rfl⟩ : syracuseStep 9424147 = 14136221) B14136221
theorem B40259389 : Blo 1653526 40259389 := bstep (se 3 (by rfl) ⟨7548635, by rfl⟩ : syracuseStep 40259389 = 15097271) B15097271
theorem B2355103 : Blo 1653526 2355103 := bstep (se 1 (by rfl) ⟨1766327, by rfl⟩ : syracuseStep 2355103 = 3532655) B3532655
theorem B3723227 : Blo 1653526 3723227 := bstep (se 1 (by rfl) ⟨2792420, by rfl⟩ : syracuseStep 3723227 = 5584841) B5584841
theorem B326447111 : Blo 1653526 326447111 := bstep (se 1 (by rfl) ⟨244835333, by rfl⟩ : syracuseStep 326447111 = 489670667) B489670667
theorem B3141679 : Blo 1653526 3141679 := bstep (se 1 (by rfl) ⟨2356259, by rfl⟩ : syracuseStep 3141679 = 4712519) B4712519
theorem B3723335 : Blo 1653526 3723335 := bstep (se 1 (by rfl) ⟨2792501, by rfl⟩ : syracuseStep 3723335 = 5585003) B5585003
theorem B3141823 : Blo 1653526 3141823 := bstep (se 1 (by rfl) ⟨2356367, by rfl⟩ : syracuseStep 3141823 = 4712735) B4712735
theorem B5656811 : Blo 1653526 5656811 := bstep (se 1 (by rfl) ⟨4242608, by rfl⟩ : syracuseStep 5656811 = 8485217) B8485217
theorem B3723623 : Blo 1653526 3723623 := bstep (se 1 (by rfl) ⟨2792717, by rfl⟩ : syracuseStep 3723623 = 5585435) B5585435
theorem B5583815 : Blo 1653526 5583815 := bstep (se 1 (by rfl) ⟨4187861, by rfl⟩ : syracuseStep 5583815 = 8375723) B8375723
theorem B2651305 : Blo 1653526 2651305 := bstep (se 2 (by rfl) ⟨994239, by rfl⟩ : syracuseStep 2651305 = 1988479) B1988479
theorem B4470187 : Blo 1653526 4470187 := bstep (se 1 (by rfl) ⟨3352640, by rfl⟩ : syracuseStep 4470187 = 6705281) B6705281
theorem B11318879 : Blo 1653526 11318879 := bstep (se 1 (by rfl) ⟨8489159, by rfl⟩ : syracuseStep 11318879 = 16978319) B16978319
theorem B12564071 : Blo 1653526 12564071 := bstep (se 1 (by rfl) ⟨9423053, by rfl⟩ : syracuseStep 12564071 = 18846107) B18846107
theorem B5445245 : Blo 1653526 5445245 := bstep (se 3 (by rfl) ⟨1020983, by rfl⟩ : syracuseStep 5445245 = 2041967) B2041967
theorem B13416425 : Blo 1653526 13416425 := bstep (se 2 (by rfl) ⟨5031159, by rfl⟩ : syracuseStep 13416425 = 10062319) B10062319
theorem B53074385 : Blo 1653526 53074385 := bstep (se 2 (by rfl) ⟨19902894, by rfl⟩ : syracuseStep 53074385 = 39805789) B39805789
theorem B12565043 : Blo 1653526 12565043 := bstep (se 1 (by rfl) ⟨9423782, by rfl⟩ : syracuseStep 12565043 = 18847565) B18847565
theorem B5585705 : Blo 1653526 5585705 := bstep (se 2 (by rfl) ⟨2094639, by rfl⟩ : syracuseStep 5585705 = 4189279) B4189279
theorem B2481023 : Blo 1653526 2481023 := bstep (se 1 (by rfl) ⟨1860767, by rfl⟩ : syracuseStep 2481023 = 3721535) B3721535
theorem B7068829 : Blo 1653526 7068829 := bstep (se 3 (by rfl) ⟨1325405, by rfl⟩ : syracuseStep 7068829 = 2650811) B2650811
theorem B2481311 : Blo 1653526 2481311 := bstep (se 1 (by rfl) ⟨1860983, by rfl⟩ : syracuseStep 2481311 = 3721967) B3721967
theorem B1653927 : Blo 1653526 1653927 := bstep (se 1 (by rfl) ⟨1240445, by rfl⟩ : syracuseStep 1653927 = 2480891) B2480891
theorem B2481455 : Blo 1653526 2481455 := bstep (se 1 (by rfl) ⟨1861091, by rfl⟩ : syracuseStep 2481455 = 3722183) B3722183
theorem B48381245 : Blo 1653526 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B1654375 : Blo 1653526 1654375 := bstep (se 1 (by rfl) ⟨1240781, by rfl⟩ : syracuseStep 1654375 = 2481563) B2481563
theorem B4710059 : Blo 1653526 4710059 := bstep (se 1 (by rfl) ⟨3532544, by rfl⟩ : syracuseStep 4710059 = 7065089) B7065089
theorem B1654555 : Blo 1653526 1654555 := bstep (se 1 (by rfl) ⟨1240916, by rfl⟩ : syracuseStep 1654555 = 2481833) B2481833
theorem B1654619 : Blo 1653526 1654619 := bstep (se 1 (by rfl) ⟨1240964, by rfl⟩ : syracuseStep 1654619 = 2481929) B2481929
theorem B8372159 : Blo 1653526 8372159 := bstep (se 1 (by rfl) ⟨6279119, by rfl⟩ : syracuseStep 8372159 = 12558239) B12558239
theorem B1654779 : Blo 1653526 1654779 := bstep (se 1 (by rfl) ⟨1241084, by rfl⟩ : syracuseStep 1654779 = 2482169) B2482169
theorem B2482223 : Blo 1653526 2482223 := bstep (se 1 (by rfl) ⟨1861667, by rfl⟩ : syracuseStep 2482223 = 3723335) B3723335
theorem B1654847 : Blo 1653526 1654847 := bstep (se 1 (by rfl) ⟨1241135, by rfl⟩ : syracuseStep 1654847 = 2482271) B2482271
theorem B2482415 : Blo 1653526 2482415 := bstep (se 1 (by rfl) ⟨1861811, by rfl⟩ : syracuseStep 2482415 = 3723623) B3723623
theorem B1655067 : Blo 1653526 1655067 := bstep (se 1 (by rfl) ⟨1241300, by rfl⟩ : syracuseStep 1655067 = 2482601) B2482601
theorem B1655343 : Blo 1653526 1655343 := bstep (se 1 (by rfl) ⟨1241507, by rfl⟩ : syracuseStep 1655343 = 2483015) B2483015
theorem B1655451 : Blo 1653526 1655451 := bstep (se 1 (by rfl) ⟨1241588, by rfl⟩ : syracuseStep 1655451 = 2483177) B2483177
theorem B3720455 : Blo 1653526 3720455 := bstep (se 1 (by rfl) ⟨2790341, by rfl⟩ : syracuseStep 3720455 = 5580683) B5580683
theorem B7947551 : Blo 1653526 7947551 := bstep (se 1 (by rfl) ⟨5960663, by rfl⟩ : syracuseStep 7947551 = 11921327) B11921327
theorem B35382923 : Blo 1653526 35382923 := bstep (se 1 (by rfl) ⟨26537192, by rfl⟩ : syracuseStep 35382923 = 53074385) B53074385
theorem B12568445 : Blo 1653526 12568445 := bstep (se 3 (by rfl) ⟨2356583, by rfl⟩ : syracuseStep 12568445 = 4713167) B4713167
theorem B7063463 : Blo 1653526 7063463 := bstep (se 1 (by rfl) ⟨5297597, by rfl⟩ : syracuseStep 7063463 = 10595195) B10595195
theorem B32254163 : Blo 1653526 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B3140039 : Blo 1653526 3140039 := bstep (se 1 (by rfl) ⟨2355029, by rfl⟩ : syracuseStep 3140039 = 4710059) B4710059
theorem B3140137 : Blo 1653526 3140137 := bstep (se 2 (by rfl) ⟨1177551, by rfl⟩ : syracuseStep 3140137 = 2355103) B2355103
theorem B5581439 : Blo 1653526 5581439 := bstep (se 1 (by rfl) ⟨4186079, by rfl⟩ : syracuseStep 5581439 = 8372159) B8372159
theorem B217631407 : Blo 1653526 217631407 := bstep (se 1 (by rfl) ⟨163223555, by rfl⟩ : syracuseStep 217631407 = 326447111) B326447111
theorem B4188905 : Blo 1653526 4188905 := bstep (se 2 (by rfl) ⟨1570839, by rfl⟩ : syracuseStep 4188905 = 3141679) B3141679
theorem B5581547 : Blo 1653526 5581547 := bstep (se 1 (by rfl) ⟨4186160, by rfl⟩ : syracuseStep 5581547 = 8372321) B8372321
theorem B4189097 : Blo 1653526 4189097 := bstep (se 2 (by rfl) ⟨1570911, by rfl⟩ : syracuseStep 4189097 = 3141823) B3141823
theorem B15084829 : Blo 1653526 15084829 := bstep (se 3 (by rfl) ⟨2828405, by rfl⟩ : syracuseStep 15084829 = 5656811) B5656811
theorem B3722543 : Blo 1653526 3722543 := bstep (se 1 (by rfl) ⟨2791907, by rfl⟩ : syracuseStep 3722543 = 5583815) B5583815
theorem B8376047 : Blo 1653526 8376047 := bstep (se 1 (by rfl) ⟨6282035, by rfl⟩ : syracuseStep 8376047 = 12564071) B12564071
theorem B14135471 : Blo 1653526 14135471 := bstep (se 1 (by rfl) ⟨10601603, by rfl⟩ : syracuseStep 14135471 = 21203207) B21203207
theorem B9425105 : Blo 1653526 9425105 := bstep (se 2 (by rfl) ⟨3534414, by rfl⟩ : syracuseStep 9425105 = 7068829) B7068829
theorem B3535073 : Blo 1653526 3535073 := bstep (se 2 (by rfl) ⟨1325652, by rfl⟩ : syracuseStep 3535073 = 2651305) B2651305
theorem B30183677 : Blo 1653526 30183677 := bstep (se 3 (by rfl) ⟨5659439, by rfl⟩ : syracuseStep 30183677 = 11318879) B11318879
theorem B14520653 : Blo 1653526 14520653 := bstep (se 3 (by rfl) ⟨2722622, by rfl⟩ : syracuseStep 14520653 = 5445245) B5445245
theorem B8376695 : Blo 1653526 8376695 := bstep (se 1 (by rfl) ⟨6282521, by rfl⟩ : syracuseStep 8376695 = 12565043) B12565043
theorem B3723803 : Blo 1653526 3723803 := bstep (se 1 (by rfl) ⟨2792852, by rfl⟩ : syracuseStep 3723803 = 5585705) B5585705
theorem B5960249 : Blo 1653526 5960249 := bstep (se 2 (by rfl) ⟨2235093, by rfl⟩ : syracuseStep 5960249 = 4470187) B4470187
theorem B2454223 : Blo 1653526 2454223 := bstep (se 1 (by rfl) ⟨1840667, by rfl⟩ : syracuseStep 2454223 = 3681335) B3681335
theorem B309965629 : Blo 1653526 309965629 := bstep (se 3 (by rfl) ⟨58118555, by rfl⟩ : syracuseStep 309965629 = 116237111) B116237111
theorem B53679185 : Blo 1653526 53679185 := bstep (se 2 (by rfl) ⟨20129694, by rfl⟩ : syracuseStep 53679185 = 40259389) B40259389
theorem B32225489 : Blo 1653526 32225489 := bstep (se 2 (by rfl) ⟨12084558, by rfl⟩ : syracuseStep 32225489 = 24169117) B24169117
theorem B14129387 : Blo 1653526 14129387 := bstep (se 1 (by rfl) ⟨10597040, by rfl⟩ : syracuseStep 14129387 = 21194081) B21194081
theorem B47700521 : Blo 1653526 47700521 := bstep (se 2 (by rfl) ⟨17887695, by rfl⟩ : syracuseStep 47700521 = 35775391) B35775391
theorem B8944283 : Blo 1653526 8944283 := bstep (se 1 (by rfl) ⟨6708212, by rfl⟩ : syracuseStep 8944283 = 13416425) B13416425
theorem B12565529 : Blo 1653526 12565529 := bstep (se 2 (by rfl) ⟨4712073, by rfl⟩ : syracuseStep 12565529 = 9424147) B9424147
theorem B2481263 : Blo 1653526 2481263 := bstep (se 1 (by rfl) ⟨1860947, by rfl⟩ : syracuseStep 2481263 = 3721895) B3721895
theorem B1654015 : Blo 1653526 1654015 := bstep (se 1 (by rfl) ⟨1240511, by rfl⟩ : syracuseStep 1654015 = 2481023) B2481023
theorem B149118317 : Blo 1653526 149118317 := bstep (se 3 (by rfl) ⟨27959684, by rfl⟩ : syracuseStep 149118317 = 55919369) B55919369
theorem B7265663 : Blo 1653526 7265663 := bstep (se 1 (by rfl) ⟨5449247, by rfl⟩ : syracuseStep 7265663 = 10898495) B10898495
theorem B1654207 : Blo 1653526 1654207 := bstep (se 1 (by rfl) ⟨1240655, by rfl⟩ : syracuseStep 1654207 = 2481311) B2481311
theorem B2481647 : Blo 1653526 2481647 := bstep (se 1 (by rfl) ⟨1861235, by rfl⟩ : syracuseStep 2481647 = 3722471) B3722471
theorem B1654303 : Blo 1653526 1654303 := bstep (se 1 (by rfl) ⟨1240727, by rfl⟩ : syracuseStep 1654303 = 2481455) B2481455
theorem B8371997 : Blo 1653526 8371997 := bstep (se 3 (by rfl) ⟨1569749, by rfl⟩ : syracuseStep 8371997 = 3139499) B3139499
theorem B2482151 : Blo 1653526 2482151 := bstep (se 1 (by rfl) ⟨1861613, by rfl⟩ : syracuseStep 2482151 = 3723227) B3723227
theorem B1654815 : Blo 1653526 1654815 := bstep (se 1 (by rfl) ⟨1241111, by rfl⟩ : syracuseStep 1654815 = 2482223) B2482223
theorem B6283403 : Blo 1653526 6283403 := bstep (se 1 (by rfl) ⟨4712552, by rfl⟩ : syracuseStep 6283403 = 9425105) B9425105
theorem B1654943 : Blo 1653526 1654943 := bstep (se 1 (by rfl) ⟨1241207, by rfl⟩ : syracuseStep 1654943 = 2482415) B2482415
theorem B2482535 : Blo 1653526 2482535 := bstep (se 1 (by rfl) ⟨1861901, by rfl⟩ : syracuseStep 2482535 = 3723803) B3723803
theorem B3973499 : Blo 1653526 3973499 := bstep (se 1 (by rfl) ⟨2980124, by rfl⟩ : syracuseStep 3973499 = 5960249) B5960249
theorem B4186849 : Blo 1653526 4186849 := bstep (se 2 (by rfl) ⟨1570068, by rfl⟩ : syracuseStep 4186849 = 3140137) B3140137
theorem B413287505 : Blo 1653526 413287505 := bstep (se 2 (by rfl) ⟨154982814, by rfl⟩ : syracuseStep 413287505 = 309965629) B309965629
theorem B20113105 : Blo 1653526 20113105 := bstep (se 2 (by rfl) ⟨7542414, by rfl⟩ : syracuseStep 20113105 = 15084829) B15084829
theorem B3720959 : Blo 1653526 3720959 := bstep (se 1 (by rfl) ⟨2790719, by rfl⟩ : syracuseStep 3720959 = 5581439) B5581439
theorem B3721031 : Blo 1653526 3721031 := bstep (se 1 (by rfl) ⟨2790773, by rfl⟩ : syracuseStep 3721031 = 5581547) B5581547
theorem B99412211 : Blo 1653526 99412211 := bstep (se 1 (by rfl) ⟨74559158, by rfl⟩ : syracuseStep 99412211 = 149118317) B149118317
theorem B4843775 : Blo 1653526 4843775 := bstep (se 1 (by rfl) ⟨3632831, by rfl⟩ : syracuseStep 4843775 = 7265663) B7265663
theorem B18835901 : Blo 1653526 18835901 := bstep (se 3 (by rfl) ⟨3531731, by rfl⟩ : syracuseStep 18835901 = 7063463) B7063463
theorem B5581331 : Blo 1653526 5581331 := bstep (se 1 (by rfl) ⟨4185998, by rfl⟩ : syracuseStep 5581331 = 8371997) B8371997
theorem B9423647 : Blo 1653526 9423647 := bstep (se 1 (by rfl) ⟨7067735, by rfl⟩ : syracuseStep 9423647 = 14135471) B14135471
theorem B20122451 : Blo 1653526 20122451 := bstep (se 1 (by rfl) ⟨15091838, by rfl⟩ : syracuseStep 20122451 = 30183677) B30183677
theorem B35786123 : Blo 1653526 35786123 := bstep (se 1 (by rfl) ⟨26839592, by rfl⟩ : syracuseStep 35786123 = 53679185) B53679185
theorem B3272297 : Blo 1653526 3272297 := bstep (se 2 (by rfl) ⟨1227111, by rfl⟩ : syracuseStep 3272297 = 2454223) B2454223
theorem B23588615 : Blo 1653526 23588615 := bstep (se 1 (by rfl) ⟨17691461, by rfl⟩ : syracuseStep 23588615 = 35382923) B35382923
theorem B21483659 : Blo 1653526 21483659 := bstep (se 1 (by rfl) ⟨16112744, by rfl⟩ : syracuseStep 21483659 = 32225489) B32225489
theorem B2093359 : Blo 1653526 2093359 := bstep (se 1 (by rfl) ⟨1570019, by rfl⟩ : syracuseStep 2093359 = 3140039) B3140039
theorem B23851421 : Blo 1653526 23851421 := bstep (se 3 (by rfl) ⟨4472141, by rfl⟩ : syracuseStep 23851421 = 8944283) B8944283
theorem B8377019 : Blo 1653526 8377019 := bstep (se 1 (by rfl) ⟨6282764, by rfl⟩ : syracuseStep 8377019 = 12565529) B12565529
theorem B5584031 : Blo 1653526 5584031 := bstep (se 1 (by rfl) ⟨4188023, by rfl⟩ : syracuseStep 5584031 = 8376047) B8376047
theorem B2356715 : Blo 1653526 2356715 := bstep (se 1 (by rfl) ⟨1767536, by rfl⟩ : syracuseStep 2356715 = 3535073) B3535073
theorem B9680435 : Blo 1653526 9680435 := bstep (se 1 (by rfl) ⟨7260326, by rfl⟩ : syracuseStep 9680435 = 14520653) B14520653
theorem B5584463 : Blo 1653526 5584463 := bstep (se 1 (by rfl) ⟨4188347, by rfl⟩ : syracuseStep 5584463 = 8376695) B8376695
theorem B2480303 : Blo 1653526 2480303 := bstep (se 1 (by rfl) ⟨1860227, by rfl⟩ : syracuseStep 2480303 = 3720455) B3720455
theorem B5298367 : Blo 1653526 5298367 := bstep (se 1 (by rfl) ⟨3973775, by rfl⟩ : syracuseStep 5298367 = 7947551) B7947551
theorem B290175209 : Blo 1653526 290175209 := bstep (se 2 (by rfl) ⟨108815703, by rfl⟩ : syracuseStep 290175209 = 217631407) B217631407
theorem B8378963 : Blo 1653526 8378963 := bstep (se 1 (by rfl) ⟨6284222, by rfl⟩ : syracuseStep 8378963 = 12568445) B12568445
theorem B21502775 : Blo 1653526 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B9419591 : Blo 1653526 9419591 := bstep (se 1 (by rfl) ⟨7064693, by rfl⟩ : syracuseStep 9419591 = 14129387) B14129387
theorem B31800347 : Blo 1653526 31800347 := bstep (se 1 (by rfl) ⟨23850260, by rfl⟩ : syracuseStep 31800347 = 47700521) B47700521
theorem B2792603 : Blo 1653526 2792603 := bstep (se 1 (by rfl) ⟨2094452, by rfl⟩ : syracuseStep 2792603 = 4188905) B4188905
theorem B2792731 : Blo 1653526 2792731 := bstep (se 1 (by rfl) ⟨2094548, by rfl⟩ : syracuseStep 2792731 = 4189097) B4189097
theorem B1654175 : Blo 1653526 1654175 := bstep (se 1 (by rfl) ⟨1240631, by rfl⟩ : syracuseStep 1654175 = 2481263) B2481263
theorem B2481695 : Blo 1653526 2481695 := bstep (se 1 (by rfl) ⟨1861271, by rfl⟩ : syracuseStep 2481695 = 3722543) B3722543
theorem B1654431 : Blo 1653526 1654431 := bstep (se 1 (by rfl) ⟨1240823, by rfl⟩ : syracuseStep 1654431 = 2481647) B2481647
theorem B1654767 : Blo 1653526 1654767 := bstep (se 1 (by rfl) ⟨1241075, by rfl⟩ : syracuseStep 1654767 = 2482151) B2482151
theorem B1655023 : Blo 1653526 1655023 := bstep (se 1 (by rfl) ⟨1241267, by rfl⟩ : syracuseStep 1655023 = 2482535) B2482535
theorem B15900947 : Blo 1653526 15900947 := bstep (se 1 (by rfl) ⟨11925710, by rfl⟩ : syracuseStep 15900947 = 23851421) B23851421
theorem B6284573 : Blo 1653526 6284573 := bstep (se 3 (by rfl) ⟨1178357, by rfl⟩ : syracuseStep 6284573 = 2356715) B2356715
theorem B66274807 : Blo 1653526 66274807 := bstep (se 1 (by rfl) ⟨49706105, by rfl⟩ : syracuseStep 66274807 = 99412211) B99412211
theorem B8726125 : Blo 1653526 8726125 := bstep (se 3 (by rfl) ⟨1636148, by rfl⟩ : syracuseStep 8726125 = 3272297) B3272297
theorem B3720887 : Blo 1653526 3720887 := bstep (se 1 (by rfl) ⟨2790665, by rfl⟩ : syracuseStep 3720887 = 5581331) B5581331
theorem B1861735 : Blo 1653526 1861735 := bstep (se 1 (by rfl) ⟨1396301, by rfl⟩ : syracuseStep 1861735 = 2792603) B2792603
theorem B23857415 : Blo 1653526 23857415 := bstep (se 1 (by rfl) ⟨17893061, by rfl⟩ : syracuseStep 23857415 = 35786123) B35786123
theorem B14322439 : Blo 1653526 14322439 := bstep (se 1 (by rfl) ⟨10741829, by rfl⟩ : syracuseStep 14322439 = 21483659) B21483659
theorem B4188935 : Blo 1653526 4188935 := bstep (se 1 (by rfl) ⟨3141701, by rfl⟩ : syracuseStep 4188935 = 6283403) B6283403
theorem B2648999 : Blo 1653526 2648999 := bstep (se 1 (by rfl) ⟨1986749, by rfl⟩ : syracuseStep 2648999 = 3973499) B3973499
theorem B7064489 : Blo 1653526 7064489 := bstep (se 2 (by rfl) ⟨2649183, by rfl⟩ : syracuseStep 7064489 = 5298367) B5298367
theorem B275525003 : Blo 1653526 275525003 := bstep (se 1 (by rfl) ⟨206643752, by rfl⟩ : syracuseStep 275525003 = 413287505) B413287505
theorem B3722687 : Blo 1653526 3722687 := bstep (se 1 (by rfl) ⟨2792015, by rfl⟩ : syracuseStep 3722687 = 5584031) B5584031
theorem B5582465 : Blo 1653526 5582465 := bstep (se 2 (by rfl) ⟨2093424, by rfl⟩ : syracuseStep 5582465 = 4186849) B4186849
theorem B3722975 : Blo 1653526 3722975 := bstep (se 1 (by rfl) ⟨2792231, by rfl⟩ : syracuseStep 3722975 = 5584463) B5584463
theorem B193450139 : Blo 1653526 193450139 := bstep (se 1 (by rfl) ⟨145087604, by rfl⟩ : syracuseStep 193450139 = 290175209) B290175209
theorem B3723641 : Blo 1653526 3723641 := bstep (se 2 (by rfl) ⟨1396365, by rfl⟩ : syracuseStep 3723641 = 2792731) B2792731
theorem B6279727 : Blo 1653526 6279727 := bstep (se 1 (by rfl) ⟨4709795, by rfl⟩ : syracuseStep 6279727 = 9419591) B9419591
theorem B13414967 : Blo 1653526 13414967 := bstep (se 1 (by rfl) ⟨10061225, by rfl⟩ : syracuseStep 13414967 = 20122451) B20122451
theorem B62902973 : Blo 1653526 62902973 := bstep (se 3 (by rfl) ⟨11794307, by rfl⟩ : syracuseStep 62902973 = 23588615) B23588615
theorem B26817473 : Blo 1653526 26817473 := bstep (se 2 (by rfl) ⟨10056552, by rfl⟩ : syracuseStep 26817473 = 20113105) B20113105
theorem B2791145 : Blo 1653526 2791145 := bstep (se 2 (by rfl) ⟨1046679, by rfl⟩ : syracuseStep 2791145 = 2093359) B2093359
theorem B5584679 : Blo 1653526 5584679 := bstep (se 1 (by rfl) ⟨4188509, by rfl⟩ : syracuseStep 5584679 = 8377019) B8377019
theorem B6453623 : Blo 1653526 6453623 := bstep (se 1 (by rfl) ⟨4840217, by rfl⟩ : syracuseStep 6453623 = 9680435) B9680435
theorem B2480639 : Blo 1653526 2480639 := bstep (se 1 (by rfl) ⟨1860479, by rfl⟩ : syracuseStep 2480639 = 3720959) B3720959
theorem B2480687 : Blo 1653526 2480687 := bstep (se 1 (by rfl) ⟨1860515, by rfl⟩ : syracuseStep 2480687 = 3721031) B3721031
theorem B1653535 : Blo 1653526 1653535 := bstep (se 1 (by rfl) ⟨1240151, by rfl⟩ : syracuseStep 1653535 = 2480303) B2480303
theorem B12557267 : Blo 1653526 12557267 := bstep (se 1 (by rfl) ⟨9417950, by rfl⟩ : syracuseStep 12557267 = 18835901) B18835901
theorem B5585975 : Blo 1653526 5585975 := bstep (se 1 (by rfl) ⟨4189481, by rfl⟩ : syracuseStep 5585975 = 8378963) B8378963
theorem B6282431 : Blo 1653526 6282431 := bstep (se 1 (by rfl) ⟨4711823, by rfl⟩ : syracuseStep 6282431 = 9423647) B9423647
theorem B14335183 : Blo 1653526 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B21200231 : Blo 1653526 21200231 := bstep (se 1 (by rfl) ⟨15900173, by rfl⟩ : syracuseStep 21200231 = 31800347) B31800347
theorem B1654463 : Blo 1653526 1654463 := bstep (se 1 (by rfl) ⟨1240847, by rfl⟩ : syracuseStep 1654463 = 2481695) B2481695
theorem B826670933 : Blo 1653526 826670933 := bstep (se 9 (by rfl) ⟨2421887, by rfl⟩ : syracuseStep 826670933 = 4843775) B4843775
theorem B128966759 : Blo 1653526 128966759 := bstep (se 1 (by rfl) ⟨96725069, by rfl⟩ : syracuseStep 128966759 = 193450139) B193450139
theorem B2482313 : Blo 1653526 2482313 := bstep (se 2 (by rfl) ⟨930867, by rfl⟩ : syracuseStep 2482313 = 1861735) B1861735
theorem B10600631 : Blo 1653526 10600631 := bstep (se 1 (by rfl) ⟨7950473, by rfl⟩ : syracuseStep 10600631 = 15900947) B15900947
theorem B2482427 : Blo 1653526 2482427 := bstep (se 1 (by rfl) ⟨1861820, by rfl⟩ : syracuseStep 2482427 = 3723641) B3723641
theorem B41935315 : Blo 1653526 41935315 := bstep (se 1 (by rfl) ⟨31451486, by rfl⟩ : syracuseStep 41935315 = 62902973) B62902973
theorem B8372969 : Blo 1653526 8372969 := bstep (se 2 (by rfl) ⟨3139863, by rfl⟩ : syracuseStep 8372969 = 6279727) B6279727
theorem B1860763 : Blo 1653526 1860763 := bstep (se 1 (by rfl) ⟨1395572, by rfl⟩ : syracuseStep 1860763 = 2791145) B2791145
theorem B4302415 : Blo 1653526 4302415 := bstep (se 1 (by rfl) ⟨3226811, by rfl⟩ : syracuseStep 4302415 = 6453623) B6453623
theorem B19113577 : Blo 1653526 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B4188287 : Blo 1653526 4188287 := bstep (se 1 (by rfl) ⟨3141215, by rfl⟩ : syracuseStep 4188287 = 6282431) B6282431
theorem B11634833 : Blo 1653526 11634833 := bstep (se 2 (by rfl) ⟨4363062, by rfl⟩ : syracuseStep 11634833 = 8726125) B8726125
theorem B14133487 : Blo 1653526 14133487 := bstep (se 1 (by rfl) ⟨10600115, by rfl⟩ : syracuseStep 14133487 = 21200231) B21200231
theorem B183683335 : Blo 1653526 183683335 := bstep (se 1 (by rfl) ⟨137762501, by rfl⟩ : syracuseStep 183683335 = 275525003) B275525003
theorem B3721643 : Blo 1653526 3721643 := bstep (se 1 (by rfl) ⟨2791232, by rfl⟩ : syracuseStep 3721643 = 5582465) B5582465
theorem B17878315 : Blo 1653526 17878315 := bstep (se 1 (by rfl) ⟨13408736, by rfl⟩ : syracuseStep 17878315 = 26817473) B26817473
theorem B4189715 : Blo 1653526 4189715 := bstep (se 1 (by rfl) ⟨3142286, by rfl⟩ : syracuseStep 4189715 = 6284573) B6284573
theorem B3723119 : Blo 1653526 3723119 := bstep (se 1 (by rfl) ⟨2792339, by rfl⟩ : syracuseStep 3723119 = 5584679) B5584679
theorem B76386341 : Blo 1653526 76386341 := bstep (se 4 (by rfl) ⟨7161219, by rfl⟩ : syracuseStep 76386341 = 14322439) B14322439
theorem B15904943 : Blo 1653526 15904943 := bstep (se 1 (by rfl) ⟨11928707, by rfl⟩ : syracuseStep 15904943 = 23857415) B23857415
theorem B1765999 : Blo 1653526 1765999 := bstep (se 1 (by rfl) ⟨1324499, by rfl⟩ : syracuseStep 1765999 = 2648999) B2648999
theorem B3723983 : Blo 1653526 3723983 := bstep (se 1 (by rfl) ⟨2792987, by rfl⟩ : syracuseStep 3723983 = 5585975) B5585975
theorem B551113955 : Blo 1653526 551113955 := bstep (se 1 (by rfl) ⟨413335466, by rfl⟩ : syracuseStep 551113955 = 826670933) B826670933
theorem B8943311 : Blo 1653526 8943311 := bstep (se 1 (by rfl) ⟨6707483, by rfl⟩ : syracuseStep 8943311 = 13414967) B13414967
theorem B2480591 : Blo 1653526 2480591 := bstep (se 1 (by rfl) ⟨1860443, by rfl⟩ : syracuseStep 2480591 = 3720887) B3720887
theorem B1653759 : Blo 1653526 1653759 := bstep (se 1 (by rfl) ⟨1240319, by rfl⟩ : syracuseStep 1653759 = 2480639) B2480639
theorem B1653791 : Blo 1653526 1653791 := bstep (se 1 (by rfl) ⟨1240343, by rfl⟩ : syracuseStep 1653791 = 2480687) B2480687
theorem B2792623 : Blo 1653526 2792623 := bstep (se 1 (by rfl) ⟨2094467, by rfl⟩ : syracuseStep 2792623 = 4188935) B4188935
theorem B4709659 : Blo 1653526 4709659 := bstep (se 1 (by rfl) ⟨3532244, by rfl⟩ : syracuseStep 4709659 = 7064489) B7064489
theorem B8371511 : Blo 1653526 8371511 := bstep (se 1 (by rfl) ⟨6278633, by rfl⟩ : syracuseStep 8371511 = 12557267) B12557267
theorem B88366409 : Blo 1653526 88366409 := bstep (se 2 (by rfl) ⟨33137403, by rfl⟩ : syracuseStep 88366409 = 66274807) B66274807
theorem B2481791 : Blo 1653526 2481791 := bstep (se 1 (by rfl) ⟨1861343, by rfl⟩ : syracuseStep 2481791 = 3722687) B3722687
theorem B2481983 : Blo 1653526 2481983 := bstep (se 1 (by rfl) ⟨1861487, by rfl⟩ : syracuseStep 2481983 = 3722975) B3722975
theorem B1654875 : Blo 1653526 1654875 := bstep (se 1 (by rfl) ⟨1241156, by rfl⟩ : syracuseStep 1654875 = 2482313) B2482313
theorem B1654951 : Blo 1653526 1654951 := bstep (se 1 (by rfl) ⟨1241213, by rfl⟩ : syracuseStep 1654951 = 2482427) B2482427
theorem B2482655 : Blo 1653526 2482655 := bstep (se 1 (by rfl) ⟨1861991, by rfl⟩ : syracuseStep 2482655 = 3723983) B3723983
theorem B5736553 : Blo 1653526 5736553 := bstep (se 2 (by rfl) ⟨2151207, by rfl⟩ : syracuseStep 5736553 = 4302415) B4302415
theorem B5581007 : Blo 1653526 5581007 := bstep (se 1 (by rfl) ⟨4185755, by rfl⟩ : syracuseStep 5581007 = 8371511) B8371511
theorem B58910939 : Blo 1653526 58910939 := bstep (se 1 (by rfl) ⟨44183204, by rfl⟩ : syracuseStep 58910939 = 88366409) B88366409
theorem B50924227 : Blo 1653526 50924227 := bstep (se 1 (by rfl) ⟨38193170, by rfl⟩ : syracuseStep 50924227 = 76386341) B76386341
theorem B85977839 : Blo 1653526 85977839 := bstep (se 1 (by rfl) ⟨64483379, by rfl⟩ : syracuseStep 85977839 = 128966759) B128966759
theorem B10603295 : Blo 1653526 10603295 := bstep (se 1 (by rfl) ⟨7952471, by rfl⟩ : syracuseStep 10603295 = 15904943) B15904943
theorem B18844649 : Blo 1653526 18844649 := bstep (se 2 (by rfl) ⟨7066743, by rfl⟩ : syracuseStep 18844649 = 14133487) B14133487
theorem B244911113 : Blo 1653526 244911113 := bstep (se 2 (by rfl) ⟨91841667, by rfl⟩ : syracuseStep 244911113 = 183683335) B183683335
theorem B5581979 : Blo 1653526 5581979 := bstep (se 1 (by rfl) ⟨4186484, by rfl⟩ : syracuseStep 5581979 = 8372969) B8372969
theorem B55913753 : Blo 1653526 55913753 := bstep (se 2 (by rfl) ⟨20967657, by rfl⟩ : syracuseStep 55913753 = 41935315) B41935315
theorem B2354665 : Blo 1653526 2354665 := bstep (se 2 (by rfl) ⟨882999, by rfl⟩ : syracuseStep 2354665 = 1765999) B1765999
theorem B3723497 : Blo 1653526 3723497 := bstep (se 2 (by rfl) ⟨1396311, by rfl⟩ : syracuseStep 3723497 = 2792623) B2792623
theorem B6279545 : Blo 1653526 6279545 := bstep (se 2 (by rfl) ⟨2354829, by rfl⟩ : syracuseStep 6279545 = 4709659) B4709659
theorem B7067087 : Blo 1653526 7067087 := bstep (se 1 (by rfl) ⟨5300315, by rfl⟩ : syracuseStep 7067087 = 10600631) B10600631
theorem B101939077 : Blo 1653526 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B367409303 : Blo 1653526 367409303 := bstep (se 1 (by rfl) ⟨275556977, by rfl⟩ : syracuseStep 367409303 = 551113955) B551113955
theorem B5962207 : Blo 1653526 5962207 := bstep (se 1 (by rfl) ⟨4471655, by rfl⟩ : syracuseStep 5962207 = 8943311) B8943311
theorem B2792191 : Blo 1653526 2792191 := bstep (se 1 (by rfl) ⟨2094143, by rfl⟩ : syracuseStep 2792191 = 4188287) B4188287
theorem B7756555 : Blo 1653526 7756555 := bstep (se 1 (by rfl) ⟨5817416, by rfl⟩ : syracuseStep 7756555 = 11634833) B11634833
theorem B2481017 : Blo 1653526 2481017 := bstep (se 2 (by rfl) ⟨930381, by rfl⟩ : syracuseStep 2481017 = 1860763) B1860763
theorem B2481095 : Blo 1653526 2481095 := bstep (se 1 (by rfl) ⟨1860821, by rfl⟩ : syracuseStep 2481095 = 3721643) B3721643
theorem B1653727 : Blo 1653526 1653727 := bstep (se 1 (by rfl) ⟨1240295, by rfl⟩ : syracuseStep 1653727 = 2480591) B2480591
theorem B23837753 : Blo 1653526 23837753 := bstep (se 2 (by rfl) ⟨8939157, by rfl⟩ : syracuseStep 23837753 = 17878315) B17878315
theorem B2793143 : Blo 1653526 2793143 := bstep (se 1 (by rfl) ⟨2094857, by rfl⟩ : syracuseStep 2793143 = 4189715) B4189715
theorem B1654527 : Blo 1653526 1654527 := bstep (se 1 (by rfl) ⟨1240895, by rfl⟩ : syracuseStep 1654527 = 2481791) B2481791
theorem B1654655 : Blo 1653526 1654655 := bstep (se 1 (by rfl) ⟨1240991, by rfl⟩ : syracuseStep 1654655 = 2481983) B2481983
theorem B2482079 : Blo 1653526 2482079 := bstep (se 1 (by rfl) ⟨1861559, by rfl⟩ : syracuseStep 2482079 = 3723119) B3723119
theorem B2482331 : Blo 1653526 2482331 := bstep (se 1 (by rfl) ⟨1861748, by rfl⟩ : syracuseStep 2482331 = 3723497) B3723497
theorem B4186363 : Blo 1653526 4186363 := bstep (se 1 (by rfl) ⟨3139772, by rfl⟩ : syracuseStep 4186363 = 6279545) B6279545
theorem B1655103 : Blo 1653526 1655103 := bstep (se 1 (by rfl) ⟨1241327, by rfl⟩ : syracuseStep 1655103 = 2482655) B2482655
theorem B149103341 : Blo 1653526 149103341 := bstep (se 3 (by rfl) ⟨27956876, by rfl⟩ : syracuseStep 149103341 = 55913753) B55913753
theorem B4711391 : Blo 1653526 4711391 := bstep (se 1 (by rfl) ⟨3533543, by rfl⟩ : syracuseStep 4711391 = 7067087) B7067087
theorem B3720671 : Blo 1653526 3720671 := bstep (se 1 (by rfl) ⟨2790503, by rfl⟩ : syracuseStep 3720671 = 5581007) B5581007
theorem B39273959 : Blo 1653526 39273959 := bstep (se 1 (by rfl) ⟨29455469, by rfl⟩ : syracuseStep 39273959 = 58910939) B58910939
theorem B3139553 : Blo 1653526 3139553 := bstep (se 2 (by rfl) ⟨1177332, by rfl⟩ : syracuseStep 3139553 = 2354665) B2354665
theorem B3721319 : Blo 1653526 3721319 := bstep (se 1 (by rfl) ⟨2790989, by rfl⟩ : syracuseStep 3721319 = 5581979) B5581979
theorem B1862095 : Blo 1653526 1862095 := bstep (se 1 (by rfl) ⟨1396571, by rfl⟩ : syracuseStep 1862095 = 2793143) B2793143
theorem B7949609 : Blo 1653526 7949609 := bstep (se 2 (by rfl) ⟨2981103, by rfl⟩ : syracuseStep 7949609 = 5962207) B5962207
theorem B67898969 : Blo 1653526 67898969 := bstep (se 2 (by rfl) ⟨25462113, by rfl⟩ : syracuseStep 67898969 = 50924227) B50924227
theorem B3722921 : Blo 1653526 3722921 := bstep (se 2 (by rfl) ⟨1396095, by rfl⟩ : syracuseStep 3722921 = 2792191) B2792191
theorem B10342073 : Blo 1653526 10342073 := bstep (se 2 (by rfl) ⟨3878277, by rfl⟩ : syracuseStep 10342073 = 7756555) B7756555
theorem B12563099 : Blo 1653526 12563099 := bstep (se 1 (by rfl) ⟨9422324, by rfl⟩ : syracuseStep 12563099 = 18844649) B18844649
theorem B135918769 : Blo 1653526 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B244939535 : Blo 1653526 244939535 := bstep (se 1 (by rfl) ⟨183704651, by rfl⟩ : syracuseStep 244939535 = 367409303) B367409303
theorem B57318559 : Blo 1653526 57318559 := bstep (se 1 (by rfl) ⟨42988919, by rfl⟩ : syracuseStep 57318559 = 85977839) B85977839
theorem B7068863 : Blo 1653526 7068863 := bstep (se 1 (by rfl) ⟨5301647, by rfl⟩ : syracuseStep 7068863 = 10603295) B10603295
theorem B1654011 : Blo 1653526 1654011 := bstep (se 1 (by rfl) ⟨1240508, by rfl⟩ : syracuseStep 1654011 = 2481017) B2481017
theorem B1654063 : Blo 1653526 1654063 := bstep (se 1 (by rfl) ⟨1240547, by rfl⟩ : syracuseStep 1654063 = 2481095) B2481095
theorem B163274075 : Blo 1653526 163274075 := bstep (se 1 (by rfl) ⟨122455556, by rfl⟩ : syracuseStep 163274075 = 244911113) B244911113
theorem B15891835 : Blo 1653526 15891835 := bstep (se 1 (by rfl) ⟨11918876, by rfl⟩ : syracuseStep 15891835 = 23837753) B23837753
theorem B122379797 : Blo 1653526 122379797 := bstep (se 6 (by rfl) ⟨2868276, by rfl⟩ : syracuseStep 122379797 = 5736553) B5736553
theorem B1654719 : Blo 1653526 1654719 := bstep (se 1 (by rfl) ⟨1241039, by rfl⟩ : syracuseStep 1654719 = 2482079) B2482079
theorem B1654887 : Blo 1653526 1654887 := bstep (se 1 (by rfl) ⟨1241165, by rfl⟩ : syracuseStep 1654887 = 2482331) B2482331
theorem B99402227 : Blo 1653526 99402227 := bstep (se 1 (by rfl) ⟨74551670, by rfl⟩ : syracuseStep 99402227 = 149103341) B149103341
theorem B2482793 : Blo 1653526 2482793 := bstep (se 2 (by rfl) ⟨931047, by rfl⟩ : syracuseStep 2482793 = 1862095) B1862095
theorem B26182639 : Blo 1653526 26182639 := bstep (se 1 (by rfl) ⟨19636979, by rfl⟩ : syracuseStep 26182639 = 39273959) B39273959
theorem B181225025 : Blo 1653526 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B163293023 : Blo 1653526 163293023 := bstep (se 1 (by rfl) ⟨122469767, by rfl⟩ : syracuseStep 163293023 = 244939535) B244939535
theorem B4712575 : Blo 1653526 4712575 := bstep (se 1 (by rfl) ⟨3534431, by rfl⟩ : syracuseStep 4712575 = 7068863) B7068863
theorem B108849383 : Blo 1653526 108849383 := bstep (se 1 (by rfl) ⟨81637037, by rfl⟩ : syracuseStep 108849383 = 163274075) B163274075
theorem B81586531 : Blo 1653526 81586531 := bstep (se 1 (by rfl) ⟨61189898, by rfl⟩ : syracuseStep 81586531 = 122379797) B122379797
theorem B5581817 : Blo 1653526 5581817 := bstep (se 2 (by rfl) ⟨2093181, by rfl⟩ : syracuseStep 5581817 = 4186363) B4186363
theorem B8375399 : Blo 1653526 8375399 := bstep (se 1 (by rfl) ⟨6281549, by rfl⟩ : syracuseStep 8375399 = 12563099) B12563099
theorem B3140927 : Blo 1653526 3140927 := bstep (se 1 (by rfl) ⟨2355695, by rfl⟩ : syracuseStep 3140927 = 4711391) B4711391
theorem B2093035 : Blo 1653526 2093035 := bstep (se 1 (by rfl) ⟨1569776, by rfl⟩ : syracuseStep 2093035 = 3139553) B3139553
theorem B21189113 : Blo 1653526 21189113 := bstep (se 2 (by rfl) ⟨7945917, by rfl⟩ : syracuseStep 21189113 = 15891835) B15891835
theorem B45265979 : Blo 1653526 45265979 := bstep (se 1 (by rfl) ⟨33949484, by rfl⟩ : syracuseStep 45265979 = 67898969) B67898969
theorem B6894715 : Blo 1653526 6894715 := bstep (se 1 (by rfl) ⟨5171036, by rfl⟩ : syracuseStep 6894715 = 10342073) B10342073
theorem B305698981 : Blo 1653526 305698981 := bstep (se 4 (by rfl) ⟨28659279, by rfl⟩ : syracuseStep 305698981 = 57318559) B57318559
theorem B2480447 : Blo 1653526 2480447 := bstep (se 1 (by rfl) ⟨1860335, by rfl⟩ : syracuseStep 2480447 = 3720671) B3720671
theorem B2480879 : Blo 1653526 2480879 := bstep (se 1 (by rfl) ⟨1860659, by rfl⟩ : syracuseStep 2480879 = 3721319) B3721319
theorem B5299739 : Blo 1653526 5299739 := bstep (se 1 (by rfl) ⟨3974804, by rfl⟩ : syracuseStep 5299739 = 7949609) B7949609
theorem B2481947 : Blo 1653526 2481947 := bstep (se 1 (by rfl) ⟨1861460, by rfl⟩ : syracuseStep 2481947 = 3722921) B3722921
theorem B6283433 : Blo 1653526 6283433 := bstep (se 2 (by rfl) ⟨2356287, by rfl⟩ : syracuseStep 6283433 = 4712575) B4712575
theorem B1655195 : Blo 1653526 1655195 := bstep (se 1 (by rfl) ⟨1241396, by rfl⟩ : syracuseStep 1655195 = 2482793) B2482793
theorem B108782041 : Blo 1653526 108782041 := bstep (se 2 (by rfl) ⟨40793265, by rfl⟩ : syracuseStep 108782041 = 81586531) B81586531
theorem B120816683 : Blo 1653526 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B72566255 : Blo 1653526 72566255 := bstep (se 1 (by rfl) ⟨54424691, by rfl⟩ : syracuseStep 72566255 = 108849383) B108849383
theorem B9192953 : Blo 1653526 9192953 := bstep (se 2 (by rfl) ⟨3447357, by rfl⟩ : syracuseStep 9192953 = 6894715) B6894715
theorem B3721211 : Blo 1653526 3721211 := bstep (se 1 (by rfl) ⟨2790908, by rfl⟩ : syracuseStep 3721211 = 5581817) B5581817
theorem B3533159 : Blo 1653526 3533159 := bstep (se 1 (by rfl) ⟨2649869, by rfl⟩ : syracuseStep 3533159 = 5299739) B5299739
theorem B66268151 : Blo 1653526 66268151 := bstep (se 1 (by rfl) ⟨49701113, by rfl⟩ : syracuseStep 66268151 = 99402227) B99402227
theorem B14126075 : Blo 1653526 14126075 := bstep (se 1 (by rfl) ⟨10594556, by rfl⟩ : syracuseStep 14126075 = 21189113) B21189113
theorem B34910185 : Blo 1653526 34910185 := bstep (se 2 (by rfl) ⟨13091319, by rfl⟩ : syracuseStep 34910185 = 26182639) B26182639
theorem B5583599 : Blo 1653526 5583599 := bstep (se 1 (by rfl) ⟨4187699, by rfl⟩ : syracuseStep 5583599 = 8375399) B8375399
theorem B2093951 : Blo 1653526 2093951 := bstep (se 1 (by rfl) ⟨1570463, by rfl⟩ : syracuseStep 2093951 = 3140927) B3140927
theorem B2790713 : Blo 1653526 2790713 := bstep (se 2 (by rfl) ⟨1046517, by rfl⟩ : syracuseStep 2790713 = 2093035) B2093035
theorem B407598641 : Blo 1653526 407598641 := bstep (se 2 (by rfl) ⟨152849490, by rfl⟩ : syracuseStep 407598641 = 305698981) B305698981
theorem B30177319 : Blo 1653526 30177319 := bstep (se 1 (by rfl) ⟨22632989, by rfl⟩ : syracuseStep 30177319 = 45265979) B45265979
theorem B108862015 : Blo 1653526 108862015 := bstep (se 1 (by rfl) ⟨81646511, by rfl⟩ : syracuseStep 108862015 = 163293023) B163293023
theorem B1653631 : Blo 1653526 1653631 := bstep (se 1 (by rfl) ⟨1240223, by rfl⟩ : syracuseStep 1653631 = 2480447) B2480447
theorem B1653919 : Blo 1653526 1653919 := bstep (se 1 (by rfl) ⟨1240439, by rfl⟩ : syracuseStep 1653919 = 2480879) B2480879
theorem B1654631 : Blo 1653526 1654631 := bstep (se 1 (by rfl) ⟨1240973, by rfl⟩ : syracuseStep 1654631 = 2481947) B2481947
theorem B80544455 : Blo 1653526 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B1860475 : Blo 1653526 1860475 := bstep (se 1 (by rfl) ⟨1395356, by rfl⟩ : syracuseStep 1860475 = 2790713) B2790713
theorem B9421757 : Blo 1653526 9421757 := bstep (se 3 (by rfl) ⟨1766579, by rfl⟩ : syracuseStep 9421757 = 3533159) B3533159
theorem B6128635 : Blo 1653526 6128635 := bstep (se 1 (by rfl) ⟨4596476, by rfl⟩ : syracuseStep 6128635 = 9192953) B9192953
theorem B4188955 : Blo 1653526 4188955 := bstep (se 1 (by rfl) ⟨3141716, by rfl⟩ : syracuseStep 4188955 = 6283433) B6283433
theorem B3722399 : Blo 1653526 3722399 := bstep (se 1 (by rfl) ⟨2791799, by rfl⟩ : syracuseStep 3722399 = 5583599) B5583599
theorem B145042721 : Blo 1653526 145042721 := bstep (se 2 (by rfl) ⟨54391020, by rfl⟩ : syracuseStep 145042721 = 108782041) B108782041
theorem B145149353 : Blo 1653526 145149353 := bstep (se 2 (by rfl) ⟨54431007, by rfl⟩ : syracuseStep 145149353 = 108862015) B108862015
theorem B48377503 : Blo 1653526 48377503 := bstep (se 1 (by rfl) ⟨36283127, by rfl⟩ : syracuseStep 48377503 = 72566255) B72566255
theorem B271732427 : Blo 1653526 271732427 := bstep (se 1 (by rfl) ⟨203799320, by rfl⟩ : syracuseStep 271732427 = 407598641) B407598641
theorem B9417383 : Blo 1653526 9417383 := bstep (se 1 (by rfl) ⟨7063037, by rfl⟩ : syracuseStep 9417383 = 14126075) B14126075
theorem B5583869 : Blo 1653526 5583869 := bstep (se 3 (by rfl) ⟨1046975, by rfl⟩ : syracuseStep 5583869 = 2093951) B2093951
theorem B40236425 : Blo 1653526 40236425 := bstep (se 2 (by rfl) ⟨15088659, by rfl⟩ : syracuseStep 40236425 = 30177319) B30177319
theorem B2480807 : Blo 1653526 2480807 := bstep (se 1 (by rfl) ⟨1860605, by rfl⟩ : syracuseStep 2480807 = 3721211) B3721211
theorem B44178767 : Blo 1653526 44178767 := bstep (se 1 (by rfl) ⟨33134075, by rfl⟩ : syracuseStep 44178767 = 66268151) B66268151
theorem B46546913 : Blo 1653526 46546913 := bstep (se 2 (by rfl) ⟨17455092, by rfl⟩ : syracuseStep 46546913 = 34910185) B34910185
theorem B29452511 : Blo 1653526 29452511 := bstep (se 1 (by rfl) ⟨22089383, by rfl⟩ : syracuseStep 29452511 = 44178767) B44178767
theorem B96766235 : Blo 1653526 96766235 := bstep (se 1 (by rfl) ⟨72574676, by rfl⟩ : syracuseStep 96766235 = 145149353) B145149353
theorem B6278255 : Blo 1653526 6278255 := bstep (se 1 (by rfl) ⟨4708691, by rfl⟩ : syracuseStep 6278255 = 9417383) B9417383
theorem B3722579 : Blo 1653526 3722579 := bstep (se 1 (by rfl) ⟨2791934, by rfl⟩ : syracuseStep 3722579 = 5583869) B5583869
theorem B26824283 : Blo 1653526 26824283 := bstep (se 1 (by rfl) ⟨20118212, by rfl⟩ : syracuseStep 26824283 = 40236425) B40236425
theorem B8171513 : Blo 1653526 8171513 := bstep (se 2 (by rfl) ⟨3064317, by rfl⟩ : syracuseStep 8171513 = 6128635) B6128635
theorem B96695147 : Blo 1653526 96695147 := bstep (se 1 (by rfl) ⟨72521360, by rfl⟩ : syracuseStep 96695147 = 145042721) B145042721
theorem B181154951 : Blo 1653526 181154951 := bstep (se 1 (by rfl) ⟨135866213, by rfl⟩ : syracuseStep 181154951 = 271732427) B271732427
theorem B53696303 : Blo 1653526 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B6281171 : Blo 1653526 6281171 := bstep (se 1 (by rfl) ⟨4710878, by rfl⟩ : syracuseStep 6281171 = 9421757) B9421757
theorem B5585273 : Blo 1653526 5585273 := bstep (se 2 (by rfl) ⟨2094477, by rfl⟩ : syracuseStep 5585273 = 4188955) B4188955
theorem B2480633 : Blo 1653526 2480633 := bstep (se 2 (by rfl) ⟨930237, by rfl⟩ : syracuseStep 2480633 = 1860475) B1860475
theorem B1653871 : Blo 1653526 1653871 := bstep (se 1 (by rfl) ⟨1240403, by rfl⟩ : syracuseStep 1653871 = 2480807) B2480807
theorem B2481599 : Blo 1653526 2481599 := bstep (se 1 (by rfl) ⟨1861199, by rfl⟩ : syracuseStep 2481599 = 3722399) B3722399
theorem B64503337 : Blo 1653526 64503337 := bstep (se 2 (by rfl) ⟨24188751, by rfl⟩ : syracuseStep 64503337 = 48377503) B48377503
theorem B31031275 : Blo 1653526 31031275 := bstep (se 1 (by rfl) ⟨23273456, by rfl⟩ : syracuseStep 31031275 = 46546913) B46546913
theorem B4187447 : Blo 1653526 4187447 := bstep (se 1 (by rfl) ⟨3140585, by rfl⟩ : syracuseStep 4187447 = 6281171) B6281171
theorem B257853725 : Blo 1653526 257853725 := bstep (se 3 (by rfl) ⟨48347573, by rfl⟩ : syracuseStep 257853725 = 96695147) B96695147
theorem B120769967 : Blo 1653526 120769967 := bstep (se 1 (by rfl) ⟨90577475, by rfl⟩ : syracuseStep 120769967 = 181154951) B181154951
theorem B3723515 : Blo 1653526 3723515 := bstep (se 1 (by rfl) ⟨2792636, by rfl⟩ : syracuseStep 3723515 = 5585273) B5585273
theorem B86004449 : Blo 1653526 86004449 := bstep (se 2 (by rfl) ⟨32251668, by rfl⟩ : syracuseStep 86004449 = 64503337) B64503337
theorem B41375033 : Blo 1653526 41375033 := bstep (se 2 (by rfl) ⟨15515637, by rfl⟩ : syracuseStep 41375033 = 31031275) B31031275
theorem B5447675 : Blo 1653526 5447675 := bstep (se 1 (by rfl) ⟨4085756, by rfl⟩ : syracuseStep 5447675 = 8171513) B8171513
theorem B35797535 : Blo 1653526 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B19635007 : Blo 1653526 19635007 := bstep (se 1 (by rfl) ⟨14726255, by rfl⟩ : syracuseStep 19635007 = 29452511) B29452511
theorem B64510823 : Blo 1653526 64510823 := bstep (se 1 (by rfl) ⟨48383117, by rfl⟩ : syracuseStep 64510823 = 96766235) B96766235
theorem B1653755 : Blo 1653526 1653755 := bstep (se 1 (by rfl) ⟨1240316, by rfl⟩ : syracuseStep 1653755 = 2480633) B2480633
theorem B4185503 : Blo 1653526 4185503 := bstep (se 1 (by rfl) ⟨3139127, by rfl⟩ : syracuseStep 4185503 = 6278255) B6278255
theorem B2481719 : Blo 1653526 2481719 := bstep (se 1 (by rfl) ⟨1861289, by rfl⟩ : syracuseStep 2481719 = 3722579) B3722579
theorem B1654399 : Blo 1653526 1654399 := bstep (se 1 (by rfl) ⟨1240799, by rfl⟩ : syracuseStep 1654399 = 2481599) B2481599
theorem B17882855 : Blo 1653526 17882855 := bstep (se 1 (by rfl) ⟨13412141, by rfl⟩ : syracuseStep 17882855 = 26824283) B26824283
theorem B2482343 : Blo 1653526 2482343 := bstep (se 1 (by rfl) ⟨1861757, by rfl⟩ : syracuseStep 2482343 = 3723515) B3723515
theorem B57336299 : Blo 1653526 57336299 := bstep (se 1 (by rfl) ⟨43002224, by rfl⟩ : syracuseStep 57336299 = 86004449) B86004449
theorem B27583355 : Blo 1653526 27583355 := bstep (se 1 (by rfl) ⟨20687516, by rfl⟩ : syracuseStep 27583355 = 41375033) B41375033
theorem B322053245 : Blo 1653526 322053245 := bstep (se 3 (by rfl) ⟨60384983, by rfl⟩ : syracuseStep 322053245 = 120769967) B120769967
theorem B171902483 : Blo 1653526 171902483 := bstep (se 1 (by rfl) ⟨128926862, by rfl⟩ : syracuseStep 171902483 = 257853725) B257853725
theorem B23865023 : Blo 1653526 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B11921903 : Blo 1653526 11921903 := bstep (se 1 (by rfl) ⟨8941427, by rfl⟩ : syracuseStep 11921903 = 17882855) B17882855
theorem B14527133 : Blo 1653526 14527133 := bstep (se 3 (by rfl) ⟨2723837, by rfl⟩ : syracuseStep 14527133 = 5447675) B5447675
theorem B2790335 : Blo 1653526 2790335 := bstep (se 1 (by rfl) ⟨2092751, by rfl⟩ : syracuseStep 2790335 = 4185503) B4185503
theorem B2791631 : Blo 1653526 2791631 := bstep (se 1 (by rfl) ⟨2093723, by rfl⟩ : syracuseStep 2791631 = 4187447) B4187447
theorem B26180009 : Blo 1653526 26180009 := bstep (se 2 (by rfl) ⟨9817503, by rfl⟩ : syracuseStep 26180009 = 19635007) B19635007
theorem B43007215 : Blo 1653526 43007215 := bstep (se 1 (by rfl) ⟨32255411, by rfl⟩ : syracuseStep 43007215 = 64510823) B64510823
theorem B1654479 : Blo 1653526 1654479 := bstep (se 1 (by rfl) ⟨1240859, by rfl⟩ : syracuseStep 1654479 = 2481719) B2481719
theorem B1654895 : Blo 1653526 1654895 := bstep (se 1 (by rfl) ⟨1241171, by rfl⟩ : syracuseStep 1654895 = 2482343) B2482343
theorem B38224199 : Blo 1653526 38224199 := bstep (se 1 (by rfl) ⟨28668149, by rfl⟩ : syracuseStep 38224199 = 57336299) B57336299
theorem B1860223 : Blo 1653526 1860223 := bstep (se 1 (by rfl) ⟨1395167, by rfl⟩ : syracuseStep 1860223 = 2790335) B2790335
theorem B15910015 : Blo 1653526 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B1861087 : Blo 1653526 1861087 := bstep (se 1 (by rfl) ⟨1395815, by rfl⟩ : syracuseStep 1861087 = 2791631) B2791631
theorem B7947935 : Blo 1653526 7947935 := bstep (se 1 (by rfl) ⟨5960951, by rfl⟩ : syracuseStep 7947935 = 11921903) B11921903
theorem B9684755 : Blo 1653526 9684755 := bstep (se 1 (by rfl) ⟨7263566, by rfl⟩ : syracuseStep 9684755 = 14527133) B14527133
theorem B114601655 : Blo 1653526 114601655 := bstep (se 1 (by rfl) ⟨85951241, by rfl⟩ : syracuseStep 114601655 = 171902483) B171902483
theorem B17453339 : Blo 1653526 17453339 := bstep (se 1 (by rfl) ⟨13090004, by rfl⟩ : syracuseStep 17453339 = 26180009) B26180009
theorem B214702163 : Blo 1653526 214702163 := bstep (se 1 (by rfl) ⟨161026622, by rfl⟩ : syracuseStep 214702163 = 322053245) B322053245
theorem B57342953 : Blo 1653526 57342953 := bstep (se 2 (by rfl) ⟨21503607, by rfl⟩ : syracuseStep 57342953 = 43007215) B43007215
theorem B73555613 : Blo 1653526 73555613 := bstep (se 3 (by rfl) ⟨13791677, by rfl⟩ : syracuseStep 73555613 = 27583355) B27583355
theorem B6456503 : Blo 1653526 6456503 := bstep (se 1 (by rfl) ⟨4842377, by rfl⟩ : syracuseStep 6456503 = 9684755) B9684755
theorem B76401103 : Blo 1653526 76401103 := bstep (se 1 (by rfl) ⟨57300827, by rfl⟩ : syracuseStep 76401103 = 114601655) B114601655
theorem B11635559 : Blo 1653526 11635559 := bstep (se 1 (by rfl) ⟨8726669, by rfl⟩ : syracuseStep 11635559 = 17453339) B17453339
theorem B143134775 : Blo 1653526 143134775 := bstep (se 1 (by rfl) ⟨107351081, by rfl⟩ : syracuseStep 143134775 = 214702163) B214702163
theorem B21213353 : Blo 1653526 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B38228635 : Blo 1653526 38228635 := bstep (se 1 (by rfl) ⟨28671476, by rfl⟩ : syracuseStep 38228635 = 57342953) B57342953
theorem B25482799 : Blo 1653526 25482799 := bstep (se 1 (by rfl) ⟨19112099, by rfl⟩ : syracuseStep 25482799 = 38224199) B38224199
theorem B2480297 : Blo 1653526 2480297 := bstep (se 2 (by rfl) ⟨930111, by rfl⟩ : syracuseStep 2480297 = 1860223) B1860223
theorem B5298623 : Blo 1653526 5298623 := bstep (se 1 (by rfl) ⟨3973967, by rfl⟩ : syracuseStep 5298623 = 7947935) B7947935
theorem B2481449 : Blo 1653526 2481449 := bstep (se 2 (by rfl) ⟨930543, by rfl⟩ : syracuseStep 2481449 = 1861087) B1861087
theorem B49037075 : Blo 1653526 49037075 := bstep (se 1 (by rfl) ⟨36777806, by rfl⟩ : syracuseStep 49037075 = 73555613) B73555613
theorem B101868137 : Blo 1653526 101868137 := bstep (se 2 (by rfl) ⟨38200551, by rfl⟩ : syracuseStep 101868137 = 76401103) B76401103
theorem B50971513 : Blo 1653526 50971513 := bstep (se 2 (by rfl) ⟨19114317, by rfl⟩ : syracuseStep 50971513 = 38228635) B38228635
theorem B3532415 : Blo 1653526 3532415 := bstep (se 1 (by rfl) ⟨2649311, by rfl⟩ : syracuseStep 3532415 = 5298623) B5298623
theorem B95423183 : Blo 1653526 95423183 := bstep (se 1 (by rfl) ⟨71567387, by rfl⟩ : syracuseStep 95423183 = 143134775) B143134775
theorem B14142235 : Blo 1653526 14142235 := bstep (se 1 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 14142235 = 21213353) B21213353
theorem B4304335 : Blo 1653526 4304335 := bstep (se 1 (by rfl) ⟨3228251, by rfl⟩ : syracuseStep 4304335 = 6456503) B6456503
theorem B33977065 : Blo 1653526 33977065 := bstep (se 2 (by rfl) ⟨12741399, by rfl⟩ : syracuseStep 33977065 = 25482799) B25482799
theorem B32691383 : Blo 1653526 32691383 := bstep (se 1 (by rfl) ⟨24518537, by rfl⟩ : syracuseStep 32691383 = 49037075) B49037075
theorem B1653531 : Blo 1653526 1653531 := bstep (se 1 (by rfl) ⟨1240148, by rfl⟩ : syracuseStep 1653531 = 2480297) B2480297
theorem B7757039 : Blo 1653526 7757039 := bstep (se 1 (by rfl) ⟨5817779, by rfl⟩ : syracuseStep 7757039 = 11635559) B11635559
theorem B1654299 : Blo 1653526 1654299 := bstep (se 1 (by rfl) ⟨1240724, by rfl⟩ : syracuseStep 1654299 = 2481449) B2481449
theorem B67912091 : Blo 1653526 67912091 := bstep (se 1 (by rfl) ⟨50934068, by rfl⟩ : syracuseStep 67912091 = 101868137) B101868137
theorem B45302753 : Blo 1653526 45302753 := bstep (se 2 (by rfl) ⟨16988532, by rfl⟩ : syracuseStep 45302753 = 33977065) B33977065
theorem B67962017 : Blo 1653526 67962017 := bstep (se 2 (by rfl) ⟨25485756, by rfl⟩ : syracuseStep 67962017 = 50971513) B50971513
theorem B5171359 : Blo 1653526 5171359 := bstep (se 1 (by rfl) ⟨3878519, by rfl⟩ : syracuseStep 5171359 = 7757039) B7757039
theorem B21794255 : Blo 1653526 21794255 := bstep (se 1 (by rfl) ⟨16345691, by rfl⟩ : syracuseStep 21794255 = 32691383) B32691383
theorem B63615455 : Blo 1653526 63615455 := bstep (se 1 (by rfl) ⟨47711591, by rfl⟩ : syracuseStep 63615455 = 95423183) B95423183
theorem B5739113 : Blo 1653526 5739113 := bstep (se 2 (by rfl) ⟨2152167, by rfl⟩ : syracuseStep 5739113 = 4304335) B4304335
theorem B18856313 : Blo 1653526 18856313 := bstep (se 2 (by rfl) ⟨7071117, by rfl⟩ : syracuseStep 18856313 = 14142235) B14142235
theorem B9419773 : Blo 1653526 9419773 := bstep (se 3 (by rfl) ⟨1766207, by rfl⟩ : syracuseStep 9419773 = 3532415) B3532415
theorem B42410303 : Blo 1653526 42410303 := bstep (se 1 (by rfl) ⟨31807727, by rfl⟩ : syracuseStep 42410303 = 63615455) B63615455
theorem B3826075 : Blo 1653526 3826075 := bstep (se 1 (by rfl) ⟨2869556, by rfl⟩ : syracuseStep 3826075 = 5739113) B5739113
theorem B12559697 : Blo 1653526 12559697 := bstep (se 2 (by rfl) ⟨4709886, by rfl⟩ : syracuseStep 12559697 = 9419773) B9419773
theorem B12570875 : Blo 1653526 12570875 := bstep (se 1 (by rfl) ⟨9428156, by rfl⟩ : syracuseStep 12570875 = 18856313) B18856313
theorem B14529503 : Blo 1653526 14529503 := bstep (se 1 (by rfl) ⟨10897127, by rfl⟩ : syracuseStep 14529503 = 21794255) B21794255
theorem B6895145 : Blo 1653526 6895145 := bstep (se 2 (by rfl) ⟨2585679, by rfl⟩ : syracuseStep 6895145 = 5171359) B5171359
theorem B45274727 : Blo 1653526 45274727 := bstep (se 1 (by rfl) ⟨33956045, by rfl⟩ : syracuseStep 45274727 = 67912091) B67912091
theorem B30201835 : Blo 1653526 30201835 := bstep (se 1 (by rfl) ⟨22651376, by rfl⟩ : syracuseStep 30201835 = 45302753) B45302753
theorem B45308011 : Blo 1653526 45308011 := bstep (se 1 (by rfl) ⟨33981008, by rfl⟩ : syracuseStep 45308011 = 67962017) B67962017
theorem B8380583 : Blo 1653526 8380583 := bstep (se 1 (by rfl) ⟨6285437, by rfl⟩ : syracuseStep 8380583 = 12570875) B12570875
theorem B8373131 : Blo 1653526 8373131 := bstep (se 1 (by rfl) ⟨6279848, by rfl⟩ : syracuseStep 8373131 = 12559697) B12559697
theorem B4596763 : Blo 1653526 4596763 := bstep (se 1 (by rfl) ⟨3447572, by rfl⟩ : syracuseStep 4596763 = 6895145) B6895145
theorem B60410681 : Blo 1653526 60410681 := bstep (se 2 (by rfl) ⟨22654005, by rfl⟩ : syracuseStep 60410681 = 45308011) B45308011
theorem B28273535 : Blo 1653526 28273535 := bstep (se 1 (by rfl) ⟨21205151, by rfl⟩ : syracuseStep 28273535 = 42410303) B42410303
theorem B38745341 : Blo 1653526 38745341 := bstep (se 3 (by rfl) ⟨7264751, by rfl⟩ : syracuseStep 38745341 = 14529503) B14529503
theorem B40269113 : Blo 1653526 40269113 := bstep (se 2 (by rfl) ⟨15100917, by rfl⟩ : syracuseStep 40269113 = 30201835) B30201835
theorem B5101433 : Blo 1653526 5101433 := bstep (se 2 (by rfl) ⟨1913037, by rfl⟩ : syracuseStep 5101433 = 3826075) B3826075
theorem B120732605 : Blo 1653526 120732605 := bstep (se 3 (by rfl) ⟨22637363, by rfl⟩ : syracuseStep 120732605 = 45274727) B45274727
theorem B5587055 : Blo 1653526 5587055 := bstep (se 1 (by rfl) ⟨4190291, by rfl⟩ : syracuseStep 5587055 = 8380583) B8380583
theorem B25830227 : Blo 1653526 25830227 := bstep (se 1 (by rfl) ⟨19372670, by rfl⟩ : syracuseStep 25830227 = 38745341) B38745341
theorem B26846075 : Blo 1653526 26846075 := bstep (se 1 (by rfl) ⟨20134556, by rfl⟩ : syracuseStep 26846075 = 40269113) B40269113
theorem B3400955 : Blo 1653526 3400955 := bstep (se 1 (by rfl) ⟨2550716, by rfl⟩ : syracuseStep 3400955 = 5101433) B5101433
theorem B6129017 : Blo 1653526 6129017 := bstep (se 2 (by rfl) ⟨2298381, by rfl⟩ : syracuseStep 6129017 = 4596763) B4596763
theorem B40273787 : Blo 1653526 40273787 := bstep (se 1 (by rfl) ⟨30205340, by rfl⟩ : syracuseStep 40273787 = 60410681) B60410681
theorem B80488403 : Blo 1653526 80488403 := bstep (se 1 (by rfl) ⟨60366302, by rfl⟩ : syracuseStep 80488403 = 120732605) B120732605
theorem B5582087 : Blo 1653526 5582087 := bstep (se 1 (by rfl) ⟨4186565, by rfl⟩ : syracuseStep 5582087 = 8373131) B8373131
theorem B18849023 : Blo 1653526 18849023 := bstep (se 1 (by rfl) ⟨14136767, by rfl⟩ : syracuseStep 18849023 = 28273535) B28273535
theorem B17220151 : Blo 1653526 17220151 := bstep (se 1 (by rfl) ⟨12915113, by rfl⟩ : syracuseStep 17220151 = 25830227) B25830227
theorem B53658935 : Blo 1653526 53658935 := bstep (se 1 (by rfl) ⟨40244201, by rfl⟩ : syracuseStep 53658935 = 80488403) B80488403
theorem B3721391 : Blo 1653526 3721391 := bstep (se 1 (by rfl) ⟨2791043, by rfl⟩ : syracuseStep 3721391 = 5582087) B5582087
theorem B26849191 : Blo 1653526 26849191 := bstep (se 1 (by rfl) ⟨20136893, by rfl⟩ : syracuseStep 26849191 = 40273787) B40273787
theorem B3724703 : Blo 1653526 3724703 := bstep (se 1 (by rfl) ⟨2793527, by rfl⟩ : syracuseStep 3724703 = 5587055) B5587055
theorem B17897383 : Blo 1653526 17897383 := bstep (se 1 (by rfl) ⟨13423037, by rfl⟩ : syracuseStep 17897383 = 26846075) B26846075
theorem B2267303 : Blo 1653526 2267303 := bstep (se 1 (by rfl) ⟨1700477, by rfl⟩ : syracuseStep 2267303 = 3400955) B3400955
theorem B4086011 : Blo 1653526 4086011 := bstep (se 1 (by rfl) ⟨3064508, by rfl⟩ : syracuseStep 4086011 = 6129017) B6129017
theorem B12566015 : Blo 1653526 12566015 := bstep (se 1 (by rfl) ⟨9424511, by rfl⟩ : syracuseStep 12566015 = 18849023) B18849023
theorem B10896029 : Blo 1653526 10896029 := bstep (se 3 (by rfl) ⟨2043005, by rfl⟩ : syracuseStep 10896029 = 4086011) B4086011
theorem B2483135 : Blo 1653526 2483135 := bstep (se 1 (by rfl) ⟨1862351, by rfl⟩ : syracuseStep 2483135 = 3724703) B3724703
theorem B24184565 : Blo 1653526 24184565 := bstep (se 5 (by rfl) ⟨1133651, by rfl⟩ : syracuseStep 24184565 = 2267303) B2267303
theorem B8377343 : Blo 1653526 8377343 := bstep (se 1 (by rfl) ⟨6283007, by rfl⟩ : syracuseStep 8377343 = 12566015) B12566015
theorem B22960201 : Blo 1653526 22960201 := bstep (se 2 (by rfl) ⟨8610075, by rfl⟩ : syracuseStep 22960201 = 17220151) B17220151
theorem B35772623 : Blo 1653526 35772623 := bstep (se 1 (by rfl) ⟨26829467, by rfl⟩ : syracuseStep 35772623 = 53658935) B53658935
theorem B2480927 : Blo 1653526 2480927 := bstep (se 1 (by rfl) ⟨1860695, by rfl⟩ : syracuseStep 2480927 = 3721391) B3721391
theorem B23863177 : Blo 1653526 23863177 := bstep (se 2 (by rfl) ⟨8948691, by rfl⟩ : syracuseStep 23863177 = 17897383) B17897383
theorem B35798921 : Blo 1653526 35798921 := bstep (se 2 (by rfl) ⟨13424595, by rfl⟩ : syracuseStep 35798921 = 26849191) B26849191
theorem B30613601 : Blo 1653526 30613601 := bstep (se 2 (by rfl) ⟨11480100, by rfl⟩ : syracuseStep 30613601 = 22960201) B22960201
theorem B1655423 : Blo 1653526 1655423 := bstep (se 1 (by rfl) ⟨1241567, by rfl⟩ : syracuseStep 1655423 = 2483135) B2483135
theorem B16123043 : Blo 1653526 16123043 := bstep (se 1 (by rfl) ⟨12092282, by rfl⟩ : syracuseStep 16123043 = 24184565) B24184565
theorem B23848415 : Blo 1653526 23848415 := bstep (se 1 (by rfl) ⟨17886311, by rfl⟩ : syracuseStep 23848415 = 35772623) B35772623
theorem B23865947 : Blo 1653526 23865947 := bstep (se 1 (by rfl) ⟨17899460, by rfl⟩ : syracuseStep 23865947 = 35798921) B35798921
theorem B7264019 : Blo 1653526 7264019 := bstep (se 1 (by rfl) ⟨5448014, by rfl⟩ : syracuseStep 7264019 = 10896029) B10896029
theorem B5584895 : Blo 1653526 5584895 := bstep (se 1 (by rfl) ⟨4188671, by rfl⟩ : syracuseStep 5584895 = 8377343) B8377343
theorem B1653951 : Blo 1653526 1653951 := bstep (se 1 (by rfl) ⟨1240463, by rfl⟩ : syracuseStep 1653951 = 2480927) B2480927
theorem B31817569 : Blo 1653526 31817569 := bstep (se 2 (by rfl) ⟨11931588, by rfl⟩ : syracuseStep 31817569 = 23863177) B23863177
theorem B10748695 : Blo 1653526 10748695 := bstep (se 1 (by rfl) ⟨8061521, by rfl⟩ : syracuseStep 10748695 = 16123043) B16123043
theorem B4842679 : Blo 1653526 4842679 := bstep (se 1 (by rfl) ⟨3632009, by rfl⟩ : syracuseStep 4842679 = 7264019) B7264019
theorem B15910631 : Blo 1653526 15910631 := bstep (se 1 (by rfl) ⟨11932973, by rfl⟩ : syracuseStep 15910631 = 23865947) B23865947
theorem B20409067 : Blo 1653526 20409067 := bstep (se 1 (by rfl) ⟨15306800, by rfl⟩ : syracuseStep 20409067 = 30613601) B30613601
theorem B3723263 : Blo 1653526 3723263 := bstep (se 1 (by rfl) ⟨2792447, by rfl⟩ : syracuseStep 3723263 = 5584895) B5584895
theorem B42423425 : Blo 1653526 42423425 := bstep (se 2 (by rfl) ⟨15908784, by rfl⟩ : syracuseStep 42423425 = 31817569) B31817569
theorem B15898943 : Blo 1653526 15898943 := bstep (se 1 (by rfl) ⟨11924207, by rfl⟩ : syracuseStep 15898943 = 23848415) B23848415
theorem B108848357 : Blo 1653526 108848357 := bstep (se 4 (by rfl) ⟨10204533, by rfl⟩ : syracuseStep 108848357 = 20409067) B20409067
theorem B6456905 : Blo 1653526 6456905 := bstep (se 2 (by rfl) ⟨2421339, by rfl⟩ : syracuseStep 6456905 = 4842679) B4842679
theorem B28282283 : Blo 1653526 28282283 := bstep (se 1 (by rfl) ⟨21211712, by rfl⟩ : syracuseStep 28282283 = 42423425) B42423425
theorem B42397181 : Blo 1653526 42397181 := bstep (se 3 (by rfl) ⟨7949471, by rfl⟩ : syracuseStep 42397181 = 15898943) B15898943
theorem B14331593 : Blo 1653526 14331593 := bstep (se 2 (by rfl) ⟨5374347, by rfl⟩ : syracuseStep 14331593 = 10748695) B10748695
theorem B2482175 : Blo 1653526 2482175 := bstep (se 1 (by rfl) ⟨1861631, by rfl⟩ : syracuseStep 2482175 = 3723263) B3723263
theorem B10607087 : Blo 1653526 10607087 := bstep (se 1 (by rfl) ⟨7955315, by rfl⟩ : syracuseStep 10607087 = 15910631) B15910631
theorem B72565571 : Blo 1653526 72565571 := bstep (se 1 (by rfl) ⟨54424178, by rfl⟩ : syracuseStep 72565571 = 108848357) B108848357
theorem B7071391 : Blo 1653526 7071391 := bstep (se 1 (by rfl) ⟨5303543, by rfl⟩ : syracuseStep 7071391 = 10607087) B10607087
theorem B28264787 : Blo 1653526 28264787 := bstep (se 1 (by rfl) ⟨21198590, by rfl⟩ : syracuseStep 28264787 = 42397181) B42397181
theorem B9554395 : Blo 1653526 9554395 := bstep (se 1 (by rfl) ⟨7165796, by rfl⟩ : syracuseStep 9554395 = 14331593) B14331593
theorem B4304603 : Blo 1653526 4304603 := bstep (se 1 (by rfl) ⟨3228452, by rfl⟩ : syracuseStep 4304603 = 6456905) B6456905
theorem B18854855 : Blo 1653526 18854855 := bstep (se 1 (by rfl) ⟨14141141, by rfl⟩ : syracuseStep 18854855 = 28282283) B28282283
theorem B1654783 : Blo 1653526 1654783 := bstep (se 1 (by rfl) ⟨1241087, by rfl⟩ : syracuseStep 1654783 = 2482175) B2482175
theorem B12739193 : Blo 1653526 12739193 := bstep (se 2 (by rfl) ⟨4777197, by rfl⟩ : syracuseStep 12739193 = 9554395) B9554395
theorem B18843191 : Blo 1653526 18843191 := bstep (se 1 (by rfl) ⟨14132393, by rfl⟩ : syracuseStep 18843191 = 28264787) B28264787
theorem B2869735 : Blo 1653526 2869735 := bstep (se 1 (by rfl) ⟨2152301, by rfl⟩ : syracuseStep 2869735 = 4304603) B4304603
theorem B12569903 : Blo 1653526 12569903 := bstep (se 1 (by rfl) ⟨9427427, by rfl⟩ : syracuseStep 12569903 = 18854855) B18854855
theorem B193508189 : Blo 1653526 193508189 := bstep (se 3 (by rfl) ⟨36282785, by rfl⟩ : syracuseStep 193508189 = 72565571) B72565571
theorem B9428521 : Blo 1653526 9428521 := bstep (se 2 (by rfl) ⟨3535695, by rfl⟩ : syracuseStep 9428521 = 7071391) B7071391
theorem B3826313 : Blo 1653526 3826313 := bstep (se 2 (by rfl) ⟨1434867, by rfl⟩ : syracuseStep 3826313 = 2869735) B2869735
theorem B12562127 : Blo 1653526 12562127 := bstep (se 1 (by rfl) ⟨9421595, by rfl⟩ : syracuseStep 12562127 = 18843191) B18843191
theorem B12571361 : Blo 1653526 12571361 := bstep (se 2 (by rfl) ⟨4714260, by rfl⟩ : syracuseStep 12571361 = 9428521) B9428521
theorem B8492795 : Blo 1653526 8492795 := bstep (se 1 (by rfl) ⟨6369596, by rfl⟩ : syracuseStep 8492795 = 12739193) B12739193
theorem B129005459 : Blo 1653526 129005459 := bstep (se 1 (by rfl) ⟨96754094, by rfl⟩ : syracuseStep 129005459 = 193508189) B193508189
theorem B8379935 : Blo 1653526 8379935 := bstep (se 1 (by rfl) ⟨6284951, by rfl⟩ : syracuseStep 8379935 = 12569903) B12569903
theorem B8380907 : Blo 1653526 8380907 := bstep (se 1 (by rfl) ⟨6285680, by rfl⟩ : syracuseStep 8380907 = 12571361) B12571361
theorem B5661863 : Blo 1653526 5661863 := bstep (se 1 (by rfl) ⟨4246397, by rfl⟩ : syracuseStep 5661863 = 8492795) B8492795
theorem B8374751 : Blo 1653526 8374751 := bstep (se 1 (by rfl) ⟨6281063, by rfl⟩ : syracuseStep 8374751 = 12562127) B12562127
theorem B2550875 : Blo 1653526 2550875 := bstep (se 1 (by rfl) ⟨1913156, by rfl⟩ : syracuseStep 2550875 = 3826313) B3826313
theorem B86003639 : Blo 1653526 86003639 := bstep (se 1 (by rfl) ⟨64502729, by rfl⟩ : syracuseStep 86003639 = 129005459) B129005459
theorem B5586623 : Blo 1653526 5586623 := bstep (se 1 (by rfl) ⟨4189967, by rfl⟩ : syracuseStep 5586623 = 8379935) B8379935
theorem B5587271 : Blo 1653526 5587271 := bstep (se 1 (by rfl) ⟨4190453, by rfl⟩ : syracuseStep 5587271 = 8380907) B8380907
theorem B27209333 : Blo 1653526 27209333 := bstep (se 5 (by rfl) ⟨1275437, by rfl⟩ : syracuseStep 27209333 = 2550875) B2550875
theorem B5583167 : Blo 1653526 5583167 := bstep (se 1 (by rfl) ⟨4187375, by rfl⟩ : syracuseStep 5583167 = 8374751) B8374751
theorem B3724415 : Blo 1653526 3724415 := bstep (se 1 (by rfl) ⟨2793311, by rfl⟩ : syracuseStep 3724415 = 5586623) B5586623
theorem B3774575 : Blo 1653526 3774575 := bstep (se 1 (by rfl) ⟨2830931, by rfl⟩ : syracuseStep 3774575 = 5661863) B5661863
theorem B57335759 : Blo 1653526 57335759 := bstep (se 1 (by rfl) ⟨43001819, by rfl⟩ : syracuseStep 57335759 = 86003639) B86003639
theorem B2482943 : Blo 1653526 2482943 := bstep (se 1 (by rfl) ⟨1862207, by rfl⟩ : syracuseStep 2482943 = 3724415) B3724415
theorem B2516383 : Blo 1653526 2516383 := bstep (se 1 (by rfl) ⟨1887287, by rfl⟩ : syracuseStep 2516383 = 3774575) B3774575
theorem B18139555 : Blo 1653526 18139555 := bstep (se 1 (by rfl) ⟨13604666, by rfl⟩ : syracuseStep 18139555 = 27209333) B27209333
theorem B3722111 : Blo 1653526 3722111 := bstep (se 1 (by rfl) ⟨2791583, by rfl⟩ : syracuseStep 3722111 = 5583167) B5583167
theorem B3724847 : Blo 1653526 3724847 := bstep (se 1 (by rfl) ⟨2793635, by rfl⟩ : syracuseStep 3724847 = 5587271) B5587271
theorem B38223839 : Blo 1653526 38223839 := bstep (se 1 (by rfl) ⟨28667879, by rfl⟩ : syracuseStep 38223839 = 57335759) B57335759
theorem B1655295 : Blo 1653526 1655295 := bstep (se 1 (by rfl) ⟨1241471, by rfl⟩ : syracuseStep 1655295 = 2482943) B2482943
theorem B2483231 : Blo 1653526 2483231 := bstep (se 1 (by rfl) ⟨1862423, by rfl⟩ : syracuseStep 2483231 = 3724847) B3724847
theorem B3355177 : Blo 1653526 3355177 := bstep (se 2 (by rfl) ⟨1258191, by rfl⟩ : syracuseStep 3355177 = 2516383) B2516383
theorem B96744293 : Blo 1653526 96744293 := bstep (se 4 (by rfl) ⟨9069777, by rfl⟩ : syracuseStep 96744293 = 18139555) B18139555
theorem B25482559 : Blo 1653526 25482559 := bstep (se 1 (by rfl) ⟨19111919, by rfl⟩ : syracuseStep 25482559 = 38223839) B38223839
theorem B2481407 : Blo 1653526 2481407 := bstep (se 1 (by rfl) ⟨1861055, by rfl⟩ : syracuseStep 2481407 = 3722111) B3722111
theorem B64496195 : Blo 1653526 64496195 := bstep (se 1 (by rfl) ⟨48372146, by rfl⟩ : syracuseStep 64496195 = 96744293) B96744293
theorem B1655487 : Blo 1653526 1655487 := bstep (se 1 (by rfl) ⟨1241615, by rfl⟩ : syracuseStep 1655487 = 2483231) B2483231
theorem B4473569 : Blo 1653526 4473569 := bstep (se 2 (by rfl) ⟨1677588, by rfl⟩ : syracuseStep 4473569 = 3355177) B3355177
theorem B33976745 : Blo 1653526 33976745 := bstep (se 2 (by rfl) ⟨12741279, by rfl⟩ : syracuseStep 33976745 = 25482559) B25482559
theorem B1654271 : Blo 1653526 1654271 := bstep (se 1 (by rfl) ⟨1240703, by rfl⟩ : syracuseStep 1654271 = 2481407) B2481407
theorem B22651163 : Blo 1653526 22651163 := bstep (se 1 (by rfl) ⟨16988372, by rfl⟩ : syracuseStep 22651163 = 33976745) B33976745
theorem B11929517 : Blo 1653526 11929517 := bstep (se 3 (by rfl) ⟨2236784, by rfl⟩ : syracuseStep 11929517 = 4473569) B4473569
theorem B42997463 : Blo 1653526 42997463 := bstep (se 1 (by rfl) ⟨32248097, by rfl⟩ : syracuseStep 42997463 = 64496195) B64496195
theorem B28664975 : Blo 1653526 28664975 := bstep (se 1 (by rfl) ⟨21498731, by rfl⟩ : syracuseStep 28664975 = 42997463) B42997463
theorem B15100775 : Blo 1653526 15100775 := bstep (se 1 (by rfl) ⟨11325581, by rfl⟩ : syracuseStep 15100775 = 22651163) B22651163
theorem B7953011 : Blo 1653526 7953011 := bstep (se 1 (by rfl) ⟨5964758, by rfl⟩ : syracuseStep 7953011 = 11929517) B11929517
theorem B76439933 : Blo 1653526 76439933 := bstep (se 3 (by rfl) ⟨14332487, by rfl⟩ : syracuseStep 76439933 = 28664975) B28664975
theorem B5302007 : Blo 1653526 5302007 := bstep (se 1 (by rfl) ⟨3976505, by rfl⟩ : syracuseStep 5302007 = 7953011) B7953011
theorem B10067183 : Blo 1653526 10067183 := bstep (se 1 (by rfl) ⟨7550387, by rfl⟩ : syracuseStep 10067183 = 15100775) B15100775
theorem B6711455 : Blo 1653526 6711455 := bstep (se 1 (by rfl) ⟨5033591, by rfl⟩ : syracuseStep 6711455 = 10067183) B10067183
theorem B3534671 : Blo 1653526 3534671 := bstep (se 1 (by rfl) ⟨2651003, by rfl⟩ : syracuseStep 3534671 = 5302007) B5302007
theorem B50959955 : Blo 1653526 50959955 := bstep (se 1 (by rfl) ⟨38219966, by rfl⟩ : syracuseStep 50959955 = 76439933) B76439933
theorem B33973303 : Blo 1653526 33973303 := bstep (se 1 (by rfl) ⟨25479977, by rfl⟩ : syracuseStep 33973303 = 50959955) B50959955
theorem B2356447 : Blo 1653526 2356447 := bstep (se 1 (by rfl) ⟨1767335, by rfl⟩ : syracuseStep 2356447 = 3534671) B3534671
theorem B17897213 : Blo 1653526 17897213 := bstep (se 3 (by rfl) ⟨3355727, by rfl⟩ : syracuseStep 17897213 = 6711455) B6711455
theorem B11931475 : Blo 1653526 11931475 := bstep (se 1 (by rfl) ⟨8948606, by rfl⟩ : syracuseStep 11931475 = 17897213) B17897213
theorem B45297737 : Blo 1653526 45297737 := bstep (se 2 (by rfl) ⟨16986651, by rfl⟩ : syracuseStep 45297737 = 33973303) B33973303
theorem B3141929 : Blo 1653526 3141929 := bstep (se 2 (by rfl) ⟨1178223, by rfl⟩ : syracuseStep 3141929 = 2356447) B2356447
theorem B30198491 : Blo 1653526 30198491 := bstep (se 1 (by rfl) ⟨22648868, by rfl⟩ : syracuseStep 30198491 = 45297737) B45297737
theorem B8378477 : Blo 1653526 8378477 := bstep (se 3 (by rfl) ⟨1570964, by rfl⟩ : syracuseStep 8378477 = 3141929) B3141929
theorem B15908633 : Blo 1653526 15908633 := bstep (se 2 (by rfl) ⟨5965737, by rfl⟩ : syracuseStep 15908633 = 11931475) B11931475
theorem B20132327 : Blo 1653526 20132327 := bstep (se 1 (by rfl) ⟨15099245, by rfl⟩ : syracuseStep 20132327 = 30198491) B30198491
theorem B10605755 : Blo 1653526 10605755 := bstep (se 1 (by rfl) ⟨7954316, by rfl⟩ : syracuseStep 10605755 = 15908633) B15908633
theorem B5585651 : Blo 1653526 5585651 := bstep (se 1 (by rfl) ⟨4189238, by rfl⟩ : syracuseStep 5585651 = 8378477) B8378477
theorem B7070503 : Blo 1653526 7070503 := bstep (se 1 (by rfl) ⟨5302877, by rfl⟩ : syracuseStep 7070503 = 10605755) B10605755
theorem B13421551 : Blo 1653526 13421551 := bstep (se 1 (by rfl) ⟨10066163, by rfl⟩ : syracuseStep 13421551 = 20132327) B20132327
theorem B3723767 : Blo 1653526 3723767 := bstep (se 1 (by rfl) ⟨2792825, by rfl⟩ : syracuseStep 3723767 = 5585651) B5585651
theorem B2482511 : Blo 1653526 2482511 := bstep (se 1 (by rfl) ⟨1861883, by rfl⟩ : syracuseStep 2482511 = 3723767) B3723767
theorem B17895401 : Blo 1653526 17895401 := bstep (se 2 (by rfl) ⟨6710775, by rfl⟩ : syracuseStep 17895401 = 13421551) B13421551
theorem B9427337 : Blo 1653526 9427337 := bstep (se 2 (by rfl) ⟨3535251, by rfl⟩ : syracuseStep 9427337 = 7070503) B7070503
theorem B1655007 : Blo 1653526 1655007 := bstep (se 1 (by rfl) ⟨1241255, by rfl⟩ : syracuseStep 1655007 = 2482511) B2482511
theorem B6284891 : Blo 1653526 6284891 := bstep (se 1 (by rfl) ⟨4713668, by rfl⟩ : syracuseStep 6284891 = 9427337) B9427337
theorem B11930267 : Blo 1653526 11930267 := bstep (se 1 (by rfl) ⟨8947700, by rfl⟩ : syracuseStep 11930267 = 17895401) B17895401
theorem B4189927 : Blo 1653526 4189927 := bstep (se 1 (by rfl) ⟨3142445, by rfl⟩ : syracuseStep 4189927 = 6284891) B6284891
theorem B7953511 : Blo 1653526 7953511 := bstep (se 1 (by rfl) ⟨5965133, by rfl⟩ : syracuseStep 7953511 = 11930267) B11930267
theorem B10604681 : Blo 1653526 10604681 := bstep (se 2 (by rfl) ⟨3976755, by rfl⟩ : syracuseStep 10604681 = 7953511) B7953511
theorem B5586569 : Blo 1653526 5586569 := bstep (se 2 (by rfl) ⟨2094963, by rfl⟩ : syracuseStep 5586569 = 4189927) B4189927
theorem B7069787 : Blo 1653526 7069787 := bstep (se 1 (by rfl) ⟨5302340, by rfl⟩ : syracuseStep 7069787 = 10604681) B10604681
theorem B3724379 : Blo 1653526 3724379 := bstep (se 1 (by rfl) ⟨2793284, by rfl⟩ : syracuseStep 3724379 = 5586569) B5586569
theorem B2482919 : Blo 1653526 2482919 := bstep (se 1 (by rfl) ⟨1862189, by rfl⟩ : syracuseStep 2482919 = 3724379) B3724379
theorem B4713191 : Blo 1653526 4713191 := bstep (se 1 (by rfl) ⟨3534893, by rfl⟩ : syracuseStep 4713191 = 7069787) B7069787
theorem B1655279 : Blo 1653526 1655279 := bstep (se 1 (by rfl) ⟨1241459, by rfl⟩ : syracuseStep 1655279 = 2482919) B2482919
theorem B3142127 : Blo 1653526 3142127 := bstep (se 1 (by rfl) ⟨2356595, by rfl⟩ : syracuseStep 3142127 = 4713191) B4713191
theorem B2094751 : Blo 1653526 2094751 := bstep (se 1 (by rfl) ⟨1571063, by rfl⟩ : syracuseStep 2094751 = 3142127) B3142127
theorem B2793001 : Blo 1653526 2793001 := bstep (se 2 (by rfl) ⟨1047375, by rfl⟩ : syracuseStep 2793001 = 2094751) B2094751
theorem B3724001 : Blo 1653526 3724001 := bstep (se 2 (by rfl) ⟨1396500, by rfl⟩ : syracuseStep 3724001 = 2793001) B2793001
theorem B2482667 : Blo 1653526 2482667 := bstep (se 1 (by rfl) ⟨1862000, by rfl⟩ : syracuseStep 2482667 = 3724001) B3724001
theorem B1655111 : Blo 1653526 1655111 := bstep (se 1 (by rfl) ⟨1241333, by rfl⟩ : syracuseStep 1655111 = 2482667) B2482667

theorem C0 (j : ℕ) (h1 : 413381 ≤ j) (h2 : j ≤ 413880) : Blo 1653526 (4 * j + 3) := by
  interval_cases j
  · exact B1653527
  · exact B1653531
  · exact B1653535
  · exact B1653539
  · exact B1653543
  · exact B1653547
  · exact B1653551
  · exact B1653555
  · exact B1653559
  · exact B1653563
  · exact B1653567
  · exact B1653571
  · exact B1653575
  · exact B1653579
  · exact B1653583
  · exact B1653587
  · exact B1653591
  · exact B1653595
  · exact B1653599
  · exact B1653603
  · exact B1653607
  · exact B1653611
  · exact B1653615
  · exact B1653619
  · exact B1653623
  · exact B1653627
  · exact B1653631
  · exact B1653635
  · exact B1653639
  · exact B1653643
  · exact B1653647
  · exact B1653651
  · exact B1653655
  · exact B1653659
  · exact B1653663
  · exact B1653667
  · exact B1653671
  · exact B1653675
  · exact B1653679
  · exact B1653683
  · exact B1653687
  · exact B1653691
  · exact B1653695
  · exact B1653699
  · exact B1653703
  · exact B1653707
  · exact B1653711
  · exact B1653715
  · exact B1653719
  · exact B1653723
  · exact B1653727
  · exact B1653731
  · exact B1653735
  · exact B1653739
  · exact B1653743
  · exact B1653747
  · exact B1653751
  · exact B1653755
  · exact B1653759
  · exact B1653763
  · exact B1653767
  · exact B1653771
  · exact B1653775
  · exact B1653779
  · exact B1653783
  · exact B1653787
  · exact B1653791
  · exact B1653795
  · exact B1653799
  · exact B1653803
  · exact B1653807
  · exact B1653811
  · exact B1653815
  · exact B1653819
  · exact B1653823
  · exact B1653827
  · exact B1653831
  · exact B1653835
  · exact B1653839
  · exact B1653843
  · exact B1653847
  · exact B1653851
  · exact B1653855
  · exact B1653859
  · exact B1653863
  · exact B1653867
  · exact B1653871
  · exact B1653875
  · exact B1653879
  · exact B1653883
  · exact B1653887
  · exact B1653891
  · exact B1653895
  · exact B1653899
  · exact B1653903
  · exact B1653907
  · exact B1653911
  · exact B1653915
  · exact B1653919
  · exact B1653923
  · exact B1653927
  · exact B1653931
  · exact B1653935
  · exact B1653939
  · exact B1653943
  · exact B1653947
  · exact B1653951
  · exact B1653955
  · exact B1653959
  · exact B1653963
  · exact B1653967
  · exact B1653971
  · exact B1653975
  · exact B1653979
  · exact B1653983
  · exact B1653987
  · exact B1653991
  · exact B1653995
  · exact B1653999
  · exact B1654003
  · exact B1654007
  · exact B1654011
  · exact B1654015
  · exact B1654019
  · exact B1654023
  · exact B1654027
  · exact B1654031
  · exact B1654035
  · exact B1654039
  · exact B1654043
  · exact B1654047
  · exact B1654051
  · exact B1654055
  · exact B1654059
  · exact B1654063
  · exact B1654067
  · exact B1654071
  · exact B1654075
  · exact B1654079
  · exact B1654083
  · exact B1654087
  · exact B1654091
  · exact B1654095
  · exact B1654099
  · exact B1654103
  · exact B1654107
  · exact B1654111
  · exact B1654115
  · exact B1654119
  · exact B1654123
  · exact B1654127
  · exact B1654131
  · exact B1654135
  · exact B1654139
  · exact B1654143
  · exact B1654147
  · exact B1654151
  · exact B1654155
  · exact B1654159
  · exact B1654163
  · exact B1654167
  · exact B1654171
  · exact B1654175
  · exact B1654179
  · exact B1654183
  · exact B1654187
  · exact B1654191
  · exact B1654195
  · exact B1654199
  · exact B1654203
  · exact B1654207
  · exact B1654211
  · exact B1654215
  · exact B1654219
  · exact B1654223
  · exact B1654227
  · exact B1654231
  · exact B1654235
  · exact B1654239
  · exact B1654243
  · exact B1654247
  · exact B1654251
  · exact B1654255
  · exact B1654259
  · exact B1654263
  · exact B1654267
  · exact B1654271
  · exact B1654275
  · exact B1654279
  · exact B1654283
  · exact B1654287
  · exact B1654291
  · exact B1654295
  · exact B1654299
  · exact B1654303
  · exact B1654307
  · exact B1654311
  · exact B1654315
  · exact B1654319
  · exact B1654323
  · exact B1654327
  · exact B1654331
  · exact B1654335
  · exact B1654339
  · exact B1654343
  · exact B1654347
  · exact B1654351
  · exact B1654355
  · exact B1654359
  · exact B1654363
  · exact B1654367
  · exact B1654371
  · exact B1654375
  · exact B1654379
  · exact B1654383
  · exact B1654387
  · exact B1654391
  · exact B1654395
  · exact B1654399
  · exact B1654403
  · exact B1654407
  · exact B1654411
  · exact B1654415
  · exact B1654419
  · exact B1654423
  · exact B1654427
  · exact B1654431
  · exact B1654435
  · exact B1654439
  · exact B1654443
  · exact B1654447
  · exact B1654451
  · exact B1654455
  · exact B1654459
  · exact B1654463
  · exact B1654467
  · exact B1654471
  · exact B1654475
  · exact B1654479
  · exact B1654483
  · exact B1654487
  · exact B1654491
  · exact B1654495
  · exact B1654499
  · exact B1654503
  · exact B1654507
  · exact B1654511
  · exact B1654515
  · exact B1654519
  · exact B1654523
  · exact B1654527
  · exact B1654531
  · exact B1654535
  · exact B1654539
  · exact B1654543
  · exact B1654547
  · exact B1654551
  · exact B1654555
  · exact B1654559
  · exact B1654563
  · exact B1654567
  · exact B1654571
  · exact B1654575
  · exact B1654579
  · exact B1654583
  · exact B1654587
  · exact B1654591
  · exact B1654595
  · exact B1654599
  · exact B1654603
  · exact B1654607
  · exact B1654611
  · exact B1654615
  · exact B1654619
  · exact B1654623
  · exact B1654627
  · exact B1654631
  · exact B1654635
  · exact B1654639
  · exact B1654643
  · exact B1654647
  · exact B1654651
  · exact B1654655
  · exact B1654659
  · exact B1654663
  · exact B1654667
  · exact B1654671
  · exact B1654675
  · exact B1654679
  · exact B1654683
  · exact B1654687
  · exact B1654691
  · exact B1654695
  · exact B1654699
  · exact B1654703
  · exact B1654707
  · exact B1654711
  · exact B1654715
  · exact B1654719
  · exact B1654723
  · exact B1654727
  · exact B1654731
  · exact B1654735
  · exact B1654739
  · exact B1654743
  · exact B1654747
  · exact B1654751
  · exact B1654755
  · exact B1654759
  · exact B1654763
  · exact B1654767
  · exact B1654771
  · exact B1654775
  · exact B1654779
  · exact B1654783
  · exact B1654787
  · exact B1654791
  · exact B1654795
  · exact B1654799
  · exact B1654803
  · exact B1654807
  · exact B1654811
  · exact B1654815
  · exact B1654819
  · exact B1654823
  · exact B1654827
  · exact B1654831
  · exact B1654835
  · exact B1654839
  · exact B1654843
  · exact B1654847
  · exact B1654851
  · exact B1654855
  · exact B1654859
  · exact B1654863
  · exact B1654867
  · exact B1654871
  · exact B1654875
  · exact B1654879
  · exact B1654883
  · exact B1654887
  · exact B1654891
  · exact B1654895
  · exact B1654899
  · exact B1654903
  · exact B1654907
  · exact B1654911
  · exact B1654915
  · exact B1654919
  · exact B1654923
  · exact B1654927
  · exact B1654931
  · exact B1654935
  · exact B1654939
  · exact B1654943
  · exact B1654947
  · exact B1654951
  · exact B1654955
  · exact B1654959
  · exact B1654963
  · exact B1654967
  · exact B1654971
  · exact B1654975
  · exact B1654979
  · exact B1654983
  · exact B1654987
  · exact B1654991
  · exact B1654995
  · exact B1654999
  · exact B1655003
  · exact B1655007
  · exact B1655011
  · exact B1655015
  · exact B1655019
  · exact B1655023
  · exact B1655027
  · exact B1655031
  · exact B1655035
  · exact B1655039
  · exact B1655043
  · exact B1655047
  · exact B1655051
  · exact B1655055
  · exact B1655059
  · exact B1655063
  · exact B1655067
  · exact B1655071
  · exact B1655075
  · exact B1655079
  · exact B1655083
  · exact B1655087
  · exact B1655091
  · exact B1655095
  · exact B1655099
  · exact B1655103
  · exact B1655107
  · exact B1655111
  · exact B1655115
  · exact B1655119
  · exact B1655123
  · exact B1655127
  · exact B1655131
  · exact B1655135
  · exact B1655139
  · exact B1655143
  · exact B1655147
  · exact B1655151
  · exact B1655155
  · exact B1655159
  · exact B1655163
  · exact B1655167
  · exact B1655171
  · exact B1655175
  · exact B1655179
  · exact B1655183
  · exact B1655187
  · exact B1655191
  · exact B1655195
  · exact B1655199
  · exact B1655203
  · exact B1655207
  · exact B1655211
  · exact B1655215
  · exact B1655219
  · exact B1655223
  · exact B1655227
  · exact B1655231
  · exact B1655235
  · exact B1655239
  · exact B1655243
  · exact B1655247
  · exact B1655251
  · exact B1655255
  · exact B1655259
  · exact B1655263
  · exact B1655267
  · exact B1655271
  · exact B1655275
  · exact B1655279
  · exact B1655283
  · exact B1655287
  · exact B1655291
  · exact B1655295
  · exact B1655299
  · exact B1655303
  · exact B1655307
  · exact B1655311
  · exact B1655315
  · exact B1655319
  · exact B1655323
  · exact B1655327
  · exact B1655331
  · exact B1655335
  · exact B1655339
  · exact B1655343
  · exact B1655347
  · exact B1655351
  · exact B1655355
  · exact B1655359
  · exact B1655363
  · exact B1655367
  · exact B1655371
  · exact B1655375
  · exact B1655379
  · exact B1655383
  · exact B1655387
  · exact B1655391
  · exact B1655395
  · exact B1655399
  · exact B1655403
  · exact B1655407
  · exact B1655411
  · exact B1655415
  · exact B1655419
  · exact B1655423
  · exact B1655427
  · exact B1655431
  · exact B1655435
  · exact B1655439
  · exact B1655443
  · exact B1655447
  · exact B1655451
  · exact B1655455
  · exact B1655459
  · exact B1655463
  · exact B1655467
  · exact B1655471
  · exact B1655475
  · exact B1655479
  · exact B1655483
  · exact B1655487
  · exact B1655491
  · exact B1655495
  · exact B1655499
  · exact B1655503
  · exact B1655507
  · exact B1655511
  · exact B1655515
  · exact B1655519
  · exact B1655523

theorem solution (m : ℕ) (hlo : 1653526 ≤ m) (hhi : m ≤ 1655526) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 413381 ≤ j := by omega
    have hj2 : j ≤ 413880 := by omega
    have hb : Blo 1653526 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
