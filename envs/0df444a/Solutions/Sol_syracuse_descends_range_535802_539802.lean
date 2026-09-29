-- Prove2me | solution 1 for syracuse_descends_range_535802_539802
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:31.252183+00:00
-- url     : https://prove2.me/submissions/5e48af1b-0f29-4d71-9feb-eac1f6d8c5c3

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


theorem B1212461 : Blo 535802 1212461 := bbase (se 3 (by rfl) ⟨227336, by rfl⟩ : syracuseStep 1212461 = 454673) (by norm_num)
theorem B29491285 : Blo 535802 29491285 := bbase (se 8 (by rfl) ⟨172800, by rfl⟩ : syracuseStep 29491285 = 345601) (by norm_num)
theorem B1212533 : Blo 535802 1212533 := bbase (se 5 (by rfl) ⟨56837, by rfl⟩ : syracuseStep 1212533 = 113675) (by norm_num)
theorem B1212605 : Blo 535802 1212605 := bbase (se 3 (by rfl) ⟨227363, by rfl⟩ : syracuseStep 1212605 = 454727) (by norm_num)
theorem B1933541 : Blo 535802 1933541 := bbase (se 4 (by rfl) ⟨181269, by rfl⟩ : syracuseStep 1933541 = 362539) (by norm_num)
theorem B1212677 : Blo 535802 1212677 := bbase (se 4 (by rfl) ⟨113688, by rfl⟩ : syracuseStep 1212677 = 227377) (by norm_num)
theorem B1212749 : Blo 535802 1212749 := bbase (se 3 (by rfl) ⟨227390, by rfl⟩ : syracuseStep 1212749 = 454781) (by norm_num)
theorem B885109 : Blo 535802 885109 := bbase (se 5 (by rfl) ⟨41489, by rfl⟩ : syracuseStep 885109 = 82979) (by norm_num)
theorem B2457973 : Blo 535802 2457973 := bbase (se 5 (by rfl) ⟨115217, by rfl⟩ : syracuseStep 2457973 = 230435) (by norm_num)
theorem B3277205 : Blo 535802 3277205 := bbase (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) (by norm_num)
theorem B1212821 : Blo 535802 1212821 := bbase (se 6 (by rfl) ⟨28425, by rfl⟩ : syracuseStep 1212821 = 56851) (by norm_num)
theorem B1212893 : Blo 535802 1212893 := bbase (se 3 (by rfl) ⟨227417, by rfl⟩ : syracuseStep 1212893 = 454835) (by norm_num)
theorem B1049093 : Blo 535802 1049093 := bbase (se 4 (by rfl) ⟨98352, by rfl⟩ : syracuseStep 1049093 = 196705) (by norm_num)
theorem B1212965 : Blo 535802 1212965 := bbase (se 4 (by rfl) ⟨113715, by rfl⟩ : syracuseStep 1212965 = 227431) (by norm_num)
theorem B1213037 : Blo 535802 1213037 := bbase (se 3 (by rfl) ⟨227444, by rfl⟩ : syracuseStep 1213037 = 454889) (by norm_num)
theorem B2589317 : Blo 535802 2589317 := bbase (se 4 (by rfl) ⟨242748, by rfl⟩ : syracuseStep 2589317 = 485497) (by norm_num)
theorem B1213109 : Blo 535802 1213109 := bbase (se 5 (by rfl) ⟨56864, by rfl⟩ : syracuseStep 1213109 = 113729) (by norm_num)
theorem B1147621 : Blo 535802 1147621 := bbase (se 4 (by rfl) ⟨107589, by rfl⟩ : syracuseStep 1147621 = 215179) (by norm_num)
theorem B1213181 : Blo 535802 1213181 := bbase (se 3 (by rfl) ⟨227471, by rfl⟩ : syracuseStep 1213181 = 454943) (by norm_num)
theorem B1213253 : Blo 535802 1213253 := bbase (se 4 (by rfl) ⟨113742, by rfl⟩ : syracuseStep 1213253 = 227485) (by norm_num)
theorem B1147765 : Blo 535802 1147765 := bbase (se 5 (by rfl) ⟨53801, by rfl⟩ : syracuseStep 1147765 = 107603) (by norm_num)
theorem B1213325 : Blo 535802 1213325 := bbase (se 3 (by rfl) ⟨227498, by rfl⟩ : syracuseStep 1213325 = 454997) (by norm_num)
theorem B1213397 : Blo 535802 1213397 := bbase (se 7 (by rfl) ⟨14219, by rfl⟩ : syracuseStep 1213397 = 28439) (by norm_num)
theorem B2720789 : Blo 535802 2720789 := bbase (se 6 (by rfl) ⟨63768, by rfl⟩ : syracuseStep 2720789 = 127537) (by norm_num)
theorem B1213469 : Blo 535802 1213469 := bbase (se 3 (by rfl) ⟨227525, by rfl⟩ : syracuseStep 1213469 = 455051) (by norm_num)
theorem B1213541 : Blo 535802 1213541 := bbase (se 4 (by rfl) ⟨113769, by rfl⟩ : syracuseStep 1213541 = 227539) (by norm_num)
theorem B1213613 : Blo 535802 1213613 := bbase (se 3 (by rfl) ⟨227552, by rfl⟩ : syracuseStep 1213613 = 455105) (by norm_num)
theorem B1934549 : Blo 535802 1934549 := bbase (se 7 (by rfl) ⟨22670, by rfl⟩ : syracuseStep 1934549 = 45341) (by norm_num)
theorem B1148141 : Blo 535802 1148141 := bbase (se 3 (by rfl) ⟨215276, by rfl⟩ : syracuseStep 1148141 = 430553) (by norm_num)
theorem B1213685 : Blo 535802 1213685 := bbase (se 5 (by rfl) ⟨56891, by rfl⟩ : syracuseStep 1213685 = 113783) (by norm_num)
theorem B820469 : Blo 535802 820469 := bbase (se 5 (by rfl) ⟨38459, by rfl⟩ : syracuseStep 820469 = 76919) (by norm_num)
theorem B1213757 : Blo 535802 1213757 := bbase (se 3 (by rfl) ⟨227579, by rfl⟩ : syracuseStep 1213757 = 455159) (by norm_num)
theorem B1213829 : Blo 535802 1213829 := bbase (se 4 (by rfl) ⟨113796, by rfl⟩ : syracuseStep 1213829 = 227593) (by norm_num)
theorem B1213901 : Blo 535802 1213901 := bbase (se 3 (by rfl) ⟨227606, by rfl⟩ : syracuseStep 1213901 = 455213) (by norm_num)
theorem B984565 : Blo 535802 984565 := bbase (se 5 (by rfl) ⟨46151, by rfl⟩ : syracuseStep 984565 = 92303) (by norm_num)
theorem B1213973 : Blo 535802 1213973 := bbase (se 6 (by rfl) ⟨28452, by rfl⟩ : syracuseStep 1213973 = 56905) (by norm_num)
theorem B1017373 : Blo 535802 1017373 := bbase (se 3 (by rfl) ⟨190757, by rfl⟩ : syracuseStep 1017373 = 381515) (by norm_num)
theorem B1148509 : Blo 535802 1148509 := bbase (se 3 (by rfl) ⟨215345, by rfl⟩ : syracuseStep 1148509 = 430691) (by norm_num)
theorem B1214045 : Blo 535802 1214045 := bbase (se 3 (by rfl) ⟨227633, by rfl⟩ : syracuseStep 1214045 = 455267) (by norm_num)
theorem B1214117 : Blo 535802 1214117 := bbase (se 4 (by rfl) ⟨113823, by rfl⟩ : syracuseStep 1214117 = 227647) (by norm_num)
theorem B1017517 : Blo 535802 1017517 := bbase (se 3 (by rfl) ⟨190784, by rfl⟩ : syracuseStep 1017517 = 381569) (by norm_num)
theorem B886477 : Blo 535802 886477 := bbase (se 3 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 886477 = 332429) (by norm_num)
theorem B1214189 : Blo 535802 1214189 := bbase (se 3 (by rfl) ⟨227660, by rfl⟩ : syracuseStep 1214189 = 455321) (by norm_num)
theorem B10323733 : Blo 535802 10323733 := bbase (se 6 (by rfl) ⟨241962, by rfl⟩ : syracuseStep 10323733 = 483925) (by norm_num)
theorem B1640245 : Blo 535802 1640245 := bbase (se 5 (by rfl) ⟨76886, by rfl⟩ : syracuseStep 1640245 = 153773) (by norm_num)
theorem B1214261 : Blo 535802 1214261 := bbase (se 5 (by rfl) ⟨56918, by rfl⟩ : syracuseStep 1214261 = 113837) (by norm_num)
theorem B5539637 : Blo 535802 5539637 := bbase (se 5 (by rfl) ⟨259670, by rfl⟩ : syracuseStep 5539637 = 519341) (by norm_num)
theorem B1017677 : Blo 535802 1017677 := bbase (se 3 (by rfl) ⟨190814, by rfl⟩ : syracuseStep 1017677 = 381629) (by norm_num)
theorem B1214333 : Blo 535802 1214333 := bbase (se 3 (by rfl) ⟨227687, by rfl⟩ : syracuseStep 1214333 = 455375) (by norm_num)
theorem B1214405 : Blo 535802 1214405 := bbase (se 4 (by rfl) ⟨113850, by rfl⟩ : syracuseStep 1214405 = 227701) (by norm_num)
theorem B1017821 : Blo 535802 1017821 := bbase (se 3 (by rfl) ⟨190841, by rfl⟩ : syracuseStep 1017821 = 381683) (by norm_num)
theorem B1214477 : Blo 535802 1214477 := bbase (se 3 (by rfl) ⟨227714, by rfl⟩ : syracuseStep 1214477 = 455429) (by norm_num)
theorem B1214549 : Blo 535802 1214549 := bbase (se 8 (by rfl) ⟨7116, by rfl⟩ : syracuseStep 1214549 = 14233) (by norm_num)
theorem B919757 : Blo 535802 919757 := bbase (se 3 (by rfl) ⟨172454, by rfl⟩ : syracuseStep 919757 = 344909) (by norm_num)
theorem B1018109 : Blo 535802 1018109 := bbase (se 3 (by rfl) ⟨190895, by rfl⟩ : syracuseStep 1018109 = 381791) (by norm_num)
theorem B2722085 : Blo 535802 2722085 := bbase (se 4 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 2722085 = 510391) (by norm_num)
theorem B1378669 : Blo 535802 1378669 := bbase (se 3 (by rfl) ⟨258500, by rfl⟩ : syracuseStep 1378669 = 517001) (by norm_num)
theorem B1018261 : Blo 535802 1018261 := bbase (se 6 (by rfl) ⟨23865, by rfl⟩ : syracuseStep 1018261 = 47731) (by norm_num)
theorem B887213 : Blo 535802 887213 := bbase (se 3 (by rfl) ⟨166352, by rfl⟩ : syracuseStep 887213 = 332705) (by norm_num)
theorem B1018565 : Blo 535802 1018565 := bbase (se 4 (by rfl) ⟨95490, by rfl⟩ : syracuseStep 1018565 = 190981) (by norm_num)
theorem B2034517 : Blo 535802 2034517 := bbase (se 9 (by rfl) ⟨5960, by rfl⟩ : syracuseStep 2034517 = 11921) (by norm_num)
theorem B1150013 : Blo 535802 1150013 := bbase (se 3 (by rfl) ⟨215627, by rfl⟩ : syracuseStep 1150013 = 431255) (by norm_num)
theorem B2034821 : Blo 535802 2034821 := bbase (se 4 (by rfl) ⟨190764, by rfl⟩ : syracuseStep 2034821 = 381529) (by norm_num)
theorem B2755781 : Blo 535802 2755781 := bbase (se 4 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 2755781 = 516709) (by norm_num)
theorem B1150157 : Blo 535802 1150157 := bbase (se 3 (by rfl) ⟨215654, by rfl⟩ : syracuseStep 1150157 = 431309) (by norm_num)
theorem B2592005 : Blo 535802 2592005 := bbase (se 4 (by rfl) ⟨243000, by rfl⟩ : syracuseStep 2592005 = 486001) (by norm_num)
theorem B1019317 : Blo 535802 1019317 := bbase (se 5 (by rfl) ⟨47780, by rfl⟩ : syracuseStep 1019317 = 95561) (by norm_num)
theorem B1936885 : Blo 535802 1936885 := bbase (se 5 (by rfl) ⟨90791, by rfl⟩ : syracuseStep 1936885 = 181583) (by norm_num)
theorem B2985461 : Blo 535802 2985461 := bbase (se 5 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 2985461 = 279887) (by norm_num)
theorem B2723381 : Blo 535802 2723381 := bbase (se 5 (by rfl) ⟨127658, by rfl⟩ : syracuseStep 2723381 = 255317) (by norm_num)
theorem B1150517 : Blo 535802 1150517 := bbase (se 5 (by rfl) ⟨53930, by rfl⟩ : syracuseStep 1150517 = 107861) (by norm_num)
theorem B1019461 : Blo 535802 1019461 := bbase (se 4 (by rfl) ⟨95574, by rfl⟩ : syracuseStep 1019461 = 191149) (by norm_num)
theorem B2297429 : Blo 535802 2297429 := bbase (se 8 (by rfl) ⟨13461, by rfl⟩ : syracuseStep 2297429 = 26923) (by norm_num)
theorem B1412813 : Blo 535802 1412813 := bbase (se 3 (by rfl) ⟨264902, by rfl⟩ : syracuseStep 1412813 = 529805) (by norm_num)
theorem B1019621 : Blo 535802 1019621 := bbase (se 4 (by rfl) ⟨95589, by rfl⟩ : syracuseStep 1019621 = 191179) (by norm_num)
theorem B1019765 : Blo 535802 1019765 := bbase (se 5 (by rfl) ⟨47801, by rfl⟩ : syracuseStep 1019765 = 95603) (by norm_num)
theorem B2297717 : Blo 535802 2297717 := bbase (se 5 (by rfl) ⟨107705, by rfl⟩ : syracuseStep 2297717 = 215411) (by norm_num)
theorem B1020053 : Blo 535802 1020053 := bbase (se 6 (by rfl) ⟨23907, by rfl⟩ : syracuseStep 1020053 = 47815) (by norm_num)
theorem B1020205 : Blo 535802 1020205 := bbase (se 3 (by rfl) ⟨191288, by rfl⟩ : syracuseStep 1020205 = 382577) (by norm_num)
theorem B1151405 : Blo 535802 1151405 := bbase (se 3 (by rfl) ⟨215888, by rfl⟩ : syracuseStep 1151405 = 431777) (by norm_num)
theorem B1020509 : Blo 535802 1020509 := bbase (se 3 (by rfl) ⟨191345, by rfl⟩ : syracuseStep 1020509 = 382691) (by norm_num)
theorem B2298469 : Blo 535802 2298469 := bbase (se 4 (by rfl) ⟨215481, by rfl⟩ : syracuseStep 2298469 = 430963) (by norm_num)
theorem B1151653 : Blo 535802 1151653 := bbase (se 4 (by rfl) ⟨107967, by rfl⟩ : syracuseStep 1151653 = 215935) (by norm_num)
theorem B7344917 : Blo 535802 7344917 := bbase (se 6 (by rfl) ⟨172146, by rfl⟩ : syracuseStep 7344917 = 344293) (by norm_num)
theorem B2724677 : Blo 535802 2724677 := bbase (se 4 (by rfl) ⟨255438, by rfl⟩ : syracuseStep 2724677 = 510877) (by norm_num)
theorem B725845 : Blo 535802 725845 := bbase (se 9 (by rfl) ⟨2126, by rfl⟩ : syracuseStep 725845 = 4253) (by norm_num)
theorem B1381277 : Blo 535802 1381277 := bbase (se 3 (by rfl) ⟨258989, by rfl⟩ : syracuseStep 1381277 = 517979) (by norm_num)
theorem B726013 : Blo 535802 726013 := bbase (se 3 (by rfl) ⟨136127, by rfl⟩ : syracuseStep 726013 = 272255) (by norm_num)
theorem B1152157 : Blo 535802 1152157 := bbase (se 3 (by rfl) ⟨216029, by rfl⟩ : syracuseStep 1152157 = 432059) (by norm_num)
theorem B2036933 : Blo 535802 2036933 := bbase (se 4 (by rfl) ⟨190962, by rfl⟩ : syracuseStep 2036933 = 381925) (by norm_num)
theorem B2299205 : Blo 535802 2299205 := bbase (se 4 (by rfl) ⟨215550, by rfl⟩ : syracuseStep 2299205 = 431101) (by norm_num)
theorem B1021261 : Blo 535802 1021261 := bbase (se 3 (by rfl) ⟨191486, by rfl⟩ : syracuseStep 1021261 = 382973) (by norm_num)
theorem B3446165 : Blo 535802 3446165 := bbase (se 6 (by rfl) ⟨80769, by rfl⟩ : syracuseStep 3446165 = 161539) (by norm_num)
theorem B1021405 : Blo 535802 1021405 := bbase (se 3 (by rfl) ⟨191513, by rfl⟩ : syracuseStep 1021405 = 383027) (by norm_num)
theorem B2037221 : Blo 535802 2037221 := bbase (se 4 (by rfl) ⟨190989, by rfl⟩ : syracuseStep 2037221 = 381979) (by norm_num)
theorem B1021565 : Blo 535802 1021565 := bbase (se 3 (by rfl) ⟨191543, by rfl⟩ : syracuseStep 1021565 = 383087) (by norm_num)
theorem B1021709 : Blo 535802 1021709 := bbase (se 3 (by rfl) ⟨191570, by rfl⟩ : syracuseStep 1021709 = 383141) (by norm_num)
theorem B628517 : Blo 535802 628517 := bbase (se 4 (by rfl) ⟨58923, by rfl⟩ : syracuseStep 628517 = 117847) (by norm_num)
theorem B1808405 : Blo 535802 1808405 := bbase (se 6 (by rfl) ⟨42384, by rfl⟩ : syracuseStep 1808405 = 84769) (by norm_num)
theorem B1021997 : Blo 535802 1021997 := bbase (se 3 (by rfl) ⟨191624, by rfl⟩ : syracuseStep 1021997 = 383249) (by norm_num)
theorem B2725973 : Blo 535802 2725973 := bbase (se 8 (by rfl) ⟨15972, by rfl⟩ : syracuseStep 2725973 = 31945) (by norm_num)
theorem B727229 : Blo 535802 727229 := bbase (se 3 (by rfl) ⟨136355, by rfl⟩ : syracuseStep 727229 = 272711) (by norm_num)
theorem B1022149 : Blo 535802 1022149 := bbase (se 4 (by rfl) ⟨95826, by rfl⟩ : syracuseStep 1022149 = 191653) (by norm_num)
theorem B17733973 : Blo 535802 17733973 := bbase (se 10 (by rfl) ⟨25977, by rfl⟩ : syracuseStep 17733973 = 51955) (by norm_num)
theorem B1382837 : Blo 535802 1382837 := bbase (se 5 (by rfl) ⟨64820, by rfl⟩ : syracuseStep 1382837 = 129641) (by norm_num)
theorem B1808837 : Blo 535802 1808837 := bbase (se 4 (by rfl) ⟨169578, by rfl⟩ : syracuseStep 1808837 = 339157) (by norm_num)
theorem B1022453 : Blo 535802 1022453 := bbase (se 5 (by rfl) ⟨47927, by rfl⟩ : syracuseStep 1022453 = 95855) (by norm_num)
theorem B596485 : Blo 535802 596485 := bbase (se 4 (by rfl) ⟨55920, by rfl⟩ : syracuseStep 596485 = 111841) (by norm_num)
theorem B4659797 : Blo 535802 4659797 := bbase (se 8 (by rfl) ⟨27303, by rfl⟩ : syracuseStep 4659797 = 54607) (by norm_num)
theorem B2038405 : Blo 535802 2038405 := bbase (se 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) (by norm_num)
theorem B5872277 : Blo 535802 5872277 := bbase (se 6 (by rfl) ⟨137631, by rfl⟩ : syracuseStep 5872277 = 275263) (by norm_num)
theorem B858941 : Blo 535802 858941 := bbase (se 3 (by rfl) ⟨161051, by rfl⟩ : syracuseStep 858941 = 322103) (by norm_num)
theorem B1809269 : Blo 535802 1809269 := bbase (se 5 (by rfl) ⟨84809, by rfl⟩ : syracuseStep 1809269 = 169619) (by norm_num)
theorem B2038709 : Blo 535802 2038709 := bbase (se 5 (by rfl) ⟨95564, by rfl⟩ : syracuseStep 2038709 = 191129) (by norm_num)
theorem B859133 : Blo 535802 859133 := bbase (se 3 (by rfl) ⟨161087, by rfl⟩ : syracuseStep 859133 = 322175) (by norm_num)
theorem B1448965 : Blo 535802 1448965 := bbase (se 4 (by rfl) ⟨135840, by rfl⟩ : syracuseStep 1448965 = 271681) (by norm_num)
theorem B859261 : Blo 535802 859261 := bbase (se 3 (by rfl) ⟨161111, by rfl⟩ : syracuseStep 859261 = 322223) (by norm_num)
theorem B1383637 : Blo 535802 1383637 := bbase (se 7 (by rfl) ⟨16214, by rfl⟩ : syracuseStep 1383637 = 32429) (by norm_num)
theorem B1023205 : Blo 535802 1023205 := bbase (se 4 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 1023205 = 191851) (by norm_num)
theorem B1809701 : Blo 535802 1809701 := bbase (se 4 (by rfl) ⟨169659, by rfl⟩ : syracuseStep 1809701 = 339319) (by norm_num)
theorem B23928149 : Blo 535802 23928149 := bbase (se 11 (by rfl) ⟨17525, by rfl⟩ : syracuseStep 23928149 = 35051) (by norm_num)
theorem B2727269 : Blo 535802 2727269 := bbase (se 4 (by rfl) ⟨255681, by rfl⟩ : syracuseStep 2727269 = 511363) (by norm_num)
theorem B1023349 : Blo 535802 1023349 := bbase (se 5 (by rfl) ⟨47969, by rfl⟩ : syracuseStep 1023349 = 95939) (by norm_num)
theorem B2334197 : Blo 535802 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B1383925 : Blo 535802 1383925 := bbase (se 5 (by rfl) ⟨64871, by rfl⟩ : syracuseStep 1383925 = 129743) (by norm_num)
theorem B1023509 : Blo 535802 1023509 := bbase (se 6 (by rfl) ⟨23988, by rfl⟩ : syracuseStep 1023509 = 47977) (by norm_num)
theorem B2367029 : Blo 535802 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B1023653 : Blo 535802 1023653 := bbase (se 4 (by rfl) ⟨95967, by rfl⟩ : syracuseStep 1023653 = 191935) (by norm_num)
theorem B1089221 : Blo 535802 1089221 := bbase (se 4 (by rfl) ⟨102114, by rfl⟩ : syracuseStep 1089221 = 204229) (by norm_num)
theorem B1810133 : Blo 535802 1810133 := bbase (se 7 (by rfl) ⟨21212, by rfl⟩ : syracuseStep 1810133 = 42425) (by norm_num)
theorem B859901 : Blo 535802 859901 := bbase (se 3 (by rfl) ⟨161231, by rfl⟩ : syracuseStep 859901 = 322463) (by norm_num)
theorem B4071221 : Blo 535802 4071221 := bbase (se 5 (by rfl) ⟨190838, by rfl⟩ : syracuseStep 4071221 = 381677) (by norm_num)
theorem B4726613 : Blo 535802 4726613 := bbase (se 9 (by rfl) ⟨13847, by rfl⟩ : syracuseStep 4726613 = 27695) (by norm_num)
theorem B1023941 : Blo 535802 1023941 := bbase (se 4 (by rfl) ⟨95994, by rfl⟩ : syracuseStep 1023941 = 191989) (by norm_num)
theorem B1024093 : Blo 535802 1024093 := bbase (se 3 (by rfl) ⟨192017, by rfl⟩ : syracuseStep 1024093 = 384035) (by norm_num)
theorem B1810565 : Blo 535802 1810565 := bbase (se 4 (by rfl) ⟨169740, by rfl⟩ : syracuseStep 1810565 = 339481) (by norm_num)
theorem B1450133 : Blo 535802 1450133 := bbase (se 6 (by rfl) ⟨33987, by rfl⟩ : syracuseStep 1450133 = 67975) (by norm_num)
theorem B860357 : Blo 535802 860357 := bbase (se 4 (by rfl) ⟨80658, by rfl⟩ : syracuseStep 860357 = 161317) (by norm_num)
theorem B3449141 : Blo 535802 3449141 := bbase (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) (by norm_num)
theorem B1024397 : Blo 535802 1024397 := bbase (se 3 (by rfl) ⟨192074, by rfl⟩ : syracuseStep 1024397 = 384149) (by norm_num)
theorem B860581 : Blo 535802 860581 := bbase (se 4 (by rfl) ⟨80679, by rfl⟩ : syracuseStep 860581 = 161359) (by norm_num)
theorem B1450469 : Blo 535802 1450469 := bbase (se 4 (by rfl) ⟨135981, by rfl⟩ : syracuseStep 1450469 = 271963) (by norm_num)
theorem B860645 : Blo 535802 860645 := bbase (se 4 (by rfl) ⟨80685, by rfl⟩ : syracuseStep 860645 = 161371) (by norm_num)
theorem B2302501 : Blo 535802 2302501 := bbase (se 4 (by rfl) ⟨215859, by rfl⟩ : syracuseStep 2302501 = 431719) (by norm_num)
theorem B1810997 : Blo 535802 1810997 := bbase (se 5 (by rfl) ⟨84890, by rfl⟩ : syracuseStep 1810997 = 169781) (by norm_num)
theorem B860773 : Blo 535802 860773 := bbase (se 4 (by rfl) ⟨80697, by rfl⟩ : syracuseStep 860773 = 161395) (by norm_num)
theorem B2728565 : Blo 535802 2728565 := bbase (se 5 (by rfl) ⟨127901, by rfl⟩ : syracuseStep 2728565 = 255803) (by norm_num)
theorem B1811429 : Blo 535802 1811429 := bbase (se 4 (by rfl) ⟨169821, by rfl⟩ : syracuseStep 1811429 = 339643) (by norm_num)
theorem B2040821 : Blo 535802 2040821 := bbase (se 5 (by rfl) ⟨95663, by rfl⟩ : syracuseStep 2040821 = 191327) (by norm_num)
theorem B2041109 : Blo 535802 2041109 := bbase (se 6 (by rfl) ⟨47838, by rfl⟩ : syracuseStep 2041109 = 95677) (by norm_num)
theorem B763229 : Blo 535802 763229 := bbase (se 3 (by rfl) ⟨143105, by rfl⟩ : syracuseStep 763229 = 286211) (by norm_num)
theorem B1811861 : Blo 535802 1811861 := bbase (se 6 (by rfl) ⟨42465, by rfl⟩ : syracuseStep 1811861 = 84931) (by norm_num)
theorem B3876245 : Blo 535802 3876245 := bbase (se 6 (by rfl) ⟨90849, by rfl⟩ : syracuseStep 3876245 = 181699) (by norm_num)
theorem B1287893 : Blo 535802 1287893 := bbase (se 7 (by rfl) ⟨15092, by rfl⟩ : syracuseStep 1287893 = 30185) (by norm_num)
theorem B2041573 : Blo 535802 2041573 := bbase (se 4 (by rfl) ⟨191397, by rfl⟩ : syracuseStep 2041573 = 382795) (by norm_num)
theorem B861997 : Blo 535802 861997 := bbase (se 3 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 861997 = 323249) (by norm_num)
theorem B1812293 : Blo 535802 1812293 := bbase (se 4 (by rfl) ⟨169902, by rfl⟩ : syracuseStep 1812293 = 339805) (by norm_num)
theorem B2729861 : Blo 535802 2729861 := bbase (se 4 (by rfl) ⟨255924, by rfl⟩ : syracuseStep 2729861 = 511849) (by norm_num)
theorem B1845125 : Blo 535802 1845125 := bbase (se 4 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 1845125 = 345961) (by norm_num)
theorem B1288277 : Blo 535802 1288277 := bbase (se 8 (by rfl) ⟨7548, by rfl⟩ : syracuseStep 1288277 = 15097) (by norm_num)
theorem B5187701 : Blo 535802 5187701 := bbase (se 5 (by rfl) ⟨243173, by rfl⟩ : syracuseStep 5187701 = 486347) (by norm_num)
theorem B1812725 : Blo 535802 1812725 := bbase (se 5 (by rfl) ⟨84971, by rfl⟩ : syracuseStep 1812725 = 169943) (by norm_num)
theorem B3877141 : Blo 535802 3877141 := bbase (se 6 (by rfl) ⟨90870, by rfl⟩ : syracuseStep 3877141 = 181741) (by norm_num)
theorem B2074901 : Blo 535802 2074901 := bbase (se 6 (by rfl) ⟨48630, by rfl⟩ : syracuseStep 2074901 = 97261) (by norm_num)
theorem B1288565 : Blo 535802 1288565 := bbase (se 5 (by rfl) ⟨60401, by rfl⟩ : syracuseStep 1288565 = 120803) (by norm_num)
theorem B993701 : Blo 535802 993701 := bbase (se 4 (by rfl) ⟨93159, by rfl⟩ : syracuseStep 993701 = 186319) (by norm_num)
theorem B2042293 : Blo 535802 2042293 := bbase (se 5 (by rfl) ⟨95732, by rfl⟩ : syracuseStep 2042293 = 191465) (by norm_num)
theorem B862669 : Blo 535802 862669 := bbase (se 3 (by rfl) ⟨161750, by rfl⟩ : syracuseStep 862669 = 323501) (by norm_num)
theorem B1813157 : Blo 535802 1813157 := bbase (se 4 (by rfl) ⟨169983, by rfl⟩ : syracuseStep 1813157 = 339967) (by norm_num)
theorem B2042597 : Blo 535802 2042597 := bbase (se 4 (by rfl) ⟨191493, by rfl⟩ : syracuseStep 2042597 = 382987) (by norm_num)
theorem B764653 : Blo 535802 764653 := bbase (se 3 (by rfl) ⟨143372, by rfl⟩ : syracuseStep 764653 = 286745) (by norm_num)
theorem B2796373 : Blo 535802 2796373 := bbase (se 9 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 2796373 = 16385) (by norm_num)
theorem B1813589 : Blo 535802 1813589 := bbase (se 8 (by rfl) ⟨10626, by rfl⟩ : syracuseStep 1813589 = 21253) (by norm_num)
theorem B2731157 : Blo 535802 2731157 := bbase (se 6 (by rfl) ⟨64011, by rfl⟩ : syracuseStep 2731157 = 128023) (by norm_num)
theorem B1223981 : Blo 535802 1223981 := bbase (se 3 (by rfl) ⟨229496, by rfl⟩ : syracuseStep 1223981 = 458993) (by norm_num)
theorem B765245 : Blo 535802 765245 := bbase (se 3 (by rfl) ⟨143483, by rfl⟩ : syracuseStep 765245 = 286967) (by norm_num)
theorem B4599125 : Blo 535802 4599125 := bbase (se 11 (by rfl) ⟨3368, by rfl⟩ : syracuseStep 4599125 = 6737) (by norm_num)
theorem B1944917 : Blo 535802 1944917 := bbase (se 11 (by rfl) ⟨1424, by rfl⟩ : syracuseStep 1944917 = 2849) (by norm_num)
theorem B765325 : Blo 535802 765325 := bbase (se 3 (by rfl) ⟨143498, by rfl⟩ : syracuseStep 765325 = 286997) (by norm_num)
theorem B2174357 : Blo 535802 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B863669 : Blo 535802 863669 := bbase (se 5 (by rfl) ⟨40484, by rfl⟩ : syracuseStep 863669 = 80969) (by norm_num)
theorem B2305493 : Blo 535802 2305493 := bbase (se 7 (by rfl) ⟨27017, by rfl⟩ : syracuseStep 2305493 = 54035) (by norm_num)
theorem B1814021 : Blo 535802 1814021 := bbase (se 4 (by rfl) ⟨170064, by rfl⟩ : syracuseStep 1814021 = 340129) (by norm_num)
theorem B765445 : Blo 535802 765445 := bbase (se 4 (by rfl) ⟨71760, by rfl⟩ : syracuseStep 765445 = 143521) (by norm_num)
theorem B765541 : Blo 535802 765541 := bbase (se 4 (by rfl) ⟨71769, by rfl⟩ : syracuseStep 765541 = 143539) (by norm_num)
theorem B3059477 : Blo 535802 3059477 := bbase (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) (by norm_num)
theorem B4665205 : Blo 535802 4665205 := bbase (se 5 (by rfl) ⟨218681, by rfl⟩ : syracuseStep 4665205 = 437363) (by norm_num)
theorem B1814453 : Blo 535802 1814453 := bbase (se 5 (by rfl) ⟨85052, by rfl⟩ : syracuseStep 1814453 = 170105) (by norm_num)
theorem B766037 : Blo 535802 766037 := bbase (se 8 (by rfl) ⟨4488, by rfl⟩ : syracuseStep 766037 = 8977) (by norm_num)
theorem B1814885 : Blo 535802 1814885 := bbase (se 4 (by rfl) ⟨170145, by rfl⟩ : syracuseStep 1814885 = 340291) (by norm_num)
theorem B2732453 : Blo 535802 2732453 := bbase (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) (by norm_num)
theorem B1716677 : Blo 535802 1716677 := bbase (se 4 (by rfl) ⟨160938, by rfl⟩ : syracuseStep 1716677 = 321877) (by norm_num)
theorem B1356365 : Blo 535802 1356365 := bbase (se 3 (by rfl) ⟨254318, by rfl⟩ : syracuseStep 1356365 = 508637) (by norm_num)
theorem B1225301 : Blo 535802 1225301 := bbase (se 8 (by rfl) ⟨7179, by rfl⟩ : syracuseStep 1225301 = 14359) (by norm_num)
theorem B9810517 : Blo 535802 9810517 := bbase (se 8 (by rfl) ⟨57483, by rfl⟩ : syracuseStep 9810517 = 114967) (by norm_num)
theorem B766589 : Blo 535802 766589 := bbase (se 3 (by rfl) ⟨143735, by rfl⟩ : syracuseStep 766589 = 287471) (by norm_num)
theorem B602797 : Blo 535802 602797 := bbase (se 3 (by rfl) ⟨113024, by rfl⟩ : syracuseStep 602797 = 226049) (by norm_num)
theorem B602833 : Blo 535802 602833 := bbase (se 2 (by rfl) ⟨226062, by rfl⟩ : syracuseStep 602833 = 452125) (by norm_num)
theorem B602869 : Blo 535802 602869 := bbase (se 5 (by rfl) ⟨28259, by rfl⟩ : syracuseStep 602869 = 56519) (by norm_num)
theorem B1815317 : Blo 535802 1815317 := bbase (se 6 (by rfl) ⟨42546, by rfl⟩ : syracuseStep 1815317 = 85093) (by norm_num)
theorem B602905 : Blo 535802 602905 := bbase (se 2 (by rfl) ⟨226089, by rfl⟩ : syracuseStep 602905 = 452179) (by norm_num)
theorem B2044709 : Blo 535802 2044709 := bbase (se 4 (by rfl) ⟨191691, by rfl⟩ : syracuseStep 2044709 = 383383) (by norm_num)
theorem B602941 : Blo 535802 602941 := bbase (se 3 (by rfl) ⟨113051, by rfl⟩ : syracuseStep 602941 = 226103) (by norm_num)
theorem B602977 : Blo 535802 602977 := bbase (se 2 (by rfl) ⟨226116, by rfl⟩ : syracuseStep 602977 = 452233) (by norm_num)
theorem B603013 : Blo 535802 603013 := bbase (se 4 (by rfl) ⟨56532, by rfl⟩ : syracuseStep 603013 = 113065) (by norm_num)
theorem B1160101 : Blo 535802 1160101 := bbase (se 4 (by rfl) ⟨108759, by rfl⟩ : syracuseStep 1160101 = 217519) (by norm_num)
theorem B1356709 : Blo 535802 1356709 := bbase (se 4 (by rfl) ⟨127191, by rfl⟩ : syracuseStep 1356709 = 254383) (by norm_num)
theorem B603049 : Blo 535802 603049 := bbase (se 2 (by rfl) ⟨226143, by rfl⟩ : syracuseStep 603049 = 452287) (by norm_num)
theorem B603085 : Blo 535802 603085 := bbase (se 3 (by rfl) ⟨113078, by rfl⟩ : syracuseStep 603085 = 226157) (by norm_num)
theorem B603121 : Blo 535802 603121 := bbase (se 2 (by rfl) ⟨226170, by rfl⟩ : syracuseStep 603121 = 452341) (by norm_num)
theorem B1356821 : Blo 535802 1356821 := bbase (se 6 (by rfl) ⟨31800, by rfl⟩ : syracuseStep 1356821 = 63601) (by norm_num)
theorem B603157 : Blo 535802 603157 := bbase (se 6 (by rfl) ⟨14136, by rfl⟩ : syracuseStep 603157 = 28273) (by norm_num)
theorem B603193 : Blo 535802 603193 := bbase (se 2 (by rfl) ⟨226197, by rfl⟩ : syracuseStep 603193 = 452395) (by norm_num)
theorem B2044997 : Blo 535802 2044997 := bbase (se 4 (by rfl) ⟨191718, by rfl⟩ : syracuseStep 2044997 = 383437) (by norm_num)
theorem B603229 : Blo 535802 603229 := bbase (se 3 (by rfl) ⟨113105, by rfl⟩ : syracuseStep 603229 = 226211) (by norm_num)
theorem B603265 : Blo 535802 603265 := bbase (se 2 (by rfl) ⟨226224, by rfl⟩ : syracuseStep 603265 = 452449) (by norm_num)
theorem B603301 : Blo 535802 603301 := bbase (se 4 (by rfl) ⟨56559, by rfl⟩ : syracuseStep 603301 = 113119) (by norm_num)
theorem B1717445 : Blo 535802 1717445 := bbase (se 4 (by rfl) ⟨161010, by rfl⟩ : syracuseStep 1717445 = 322021) (by norm_num)
theorem B1815749 : Blo 535802 1815749 := bbase (se 4 (by rfl) ⟨170226, by rfl⟩ : syracuseStep 1815749 = 340453) (by norm_num)
theorem B603337 : Blo 535802 603337 := bbase (se 2 (by rfl) ⟨226251, by rfl⟩ : syracuseStep 603337 = 452503) (by norm_num)
theorem B1357013 : Blo 535802 1357013 := bbase (se 7 (by rfl) ⟨15902, by rfl⟩ : syracuseStep 1357013 = 31805) (by norm_num)
theorem B603373 : Blo 535802 603373 := bbase (se 3 (by rfl) ⟨113132, by rfl⟩ : syracuseStep 603373 = 226265) (by norm_num)
theorem B603409 : Blo 535802 603409 := bbase (se 2 (by rfl) ⟨226278, by rfl⟩ : syracuseStep 603409 = 452557) (by norm_num)
theorem B603445 : Blo 535802 603445 := bbase (se 5 (by rfl) ⟨28286, by rfl⟩ : syracuseStep 603445 = 56573) (by norm_num)
theorem B603481 : Blo 535802 603481 := bbase (se 2 (by rfl) ⟨226305, by rfl⟩ : syracuseStep 603481 = 452611) (by norm_num)
theorem B1291621 : Blo 535802 1291621 := bbase (se 4 (by rfl) ⟨121089, by rfl⟩ : syracuseStep 1291621 = 242179) (by norm_num)
theorem B767341 : Blo 535802 767341 := bbase (se 3 (by rfl) ⟨143876, by rfl⟩ : syracuseStep 767341 = 287753) (by norm_num)
theorem B603517 : Blo 535802 603517 := bbase (se 3 (by rfl) ⟨113159, by rfl⟩ : syracuseStep 603517 = 226319) (by norm_num)
theorem B603553 : Blo 535802 603553 := bbase (se 2 (by rfl) ⟨226332, by rfl⟩ : syracuseStep 603553 = 452665) (by norm_num)
theorem B603589 : Blo 535802 603589 := bbase (se 4 (by rfl) ⟨56586, by rfl⟩ : syracuseStep 603589 = 113173) (by norm_num)
theorem B603625 : Blo 535802 603625 := bbase (se 2 (by rfl) ⟨226359, by rfl⟩ : syracuseStep 603625 = 452719) (by norm_num)
theorem B603661 : Blo 535802 603661 := bbase (se 3 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 603661 = 226373) (by norm_num)
theorem B1357357 : Blo 535802 1357357 := bbase (se 3 (by rfl) ⟨254504, by rfl⟩ : syracuseStep 1357357 = 509009) (by norm_num)
theorem B603697 : Blo 535802 603697 := bbase (se 2 (by rfl) ⟨226386, by rfl⟩ : syracuseStep 603697 = 452773) (by norm_num)
theorem B603733 : Blo 535802 603733 := bbase (se 8 (by rfl) ⟨3537, by rfl⟩ : syracuseStep 603733 = 7075) (by norm_num)
theorem B1816181 : Blo 535802 1816181 := bbase (se 5 (by rfl) ⟨85133, by rfl⟩ : syracuseStep 1816181 = 170267) (by norm_num)
theorem B603769 : Blo 535802 603769 := bbase (se 2 (by rfl) ⟨226413, by rfl⟩ : syracuseStep 603769 = 452827) (by norm_num)
theorem B1357469 : Blo 535802 1357469 := bbase (se 3 (by rfl) ⟨254525, by rfl⟩ : syracuseStep 1357469 = 509051) (by norm_num)
theorem B603805 : Blo 535802 603805 := bbase (se 3 (by rfl) ⟨113213, by rfl⟩ : syracuseStep 603805 = 226427) (by norm_num)
theorem B603841 : Blo 535802 603841 := bbase (se 2 (by rfl) ⟨226440, by rfl⟩ : syracuseStep 603841 = 452881) (by norm_num)
theorem B1717957 : Blo 535802 1717957 := bbase (se 4 (by rfl) ⟨161058, by rfl⟩ : syracuseStep 1717957 = 322117) (by norm_num)
theorem B603877 : Blo 535802 603877 := bbase (se 4 (by rfl) ⟨56613, by rfl⟩ : syracuseStep 603877 = 113227) (by norm_num)
theorem B603913 : Blo 535802 603913 := bbase (se 2 (by rfl) ⟨226467, by rfl⟩ : syracuseStep 603913 = 452935) (by norm_num)
theorem B603949 : Blo 535802 603949 := bbase (se 3 (by rfl) ⟨113240, by rfl⟩ : syracuseStep 603949 = 226481) (by norm_num)
theorem B603985 : Blo 535802 603985 := bbase (se 2 (by rfl) ⟨226494, by rfl⟩ : syracuseStep 603985 = 452989) (by norm_num)
theorem B1357661 : Blo 535802 1357661 := bbase (se 3 (by rfl) ⟨254561, by rfl⟩ : syracuseStep 1357661 = 509123) (by norm_num)
theorem B2176885 : Blo 535802 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B604021 : Blo 535802 604021 := bbase (se 5 (by rfl) ⟨28313, by rfl⟩ : syracuseStep 604021 = 56627) (by norm_num)
theorem B604057 : Blo 535802 604057 := bbase (se 2 (by rfl) ⟨226521, by rfl⟩ : syracuseStep 604057 = 453043) (by norm_num)
theorem B604093 : Blo 535802 604093 := bbase (se 3 (by rfl) ⟨113267, by rfl⟩ : syracuseStep 604093 = 226535) (by norm_num)
theorem B1292237 : Blo 535802 1292237 := bbase (se 3 (by rfl) ⟨242294, by rfl⟩ : syracuseStep 1292237 = 484589) (by norm_num)
theorem B604129 : Blo 535802 604129 := bbase (se 2 (by rfl) ⟨226548, by rfl⟩ : syracuseStep 604129 = 453097) (by norm_num)
theorem B604165 : Blo 535802 604165 := bbase (se 4 (by rfl) ⟨56640, by rfl⟩ : syracuseStep 604165 = 113281) (by norm_num)
theorem B1816613 : Blo 535802 1816613 := bbase (se 4 (by rfl) ⟨170307, by rfl⟩ : syracuseStep 1816613 = 340615) (by norm_num)
theorem B604201 : Blo 535802 604201 := bbase (se 2 (by rfl) ⟨226575, by rfl⟩ : syracuseStep 604201 = 453151) (by norm_num)
theorem B604237 : Blo 535802 604237 := bbase (se 3 (by rfl) ⟨113294, by rfl⟩ : syracuseStep 604237 = 226589) (by norm_num)
theorem B8697941 : Blo 535802 8697941 := bbase (se 8 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 8697941 = 101929) (by norm_num)
theorem B604273 : Blo 535802 604273 := bbase (se 2 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 604273 = 453205) (by norm_num)
theorem B768133 : Blo 535802 768133 := bbase (se 4 (by rfl) ⟨72012, by rfl⟩ : syracuseStep 768133 = 144025) (by norm_num)
theorem B1292429 : Blo 535802 1292429 := bbase (se 3 (by rfl) ⟨242330, by rfl⟩ : syracuseStep 1292429 = 484661) (by norm_num)
theorem B604309 : Blo 535802 604309 := bbase (se 6 (by rfl) ⟨14163, by rfl⟩ : syracuseStep 604309 = 28327) (by norm_num)
theorem B1358005 : Blo 535802 1358005 := bbase (se 5 (by rfl) ⟨63656, by rfl⟩ : syracuseStep 1358005 = 127313) (by norm_num)
theorem B604345 : Blo 535802 604345 := bbase (se 2 (by rfl) ⟨226629, by rfl⟩ : syracuseStep 604345 = 453259) (by norm_num)
theorem B735437 : Blo 535802 735437 := bbase (se 3 (by rfl) ⟨137894, by rfl⟩ : syracuseStep 735437 = 275789) (by norm_num)
theorem B604381 : Blo 535802 604381 := bbase (se 3 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 604381 = 226643) (by norm_num)
theorem B2046181 : Blo 535802 2046181 := bbase (se 4 (by rfl) ⟨191829, by rfl⟩ : syracuseStep 2046181 = 383659) (by norm_num)
theorem B604417 : Blo 535802 604417 := bbase (se 2 (by rfl) ⟨226656, by rfl⟩ : syracuseStep 604417 = 453313) (by norm_num)
theorem B1358117 : Blo 535802 1358117 := bbase (se 4 (by rfl) ⟨127323, by rfl⟩ : syracuseStep 1358117 = 254647) (by norm_num)
theorem B604453 : Blo 535802 604453 := bbase (se 4 (by rfl) ⟨56667, by rfl⟩ : syracuseStep 604453 = 113335) (by norm_num)
theorem B604489 : Blo 535802 604489 := bbase (se 2 (by rfl) ⟨226683, by rfl⟩ : syracuseStep 604489 = 453367) (by norm_num)
theorem B604525 : Blo 535802 604525 := bbase (se 3 (by rfl) ⟨113348, by rfl⟩ : syracuseStep 604525 = 226697) (by norm_num)
theorem B1227125 : Blo 535802 1227125 := bbase (se 5 (by rfl) ⟨57521, by rfl⟩ : syracuseStep 1227125 = 115043) (by norm_num)
theorem B604561 : Blo 535802 604561 := bbase (se 2 (by rfl) ⟨226710, by rfl⟩ : syracuseStep 604561 = 453421) (by norm_num)
theorem B604597 : Blo 535802 604597 := bbase (se 5 (by rfl) ⟨28340, by rfl⟩ : syracuseStep 604597 = 56681) (by norm_num)
theorem B1817045 : Blo 535802 1817045 := bbase (se 7 (by rfl) ⟨21293, by rfl⟩ : syracuseStep 1817045 = 42587) (by norm_num)
theorem B768469 : Blo 535802 768469 := bbase (se 7 (by rfl) ⟨9005, by rfl⟩ : syracuseStep 768469 = 18011) (by norm_num)
theorem B604633 : Blo 535802 604633 := bbase (se 2 (by rfl) ⟨226737, by rfl⟩ : syracuseStep 604633 = 453475) (by norm_num)
theorem B1358309 : Blo 535802 1358309 := bbase (se 4 (by rfl) ⟨127341, by rfl⟩ : syracuseStep 1358309 = 254683) (by norm_num)
theorem B604669 : Blo 535802 604669 := bbase (se 3 (by rfl) ⟨113375, by rfl⟩ : syracuseStep 604669 = 226751) (by norm_num)
theorem B2046485 : Blo 535802 2046485 := bbase (se 6 (by rfl) ⟨47964, by rfl⟩ : syracuseStep 2046485 = 95929) (by norm_num)
theorem B604705 : Blo 535802 604705 := bbase (se 2 (by rfl) ⟨226764, by rfl⟩ : syracuseStep 604705 = 453529) (by norm_num)
theorem B604741 : Blo 535802 604741 := bbase (se 4 (by rfl) ⟨56694, by rfl⟩ : syracuseStep 604741 = 113389) (by norm_num)
theorem B604777 : Blo 535802 604777 := bbase (se 2 (by rfl) ⟨226791, by rfl⟩ : syracuseStep 604777 = 453583) (by norm_num)
theorem B604813 : Blo 535802 604813 := bbase (se 3 (by rfl) ⟨113402, by rfl⟩ : syracuseStep 604813 = 226805) (by norm_num)
theorem B604849 : Blo 535802 604849 := bbase (se 2 (by rfl) ⟨226818, by rfl⟩ : syracuseStep 604849 = 453637) (by norm_num)
theorem B1293005 : Blo 535802 1293005 := bbase (se 3 (by rfl) ⟨242438, by rfl⟩ : syracuseStep 1293005 = 484877) (by norm_num)
theorem B604885 : Blo 535802 604885 := bbase (se 7 (by rfl) ⟨7088, by rfl⟩ : syracuseStep 604885 = 14177) (by norm_num)
theorem B604921 : Blo 535802 604921 := bbase (se 2 (by rfl) ⟨226845, by rfl⟩ : syracuseStep 604921 = 453691) (by norm_num)
theorem B604957 : Blo 535802 604957 := bbase (se 3 (by rfl) ⟨113429, by rfl⟩ : syracuseStep 604957 = 226859) (by norm_num)
theorem B1358653 : Blo 535802 1358653 := bbase (se 3 (by rfl) ⟨254747, by rfl⟩ : syracuseStep 1358653 = 509495) (by norm_num)
theorem B604993 : Blo 535802 604993 := bbase (se 2 (by rfl) ⟨226872, by rfl⟩ : syracuseStep 604993 = 453745) (by norm_num)
theorem B605029 : Blo 535802 605029 := bbase (se 4 (by rfl) ⟨56721, by rfl⟩ : syracuseStep 605029 = 113443) (by norm_num)
theorem B1817477 : Blo 535802 1817477 := bbase (se 4 (by rfl) ⟨170388, by rfl⟩ : syracuseStep 1817477 = 340777) (by norm_num)
theorem B605065 : Blo 535802 605065 := bbase (se 2 (by rfl) ⟨226899, by rfl⟩ : syracuseStep 605065 = 453799) (by norm_num)
theorem B1031077 : Blo 535802 1031077 := bbase (se 4 (by rfl) ⟨96663, by rfl⟩ : syracuseStep 1031077 = 193327) (by norm_num)
theorem B1358765 : Blo 535802 1358765 := bbase (se 3 (by rfl) ⟨254768, by rfl⟩ : syracuseStep 1358765 = 509537) (by norm_num)
theorem B605101 : Blo 535802 605101 := bbase (se 3 (by rfl) ⟨113456, by rfl⟩ : syracuseStep 605101 = 226913) (by norm_num)
theorem B572341 : Blo 535802 572341 := bbase (se 5 (by rfl) ⟨26828, by rfl⟩ : syracuseStep 572341 = 53657) (by norm_num)
theorem B605137 : Blo 535802 605137 := bbase (se 2 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 605137 = 453853) (by norm_num)
theorem B605173 : Blo 535802 605173 := bbase (se 5 (by rfl) ⟨28367, by rfl⟩ : syracuseStep 605173 = 56735) (by norm_num)
theorem B605209 : Blo 535802 605209 := bbase (se 2 (by rfl) ⟨226953, by rfl⟩ : syracuseStep 605209 = 453907) (by norm_num)
theorem B605245 : Blo 535802 605245 := bbase (se 3 (by rfl) ⟨113483, by rfl⟩ : syracuseStep 605245 = 226967) (by norm_num)
theorem B1293389 : Blo 535802 1293389 := bbase (se 3 (by rfl) ⟨242510, by rfl⟩ : syracuseStep 1293389 = 485021) (by norm_num)
theorem B605281 : Blo 535802 605281 := bbase (se 2 (by rfl) ⟨226980, by rfl⟩ : syracuseStep 605281 = 453961) (by norm_num)
theorem B1358957 : Blo 535802 1358957 := bbase (se 3 (by rfl) ⟨254804, by rfl⟩ : syracuseStep 1358957 = 509609) (by norm_num)
theorem B605317 : Blo 535802 605317 := bbase (se 4 (by rfl) ⟨56748, by rfl⟩ : syracuseStep 605317 = 113497) (by norm_num)
theorem B605353 : Blo 535802 605353 := bbase (se 2 (by rfl) ⟨227007, by rfl⟩ : syracuseStep 605353 = 454015) (by norm_num)
theorem B605389 : Blo 535802 605389 := bbase (se 3 (by rfl) ⟨113510, by rfl⟩ : syracuseStep 605389 = 227021) (by norm_num)
theorem B605425 : Blo 535802 605425 := bbase (se 2 (by rfl) ⟨227034, by rfl⟩ : syracuseStep 605425 = 454069) (by norm_num)
theorem B605461 : Blo 535802 605461 := bbase (se 6 (by rfl) ⟨14190, by rfl⟩ : syracuseStep 605461 = 28381) (by norm_num)
theorem B572717 : Blo 535802 572717 := bbase (se 3 (by rfl) ⟨107384, by rfl⟩ : syracuseStep 572717 = 214769) (by norm_num)
theorem B1817909 : Blo 535802 1817909 := bbase (se 5 (by rfl) ⟨85214, by rfl⟩ : syracuseStep 1817909 = 170429) (by norm_num)
theorem B605497 : Blo 535802 605497 := bbase (se 2 (by rfl) ⟨227061, by rfl⟩ : syracuseStep 605497 = 454123) (by norm_num)
theorem B605533 : Blo 535802 605533 := bbase (se 3 (by rfl) ⟨113537, by rfl⟩ : syracuseStep 605533 = 227075) (by norm_num)
theorem B572789 : Blo 535802 572789 := bbase (se 5 (by rfl) ⟨26849, by rfl⟩ : syracuseStep 572789 = 53699) (by norm_num)
theorem B605569 : Blo 535802 605569 := bbase (se 2 (by rfl) ⟨227088, by rfl⟩ : syracuseStep 605569 = 454177) (by norm_num)
theorem B1719701 : Blo 535802 1719701 := bbase (se 6 (by rfl) ⟨40305, by rfl⟩ : syracuseStep 1719701 = 80611) (by norm_num)
theorem B4078997 : Blo 535802 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B605605 : Blo 535802 605605 := bbase (se 4 (by rfl) ⟨56775, by rfl⟩ : syracuseStep 605605 = 113551) (by norm_num)
theorem B1359301 : Blo 535802 1359301 := bbase (se 4 (by rfl) ⟨127434, by rfl⟩ : syracuseStep 1359301 = 254869) (by norm_num)
theorem B605641 : Blo 535802 605641 := bbase (se 2 (by rfl) ⟨227115, by rfl⟩ : syracuseStep 605641 = 454231) (by norm_num)
theorem B605677 : Blo 535802 605677 := bbase (se 3 (by rfl) ⟨113564, by rfl⟩ : syracuseStep 605677 = 227129) (by norm_num)
theorem B605713 : Blo 535802 605713 := bbase (se 2 (by rfl) ⟨227142, by rfl⟩ : syracuseStep 605713 = 454285) (by norm_num)
theorem B572977 : Blo 535802 572977 := bbase (se 2 (by rfl) ⟨214866, by rfl⟩ : syracuseStep 572977 = 429733) (by norm_num)
theorem B1359413 : Blo 535802 1359413 := bbase (se 5 (by rfl) ⟨63722, by rfl⟩ : syracuseStep 1359413 = 127445) (by norm_num)
theorem B605749 : Blo 535802 605749 := bbase (se 5 (by rfl) ⟨28394, by rfl⟩ : syracuseStep 605749 = 56789) (by norm_num)
theorem B1719893 : Blo 535802 1719893 := bbase (se 8 (by rfl) ⟨10077, by rfl⟩ : syracuseStep 1719893 = 20155) (by norm_num)
theorem B605785 : Blo 535802 605785 := bbase (se 2 (by rfl) ⟨227169, by rfl⟩ : syracuseStep 605785 = 454339) (by norm_num)
theorem B605821 : Blo 535802 605821 := bbase (se 3 (by rfl) ⟨113591, by rfl⟩ : syracuseStep 605821 = 227183) (by norm_num)
theorem B605857 : Blo 535802 605857 := bbase (se 2 (by rfl) ⟨227196, by rfl⟩ : syracuseStep 605857 = 454393) (by norm_num)
theorem B605893 : Blo 535802 605893 := bbase (se 4 (by rfl) ⟨56802, by rfl⟩ : syracuseStep 605893 = 113605) (by norm_num)
theorem B1818341 : Blo 535802 1818341 := bbase (se 4 (by rfl) ⟨170469, by rfl⟩ : syracuseStep 1818341 = 340939) (by norm_num)
theorem B573161 : Blo 535802 573161 := bbase (se 2 (by rfl) ⟨214935, by rfl⟩ : syracuseStep 573161 = 429871) (by norm_num)
theorem B605929 : Blo 535802 605929 := bbase (se 2 (by rfl) ⟨227223, by rfl⟩ : syracuseStep 605929 = 454447) (by norm_num)
theorem B1359605 : Blo 535802 1359605 := bbase (se 5 (by rfl) ⟨63731, by rfl⟩ : syracuseStep 1359605 = 127463) (by norm_num)
theorem B605965 : Blo 535802 605965 := bbase (se 3 (by rfl) ⟨113618, by rfl⟩ : syracuseStep 605965 = 227237) (by norm_num)
theorem B606001 : Blo 535802 606001 := bbase (se 2 (by rfl) ⟨227250, by rfl⟩ : syracuseStep 606001 = 454501) (by norm_num)
theorem B606037 : Blo 535802 606037 := bbase (se 9 (by rfl) ⟨1775, by rfl⟩ : syracuseStep 606037 = 3551) (by norm_num)
theorem B606073 : Blo 535802 606073 := bbase (se 2 (by rfl) ⟨227277, by rfl⟩ : syracuseStep 606073 = 454555) (by norm_num)
theorem B606109 : Blo 535802 606109 := bbase (se 3 (by rfl) ⟨113645, by rfl⟩ : syracuseStep 606109 = 227291) (by norm_num)
theorem B1228733 : Blo 535802 1228733 := bbase (se 3 (by rfl) ⟨230387, by rfl⟩ : syracuseStep 1228733 = 460775) (by norm_num)
theorem B606145 : Blo 535802 606145 := bbase (se 2 (by rfl) ⟨227304, by rfl⟩ : syracuseStep 606145 = 454609) (by norm_num)
theorem B606181 : Blo 535802 606181 := bbase (se 4 (by rfl) ⟨56829, by rfl⟩ : syracuseStep 606181 = 113659) (by norm_num)
theorem B606217 : Blo 535802 606217 := bbase (se 2 (by rfl) ⟨227331, by rfl⟩ : syracuseStep 606217 = 454663) (by norm_num)
theorem B606253 : Blo 535802 606253 := bbase (se 3 (by rfl) ⟨113672, by rfl⟩ : syracuseStep 606253 = 227345) (by norm_num)
theorem B1359949 : Blo 535802 1359949 := bbase (se 3 (by rfl) ⟨254990, by rfl⟩ : syracuseStep 1359949 = 509981) (by norm_num)
theorem B606289 : Blo 535802 606289 := bbase (se 2 (by rfl) ⟨227358, by rfl⟩ : syracuseStep 606289 = 454717) (by norm_num)
theorem B606325 : Blo 535802 606325 := bbase (se 5 (by rfl) ⟨28421, by rfl⟩ : syracuseStep 606325 = 56843) (by norm_num)
theorem B1818773 : Blo 535802 1818773 := bbase (se 6 (by rfl) ⟨42627, by rfl⟩ : syracuseStep 1818773 = 85255) (by norm_num)
theorem B606361 : Blo 535802 606361 := bbase (se 2 (by rfl) ⟨227385, by rfl⟩ : syracuseStep 606361 = 454771) (by norm_num)
theorem B1360061 : Blo 535802 1360061 := bbase (se 3 (by rfl) ⟨255011, by rfl⟩ : syracuseStep 1360061 = 510023) (by norm_num)
theorem B606397 : Blo 535802 606397 := bbase (se 3 (by rfl) ⟨113699, by rfl⟩ : syracuseStep 606397 = 227399) (by norm_num)
theorem B3457237 : Blo 535802 3457237 := bbase (se 7 (by rfl) ⟨40514, by rfl⟩ : syracuseStep 3457237 = 81029) (by norm_num)
theorem B606433 : Blo 535802 606433 := bbase (se 2 (by rfl) ⟨227412, by rfl⟩ : syracuseStep 606433 = 454825) (by norm_num)
theorem B606469 : Blo 535802 606469 := bbase (se 4 (by rfl) ⟨56856, by rfl⟩ : syracuseStep 606469 = 113713) (by norm_num)
theorem B606505 : Blo 535802 606505 := bbase (se 2 (by rfl) ⟨227439, by rfl⟩ : syracuseStep 606505 = 454879) (by norm_num)
theorem B606541 : Blo 535802 606541 := bbase (se 3 (by rfl) ⟨113726, by rfl⟩ : syracuseStep 606541 = 227453) (by norm_num)
theorem B606577 : Blo 535802 606577 := bbase (se 2 (by rfl) ⟨227466, by rfl⟩ : syracuseStep 606577 = 454933) (by norm_num)
theorem B1360253 : Blo 535802 1360253 := bbase (se 3 (by rfl) ⟨255047, by rfl⟩ : syracuseStep 1360253 = 510095) (by norm_num)
theorem B606613 : Blo 535802 606613 := bbase (se 6 (by rfl) ⟨14217, by rfl⟩ : syracuseStep 606613 = 28435) (by norm_num)
theorem B606649 : Blo 535802 606649 := bbase (se 2 (by rfl) ⟨227493, by rfl⟩ : syracuseStep 606649 = 454987) (by norm_num)
theorem B1229261 : Blo 535802 1229261 := bbase (se 3 (by rfl) ⟨230486, by rfl⟩ : syracuseStep 1229261 = 460973) (by norm_num)
theorem B573913 : Blo 535802 573913 := bbase (se 2 (by rfl) ⟨215217, by rfl⟩ : syracuseStep 573913 = 430435) (by norm_num)
theorem B606685 : Blo 535802 606685 := bbase (se 3 (by rfl) ⟨113753, by rfl⟩ : syracuseStep 606685 = 227507) (by norm_num)
theorem B606721 : Blo 535802 606721 := bbase (se 2 (by rfl) ⟨227520, by rfl⟩ : syracuseStep 606721 = 455041) (by norm_num)
theorem B573985 : Blo 535802 573985 := bbase (se 2 (by rfl) ⟨215244, by rfl⟩ : syracuseStep 573985 = 430489) (by norm_num)
theorem B606757 : Blo 535802 606757 := bbase (se 4 (by rfl) ⟨56883, by rfl⟩ : syracuseStep 606757 = 113767) (by norm_num)
theorem B1819205 : Blo 535802 1819205 := bbase (se 4 (by rfl) ⟨170550, by rfl⟩ : syracuseStep 1819205 = 341101) (by norm_num)
theorem B606793 : Blo 535802 606793 := bbase (se 2 (by rfl) ⟨227547, by rfl⟩ : syracuseStep 606793 = 455095) (by norm_num)
theorem B2048597 : Blo 535802 2048597 := bbase (se 8 (by rfl) ⟨12003, by rfl⟩ : syracuseStep 2048597 = 24007) (by norm_num)
theorem B1458773 : Blo 535802 1458773 := bbase (se 8 (by rfl) ⟨8547, by rfl⟩ : syracuseStep 1458773 = 17095) (by norm_num)
theorem B606829 : Blo 535802 606829 := bbase (se 3 (by rfl) ⟨113780, by rfl⟩ : syracuseStep 606829 = 227561) (by norm_num)
theorem B606865 : Blo 535802 606865 := bbase (se 2 (by rfl) ⟨227574, by rfl⟩ : syracuseStep 606865 = 455149) (by norm_num)
theorem B606901 : Blo 535802 606901 := bbase (se 5 (by rfl) ⟨28448, by rfl⟩ : syracuseStep 606901 = 56897) (by norm_num)
theorem B1360597 : Blo 535802 1360597 := bbase (se 7 (by rfl) ⟨15944, by rfl⟩ : syracuseStep 1360597 = 31889) (by norm_num)
theorem B574165 : Blo 535802 574165 := bbase (se 7 (by rfl) ⟨6728, by rfl⟩ : syracuseStep 574165 = 13457) (by norm_num)
theorem B606937 : Blo 535802 606937 := bbase (se 2 (by rfl) ⟨227601, by rfl⟩ : syracuseStep 606937 = 455203) (by norm_num)
theorem B606973 : Blo 535802 606973 := bbase (se 3 (by rfl) ⟨113807, by rfl⟩ : syracuseStep 606973 = 227615) (by norm_num)
theorem B607009 : Blo 535802 607009 := bbase (se 2 (by rfl) ⟨227628, by rfl⟩ : syracuseStep 607009 = 455257) (by norm_num)
theorem B1295149 : Blo 535802 1295149 := bbase (se 3 (by rfl) ⟨242840, by rfl⟩ : syracuseStep 1295149 = 485681) (by norm_num)
theorem B967477 : Blo 535802 967477 := bbase (se 5 (by rfl) ⟨45350, by rfl⟩ : syracuseStep 967477 = 90701) (by norm_num)
theorem B1360709 : Blo 535802 1360709 := bbase (se 4 (by rfl) ⟨127566, by rfl⟩ : syracuseStep 1360709 = 255133) (by norm_num)
theorem B607045 : Blo 535802 607045 := bbase (se 4 (by rfl) ⟨56910, by rfl⟩ : syracuseStep 607045 = 113821) (by norm_num)
theorem B607081 : Blo 535802 607081 := bbase (se 2 (by rfl) ⟨227655, by rfl⟩ : syracuseStep 607081 = 455311) (by norm_num)
theorem B2048885 : Blo 535802 2048885 := bbase (se 5 (by rfl) ⟨96041, by rfl⟩ : syracuseStep 2048885 = 192083) (by norm_num)
theorem B803717 : Blo 535802 803717 := bbase (se 4 (by rfl) ⟨75348, by rfl⟩ : syracuseStep 803717 = 150697) (by norm_num)
theorem B934789 : Blo 535802 934789 := bbase (se 4 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 934789 = 175273) (by norm_num)
theorem B607117 : Blo 535802 607117 := bbase (se 3 (by rfl) ⟨113834, by rfl⟩ : syracuseStep 607117 = 227669) (by norm_num)
theorem B803741 : Blo 535802 803741 := bbase (se 3 (by rfl) ⟨150701, by rfl⟩ : syracuseStep 803741 = 301403) (by norm_num)
theorem B607153 : Blo 535802 607153 := bbase (se 2 (by rfl) ⟨227682, by rfl⟩ : syracuseStep 607153 = 455365) (by norm_num)
theorem B803765 : Blo 535802 803765 := bbase (se 5 (by rfl) ⟨37676, by rfl⟩ : syracuseStep 803765 = 75353) (by norm_num)
theorem B803789 : Blo 535802 803789 := bbase (se 3 (by rfl) ⟨150710, by rfl⟩ : syracuseStep 803789 = 301421) (by norm_num)
theorem B607189 : Blo 535802 607189 := bbase (se 7 (by rfl) ⟨7115, by rfl⟩ : syracuseStep 607189 = 14231) (by norm_num)
theorem B803813 : Blo 535802 803813 := bbase (se 4 (by rfl) ⟨75357, by rfl⟩ : syracuseStep 803813 = 150715) (by norm_num)
theorem B1819637 : Blo 535802 1819637 := bbase (se 5 (by rfl) ⟨85295, by rfl⟩ : syracuseStep 1819637 = 170591) (by norm_num)
theorem B607225 : Blo 535802 607225 := bbase (se 2 (by rfl) ⟨227709, by rfl⟩ : syracuseStep 607225 = 455419) (by norm_num)
theorem B803837 : Blo 535802 803837 := bbase (se 3 (by rfl) ⟨150719, by rfl⟩ : syracuseStep 803837 = 301439) (by norm_num)
theorem B1360901 : Blo 535802 1360901 := bbase (se 4 (by rfl) ⟨127584, by rfl⟩ : syracuseStep 1360901 = 255169) (by norm_num)
theorem B803861 : Blo 535802 803861 := bbase (se 6 (by rfl) ⟨18840, by rfl⟩ : syracuseStep 803861 = 37681) (by norm_num)
theorem B607261 : Blo 535802 607261 := bbase (se 3 (by rfl) ⟨113861, by rfl⟩ : syracuseStep 607261 = 227723) (by norm_num)
theorem B803885 : Blo 535802 803885 := bbase (se 3 (by rfl) ⟨150728, by rfl⟩ : syracuseStep 803885 = 301457) (by norm_num)
theorem B803909 : Blo 535802 803909 := bbase (se 4 (by rfl) ⟨75366, by rfl⟩ : syracuseStep 803909 = 150733) (by norm_num)
theorem B803933 : Blo 535802 803933 := bbase (se 3 (by rfl) ⟨150737, by rfl⟩ : syracuseStep 803933 = 301475) (by norm_num)
theorem B803957 : Blo 535802 803957 := bbase (se 5 (by rfl) ⟨37685, by rfl⟩ : syracuseStep 803957 = 75371) (by norm_num)
theorem B803981 : Blo 535802 803981 := bbase (se 3 (by rfl) ⟨150746, by rfl⟩ : syracuseStep 803981 = 301493) (by norm_num)
theorem B574609 : Blo 535802 574609 := bbase (se 2 (by rfl) ⟨215478, by rfl⟩ : syracuseStep 574609 = 430957) (by norm_num)
theorem B804005 : Blo 535802 804005 := bbase (se 4 (by rfl) ⟨75375, by rfl⟩ : syracuseStep 804005 = 150751) (by norm_num)
theorem B804029 : Blo 535802 804029 := bbase (se 3 (by rfl) ⟨150755, by rfl⟩ : syracuseStep 804029 = 301511) (by norm_num)
theorem B804053 : Blo 535802 804053 := bbase (se 7 (by rfl) ⟨9422, by rfl⟩ : syracuseStep 804053 = 18845) (by norm_num)
theorem B967909 : Blo 535802 967909 := bbase (se 4 (by rfl) ⟨90741, by rfl⟩ : syracuseStep 967909 = 181483) (by norm_num)
theorem B804077 : Blo 535802 804077 := bbase (se 3 (by rfl) ⟨150764, by rfl⟩ : syracuseStep 804077 = 301529) (by norm_num)
theorem B804101 : Blo 535802 804101 := bbase (se 4 (by rfl) ⟨75384, by rfl⟩ : syracuseStep 804101 = 150769) (by norm_num)
theorem B574733 : Blo 535802 574733 := bbase (se 3 (by rfl) ⟨107762, by rfl⟩ : syracuseStep 574733 = 215525) (by norm_num)
theorem B804125 : Blo 535802 804125 := bbase (se 3 (by rfl) ⟨150773, by rfl⟩ : syracuseStep 804125 = 301547) (by norm_num)
theorem B804149 : Blo 535802 804149 := bbase (se 5 (by rfl) ⟨37694, by rfl⟩ : syracuseStep 804149 = 75389) (by norm_num)
theorem B804173 : Blo 535802 804173 := bbase (se 3 (by rfl) ⟨150782, by rfl⟩ : syracuseStep 804173 = 301565) (by norm_num)
theorem B1361245 : Blo 535802 1361245 := bbase (se 3 (by rfl) ⟨255233, by rfl⟩ : syracuseStep 1361245 = 510467) (by norm_num)
theorem B804197 : Blo 535802 804197 := bbase (se 4 (by rfl) ⟨75393, by rfl⟩ : syracuseStep 804197 = 150787) (by norm_num)
theorem B968053 : Blo 535802 968053 := bbase (se 5 (by rfl) ⟨45377, by rfl⟩ : syracuseStep 968053 = 90755) (by norm_num)
theorem B804221 : Blo 535802 804221 := bbase (se 3 (by rfl) ⟨150791, by rfl⟩ : syracuseStep 804221 = 301583) (by norm_num)
theorem B804245 : Blo 535802 804245 := bbase (se 6 (by rfl) ⟨18849, by rfl⟩ : syracuseStep 804245 = 37699) (by norm_num)
theorem B1820069 : Blo 535802 1820069 := bbase (se 4 (by rfl) ⟨170631, by rfl⟩ : syracuseStep 1820069 = 341263) (by norm_num)
theorem B804269 : Blo 535802 804269 := bbase (se 3 (by rfl) ⟨150800, by rfl⟩ : syracuseStep 804269 = 301601) (by norm_num)
theorem B804293 : Blo 535802 804293 := bbase (se 4 (by rfl) ⟨75402, by rfl⟩ : syracuseStep 804293 = 150805) (by norm_num)
theorem B1361357 : Blo 535802 1361357 := bbase (se 3 (by rfl) ⟨255254, by rfl⟩ : syracuseStep 1361357 = 510509) (by norm_num)
theorem B804317 : Blo 535802 804317 := bbase (se 3 (by rfl) ⟨150809, by rfl⟩ : syracuseStep 804317 = 301619) (by norm_num)
theorem B804341 : Blo 535802 804341 := bbase (se 5 (by rfl) ⟨37703, by rfl⟩ : syracuseStep 804341 = 75407) (by norm_num)
theorem B574985 : Blo 535802 574985 := bbase (se 2 (by rfl) ⟨215619, by rfl⟩ : syracuseStep 574985 = 431239) (by norm_num)
theorem B804365 : Blo 535802 804365 := bbase (se 3 (by rfl) ⟨150818, by rfl⟩ : syracuseStep 804365 = 301637) (by norm_num)
theorem B738829 : Blo 535802 738829 := bbase (se 3 (by rfl) ⟨138530, by rfl⟩ : syracuseStep 738829 = 277061) (by norm_num)
theorem B804389 : Blo 535802 804389 := bbase (se 4 (by rfl) ⟨75411, by rfl⟩ : syracuseStep 804389 = 150823) (by norm_num)
theorem B804413 : Blo 535802 804413 := bbase (se 3 (by rfl) ⟨150827, by rfl⟩ : syracuseStep 804413 = 301655) (by norm_num)
theorem B968269 : Blo 535802 968269 := bbase (se 3 (by rfl) ⟨181550, by rfl⟩ : syracuseStep 968269 = 363101) (by norm_num)
theorem B804437 : Blo 535802 804437 := bbase (se 8 (by rfl) ⟨4713, by rfl⟩ : syracuseStep 804437 = 9427) (by norm_num)
theorem B804461 : Blo 535802 804461 := bbase (se 3 (by rfl) ⟨150836, by rfl⟩ : syracuseStep 804461 = 301673) (by norm_num)
theorem B804485 : Blo 535802 804485 := bbase (se 4 (by rfl) ⟨75420, by rfl⟩ : syracuseStep 804485 = 150841) (by norm_num)
theorem B1361549 : Blo 535802 1361549 := bbase (se 3 (by rfl) ⟨255290, by rfl⟩ : syracuseStep 1361549 = 510581) (by norm_num)
theorem B804509 : Blo 535802 804509 := bbase (se 3 (by rfl) ⟨150845, by rfl⟩ : syracuseStep 804509 = 301691) (by norm_num)
theorem B804533 : Blo 535802 804533 := bbase (se 5 (by rfl) ⟨37712, by rfl⟩ : syracuseStep 804533 = 75425) (by norm_num)
theorem B804557 : Blo 535802 804557 := bbase (se 3 (by rfl) ⟨150854, by rfl⟩ : syracuseStep 804557 = 301709) (by norm_num)
theorem B804581 : Blo 535802 804581 := bbase (se 4 (by rfl) ⟨75429, by rfl⟩ : syracuseStep 804581 = 150859) (by norm_num)
theorem B804605 : Blo 535802 804605 := bbase (se 3 (by rfl) ⟨150863, by rfl⟩ : syracuseStep 804605 = 301727) (by norm_num)
theorem B804629 : Blo 535802 804629 := bbase (se 6 (by rfl) ⟨18858, by rfl⟩ : syracuseStep 804629 = 37717) (by norm_num)
theorem B1296157 : Blo 535802 1296157 := bbase (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) (by norm_num)
theorem B804653 : Blo 535802 804653 := bbase (se 3 (by rfl) ⟨150872, by rfl⟩ : syracuseStep 804653 = 301745) (by norm_num)
theorem B804677 : Blo 535802 804677 := bbase (se 4 (by rfl) ⟨75438, by rfl⟩ : syracuseStep 804677 = 150877) (by norm_num)
theorem B1820501 : Blo 535802 1820501 := bbase (se 9 (by rfl) ⟨5333, by rfl⟩ : syracuseStep 1820501 = 10667) (by norm_num)
theorem B804701 : Blo 535802 804701 := bbase (se 3 (by rfl) ⟨150881, by rfl⟩ : syracuseStep 804701 = 301763) (by norm_num)
theorem B804725 : Blo 535802 804725 := bbase (se 5 (by rfl) ⟨37721, by rfl⟩ : syracuseStep 804725 = 75443) (by norm_num)
theorem B1296253 : Blo 535802 1296253 := bbase (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) (by norm_num)
theorem B804749 : Blo 535802 804749 := bbase (se 3 (by rfl) ⟨150890, by rfl⟩ : syracuseStep 804749 = 301781) (by norm_num)
theorem B804773 : Blo 535802 804773 := bbase (se 4 (by rfl) ⟨75447, by rfl⟩ : syracuseStep 804773 = 150895) (by norm_num)
theorem B804797 : Blo 535802 804797 := bbase (se 3 (by rfl) ⟨150899, by rfl⟩ : syracuseStep 804797 = 301799) (by norm_num)
theorem B575429 : Blo 535802 575429 := bbase (se 4 (by rfl) ⟨53946, by rfl⟩ : syracuseStep 575429 = 107893) (by norm_num)
theorem B804821 : Blo 535802 804821 := bbase (se 7 (by rfl) ⟨9431, by rfl⟩ : syracuseStep 804821 = 18863) (by norm_num)
theorem B1361893 : Blo 535802 1361893 := bbase (se 4 (by rfl) ⟨127677, by rfl⟩ : syracuseStep 1361893 = 255355) (by norm_num)
theorem B804845 : Blo 535802 804845 := bbase (se 3 (by rfl) ⟨150908, by rfl⟩ : syracuseStep 804845 = 301817) (by norm_num)
theorem B804869 : Blo 535802 804869 := bbase (se 4 (by rfl) ⟨75456, by rfl⟩ : syracuseStep 804869 = 150913) (by norm_num)
theorem B804893 : Blo 535802 804893 := bbase (se 3 (by rfl) ⟨150917, by rfl⟩ : syracuseStep 804893 = 301835) (by norm_num)
theorem B804917 : Blo 535802 804917 := bbase (se 5 (by rfl) ⟨37730, by rfl⟩ : syracuseStep 804917 = 75461) (by norm_num)
theorem B804941 : Blo 535802 804941 := bbase (se 3 (by rfl) ⟨150926, by rfl⟩ : syracuseStep 804941 = 301853) (by norm_num)
theorem B1362005 : Blo 535802 1362005 := bbase (se 8 (by rfl) ⟨7980, by rfl⟩ : syracuseStep 1362005 = 15961) (by norm_num)
theorem B804965 : Blo 535802 804965 := bbase (se 4 (by rfl) ⟨75465, by rfl⟩ : syracuseStep 804965 = 150931) (by norm_num)
theorem B804989 : Blo 535802 804989 := bbase (se 3 (by rfl) ⟨150935, by rfl⟩ : syracuseStep 804989 = 301871) (by norm_num)
theorem B805013 : Blo 535802 805013 := bbase (se 6 (by rfl) ⟨18867, by rfl⟩ : syracuseStep 805013 = 37735) (by norm_num)
theorem B968861 : Blo 535802 968861 := bbase (se 3 (by rfl) ⟨181661, by rfl⟩ : syracuseStep 968861 = 363323) (by norm_num)
theorem B1231013 : Blo 535802 1231013 := bbase (se 4 (by rfl) ⟨115407, by rfl⟩ : syracuseStep 1231013 = 230815) (by norm_num)
theorem B805037 : Blo 535802 805037 := bbase (se 3 (by rfl) ⟨150944, by rfl⟩ : syracuseStep 805037 = 301889) (by norm_num)
theorem B575677 : Blo 535802 575677 := bbase (se 3 (by rfl) ⟨107939, by rfl⟩ : syracuseStep 575677 = 215879) (by norm_num)
theorem B805061 : Blo 535802 805061 := bbase (se 4 (by rfl) ⟨75474, by rfl⟩ : syracuseStep 805061 = 150949) (by norm_num)
theorem B805085 : Blo 535802 805085 := bbase (se 3 (by rfl) ⟨150953, by rfl⟩ : syracuseStep 805085 = 301907) (by norm_num)
theorem B805109 : Blo 535802 805109 := bbase (se 5 (by rfl) ⟨37739, by rfl⟩ : syracuseStep 805109 = 75479) (by norm_num)
theorem B1820933 : Blo 535802 1820933 := bbase (se 4 (by rfl) ⟨170712, by rfl⟩ : syracuseStep 1820933 = 341425) (by norm_num)
theorem B805133 : Blo 535802 805133 := bbase (se 3 (by rfl) ⟨150962, by rfl⟩ : syracuseStep 805133 = 301925) (by norm_num)
theorem B1362197 : Blo 535802 1362197 := bbase (se 6 (by rfl) ⟨31926, by rfl⟩ : syracuseStep 1362197 = 63853) (by norm_num)
theorem B805157 : Blo 535802 805157 := bbase (se 4 (by rfl) ⟨75483, by rfl⟩ : syracuseStep 805157 = 150967) (by norm_num)
theorem B805181 : Blo 535802 805181 := bbase (se 3 (by rfl) ⟨150971, by rfl⟩ : syracuseStep 805181 = 301943) (by norm_num)
theorem B805205 : Blo 535802 805205 := bbase (se 10 (by rfl) ⟨1179, by rfl⟩ : syracuseStep 805205 = 2359) (by norm_num)
theorem B805229 : Blo 535802 805229 := bbase (se 3 (by rfl) ⟨150980, by rfl⟩ : syracuseStep 805229 = 301961) (by norm_num)
theorem B969077 : Blo 535802 969077 := bbase (se 5 (by rfl) ⟨45425, by rfl⟩ : syracuseStep 969077 = 90851) (by norm_num)
theorem B805253 : Blo 535802 805253 := bbase (se 4 (by rfl) ⟨75492, by rfl⟩ : syracuseStep 805253 = 150985) (by norm_num)
theorem B1296773 : Blo 535802 1296773 := bbase (se 4 (by rfl) ⟨121572, by rfl⟩ : syracuseStep 1296773 = 243145) (by norm_num)
theorem B805277 : Blo 535802 805277 := bbase (se 3 (by rfl) ⟨150989, by rfl⟩ : syracuseStep 805277 = 301979) (by norm_num)
theorem B805301 : Blo 535802 805301 := bbase (se 5 (by rfl) ⟨37748, by rfl⟩ : syracuseStep 805301 = 75497) (by norm_num)
theorem B805325 : Blo 535802 805325 := bbase (se 3 (by rfl) ⟨150998, by rfl⟩ : syracuseStep 805325 = 301997) (by norm_num)
theorem B805349 : Blo 535802 805349 := bbase (se 4 (by rfl) ⟨75501, by rfl⟩ : syracuseStep 805349 = 151003) (by norm_num)
theorem B805373 : Blo 535802 805373 := bbase (se 3 (by rfl) ⟨151007, by rfl⟩ : syracuseStep 805373 = 302015) (by norm_num)
theorem B805397 : Blo 535802 805397 := bbase (se 6 (by rfl) ⟨18876, by rfl⟩ : syracuseStep 805397 = 37753) (by norm_num)
theorem B805421 : Blo 535802 805421 := bbase (se 3 (by rfl) ⟨151016, by rfl⟩ : syracuseStep 805421 = 302033) (by norm_num)
theorem B805445 : Blo 535802 805445 := bbase (se 4 (by rfl) ⟨75510, by rfl⟩ : syracuseStep 805445 = 151021) (by norm_num)
theorem B543313 : Blo 535802 543313 := bbase (se 2 (by rfl) ⟨203742, by rfl⟩ : syracuseStep 543313 = 407485) (by norm_num)
theorem B805469 : Blo 535802 805469 := bbase (se 3 (by rfl) ⟨151025, by rfl⟩ : syracuseStep 805469 = 302051) (by norm_num)
theorem B1362541 : Blo 535802 1362541 := bbase (se 3 (by rfl) ⟨255476, by rfl⟩ : syracuseStep 1362541 = 510953) (by norm_num)
theorem B805493 : Blo 535802 805493 := bbase (se 5 (by rfl) ⟨37757, by rfl⟩ : syracuseStep 805493 = 75515) (by norm_num)
theorem B576121 : Blo 535802 576121 := bbase (se 2 (by rfl) ⟨216045, by rfl⟩ : syracuseStep 576121 = 432091) (by norm_num)
theorem B805517 : Blo 535802 805517 := bbase (se 3 (by rfl) ⟨151034, by rfl⟩ : syracuseStep 805517 = 302069) (by norm_num)
theorem B969365 : Blo 535802 969365 := bbase (se 6 (by rfl) ⟨22719, by rfl⟩ : syracuseStep 969365 = 45439) (by norm_num)
theorem B805541 : Blo 535802 805541 := bbase (se 4 (by rfl) ⟨75519, by rfl⟩ : syracuseStep 805541 = 151039) (by norm_num)
theorem B576181 : Blo 535802 576181 := bbase (se 5 (by rfl) ⟨27008, by rfl⟩ : syracuseStep 576181 = 54017) (by norm_num)
theorem B1821365 : Blo 535802 1821365 := bbase (se 5 (by rfl) ⟨85376, by rfl⟩ : syracuseStep 1821365 = 170753) (by norm_num)
theorem B805565 : Blo 535802 805565 := bbase (se 3 (by rfl) ⟨151043, by rfl⟩ : syracuseStep 805565 = 302087) (by norm_num)
theorem B805589 : Blo 535802 805589 := bbase (se 7 (by rfl) ⟨9440, by rfl⟩ : syracuseStep 805589 = 18881) (by norm_num)
theorem B1362653 : Blo 535802 1362653 := bbase (se 3 (by rfl) ⟨255497, by rfl⟩ : syracuseStep 1362653 = 510995) (by norm_num)
theorem B805613 : Blo 535802 805613 := bbase (se 3 (by rfl) ⟨151052, by rfl⟩ : syracuseStep 805613 = 302105) (by norm_num)
theorem B805637 : Blo 535802 805637 := bbase (se 4 (by rfl) ⟨75528, by rfl⟩ : syracuseStep 805637 = 151057) (by norm_num)
theorem B805661 : Blo 535802 805661 := bbase (se 3 (by rfl) ⟨151061, by rfl⟩ : syracuseStep 805661 = 302123) (by norm_num)
theorem B805685 : Blo 535802 805685 := bbase (se 5 (by rfl) ⟨37766, by rfl⟩ : syracuseStep 805685 = 75533) (by norm_num)
theorem B805709 : Blo 535802 805709 := bbase (se 3 (by rfl) ⟨151070, by rfl⟩ : syracuseStep 805709 = 302141) (by norm_num)
theorem B805733 : Blo 535802 805733 := bbase (se 4 (by rfl) ⟨75537, by rfl⟩ : syracuseStep 805733 = 151075) (by norm_num)
theorem B805757 : Blo 535802 805757 := bbase (se 3 (by rfl) ⟨151079, by rfl⟩ : syracuseStep 805757 = 302159) (by norm_num)
theorem B805781 : Blo 535802 805781 := bbase (se 6 (by rfl) ⟨18885, by rfl⟩ : syracuseStep 805781 = 37771) (by norm_num)
theorem B1362845 : Blo 535802 1362845 := bbase (se 3 (by rfl) ⟨255533, by rfl⟩ : syracuseStep 1362845 = 511067) (by norm_num)
theorem B805805 : Blo 535802 805805 := bbase (se 3 (by rfl) ⟨151088, by rfl⟩ : syracuseStep 805805 = 302177) (by norm_num)
theorem B805829 : Blo 535802 805829 := bbase (se 4 (by rfl) ⟨75546, by rfl⟩ : syracuseStep 805829 = 151093) (by norm_num)
theorem B1264589 : Blo 535802 1264589 := bbase (se 3 (by rfl) ⟨237110, by rfl⟩ : syracuseStep 1264589 = 474221) (by norm_num)
theorem B805853 : Blo 535802 805853 := bbase (se 3 (by rfl) ⟨151097, by rfl⟩ : syracuseStep 805853 = 302195) (by norm_num)
theorem B805877 : Blo 535802 805877 := bbase (se 5 (by rfl) ⟨37775, by rfl⟩ : syracuseStep 805877 = 75551) (by norm_num)
theorem B904189 : Blo 535802 904189 := bbase (se 3 (by rfl) ⟨169535, by rfl⟩ : syracuseStep 904189 = 339071) (by norm_num)
theorem B1526789 : Blo 535802 1526789 := bbase (se 4 (by rfl) ⟨143136, by rfl⟩ : syracuseStep 1526789 = 286273) (by norm_num)
theorem B805901 : Blo 535802 805901 := bbase (se 3 (by rfl) ⟨151106, by rfl⟩ : syracuseStep 805901 = 302213) (by norm_num)
theorem B805925 : Blo 535802 805925 := bbase (se 4 (by rfl) ⟨75555, by rfl⟩ : syracuseStep 805925 = 151111) (by norm_num)
theorem B805949 : Blo 535802 805949 := bbase (se 3 (by rfl) ⟨151115, by rfl⟩ : syracuseStep 805949 = 302231) (by norm_num)
theorem B904277 : Blo 535802 904277 := bbase (se 8 (by rfl) ⟨5298, by rfl⟩ : syracuseStep 904277 = 10597) (by norm_num)
theorem B805973 : Blo 535802 805973 := bbase (se 8 (by rfl) ⟨4722, by rfl⟩ : syracuseStep 805973 = 9445) (by norm_num)
theorem B1723493 : Blo 535802 1723493 := bbase (se 4 (by rfl) ⟨161577, by rfl⟩ : syracuseStep 1723493 = 323155) (by norm_num)
theorem B1821797 : Blo 535802 1821797 := bbase (se 4 (by rfl) ⟨170793, by rfl⟩ : syracuseStep 1821797 = 341587) (by norm_num)
theorem B805997 : Blo 535802 805997 := bbase (se 3 (by rfl) ⟨151124, by rfl⟩ : syracuseStep 805997 = 302249) (by norm_num)
theorem B806021 : Blo 535802 806021 := bbase (se 4 (by rfl) ⟨75564, by rfl⟩ : syracuseStep 806021 = 151129) (by norm_num)
theorem B806045 : Blo 535802 806045 := bbase (se 3 (by rfl) ⟨151133, by rfl⟩ : syracuseStep 806045 = 302267) (by norm_num)
theorem B806069 : Blo 535802 806069 := bbase (se 5 (by rfl) ⟨37784, by rfl⟩ : syracuseStep 806069 = 75569) (by norm_num)
theorem B806093 : Blo 535802 806093 := bbase (se 3 (by rfl) ⟨151142, by rfl⟩ : syracuseStep 806093 = 302285) (by norm_num)
theorem B904405 : Blo 535802 904405 := bbase (se 7 (by rfl) ⟨10598, by rfl⟩ : syracuseStep 904405 = 21197) (by norm_num)
theorem B4607189 : Blo 535802 4607189 := bbase (se 7 (by rfl) ⟨53990, by rfl⟩ : syracuseStep 4607189 = 107981) (by norm_num)
theorem B806117 : Blo 535802 806117 := bbase (se 4 (by rfl) ⟨75573, by rfl⟩ : syracuseStep 806117 = 151147) (by norm_num)
theorem B1363189 : Blo 535802 1363189 := bbase (se 5 (by rfl) ⟨63899, by rfl⟩ : syracuseStep 1363189 = 127799) (by norm_num)
theorem B806141 : Blo 535802 806141 := bbase (se 3 (by rfl) ⟨151151, by rfl⟩ : syracuseStep 806141 = 302303) (by norm_num)
theorem B806165 : Blo 535802 806165 := bbase (se 6 (by rfl) ⟨18894, by rfl⟩ : syracuseStep 806165 = 37789) (by norm_num)
theorem B904493 : Blo 535802 904493 := bbase (se 3 (by rfl) ⟨169592, by rfl⟩ : syracuseStep 904493 = 339185) (by norm_num)
theorem B806189 : Blo 535802 806189 := bbase (se 3 (by rfl) ⟨151160, by rfl⟩ : syracuseStep 806189 = 302321) (by norm_num)
theorem B806213 : Blo 535802 806213 := bbase (se 4 (by rfl) ⟨75582, by rfl⟩ : syracuseStep 806213 = 151165) (by norm_num)
theorem B1035605 : Blo 535802 1035605 := bbase (se 11 (by rfl) ⟨758, by rfl⟩ : syracuseStep 1035605 = 1517) (by norm_num)
theorem B806237 : Blo 535802 806237 := bbase (se 3 (by rfl) ⟨151169, by rfl⟩ : syracuseStep 806237 = 302339) (by norm_num)
theorem B1363301 : Blo 535802 1363301 := bbase (se 4 (by rfl) ⟨127809, by rfl⟩ : syracuseStep 1363301 = 255619) (by norm_num)
theorem B806261 : Blo 535802 806261 := bbase (se 5 (by rfl) ⟨37793, by rfl⟩ : syracuseStep 806261 = 75587) (by norm_num)
theorem B806285 : Blo 535802 806285 := bbase (se 3 (by rfl) ⟨151178, by rfl⟩ : syracuseStep 806285 = 302357) (by norm_num)
theorem B806309 : Blo 535802 806309 := bbase (se 4 (by rfl) ⟨75591, by rfl⟩ : syracuseStep 806309 = 151183) (by norm_num)
theorem B904621 : Blo 535802 904621 := bbase (se 3 (by rfl) ⟨169616, by rfl⟩ : syracuseStep 904621 = 339233) (by norm_num)
theorem B806333 : Blo 535802 806333 := bbase (se 3 (by rfl) ⟨151187, by rfl⟩ : syracuseStep 806333 = 302375) (by norm_num)
theorem B806357 : Blo 535802 806357 := bbase (se 7 (by rfl) ⟨9449, by rfl⟩ : syracuseStep 806357 = 18899) (by norm_num)
theorem B806381 : Blo 535802 806381 := bbase (se 3 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 806381 = 302393) (by norm_num)
theorem B904709 : Blo 535802 904709 := bbase (se 4 (by rfl) ⟨84816, by rfl⟩ : syracuseStep 904709 = 169633) (by norm_num)
theorem B806405 : Blo 535802 806405 := bbase (se 4 (by rfl) ⟨75600, by rfl⟩ : syracuseStep 806405 = 151201) (by norm_num)
theorem B806429 : Blo 535802 806429 := bbase (se 3 (by rfl) ⟨151205, by rfl⟩ : syracuseStep 806429 = 302411) (by norm_num)
theorem B1363493 : Blo 535802 1363493 := bbase (se 4 (by rfl) ⟨127827, by rfl⟩ : syracuseStep 1363493 = 255655) (by norm_num)
theorem B773677 : Blo 535802 773677 := bbase (se 3 (by rfl) ⟨145064, by rfl⟩ : syracuseStep 773677 = 290129) (by norm_num)
theorem B806453 : Blo 535802 806453 := bbase (se 5 (by rfl) ⟨37802, by rfl⟩ : syracuseStep 806453 = 75605) (by norm_num)
theorem B806477 : Blo 535802 806477 := bbase (se 3 (by rfl) ⟨151214, by rfl⟩ : syracuseStep 806477 = 302429) (by norm_num)
theorem B806501 : Blo 535802 806501 := bbase (se 4 (by rfl) ⟨75609, by rfl⟩ : syracuseStep 806501 = 151219) (by norm_num)
theorem B806525 : Blo 535802 806525 := bbase (se 3 (by rfl) ⟨151223, by rfl⟩ : syracuseStep 806525 = 302447) (by norm_num)
theorem B904837 : Blo 535802 904837 := bbase (se 4 (by rfl) ⟨84828, by rfl⟩ : syracuseStep 904837 = 169657) (by norm_num)
theorem B806549 : Blo 535802 806549 := bbase (se 6 (by rfl) ⟨18903, by rfl⟩ : syracuseStep 806549 = 37807) (by norm_num)
theorem B3067541 : Blo 535802 3067541 := bbase (se 6 (by rfl) ⟨71895, by rfl⟩ : syracuseStep 3067541 = 143791) (by norm_num)
theorem B1527461 : Blo 535802 1527461 := bbase (se 4 (by rfl) ⟨143199, by rfl⟩ : syracuseStep 1527461 = 286399) (by norm_num)
theorem B806573 : Blo 535802 806573 := bbase (se 3 (by rfl) ⟨151232, by rfl⟩ : syracuseStep 806573 = 302465) (by norm_num)
theorem B806597 : Blo 535802 806597 := bbase (se 4 (by rfl) ⟨75618, by rfl⟩ : syracuseStep 806597 = 151237) (by norm_num)
theorem B2182853 : Blo 535802 2182853 := bbase (se 4 (by rfl) ⟨204642, by rfl⟩ : syracuseStep 2182853 = 409285) (by norm_num)
theorem B544465 : Blo 535802 544465 := bbase (se 2 (by rfl) ⟨204174, by rfl⟩ : syracuseStep 544465 = 408349) (by norm_num)
theorem B904925 : Blo 535802 904925 := bbase (se 3 (by rfl) ⟨169673, by rfl⟩ : syracuseStep 904925 = 339347) (by norm_num)
theorem B806621 : Blo 535802 806621 := bbase (se 3 (by rfl) ⟨151241, by rfl⟩ : syracuseStep 806621 = 302483) (by norm_num)
theorem B806645 : Blo 535802 806645 := bbase (se 5 (by rfl) ⟨37811, by rfl⟩ : syracuseStep 806645 = 75623) (by norm_num)
theorem B806669 : Blo 535802 806669 := bbase (se 3 (by rfl) ⟨151250, by rfl⟩ : syracuseStep 806669 = 302501) (by norm_num)
theorem B806693 : Blo 535802 806693 := bbase (se 4 (by rfl) ⟨75627, by rfl⟩ : syracuseStep 806693 = 151255) (by norm_num)
theorem B806717 : Blo 535802 806717 := bbase (se 3 (by rfl) ⟨151259, by rfl⟩ : syracuseStep 806717 = 302519) (by norm_num)
theorem B806741 : Blo 535802 806741 := bbase (se 9 (by rfl) ⟨2363, by rfl⟩ : syracuseStep 806741 = 4727) (by norm_num)
theorem B905053 : Blo 535802 905053 := bbase (se 3 (by rfl) ⟨169697, by rfl⟩ : syracuseStep 905053 = 339395) (by norm_num)
theorem B806765 : Blo 535802 806765 := bbase (se 3 (by rfl) ⟨151268, by rfl⟩ : syracuseStep 806765 = 302537) (by norm_num)
theorem B2576245 : Blo 535802 2576245 := bbase (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) (by norm_num)
theorem B970613 : Blo 535802 970613 := bbase (se 5 (by rfl) ⟨45497, by rfl⟩ : syracuseStep 970613 = 90995) (by norm_num)
theorem B1363837 : Blo 535802 1363837 := bbase (se 3 (by rfl) ⟨255719, by rfl⟩ : syracuseStep 1363837 = 511439) (by norm_num)
theorem B806789 : Blo 535802 806789 := bbase (se 4 (by rfl) ⟨75636, by rfl⟩ : syracuseStep 806789 = 151273) (by norm_num)
theorem B806813 : Blo 535802 806813 := bbase (se 3 (by rfl) ⟨151277, by rfl⟩ : syracuseStep 806813 = 302555) (by norm_num)
theorem B905141 : Blo 535802 905141 := bbase (se 5 (by rfl) ⟨42428, by rfl⟩ : syracuseStep 905141 = 84857) (by norm_num)
theorem B806837 : Blo 535802 806837 := bbase (se 5 (by rfl) ⟨37820, by rfl⟩ : syracuseStep 806837 = 75641) (by norm_num)
theorem B806861 : Blo 535802 806861 := bbase (se 3 (by rfl) ⟨151286, by rfl⟩ : syracuseStep 806861 = 302573) (by norm_num)
theorem B806885 : Blo 535802 806885 := bbase (se 4 (by rfl) ⟨75645, by rfl⟩ : syracuseStep 806885 = 151291) (by norm_num)
theorem B1363949 : Blo 535802 1363949 := bbase (se 3 (by rfl) ⟨255740, by rfl⟩ : syracuseStep 1363949 = 511481) (by norm_num)
theorem B806909 : Blo 535802 806909 := bbase (se 3 (by rfl) ⟨151295, by rfl⟩ : syracuseStep 806909 = 302591) (by norm_num)
theorem B544781 : Blo 535802 544781 := bbase (se 3 (by rfl) ⟨102146, by rfl⟩ : syracuseStep 544781 = 204293) (by norm_num)
theorem B806933 : Blo 535802 806933 := bbase (se 6 (by rfl) ⟨18912, by rfl⟩ : syracuseStep 806933 = 37825) (by norm_num)
theorem B774181 : Blo 535802 774181 := bbase (se 4 (by rfl) ⟨72579, by rfl⟩ : syracuseStep 774181 = 145159) (by norm_num)
theorem B806957 : Blo 535802 806957 := bbase (se 3 (by rfl) ⟨151304, by rfl⟩ : syracuseStep 806957 = 302609) (by norm_num)
theorem B905269 : Blo 535802 905269 := bbase (se 5 (by rfl) ⟨42434, by rfl⟩ : syracuseStep 905269 = 84869) (by norm_num)
theorem B806981 : Blo 535802 806981 := bbase (se 4 (by rfl) ⟨75654, by rfl⟩ : syracuseStep 806981 = 151309) (by norm_num)
theorem B1527893 : Blo 535802 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B807005 : Blo 535802 807005 := bbase (se 3 (by rfl) ⟨151313, by rfl⟩ : syracuseStep 807005 = 302627) (by norm_num)
theorem B807029 : Blo 535802 807029 := bbase (se 5 (by rfl) ⟨37829, by rfl⟩ : syracuseStep 807029 = 75659) (by norm_num)
theorem B905357 : Blo 535802 905357 := bbase (se 3 (by rfl) ⟨169754, by rfl⟩ : syracuseStep 905357 = 339509) (by norm_num)
theorem B807053 : Blo 535802 807053 := bbase (se 3 (by rfl) ⟨151322, by rfl⟩ : syracuseStep 807053 = 302645) (by norm_num)
theorem B3920021 : Blo 535802 3920021 := bbase (se 6 (by rfl) ⟨91875, by rfl⟩ : syracuseStep 3920021 = 183751) (by norm_num)
theorem B807077 : Blo 535802 807077 := bbase (se 4 (by rfl) ⟨75663, by rfl⟩ : syracuseStep 807077 = 151327) (by norm_num)
theorem B1364141 : Blo 535802 1364141 := bbase (se 3 (by rfl) ⟨255776, by rfl⟩ : syracuseStep 1364141 = 511553) (by norm_num)
theorem B807101 : Blo 535802 807101 := bbase (se 3 (by rfl) ⟨151331, by rfl⟩ : syracuseStep 807101 = 302663) (by norm_num)
theorem B807125 : Blo 535802 807125 := bbase (se 7 (by rfl) ⟨9458, by rfl⟩ : syracuseStep 807125 = 18917) (by norm_num)
theorem B807149 : Blo 535802 807149 := bbase (se 3 (by rfl) ⟨151340, by rfl⟩ : syracuseStep 807149 = 302681) (by norm_num)
theorem B807173 : Blo 535802 807173 := bbase (se 4 (by rfl) ⟨75672, by rfl⟩ : syracuseStep 807173 = 151345) (by norm_num)
theorem B905485 : Blo 535802 905485 := bbase (se 3 (by rfl) ⟨169778, by rfl⟩ : syracuseStep 905485 = 339557) (by norm_num)
theorem B807197 : Blo 535802 807197 := bbase (se 3 (by rfl) ⟨151349, by rfl⟩ : syracuseStep 807197 = 302699) (by norm_num)
theorem B807221 : Blo 535802 807221 := bbase (se 5 (by rfl) ⟨37838, by rfl⟩ : syracuseStep 807221 = 75677) (by norm_num)
theorem B807245 : Blo 535802 807245 := bbase (se 3 (by rfl) ⟨151358, by rfl⟩ : syracuseStep 807245 = 302717) (by norm_num)
theorem B905573 : Blo 535802 905573 := bbase (se 4 (by rfl) ⟨84897, by rfl⟩ : syracuseStep 905573 = 169795) (by norm_num)
theorem B807269 : Blo 535802 807269 := bbase (se 4 (by rfl) ⟨75681, by rfl⟩ : syracuseStep 807269 = 151363) (by norm_num)
theorem B807293 : Blo 535802 807293 := bbase (se 3 (by rfl) ⟨151367, by rfl⟩ : syracuseStep 807293 = 302735) (by norm_num)
theorem B807317 : Blo 535802 807317 := bbase (se 6 (by rfl) ⟨18921, by rfl⟩ : syracuseStep 807317 = 37843) (by norm_num)
theorem B807341 : Blo 535802 807341 := bbase (se 3 (by rfl) ⟨151376, by rfl⟩ : syracuseStep 807341 = 302753) (by norm_num)
theorem B807365 : Blo 535802 807365 := bbase (se 4 (by rfl) ⟨75690, by rfl⟩ : syracuseStep 807365 = 151381) (by norm_num)
theorem B807389 : Blo 535802 807389 := bbase (se 3 (by rfl) ⟨151385, by rfl⟩ : syracuseStep 807389 = 302771) (by norm_num)
theorem B905701 : Blo 535802 905701 := bbase (se 4 (by rfl) ⟨84909, by rfl⟩ : syracuseStep 905701 = 169819) (by norm_num)
theorem B807413 : Blo 535802 807413 := bbase (se 5 (by rfl) ⟨37847, by rfl⟩ : syracuseStep 807413 = 75695) (by norm_num)
theorem B1364485 : Blo 535802 1364485 := bbase (se 4 (by rfl) ⟨127920, by rfl⟩ : syracuseStep 1364485 = 255841) (by norm_num)
theorem B807437 : Blo 535802 807437 := bbase (se 3 (by rfl) ⟨151394, by rfl⟩ : syracuseStep 807437 = 302789) (by norm_num)
theorem B807461 : Blo 535802 807461 := bbase (se 4 (by rfl) ⟨75699, by rfl⟩ : syracuseStep 807461 = 151399) (by norm_num)
theorem B905789 : Blo 535802 905789 := bbase (se 3 (by rfl) ⟨169835, by rfl⟩ : syracuseStep 905789 = 339671) (by norm_num)
theorem B807485 : Blo 535802 807485 := bbase (se 3 (by rfl) ⟨151403, by rfl⟩ : syracuseStep 807485 = 302807) (by norm_num)
theorem B16536149 : Blo 535802 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B807509 : Blo 535802 807509 := bbase (se 8 (by rfl) ⟨4731, by rfl⟩ : syracuseStep 807509 = 9463) (by norm_num)
theorem B807533 : Blo 535802 807533 := bbase (se 3 (by rfl) ⟨151412, by rfl⟩ : syracuseStep 807533 = 302825) (by norm_num)
theorem B1364597 : Blo 535802 1364597 := bbase (se 5 (by rfl) ⟨63965, by rfl⟩ : syracuseStep 1364597 = 127931) (by norm_num)
theorem B807557 : Blo 535802 807557 := bbase (se 4 (by rfl) ⟨75708, by rfl⟩ : syracuseStep 807557 = 151417) (by norm_num)
theorem B807581 : Blo 535802 807581 := bbase (se 3 (by rfl) ⟨151421, by rfl⟩ : syracuseStep 807581 = 302843) (by norm_num)
theorem B807605 : Blo 535802 807605 := bbase (se 5 (by rfl) ⟨37856, by rfl⟩ : syracuseStep 807605 = 75713) (by norm_num)
theorem B905917 : Blo 535802 905917 := bbase (se 3 (by rfl) ⟨169859, by rfl⟩ : syracuseStep 905917 = 339719) (by norm_num)
theorem B807629 : Blo 535802 807629 := bbase (se 3 (by rfl) ⟨151430, by rfl⟩ : syracuseStep 807629 = 302861) (by norm_num)
theorem B807653 : Blo 535802 807653 := bbase (se 4 (by rfl) ⟨75717, by rfl⟩ : syracuseStep 807653 = 151435) (by norm_num)
theorem B1037045 : Blo 535802 1037045 := bbase (se 5 (by rfl) ⟨48611, by rfl⟩ : syracuseStep 1037045 = 97223) (by norm_num)
theorem B807677 : Blo 535802 807677 := bbase (se 3 (by rfl) ⟨151439, by rfl⟩ : syracuseStep 807677 = 302879) (by norm_num)
theorem B807701 : Blo 535802 807701 := bbase (se 6 (by rfl) ⟨18930, by rfl⟩ : syracuseStep 807701 = 37861) (by norm_num)
theorem B906005 : Blo 535802 906005 := bbase (se 6 (by rfl) ⟨21234, by rfl⟩ : syracuseStep 906005 = 42469) (by norm_num)
theorem B807725 : Blo 535802 807725 := bbase (se 3 (by rfl) ⟨151448, by rfl⟩ : syracuseStep 807725 = 302897) (by norm_num)
theorem B3068725 : Blo 535802 3068725 := bbase (se 5 (by rfl) ⟨143846, by rfl⟩ : syracuseStep 3068725 = 287693) (by norm_num)
theorem B1364789 : Blo 535802 1364789 := bbase (se 5 (by rfl) ⟨63974, by rfl⟩ : syracuseStep 1364789 = 127949) (by norm_num)
theorem B1528645 : Blo 535802 1528645 := bbase (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) (by norm_num)
theorem B807749 : Blo 535802 807749 := bbase (se 4 (by rfl) ⟨75726, by rfl⟩ : syracuseStep 807749 = 151453) (by norm_num)
theorem B807773 : Blo 535802 807773 := bbase (se 3 (by rfl) ⟨151457, by rfl⟩ : syracuseStep 807773 = 302915) (by norm_num)
theorem B807797 : Blo 535802 807797 := bbase (se 5 (by rfl) ⟨37865, by rfl⟩ : syracuseStep 807797 = 75731) (by norm_num)
theorem B709517 : Blo 535802 709517 := bbase (se 3 (by rfl) ⟨133034, by rfl⟩ : syracuseStep 709517 = 266069) (by norm_num)
theorem B807821 : Blo 535802 807821 := bbase (se 3 (by rfl) ⟨151466, by rfl⟩ : syracuseStep 807821 = 302933) (by norm_num)
theorem B906133 : Blo 535802 906133 := bbase (se 6 (by rfl) ⟨21237, by rfl⟩ : syracuseStep 906133 = 42475) (by norm_num)
theorem B807845 : Blo 535802 807845 := bbase (se 4 (by rfl) ⟨75735, by rfl⟩ : syracuseStep 807845 = 151471) (by norm_num)
theorem B807869 : Blo 535802 807869 := bbase (se 3 (by rfl) ⟨151475, by rfl⟩ : syracuseStep 807869 = 302951) (by norm_num)
theorem B6116309 : Blo 535802 6116309 := bbase (se 7 (by rfl) ⟨71675, by rfl⟩ : syracuseStep 6116309 = 143351) (by norm_num)
theorem B807893 : Blo 535802 807893 := bbase (se 7 (by rfl) ⟨9467, by rfl⟩ : syracuseStep 807893 = 18935) (by norm_num)
theorem B906221 : Blo 535802 906221 := bbase (se 3 (by rfl) ⟨169916, by rfl⟩ : syracuseStep 906221 = 339833) (by norm_num)
theorem B807917 : Blo 535802 807917 := bbase (se 3 (by rfl) ⟨151484, by rfl⟩ : syracuseStep 807917 = 302969) (by norm_num)
theorem B807941 : Blo 535802 807941 := bbase (se 4 (by rfl) ⟨75744, by rfl⟩ : syracuseStep 807941 = 151489) (by norm_num)
theorem B807965 : Blo 535802 807965 := bbase (se 3 (by rfl) ⟨151493, by rfl⟩ : syracuseStep 807965 = 302987) (by norm_num)
theorem B807989 : Blo 535802 807989 := bbase (se 5 (by rfl) ⟨37874, by rfl⟩ : syracuseStep 807989 = 75749) (by norm_num)
theorem B808013 : Blo 535802 808013 := bbase (se 3 (by rfl) ⟨151502, by rfl⟩ : syracuseStep 808013 = 303005) (by norm_num)
theorem B808037 : Blo 535802 808037 := bbase (se 4 (by rfl) ⟨75753, by rfl⟩ : syracuseStep 808037 = 151507) (by norm_num)
theorem B906349 : Blo 535802 906349 := bbase (se 3 (by rfl) ⟨169940, by rfl⟩ : syracuseStep 906349 = 339881) (by norm_num)
theorem B808061 : Blo 535802 808061 := bbase (se 3 (by rfl) ⟨151511, by rfl⟩ : syracuseStep 808061 = 303023) (by norm_num)
theorem B1365133 : Blo 535802 1365133 := bbase (se 3 (by rfl) ⟨255962, by rfl⟩ : syracuseStep 1365133 = 511925) (by norm_num)
theorem B808085 : Blo 535802 808085 := bbase (se 6 (by rfl) ⟨18939, by rfl⟩ : syracuseStep 808085 = 37879) (by norm_num)
theorem B808109 : Blo 535802 808109 := bbase (se 3 (by rfl) ⟨151520, by rfl⟩ : syracuseStep 808109 = 303041) (by norm_num)
theorem B808133 : Blo 535802 808133 := bbase (se 4 (by rfl) ⟨75762, by rfl⟩ : syracuseStep 808133 = 151525) (by norm_num)
theorem B906437 : Blo 535802 906437 := bbase (se 4 (by rfl) ⟨84978, by rfl⟩ : syracuseStep 906437 = 169957) (by norm_num)
theorem B775381 : Blo 535802 775381 := bbase (se 7 (by rfl) ⟨9086, by rfl⟩ : syracuseStep 775381 = 18173) (by norm_num)
theorem B808157 : Blo 535802 808157 := bbase (se 3 (by rfl) ⟨151529, by rfl⟩ : syracuseStep 808157 = 303059) (by norm_num)
theorem B808181 : Blo 535802 808181 := bbase (se 5 (by rfl) ⟨37883, by rfl⟩ : syracuseStep 808181 = 75767) (by norm_num)
theorem B1365245 : Blo 535802 1365245 := bbase (se 3 (by rfl) ⟨255983, by rfl⟩ : syracuseStep 1365245 = 511967) (by norm_num)
theorem B808205 : Blo 535802 808205 := bbase (se 3 (by rfl) ⟨151538, by rfl⟩ : syracuseStep 808205 = 303077) (by norm_num)
theorem B808229 : Blo 535802 808229 := bbase (se 4 (by rfl) ⟨75771, by rfl⟩ : syracuseStep 808229 = 151543) (by norm_num)
theorem B1725749 : Blo 535802 1725749 := bbase (se 5 (by rfl) ⟨80894, by rfl⟩ : syracuseStep 1725749 = 161789) (by norm_num)
theorem B808253 : Blo 535802 808253 := bbase (se 3 (by rfl) ⟨151547, by rfl⟩ : syracuseStep 808253 = 303095) (by norm_num)
theorem B906565 : Blo 535802 906565 := bbase (se 4 (by rfl) ⟨84990, by rfl⟩ : syracuseStep 906565 = 169981) (by norm_num)
theorem B808277 : Blo 535802 808277 := bbase (se 16 (by rfl) ⟨18, by rfl⟩ : syracuseStep 808277 = 37) (by norm_num)
theorem B808301 : Blo 535802 808301 := bbase (se 3 (by rfl) ⟨151556, by rfl⟩ : syracuseStep 808301 = 303113) (by norm_num)
theorem B808325 : Blo 535802 808325 := bbase (se 4 (by rfl) ⟨75780, by rfl⟩ : syracuseStep 808325 = 151561) (by norm_num)
theorem B906653 : Blo 535802 906653 := bbase (se 3 (by rfl) ⟨169997, by rfl⟩ : syracuseStep 906653 = 339995) (by norm_num)
theorem B808349 : Blo 535802 808349 := bbase (se 3 (by rfl) ⟨151565, by rfl⟩ : syracuseStep 808349 = 303131) (by norm_num)
theorem B1725877 : Blo 535802 1725877 := bbase (se 5 (by rfl) ⟨80900, by rfl⟩ : syracuseStep 1725877 = 161801) (by norm_num)
theorem B546229 : Blo 535802 546229 := bbase (se 5 (by rfl) ⟨25604, by rfl⟩ : syracuseStep 546229 = 51209) (by norm_num)
theorem B808373 : Blo 535802 808373 := bbase (se 5 (by rfl) ⟨37892, by rfl⟩ : syracuseStep 808373 = 75785) (by norm_num)
theorem B1365437 : Blo 535802 1365437 := bbase (se 3 (by rfl) ⟨256019, by rfl⟩ : syracuseStep 1365437 = 512039) (by norm_num)
theorem B808397 : Blo 535802 808397 := bbase (se 3 (by rfl) ⟨151574, by rfl⟩ : syracuseStep 808397 = 303149) (by norm_num)
theorem B808421 : Blo 535802 808421 := bbase (se 4 (by rfl) ⟨75789, by rfl⟩ : syracuseStep 808421 = 151579) (by norm_num)
theorem B808445 : Blo 535802 808445 := bbase (se 3 (by rfl) ⟨151583, by rfl⟩ : syracuseStep 808445 = 303167) (by norm_num)
theorem B808469 : Blo 535802 808469 := bbase (se 6 (by rfl) ⟨18948, by rfl⟩ : syracuseStep 808469 = 37897) (by norm_num)
theorem B906781 : Blo 535802 906781 := bbase (se 3 (by rfl) ⟨170021, by rfl⟩ : syracuseStep 906781 = 340043) (by norm_num)
theorem B808493 : Blo 535802 808493 := bbase (se 3 (by rfl) ⟨151592, by rfl⟩ : syracuseStep 808493 = 303185) (by norm_num)
theorem B644657 : Blo 535802 644657 := bbase (se 2 (by rfl) ⟨241746, by rfl⟩ : syracuseStep 644657 = 483493) (by norm_num)
theorem B808517 : Blo 535802 808517 := bbase (se 4 (by rfl) ⟨75798, by rfl⟩ : syracuseStep 808517 = 151597) (by norm_num)
theorem B808541 : Blo 535802 808541 := bbase (se 3 (by rfl) ⟨151601, by rfl⟩ : syracuseStep 808541 = 303203) (by norm_num)
theorem B906869 : Blo 535802 906869 := bbase (se 5 (by rfl) ⟨42509, by rfl⟩ : syracuseStep 906869 = 85019) (by norm_num)
theorem B808565 : Blo 535802 808565 := bbase (se 5 (by rfl) ⟨37901, by rfl⟩ : syracuseStep 808565 = 75803) (by norm_num)
theorem B808589 : Blo 535802 808589 := bbase (se 3 (by rfl) ⟨151610, by rfl⟩ : syracuseStep 808589 = 303221) (by norm_num)
theorem B808613 : Blo 535802 808613 := bbase (se 4 (by rfl) ⟨75807, by rfl⟩ : syracuseStep 808613 = 151615) (by norm_num)
theorem B808637 : Blo 535802 808637 := bbase (se 3 (by rfl) ⟨151619, by rfl⟩ : syracuseStep 808637 = 303239) (by norm_num)
theorem B808661 : Blo 535802 808661 := bbase (se 7 (by rfl) ⟨9476, by rfl⟩ : syracuseStep 808661 = 18953) (by norm_num)
theorem B1038037 : Blo 535802 1038037 := bbase (se 7 (by rfl) ⟨12164, by rfl⟩ : syracuseStep 1038037 = 24329) (by norm_num)
theorem B808685 : Blo 535802 808685 := bbase (se 3 (by rfl) ⟨151628, by rfl⟩ : syracuseStep 808685 = 303257) (by norm_num)
theorem B906997 : Blo 535802 906997 := bbase (se 5 (by rfl) ⟨42515, by rfl⟩ : syracuseStep 906997 = 85031) (by norm_num)
theorem B644869 : Blo 535802 644869 := bbase (se 4 (by rfl) ⟨60456, by rfl⟩ : syracuseStep 644869 = 120913) (by norm_num)
theorem B808709 : Blo 535802 808709 := bbase (se 4 (by rfl) ⟨75816, by rfl⟩ : syracuseStep 808709 = 151633) (by norm_num)
theorem B1365781 : Blo 535802 1365781 := bbase (se 6 (by rfl) ⟨32010, by rfl⟩ : syracuseStep 1365781 = 64021) (by norm_num)
theorem B808733 : Blo 535802 808733 := bbase (se 3 (by rfl) ⟨151637, by rfl⟩ : syracuseStep 808733 = 303275) (by norm_num)
theorem B808757 : Blo 535802 808757 := bbase (se 5 (by rfl) ⟨37910, by rfl⟩ : syracuseStep 808757 = 75821) (by norm_num)
theorem B907085 : Blo 535802 907085 := bbase (se 3 (by rfl) ⟨170078, by rfl⟩ : syracuseStep 907085 = 340157) (by norm_num)
theorem B808781 : Blo 535802 808781 := bbase (se 3 (by rfl) ⟨151646, by rfl⟩ : syracuseStep 808781 = 303293) (by norm_num)
theorem B808805 : Blo 535802 808805 := bbase (se 4 (by rfl) ⟨75825, by rfl⟩ : syracuseStep 808805 = 151651) (by norm_num)
theorem B2905973 : Blo 535802 2905973 := bbase (se 5 (by rfl) ⟨136217, by rfl⟩ : syracuseStep 2905973 = 272435) (by norm_num)
theorem B808829 : Blo 535802 808829 := bbase (se 3 (by rfl) ⟨151655, by rfl⟩ : syracuseStep 808829 = 303311) (by norm_num)
theorem B1365893 : Blo 535802 1365893 := bbase (se 4 (by rfl) ⟨128052, by rfl⟩ : syracuseStep 1365893 = 256105) (by norm_num)
theorem B645013 : Blo 535802 645013 := bbase (se 6 (by rfl) ⟨15117, by rfl⟩ : syracuseStep 645013 = 30235) (by norm_num)
theorem B808853 : Blo 535802 808853 := bbase (se 6 (by rfl) ⟨18957, by rfl⟩ : syracuseStep 808853 = 37915) (by norm_num)
theorem B808877 : Blo 535802 808877 := bbase (se 3 (by rfl) ⟨151664, by rfl⟩ : syracuseStep 808877 = 303329) (by norm_num)
theorem B808901 : Blo 535802 808901 := bbase (se 4 (by rfl) ⟨75834, by rfl⟩ : syracuseStep 808901 = 151669) (by norm_num)
theorem B907213 : Blo 535802 907213 := bbase (se 3 (by rfl) ⟨170102, by rfl⟩ : syracuseStep 907213 = 340205) (by norm_num)
theorem B5167061 : Blo 535802 5167061 := bbase (se 7 (by rfl) ⟨60551, by rfl⟩ : syracuseStep 5167061 = 121103) (by norm_num)
theorem B808925 : Blo 535802 808925 := bbase (se 3 (by rfl) ⟨151673, by rfl⟩ : syracuseStep 808925 = 303347) (by norm_num)
theorem B808949 : Blo 535802 808949 := bbase (se 5 (by rfl) ⟨37919, by rfl⟩ : syracuseStep 808949 = 75839) (by norm_num)
theorem B808973 : Blo 535802 808973 := bbase (se 3 (by rfl) ⟨151682, by rfl⟩ : syracuseStep 808973 = 303365) (by norm_num)
theorem B907301 : Blo 535802 907301 := bbase (se 4 (by rfl) ⟨85059, by rfl⟩ : syracuseStep 907301 = 170119) (by norm_num)
theorem B808997 : Blo 535802 808997 := bbase (se 4 (by rfl) ⟨75843, by rfl⟩ : syracuseStep 808997 = 151687) (by norm_num)
theorem B809021 : Blo 535802 809021 := bbase (se 3 (by rfl) ⟨151691, by rfl⟩ : syracuseStep 809021 = 303383) (by norm_num)
theorem B546881 : Blo 535802 546881 := bbase (se 2 (by rfl) ⟨205080, by rfl⟩ : syracuseStep 546881 = 410161) (by norm_num)
theorem B1366085 : Blo 535802 1366085 := bbase (se 4 (by rfl) ⟨128070, by rfl⟩ : syracuseStep 1366085 = 256141) (by norm_num)
theorem B809045 : Blo 535802 809045 := bbase (se 8 (by rfl) ⟨4740, by rfl⟩ : syracuseStep 809045 = 9481) (by norm_num)
theorem B809069 : Blo 535802 809069 := bbase (se 3 (by rfl) ⟨151700, by rfl⟩ : syracuseStep 809069 = 303401) (by norm_num)
theorem B809093 : Blo 535802 809093 := bbase (se 4 (by rfl) ⟨75852, by rfl⟩ : syracuseStep 809093 = 151705) (by norm_num)
theorem B809117 : Blo 535802 809117 := bbase (se 3 (by rfl) ⟨151709, by rfl⟩ : syracuseStep 809117 = 303419) (by norm_num)
theorem B907429 : Blo 535802 907429 := bbase (se 4 (by rfl) ⟨85071, by rfl⟩ : syracuseStep 907429 = 170143) (by norm_num)
theorem B809141 : Blo 535802 809141 := bbase (se 5 (by rfl) ⟨37928, by rfl⟩ : syracuseStep 809141 = 75857) (by norm_num)
theorem B809165 : Blo 535802 809165 := bbase (se 3 (by rfl) ⟨151718, by rfl⟩ : syracuseStep 809165 = 303437) (by norm_num)
theorem B809189 : Blo 535802 809189 := bbase (se 4 (by rfl) ⟨75861, by rfl⟩ : syracuseStep 809189 = 151723) (by norm_num)
theorem B907517 : Blo 535802 907517 := bbase (se 3 (by rfl) ⟨170159, by rfl⟩ : syracuseStep 907517 = 340319) (by norm_num)
theorem B809213 : Blo 535802 809213 := bbase (se 3 (by rfl) ⟨151727, by rfl⟩ : syracuseStep 809213 = 303455) (by norm_num)
theorem B809237 : Blo 535802 809237 := bbase (se 6 (by rfl) ⟨18966, by rfl⟩ : syracuseStep 809237 = 37933) (by norm_num)
theorem B809261 : Blo 535802 809261 := bbase (se 3 (by rfl) ⟨151736, by rfl⟩ : syracuseStep 809261 = 303473) (by norm_num)
theorem B809285 : Blo 535802 809285 := bbase (se 4 (by rfl) ⟨75870, by rfl⟩ : syracuseStep 809285 = 151741) (by norm_num)
theorem B678233 : Blo 535802 678233 := bbase (se 2 (by rfl) ⟨254337, by rfl⟩ : syracuseStep 678233 = 508675) (by norm_num)
theorem B809309 : Blo 535802 809309 := bbase (se 3 (by rfl) ⟨151745, by rfl⟩ : syracuseStep 809309 = 303491) (by norm_num)
theorem B809333 : Blo 535802 809333 := bbase (se 5 (by rfl) ⟨37937, by rfl⟩ : syracuseStep 809333 = 75875) (by norm_num)
theorem B907645 : Blo 535802 907645 := bbase (se 3 (by rfl) ⟨170183, by rfl⟩ : syracuseStep 907645 = 340367) (by norm_num)
theorem B809357 : Blo 535802 809357 := bbase (se 3 (by rfl) ⟨151754, by rfl⟩ : syracuseStep 809357 = 303509) (by norm_num)
theorem B678289 : Blo 535802 678289 := bbase (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) (by norm_num)
theorem B7756181 : Blo 535802 7756181 := bbase (se 6 (by rfl) ⟨181785, by rfl⟩ : syracuseStep 7756181 = 363571) (by norm_num)
theorem B809381 : Blo 535802 809381 := bbase (se 4 (by rfl) ⟨75879, by rfl⟩ : syracuseStep 809381 = 151759) (by norm_num)
theorem B612793 : Blo 535802 612793 := bbase (se 2 (by rfl) ⟨229797, by rfl⟩ : syracuseStep 612793 = 459595) (by norm_num)
theorem B809405 : Blo 535802 809405 := bbase (se 3 (by rfl) ⟨151763, by rfl⟩ : syracuseStep 809405 = 303527) (by norm_num)
theorem B907733 : Blo 535802 907733 := bbase (se 7 (by rfl) ⟨10637, by rfl⟩ : syracuseStep 907733 = 21275) (by norm_num)
theorem B809429 : Blo 535802 809429 := bbase (se 7 (by rfl) ⟨9485, by rfl⟩ : syracuseStep 809429 = 18971) (by norm_num)
theorem B809453 : Blo 535802 809453 := bbase (se 3 (by rfl) ⟨151772, by rfl⟩ : syracuseStep 809453 = 303545) (by norm_num)
theorem B678385 : Blo 535802 678385 := bbase (se 2 (by rfl) ⟨254394, by rfl⟩ : syracuseStep 678385 = 508789) (by norm_num)
theorem B809477 : Blo 535802 809477 := bbase (se 4 (by rfl) ⟨75888, by rfl⟩ : syracuseStep 809477 = 151777) (by norm_num)
theorem B809501 : Blo 535802 809501 := bbase (se 3 (by rfl) ⟨151781, by rfl⟩ : syracuseStep 809501 = 303563) (by norm_num)
theorem B809525 : Blo 535802 809525 := bbase (se 5 (by rfl) ⟨37946, by rfl⟩ : syracuseStep 809525 = 75893) (by norm_num)
theorem B809549 : Blo 535802 809549 := bbase (se 3 (by rfl) ⟨151790, by rfl⟩ : syracuseStep 809549 = 303581) (by norm_num)
theorem B907861 : Blo 535802 907861 := bbase (se 8 (by rfl) ⟨5319, by rfl⟩ : syracuseStep 907861 = 10639) (by norm_num)
theorem B809573 : Blo 535802 809573 := bbase (se 4 (by rfl) ⟨75897, by rfl⟩ : syracuseStep 809573 = 151795) (by norm_num)
theorem B809597 : Blo 535802 809597 := bbase (se 3 (by rfl) ⟨151799, by rfl⟩ : syracuseStep 809597 = 303599) (by norm_num)
theorem B809621 : Blo 535802 809621 := bbase (se 6 (by rfl) ⟨18975, by rfl⟩ : syracuseStep 809621 = 37951) (by norm_num)
theorem B678557 : Blo 535802 678557 := bbase (se 3 (by rfl) ⟨127229, by rfl⟩ : syracuseStep 678557 = 254459) (by norm_num)
theorem B907949 : Blo 535802 907949 := bbase (se 3 (by rfl) ⟨170240, by rfl⟩ : syracuseStep 907949 = 340481) (by norm_num)
theorem B809645 : Blo 535802 809645 := bbase (se 3 (by rfl) ⟨151808, by rfl⟩ : syracuseStep 809645 = 303617) (by norm_num)
theorem B809669 : Blo 535802 809669 := bbase (se 4 (by rfl) ⟨75906, by rfl⟩ : syracuseStep 809669 = 151813) (by norm_num)
theorem B678613 : Blo 535802 678613 := bbase (se 7 (by rfl) ⟨7952, by rfl⟩ : syracuseStep 678613 = 15905) (by norm_num)
theorem B809693 : Blo 535802 809693 := bbase (se 3 (by rfl) ⟨151817, by rfl⟩ : syracuseStep 809693 = 303635) (by norm_num)
theorem B3496693 : Blo 535802 3496693 := bbase (se 5 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 3496693 = 327815) (by norm_num)
theorem B3070709 : Blo 535802 3070709 := bbase (se 5 (by rfl) ⟨143939, by rfl⟩ : syracuseStep 3070709 = 287879) (by norm_num)
theorem B908077 : Blo 535802 908077 := bbase (se 3 (by rfl) ⟨170264, by rfl⟩ : syracuseStep 908077 = 340529) (by norm_num)
theorem B678709 : Blo 535802 678709 := bbase (se 5 (by rfl) ⟨31814, by rfl⟩ : syracuseStep 678709 = 63629) (by norm_num)
theorem B908165 : Blo 535802 908165 := bbase (se 4 (by rfl) ⟨85140, by rfl⟩ : syracuseStep 908165 = 170281) (by norm_num)
theorem B678881 : Blo 535802 678881 := bbase (se 2 (by rfl) ⟨254580, by rfl⟩ : syracuseStep 678881 = 509161) (by norm_num)
theorem B4086773 : Blo 535802 4086773 := bbase (se 5 (by rfl) ⟨191567, by rfl⟩ : syracuseStep 4086773 = 383135) (by norm_num)
theorem B908293 : Blo 535802 908293 := bbase (se 4 (by rfl) ⟨85152, by rfl⟩ : syracuseStep 908293 = 170305) (by norm_num)
theorem B678937 : Blo 535802 678937 := bbase (se 2 (by rfl) ⟨254601, by rfl⟩ : syracuseStep 678937 = 509203) (by norm_num)
theorem B908381 : Blo 535802 908381 := bbase (se 3 (by rfl) ⟨170321, by rfl⟩ : syracuseStep 908381 = 340643) (by norm_num)
theorem B679033 : Blo 535802 679033 := bbase (se 2 (by rfl) ⟨254637, by rfl⟩ : syracuseStep 679033 = 509275) (by norm_num)
theorem B908509 : Blo 535802 908509 := bbase (se 3 (by rfl) ⟨170345, by rfl⟩ : syracuseStep 908509 = 340691) (by norm_num)
theorem B580865 : Blo 535802 580865 := bbase (se 2 (by rfl) ⟨217824, by rfl⟩ : syracuseStep 580865 = 435649) (by norm_num)
theorem B679205 : Blo 535802 679205 := bbase (se 4 (by rfl) ⟨63675, by rfl⟩ : syracuseStep 679205 = 127351) (by norm_num)
theorem B908597 : Blo 535802 908597 := bbase (se 5 (by rfl) ⟨42590, by rfl⟩ : syracuseStep 908597 = 85181) (by norm_num)
theorem B679261 : Blo 535802 679261 := bbase (se 3 (by rfl) ⟨127361, by rfl⟩ : syracuseStep 679261 = 254723) (by norm_num)
theorem B10345877 : Blo 535802 10345877 := bbase (se 6 (by rfl) ⟨242481, by rfl⟩ : syracuseStep 10345877 = 484963) (by norm_num)
theorem B908725 : Blo 535802 908725 := bbase (se 5 (by rfl) ⟨42596, by rfl⟩ : syracuseStep 908725 = 85193) (by norm_num)
theorem B679357 : Blo 535802 679357 := bbase (se 3 (by rfl) ⟨127379, by rfl⟩ : syracuseStep 679357 = 254759) (by norm_num)
theorem B646589 : Blo 535802 646589 := bbase (se 3 (by rfl) ⟨121235, by rfl⟩ : syracuseStep 646589 = 242471) (by norm_num)
theorem B908813 : Blo 535802 908813 := bbase (se 3 (by rfl) ⟨170402, by rfl⟩ : syracuseStep 908813 = 340805) (by norm_num)
theorem B1531493 : Blo 535802 1531493 := bbase (se 4 (by rfl) ⟨143577, by rfl⟩ : syracuseStep 1531493 = 287155) (by norm_num)
theorem B679529 : Blo 535802 679529 := bbase (se 2 (by rfl) ⟨254823, by rfl⟩ : syracuseStep 679529 = 509647) (by norm_num)
theorem B908941 : Blo 535802 908941 := bbase (se 3 (by rfl) ⟨170426, by rfl⟩ : syracuseStep 908941 = 340853) (by norm_num)
theorem B679585 : Blo 535802 679585 := bbase (se 2 (by rfl) ⟨254844, by rfl⟩ : syracuseStep 679585 = 509689) (by norm_num)
theorem B909029 : Blo 535802 909029 := bbase (se 4 (by rfl) ⟨85221, by rfl⟩ : syracuseStep 909029 = 170443) (by norm_num)
theorem B679681 : Blo 535802 679681 := bbase (se 2 (by rfl) ⟨254880, by rfl⟩ : syracuseStep 679681 = 509761) (by norm_num)
theorem B646925 : Blo 535802 646925 := bbase (se 3 (by rfl) ⟨121298, by rfl⟩ : syracuseStep 646925 = 242597) (by norm_num)
theorem B88137557 : Blo 535802 88137557 := bbase (se 9 (by rfl) ⟨258215, by rfl⟩ : syracuseStep 88137557 = 516431) (by norm_num)
theorem B4972373 : Blo 535802 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B909157 : Blo 535802 909157 := bbase (se 4 (by rfl) ⟨85233, by rfl⟩ : syracuseStep 909157 = 170467) (by norm_num)
theorem B647041 : Blo 535802 647041 := bbase (se 2 (by rfl) ⟨242640, by rfl⟩ : syracuseStep 647041 = 485281) (by norm_num)
theorem B679853 : Blo 535802 679853 := bbase (se 3 (by rfl) ⟨127472, by rfl⟩ : syracuseStep 679853 = 254945) (by norm_num)
theorem B909245 : Blo 535802 909245 := bbase (se 3 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 909245 = 340967) (by norm_num)
theorem B647113 : Blo 535802 647113 := bbase (se 2 (by rfl) ⟨242667, by rfl⟩ : syracuseStep 647113 = 485335) (by norm_num)
theorem B647137 : Blo 535802 647137 := bbase (se 2 (by rfl) ⟨242676, by rfl⟩ : syracuseStep 647137 = 485353) (by norm_num)
theorem B679909 : Blo 535802 679909 := bbase (se 4 (by rfl) ⟨63741, by rfl⟩ : syracuseStep 679909 = 127483) (by norm_num)
theorem B909373 : Blo 535802 909373 := bbase (se 3 (by rfl) ⟨170507, by rfl⟩ : syracuseStep 909373 = 341015) (by norm_num)
theorem B680005 : Blo 535802 680005 := bbase (se 4 (by rfl) ⟨63750, by rfl⟩ : syracuseStep 680005 = 127501) (by norm_num)
theorem B647281 : Blo 535802 647281 := bbase (se 2 (by rfl) ⟨242730, by rfl⟩ : syracuseStep 647281 = 485461) (by norm_num)
theorem B909461 : Blo 535802 909461 := bbase (se 6 (by rfl) ⟨21315, by rfl⟩ : syracuseStep 909461 = 42631) (by norm_num)
theorem B614585 : Blo 535802 614585 := bbase (se 2 (by rfl) ⟨230469, by rfl⟩ : syracuseStep 614585 = 460939) (by norm_num)
theorem B680177 : Blo 535802 680177 := bbase (se 2 (by rfl) ⟨255066, by rfl⟩ : syracuseStep 680177 = 510133) (by norm_num)
theorem B1138933 : Blo 535802 1138933 := bbase (se 5 (by rfl) ⟨53387, by rfl⟩ : syracuseStep 1138933 = 106775) (by norm_num)
theorem B1728773 : Blo 535802 1728773 := bbase (se 4 (by rfl) ⟨162072, by rfl⟩ : syracuseStep 1728773 = 324145) (by norm_num)
theorem B909589 : Blo 535802 909589 := bbase (se 6 (by rfl) ⟨21318, by rfl⟩ : syracuseStep 909589 = 42637) (by norm_num)
theorem B680233 : Blo 535802 680233 := bbase (se 2 (by rfl) ⟨255087, by rfl⟩ : syracuseStep 680233 = 510175) (by norm_num)
theorem B2580821 : Blo 535802 2580821 := bbase (se 10 (by rfl) ⟨3780, by rfl⟩ : syracuseStep 2580821 = 7561) (by norm_num)
theorem B909677 : Blo 535802 909677 := bbase (se 3 (by rfl) ⟨170564, by rfl⟩ : syracuseStep 909677 = 341129) (by norm_num)
theorem B680329 : Blo 535802 680329 := bbase (se 2 (by rfl) ⟨255123, by rfl⟩ : syracuseStep 680329 = 510247) (by norm_num)
theorem B3498389 : Blo 535802 3498389 := bbase (se 6 (by rfl) ⟨81993, by rfl⟩ : syracuseStep 3498389 = 163987) (by norm_num)
theorem B909805 : Blo 535802 909805 := bbase (se 3 (by rfl) ⟨170588, by rfl⟩ : syracuseStep 909805 = 341177) (by norm_num)
theorem B680501 : Blo 535802 680501 := bbase (se 5 (by rfl) ⟨31898, by rfl⟩ : syracuseStep 680501 = 63797) (by norm_num)
theorem B909893 : Blo 535802 909893 := bbase (se 4 (by rfl) ⟨85302, by rfl⟩ : syracuseStep 909893 = 170605) (by norm_num)
theorem B680557 : Blo 535802 680557 := bbase (se 3 (by rfl) ⟨127604, by rfl⟩ : syracuseStep 680557 = 255209) (by norm_num)
theorem B1401517 : Blo 535802 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B910021 : Blo 535802 910021 := bbase (se 4 (by rfl) ⟨85314, by rfl⟩ : syracuseStep 910021 = 170629) (by norm_num)
theorem B680653 : Blo 535802 680653 := bbase (se 3 (by rfl) ⟨127622, by rfl⟩ : syracuseStep 680653 = 255245) (by norm_num)
theorem B1532677 : Blo 535802 1532677 := bbase (se 4 (by rfl) ⟨143688, by rfl⟩ : syracuseStep 1532677 = 287377) (by norm_num)
theorem B3498773 : Blo 535802 3498773 := bbase (se 6 (by rfl) ⟨82002, by rfl⟩ : syracuseStep 3498773 = 164005) (by norm_num)
theorem B910109 : Blo 535802 910109 := bbase (se 3 (by rfl) ⟨170645, by rfl⟩ : syracuseStep 910109 = 341291) (by norm_num)
theorem B680825 : Blo 535802 680825 := bbase (se 2 (by rfl) ⟨255309, by rfl⟩ : syracuseStep 680825 = 510619) (by norm_num)
theorem B3072917 : Blo 535802 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B910237 : Blo 535802 910237 := bbase (se 3 (by rfl) ⟨170669, by rfl⟩ : syracuseStep 910237 = 341339) (by norm_num)
theorem B1532837 : Blo 535802 1532837 := bbase (se 4 (by rfl) ⟨143703, by rfl⟩ : syracuseStep 1532837 = 287407) (by norm_num)
theorem B680881 : Blo 535802 680881 := bbase (se 2 (by rfl) ⟨255330, by rfl⟩ : syracuseStep 680881 = 510661) (by norm_num)
theorem B910325 : Blo 535802 910325 := bbase (se 5 (by rfl) ⟨42671, by rfl⟩ : syracuseStep 910325 = 85343) (by norm_num)
theorem B680977 : Blo 535802 680977 := bbase (se 2 (by rfl) ⟨255366, by rfl⟩ : syracuseStep 680977 = 510733) (by norm_num)
theorem B910453 : Blo 535802 910453 := bbase (se 5 (by rfl) ⟨42677, by rfl⟩ : syracuseStep 910453 = 85355) (by norm_num)
theorem B1533077 : Blo 535802 1533077 := bbase (se 6 (by rfl) ⟨35931, by rfl⟩ : syracuseStep 1533077 = 71863) (by norm_num)
theorem B681149 : Blo 535802 681149 := bbase (se 3 (by rfl) ⟨127715, by rfl⟩ : syracuseStep 681149 = 255431) (by norm_num)
theorem B910541 : Blo 535802 910541 := bbase (se 3 (by rfl) ⟨170726, by rfl⟩ : syracuseStep 910541 = 341453) (by norm_num)
theorem B681205 : Blo 535802 681205 := bbase (se 5 (by rfl) ⟨31931, by rfl⟩ : syracuseStep 681205 = 63863) (by norm_num)
theorem B910669 : Blo 535802 910669 := bbase (se 3 (by rfl) ⟨170750, by rfl⟩ : syracuseStep 910669 = 341501) (by norm_num)
theorem B681301 : Blo 535802 681301 := bbase (se 12 (by rfl) ⟨249, by rfl⟩ : syracuseStep 681301 = 499) (by norm_num)
theorem B1533269 : Blo 535802 1533269 := bbase (se 12 (by rfl) ⟨561, by rfl⟩ : syracuseStep 1533269 = 1123) (by norm_num)
theorem B1205621 : Blo 535802 1205621 := bbase (se 5 (by rfl) ⟨56513, by rfl⟩ : syracuseStep 1205621 = 113027) (by norm_num)
theorem B910757 : Blo 535802 910757 := bbase (se 4 (by rfl) ⟨85383, by rfl⟩ : syracuseStep 910757 = 170767) (by norm_num)
theorem B2713013 : Blo 535802 2713013 := bbase (se 5 (by rfl) ⟨127172, by rfl⟩ : syracuseStep 2713013 = 254345) (by norm_num)
theorem B1205693 : Blo 535802 1205693 := bbase (se 3 (by rfl) ⟨226067, by rfl⟩ : syracuseStep 1205693 = 452135) (by norm_num)
theorem B681473 : Blo 535802 681473 := bbase (se 2 (by rfl) ⟨255552, by rfl⟩ : syracuseStep 681473 = 511105) (by norm_num)
theorem B1205765 : Blo 535802 1205765 := bbase (se 4 (by rfl) ⟨113040, by rfl⟩ : syracuseStep 1205765 = 226081) (by norm_num)
theorem B910885 : Blo 535802 910885 := bbase (se 4 (by rfl) ⟨85395, by rfl⟩ : syracuseStep 910885 = 170791) (by norm_num)
theorem B681529 : Blo 535802 681529 := bbase (se 2 (by rfl) ⟨255573, by rfl⟩ : syracuseStep 681529 = 511147) (by norm_num)
theorem B1205837 : Blo 535802 1205837 := bbase (se 3 (by rfl) ⟨226094, by rfl⟩ : syracuseStep 1205837 = 452189) (by norm_num)
theorem B3434069 : Blo 535802 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B1205909 : Blo 535802 1205909 := bbase (se 6 (by rfl) ⟨28263, by rfl⟩ : syracuseStep 1205909 = 56527) (by norm_num)
theorem B681625 : Blo 535802 681625 := bbase (se 2 (by rfl) ⟨255609, by rfl⟩ : syracuseStep 681625 = 511219) (by norm_num)
theorem B1205981 : Blo 535802 1205981 := bbase (se 3 (by rfl) ⟨226121, by rfl⟩ : syracuseStep 1205981 = 452243) (by norm_num)
theorem B4351765 : Blo 535802 4351765 := bbase (se 6 (by rfl) ⟨101994, by rfl⟩ : syracuseStep 4351765 = 203989) (by norm_num)
theorem B1206053 : Blo 535802 1206053 := bbase (se 4 (by rfl) ⟨113067, by rfl⟩ : syracuseStep 1206053 = 226135) (by norm_num)
theorem B681797 : Blo 535802 681797 := bbase (se 4 (by rfl) ⟨63918, by rfl⟩ : syracuseStep 681797 = 127837) (by norm_num)
theorem B1206125 : Blo 535802 1206125 := bbase (se 3 (by rfl) ⟨226148, by rfl⟩ : syracuseStep 1206125 = 452297) (by norm_num)
theorem B681853 : Blo 535802 681853 := bbase (se 3 (by rfl) ⟨127847, by rfl⟩ : syracuseStep 681853 = 255695) (by norm_num)
theorem B1206197 : Blo 535802 1206197 := bbase (se 5 (by rfl) ⟨56540, by rfl⟩ : syracuseStep 1206197 = 113081) (by norm_num)
theorem B681949 : Blo 535802 681949 := bbase (se 3 (by rfl) ⟨127865, by rfl⟩ : syracuseStep 681949 = 255731) (by norm_num)
theorem B1206269 : Blo 535802 1206269 := bbase (se 3 (by rfl) ⟨226175, by rfl⟩ : syracuseStep 1206269 = 452351) (by norm_num)
theorem B583705 : Blo 535802 583705 := bbase (se 2 (by rfl) ⟨218889, by rfl⟩ : syracuseStep 583705 = 437779) (by norm_num)
theorem B1206341 : Blo 535802 1206341 := bbase (se 4 (by rfl) ⟨113094, by rfl⟩ : syracuseStep 1206341 = 226189) (by norm_num)
theorem B682121 : Blo 535802 682121 := bbase (se 2 (by rfl) ⟨255795, by rfl⟩ : syracuseStep 682121 = 511591) (by norm_num)
theorem B1206413 : Blo 535802 1206413 := bbase (se 3 (by rfl) ⟨226202, by rfl⟩ : syracuseStep 1206413 = 452405) (by norm_num)
theorem B1632421 : Blo 535802 1632421 := bbase (se 4 (by rfl) ⟨153039, by rfl⟩ : syracuseStep 1632421 = 306079) (by norm_num)
theorem B682177 : Blo 535802 682177 := bbase (se 2 (by rfl) ⟨255816, by rfl⟩ : syracuseStep 682177 = 511633) (by norm_num)
theorem B1206485 : Blo 535802 1206485 := bbase (se 7 (by rfl) ⟨14138, by rfl⟩ : syracuseStep 1206485 = 28277) (by norm_num)
theorem B1206557 : Blo 535802 1206557 := bbase (se 3 (by rfl) ⟨226229, by rfl⟩ : syracuseStep 1206557 = 452459) (by norm_num)
theorem B682273 : Blo 535802 682273 := bbase (se 2 (by rfl) ⟨255852, by rfl⟩ : syracuseStep 682273 = 511705) (by norm_num)
theorem B1534261 : Blo 535802 1534261 := bbase (se 5 (by rfl) ⟨71918, by rfl⟩ : syracuseStep 1534261 = 143837) (by norm_num)
theorem B1206629 : Blo 535802 1206629 := bbase (se 4 (by rfl) ⟨113121, by rfl⟩ : syracuseStep 1206629 = 226243) (by norm_num)
theorem B1206701 : Blo 535802 1206701 := bbase (se 3 (by rfl) ⟨226256, by rfl⟩ : syracuseStep 1206701 = 452513) (by norm_num)
theorem B682445 : Blo 535802 682445 := bbase (se 3 (by rfl) ⟨127958, by rfl⟩ : syracuseStep 682445 = 255917) (by norm_num)
theorem B5302741 : Blo 535802 5302741 := bbase (se 7 (by rfl) ⟨62141, by rfl⟩ : syracuseStep 5302741 = 124283) (by norm_num)
theorem B584173 : Blo 535802 584173 := bbase (se 3 (by rfl) ⟨109532, by rfl⟩ : syracuseStep 584173 = 219065) (by norm_num)
theorem B1206773 : Blo 535802 1206773 := bbase (se 5 (by rfl) ⟨56567, by rfl⟩ : syracuseStep 1206773 = 113135) (by norm_num)
theorem B682501 : Blo 535802 682501 := bbase (se 4 (by rfl) ⟨63984, by rfl⟩ : syracuseStep 682501 = 127969) (by norm_num)
theorem B1206845 : Blo 535802 1206845 := bbase (se 3 (by rfl) ⟨226283, by rfl⟩ : syracuseStep 1206845 = 452567) (by norm_num)
theorem B682597 : Blo 535802 682597 := bbase (se 4 (by rfl) ⟨63993, by rfl⟩ : syracuseStep 682597 = 127987) (by norm_num)
theorem B1206917 : Blo 535802 1206917 := bbase (se 4 (by rfl) ⟨113148, by rfl⟩ : syracuseStep 1206917 = 226297) (by norm_num)
theorem B2714309 : Blo 535802 2714309 := bbase (se 4 (by rfl) ⟨254466, by rfl⟩ : syracuseStep 2714309 = 508933) (by norm_num)
theorem B1206989 : Blo 535802 1206989 := bbase (se 3 (by rfl) ⟨226310, by rfl⟩ : syracuseStep 1206989 = 452621) (by norm_num)
theorem B682769 : Blo 535802 682769 := bbase (se 2 (by rfl) ⟨256038, by rfl⟩ : syracuseStep 682769 = 512077) (by norm_num)
theorem B1207061 : Blo 535802 1207061 := bbase (se 6 (by rfl) ⟨28290, by rfl⟩ : syracuseStep 1207061 = 56581) (by norm_num)
theorem B682825 : Blo 535802 682825 := bbase (se 2 (by rfl) ⟨256059, by rfl⟩ : syracuseStep 682825 = 512119) (by norm_num)
theorem B1207133 : Blo 535802 1207133 := bbase (se 3 (by rfl) ⟨226337, by rfl⟩ : syracuseStep 1207133 = 452675) (by norm_num)
theorem B1207205 : Blo 535802 1207205 := bbase (se 4 (by rfl) ⟨113175, by rfl⟩ : syracuseStep 1207205 = 226351) (by norm_num)
theorem B682921 : Blo 535802 682921 := bbase (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) (by norm_num)
theorem B1207277 : Blo 535802 1207277 := bbase (se 3 (by rfl) ⟨226364, by rfl⟩ : syracuseStep 1207277 = 452729) (by norm_num)
theorem B1207349 : Blo 535802 1207349 := bbase (se 5 (by rfl) ⟨56594, by rfl⟩ : syracuseStep 1207349 = 113189) (by norm_num)
theorem B683093 : Blo 535802 683093 := bbase (se 8 (by rfl) ⟨4002, by rfl⟩ : syracuseStep 683093 = 8005) (by norm_num)
theorem B1207421 : Blo 535802 1207421 := bbase (se 3 (by rfl) ⟨226391, by rfl⟩ : syracuseStep 1207421 = 452783) (by norm_num)
theorem B683149 : Blo 535802 683149 := bbase (se 3 (by rfl) ⟨128090, by rfl⟩ : syracuseStep 683149 = 256181) (by norm_num)
theorem B1207493 : Blo 535802 1207493 := bbase (se 4 (by rfl) ⟨113202, by rfl⟩ : syracuseStep 1207493 = 226405) (by norm_num)
theorem B1207565 : Blo 535802 1207565 := bbase (se 3 (by rfl) ⟨226418, by rfl⟩ : syracuseStep 1207565 = 452837) (by norm_num)
theorem B1207637 : Blo 535802 1207637 := bbase (se 11 (by rfl) ⟨884, by rfl⟩ : syracuseStep 1207637 = 1769) (by norm_num)
theorem B1633637 : Blo 535802 1633637 := bbase (se 4 (by rfl) ⟨153153, by rfl⟩ : syracuseStep 1633637 = 306307) (by norm_num)
theorem B1305973 : Blo 535802 1305973 := bbase (se 5 (by rfl) ⟨61217, by rfl⟩ : syracuseStep 1305973 = 122435) (by norm_num)
theorem B1535365 : Blo 535802 1535365 := bbase (se 4 (by rfl) ⟨143940, by rfl⟩ : syracuseStep 1535365 = 287881) (by norm_num)
theorem B1207709 : Blo 535802 1207709 := bbase (se 3 (by rfl) ⟨226445, by rfl⟩ : syracuseStep 1207709 = 452891) (by norm_num)
theorem B1207781 : Blo 535802 1207781 := bbase (se 4 (by rfl) ⟨113229, by rfl⟩ : syracuseStep 1207781 = 226459) (by norm_num)
theorem B1207853 : Blo 535802 1207853 := bbase (se 3 (by rfl) ⟨226472, by rfl⟩ : syracuseStep 1207853 = 452945) (by norm_num)
theorem B12381781 : Blo 535802 12381781 := bbase (se 8 (by rfl) ⟨72549, by rfl⟩ : syracuseStep 12381781 = 145099) (by norm_num)
theorem B1207925 : Blo 535802 1207925 := bbase (se 5 (by rfl) ⟨56621, by rfl⟩ : syracuseStep 1207925 = 113243) (by norm_num)
theorem B1207997 : Blo 535802 1207997 := bbase (se 3 (by rfl) ⟨226499, by rfl⟩ : syracuseStep 1207997 = 452999) (by norm_num)
theorem B814789 : Blo 535802 814789 := bbase (se 4 (by rfl) ⟨76386, by rfl⟩ : syracuseStep 814789 = 152773) (by norm_num)
theorem B1208069 : Blo 535802 1208069 := bbase (se 4 (by rfl) ⟨113256, by rfl⟩ : syracuseStep 1208069 = 226513) (by norm_num)
theorem B1208141 : Blo 535802 1208141 := bbase (se 3 (by rfl) ⟨226526, by rfl⟩ : syracuseStep 1208141 = 453053) (by norm_num)
theorem B1208213 : Blo 535802 1208213 := bbase (se 6 (by rfl) ⟨28317, by rfl⟩ : syracuseStep 1208213 = 56635) (by norm_num)
theorem B2715605 : Blo 535802 2715605 := bbase (se 7 (by rfl) ⟨31823, by rfl⟩ : syracuseStep 2715605 = 63647) (by norm_num)
theorem B1208285 : Blo 535802 1208285 := bbase (se 3 (by rfl) ⟨226553, by rfl⟩ : syracuseStep 1208285 = 453107) (by norm_num)
theorem B2289653 : Blo 535802 2289653 := bbase (se 5 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 2289653 = 214655) (by norm_num)
theorem B1208357 : Blo 535802 1208357 := bbase (se 4 (by rfl) ⟨113283, by rfl⟩ : syracuseStep 1208357 = 226567) (by norm_num)
theorem B1208429 : Blo 535802 1208429 := bbase (se 3 (by rfl) ⟨226580, by rfl⟩ : syracuseStep 1208429 = 453161) (by norm_num)
theorem B1208501 : Blo 535802 1208501 := bbase (se 5 (by rfl) ⟨56648, by rfl⟩ : syracuseStep 1208501 = 113297) (by norm_num)
theorem B1208573 : Blo 535802 1208573 := bbase (se 3 (by rfl) ⟨226607, by rfl⟩ : syracuseStep 1208573 = 453215) (by norm_num)
theorem B1208645 : Blo 535802 1208645 := bbase (se 4 (by rfl) ⟨113310, by rfl⟩ : syracuseStep 1208645 = 226621) (by norm_num)
theorem B1208717 : Blo 535802 1208717 := bbase (se 3 (by rfl) ⟨226634, by rfl⟩ : syracuseStep 1208717 = 453269) (by norm_num)
theorem B1208789 : Blo 535802 1208789 := bbase (se 7 (by rfl) ⟨14165, by rfl⟩ : syracuseStep 1208789 = 28331) (by norm_num)
theorem B1208861 : Blo 535802 1208861 := bbase (se 3 (by rfl) ⟨226661, by rfl⟩ : syracuseStep 1208861 = 453323) (by norm_num)
theorem B2585125 : Blo 535802 2585125 := bbase (se 4 (by rfl) ⟨242355, by rfl⟩ : syracuseStep 2585125 = 484711) (by norm_num)
theorem B1208933 : Blo 535802 1208933 := bbase (se 4 (by rfl) ⟨113337, by rfl⟩ : syracuseStep 1208933 = 226675) (by norm_num)
theorem B1209005 : Blo 535802 1209005 := bbase (se 3 (by rfl) ⟨226688, by rfl⟩ : syracuseStep 1209005 = 453377) (by norm_num)
theorem B1209077 : Blo 535802 1209077 := bbase (se 5 (by rfl) ⟨56675, by rfl⟩ : syracuseStep 1209077 = 113351) (by norm_num)
theorem B1209149 : Blo 535802 1209149 := bbase (se 3 (by rfl) ⟨226715, by rfl⟩ : syracuseStep 1209149 = 453431) (by norm_num)
theorem B1536869 : Blo 535802 1536869 := bbase (se 4 (by rfl) ⟨144081, by rfl⟩ : syracuseStep 1536869 = 288163) (by norm_num)
theorem B1209221 : Blo 535802 1209221 := bbase (se 4 (by rfl) ⟨113364, by rfl⟩ : syracuseStep 1209221 = 226729) (by norm_num)
theorem B1209293 : Blo 535802 1209293 := bbase (se 3 (by rfl) ⟨226742, by rfl⟩ : syracuseStep 1209293 = 453485) (by norm_num)
theorem B1209365 : Blo 535802 1209365 := bbase (se 6 (by rfl) ⟨28344, by rfl⟩ : syracuseStep 1209365 = 56689) (by norm_num)
theorem B1209437 : Blo 535802 1209437 := bbase (se 3 (by rfl) ⟨226769, by rfl⟩ : syracuseStep 1209437 = 453539) (by norm_num)
theorem B5534837 : Blo 535802 5534837 := bbase (se 5 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 5534837 = 518891) (by norm_num)
theorem B1209509 : Blo 535802 1209509 := bbase (se 4 (by rfl) ⟨113391, by rfl⟩ : syracuseStep 1209509 = 226783) (by norm_num)
theorem B2716901 : Blo 535802 2716901 := bbase (se 4 (by rfl) ⟨254709, by rfl⟩ : syracuseStep 2716901 = 509419) (by norm_num)
theorem B1209581 : Blo 535802 1209581 := bbase (se 3 (by rfl) ⟨226796, by rfl⟩ : syracuseStep 1209581 = 453593) (by norm_num)
theorem B1209653 : Blo 535802 1209653 := bbase (se 5 (by rfl) ⟨56702, by rfl⟩ : syracuseStep 1209653 = 113405) (by norm_num)
theorem B1209725 : Blo 535802 1209725 := bbase (se 3 (by rfl) ⟨226823, by rfl⟩ : syracuseStep 1209725 = 453647) (by norm_num)
theorem B1209797 : Blo 535802 1209797 := bbase (se 4 (by rfl) ⟨113418, by rfl⟩ : syracuseStep 1209797 = 226837) (by norm_num)
theorem B1209869 : Blo 535802 1209869 := bbase (se 3 (by rfl) ⟨226850, by rfl⟩ : syracuseStep 1209869 = 453701) (by norm_num)
theorem B4585045 : Blo 535802 4585045 := bbase (se 8 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 4585045 = 53731) (by norm_num)
theorem B1209941 : Blo 535802 1209941 := bbase (se 8 (by rfl) ⟨7089, by rfl⟩ : syracuseStep 1209941 = 14179) (by norm_num)
theorem B3929717 : Blo 535802 3929717 := bbase (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) (by norm_num)
theorem B1210013 : Blo 535802 1210013 := bbase (se 3 (by rfl) ⟨226877, by rfl⟩ : syracuseStep 1210013 = 453755) (by norm_num)
theorem B2291429 : Blo 535802 2291429 := bbase (se 4 (by rfl) ⟨214821, by rfl⟩ : syracuseStep 2291429 = 429643) (by norm_num)
theorem B1210085 : Blo 535802 1210085 := bbase (se 4 (by rfl) ⟨113445, by rfl⟩ : syracuseStep 1210085 = 226891) (by norm_num)
theorem B1144621 : Blo 535802 1144621 := bbase (se 3 (by rfl) ⟨214616, by rfl⟩ : syracuseStep 1144621 = 429233) (by norm_num)
theorem B1210157 : Blo 535802 1210157 := bbase (se 3 (by rfl) ⟨226904, by rfl⟩ : syracuseStep 1210157 = 453809) (by norm_num)
theorem B1210229 : Blo 535802 1210229 := bbase (se 5 (by rfl) ⟨56729, by rfl⟩ : syracuseStep 1210229 = 113459) (by norm_num)
theorem B1210301 : Blo 535802 1210301 := bbase (se 3 (by rfl) ⟨226931, by rfl⟩ : syracuseStep 1210301 = 453863) (by norm_num)
theorem B1210373 : Blo 535802 1210373 := bbase (se 4 (by rfl) ⟨113472, by rfl⟩ : syracuseStep 1210373 = 226945) (by norm_num)
theorem B1964101 : Blo 535802 1964101 := bbase (se 4 (by rfl) ⟨184134, by rfl⟩ : syracuseStep 1964101 = 368269) (by norm_num)
theorem B1210445 : Blo 535802 1210445 := bbase (se 3 (by rfl) ⟨226958, by rfl⟩ : syracuseStep 1210445 = 453917) (by norm_num)
theorem B1210517 : Blo 535802 1210517 := bbase (se 6 (by rfl) ⟨28371, by rfl⟩ : syracuseStep 1210517 = 56743) (by norm_num)
theorem B1210589 : Blo 535802 1210589 := bbase (se 3 (by rfl) ⟨226985, by rfl⟩ : syracuseStep 1210589 = 453971) (by norm_num)
theorem B1145117 : Blo 535802 1145117 := bbase (se 3 (by rfl) ⟨214709, by rfl⟩ : syracuseStep 1145117 = 429419) (by norm_num)
theorem B1210661 : Blo 535802 1210661 := bbase (se 4 (by rfl) ⟨113499, by rfl⟩ : syracuseStep 1210661 = 226999) (by norm_num)
theorem B1210733 : Blo 535802 1210733 := bbase (se 3 (by rfl) ⟨227012, by rfl⟩ : syracuseStep 1210733 = 454025) (by norm_num)
theorem B1210805 : Blo 535802 1210805 := bbase (se 5 (by rfl) ⟨56756, by rfl⟩ : syracuseStep 1210805 = 113513) (by norm_num)
theorem B817597 : Blo 535802 817597 := bbase (se 3 (by rfl) ⟨153299, by rfl⟩ : syracuseStep 817597 = 306599) (by norm_num)
theorem B2718197 : Blo 535802 2718197 := bbase (se 5 (by rfl) ⟨127415, by rfl⟩ : syracuseStep 2718197 = 254831) (by norm_num)
theorem B1210877 : Blo 535802 1210877 := bbase (se 3 (by rfl) ⟨227039, by rfl⟩ : syracuseStep 1210877 = 454079) (by norm_num)
theorem B1210949 : Blo 535802 1210949 := bbase (se 4 (by rfl) ⟨113526, by rfl⟩ : syracuseStep 1210949 = 227053) (by norm_num)
theorem B4094549 : Blo 535802 4094549 := bbase (se 8 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 4094549 = 47983) (by norm_num)
theorem B1211021 : Blo 535802 1211021 := bbase (se 3 (by rfl) ⟨227066, by rfl⟩ : syracuseStep 1211021 = 454133) (by norm_num)
theorem B2292421 : Blo 535802 2292421 := bbase (se 4 (by rfl) ⟨214914, by rfl⟩ : syracuseStep 2292421 = 429829) (by norm_num)
theorem B1211093 : Blo 535802 1211093 := bbase (se 7 (by rfl) ⟨14192, by rfl⟩ : syracuseStep 1211093 = 28385) (by norm_num)
theorem B1211165 : Blo 535802 1211165 := bbase (se 3 (by rfl) ⟨227093, by rfl⟩ : syracuseStep 1211165 = 454187) (by norm_num)
theorem B1211237 : Blo 535802 1211237 := bbase (se 4 (by rfl) ⟨113553, by rfl⟩ : syracuseStep 1211237 = 227107) (by norm_num)
theorem B2915189 : Blo 535802 2915189 := bbase (se 5 (by rfl) ⟨136649, by rfl⟩ : syracuseStep 2915189 = 273299) (by norm_num)
theorem B1211309 : Blo 535802 1211309 := bbase (se 3 (by rfl) ⟨227120, by rfl⟩ : syracuseStep 1211309 = 454241) (by norm_num)
theorem B1211381 : Blo 535802 1211381 := bbase (se 5 (by rfl) ⟨56783, by rfl⟩ : syracuseStep 1211381 = 113567) (by norm_num)
theorem B654349 : Blo 535802 654349 := bbase (se 3 (by rfl) ⟨122690, by rfl⟩ : syracuseStep 654349 = 245381) (by norm_num)
theorem B1211453 : Blo 535802 1211453 := bbase (se 3 (by rfl) ⟨227147, by rfl⟩ : syracuseStep 1211453 = 454295) (by norm_num)
theorem B1145981 : Blo 535802 1145981 := bbase (se 3 (by rfl) ⟨214871, by rfl⟩ : syracuseStep 1145981 = 429743) (by norm_num)
theorem B1211525 : Blo 535802 1211525 := bbase (se 4 (by rfl) ⟨113580, by rfl⟩ : syracuseStep 1211525 = 227161) (by norm_num)
theorem B1211597 : Blo 535802 1211597 := bbase (se 3 (by rfl) ⟨227174, by rfl⟩ : syracuseStep 1211597 = 454349) (by norm_num)
theorem B1375501 : Blo 535802 1375501 := bbase (se 3 (by rfl) ⟨257906, by rfl⟩ : syracuseStep 1375501 = 515813) (by norm_num)
theorem B1146125 : Blo 535802 1146125 := bbase (se 3 (by rfl) ⟨214898, by rfl⟩ : syracuseStep 1146125 = 429797) (by norm_num)
theorem B1211669 : Blo 535802 1211669 := bbase (se 6 (by rfl) ⟨28398, by rfl⟩ : syracuseStep 1211669 = 56797) (by norm_num)
theorem B1637653 : Blo 535802 1637653 := bbase (se 6 (by rfl) ⟨38382, by rfl⟩ : syracuseStep 1637653 = 76765) (by norm_num)
theorem B687421 : Blo 535802 687421 := bbase (se 3 (by rfl) ⟨128891, by rfl⟩ : syracuseStep 687421 = 257783) (by norm_num)
theorem B1211741 : Blo 535802 1211741 := bbase (se 3 (by rfl) ⟨227201, by rfl⟩ : syracuseStep 1211741 = 454403) (by norm_num)
theorem B1211813 : Blo 535802 1211813 := bbase (se 4 (by rfl) ⟨113607, by rfl⟩ : syracuseStep 1211813 = 227215) (by norm_num)
theorem B3866069 : Blo 535802 3866069 := bbase (se 7 (by rfl) ⟨45305, by rfl⟩ : syracuseStep 3866069 = 90611) (by norm_num)
theorem B1211885 : Blo 535802 1211885 := bbase (se 3 (by rfl) ⟨227228, by rfl⟩ : syracuseStep 1211885 = 454457) (by norm_num)
theorem B4587029 : Blo 535802 4587029 := bbase (se 6 (by rfl) ⟨107508, by rfl⟩ : syracuseStep 4587029 = 215017) (by norm_num)
theorem B1211957 : Blo 535802 1211957 := bbase (se 5 (by rfl) ⟨56810, by rfl⟩ : syracuseStep 1211957 = 113621) (by norm_num)
theorem B1375829 : Blo 535802 1375829 := bbase (se 8 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 1375829 = 16123) (by norm_num)
theorem B1212029 : Blo 535802 1212029 := bbase (se 3 (by rfl) ⟨227255, by rfl⟩ : syracuseStep 1212029 = 454511) (by norm_num)
theorem B1212101 : Blo 535802 1212101 := bbase (se 4 (by rfl) ⟨113634, by rfl⟩ : syracuseStep 1212101 = 227269) (by norm_num)
theorem B1310453 : Blo 535802 1310453 := bbase (se 5 (by rfl) ⟨61427, by rfl⟩ : syracuseStep 1310453 = 122855) (by norm_num)
theorem B2719493 : Blo 535802 2719493 := bbase (se 4 (by rfl) ⟨254952, by rfl⟩ : syracuseStep 2719493 = 509905) (by norm_num)
theorem B1212173 : Blo 535802 1212173 := bbase (se 3 (by rfl) ⟨227282, by rfl⟩ : syracuseStep 1212173 = 454565) (by norm_num)
theorem B1212245 : Blo 535802 1212245 := bbase (se 9 (by rfl) ⟨3551, by rfl⟩ : syracuseStep 1212245 = 7103) (by norm_num)
theorem B1212317 : Blo 535802 1212317 := bbase (se 3 (by rfl) ⟨227309, by rfl⟩ : syracuseStep 1212317 = 454619) (by norm_num)
theorem B1212389 : Blo 535802 1212389 := bbase (se 4 (by rfl) ⟨113661, by rfl⟩ : syracuseStep 1212389 = 227323) (by norm_num)
theorem B1146869 : Blo 535802 1146869 := bbase (se 5 (by rfl) ⟨53759, by rfl⟩ : syracuseStep 1146869 = 107519) (by norm_num)
theorem B1212497 : Blo 535802 1212497 := bstep (se 2 (by rfl) ⟨454686, by rfl⟩ : syracuseStep 1212497 = 909373) B909373
theorem B1212515 : Blo 535802 1212515 := bstep (se 1 (by rfl) ⟨909386, by rfl⟩ : syracuseStep 1212515 = 1818773) B1818773
theorem B39321713 : Blo 535802 39321713 := bstep (se 2 (by rfl) ⟨14745642, by rfl⟩ : syracuseStep 39321713 = 29491285) B29491285
theorem B3113093 : Blo 535802 3113093 := bstep (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) B583705
theorem B4128965 : Blo 535802 4128965 := bstep (se 4 (by rfl) ⟨387090, by rfl⟩ : syracuseStep 4128965 = 774181) B774181
theorem B1212785 : Blo 535802 1212785 := bstep (se 2 (by rfl) ⟨454794, by rfl⟩ : syracuseStep 1212785 = 909589) B909589
theorem B1212803 : Blo 535802 1212803 := bstep (se 1 (by rfl) ⟨909602, by rfl⟩ : syracuseStep 1212803 = 1819205) B1819205
theorem B2720141 : Blo 535802 2720141 := bstep (se 3 (by rfl) ⟨510026, by rfl⟩ : syracuseStep 2720141 = 1020053) B1020053
theorem B1638893 : Blo 535802 1638893 := bstep (se 3 (by rfl) ⟨307292, by rfl⟩ : syracuseStep 1638893 = 614585) B614585
theorem B1180145 : Blo 535802 1180145 := bstep (se 2 (by rfl) ⟨442554, by rfl⟩ : syracuseStep 1180145 = 885109) B885109
theorem B3277297 : Blo 535802 3277297 := bstep (se 2 (by rfl) ⟨1228986, by rfl⟩ : syracuseStep 3277297 = 2457973) B2457973
theorem B1147441 : Blo 535802 1147441 := bstep (se 2 (by rfl) ⟨430290, by rfl⟩ : syracuseStep 1147441 = 860581) B860581
theorem B1213073 : Blo 535802 1213073 := bstep (se 2 (by rfl) ⟨454902, by rfl⟩ : syracuseStep 1213073 = 909805) B909805
theorem B1213091 : Blo 535802 1213091 := bstep (se 1 (by rfl) ⟨909818, by rfl⟩ : syracuseStep 1213091 = 1819637) B1819637
theorem B5833397 : Blo 535802 5833397 := bstep (se 5 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 5833397 = 546881) B546881
theorem B1147697 : Blo 535802 1147697 := bstep (se 2 (by rfl) ⟨430386, by rfl⟩ : syracuseStep 1147697 = 860773) B860773
theorem B1868689 : Blo 535802 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B1213361 : Blo 535802 1213361 := bstep (se 2 (by rfl) ⟨455010, by rfl⟩ : syracuseStep 1213361 = 910021) B910021
theorem B1213379 : Blo 535802 1213379 := bstep (se 1 (by rfl) ⟨910034, by rfl⟩ : syracuseStep 1213379 = 1820069) B1820069
theorem B1246385 : Blo 535802 1246385 := bstep (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) B934789
theorem B3278029 : Blo 535802 3278029 := bstep (se 3 (by rfl) ⟨614630, by rfl⟩ : syracuseStep 3278029 = 1229261) B1229261
theorem B1213649 : Blo 535802 1213649 := bstep (se 2 (by rfl) ⟨455118, by rfl⟩ : syracuseStep 1213649 = 910237) B910237
theorem B1213667 : Blo 535802 1213667 := bstep (se 1 (by rfl) ⟨910250, by rfl⟩ : syracuseStep 1213667 = 1820501) B1820501
theorem B2295053 : Blo 535802 2295053 := bstep (se 3 (by rfl) ⟨430322, by rfl⟩ : syracuseStep 2295053 = 860645) B860645
theorem B820675 : Blo 535802 820675 := bstep (se 1 (by rfl) ⟨615506, by rfl⟩ : syracuseStep 820675 = 1231013) B1231013
theorem B1213937 : Blo 535802 1213937 := bstep (se 2 (by rfl) ⟨455226, by rfl⟩ : syracuseStep 1213937 = 910453) B910453
theorem B1213955 : Blo 535802 1213955 := bstep (se 1 (by rfl) ⟨910466, by rfl⟩ : syracuseStep 1213955 = 1820933) B1820933
theorem B1214225 : Blo 535802 1214225 := bstep (se 2 (by rfl) ⟨455334, by rfl⟩ : syracuseStep 1214225 = 910669) B910669
theorem B1214243 : Blo 535802 1214243 := bstep (se 1 (by rfl) ⟨910682, by rfl⟩ : syracuseStep 1214243 = 1821365) B1821365
theorem B1312753 : Blo 535802 1312753 := bstep (se 2 (by rfl) ⟨492282, by rfl⟩ : syracuseStep 1312753 = 984565) B984565
theorem B1017859 : Blo 535802 1017859 := bstep (se 1 (by rfl) ⟨763394, by rfl⟩ : syracuseStep 1017859 = 1526789) B1526789
theorem B985105 : Blo 535802 985105 := bstep (se 2 (by rfl) ⟨369414, by rfl⟩ : syracuseStep 985105 = 738829) B738829
theorem B1214513 : Blo 535802 1214513 := bstep (se 2 (by rfl) ⟨455442, by rfl⟩ : syracuseStep 1214513 = 910885) B910885
theorem B1148995 : Blo 535802 1148995 := bstep (se 1 (by rfl) ⟨861746, by rfl⟩ : syracuseStep 1148995 = 1723493) B1723493
theorem B1214531 : Blo 535802 1214531 := bstep (se 1 (by rfl) ⟨910898, by rfl⟩ : syracuseStep 1214531 = 1821797) B1821797
theorem B1837187 : Blo 535802 1837187 := bstep (se 1 (by rfl) ⟨1377890, by rfl⟩ : syracuseStep 1837187 = 2755781) B2755781
theorem B1181969 : Blo 535802 1181969 := bstep (se 2 (by rfl) ⟨443238, by rfl⟩ : syracuseStep 1181969 = 886477) B886477
theorem B2722097 : Blo 535802 2722097 := bstep (se 2 (by rfl) ⟨1020786, by rfl⟩ : syracuseStep 2722097 = 2041573) B2041573
theorem B4360517 : Blo 535802 4360517 := bstep (se 4 (by rfl) ⟨408798, by rfl⟩ : syracuseStep 4360517 = 817597) B817597
theorem B5802353 : Blo 535802 5802353 := bstep (se 2 (by rfl) ⟨2175882, by rfl⟩ : syracuseStep 5802353 = 4351765) B4351765
theorem B13764977 : Blo 535802 13764977 := bstep (se 2 (by rfl) ⟨5161866, by rfl⟩ : syracuseStep 13764977 = 10323733) B10323733
theorem B1149329 : Blo 535802 1149329 := bstep (se 2 (by rfl) ⟨430998, by rfl⟩ : syracuseStep 1149329 = 861997) B861997
theorem B1018307 : Blo 535802 1018307 := bstep (se 1 (by rfl) ⟨763730, by rfl⟩ : syracuseStep 1018307 = 1527461) B1527461
theorem B1018595 : Blo 535802 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B1838225 : Blo 535802 1838225 := bstep (se 2 (by rfl) ⟨689334, by rfl⟩ : syracuseStep 1838225 = 1378669) B1378669
theorem B691363 : Blo 535802 691363 := bstep (se 1 (by rfl) ⟨518522, by rfl⟩ : syracuseStep 691363 = 1037045) B1037045
theorem B2723057 : Blo 535802 2723057 := bstep (se 2 (by rfl) ⟨1021146, by rfl⟩ : syracuseStep 2723057 = 2042293) B2042293
theorem B920851 : Blo 535802 920851 := bstep (se 1 (by rfl) ⟨690638, by rfl⟩ : syracuseStep 920851 = 1381277) B1381277
theorem B1150499 : Blo 535802 1150499 := bstep (se 1 (by rfl) ⟨862874, by rfl⟩ : syracuseStep 1150499 = 1725749) B1725749
theorem B2035277 : Blo 535802 2035277 := bstep (se 3 (by rfl) ⟨381614, by rfl⟩ : syracuseStep 2035277 = 763229) B763229
theorem B1019537 : Blo 535802 1019537 := bstep (se 2 (by rfl) ⟨382326, by rfl⟩ : syracuseStep 1019537 = 764653) B764653
theorem B1937315 : Blo 535802 1937315 := bstep (se 1 (by rfl) ⟨1452986, by rfl⟩ : syracuseStep 1937315 = 2905973) B2905973
theorem B3444707 : Blo 535802 3444707 := bstep (se 1 (by rfl) ⟨2583530, by rfl⟩ : syracuseStep 3444707 = 5167061) B5167061
theorem B14913989 : Blo 535802 14913989 := bstep (se 4 (by rfl) ⟨1398186, by rfl⟩ : syracuseStep 14913989 = 2796373) B2796373
theorem B1741297 : Blo 535802 1741297 := bstep (se 2 (by rfl) ⟨652986, by rfl⟩ : syracuseStep 1741297 = 1305973) B1305973
theorem B1020433 : Blo 535802 1020433 := bstep (se 2 (by rfl) ⟨382662, by rfl⟩ : syracuseStep 1020433 = 765325) B765325
theorem B2724515 : Blo 535802 2724515 := bstep (se 1 (by rfl) ⟨2043386, by rfl⟩ : syracuseStep 2724515 = 4086773) B4086773
theorem B1020593 : Blo 535802 1020593 := bstep (se 2 (by rfl) ⟨382722, by rfl⟩ : syracuseStep 1020593 = 765445) B765445
theorem B1676045 : Blo 535802 1676045 := bstep (se 3 (by rfl) ⟨314258, by rfl⟩ : syracuseStep 1676045 = 628517) B628517
theorem B1086385 : Blo 535802 1086385 := bstep (se 2 (by rfl) ⟨407394, by rfl⟩ : syracuseStep 1086385 = 814789) B814789
theorem B1020995 : Blo 535802 1020995 := bstep (se 1 (by rfl) ⟨765746, by rfl⟩ : syracuseStep 1020995 = 1531493) B1531493
theorem B58758371 : Blo 535802 58758371 := bstep (se 1 (by rfl) ⟨44068778, by rfl⟩ : syracuseStep 58758371 = 88137557) B88137557
theorem B3314915 : Blo 535802 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B3151075 : Blo 535802 3151075 := bstep (se 1 (by rfl) ⟨2363306, by rfl⟩ : syracuseStep 3151075 = 4726613) B4726613
theorem B3872069 : Blo 535802 3872069 := bstep (se 4 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 3872069 = 726013) B726013
theorem B2725325 : Blo 535802 2725325 := bstep (se 3 (by rfl) ⟨510998, by rfl⟩ : syracuseStep 2725325 = 1021997) B1021997
theorem B1152515 : Blo 535802 1152515 := bstep (se 1 (by rfl) ⟨864386, by rfl⟩ : syracuseStep 1152515 = 1728773) B1728773
theorem B2299427 : Blo 535802 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B2332259 : Blo 535802 2332259 := bstep (se 1 (by rfl) ⟨1749194, by rfl⟩ : syracuseStep 2332259 = 3498389) B3498389
theorem B1939277 : Blo 535802 1939277 := bstep (se 3 (by rfl) ⟨363614, by rfl⟩ : syracuseStep 1939277 = 727229) B727229
theorem B1021891 : Blo 535802 1021891 := bstep (se 1 (by rfl) ⟨766418, by rfl⟩ : syracuseStep 1021891 = 1532837) B1532837
theorem B3446833 : Blo 535802 3446833 := bstep (se 2 (by rfl) ⟨1292562, by rfl⟩ : syracuseStep 3446833 = 2585125) B2585125
theorem B3053645 : Blo 535802 3053645 := bstep (se 3 (by rfl) ⟨572558, by rfl⟩ : syracuseStep 3053645 = 1145117) B1145117
theorem B1022051 : Blo 535802 1022051 := bstep (se 1 (by rfl) ⟨766538, by rfl⟩ : syracuseStep 1022051 = 1533077) B1533077
theorem B13080689 : Blo 535802 13080689 := bstep (se 2 (by rfl) ⟨4905258, by rfl⟩ : syracuseStep 13080689 = 9810517) B9810517
theorem B1808621 : Blo 535802 1808621 := bstep (se 3 (by rfl) ⟨339116, by rfl⟩ : syracuseStep 1808621 = 678233) B678233
theorem B1808675 : Blo 535802 1808675 := bstep (se 1 (by rfl) ⟨1356506, by rfl⟩ : syracuseStep 1808675 = 2713013) B2713013
theorem B2038193 : Blo 535802 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B2365901 : Blo 535802 2365901 := bstep (se 3 (by rfl) ⟨443606, by rfl⟩ : syracuseStep 2365901 = 887213) B887213
theorem B858595 : Blo 535802 858595 := bstep (se 1 (by rfl) ⟨643946, by rfl⟩ : syracuseStep 858595 = 1287893) B1287893
theorem B1808945 : Blo 535802 1808945 := bstep (se 2 (by rfl) ⟨678354, by rfl⟩ : syracuseStep 1808945 = 1356709) B1356709
theorem B858851 : Blo 535802 858851 := bstep (se 1 (by rfl) ⟨644138, by rfl⟩ : syracuseStep 858851 = 1288277) B1288277
theorem B859043 : Blo 535802 859043 := bstep (se 1 (by rfl) ⟨644282, by rfl⟩ : syracuseStep 859043 = 1288565) B1288565
theorem B662467 : Blo 535802 662467 := bstep (se 1 (by rfl) ⟨496850, by rfl⟩ : syracuseStep 662467 = 993701) B993701
theorem B1809485 : Blo 535802 1809485 := bstep (se 3 (by rfl) ⟨339278, by rfl⟩ : syracuseStep 1809485 = 678557) B678557
theorem B1809539 : Blo 535802 1809539 := bstep (se 1 (by rfl) ⟨1357154, by rfl⟩ : syracuseStep 1809539 = 2714309) B2714309
theorem B1023121 : Blo 535802 1023121 := bstep (se 2 (by rfl) ⟨383670, by rfl⟩ : syracuseStep 1023121 = 767341) B767341
theorem B2301169 : Blo 535802 2301169 := bstep (se 2 (by rfl) ⟨862938, by rfl⟩ : syracuseStep 2301169 = 1725877) B1725877
theorem B1809809 : Blo 535802 1809809 := bstep (se 2 (by rfl) ⟨678678, by rfl⟩ : syracuseStep 1809809 = 1357357) B1357357
theorem B1089091 : Blo 535802 1089091 := bstep (se 1 (by rfl) ⟨816818, by rfl⟩ : syracuseStep 1089091 = 1633637) B1633637
theorem B1449571 : Blo 535802 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B1384049 : Blo 535802 1384049 := bstep (se 2 (by rfl) ⟨519018, by rfl⟩ : syracuseStep 1384049 = 1038037) B1038037
theorem B859825 : Blo 535802 859825 := bstep (se 2 (by rfl) ⟨322434, by rfl⟩ : syracuseStep 859825 = 644869) B644869
theorem B2039651 : Blo 535802 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B1810349 : Blo 535802 1810349 := bstep (se 3 (by rfl) ⟨339440, by rfl⟩ : syracuseStep 1810349 = 678881) B678881
theorem B1810403 : Blo 535802 1810403 := bstep (se 1 (by rfl) ⟨1357802, by rfl⟩ : syracuseStep 1810403 = 2715605) B2715605
theorem B1024177 : Blo 535802 1024177 := bstep (se 2 (by rfl) ⟨384066, by rfl⟩ : syracuseStep 1024177 = 768133) B768133
theorem B1810673 : Blo 535802 1810673 := bstep (se 2 (by rfl) ⟨679002, by rfl⟩ : syracuseStep 1810673 = 1358005) B1358005
theorem B3055877 : Blo 535802 3055877 := bstep (se 4 (by rfl) ⟨286488, by rfl⟩ : syracuseStep 3055877 = 572977) B572977
theorem B2728241 : Blo 535802 2728241 := bstep (se 2 (by rfl) ⟨1023090, by rfl⟩ : syracuseStep 2728241 = 2046181) B2046181
theorem B1024579 : Blo 535802 1024579 := bstep (se 1 (by rfl) ⟨768434, by rfl⟩ : syracuseStep 1024579 = 1536869) B1536869
theorem B1024625 : Blo 535802 1024625 := bstep (se 2 (by rfl) ⟨384234, by rfl⟩ : syracuseStep 1024625 = 768469) B768469
theorem B1548973 : Blo 535802 1548973 := bstep (se 3 (by rfl) ⟨290432, by rfl⟩ : syracuseStep 1548973 = 580865) B580865
theorem B795313 : Blo 535802 795313 := bstep (se 2 (by rfl) ⟨298242, by rfl⟩ : syracuseStep 795313 = 596485) B596485
theorem B1811213 : Blo 535802 1811213 := bstep (se 3 (by rfl) ⟨339602, by rfl⟩ : syracuseStep 1811213 = 679205) B679205
theorem B1811267 : Blo 535802 1811267 := bstep (se 1 (by rfl) ⟨1358450, by rfl⟩ : syracuseStep 1811267 = 2716901) B2716901
theorem B2040653 : Blo 535802 2040653 := bstep (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) B765245
theorem B2761613 : Blo 535802 2761613 := bstep (se 3 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 2761613 = 1035605) B1035605
theorem B3056561 : Blo 535802 3056561 := bstep (se 2 (by rfl) ⟨1146210, by rfl⟩ : syracuseStep 3056561 = 2292421) B2292421
theorem B4662257 : Blo 535802 4662257 := bstep (se 2 (by rfl) ⟨1748346, by rfl⟩ : syracuseStep 4662257 = 3496693) B3496693
theorem B1811537 : Blo 535802 1811537 := bstep (se 2 (by rfl) ⟨679326, by rfl⟩ : syracuseStep 1811537 = 1358653) B1358653
theorem B2303117 : Blo 535802 2303117 := bstep (se 3 (by rfl) ⟨431834, by rfl⟩ : syracuseStep 2303117 = 863669) B863669
theorem B763121 : Blo 535802 763121 := bstep (se 2 (by rfl) ⟨286170, by rfl⟩ : syracuseStep 763121 = 572341) B572341
theorem B861491 : Blo 535802 861491 := bstep (se 1 (by rfl) ⟨646118, by rfl⟩ : syracuseStep 861491 = 1292237) B1292237
theorem B861619 : Blo 535802 861619 := bstep (se 1 (by rfl) ⟨646214, by rfl⟩ : syracuseStep 861619 = 1292429) B1292429
theorem B6104645 : Blo 535802 6104645 := bstep (se 4 (by rfl) ⟨572310, by rfl⟩ : syracuseStep 6104645 = 1144621) B1144621
theorem B1812077 : Blo 535802 1812077 := bstep (se 3 (by rfl) ⟨339764, by rfl⟩ : syracuseStep 1812077 = 679529) B679529
theorem B1844849 : Blo 535802 1844849 := bstep (se 2 (by rfl) ⟨691818, by rfl⟩ : syracuseStep 1844849 = 1383637) B1383637
theorem B1812131 : Blo 535802 1812131 := bstep (se 1 (by rfl) ⟨1359098, by rfl⟩ : syracuseStep 1812131 = 2718197) B2718197
theorem B2729699 : Blo 535802 2729699 := bstep (se 1 (by rfl) ⟨2047274, by rfl⟩ : syracuseStep 2729699 = 4094549) B4094549
theorem B862003 : Blo 535802 862003 := bstep (se 1 (by rfl) ⟨646502, by rfl⟩ : syracuseStep 862003 = 1293005) B1293005
theorem B1943459 : Blo 535802 1943459 := bstep (se 1 (by rfl) ⟨1457594, by rfl⟩ : syracuseStep 1943459 = 2915189) B2915189
theorem B1812401 : Blo 535802 1812401 := bstep (se 2 (by rfl) ⟨679650, by rfl⟩ : syracuseStep 1812401 = 1359301) B1359301
theorem B11610053 : Blo 535802 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B1845233 : Blo 535802 1845233 := bstep (se 2 (by rfl) ⟨691962, by rfl⟩ : syracuseStep 1845233 = 1383925) B1383925
theorem B862259 : Blo 535802 862259 := bstep (se 1 (by rfl) ⟨646694, by rfl⟩ : syracuseStep 862259 = 1293389) B1293389
theorem B763987 : Blo 535802 763987 := bstep (se 1 (by rfl) ⟨572990, by rfl⟩ : syracuseStep 763987 = 1145981) B1145981
theorem B764083 : Blo 535802 764083 := bstep (se 1 (by rfl) ⟨573062, by rfl⟩ : syracuseStep 764083 = 1146125) B1146125
theorem B3058019 : Blo 535802 3058019 := bstep (se 1 (by rfl) ⟨2293514, by rfl⟩ : syracuseStep 3058019 = 4587029) B4587029
theorem B1812941 : Blo 535802 1812941 := bstep (se 3 (by rfl) ⟨339926, by rfl⟩ : syracuseStep 1812941 = 679853) B679853
theorem B862721 : Blo 535802 862721 := bstep (se 2 (by rfl) ⟨323520, by rfl⟩ : syracuseStep 862721 = 647041) B647041
theorem B1812995 : Blo 535802 1812995 := bstep (se 1 (by rfl) ⟨1359746, by rfl⟩ : syracuseStep 1812995 = 2719493) B2719493
theorem B2730509 : Blo 535802 2730509 := bstep (se 3 (by rfl) ⟨511970, by rfl⟩ : syracuseStep 2730509 = 1023941) B1023941
theorem B862817 : Blo 535802 862817 := bstep (se 2 (by rfl) ⟨323556, by rfl⟩ : syracuseStep 862817 = 647113) B647113
theorem B862849 : Blo 535802 862849 := bstep (se 2 (by rfl) ⟨323568, by rfl⟩ : syracuseStep 862849 = 647137) B647137
theorem B764579 : Blo 535802 764579 := bstep (se 1 (by rfl) ⟨573434, by rfl⟩ : syracuseStep 764579 = 1146869) B1146869
theorem B1452749 : Blo 535802 1452749 := bstep (se 3 (by rfl) ⟨272390, by rfl⟩ : syracuseStep 1452749 = 544781) B544781
theorem B1813265 : Blo 535802 1813265 := bstep (se 2 (by rfl) ⟨679974, by rfl⟩ : syracuseStep 1813265 = 1359949) B1359949
theorem B1289027 : Blo 535802 1289027 := bstep (se 1 (by rfl) ⟨966770, by rfl⟩ : syracuseStep 1289027 = 1933541) B1933541
theorem B2042765 : Blo 535802 2042765 := bstep (se 3 (by rfl) ⟨383018, by rfl⟩ : syracuseStep 2042765 = 766037) B766037
theorem B535811 : Blo 535802 535811 := bstep (se 1 (by rfl) ⟨401858, by rfl⟩ : syracuseStep 535811 = 803717) B803717
theorem B3452165 : Blo 535802 3452165 := bstep (se 4 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 3452165 = 647281) B647281
theorem B535827 : Blo 535802 535827 := bstep (se 1 (by rfl) ⟨401870, by rfl⟩ : syracuseStep 535827 = 803741) B803741
theorem B765217 : Blo 535802 765217 := bstep (se 2 (by rfl) ⟨286956, by rfl⟩ : syracuseStep 765217 = 573913) B573913
theorem B535843 : Blo 535802 535843 := bstep (se 1 (by rfl) ⟨401882, by rfl⟩ : syracuseStep 535843 = 803765) B803765
theorem B1813805 : Blo 535802 1813805 := bstep (se 3 (by rfl) ⟨340088, by rfl⟩ : syracuseStep 1813805 = 680177) B680177
theorem B535859 : Blo 535802 535859 := bstep (se 1 (by rfl) ⟨401894, by rfl⟩ : syracuseStep 535859 = 803789) B803789
theorem B535875 : Blo 535802 535875 := bstep (se 1 (by rfl) ⟨401906, by rfl⟩ : syracuseStep 535875 = 803813) B803813
theorem B535891 : Blo 535802 535891 := bstep (se 1 (by rfl) ⟨401918, by rfl⟩ : syracuseStep 535891 = 803837) B803837
theorem B535907 : Blo 535802 535907 := bstep (se 1 (by rfl) ⟨401930, by rfl⟩ : syracuseStep 535907 = 803861) B803861
theorem B1813859 : Blo 535802 1813859 := bstep (se 1 (by rfl) ⟨1360394, by rfl⟩ : syracuseStep 1813859 = 2720789) B2720789
theorem B535923 : Blo 535802 535923 := bstep (se 1 (by rfl) ⟨401942, by rfl⟩ : syracuseStep 535923 = 803885) B803885
theorem B535939 : Blo 535802 535939 := bstep (se 1 (by rfl) ⟨401954, by rfl⟩ : syracuseStep 535939 = 803909) B803909
theorem B535955 : Blo 535802 535955 := bstep (se 1 (by rfl) ⟨401966, by rfl⟩ : syracuseStep 535955 = 803933) B803933
theorem B535971 : Blo 535802 535971 := bstep (se 1 (by rfl) ⟨401978, by rfl⟩ : syracuseStep 535971 = 803957) B803957
theorem B535987 : Blo 535802 535987 := bstep (se 1 (by rfl) ⟨401990, by rfl⟩ : syracuseStep 535987 = 803981) B803981
theorem B536003 : Blo 535802 536003 := bstep (se 1 (by rfl) ⟨402002, by rfl⟩ : syracuseStep 536003 = 804005) B804005
theorem B536019 : Blo 535802 536019 := bstep (se 1 (by rfl) ⟨402014, by rfl⟩ : syracuseStep 536019 = 804029) B804029
theorem B536035 : Blo 535802 536035 := bstep (se 1 (by rfl) ⟨402026, by rfl⟩ : syracuseStep 536035 = 804053) B804053
theorem B1289699 : Blo 535802 1289699 := bstep (se 1 (by rfl) ⟨967274, by rfl⟩ : syracuseStep 1289699 = 1934549) B1934549
theorem B536051 : Blo 535802 536051 := bstep (se 1 (by rfl) ⟨402038, by rfl⟩ : syracuseStep 536051 = 804077) B804077
theorem B536067 : Blo 535802 536067 := bstep (se 1 (by rfl) ⟨402050, by rfl⟩ : syracuseStep 536067 = 804101) B804101
theorem B536083 : Blo 535802 536083 := bstep (se 1 (by rfl) ⟨402062, by rfl⟩ : syracuseStep 536083 = 804125) B804125
theorem B536099 : Blo 535802 536099 := bstep (se 1 (by rfl) ⟨402074, by rfl⟩ : syracuseStep 536099 = 804149) B804149
theorem B536115 : Blo 535802 536115 := bstep (se 1 (by rfl) ⟨402086, by rfl⟩ : syracuseStep 536115 = 804173) B804173
theorem B536131 : Blo 535802 536131 := bstep (se 1 (by rfl) ⟨402098, by rfl⟩ : syracuseStep 536131 = 804197) B804197
theorem B536147 : Blo 535802 536147 := bstep (se 1 (by rfl) ⟨402110, by rfl⟩ : syracuseStep 536147 = 804221) B804221
theorem B536163 : Blo 535802 536163 := bstep (se 1 (by rfl) ⟨402122, by rfl⟩ : syracuseStep 536163 = 804245) B804245
theorem B1814129 : Blo 535802 1814129 := bstep (se 2 (by rfl) ⟨680298, by rfl⟩ : syracuseStep 1814129 = 1360597) B1360597
theorem B765553 : Blo 535802 765553 := bstep (se 2 (by rfl) ⟨287082, by rfl⟩ : syracuseStep 765553 = 574165) B574165
theorem B536179 : Blo 535802 536179 := bstep (se 1 (by rfl) ⟨402134, by rfl⟩ : syracuseStep 536179 = 804269) B804269
theorem B536195 : Blo 535802 536195 := bstep (se 1 (by rfl) ⟨402146, by rfl⟩ : syracuseStep 536195 = 804293) B804293
theorem B536211 : Blo 535802 536211 := bstep (se 1 (by rfl) ⟨402158, by rfl⟩ : syracuseStep 536211 = 804317) B804317
theorem B536227 : Blo 535802 536227 := bstep (se 1 (by rfl) ⟨402170, by rfl⟩ : syracuseStep 536227 = 804341) B804341
theorem B2043569 : Blo 535802 2043569 := bstep (se 2 (by rfl) ⟨766338, by rfl⟩ : syracuseStep 2043569 = 1532677) B1532677
theorem B536243 : Blo 535802 536243 := bstep (se 1 (by rfl) ⟨402182, by rfl⟩ : syracuseStep 536243 = 804365) B804365
theorem B536259 : Blo 535802 536259 := bstep (se 1 (by rfl) ⟨402194, by rfl⟩ : syracuseStep 536259 = 804389) B804389
theorem B536275 : Blo 535802 536275 := bstep (se 1 (by rfl) ⟨402206, by rfl⟩ : syracuseStep 536275 = 804413) B804413
theorem B536291 : Blo 535802 536291 := bstep (se 1 (by rfl) ⟨402218, by rfl⟩ : syracuseStep 536291 = 804437) B804437
theorem B1289969 : Blo 535802 1289969 := bstep (se 2 (by rfl) ⟨483738, by rfl⟩ : syracuseStep 1289969 = 967477) B967477
theorem B536307 : Blo 535802 536307 := bstep (se 1 (by rfl) ⟨402230, by rfl⟩ : syracuseStep 536307 = 804461) B804461
theorem B536323 : Blo 535802 536323 := bstep (se 1 (by rfl) ⟨402242, by rfl⟩ : syracuseStep 536323 = 804485) B804485
theorem B536339 : Blo 535802 536339 := bstep (se 1 (by rfl) ⟨402254, by rfl⟩ : syracuseStep 536339 = 804509) B804509
theorem B536355 : Blo 535802 536355 := bstep (se 1 (by rfl) ⟨402266, by rfl⟩ : syracuseStep 536355 = 804533) B804533
theorem B536371 : Blo 535802 536371 := bstep (se 1 (by rfl) ⟨402278, by rfl⟩ : syracuseStep 536371 = 804557) B804557
theorem B536387 : Blo 535802 536387 := bstep (se 1 (by rfl) ⟨402290, by rfl⟩ : syracuseStep 536387 = 804581) B804581
theorem B536403 : Blo 535802 536403 := bstep (se 1 (by rfl) ⟨402302, by rfl⟩ : syracuseStep 536403 = 804605) B804605
theorem B536419 : Blo 535802 536419 := bstep (se 1 (by rfl) ⟨402314, by rfl⟩ : syracuseStep 536419 = 804629) B804629
theorem B536435 : Blo 535802 536435 := bstep (se 1 (by rfl) ⟨402326, by rfl⟩ : syracuseStep 536435 = 804653) B804653
theorem B536451 : Blo 535802 536451 := bstep (se 1 (by rfl) ⟨402338, by rfl⟩ : syracuseStep 536451 = 804677) B804677
theorem B536467 : Blo 535802 536467 := bstep (se 1 (by rfl) ⟨402350, by rfl⟩ : syracuseStep 536467 = 804701) B804701
theorem B536483 : Blo 535802 536483 := bstep (se 1 (by rfl) ⟨402362, by rfl⟩ : syracuseStep 536483 = 804725) B804725
theorem B536499 : Blo 535802 536499 := bstep (se 1 (by rfl) ⟨402374, by rfl⟩ : syracuseStep 536499 = 804749) B804749
theorem B536515 : Blo 535802 536515 := bstep (se 1 (by rfl) ⟨402386, by rfl⟩ : syracuseStep 536515 = 804773) B804773
theorem B6074309 : Blo 535802 6074309 := bstep (se 4 (by rfl) ⟨569466, by rfl⟩ : syracuseStep 6074309 = 1138933) B1138933
theorem B536531 : Blo 535802 536531 := bstep (se 1 (by rfl) ⟨402398, by rfl⟩ : syracuseStep 536531 = 804797) B804797
theorem B536547 : Blo 535802 536547 := bstep (se 1 (by rfl) ⟨402410, by rfl⟩ : syracuseStep 536547 = 804821) B804821
theorem B536563 : Blo 535802 536563 := bstep (se 1 (by rfl) ⟨402422, by rfl⟩ : syracuseStep 536563 = 804845) B804845
theorem B536579 : Blo 535802 536579 := bstep (se 1 (by rfl) ⟨402434, by rfl⟩ : syracuseStep 536579 = 804869) B804869
theorem B536595 : Blo 535802 536595 := bstep (se 1 (by rfl) ⟨402446, by rfl⟩ : syracuseStep 536595 = 804893) B804893
theorem B536611 : Blo 535802 536611 := bstep (se 1 (by rfl) ⟨402458, by rfl⟩ : syracuseStep 536611 = 804917) B804917
theorem B536627 : Blo 535802 536627 := bstep (se 1 (by rfl) ⟨402470, by rfl⟩ : syracuseStep 536627 = 804941) B804941
theorem B536643 : Blo 535802 536643 := bstep (se 1 (by rfl) ⟨402482, by rfl⟩ : syracuseStep 536643 = 804965) B804965
theorem B536659 : Blo 535802 536659 := bstep (se 1 (by rfl) ⟨402494, by rfl⟩ : syracuseStep 536659 = 804989) B804989
theorem B536675 : Blo 535802 536675 := bstep (se 1 (by rfl) ⟨402506, by rfl⟩ : syracuseStep 536675 = 805013) B805013
theorem B536691 : Blo 535802 536691 := bstep (se 1 (by rfl) ⟨402518, by rfl⟩ : syracuseStep 536691 = 805037) B805037
theorem B536707 : Blo 535802 536707 := bstep (se 1 (by rfl) ⟨402530, by rfl⟩ : syracuseStep 536707 = 805061) B805061
theorem B1814669 : Blo 535802 1814669 := bstep (se 3 (by rfl) ⟨340250, by rfl⟩ : syracuseStep 1814669 = 680501) B680501
theorem B536723 : Blo 535802 536723 := bstep (se 1 (by rfl) ⟨402542, by rfl⟩ : syracuseStep 536723 = 805085) B805085
theorem B536739 : Blo 535802 536739 := bstep (se 1 (by rfl) ⟨402554, by rfl⟩ : syracuseStep 536739 = 805109) B805109
theorem B536755 : Blo 535802 536755 := bstep (se 1 (by rfl) ⟨402566, by rfl⟩ : syracuseStep 536755 = 805133) B805133
theorem B766145 : Blo 535802 766145 := bstep (se 2 (by rfl) ⟨287304, by rfl⟩ : syracuseStep 766145 = 574609) B574609
theorem B536771 : Blo 535802 536771 := bstep (se 1 (by rfl) ⟨402578, by rfl⟩ : syracuseStep 536771 = 805157) B805157
theorem B1814723 : Blo 535802 1814723 := bstep (se 1 (by rfl) ⟨1361042, by rfl⟩ : syracuseStep 1814723 = 2722085) B2722085
theorem B536787 : Blo 535802 536787 := bstep (se 1 (by rfl) ⟨402590, by rfl⟩ : syracuseStep 536787 = 805181) B805181
theorem B536803 : Blo 535802 536803 := bstep (se 1 (by rfl) ⟨402602, by rfl⟩ : syracuseStep 536803 = 805205) B805205
theorem B536819 : Blo 535802 536819 := bstep (se 1 (by rfl) ⟨402614, by rfl⟩ : syracuseStep 536819 = 805229) B805229
theorem B536835 : Blo 535802 536835 := bstep (se 1 (by rfl) ⟨402626, by rfl⟩ : syracuseStep 536835 = 805253) B805253
theorem B864515 : Blo 535802 864515 := bstep (se 1 (by rfl) ⟨648386, by rfl⟩ : syracuseStep 864515 = 1296773) B1296773
theorem B536851 : Blo 535802 536851 := bstep (se 1 (by rfl) ⟨402638, by rfl⟩ : syracuseStep 536851 = 805277) B805277
theorem B536867 : Blo 535802 536867 := bstep (se 1 (by rfl) ⟨402650, by rfl⟩ : syracuseStep 536867 = 805301) B805301
theorem B1290545 : Blo 535802 1290545 := bstep (se 2 (by rfl) ⟨483954, by rfl⟩ : syracuseStep 1290545 = 967909) B967909
theorem B536883 : Blo 535802 536883 := bstep (se 1 (by rfl) ⟨402662, by rfl⟩ : syracuseStep 536883 = 805325) B805325
theorem B536899 : Blo 535802 536899 := bstep (se 1 (by rfl) ⟨402674, by rfl⟩ : syracuseStep 536899 = 805349) B805349
theorem B2044237 : Blo 535802 2044237 := bstep (se 3 (by rfl) ⟨383294, by rfl⟩ : syracuseStep 2044237 = 766589) B766589
theorem B536915 : Blo 535802 536915 := bstep (se 1 (by rfl) ⟨402686, by rfl⟩ : syracuseStep 536915 = 805373) B805373
theorem B536931 : Blo 535802 536931 := bstep (se 1 (by rfl) ⟨402698, by rfl⟩ : syracuseStep 536931 = 805397) B805397
theorem B536947 : Blo 535802 536947 := bstep (se 1 (by rfl) ⟨402710, by rfl⟩ : syracuseStep 536947 = 805421) B805421
theorem B536963 : Blo 535802 536963 := bstep (se 1 (by rfl) ⟨402722, by rfl⟩ : syracuseStep 536963 = 805445) B805445
theorem B536979 : Blo 535802 536979 := bstep (se 1 (by rfl) ⟨402734, by rfl⟩ : syracuseStep 536979 = 805469) B805469
theorem B536995 : Blo 535802 536995 := bstep (se 1 (by rfl) ⟨402746, by rfl⟩ : syracuseStep 536995 = 805493) B805493
theorem B537011 : Blo 535802 537011 := bstep (se 1 (by rfl) ⟨402758, by rfl⟩ : syracuseStep 537011 = 805517) B805517
theorem B537027 : Blo 535802 537027 := bstep (se 1 (by rfl) ⟨402770, by rfl⟩ : syracuseStep 537027 = 805541) B805541
theorem B1814993 : Blo 535802 1814993 := bstep (se 2 (by rfl) ⟨680622, by rfl⟩ : syracuseStep 1814993 = 1361245) B1361245
theorem B537043 : Blo 535802 537043 := bstep (se 1 (by rfl) ⟨402782, by rfl⟩ : syracuseStep 537043 = 805565) B805565
theorem B537059 : Blo 535802 537059 := bstep (se 1 (by rfl) ⟨402794, by rfl⟩ : syracuseStep 537059 = 805589) B805589
theorem B1290737 : Blo 535802 1290737 := bstep (se 2 (by rfl) ⟨484026, by rfl⟩ : syracuseStep 1290737 = 968053) B968053
theorem B537075 : Blo 535802 537075 := bstep (se 1 (by rfl) ⟨402806, by rfl⟩ : syracuseStep 537075 = 805613) B805613
theorem B537091 : Blo 535802 537091 := bstep (se 1 (by rfl) ⟨402818, by rfl⟩ : syracuseStep 537091 = 805637) B805637
theorem B537107 : Blo 535802 537107 := bstep (se 1 (by rfl) ⟨402830, by rfl⟩ : syracuseStep 537107 = 805661) B805661
theorem B537123 : Blo 535802 537123 := bstep (se 1 (by rfl) ⟨402842, by rfl⟩ : syracuseStep 537123 = 805685) B805685
theorem B537139 : Blo 535802 537139 := bstep (se 1 (by rfl) ⟨402854, by rfl⟩ : syracuseStep 537139 = 805709) B805709
theorem B537155 : Blo 535802 537155 := bstep (se 1 (by rfl) ⟨402866, by rfl⟩ : syracuseStep 537155 = 805733) B805733
theorem B537171 : Blo 535802 537171 := bstep (se 1 (by rfl) ⟨402878, by rfl⟩ : syracuseStep 537171 = 805757) B805757
theorem B537187 : Blo 535802 537187 := bstep (se 1 (by rfl) ⟨402890, by rfl⟩ : syracuseStep 537187 = 805781) B805781
theorem B537203 : Blo 535802 537203 := bstep (se 1 (by rfl) ⟨402902, by rfl⟩ : syracuseStep 537203 = 805805) B805805
theorem B537219 : Blo 535802 537219 := bstep (se 1 (by rfl) ⟨402914, by rfl⟩ : syracuseStep 537219 = 805829) B805829
theorem B537235 : Blo 535802 537235 := bstep (se 1 (by rfl) ⟨402926, by rfl⟩ : syracuseStep 537235 = 805853) B805853
theorem B537251 : Blo 535802 537251 := bstep (se 1 (by rfl) ⟨402938, by rfl⟩ : syracuseStep 537251 = 805877) B805877
theorem B537267 : Blo 535802 537267 := bstep (se 1 (by rfl) ⟨402950, by rfl⟩ : syracuseStep 537267 = 805901) B805901
theorem B537283 : Blo 535802 537283 := bstep (se 1 (by rfl) ⟨402962, by rfl⟩ : syracuseStep 537283 = 805925) B805925
theorem B1356497 : Blo 535802 1356497 := bstep (se 2 (by rfl) ⟨508686, by rfl⟩ : syracuseStep 1356497 = 1017373) B1017373
theorem B537299 : Blo 535802 537299 := bstep (se 1 (by rfl) ⟨402974, by rfl⟩ : syracuseStep 537299 = 805949) B805949
theorem B766675 : Blo 535802 766675 := bstep (se 1 (by rfl) ⟨575006, by rfl⟩ : syracuseStep 766675 = 1150013) B1150013
theorem B602851 : Blo 535802 602851 := bstep (se 1 (by rfl) ⟨452138, by rfl⟩ : syracuseStep 602851 = 904277) B904277
theorem B537315 : Blo 535802 537315 := bstep (se 1 (by rfl) ⟨402986, by rfl⟩ : syracuseStep 537315 = 805973) B805973
theorem B537331 : Blo 535802 537331 := bstep (se 1 (by rfl) ⟨402998, by rfl⟩ : syracuseStep 537331 = 805997) B805997
theorem B1356547 : Blo 535802 1356547 := bstep (se 1 (by rfl) ⟨1017410, by rfl⟩ : syracuseStep 1356547 = 2034821) B2034821
theorem B537347 : Blo 535802 537347 := bstep (se 1 (by rfl) ⟨403010, by rfl⟩ : syracuseStep 537347 = 806021) B806021
theorem B1291025 : Blo 535802 1291025 := bstep (se 2 (by rfl) ⟨484134, by rfl⟩ : syracuseStep 1291025 = 968269) B968269
theorem B537363 : Blo 535802 537363 := bstep (se 1 (by rfl) ⟨403022, by rfl⟩ : syracuseStep 537363 = 806045) B806045
theorem B537379 : Blo 535802 537379 := bstep (se 1 (by rfl) ⟨403034, by rfl⟩ : syracuseStep 537379 = 806069) B806069
theorem B537395 : Blo 535802 537395 := bstep (se 1 (by rfl) ⟨403046, by rfl⟩ : syracuseStep 537395 = 806093) B806093
theorem B537411 : Blo 535802 537411 := bstep (se 1 (by rfl) ⟨403058, by rfl⟩ : syracuseStep 537411 = 806117) B806117
theorem B537427 : Blo 535802 537427 := bstep (se 1 (by rfl) ⟨403070, by rfl⟩ : syracuseStep 537427 = 806141) B806141
theorem B537443 : Blo 535802 537443 := bstep (se 1 (by rfl) ⟨403082, by rfl⟩ : syracuseStep 537443 = 806165) B806165
theorem B602995 : Blo 535802 602995 := bstep (se 1 (by rfl) ⟨452246, by rfl⟩ : syracuseStep 602995 = 904493) B904493
theorem B537459 : Blo 535802 537459 := bstep (se 1 (by rfl) ⟨403094, by rfl⟩ : syracuseStep 537459 = 806189) B806189
theorem B537475 : Blo 535802 537475 := bstep (se 1 (by rfl) ⟨403106, by rfl⟩ : syracuseStep 537475 = 806213) B806213
theorem B1356689 : Blo 535802 1356689 := bstep (se 2 (by rfl) ⟨508758, by rfl⟩ : syracuseStep 1356689 = 1017517) B1017517
theorem B537491 : Blo 535802 537491 := bstep (se 1 (by rfl) ⟨403118, by rfl⟩ : syracuseStep 537491 = 806237) B806237
theorem B537507 : Blo 535802 537507 := bstep (se 1 (by rfl) ⟨403130, by rfl⟩ : syracuseStep 537507 = 806261) B806261
theorem B537523 : Blo 535802 537523 := bstep (se 1 (by rfl) ⟨403142, by rfl⟩ : syracuseStep 537523 = 806285) B806285
theorem B537539 : Blo 535802 537539 := bstep (se 1 (by rfl) ⟨403154, by rfl⟩ : syracuseStep 537539 = 806309) B806309
theorem B537555 : Blo 535802 537555 := bstep (se 1 (by rfl) ⟨403166, by rfl⟩ : syracuseStep 537555 = 806333) B806333
theorem B537571 : Blo 535802 537571 := bstep (se 1 (by rfl) ⟨403178, by rfl⟩ : syracuseStep 537571 = 806357) B806357
theorem B1815533 : Blo 535802 1815533 := bstep (se 3 (by rfl) ⟨340412, by rfl⟩ : syracuseStep 1815533 = 680825) B680825
theorem B537587 : Blo 535802 537587 := bstep (se 1 (by rfl) ⟨403190, by rfl⟩ : syracuseStep 537587 = 806381) B806381
theorem B603139 : Blo 535802 603139 := bstep (se 1 (by rfl) ⟨452354, by rfl⟩ : syracuseStep 603139 = 904709) B904709
theorem B537603 : Blo 535802 537603 := bstep (se 1 (by rfl) ⟨403202, by rfl⟩ : syracuseStep 537603 = 806405) B806405
theorem B537619 : Blo 535802 537619 := bstep (se 1 (by rfl) ⟨403214, by rfl⟩ : syracuseStep 537619 = 806429) B806429
theorem B767011 : Blo 535802 767011 := bstep (se 1 (by rfl) ⟨575258, by rfl⟩ : syracuseStep 767011 = 1150517) B1150517
theorem B537635 : Blo 535802 537635 := bstep (se 1 (by rfl) ⟨403226, by rfl⟩ : syracuseStep 537635 = 806453) B806453
theorem B1815587 : Blo 535802 1815587 := bstep (se 1 (by rfl) ⟨1361690, by rfl⟩ : syracuseStep 1815587 = 2723381) B2723381
theorem B537651 : Blo 535802 537651 := bstep (se 1 (by rfl) ⟨403238, by rfl⟩ : syracuseStep 537651 = 806477) B806477
theorem B537667 : Blo 535802 537667 := bstep (se 1 (by rfl) ⟨403250, by rfl⟩ : syracuseStep 537667 = 806501) B806501
theorem B4600901 : Blo 535802 4600901 := bstep (se 4 (by rfl) ⟨431334, by rfl⟩ : syracuseStep 4600901 = 862669) B862669
theorem B537683 : Blo 535802 537683 := bstep (se 1 (by rfl) ⟨403262, by rfl⟩ : syracuseStep 537683 = 806525) B806525
theorem B537699 : Blo 535802 537699 := bstep (se 1 (by rfl) ⟨403274, by rfl⟩ : syracuseStep 537699 = 806549) B806549
theorem B2045027 : Blo 535802 2045027 := bstep (se 1 (by rfl) ⟨1533770, by rfl⟩ : syracuseStep 2045027 = 3067541) B3067541
theorem B537715 : Blo 535802 537715 := bstep (se 1 (by rfl) ⟨403286, by rfl⟩ : syracuseStep 537715 = 806573) B806573
theorem B537731 : Blo 535802 537731 := bstep (se 1 (by rfl) ⟨403298, by rfl⟩ : syracuseStep 537731 = 806597) B806597
theorem B1455235 : Blo 535802 1455235 := bstep (se 1 (by rfl) ⟨1091426, by rfl⟩ : syracuseStep 1455235 = 2182853) B2182853
theorem B603283 : Blo 535802 603283 := bstep (se 1 (by rfl) ⟨452462, by rfl⟩ : syracuseStep 603283 = 904925) B904925
theorem B537747 : Blo 535802 537747 := bstep (se 1 (by rfl) ⟨403310, by rfl⟩ : syracuseStep 537747 = 806621) B806621
theorem B537763 : Blo 535802 537763 := bstep (se 1 (by rfl) ⟨403322, by rfl⟩ : syracuseStep 537763 = 806645) B806645
theorem B537779 : Blo 535802 537779 := bstep (se 1 (by rfl) ⟨403334, by rfl⟩ : syracuseStep 537779 = 806669) B806669
theorem B537795 : Blo 535802 537795 := bstep (se 1 (by rfl) ⟨403346, by rfl⟩ : syracuseStep 537795 = 806693) B806693
theorem B537811 : Blo 535802 537811 := bstep (se 1 (by rfl) ⟨403358, by rfl⟩ : syracuseStep 537811 = 806717) B806717
theorem B537827 : Blo 535802 537827 := bstep (se 1 (by rfl) ⟨403370, by rfl⟩ : syracuseStep 537827 = 806741) B806741
theorem B537843 : Blo 535802 537843 := bstep (se 1 (by rfl) ⟨403382, by rfl⟩ : syracuseStep 537843 = 806765) B806765
theorem B537859 : Blo 535802 537859 := bstep (se 1 (by rfl) ⟨403394, by rfl⟩ : syracuseStep 537859 = 806789) B806789
theorem B537875 : Blo 535802 537875 := bstep (se 1 (by rfl) ⟨403406, by rfl⟩ : syracuseStep 537875 = 806813) B806813
theorem B603427 : Blo 535802 603427 := bstep (se 1 (by rfl) ⟨452570, by rfl⟩ : syracuseStep 603427 = 905141) B905141
theorem B537891 : Blo 535802 537891 := bstep (se 1 (by rfl) ⟨403418, by rfl⟩ : syracuseStep 537891 = 806837) B806837
theorem B1815857 : Blo 535802 1815857 := bstep (se 2 (by rfl) ⟨680946, by rfl⟩ : syracuseStep 1815857 = 1361893) B1361893
theorem B537907 : Blo 535802 537907 := bstep (se 1 (by rfl) ⟨403430, by rfl⟩ : syracuseStep 537907 = 806861) B806861
theorem B537923 : Blo 535802 537923 := bstep (se 1 (by rfl) ⟨403442, by rfl⟩ : syracuseStep 537923 = 806885) B806885
theorem B537939 : Blo 535802 537939 := bstep (se 1 (by rfl) ⟨403454, by rfl⟩ : syracuseStep 537939 = 806909) B806909
theorem B537955 : Blo 535802 537955 := bstep (se 1 (by rfl) ⟨403466, by rfl⟩ : syracuseStep 537955 = 806933) B806933
theorem B537971 : Blo 535802 537971 := bstep (se 1 (by rfl) ⟨403478, by rfl⟩ : syracuseStep 537971 = 806957) B806957
theorem B537987 : Blo 535802 537987 := bstep (se 1 (by rfl) ⟨403490, by rfl⟩ : syracuseStep 537987 = 806981) B806981
theorem B538003 : Blo 535802 538003 := bstep (se 1 (by rfl) ⟨403502, by rfl⟩ : syracuseStep 538003 = 807005) B807005
theorem B538019 : Blo 535802 538019 := bstep (se 1 (by rfl) ⟨403514, by rfl⟩ : syracuseStep 538019 = 807029) B807029
theorem B603571 : Blo 535802 603571 := bstep (se 1 (by rfl) ⟨452678, by rfl⟩ : syracuseStep 603571 = 905357) B905357
theorem B538035 : Blo 535802 538035 := bstep (se 1 (by rfl) ⟨403526, by rfl⟩ : syracuseStep 538035 = 807053) B807053
theorem B538051 : Blo 535802 538051 := bstep (se 1 (by rfl) ⟨403538, by rfl⟩ : syracuseStep 538051 = 807077) B807077
theorem B538067 : Blo 535802 538067 := bstep (se 1 (by rfl) ⟨403550, by rfl⟩ : syracuseStep 538067 = 807101) B807101
theorem B538083 : Blo 535802 538083 := bstep (se 1 (by rfl) ⟨403562, by rfl⟩ : syracuseStep 538083 = 807125) B807125
theorem B538099 : Blo 535802 538099 := bstep (se 1 (by rfl) ⟨403574, by rfl⟩ : syracuseStep 538099 = 807149) B807149
theorem B538115 : Blo 535802 538115 := bstep (se 1 (by rfl) ⟨403586, by rfl⟩ : syracuseStep 538115 = 807173) B807173
theorem B3061253 : Blo 535802 3061253 := bstep (se 4 (by rfl) ⟨286992, by rfl⟩ : syracuseStep 3061253 = 573985) B573985
theorem B538131 : Blo 535802 538131 := bstep (se 1 (by rfl) ⟨403598, by rfl⟩ : syracuseStep 538131 = 807197) B807197
theorem B538147 : Blo 535802 538147 := bstep (se 1 (by rfl) ⟨403610, by rfl⟩ : syracuseStep 538147 = 807221) B807221
theorem B2176561 : Blo 535802 2176561 := bstep (se 2 (by rfl) ⟨816210, by rfl⟩ : syracuseStep 2176561 = 1632421) B1632421
theorem B538163 : Blo 535802 538163 := bstep (se 1 (by rfl) ⟨403622, by rfl⟩ : syracuseStep 538163 = 807245) B807245
theorem B603715 : Blo 535802 603715 := bstep (se 1 (by rfl) ⟨452786, by rfl⟩ : syracuseStep 603715 = 905573) B905573
theorem B538179 : Blo 535802 538179 := bstep (se 1 (by rfl) ⟨403634, by rfl⟩ : syracuseStep 538179 = 807269) B807269
theorem B767569 : Blo 535802 767569 := bstep (se 2 (by rfl) ⟨287838, by rfl⟩ : syracuseStep 767569 = 575677) B575677
theorem B538195 : Blo 535802 538195 := bstep (se 1 (by rfl) ⟨403646, by rfl⟩ : syracuseStep 538195 = 807293) B807293
theorem B538211 : Blo 535802 538211 := bstep (se 1 (by rfl) ⟨403658, by rfl⟩ : syracuseStep 538211 = 807317) B807317
theorem B538227 : Blo 535802 538227 := bstep (se 1 (by rfl) ⟨403670, by rfl⟩ : syracuseStep 538227 = 807341) B807341
theorem B767603 : Blo 535802 767603 := bstep (se 1 (by rfl) ⟨575702, by rfl⟩ : syracuseStep 767603 = 1151405) B1151405
theorem B538243 : Blo 535802 538243 := bstep (se 1 (by rfl) ⟨403682, by rfl⟩ : syracuseStep 538243 = 807365) B807365
theorem B538259 : Blo 535802 538259 := bstep (se 1 (by rfl) ⟨403694, by rfl⟩ : syracuseStep 538259 = 807389) B807389
theorem B538275 : Blo 535802 538275 := bstep (se 1 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 538275 = 807413) B807413
theorem B538291 : Blo 535802 538291 := bstep (se 1 (by rfl) ⟨403718, by rfl⟩ : syracuseStep 538291 = 807437) B807437
theorem B538307 : Blo 535802 538307 := bstep (se 1 (by rfl) ⟨403730, by rfl⟩ : syracuseStep 538307 = 807461) B807461
theorem B603859 : Blo 535802 603859 := bstep (se 1 (by rfl) ⟨452894, by rfl⟩ : syracuseStep 603859 = 905789) B905789
theorem B538323 : Blo 535802 538323 := bstep (se 1 (by rfl) ⟨403742, by rfl⟩ : syracuseStep 538323 = 807485) B807485
theorem B11024099 : Blo 535802 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B538339 : Blo 535802 538339 := bstep (se 1 (by rfl) ⟨403754, by rfl⟩ : syracuseStep 538339 = 807509) B807509
theorem B2045681 : Blo 535802 2045681 := bstep (se 2 (by rfl) ⟨767130, by rfl⟩ : syracuseStep 2045681 = 1534261) B1534261
theorem B538355 : Blo 535802 538355 := bstep (se 1 (by rfl) ⟨403766, by rfl⟩ : syracuseStep 538355 = 807533) B807533
theorem B538371 : Blo 535802 538371 := bstep (se 1 (by rfl) ⟨403778, by rfl⟩ : syracuseStep 538371 = 807557) B807557
theorem B2897669 : Blo 535802 2897669 := bstep (se 4 (by rfl) ⟨271656, by rfl⟩ : syracuseStep 2897669 = 543313) B543313
theorem B538387 : Blo 535802 538387 := bstep (se 1 (by rfl) ⟨403790, by rfl⟩ : syracuseStep 538387 = 807581) B807581
theorem B538403 : Blo 535802 538403 := bstep (se 1 (by rfl) ⟨403802, by rfl⟩ : syracuseStep 538403 = 807605) B807605
theorem B538419 : Blo 535802 538419 := bstep (se 1 (by rfl) ⟨403814, by rfl⟩ : syracuseStep 538419 = 807629) B807629
theorem B538435 : Blo 535802 538435 := bstep (se 1 (by rfl) ⟨403826, by rfl⟩ : syracuseStep 538435 = 807653) B807653
theorem B1816397 : Blo 535802 1816397 := bstep (se 3 (by rfl) ⟨340574, by rfl⟩ : syracuseStep 1816397 = 681149) B681149
theorem B538451 : Blo 535802 538451 := bstep (se 1 (by rfl) ⟨403838, by rfl⟩ : syracuseStep 538451 = 807677) B807677
theorem B4896611 : Blo 535802 4896611 := bstep (se 1 (by rfl) ⟨3672458, by rfl⟩ : syracuseStep 4896611 = 7344917) B7344917
theorem B604003 : Blo 535802 604003 := bstep (se 1 (by rfl) ⟨453002, by rfl⟩ : syracuseStep 604003 = 906005) B906005
theorem B538467 : Blo 535802 538467 := bstep (se 1 (by rfl) ⟨403850, by rfl⟩ : syracuseStep 538467 = 807701) B807701
theorem B1357681 : Blo 535802 1357681 := bstep (se 2 (by rfl) ⟨509130, by rfl⟩ : syracuseStep 1357681 = 1018261) B1018261
theorem B538483 : Blo 535802 538483 := bstep (se 1 (by rfl) ⟨403862, by rfl⟩ : syracuseStep 538483 = 807725) B807725
theorem B1816451 : Blo 535802 1816451 := bstep (se 1 (by rfl) ⟨1362338, by rfl⟩ : syracuseStep 1816451 = 2724677) B2724677
theorem B538499 : Blo 535802 538499 := bstep (se 1 (by rfl) ⟨403874, by rfl⟩ : syracuseStep 538499 = 807749) B807749
theorem B538515 : Blo 535802 538515 := bstep (se 1 (by rfl) ⟨403886, by rfl⟩ : syracuseStep 538515 = 807773) B807773
theorem B538531 : Blo 535802 538531 := bstep (se 1 (by rfl) ⟨403898, by rfl⟩ : syracuseStep 538531 = 807797) B807797
theorem B538547 : Blo 535802 538547 := bstep (se 1 (by rfl) ⟨403910, by rfl⟩ : syracuseStep 538547 = 807821) B807821
theorem B538563 : Blo 535802 538563 := bstep (se 1 (by rfl) ⟨403922, by rfl⟩ : syracuseStep 538563 = 807845) B807845
theorem B3061709 : Blo 535802 3061709 := bstep (se 3 (by rfl) ⟨574070, by rfl⟩ : syracuseStep 3061709 = 1148141) B1148141
theorem B538579 : Blo 535802 538579 := bstep (se 1 (by rfl) ⟨403934, by rfl⟩ : syracuseStep 538579 = 807869) B807869
theorem B4077539 : Blo 535802 4077539 := bstep (se 1 (by rfl) ⟨3058154, by rfl⟩ : syracuseStep 4077539 = 6116309) B6116309
theorem B538595 : Blo 535802 538595 := bstep (se 1 (by rfl) ⟨403946, by rfl⟩ : syracuseStep 538595 = 807893) B807893
theorem B604147 : Blo 535802 604147 := bstep (se 1 (by rfl) ⟨453110, by rfl⟩ : syracuseStep 604147 = 906221) B906221
theorem B538611 : Blo 535802 538611 := bstep (se 1 (by rfl) ⟨403958, by rfl⟩ : syracuseStep 538611 = 807917) B807917
theorem B538627 : Blo 535802 538627 := bstep (se 1 (by rfl) ⟨403970, by rfl⟩ : syracuseStep 538627 = 807941) B807941
theorem B538643 : Blo 535802 538643 := bstep (se 1 (by rfl) ⟨403982, by rfl⟩ : syracuseStep 538643 = 807965) B807965
theorem B538659 : Blo 535802 538659 := bstep (se 1 (by rfl) ⟨403994, by rfl⟩ : syracuseStep 538659 = 807989) B807989
theorem B538675 : Blo 535802 538675 := bstep (se 1 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 538675 = 808013) B808013
theorem B538691 : Blo 535802 538691 := bstep (se 1 (by rfl) ⟨404018, by rfl⟩ : syracuseStep 538691 = 808037) B808037
theorem B538707 : Blo 535802 538707 := bstep (se 1 (by rfl) ⟨404030, by rfl⟩ : syracuseStep 538707 = 808061) B808061
theorem B538723 : Blo 535802 538723 := bstep (se 1 (by rfl) ⟨404042, by rfl⟩ : syracuseStep 538723 = 808085) B808085
theorem B538739 : Blo 535802 538739 := bstep (se 1 (by rfl) ⟨404054, by rfl⟩ : syracuseStep 538739 = 808109) B808109
theorem B1357955 : Blo 535802 1357955 := bstep (se 1 (by rfl) ⟨1018466, by rfl⟩ : syracuseStep 1357955 = 2036933) B2036933
theorem B604291 : Blo 535802 604291 := bstep (se 1 (by rfl) ⟨453218, by rfl⟩ : syracuseStep 604291 = 906437) B906437
theorem B538755 : Blo 535802 538755 := bstep (se 1 (by rfl) ⟨404066, by rfl⟩ : syracuseStep 538755 = 808133) B808133
theorem B1816721 : Blo 535802 1816721 := bstep (se 2 (by rfl) ⟨681270, by rfl⟩ : syracuseStep 1816721 = 1362541) B1362541
theorem B538771 : Blo 535802 538771 := bstep (se 1 (by rfl) ⟨404078, by rfl⟩ : syracuseStep 538771 = 808157) B808157
theorem B768161 : Blo 535802 768161 := bstep (se 2 (by rfl) ⟨288060, by rfl⟩ : syracuseStep 768161 = 576121) B576121
theorem B538787 : Blo 535802 538787 := bstep (se 1 (by rfl) ⟨404090, by rfl⟩ : syracuseStep 538787 = 808181) B808181
theorem B538803 : Blo 535802 538803 := bstep (se 1 (by rfl) ⟨404102, by rfl⟩ : syracuseStep 538803 = 808205) B808205
theorem B538819 : Blo 535802 538819 := bstep (se 1 (by rfl) ⟨404114, by rfl⟩ : syracuseStep 538819 = 808229) B808229
theorem B538835 : Blo 535802 538835 := bstep (se 1 (by rfl) ⟨404126, by rfl⟩ : syracuseStep 538835 = 808253) B808253
theorem B538851 : Blo 535802 538851 := bstep (se 1 (by rfl) ⟨404138, by rfl⟩ : syracuseStep 538851 = 808277) B808277
theorem B768241 : Blo 535802 768241 := bstep (se 2 (by rfl) ⟨288090, by rfl⟩ : syracuseStep 768241 = 576181) B576181
theorem B538867 : Blo 535802 538867 := bstep (se 1 (by rfl) ⟨404150, by rfl⟩ : syracuseStep 538867 = 808301) B808301
theorem B538883 : Blo 535802 538883 := bstep (se 1 (by rfl) ⟨404162, by rfl⟩ : syracuseStep 538883 = 808325) B808325
theorem B604435 : Blo 535802 604435 := bstep (se 1 (by rfl) ⟨453326, by rfl⟩ : syracuseStep 604435 = 906653) B906653
theorem B538899 : Blo 535802 538899 := bstep (se 1 (by rfl) ⟨404174, by rfl⟩ : syracuseStep 538899 = 808349) B808349
theorem B538915 : Blo 535802 538915 := bstep (se 1 (by rfl) ⟨404186, by rfl⟩ : syracuseStep 538915 = 808373) B808373
theorem B538931 : Blo 535802 538931 := bstep (se 1 (by rfl) ⟨404198, by rfl⟩ : syracuseStep 538931 = 808397) B808397
theorem B1358147 : Blo 535802 1358147 := bstep (se 1 (by rfl) ⟨1018610, by rfl⟩ : syracuseStep 1358147 = 2037221) B2037221
theorem B538947 : Blo 535802 538947 := bstep (se 1 (by rfl) ⟨404210, by rfl⟩ : syracuseStep 538947 = 808421) B808421
theorem B538963 : Blo 535802 538963 := bstep (se 1 (by rfl) ⟨404222, by rfl⟩ : syracuseStep 538963 = 808445) B808445
theorem B538979 : Blo 535802 538979 := bstep (se 1 (by rfl) ⟨404234, by rfl⟩ : syracuseStep 538979 = 808469) B808469
theorem B538995 : Blo 535802 538995 := bstep (se 1 (by rfl) ⟨404246, by rfl⟩ : syracuseStep 538995 = 808493) B808493
theorem B539011 : Blo 535802 539011 := bstep (se 1 (by rfl) ⟨404258, by rfl⟩ : syracuseStep 539011 = 808517) B808517
theorem B9189773 : Blo 535802 9189773 := bstep (se 3 (by rfl) ⟨1723082, by rfl⟩ : syracuseStep 9189773 = 3446165) B3446165
theorem B539027 : Blo 535802 539027 := bstep (se 1 (by rfl) ⟨404270, by rfl⟩ : syracuseStep 539027 = 808541) B808541
theorem B604579 : Blo 535802 604579 := bstep (se 1 (by rfl) ⟨453434, by rfl⟩ : syracuseStep 604579 = 906869) B906869
theorem B539043 : Blo 535802 539043 := bstep (se 1 (by rfl) ⟨404282, by rfl⟩ : syracuseStep 539043 = 808565) B808565
theorem B539059 : Blo 535802 539059 := bstep (se 1 (by rfl) ⟨404294, by rfl⟩ : syracuseStep 539059 = 808589) B808589
theorem B539075 : Blo 535802 539075 := bstep (se 1 (by rfl) ⟨404306, by rfl⟩ : syracuseStep 539075 = 808613) B808613
theorem B539091 : Blo 535802 539091 := bstep (se 1 (by rfl) ⟨404318, by rfl⟩ : syracuseStep 539091 = 808637) B808637
theorem B539107 : Blo 535802 539107 := bstep (se 1 (by rfl) ⟨404330, by rfl⟩ : syracuseStep 539107 = 808661) B808661
theorem B539123 : Blo 535802 539123 := bstep (se 1 (by rfl) ⟨404342, by rfl⟩ : syracuseStep 539123 = 808685) B808685
theorem B539139 : Blo 535802 539139 := bstep (se 1 (by rfl) ⟨404354, by rfl⟩ : syracuseStep 539139 = 808709) B808709
theorem B539155 : Blo 535802 539155 := bstep (se 1 (by rfl) ⟨404366, by rfl⟩ : syracuseStep 539155 = 808733) B808733
theorem B539171 : Blo 535802 539171 := bstep (se 1 (by rfl) ⟨404378, by rfl⟩ : syracuseStep 539171 = 808757) B808757
theorem B604723 : Blo 535802 604723 := bstep (se 1 (by rfl) ⟨453542, by rfl⟩ : syracuseStep 604723 = 907085) B907085
theorem B539187 : Blo 535802 539187 := bstep (se 1 (by rfl) ⟨404390, by rfl⟩ : syracuseStep 539187 = 808781) B808781
theorem B539203 : Blo 535802 539203 := bstep (se 1 (by rfl) ⟨404402, by rfl⟩ : syracuseStep 539203 = 808805) B808805
theorem B539219 : Blo 535802 539219 := bstep (se 1 (by rfl) ⟨404414, by rfl⟩ : syracuseStep 539219 = 808829) B808829
theorem B539235 : Blo 535802 539235 := bstep (se 1 (by rfl) ⟨404426, by rfl⟩ : syracuseStep 539235 = 808853) B808853
theorem B539251 : Blo 535802 539251 := bstep (se 1 (by rfl) ⟨404438, by rfl⟩ : syracuseStep 539251 = 808877) B808877
theorem B539267 : Blo 535802 539267 := bstep (se 1 (by rfl) ⟨404450, by rfl⟩ : syracuseStep 539267 = 808901) B808901
theorem B539283 : Blo 535802 539283 := bstep (se 1 (by rfl) ⟨404462, by rfl⟩ : syracuseStep 539283 = 808925) B808925
theorem B539299 : Blo 535802 539299 := bstep (se 1 (by rfl) ⟨404474, by rfl⟩ : syracuseStep 539299 = 808949) B808949
theorem B1817261 : Blo 535802 1817261 := bstep (se 3 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 1817261 = 681473) B681473
theorem B539315 : Blo 535802 539315 := bstep (se 1 (by rfl) ⟨404486, by rfl⟩ : syracuseStep 539315 = 808973) B808973
theorem B604867 : Blo 535802 604867 := bstep (se 1 (by rfl) ⟨453650, by rfl⟩ : syracuseStep 604867 = 907301) B907301
theorem B539331 : Blo 535802 539331 := bstep (se 1 (by rfl) ⟨404498, by rfl⟩ : syracuseStep 539331 = 808997) B808997
theorem B539347 : Blo 535802 539347 := bstep (se 1 (by rfl) ⟨404510, by rfl⟩ : syracuseStep 539347 = 809021) B809021
theorem B1817315 : Blo 535802 1817315 := bstep (se 1 (by rfl) ⟨1362986, by rfl⟩ : syracuseStep 1817315 = 2725973) B2725973
theorem B539363 : Blo 535802 539363 := bstep (se 1 (by rfl) ⟨404522, by rfl⟩ : syracuseStep 539363 = 809045) B809045
theorem B539379 : Blo 535802 539379 := bstep (se 1 (by rfl) ⟨404534, by rfl⟩ : syracuseStep 539379 = 809069) B809069
theorem B539395 : Blo 535802 539395 := bstep (se 1 (by rfl) ⟨404546, by rfl⟩ : syracuseStep 539395 = 809093) B809093
theorem B539411 : Blo 535802 539411 := bstep (se 1 (by rfl) ⟨404558, by rfl⟩ : syracuseStep 539411 = 809117) B809117
theorem B539427 : Blo 535802 539427 := bstep (se 1 (by rfl) ⟨404570, by rfl⟩ : syracuseStep 539427 = 809141) B809141
theorem B1719085 : Blo 535802 1719085 := bstep (se 3 (by rfl) ⟨322328, by rfl⟩ : syracuseStep 1719085 = 644657) B644657
theorem B539443 : Blo 535802 539443 := bstep (se 1 (by rfl) ⟨404582, by rfl⟩ : syracuseStep 539443 = 809165) B809165
theorem B539459 : Blo 535802 539459 := bstep (se 1 (by rfl) ⟨404594, by rfl⟩ : syracuseStep 539459 = 809189) B809189
theorem B605011 : Blo 535802 605011 := bstep (se 1 (by rfl) ⟨453758, by rfl⟩ : syracuseStep 605011 = 907517) B907517
theorem B539475 : Blo 535802 539475 := bstep (se 1 (by rfl) ⟨404606, by rfl⟩ : syracuseStep 539475 = 809213) B809213
theorem B539491 : Blo 535802 539491 := bstep (se 1 (by rfl) ⟨404618, by rfl⟩ : syracuseStep 539491 = 809237) B809237
theorem B539507 : Blo 535802 539507 := bstep (se 1 (by rfl) ⟨404630, by rfl⟩ : syracuseStep 539507 = 809261) B809261
theorem B539523 : Blo 535802 539523 := bstep (se 1 (by rfl) ⟨404642, by rfl⟩ : syracuseStep 539523 = 809285) B809285
theorem B539539 : Blo 535802 539539 := bstep (se 1 (by rfl) ⟨404654, by rfl⟩ : syracuseStep 539539 = 809309) B809309
theorem B539555 : Blo 535802 539555 := bstep (se 1 (by rfl) ⟨404666, by rfl⟩ : syracuseStep 539555 = 809333) B809333
theorem B539571 : Blo 535802 539571 := bstep (se 1 (by rfl) ⟨404678, by rfl⟩ : syracuseStep 539571 = 809357) B809357
theorem B539587 : Blo 535802 539587 := bstep (se 1 (by rfl) ⟨404690, by rfl⟩ : syracuseStep 539587 = 809381) B809381
theorem B539603 : Blo 535802 539603 := bstep (se 1 (by rfl) ⟨404702, by rfl⟩ : syracuseStep 539603 = 809405) B809405
theorem B605155 : Blo 535802 605155 := bstep (se 1 (by rfl) ⟨453866, by rfl⟩ : syracuseStep 605155 = 907733) B907733
theorem B539619 : Blo 535802 539619 := bstep (se 1 (by rfl) ⟨404714, by rfl⟩ : syracuseStep 539619 = 809429) B809429
theorem B1817585 : Blo 535802 1817585 := bstep (se 2 (by rfl) ⟨681594, by rfl⟩ : syracuseStep 1817585 = 1363189) B1363189
theorem B539635 : Blo 535802 539635 := bstep (se 1 (by rfl) ⟨404726, by rfl⟩ : syracuseStep 539635 = 809453) B809453
theorem B539651 : Blo 535802 539651 := bstep (se 1 (by rfl) ⟨404738, by rfl⟩ : syracuseStep 539651 = 809477) B809477
theorem B539667 : Blo 535802 539667 := bstep (se 1 (by rfl) ⟨404750, by rfl⟩ : syracuseStep 539667 = 809501) B809501
theorem B539683 : Blo 535802 539683 := bstep (se 1 (by rfl) ⟨404762, by rfl⟩ : syracuseStep 539683 = 809525) B809525
theorem B539699 : Blo 535802 539699 := bstep (se 1 (by rfl) ⟨404774, by rfl⟩ : syracuseStep 539699 = 809549) B809549
theorem B539715 : Blo 535802 539715 := bstep (se 1 (by rfl) ⟨404786, by rfl⟩ : syracuseStep 539715 = 809573) B809573
theorem B539731 : Blo 535802 539731 := bstep (se 1 (by rfl) ⟨404798, by rfl⟩ : syracuseStep 539731 = 809597) B809597
theorem B3914851 : Blo 535802 3914851 := bstep (se 1 (by rfl) ⟨2936138, by rfl⟩ : syracuseStep 3914851 = 5872277) B5872277
theorem B539747 : Blo 535802 539747 := bstep (se 1 (by rfl) ⟨404810, by rfl⟩ : syracuseStep 539747 = 809621) B809621
theorem B605299 : Blo 535802 605299 := bstep (se 1 (by rfl) ⟨453974, by rfl⟩ : syracuseStep 605299 = 907949) B907949
theorem B539763 : Blo 535802 539763 := bstep (se 1 (by rfl) ⟨404822, by rfl⟩ : syracuseStep 539763 = 809645) B809645
theorem B539779 : Blo 535802 539779 := bstep (se 1 (by rfl) ⟨404834, by rfl⟩ : syracuseStep 539779 = 809669) B809669
theorem B539795 : Blo 535802 539795 := bstep (se 1 (by rfl) ⟨404846, by rfl⟩ : syracuseStep 539795 = 809693) B809693
theorem B2047139 : Blo 535802 2047139 := bstep (se 1 (by rfl) ⟨1535354, by rfl⟩ : syracuseStep 2047139 = 3070709) B3070709
theorem B2047153 : Blo 535802 2047153 := bstep (se 2 (by rfl) ⟨767682, by rfl⟩ : syracuseStep 2047153 = 1535365) B1535365
theorem B572627 : Blo 535802 572627 := bstep (se 1 (by rfl) ⟨429470, by rfl⟩ : syracuseStep 572627 = 858941) B858941
theorem B1359089 : Blo 535802 1359089 := bstep (se 2 (by rfl) ⟨509658, by rfl⟩ : syracuseStep 1359089 = 1019317) B1019317
theorem B605443 : Blo 535802 605443 := bstep (se 1 (by rfl) ⟨454082, by rfl⟩ : syracuseStep 605443 = 908165) B908165
theorem B6110477 : Blo 535802 6110477 := bstep (se 3 (by rfl) ⟨1145714, by rfl⟩ : syracuseStep 6110477 = 2291429) B2291429
theorem B1359139 : Blo 535802 1359139 := bstep (se 1 (by rfl) ⟨1019354, by rfl⟩ : syracuseStep 1359139 = 2038709) B2038709
theorem B572755 : Blo 535802 572755 := bstep (se 1 (by rfl) ⟨429566, by rfl⟩ : syracuseStep 572755 = 859133) B859133
theorem B605587 : Blo 535802 605587 := bstep (se 1 (by rfl) ⟨454190, by rfl⟩ : syracuseStep 605587 = 908381) B908381
theorem B1359281 : Blo 535802 1359281 := bstep (se 2 (by rfl) ⟨509730, by rfl⟩ : syracuseStep 1359281 = 1019461) B1019461
theorem B1818125 : Blo 535802 1818125 := bstep (se 3 (by rfl) ⟨340898, by rfl⟩ : syracuseStep 1818125 = 681797) B681797
theorem B605731 : Blo 535802 605731 := bstep (se 1 (by rfl) ⟨454298, by rfl⟩ : syracuseStep 605731 = 908597) B908597
theorem B1818179 : Blo 535802 1818179 := bstep (se 1 (by rfl) ⟨1363634, by rfl⟩ : syracuseStep 1818179 = 2727269) B2727269
theorem B6897251 : Blo 535802 6897251 := bstep (se 1 (by rfl) ⟨5172938, by rfl⟩ : syracuseStep 6897251 = 10345877) B10345877
theorem B1556131 : Blo 535802 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B605875 : Blo 535802 605875 := bstep (se 1 (by rfl) ⟨454406, by rfl⟩ : syracuseStep 605875 = 908813) B908813
theorem B606019 : Blo 535802 606019 := bstep (se 1 (by rfl) ⟨454514, by rfl⟩ : syracuseStep 606019 = 909029) B909029
theorem B1818449 : Blo 535802 1818449 := bstep (se 2 (by rfl) ⟨681918, by rfl⟩ : syracuseStep 1818449 = 1363837) B1363837
theorem B606163 : Blo 535802 606163 := bstep (se 1 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 606163 = 909245) B909245
theorem B11190325 : Blo 535802 11190325 := bstep (se 5 (by rfl) ⟨524546, by rfl⟩ : syracuseStep 11190325 = 1049093) B1049093
theorem B966755 : Blo 535802 966755 := bstep (se 1 (by rfl) ⟨725066, by rfl⟩ : syracuseStep 966755 = 1450133) B1450133
theorem B606307 : Blo 535802 606307 := bstep (se 1 (by rfl) ⟨454730, by rfl⟩ : syracuseStep 606307 = 909461) B909461
theorem B573571 : Blo 535802 573571 := bstep (se 1 (by rfl) ⟨430178, by rfl⟩ : syracuseStep 573571 = 860357) B860357
theorem B1720547 : Blo 535802 1720547 := bstep (se 1 (by rfl) ⟨1290410, by rfl⟩ : syracuseStep 1720547 = 2580821) B2580821
theorem B606451 : Blo 535802 606451 := bstep (se 1 (by rfl) ⟨454838, by rfl⟩ : syracuseStep 606451 = 909677) B909677
theorem B966979 : Blo 535802 966979 := bstep (se 1 (by rfl) ⟨725234, by rfl⟩ : syracuseStep 966979 = 1450469) B1450469
theorem B1818989 : Blo 535802 1818989 := bstep (se 3 (by rfl) ⟨341060, by rfl⟩ : syracuseStep 1818989 = 682121) B682121
theorem B606595 : Blo 535802 606595 := bstep (se 1 (by rfl) ⟨454946, by rfl⟩ : syracuseStep 606595 = 909893) B909893
theorem B1360273 : Blo 535802 1360273 := bstep (se 2 (by rfl) ⟨510102, by rfl⟩ : syracuseStep 1360273 = 1020205) B1020205
theorem B1819043 : Blo 535802 1819043 := bstep (se 1 (by rfl) ⟨1364282, by rfl⟩ : syracuseStep 1819043 = 2728565) B2728565
theorem B606739 : Blo 535802 606739 := bstep (se 1 (by rfl) ⟨455054, by rfl⟩ : syracuseStep 606739 = 910109) B910109
theorem B2048611 : Blo 535802 2048611 := bstep (se 1 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 2048611 = 3072917) B3072917
theorem B1360547 : Blo 535802 1360547 := bstep (se 1 (by rfl) ⟨1020410, by rfl⟩ : syracuseStep 1360547 = 2040821) B2040821
theorem B606883 : Blo 535802 606883 := bstep (se 1 (by rfl) ⟨455162, by rfl⟩ : syracuseStep 606883 = 910325) B910325
theorem B1819313 : Blo 535802 1819313 := bstep (se 2 (by rfl) ⟨682242, by rfl⟩ : syracuseStep 1819313 = 1364485) B1364485
theorem B3064625 : Blo 535802 3064625 := bstep (se 2 (by rfl) ⟨1149234, by rfl⟩ : syracuseStep 3064625 = 2298469) B2298469
theorem B607027 : Blo 535802 607027 := bstep (se 1 (by rfl) ⟨455270, by rfl⟩ : syracuseStep 607027 = 910541) B910541
theorem B1360739 : Blo 535802 1360739 := bstep (se 1 (by rfl) ⟨1020554, by rfl⟩ : syracuseStep 1360739 = 2041109) B2041109
theorem B803729 : Blo 535802 803729 := bstep (se 2 (by rfl) ⟨301398, by rfl⟩ : syracuseStep 803729 = 602797) B602797
theorem B803747 : Blo 535802 803747 := bstep (se 1 (by rfl) ⟨602810, by rfl⟩ : syracuseStep 803747 = 1205621) B1205621
theorem B803777 : Blo 535802 803777 := bstep (se 2 (by rfl) ⟨301416, by rfl⟩ : syracuseStep 803777 = 602833) B602833
theorem B607171 : Blo 535802 607171 := bstep (se 1 (by rfl) ⟨455378, by rfl⟩ : syracuseStep 607171 = 910757) B910757
theorem B803795 : Blo 535802 803795 := bstep (se 1 (by rfl) ⟨602846, by rfl⟩ : syracuseStep 803795 = 1205693) B1205693
theorem B803825 : Blo 535802 803825 := bstep (se 2 (by rfl) ⟨301434, by rfl⟩ : syracuseStep 803825 = 602869) B602869
theorem B803843 : Blo 535802 803843 := bstep (se 1 (by rfl) ⟨602882, by rfl⟩ : syracuseStep 803843 = 1205765) B1205765
theorem B803873 : Blo 535802 803873 := bstep (se 2 (by rfl) ⟨301452, by rfl⟩ : syracuseStep 803873 = 602905) B602905
theorem B803891 : Blo 535802 803891 := bstep (se 1 (by rfl) ⟨602918, by rfl⟩ : syracuseStep 803891 = 1205837) B1205837
theorem B803921 : Blo 535802 803921 := bstep (se 2 (by rfl) ⟨301470, by rfl⟩ : syracuseStep 803921 = 602941) B602941
theorem B803939 : Blo 535802 803939 := bstep (se 1 (by rfl) ⟨602954, by rfl⟩ : syracuseStep 803939 = 1205909) B1205909
theorem B967793 : Blo 535802 967793 := bstep (se 2 (by rfl) ⟨362922, by rfl⟩ : syracuseStep 967793 = 725845) B725845
theorem B803969 : Blo 535802 803969 := bstep (se 2 (by rfl) ⟨301488, by rfl⟩ : syracuseStep 803969 = 602977) B602977
theorem B3687565 : Blo 535802 3687565 := bstep (se 3 (by rfl) ⟨691418, by rfl⟩ : syracuseStep 3687565 = 1382837) B1382837
theorem B803987 : Blo 535802 803987 := bstep (se 1 (by rfl) ⟨602990, by rfl⟩ : syracuseStep 803987 = 1205981) B1205981
theorem B804017 : Blo 535802 804017 := bstep (se 2 (by rfl) ⟨301506, by rfl⟩ : syracuseStep 804017 = 603013) B603013
theorem B804035 : Blo 535802 804035 := bstep (se 1 (by rfl) ⟨603026, by rfl⟩ : syracuseStep 804035 = 1206053) B1206053
theorem B1819853 : Blo 535802 1819853 := bstep (se 3 (by rfl) ⟨341222, by rfl⟩ : syracuseStep 1819853 = 682445) B682445
theorem B804065 : Blo 535802 804065 := bstep (se 2 (by rfl) ⟨301524, by rfl⟩ : syracuseStep 804065 = 603049) B603049
theorem B804083 : Blo 535802 804083 := bstep (se 1 (by rfl) ⟨603062, by rfl⟩ : syracuseStep 804083 = 1206125) B1206125
theorem B1819907 : Blo 535802 1819907 := bstep (se 1 (by rfl) ⟨1364930, by rfl⟩ : syracuseStep 1819907 = 2729861) B2729861
theorem B1230083 : Blo 535802 1230083 := bstep (se 1 (by rfl) ⟨922562, by rfl⟩ : syracuseStep 1230083 = 1845125) B1845125
theorem B804113 : Blo 535802 804113 := bstep (se 2 (by rfl) ⟨301542, by rfl⟩ : syracuseStep 804113 = 603085) B603085
theorem B804131 : Blo 535802 804131 := bstep (se 1 (by rfl) ⟨603098, by rfl⟩ : syracuseStep 804131 = 1206197) B1206197
theorem B804161 : Blo 535802 804161 := bstep (se 2 (by rfl) ⟨301560, by rfl⟩ : syracuseStep 804161 = 603121) B603121
theorem B804179 : Blo 535802 804179 := bstep (se 1 (by rfl) ⟨603134, by rfl⟩ : syracuseStep 804179 = 1206269) B1206269
theorem B804209 : Blo 535802 804209 := bstep (se 2 (by rfl) ⟨301578, by rfl⟩ : syracuseStep 804209 = 603157) B603157
theorem B804227 : Blo 535802 804227 := bstep (se 1 (by rfl) ⟨603170, by rfl⟩ : syracuseStep 804227 = 1206341) B1206341
theorem B804257 : Blo 535802 804257 := bstep (se 2 (by rfl) ⟨301596, by rfl⟩ : syracuseStep 804257 = 603193) B603193
theorem B3458467 : Blo 535802 3458467 := bstep (se 1 (by rfl) ⟨2593850, by rfl⟩ : syracuseStep 3458467 = 5187701) B5187701
theorem B804275 : Blo 535802 804275 := bstep (se 1 (by rfl) ⟨603206, by rfl⟩ : syracuseStep 804275 = 1206413) B1206413
theorem B804305 : Blo 535802 804305 := bstep (se 2 (by rfl) ⟨301614, by rfl⟩ : syracuseStep 804305 = 603229) B603229
theorem B804323 : Blo 535802 804323 := bstep (se 1 (by rfl) ⟨603242, by rfl⟩ : syracuseStep 804323 = 1206485) B1206485
theorem B804353 : Blo 535802 804353 := bstep (se 2 (by rfl) ⟨301632, by rfl⟩ : syracuseStep 804353 = 603265) B603265
theorem B1820177 : Blo 535802 1820177 := bstep (se 2 (by rfl) ⟨682566, by rfl⟩ : syracuseStep 1820177 = 1365133) B1365133
theorem B804371 : Blo 535802 804371 := bstep (se 1 (by rfl) ⟨603278, by rfl⟩ : syracuseStep 804371 = 1206557) B1206557
theorem B804401 : Blo 535802 804401 := bstep (se 2 (by rfl) ⟨301650, by rfl⟩ : syracuseStep 804401 = 603301) B603301
theorem B804419 : Blo 535802 804419 := bstep (se 1 (by rfl) ⟨603314, by rfl⟩ : syracuseStep 804419 = 1206629) B1206629
theorem B804449 : Blo 535802 804449 := bstep (se 2 (by rfl) ⟨301668, by rfl⟩ : syracuseStep 804449 = 603337) B603337
theorem B1033841 : Blo 535802 1033841 := bstep (se 2 (by rfl) ⟨387690, by rfl⟩ : syracuseStep 1033841 = 775381) B775381
theorem B804467 : Blo 535802 804467 := bstep (se 1 (by rfl) ⟨603350, by rfl⟩ : syracuseStep 804467 = 1206701) B1206701
theorem B804497 : Blo 535802 804497 := bstep (se 2 (by rfl) ⟨301686, by rfl⟩ : syracuseStep 804497 = 603373) B603373
theorem B804515 : Blo 535802 804515 := bstep (se 1 (by rfl) ⟨603386, by rfl⟩ : syracuseStep 804515 = 1206773) B1206773
theorem B804545 : Blo 535802 804545 := bstep (se 2 (by rfl) ⟨301704, by rfl⟩ : syracuseStep 804545 = 603409) B603409
theorem B804563 : Blo 535802 804563 := bstep (se 1 (by rfl) ⟨603422, by rfl⟩ : syracuseStep 804563 = 1206845) B1206845
theorem B804593 : Blo 535802 804593 := bstep (se 2 (by rfl) ⟨301722, by rfl⟩ : syracuseStep 804593 = 603445) B603445
theorem B804611 : Blo 535802 804611 := bstep (se 1 (by rfl) ⟨603458, by rfl⟩ : syracuseStep 804611 = 1206917) B1206917
theorem B1361681 : Blo 535802 1361681 := bstep (se 2 (by rfl) ⟨510630, by rfl⟩ : syracuseStep 1361681 = 1021261) B1021261
theorem B804641 : Blo 535802 804641 := bstep (se 2 (by rfl) ⟨301740, by rfl⟩ : syracuseStep 804641 = 603481) B603481
theorem B1722161 : Blo 535802 1722161 := bstep (se 2 (by rfl) ⟨645810, by rfl⟩ : syracuseStep 1722161 = 1291621) B1291621
theorem B804659 : Blo 535802 804659 := bstep (se 1 (by rfl) ⟨603494, by rfl⟩ : syracuseStep 804659 = 1206989) B1206989
theorem B1361731 : Blo 535802 1361731 := bstep (se 1 (by rfl) ⟨1021298, by rfl⟩ : syracuseStep 1361731 = 2042597) B2042597
theorem B804689 : Blo 535802 804689 := bstep (se 2 (by rfl) ⟨301758, by rfl⟩ : syracuseStep 804689 = 603517) B603517
theorem B804707 : Blo 535802 804707 := bstep (se 1 (by rfl) ⟨603530, by rfl⟩ : syracuseStep 804707 = 1207061) B1207061
theorem B804737 : Blo 535802 804737 := bstep (se 2 (by rfl) ⟨301776, by rfl⟩ : syracuseStep 804737 = 603553) B603553
theorem B804755 : Blo 535802 804755 := bstep (se 1 (by rfl) ⟨603566, by rfl⟩ : syracuseStep 804755 = 1207133) B1207133
theorem B804785 : Blo 535802 804785 := bstep (se 2 (by rfl) ⟨301794, by rfl⟩ : syracuseStep 804785 = 603589) B603589
theorem B804803 : Blo 535802 804803 := bstep (se 1 (by rfl) ⟨603602, by rfl⟩ : syracuseStep 804803 = 1207205) B1207205
theorem B1361873 : Blo 535802 1361873 := bstep (se 2 (by rfl) ⟨510702, by rfl⟩ : syracuseStep 1361873 = 1021405) B1021405
theorem B804833 : Blo 535802 804833 := bstep (se 2 (by rfl) ⟨301812, by rfl⟩ : syracuseStep 804833 = 603625) B603625
theorem B804851 : Blo 535802 804851 := bstep (se 1 (by rfl) ⟨603638, by rfl⟩ : syracuseStep 804851 = 1207277) B1207277
theorem B804881 : Blo 535802 804881 := bstep (se 2 (by rfl) ⟨301830, by rfl⟩ : syracuseStep 804881 = 603661) B603661
theorem B804899 : Blo 535802 804899 := bstep (se 1 (by rfl) ⟨603674, by rfl⟩ : syracuseStep 804899 = 1207349) B1207349
theorem B1820717 : Blo 535802 1820717 := bstep (se 3 (by rfl) ⟨341384, by rfl⟩ : syracuseStep 1820717 = 682769) B682769
theorem B804929 : Blo 535802 804929 := bstep (se 2 (by rfl) ⟨301848, by rfl⟩ : syracuseStep 804929 = 603697) B603697
theorem B804947 : Blo 535802 804947 := bstep (se 1 (by rfl) ⟨603710, by rfl⟩ : syracuseStep 804947 = 1207421) B1207421
theorem B1820771 : Blo 535802 1820771 := bstep (se 1 (by rfl) ⟨1365578, by rfl⟩ : syracuseStep 1820771 = 2731157) B2731157
theorem B804977 : Blo 535802 804977 := bstep (se 2 (by rfl) ⟨301866, by rfl⟩ : syracuseStep 804977 = 603733) B603733
theorem B6113393 : Blo 535802 6113393 := bstep (se 2 (by rfl) ⟨2292522, by rfl⟩ : syracuseStep 6113393 = 4585045) B4585045
theorem B804995 : Blo 535802 804995 := bstep (se 1 (by rfl) ⟨603746, by rfl⟩ : syracuseStep 804995 = 1207493) B1207493
theorem B805025 : Blo 535802 805025 := bstep (se 2 (by rfl) ⟨301884, by rfl⟩ : syracuseStep 805025 = 603769) B603769
theorem B805043 : Blo 535802 805043 := bstep (se 1 (by rfl) ⟨603782, by rfl⟩ : syracuseStep 805043 = 1207565) B1207565
theorem B805073 : Blo 535802 805073 := bstep (se 2 (by rfl) ⟨301902, by rfl⟩ : syracuseStep 805073 = 603805) B603805
theorem B805091 : Blo 535802 805091 := bstep (se 1 (by rfl) ⟨603818, by rfl⟩ : syracuseStep 805091 = 1207637) B1207637
theorem B3066083 : Blo 535802 3066083 := bstep (se 1 (by rfl) ⟨2299562, by rfl⟩ : syracuseStep 3066083 = 4599125) B4599125
theorem B1296611 : Blo 535802 1296611 := bstep (se 1 (by rfl) ⟨972458, by rfl⟩ : syracuseStep 1296611 = 1944917) B1944917
theorem B805121 : Blo 535802 805121 := bstep (se 2 (by rfl) ⟨301920, by rfl⟩ : syracuseStep 805121 = 603841) B603841
theorem B805139 : Blo 535802 805139 := bstep (se 1 (by rfl) ⟨603854, by rfl⟩ : syracuseStep 805139 = 1207709) B1207709
theorem B805169 : Blo 535802 805169 := bstep (se 2 (by rfl) ⟨301938, by rfl⟩ : syracuseStep 805169 = 603877) B603877
theorem B805187 : Blo 535802 805187 := bstep (se 1 (by rfl) ⟨603890, by rfl⟩ : syracuseStep 805187 = 1207781) B1207781
theorem B805217 : Blo 535802 805217 := bstep (se 2 (by rfl) ⟨301956, by rfl⟩ : syracuseStep 805217 = 603913) B603913
theorem B1821041 : Blo 535802 1821041 := bstep (se 2 (by rfl) ⟨682890, by rfl⟩ : syracuseStep 1821041 = 1365781) B1365781
theorem B805235 : Blo 535802 805235 := bstep (se 1 (by rfl) ⟨603926, by rfl⟩ : syracuseStep 805235 = 1207853) B1207853
theorem B805265 : Blo 535802 805265 := bstep (se 2 (by rfl) ⟨301974, by rfl⟩ : syracuseStep 805265 = 603949) B603949
theorem B805283 : Blo 535802 805283 := bstep (se 1 (by rfl) ⟨603962, by rfl⟩ : syracuseStep 805283 = 1207925) B1207925
theorem B805313 : Blo 535802 805313 := bstep (se 2 (by rfl) ⟨301992, by rfl⟩ : syracuseStep 805313 = 603985) B603985
theorem B805331 : Blo 535802 805331 := bstep (se 1 (by rfl) ⟨603998, by rfl⟩ : syracuseStep 805331 = 1207997) B1207997
theorem B805361 : Blo 535802 805361 := bstep (se 2 (by rfl) ⟨302010, by rfl⟩ : syracuseStep 805361 = 604021) B604021
theorem B805379 : Blo 535802 805379 := bstep (se 1 (by rfl) ⟨604034, by rfl⟩ : syracuseStep 805379 = 1208069) B1208069
theorem B805409 : Blo 535802 805409 := bstep (se 2 (by rfl) ⟨302028, by rfl⟩ : syracuseStep 805409 = 604057) B604057
theorem B805427 : Blo 535802 805427 := bstep (se 1 (by rfl) ⟨604070, by rfl⟩ : syracuseStep 805427 = 1208141) B1208141
theorem B805457 : Blo 535802 805457 := bstep (se 2 (by rfl) ⟨302046, by rfl⟩ : syracuseStep 805457 = 604093) B604093
theorem B805475 : Blo 535802 805475 := bstep (se 1 (by rfl) ⟨604106, by rfl⟩ : syracuseStep 805475 = 1208213) B1208213
theorem B805505 : Blo 535802 805505 := bstep (se 2 (by rfl) ⟨302064, by rfl⟩ : syracuseStep 805505 = 604129) B604129
theorem B805523 : Blo 535802 805523 := bstep (se 1 (by rfl) ⟨604142, by rfl⟩ : syracuseStep 805523 = 1208285) B1208285
theorem B1526435 : Blo 535802 1526435 := bstep (se 1 (by rfl) ⟨1144826, by rfl⟩ : syracuseStep 1526435 = 2289653) B2289653
theorem B805553 : Blo 535802 805553 := bstep (se 2 (by rfl) ⟨302082, by rfl⟩ : syracuseStep 805553 = 604165) B604165
theorem B805571 : Blo 535802 805571 := bstep (se 1 (by rfl) ⟨604178, by rfl⟩ : syracuseStep 805571 = 1208357) B1208357
theorem B805601 : Blo 535802 805601 := bstep (se 2 (by rfl) ⟨302100, by rfl⟩ : syracuseStep 805601 = 604201) B604201
theorem B805619 : Blo 535802 805619 := bstep (se 1 (by rfl) ⟨604214, by rfl⟩ : syracuseStep 805619 = 1208429) B1208429
theorem B805649 : Blo 535802 805649 := bstep (se 2 (by rfl) ⟨302118, by rfl⟩ : syracuseStep 805649 = 604237) B604237
theorem B805667 : Blo 535802 805667 := bstep (se 1 (by rfl) ⟨604250, by rfl⟩ : syracuseStep 805667 = 1208501) B1208501
theorem B805697 : Blo 535802 805697 := bstep (se 2 (by rfl) ⟨302136, by rfl⟩ : syracuseStep 805697 = 604273) B604273
theorem B805715 : Blo 535802 805715 := bstep (se 1 (by rfl) ⟨604286, by rfl⟩ : syracuseStep 805715 = 1208573) B1208573
theorem B805745 : Blo 535802 805745 := bstep (se 2 (by rfl) ⟨302154, by rfl⟩ : syracuseStep 805745 = 604309) B604309
theorem B805763 : Blo 535802 805763 := bstep (se 1 (by rfl) ⟨604322, by rfl⟩ : syracuseStep 805763 = 1208645) B1208645
theorem B1821581 : Blo 535802 1821581 := bstep (se 3 (by rfl) ⟨341546, by rfl⟩ : syracuseStep 1821581 = 683093) B683093
theorem B805793 : Blo 535802 805793 := bstep (se 2 (by rfl) ⟨302172, by rfl⟩ : syracuseStep 805793 = 604345) B604345
theorem B1362865 : Blo 535802 1362865 := bstep (se 2 (by rfl) ⟨511074, by rfl⟩ : syracuseStep 1362865 = 1022149) B1022149
theorem B805811 : Blo 535802 805811 := bstep (se 1 (by rfl) ⟨604358, by rfl⟩ : syracuseStep 805811 = 1208717) B1208717
theorem B1821635 : Blo 535802 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B805841 : Blo 535802 805841 := bstep (se 2 (by rfl) ⟨302190, by rfl⟩ : syracuseStep 805841 = 604381) B604381
theorem B805859 : Blo 535802 805859 := bstep (se 1 (by rfl) ⟨604394, by rfl⟩ : syracuseStep 805859 = 1208789) B1208789
theorem B805889 : Blo 535802 805889 := bstep (se 2 (by rfl) ⟨302208, by rfl⟩ : syracuseStep 805889 = 604417) B604417
theorem B805907 : Blo 535802 805907 := bstep (se 1 (by rfl) ⟨604430, by rfl⟩ : syracuseStep 805907 = 1208861) B1208861
theorem B805937 : Blo 535802 805937 := bstep (se 2 (by rfl) ⟨302226, by rfl⟩ : syracuseStep 805937 = 604453) B604453
theorem B904243 : Blo 535802 904243 := bstep (se 1 (by rfl) ⟨678182, by rfl⟩ : syracuseStep 904243 = 1356365) B1356365
theorem B805955 : Blo 535802 805955 := bstep (se 1 (by rfl) ⟨604466, by rfl⟩ : syracuseStep 805955 = 1208933) B1208933
theorem B805985 : Blo 535802 805985 := bstep (se 2 (by rfl) ⟨302244, by rfl⟩ : syracuseStep 805985 = 604489) B604489
theorem B23645297 : Blo 535802 23645297 := bstep (se 2 (by rfl) ⟨8866986, by rfl⟩ : syracuseStep 23645297 = 17733973) B17733973
theorem B806003 : Blo 535802 806003 := bstep (se 1 (by rfl) ⟨604502, by rfl⟩ : syracuseStep 806003 = 1209005) B1209005
theorem B806033 : Blo 535802 806033 := bstep (se 2 (by rfl) ⟨302262, by rfl⟩ : syracuseStep 806033 = 604525) B604525
theorem B806051 : Blo 535802 806051 := bstep (se 1 (by rfl) ⟨604538, by rfl⟩ : syracuseStep 806051 = 1209077) B1209077
theorem B904385 : Blo 535802 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B806081 : Blo 535802 806081 := bstep (se 2 (by rfl) ⟨302280, by rfl⟩ : syracuseStep 806081 = 604561) B604561
theorem B1363139 : Blo 535802 1363139 := bstep (se 1 (by rfl) ⟨1022354, by rfl⟩ : syracuseStep 1363139 = 2044709) B2044709
theorem B4082885 : Blo 535802 4082885 := bstep (se 4 (by rfl) ⟨382770, by rfl⟩ : syracuseStep 4082885 = 765541) B765541
theorem B3067085 : Blo 535802 3067085 := bstep (se 3 (by rfl) ⟨575078, by rfl⟩ : syracuseStep 3067085 = 1150157) B1150157
theorem B806099 : Blo 535802 806099 := bstep (se 1 (by rfl) ⟨604574, by rfl⟩ : syracuseStep 806099 = 1209149) B1209149
theorem B806129 : Blo 535802 806129 := bstep (se 2 (by rfl) ⟨302298, by rfl⟩ : syracuseStep 806129 = 604597) B604597
theorem B806147 : Blo 535802 806147 := bstep (se 1 (by rfl) ⟨604610, by rfl⟩ : syracuseStep 806147 = 1209221) B1209221
theorem B806177 : Blo 535802 806177 := bstep (se 2 (by rfl) ⟨302316, by rfl⟩ : syracuseStep 806177 = 604633) B604633
theorem B806195 : Blo 535802 806195 := bstep (se 1 (by rfl) ⟨604646, by rfl⟩ : syracuseStep 806195 = 1209293) B1209293
theorem B904513 : Blo 535802 904513 := bstep (se 2 (by rfl) ⟨339192, by rfl⟩ : syracuseStep 904513 = 678385) B678385
theorem B806225 : Blo 535802 806225 := bstep (se 2 (by rfl) ⟨302334, by rfl⟩ : syracuseStep 806225 = 604669) B604669
theorem B904547 : Blo 535802 904547 := bstep (se 1 (by rfl) ⟨678410, by rfl⟩ : syracuseStep 904547 = 1356821) B1356821
theorem B806243 : Blo 535802 806243 := bstep (se 1 (by rfl) ⟨604682, by rfl⟩ : syracuseStep 806243 = 1209365) B1209365
theorem B806273 : Blo 535802 806273 := bstep (se 2 (by rfl) ⟨302352, by rfl⟩ : syracuseStep 806273 = 604705) B604705
theorem B1363331 : Blo 535802 1363331 := bstep (se 1 (by rfl) ⟨1022498, by rfl⟩ : syracuseStep 1363331 = 2044997) B2044997
theorem B806291 : Blo 535802 806291 := bstep (se 1 (by rfl) ⟨604718, by rfl⟩ : syracuseStep 806291 = 1209437) B1209437
theorem B3689891 : Blo 535802 3689891 := bstep (se 1 (by rfl) ⟨2767418, by rfl⟩ : syracuseStep 3689891 = 5534837) B5534837
theorem B806321 : Blo 535802 806321 := bstep (se 2 (by rfl) ⟨302370, by rfl⟩ : syracuseStep 806321 = 604741) B604741
theorem B806339 : Blo 535802 806339 := bstep (se 1 (by rfl) ⟨604754, by rfl⟩ : syracuseStep 806339 = 1209509) B1209509
theorem B1527245 : Blo 535802 1527245 := bstep (se 3 (by rfl) ⟨286358, by rfl⟩ : syracuseStep 1527245 = 572717) B572717
theorem B806369 : Blo 535802 806369 := bstep (se 2 (by rfl) ⟨302388, by rfl⟩ : syracuseStep 806369 = 604777) B604777
theorem B904675 : Blo 535802 904675 := bstep (se 1 (by rfl) ⟨678506, by rfl⟩ : syracuseStep 904675 = 1357013) B1357013
theorem B806387 : Blo 535802 806387 := bstep (se 1 (by rfl) ⟨604790, by rfl⟩ : syracuseStep 806387 = 1209581) B1209581
theorem B806417 : Blo 535802 806417 := bstep (se 2 (by rfl) ⟨302406, by rfl⟩ : syracuseStep 806417 = 604813) B604813
theorem B806435 : Blo 535802 806435 := bstep (se 1 (by rfl) ⟨604826, by rfl⟩ : syracuseStep 806435 = 1209653) B1209653
theorem B806465 : Blo 535802 806465 := bstep (se 2 (by rfl) ⟨302424, by rfl⟩ : syracuseStep 806465 = 604849) B604849
theorem B806483 : Blo 535802 806483 := bstep (se 1 (by rfl) ⟨604862, by rfl⟩ : syracuseStep 806483 = 1209725) B1209725
theorem B904817 : Blo 535802 904817 := bstep (se 2 (by rfl) ⟨339306, by rfl⟩ : syracuseStep 904817 = 678613) B678613
theorem B806513 : Blo 535802 806513 := bstep (se 2 (by rfl) ⟨302442, by rfl⟩ : syracuseStep 806513 = 604885) B604885
theorem B806531 : Blo 535802 806531 := bstep (se 1 (by rfl) ⟨604898, by rfl⟩ : syracuseStep 806531 = 1209797) B1209797
theorem B1527437 : Blo 535802 1527437 := bstep (se 3 (by rfl) ⟨286394, by rfl⟩ : syracuseStep 1527437 = 572789) B572789
theorem B806561 : Blo 535802 806561 := bstep (se 2 (by rfl) ⟨302460, by rfl⟩ : syracuseStep 806561 = 604921) B604921
theorem B806579 : Blo 535802 806579 := bstep (se 1 (by rfl) ⟨604934, by rfl⟩ : syracuseStep 806579 = 1209869) B1209869
theorem B806609 : Blo 535802 806609 := bstep (se 2 (by rfl) ⟨302478, by rfl⟩ : syracuseStep 806609 = 604957) B604957
theorem B806627 : Blo 535802 806627 := bstep (se 1 (by rfl) ⟨604970, by rfl⟩ : syracuseStep 806627 = 1209941) B1209941
theorem B904945 : Blo 535802 904945 := bstep (se 2 (by rfl) ⟨339354, by rfl⟩ : syracuseStep 904945 = 678709) B678709
theorem B806657 : Blo 535802 806657 := bstep (se 2 (by rfl) ⟨302496, by rfl⟩ : syracuseStep 806657 = 604993) B604993
theorem B2903813 : Blo 535802 2903813 := bstep (se 4 (by rfl) ⟨272232, by rfl⟩ : syracuseStep 2903813 = 544465) B544465
theorem B904979 : Blo 535802 904979 := bstep (se 1 (by rfl) ⟨678734, by rfl⟩ : syracuseStep 904979 = 1357469) B1357469
theorem B806675 : Blo 535802 806675 := bstep (se 1 (by rfl) ⟨605006, by rfl⟩ : syracuseStep 806675 = 1210013) B1210013
theorem B806705 : Blo 535802 806705 := bstep (se 2 (by rfl) ⟨302514, by rfl⟩ : syracuseStep 806705 = 605029) B605029
theorem B806723 : Blo 535802 806723 := bstep (se 1 (by rfl) ⟨605042, by rfl⟩ : syracuseStep 806723 = 1210085) B1210085
theorem B1724237 : Blo 535802 1724237 := bstep (se 3 (by rfl) ⟨323294, by rfl⟩ : syracuseStep 1724237 = 646589) B646589
theorem B806753 : Blo 535802 806753 := bstep (se 2 (by rfl) ⟨302532, by rfl⟩ : syracuseStep 806753 = 605065) B605065
theorem B806771 : Blo 535802 806771 := bstep (se 1 (by rfl) ⟨605078, by rfl⟩ : syracuseStep 806771 = 1210157) B1210157
theorem B10309517 : Blo 535802 10309517 := bstep (se 3 (by rfl) ⟨1933034, by rfl⟩ : syracuseStep 10309517 = 3866069) B3866069
theorem B806801 : Blo 535802 806801 := bstep (se 2 (by rfl) ⟨302550, by rfl⟩ : syracuseStep 806801 = 605101) B605101
theorem B905107 : Blo 535802 905107 := bstep (se 1 (by rfl) ⟨678830, by rfl⟩ : syracuseStep 905107 = 1357661) B1357661
theorem B806819 : Blo 535802 806819 := bstep (se 1 (by rfl) ⟨605114, by rfl⟩ : syracuseStep 806819 = 1210229) B1210229
theorem B806849 : Blo 535802 806849 := bstep (se 2 (by rfl) ⟨302568, by rfl⟩ : syracuseStep 806849 = 605137) B605137
theorem B806867 : Blo 535802 806867 := bstep (se 1 (by rfl) ⟨605150, by rfl⟩ : syracuseStep 806867 = 1210301) B1210301
theorem B806897 : Blo 535802 806897 := bstep (se 2 (by rfl) ⟨302586, by rfl⟩ : syracuseStep 806897 = 605173) B605173
theorem B806915 : Blo 535802 806915 := bstep (se 1 (by rfl) ⟨605186, by rfl⟩ : syracuseStep 806915 = 1210373) B1210373
theorem B872465 : Blo 535802 872465 := bstep (se 2 (by rfl) ⟨327174, by rfl⟩ : syracuseStep 872465 = 654349) B654349
theorem B905249 : Blo 535802 905249 := bstep (se 2 (by rfl) ⟨339468, by rfl⟩ : syracuseStep 905249 = 678937) B678937
theorem B806945 : Blo 535802 806945 := bstep (se 2 (by rfl) ⟨302604, by rfl⟩ : syracuseStep 806945 = 605209) B605209
theorem B806963 : Blo 535802 806963 := bstep (se 1 (by rfl) ⟨605222, by rfl⟩ : syracuseStep 806963 = 1210445) B1210445
theorem B806993 : Blo 535802 806993 := bstep (se 2 (by rfl) ⟨302622, by rfl⟩ : syracuseStep 806993 = 605245) B605245
theorem B807011 : Blo 535802 807011 := bstep (se 1 (by rfl) ⟨605258, by rfl⟩ : syracuseStep 807011 = 1210517) B1210517
theorem B807041 : Blo 535802 807041 := bstep (se 2 (by rfl) ⟨302640, by rfl⟩ : syracuseStep 807041 = 605281) B605281
theorem B6312077 : Blo 535802 6312077 := bstep (se 3 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 6312077 = 2367029) B2367029
theorem B807059 : Blo 535802 807059 := bstep (se 1 (by rfl) ⟨605294, by rfl⟩ : syracuseStep 807059 = 1210589) B1210589
theorem B905377 : Blo 535802 905377 := bstep (se 2 (by rfl) ⟨339516, by rfl⟩ : syracuseStep 905377 = 679033) B679033
theorem B807089 : Blo 535802 807089 := bstep (se 2 (by rfl) ⟨302658, by rfl⟩ : syracuseStep 807089 = 605317) B605317
theorem B905411 : Blo 535802 905411 := bstep (se 1 (by rfl) ⟨679058, by rfl⟩ : syracuseStep 905411 = 1358117) B1358117
theorem B807107 : Blo 535802 807107 := bstep (se 1 (by rfl) ⟨605330, by rfl⟩ : syracuseStep 807107 = 1210661) B1210661
theorem B807137 : Blo 535802 807137 := bstep (se 2 (by rfl) ⟨302676, by rfl⟩ : syracuseStep 807137 = 605353) B605353
theorem B807155 : Blo 535802 807155 := bstep (se 1 (by rfl) ⟨605366, by rfl⟩ : syracuseStep 807155 = 1210733) B1210733
theorem B807185 : Blo 535802 807185 := bstep (se 2 (by rfl) ⟨302694, by rfl⟩ : syracuseStep 807185 = 605389) B605389
theorem B807203 : Blo 535802 807203 := bstep (se 1 (by rfl) ⟨605402, by rfl⟩ : syracuseStep 807203 = 1210805) B1210805
theorem B1364273 : Blo 535802 1364273 := bstep (se 2 (by rfl) ⟨511602, by rfl⟩ : syracuseStep 1364273 = 1023205) B1023205
theorem B807233 : Blo 535802 807233 := bstep (se 2 (by rfl) ⟨302712, by rfl⟩ : syracuseStep 807233 = 605425) B605425
theorem B905539 : Blo 535802 905539 := bstep (se 1 (by rfl) ⟨679154, by rfl⟩ : syracuseStep 905539 = 1358309) B1358309
theorem B807251 : Blo 535802 807251 := bstep (se 1 (by rfl) ⟨605438, by rfl⟩ : syracuseStep 807251 = 1210877) B1210877
theorem B1364323 : Blo 535802 1364323 := bstep (se 1 (by rfl) ⟨1023242, by rfl⟩ : syracuseStep 1364323 = 2046485) B2046485
theorem B807281 : Blo 535802 807281 := bstep (se 2 (by rfl) ⟨302730, by rfl⟩ : syracuseStep 807281 = 605461) B605461
theorem B2183537 : Blo 535802 2183537 := bstep (se 2 (by rfl) ⟨818826, by rfl⟩ : syracuseStep 2183537 = 1637653) B1637653
theorem B807299 : Blo 535802 807299 := bstep (se 1 (by rfl) ⟨605474, by rfl⟩ : syracuseStep 807299 = 1210949) B1210949
theorem B807329 : Blo 535802 807329 := bstep (se 2 (by rfl) ⟨302748, by rfl⟩ : syracuseStep 807329 = 605497) B605497
theorem B807347 : Blo 535802 807347 := bstep (se 1 (by rfl) ⟨605510, by rfl⟩ : syracuseStep 807347 = 1211021) B1211021
theorem B905681 : Blo 535802 905681 := bstep (se 2 (by rfl) ⟨339630, by rfl⟩ : syracuseStep 905681 = 679261) B679261
theorem B807377 : Blo 535802 807377 := bstep (se 2 (by rfl) ⟨302766, by rfl⟩ : syracuseStep 807377 = 605533) B605533
theorem B807395 : Blo 535802 807395 := bstep (se 1 (by rfl) ⟨605546, by rfl⟩ : syracuseStep 807395 = 1211093) B1211093
theorem B1364465 : Blo 535802 1364465 := bstep (se 2 (by rfl) ⟨511674, by rfl⟩ : syracuseStep 1364465 = 1023349) B1023349
theorem B807425 : Blo 535802 807425 := bstep (se 2 (by rfl) ⟨302784, by rfl⟩ : syracuseStep 807425 = 605569) B605569
theorem B2904589 : Blo 535802 2904589 := bstep (se 3 (by rfl) ⟨544610, by rfl⟩ : syracuseStep 2904589 = 1089221) B1089221
theorem B807443 : Blo 535802 807443 := bstep (se 1 (by rfl) ⟨605582, by rfl⟩ : syracuseStep 807443 = 1211165) B1211165
theorem B807473 : Blo 535802 807473 := bstep (se 2 (by rfl) ⟨302802, by rfl⟩ : syracuseStep 807473 = 605605) B605605
theorem B807491 : Blo 535802 807491 := bstep (se 1 (by rfl) ⟨605618, by rfl⟩ : syracuseStep 807491 = 1211237) B1211237
theorem B905809 : Blo 535802 905809 := bstep (se 2 (by rfl) ⟨339678, by rfl⟩ : syracuseStep 905809 = 679357) B679357
theorem B807521 : Blo 535802 807521 := bstep (se 2 (by rfl) ⟨302820, by rfl⟩ : syracuseStep 807521 = 605641) B605641
theorem B1528429 : Blo 535802 1528429 := bstep (se 3 (by rfl) ⟨286580, by rfl⟩ : syracuseStep 1528429 = 573161) B573161
theorem B905843 : Blo 535802 905843 := bstep (se 1 (by rfl) ⟨679382, by rfl⟩ : syracuseStep 905843 = 1358765) B1358765
theorem B807539 : Blo 535802 807539 := bstep (se 1 (by rfl) ⟨605654, by rfl⟩ : syracuseStep 807539 = 1211309) B1211309
theorem B807569 : Blo 535802 807569 := bstep (se 2 (by rfl) ⟨302838, by rfl⟩ : syracuseStep 807569 = 605677) B605677
theorem B807587 : Blo 535802 807587 := bstep (se 1 (by rfl) ⟨605690, by rfl⟩ : syracuseStep 807587 = 1211381) B1211381
theorem B807617 : Blo 535802 807617 := bstep (se 2 (by rfl) ⟨302856, by rfl⟩ : syracuseStep 807617 = 605713) B605713
theorem B1725133 : Blo 535802 1725133 := bstep (se 3 (by rfl) ⟨323462, by rfl⟩ : syracuseStep 1725133 = 646925) B646925
theorem B807635 : Blo 535802 807635 := bstep (se 1 (by rfl) ⟨605726, by rfl⟩ : syracuseStep 807635 = 1211453) B1211453
theorem B807665 : Blo 535802 807665 := bstep (se 2 (by rfl) ⟨302874, by rfl⟩ : syracuseStep 807665 = 605749) B605749
theorem B905971 : Blo 535802 905971 := bstep (se 1 (by rfl) ⟨679478, by rfl⟩ : syracuseStep 905971 = 1358957) B1358957
theorem B807683 : Blo 535802 807683 := bstep (se 1 (by rfl) ⟨605762, by rfl⟩ : syracuseStep 807683 = 1211525) B1211525
theorem B807713 : Blo 535802 807713 := bstep (se 2 (by rfl) ⟨302892, by rfl⟩ : syracuseStep 807713 = 605785) B605785
theorem B807731 : Blo 535802 807731 := bstep (se 1 (by rfl) ⟨605798, by rfl⟩ : syracuseStep 807731 = 1211597) B1211597
theorem B807761 : Blo 535802 807761 := bstep (se 2 (by rfl) ⟨302910, by rfl⟩ : syracuseStep 807761 = 605821) B605821
theorem B807779 : Blo 535802 807779 := bstep (se 1 (by rfl) ⟨605834, by rfl⟩ : syracuseStep 807779 = 1211669) B1211669
theorem B906113 : Blo 535802 906113 := bstep (se 2 (by rfl) ⟨339792, by rfl⟩ : syracuseStep 906113 = 679585) B679585
theorem B807809 : Blo 535802 807809 := bstep (se 2 (by rfl) ⟨302928, by rfl⟩ : syracuseStep 807809 = 605857) B605857
theorem B807827 : Blo 535802 807827 := bstep (se 1 (by rfl) ⟨605870, by rfl⟩ : syracuseStep 807827 = 1211741) B1211741
theorem B807857 : Blo 535802 807857 := bstep (se 2 (by rfl) ⟨302946, by rfl⟩ : syracuseStep 807857 = 605893) B605893
theorem B807875 : Blo 535802 807875 := bstep (se 1 (by rfl) ⟨605906, by rfl⟩ : syracuseStep 807875 = 1211813) B1211813
theorem B807905 : Blo 535802 807905 := bstep (se 2 (by rfl) ⟨302964, by rfl⟩ : syracuseStep 807905 = 605929) B605929
theorem B807923 : Blo 535802 807923 := bstep (se 1 (by rfl) ⟨605942, by rfl⟩ : syracuseStep 807923 = 1211885) B1211885
theorem B906241 : Blo 535802 906241 := bstep (se 2 (by rfl) ⟨339840, by rfl⟩ : syracuseStep 906241 = 679681) B679681
theorem B807953 : Blo 535802 807953 := bstep (se 2 (by rfl) ⟨302982, by rfl⟩ : syracuseStep 807953 = 605965) B605965
theorem B906275 : Blo 535802 906275 := bstep (se 1 (by rfl) ⟨679706, by rfl⟩ : syracuseStep 906275 = 1359413) B1359413
theorem B807971 : Blo 535802 807971 := bstep (se 1 (by rfl) ⟨605978, by rfl⟩ : syracuseStep 807971 = 1211957) B1211957
theorem B808001 : Blo 535802 808001 := bstep (se 2 (by rfl) ⟨303000, by rfl⟩ : syracuseStep 808001 = 606001) B606001
theorem B808019 : Blo 535802 808019 := bstep (se 1 (by rfl) ⟨606014, by rfl⟩ : syracuseStep 808019 = 1212029) B1212029
theorem B808049 : Blo 535802 808049 := bstep (se 2 (by rfl) ⟨303018, by rfl⟩ : syracuseStep 808049 = 606037) B606037
theorem B808067 : Blo 535802 808067 := bstep (se 1 (by rfl) ⟨606050, by rfl⟩ : syracuseStep 808067 = 1212101) B1212101
theorem B808097 : Blo 535802 808097 := bstep (se 2 (by rfl) ⟨303036, by rfl⟩ : syracuseStep 808097 = 606073) B606073
theorem B906403 : Blo 535802 906403 := bstep (se 1 (by rfl) ⟨679802, by rfl⟩ : syracuseStep 906403 = 1359605) B1359605
theorem B873635 : Blo 535802 873635 := bstep (se 1 (by rfl) ⟨655226, by rfl⟩ : syracuseStep 873635 = 1310453) B1310453
theorem B808115 : Blo 535802 808115 := bstep (se 1 (by rfl) ⟨606086, by rfl⟩ : syracuseStep 808115 = 1212173) B1212173
theorem B808145 : Blo 535802 808145 := bstep (se 2 (by rfl) ⟨303054, by rfl⟩ : syracuseStep 808145 = 606109) B606109
theorem B808163 : Blo 535802 808163 := bstep (se 1 (by rfl) ⟨606122, by rfl⟩ : syracuseStep 808163 = 1212245) B1212245
theorem B808193 : Blo 535802 808193 := bstep (se 2 (by rfl) ⟨303072, by rfl⟩ : syracuseStep 808193 = 606145) B606145
theorem B808211 : Blo 535802 808211 := bstep (se 1 (by rfl) ⟨606158, by rfl⟩ : syracuseStep 808211 = 1212317) B1212317
theorem B906545 : Blo 535802 906545 := bstep (se 2 (by rfl) ⟨339954, by rfl⟩ : syracuseStep 906545 = 679909) B679909
theorem B808241 : Blo 535802 808241 := bstep (se 2 (by rfl) ⟨303090, by rfl⟩ : syracuseStep 808241 = 606181) B606181
theorem B808259 : Blo 535802 808259 := bstep (se 1 (by rfl) ⟨606194, by rfl⟩ : syracuseStep 808259 = 1212389) B1212389
theorem B808289 : Blo 535802 808289 := bstep (se 2 (by rfl) ⟨303108, by rfl⟩ : syracuseStep 808289 = 606217) B606217
theorem B808307 : Blo 535802 808307 := bstep (se 1 (by rfl) ⟨606230, by rfl⟩ : syracuseStep 808307 = 1212461) B1212461
theorem B808337 : Blo 535802 808337 := bstep (se 2 (by rfl) ⟨303126, by rfl⟩ : syracuseStep 808337 = 606253) B606253
theorem B808355 : Blo 535802 808355 := bstep (se 1 (by rfl) ⟨606266, by rfl⟩ : syracuseStep 808355 = 1212533) B1212533
theorem B906673 : Blo 535802 906673 := bstep (se 2 (by rfl) ⟨340002, by rfl⟩ : syracuseStep 906673 = 680005) B680005
theorem B808385 : Blo 535802 808385 := bstep (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) B606289
theorem B1365457 : Blo 535802 1365457 := bstep (se 2 (by rfl) ⟨512046, by rfl⟩ : syracuseStep 1365457 = 1024093) B1024093
theorem B906707 : Blo 535802 906707 := bstep (se 1 (by rfl) ⟨680030, by rfl⟩ : syracuseStep 906707 = 1360061) B1360061
theorem B808403 : Blo 535802 808403 := bstep (se 1 (by rfl) ⟨606302, by rfl⟩ : syracuseStep 808403 = 1212605) B1212605
theorem B808433 : Blo 535802 808433 := bstep (se 2 (by rfl) ⟨303162, by rfl⟩ : syracuseStep 808433 = 606325) B606325
theorem B808451 : Blo 535802 808451 := bstep (se 1 (by rfl) ⟨606338, by rfl⟩ : syracuseStep 808451 = 1212677) B1212677
theorem B808481 : Blo 535802 808481 := bstep (se 2 (by rfl) ⟨303180, by rfl⟩ : syracuseStep 808481 = 606361) B606361
theorem B808499 : Blo 535802 808499 := bstep (se 1 (by rfl) ⟨606374, by rfl⟩ : syracuseStep 808499 = 1212749) B1212749
theorem B808529 : Blo 535802 808529 := bstep (se 2 (by rfl) ⟨303198, by rfl⟩ : syracuseStep 808529 = 606397) B606397
theorem B906835 : Blo 535802 906835 := bstep (se 1 (by rfl) ⟨680126, by rfl⟩ : syracuseStep 906835 = 1360253) B1360253
theorem B2184803 : Blo 535802 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B808547 : Blo 535802 808547 := bstep (se 1 (by rfl) ⟨606410, by rfl⟩ : syracuseStep 808547 = 1212821) B1212821
theorem B4609649 : Blo 535802 4609649 := bstep (se 2 (by rfl) ⟨1728618, by rfl⟩ : syracuseStep 4609649 = 3457237) B3457237
theorem B808577 : Blo 535802 808577 := bstep (se 2 (by rfl) ⟨303216, by rfl⟩ : syracuseStep 808577 = 606433) B606433
theorem B808595 : Blo 535802 808595 := bstep (se 1 (by rfl) ⟨606446, by rfl⟩ : syracuseStep 808595 = 1212893) B1212893
theorem B808625 : Blo 535802 808625 := bstep (se 2 (by rfl) ⟨303234, by rfl⟩ : syracuseStep 808625 = 606469) B606469
theorem B808643 : Blo 535802 808643 := bstep (se 1 (by rfl) ⟨606482, by rfl⟩ : syracuseStep 808643 = 1212965) B1212965
theorem B906977 : Blo 535802 906977 := bstep (se 2 (by rfl) ⟨340116, by rfl⟩ : syracuseStep 906977 = 680233) B680233
theorem B808673 : Blo 535802 808673 := bstep (se 2 (by rfl) ⟨303252, by rfl⟩ : syracuseStep 808673 = 606505) B606505
theorem B1365731 : Blo 535802 1365731 := bstep (se 1 (by rfl) ⟨1024298, by rfl⟩ : syracuseStep 1365731 = 2048597) B2048597
theorem B972515 : Blo 535802 972515 := bstep (se 1 (by rfl) ⟨729386, by rfl⟩ : syracuseStep 972515 = 1458773) B1458773
theorem B808691 : Blo 535802 808691 := bstep (se 1 (by rfl) ⟨606518, by rfl⟩ : syracuseStep 808691 = 1213037) B1213037
theorem B1726211 : Blo 535802 1726211 := bstep (se 1 (by rfl) ⟨1294658, by rfl⟩ : syracuseStep 1726211 = 2589317) B2589317
theorem B808721 : Blo 535802 808721 := bstep (se 2 (by rfl) ⟨303270, by rfl⟩ : syracuseStep 808721 = 606541) B606541
theorem B808739 : Blo 535802 808739 := bstep (se 1 (by rfl) ⟨606554, by rfl⟩ : syracuseStep 808739 = 1213109) B1213109
theorem B808769 : Blo 535802 808769 := bstep (se 2 (by rfl) ⟨303288, by rfl⟩ : syracuseStep 808769 = 606577) B606577
theorem B808787 : Blo 535802 808787 := bstep (se 1 (by rfl) ⟨606590, by rfl⟩ : syracuseStep 808787 = 1213181) B1213181
theorem B907105 : Blo 535802 907105 := bstep (se 2 (by rfl) ⟨340164, by rfl⟩ : syracuseStep 907105 = 680329) B680329
theorem B808817 : Blo 535802 808817 := bstep (se 2 (by rfl) ⟨303306, by rfl⟩ : syracuseStep 808817 = 606613) B606613
theorem B907139 : Blo 535802 907139 := bstep (se 1 (by rfl) ⟨680354, by rfl⟩ : syracuseStep 907139 = 1360709) B1360709
theorem B808835 : Blo 535802 808835 := bstep (se 1 (by rfl) ⟨606626, by rfl⟩ : syracuseStep 808835 = 1213253) B1213253
theorem B808865 : Blo 535802 808865 := bstep (se 2 (by rfl) ⟨303324, by rfl⟩ : syracuseStep 808865 = 606649) B606649
theorem B1365923 : Blo 535802 1365923 := bstep (se 1 (by rfl) ⟨1024442, by rfl⟩ : syracuseStep 1365923 = 2048885) B2048885
theorem B808883 : Blo 535802 808883 := bstep (se 1 (by rfl) ⟨606662, by rfl⟩ : syracuseStep 808883 = 1213325) B1213325
theorem B808913 : Blo 535802 808913 := bstep (se 2 (by rfl) ⟨303342, by rfl⟩ : syracuseStep 808913 = 606685) B606685
theorem B808931 : Blo 535802 808931 := bstep (se 1 (by rfl) ⟨606698, by rfl⟩ : syracuseStep 808931 = 1213397) B1213397
theorem B808961 : Blo 535802 808961 := bstep (se 2 (by rfl) ⟨303360, by rfl⟩ : syracuseStep 808961 = 606721) B606721
theorem B907267 : Blo 535802 907267 := bstep (se 1 (by rfl) ⟨680450, by rfl⟩ : syracuseStep 907267 = 1360901) B1360901
theorem B808979 : Blo 535802 808979 := bstep (se 1 (by rfl) ⟨606734, by rfl⟩ : syracuseStep 808979 = 1213469) B1213469
theorem B3070001 : Blo 535802 3070001 := bstep (se 2 (by rfl) ⟨1151250, by rfl⟩ : syracuseStep 3070001 = 2302501) B2302501
theorem B809009 : Blo 535802 809009 := bstep (se 2 (by rfl) ⟨303378, by rfl⟩ : syracuseStep 809009 = 606757) B606757
theorem B809027 : Blo 535802 809027 := bstep (se 1 (by rfl) ⟨606770, by rfl⟩ : syracuseStep 809027 = 1213541) B1213541
theorem B809057 : Blo 535802 809057 := bstep (se 2 (by rfl) ⟨303396, by rfl⟩ : syracuseStep 809057 = 606793) B606793
theorem B809075 : Blo 535802 809075 := bstep (se 1 (by rfl) ⟨606806, by rfl⟩ : syracuseStep 809075 = 1213613) B1213613
theorem B907409 : Blo 535802 907409 := bstep (se 2 (by rfl) ⟨340278, by rfl⟩ : syracuseStep 907409 = 680557) B680557
theorem B809105 : Blo 535802 809105 := bstep (se 2 (by rfl) ⟨303414, by rfl⟩ : syracuseStep 809105 = 606829) B606829
theorem B809123 : Blo 535802 809123 := bstep (se 1 (by rfl) ⟨606842, by rfl⟩ : syracuseStep 809123 = 1213685) B1213685
theorem B809153 : Blo 535802 809153 := bstep (se 2 (by rfl) ⟨303432, by rfl⟩ : syracuseStep 809153 = 606865) B606865
theorem B809171 : Blo 535802 809171 := bstep (se 1 (by rfl) ⟨606878, by rfl⟩ : syracuseStep 809171 = 1213757) B1213757
theorem B809201 : Blo 535802 809201 := bstep (se 2 (by rfl) ⟨303450, by rfl⟩ : syracuseStep 809201 = 606901) B606901
theorem B809219 : Blo 535802 809219 := bstep (se 1 (by rfl) ⟨606914, by rfl⟩ : syracuseStep 809219 = 1213829) B1213829
theorem B907537 : Blo 535802 907537 := bstep (se 2 (by rfl) ⟨340326, by rfl⟩ : syracuseStep 907537 = 680653) B680653
theorem B809249 : Blo 535802 809249 := bstep (se 2 (by rfl) ⟨303468, by rfl⟩ : syracuseStep 809249 = 606937) B606937
theorem B1530161 : Blo 535802 1530161 := bstep (se 2 (by rfl) ⟨573810, by rfl⟩ : syracuseStep 1530161 = 1147621) B1147621
theorem B907571 : Blo 535802 907571 := bstep (se 1 (by rfl) ⟨680678, by rfl⟩ : syracuseStep 907571 = 1361357) B1361357
theorem B809267 : Blo 535802 809267 := bstep (se 1 (by rfl) ⟨606950, by rfl⟩ : syracuseStep 809267 = 1213901) B1213901
theorem B809297 : Blo 535802 809297 := bstep (se 2 (by rfl) ⟨303486, by rfl⟩ : syracuseStep 809297 = 606973) B606973
theorem B809315 : Blo 535802 809315 := bstep (se 1 (by rfl) ⟨606986, by rfl⟩ : syracuseStep 809315 = 1213973) B1213973
theorem B809345 : Blo 535802 809345 := bstep (se 2 (by rfl) ⟨303504, by rfl⟩ : syracuseStep 809345 = 607009) B607009
theorem B1726865 : Blo 535802 1726865 := bstep (se 2 (by rfl) ⟨647574, by rfl⟩ : syracuseStep 1726865 = 1295149) B1295149
theorem B809363 : Blo 535802 809363 := bstep (se 1 (by rfl) ⟨607022, by rfl⟩ : syracuseStep 809363 = 1214045) B1214045
theorem B809393 : Blo 535802 809393 := bstep (se 2 (by rfl) ⟨303522, by rfl⟩ : syracuseStep 809393 = 607045) B607045
theorem B907699 : Blo 535802 907699 := bstep (se 1 (by rfl) ⟨680774, by rfl⟩ : syracuseStep 907699 = 1361549) B1361549
theorem B809411 : Blo 535802 809411 := bstep (se 1 (by rfl) ⟨607058, by rfl⟩ : syracuseStep 809411 = 1214117) B1214117
theorem B809441 : Blo 535802 809441 := bstep (se 2 (by rfl) ⟨303540, by rfl⟩ : syracuseStep 809441 = 607081) B607081
theorem B1530353 : Blo 535802 1530353 := bstep (se 2 (by rfl) ⟨573882, by rfl⟩ : syracuseStep 1530353 = 1147765) B1147765
theorem B809459 : Blo 535802 809459 := bstep (se 1 (by rfl) ⟨607094, by rfl⟩ : syracuseStep 809459 = 1214189) B1214189
theorem B809489 : Blo 535802 809489 := bstep (se 2 (by rfl) ⟨303558, by rfl⟩ : syracuseStep 809489 = 607117) B607117
theorem B809507 : Blo 535802 809507 := bstep (se 1 (by rfl) ⟨607130, by rfl⟩ : syracuseStep 809507 = 1214261) B1214261
theorem B678451 : Blo 535802 678451 := bstep (se 1 (by rfl) ⟨508838, by rfl⟩ : syracuseStep 678451 = 1017677) B1017677
theorem B907841 : Blo 535802 907841 := bstep (se 2 (by rfl) ⟨340440, by rfl⟩ : syracuseStep 907841 = 680881) B680881
theorem B809537 : Blo 535802 809537 := bstep (se 2 (by rfl) ⟨303576, by rfl⟩ : syracuseStep 809537 = 607153) B607153
theorem B809555 : Blo 535802 809555 := bstep (se 1 (by rfl) ⟨607166, by rfl⟩ : syracuseStep 809555 = 1214333) B1214333
theorem B809585 : Blo 535802 809585 := bstep (se 2 (by rfl) ⟨303594, by rfl⟩ : syracuseStep 809585 = 607189) B607189
theorem B809603 : Blo 535802 809603 := bstep (se 1 (by rfl) ⟨607202, by rfl⟩ : syracuseStep 809603 = 1214405) B1214405
theorem B678547 : Blo 535802 678547 := bstep (se 1 (by rfl) ⟨508910, by rfl⟩ : syracuseStep 678547 = 1017821) B1017821
theorem B809633 : Blo 535802 809633 := bstep (se 2 (by rfl) ⟨303612, by rfl⟩ : syracuseStep 809633 = 607225) B607225
theorem B809651 : Blo 535802 809651 := bstep (se 1 (by rfl) ⟨607238, by rfl⟩ : syracuseStep 809651 = 1214477) B1214477
theorem B907969 : Blo 535802 907969 := bstep (se 2 (by rfl) ⟨340488, by rfl⟩ : syracuseStep 907969 = 680977) B680977
theorem B809681 : Blo 535802 809681 := bstep (se 2 (by rfl) ⟨303630, by rfl⟩ : syracuseStep 809681 = 607261) B607261
theorem B908003 : Blo 535802 908003 := bstep (se 1 (by rfl) ⟨681002, by rfl⟩ : syracuseStep 908003 = 1362005) B1362005
theorem B809699 : Blo 535802 809699 := bstep (se 1 (by rfl) ⟨607274, by rfl⟩ : syracuseStep 809699 = 1214549) B1214549
theorem B645907 : Blo 535802 645907 := bstep (se 1 (by rfl) ⟨484430, by rfl⟩ : syracuseStep 645907 = 968861) B968861
theorem B613171 : Blo 535802 613171 := bstep (se 1 (by rfl) ⟨459878, by rfl⟩ : syracuseStep 613171 = 919757) B919757
theorem B908131 : Blo 535802 908131 := bstep (se 1 (by rfl) ⟨681098, by rfl⟩ : syracuseStep 908131 = 1362197) B1362197
theorem B3267469 : Blo 535802 3267469 := bstep (se 3 (by rfl) ⟨612650, by rfl⟩ : syracuseStep 3267469 = 1225301) B1225301
theorem B646051 : Blo 535802 646051 := bstep (se 1 (by rfl) ⟨484538, by rfl⟩ : syracuseStep 646051 = 969077) B969077
theorem B908273 : Blo 535802 908273 := bstep (se 2 (by rfl) ⟨340602, by rfl⟩ : syracuseStep 908273 = 681205) B681205
theorem B908401 : Blo 535802 908401 := bstep (se 2 (by rfl) ⟨340650, by rfl⟩ : syracuseStep 908401 = 681301) B681301
theorem B679043 : Blo 535802 679043 := bstep (se 1 (by rfl) ⟨509282, by rfl⟩ : syracuseStep 679043 = 1018565) B1018565
theorem B908435 : Blo 535802 908435 := bstep (se 1 (by rfl) ⟨681326, by rfl⟩ : syracuseStep 908435 = 1362653) B1362653
theorem B908563 : Blo 535802 908563 := bstep (se 1 (by rfl) ⟨681422, by rfl⟩ : syracuseStep 908563 = 1362845) B1362845
theorem B843059 : Blo 535802 843059 := bstep (se 1 (by rfl) ⟨632294, by rfl⟩ : syracuseStep 843059 = 1264589) B1264589
theorem B9330061 : Blo 535802 9330061 := bstep (se 3 (by rfl) ⟨1749386, by rfl⟩ : syracuseStep 9330061 = 3498773) B3498773
theorem B908705 : Blo 535802 908705 := bstep (se 2 (by rfl) ⟨340764, by rfl⟩ : syracuseStep 908705 = 681529) B681529
theorem B1531345 : Blo 535802 1531345 := bstep (se 2 (by rfl) ⟨574254, by rfl⟩ : syracuseStep 1531345 = 1148509) B1148509
theorem B3071459 : Blo 535802 3071459 := bstep (se 1 (by rfl) ⟨2303594, by rfl⟩ : syracuseStep 3071459 = 4607189) B4607189
theorem B908833 : Blo 535802 908833 := bstep (se 2 (by rfl) ⟨340812, by rfl⟩ : syracuseStep 908833 = 681625) B681625
theorem B908867 : Blo 535802 908867 := bstep (se 1 (by rfl) ⟨681650, by rfl⟩ : syracuseStep 908867 = 1363301) B1363301
theorem B1990307 : Blo 535802 1990307 := bstep (se 1 (by rfl) ⟨1492730, by rfl⟩ : syracuseStep 1990307 = 2985461) B2985461
theorem B908995 : Blo 535802 908995 := bstep (se 1 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 908995 = 1363493) B1363493
theorem B1892045 : Blo 535802 1892045 := bstep (se 3 (by rfl) ⟨354758, by rfl⟩ : syracuseStep 1892045 = 709517) B709517
theorem B1728209 : Blo 535802 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B1531619 : Blo 535802 1531619 := bstep (se 1 (by rfl) ⟨1148714, by rfl⟩ : syracuseStep 1531619 = 2297429) B2297429
theorem B2186993 : Blo 535802 2186993 := bstep (se 2 (by rfl) ⟨820122, by rfl⟩ : syracuseStep 2186993 = 1640245) B1640245
theorem B679747 : Blo 535802 679747 := bstep (se 1 (by rfl) ⟨509810, by rfl⟩ : syracuseStep 679747 = 1019621) B1019621
theorem B909137 : Blo 535802 909137 := bstep (se 2 (by rfl) ⟨340926, by rfl⟩ : syracuseStep 909137 = 681853) B681853
theorem B679843 : Blo 535802 679843 := bstep (se 1 (by rfl) ⟨509882, by rfl⟩ : syracuseStep 679843 = 1019765) B1019765
theorem B1531811 : Blo 535802 1531811 := bstep (se 1 (by rfl) ⟨1148858, by rfl⟩ : syracuseStep 1531811 = 2297717) B2297717
theorem B647075 : Blo 535802 647075 := bstep (se 1 (by rfl) ⟨485306, by rfl⟩ : syracuseStep 647075 = 970613) B970613
theorem B909265 : Blo 535802 909265 := bstep (se 2 (by rfl) ⟨340974, by rfl⟩ : syracuseStep 909265 = 681949) B681949
theorem B909299 : Blo 535802 909299 := bstep (se 1 (by rfl) ⟨681974, by rfl⟩ : syracuseStep 909299 = 1363949) B1363949
theorem B2613347 : Blo 535802 2613347 := bstep (se 1 (by rfl) ⟨1960010, by rfl⟩ : syracuseStep 2613347 = 3920021) B3920021
theorem B909427 : Blo 535802 909427 := bstep (se 1 (by rfl) ⟨682070, by rfl⟩ : syracuseStep 909427 = 1364141) B1364141
theorem B909569 : Blo 535802 909569 := bstep (se 2 (by rfl) ⟨341088, by rfl⟩ : syracuseStep 909569 = 682177) B682177
theorem B5169521 : Blo 535802 5169521 := bstep (se 2 (by rfl) ⟨1938570, by rfl⟩ : syracuseStep 5169521 = 3877141) B3877141
theorem B909697 : Blo 535802 909697 := bstep (se 2 (by rfl) ⟨341136, by rfl⟩ : syracuseStep 909697 = 682273) B682273
theorem B680339 : Blo 535802 680339 := bstep (se 1 (by rfl) ⟨510254, by rfl⟩ : syracuseStep 680339 = 1020509) B1020509
theorem B909731 : Blo 535802 909731 := bstep (se 1 (by rfl) ⟨682298, by rfl⟩ : syracuseStep 909731 = 1364597) B1364597
theorem B909859 : Blo 535802 909859 := bstep (se 1 (by rfl) ⟨682394, by rfl⟩ : syracuseStep 909859 = 1364789) B1364789
theorem B7070321 : Blo 535802 7070321 := bstep (se 2 (by rfl) ⟨2651370, by rfl⟩ : syracuseStep 7070321 = 5302741) B5302741
theorem B2187917 : Blo 535802 2187917 := bstep (se 3 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 2187917 = 820469) B820469
theorem B778897 : Blo 535802 778897 := bstep (se 2 (by rfl) ⟨292086, by rfl⟩ : syracuseStep 778897 = 584173) B584173
theorem B910001 : Blo 535802 910001 := bstep (se 2 (by rfl) ⟨341250, by rfl⟩ : syracuseStep 910001 = 682501) B682501
theorem B1532621 : Blo 535802 1532621 := bstep (se 3 (by rfl) ⟨287366, by rfl⟩ : syracuseStep 1532621 = 574733) B574733
theorem B910129 : Blo 535802 910129 := bstep (se 2 (by rfl) ⟨341298, by rfl⟩ : syracuseStep 910129 = 682597) B682597
theorem B910163 : Blo 535802 910163 := bstep (se 1 (by rfl) ⟨682622, by rfl⟩ : syracuseStep 910163 = 1365245) B1365245
theorem B1532803 : Blo 535802 1532803 := bstep (se 1 (by rfl) ⟨1149602, by rfl⟩ : syracuseStep 1532803 = 2299205) B2299205
theorem B4088717 : Blo 535802 4088717 := bstep (se 3 (by rfl) ⟨766634, by rfl⟩ : syracuseStep 4088717 = 1533269) B1533269
theorem B910291 : Blo 535802 910291 := bstep (se 1 (by rfl) ⟨682718, by rfl⟩ : syracuseStep 910291 = 1365437) B1365437
theorem B681043 : Blo 535802 681043 := bstep (se 1 (by rfl) ⟨510782, by rfl⟩ : syracuseStep 681043 = 1021565) B1021565
theorem B910433 : Blo 535802 910433 := bstep (se 2 (by rfl) ⟨341412, by rfl⟩ : syracuseStep 910433 = 682825) B682825
theorem B2712689 : Blo 535802 2712689 := bstep (se 2 (by rfl) ⟨1017258, by rfl⟩ : syracuseStep 2712689 = 2034517) B2034517
theorem B681139 : Blo 535802 681139 := bstep (se 1 (by rfl) ⟨510854, by rfl⟩ : syracuseStep 681139 = 1021709) B1021709
theorem B910561 : Blo 535802 910561 := bstep (se 2 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 910561 = 682921) B682921
theorem B910595 : Blo 535802 910595 := bstep (se 1 (by rfl) ⟨682946, by rfl⟩ : syracuseStep 910595 = 1365893) B1365893
theorem B1205585 : Blo 535802 1205585 := bstep (se 2 (by rfl) ⟨452094, by rfl⟩ : syracuseStep 1205585 = 904189) B904189
theorem B1205603 : Blo 535802 1205603 := bstep (se 1 (by rfl) ⟨904202, by rfl⟩ : syracuseStep 1205603 = 1808405) B1808405
theorem B1533293 : Blo 535802 1533293 := bstep (se 3 (by rfl) ⟨287492, by rfl⟩ : syracuseStep 1533293 = 574985) B574985
theorem B910723 : Blo 535802 910723 := bstep (se 1 (by rfl) ⟨683042, by rfl⟩ : syracuseStep 910723 = 1366085) B1366085
theorem B910865 : Blo 535802 910865 := bstep (se 2 (by rfl) ⟨341574, by rfl⟩ : syracuseStep 910865 = 683149) B683149
theorem B5170787 : Blo 535802 5170787 := bstep (se 1 (by rfl) ⟨3878090, by rfl⟩ : syracuseStep 5170787 = 7756181) B7756181
theorem B1205873 : Blo 535802 1205873 := bstep (se 2 (by rfl) ⟨452202, by rfl⟩ : syracuseStep 1205873 = 904405) B904405
theorem B1205891 : Blo 535802 1205891 := bstep (se 1 (by rfl) ⟨904418, by rfl⟩ : syracuseStep 1205891 = 1808837) B1808837
theorem B681635 : Blo 535802 681635 := bstep (se 1 (by rfl) ⟨511226, by rfl⟩ : syracuseStep 681635 = 1022453) B1022453
theorem B3106531 : Blo 535802 3106531 := bstep (se 1 (by rfl) ⟨2329898, by rfl⟩ : syracuseStep 3106531 = 4659797) B4659797
theorem B1206161 : Blo 535802 1206161 := bstep (se 2 (by rfl) ⟨452310, by rfl⟩ : syracuseStep 1206161 = 904621) B904621
theorem B1206179 : Blo 535802 1206179 := bstep (se 1 (by rfl) ⟨904634, by rfl⟩ : syracuseStep 1206179 = 1809269) B1809269
theorem B2582513 : Blo 535802 2582513 := bstep (se 2 (by rfl) ⟨968442, by rfl⟩ : syracuseStep 2582513 = 1936885) B1936885
theorem B16509041 : Blo 535802 16509041 := bstep (se 2 (by rfl) ⟨6190890, by rfl⟩ : syracuseStep 16509041 = 12381781) B12381781
theorem B14772365 : Blo 535802 14772365 := bstep (se 3 (by rfl) ⟨2769818, by rfl⟩ : syracuseStep 14772365 = 5539637) B5539637
theorem B1206449 : Blo 535802 1206449 := bstep (se 2 (by rfl) ⟨452418, by rfl⟩ : syracuseStep 1206449 = 904837) B904837
theorem B1206467 : Blo 535802 1206467 := bstep (se 1 (by rfl) ⟨904850, by rfl⟩ : syracuseStep 1206467 = 1809701) B1809701
theorem B6187205 : Blo 535802 6187205 := bstep (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) B1160101
theorem B15952099 : Blo 535802 15952099 := bstep (se 1 (by rfl) ⟨11964074, by rfl⟩ : syracuseStep 15952099 = 23928149) B23928149
theorem B682339 : Blo 535802 682339 := bstep (se 1 (by rfl) ⟨511754, by rfl⟩ : syracuseStep 682339 = 1023509) B1023509
theorem B682435 : Blo 535802 682435 := bstep (se 1 (by rfl) ⟨511826, by rfl⟩ : syracuseStep 682435 = 1023653) B1023653
theorem B1206737 : Blo 535802 1206737 := bstep (se 2 (by rfl) ⟨452526, by rfl⟩ : syracuseStep 1206737 = 905053) B905053
theorem B1206755 : Blo 535802 1206755 := bstep (se 1 (by rfl) ⟨905066, by rfl⟩ : syracuseStep 1206755 = 1810133) B1810133
theorem B3434993 : Blo 535802 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B6220273 : Blo 535802 6220273 := bstep (se 2 (by rfl) ⟨2332602, by rfl⟩ : syracuseStep 6220273 = 4665205) B4665205
theorem B1534477 : Blo 535802 1534477 := bstep (se 3 (by rfl) ⟨287714, by rfl⟩ : syracuseStep 1534477 = 575429) B575429
theorem B2714147 : Blo 535802 2714147 := bstep (se 1 (by rfl) ⟨2035610, by rfl⟩ : syracuseStep 2714147 = 4071221) B4071221
theorem B1207025 : Blo 535802 1207025 := bstep (se 2 (by rfl) ⟨452634, by rfl⟩ : syracuseStep 1207025 = 905269) B905269
theorem B1207043 : Blo 535802 1207043 := bstep (se 1 (by rfl) ⟨905282, by rfl⟩ : syracuseStep 1207043 = 1810565) B1810565
theorem B682931 : Blo 535802 682931 := bstep (se 1 (by rfl) ⟨512198, by rfl⟩ : syracuseStep 682931 = 1024397) B1024397
theorem B1207313 : Blo 535802 1207313 := bstep (se 2 (by rfl) ⟨452742, by rfl⟩ : syracuseStep 1207313 = 905485) B905485
theorem B1207331 : Blo 535802 1207331 := bstep (se 1 (by rfl) ⟨905498, by rfl⟩ : syracuseStep 1207331 = 1810997) B1810997
theorem B1961165 : Blo 535802 1961165 := bstep (se 3 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 1961165 = 735437) B735437
theorem B1207601 : Blo 535802 1207601 := bstep (se 2 (by rfl) ⟨452850, by rfl⟩ : syracuseStep 1207601 = 905701) B905701
theorem B1207619 : Blo 535802 1207619 := bstep (se 1 (by rfl) ⟨905714, by rfl⟩ : syracuseStep 1207619 = 1811429) B1811429
theorem B2714957 : Blo 535802 2714957 := bstep (se 3 (by rfl) ⟨509054, by rfl⟩ : syracuseStep 2714957 = 1018109) B1018109
theorem B5533069 : Blo 535802 5533069 := bstep (se 3 (by rfl) ⟨1037450, by rfl⟩ : syracuseStep 5533069 = 2074901) B2074901
theorem B1535537 : Blo 535802 1535537 := bstep (se 2 (by rfl) ⟨575826, by rfl⟩ : syracuseStep 1535537 = 1151653) B1151653
theorem B1207889 : Blo 535802 1207889 := bstep (se 2 (by rfl) ⟨452958, by rfl⟩ : syracuseStep 1207889 = 905917) B905917
theorem B1207907 : Blo 535802 1207907 := bstep (se 1 (by rfl) ⟨905930, by rfl⟩ : syracuseStep 1207907 = 1811861) B1811861
theorem B2584163 : Blo 535802 2584163 := bstep (se 1 (by rfl) ⟨1938122, by rfl⟩ : syracuseStep 2584163 = 3876245) B3876245
theorem B3272333 : Blo 535802 3272333 := bstep (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) B1227125
theorem B2289379 : Blo 535802 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B4091633 : Blo 535802 4091633 := bstep (se 2 (by rfl) ⟨1534362, by rfl⟩ : syracuseStep 4091633 = 3068725) B3068725
theorem B1208177 : Blo 535802 1208177 := bstep (se 2 (by rfl) ⟨453066, by rfl⟩ : syracuseStep 1208177 = 906133) B906133
theorem B1208195 : Blo 535802 1208195 := bstep (se 1 (by rfl) ⟨906146, by rfl⟩ : syracuseStep 1208195 = 1812293) B1812293
theorem B1208465 : Blo 535802 1208465 := bstep (se 2 (by rfl) ⟨453174, by rfl⟩ : syracuseStep 1208465 = 906349) B906349
theorem B1208483 : Blo 535802 1208483 := bstep (se 1 (by rfl) ⟨906362, by rfl⟩ : syracuseStep 1208483 = 1812725) B1812725
theorem B1536209 : Blo 535802 1536209 := bstep (se 2 (by rfl) ⟨576078, by rfl⟩ : syracuseStep 1536209 = 1152157) B1152157
theorem B2584973 : Blo 535802 2584973 := bstep (se 3 (by rfl) ⟨484682, by rfl⟩ : syracuseStep 2584973 = 969365) B969365
theorem B1208753 : Blo 535802 1208753 := bstep (se 2 (by rfl) ⟨453282, by rfl⟩ : syracuseStep 1208753 = 906565) B906565
theorem B1208771 : Blo 535802 1208771 := bstep (se 1 (by rfl) ⟨906578, by rfl⟩ : syracuseStep 1208771 = 1813157) B1813157
theorem B1209041 : Blo 535802 1209041 := bstep (se 2 (by rfl) ⟨453390, by rfl⟩ : syracuseStep 1209041 = 906781) B906781
theorem B1209059 : Blo 535802 1209059 := bstep (se 1 (by rfl) ⟨906794, by rfl⟩ : syracuseStep 1209059 = 1813589) B1813589
theorem B815987 : Blo 535802 815987 := bstep (se 1 (by rfl) ⟨611990, by rfl⟩ : syracuseStep 815987 = 1223981) B1223981
theorem B2290609 : Blo 535802 2290609 := bstep (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) B1717957
theorem B2913221 : Blo 535802 2913221 := bstep (se 4 (by rfl) ⟨273114, by rfl⟩ : syracuseStep 2913221 = 546229) B546229
theorem B1536995 : Blo 535802 1536995 := bstep (se 1 (by rfl) ⟨1152746, by rfl⟩ : syracuseStep 1536995 = 2305493) B2305493
theorem B1209329 : Blo 535802 1209329 := bstep (se 2 (by rfl) ⟨453498, by rfl⟩ : syracuseStep 1209329 = 906997) B906997
theorem B1209347 : Blo 535802 1209347 := bstep (se 1 (by rfl) ⟨907010, by rfl⟩ : syracuseStep 1209347 = 1814021) B1814021
theorem B1209617 : Blo 535802 1209617 := bstep (se 2 (by rfl) ⟨453606, by rfl⟩ : syracuseStep 1209617 = 907213) B907213
theorem B1209635 : Blo 535802 1209635 := bstep (se 1 (by rfl) ⟨907226, by rfl⟩ : syracuseStep 1209635 = 1814453) B1814453
theorem B9172277 : Blo 535802 9172277 := bstep (se 5 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 9172277 = 859901) B859901
theorem B2618801 : Blo 535802 2618801 := bstep (se 2 (by rfl) ⟨982050, by rfl⟩ : syracuseStep 2618801 = 1964101) B1964101
theorem B1209905 : Blo 535802 1209905 := bstep (se 2 (by rfl) ⟨453714, by rfl⟩ : syracuseStep 1209905 = 907429) B907429
theorem B1209923 : Blo 535802 1209923 := bstep (se 1 (by rfl) ⟨907442, by rfl⟩ : syracuseStep 1209923 = 1814885) B1814885
theorem B4126277 : Blo 535802 4126277 := bstep (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) B773677
theorem B1144451 : Blo 535802 1144451 := bstep (se 1 (by rfl) ⟨858338, by rfl⟩ : syracuseStep 1144451 = 1716677) B1716677
theorem B1210193 : Blo 535802 1210193 := bstep (se 2 (by rfl) ⟨453822, by rfl⟩ : syracuseStep 1210193 = 907645) B907645
theorem B1210211 : Blo 535802 1210211 := bstep (se 1 (by rfl) ⟨907658, by rfl⟩ : syracuseStep 1210211 = 1815317) B1815317
theorem B817057 : Blo 535802 817057 := bstep (se 2 (by rfl) ⟨306396, by rfl⟩ : syracuseStep 817057 = 612793) B612793
theorem B6912013 : Blo 535802 6912013 := bstep (se 3 (by rfl) ⟨1296002, by rfl⟩ : syracuseStep 6912013 = 2592005) B2592005
theorem B1210481 : Blo 535802 1210481 := bstep (se 2 (by rfl) ⟨453930, by rfl⟩ : syracuseStep 1210481 = 907861) B907861
theorem B1144963 : Blo 535802 1144963 := bstep (se 1 (by rfl) ⟨858722, by rfl⟩ : syracuseStep 1144963 = 1717445) B1717445
theorem B1210499 : Blo 535802 1210499 := bstep (se 1 (by rfl) ⟨907874, by rfl⟩ : syracuseStep 1210499 = 1815749) B1815749
theorem B2717873 : Blo 535802 2717873 := bstep (se 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) B2038405
theorem B1210769 : Blo 535802 1210769 := bstep (se 2 (by rfl) ⟨454038, by rfl⟩ : syracuseStep 1210769 = 908077) B908077
theorem B2619811 : Blo 535802 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B1210787 : Blo 535802 1210787 := bstep (se 1 (by rfl) ⟨908090, by rfl⟩ : syracuseStep 1210787 = 1816181) B1816181
theorem B1374769 : Blo 535802 1374769 := bstep (se 2 (by rfl) ⟨515538, by rfl⟩ : syracuseStep 1374769 = 1031077) B1031077
theorem B1931953 : Blo 535802 1931953 := bstep (se 2 (by rfl) ⟨724482, by rfl⟩ : syracuseStep 1931953 = 1448965) B1448965
theorem B1211057 : Blo 535802 1211057 := bstep (se 2 (by rfl) ⟨454146, by rfl⟩ : syracuseStep 1211057 = 908293) B908293
theorem B1211075 : Blo 535802 1211075 := bstep (se 1 (by rfl) ⟨908306, by rfl⟩ : syracuseStep 1211075 = 1816613) B1816613
theorem B5798627 : Blo 535802 5798627 := bstep (se 1 (by rfl) ⟨4348970, by rfl⟩ : syracuseStep 5798627 = 8697941) B8697941
theorem B1145681 : Blo 535802 1145681 := bstep (se 2 (by rfl) ⟨429630, by rfl⟩ : syracuseStep 1145681 = 859261) B859261
theorem B4586381 : Blo 535802 4586381 := bstep (se 3 (by rfl) ⟨859946, by rfl⟩ : syracuseStep 4586381 = 1719893) B1719893
theorem B1211345 : Blo 535802 1211345 := bstep (se 2 (by rfl) ⟨454254, by rfl⟩ : syracuseStep 1211345 = 908509) B908509
theorem B1211363 : Blo 535802 1211363 := bstep (se 1 (by rfl) ⟨908522, by rfl⟩ : syracuseStep 1211363 = 1817045) B1817045
theorem B1834001 : Blo 535802 1834001 := bstep (se 2 (by rfl) ⟨687750, by rfl⟩ : syracuseStep 1834001 = 1375501) B1375501
theorem B916561 : Blo 535802 916561 := bstep (se 2 (by rfl) ⟨343710, by rfl⟩ : syracuseStep 916561 = 687421) B687421
theorem B3767501 : Blo 535802 3767501 := bstep (se 3 (by rfl) ⟨706406, by rfl⟩ : syracuseStep 3767501 = 1412813) B1412813
theorem B1211633 : Blo 535802 1211633 := bstep (se 2 (by rfl) ⟨454362, by rfl⟩ : syracuseStep 1211633 = 908725) B908725
theorem B1211651 : Blo 535802 1211651 := bstep (se 1 (by rfl) ⟨908738, by rfl⟩ : syracuseStep 1211651 = 1817477) B1817477
theorem B6913349 : Blo 535802 6913349 := bstep (se 4 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 6913349 = 1296253) B1296253
theorem B3440069 : Blo 535802 3440069 := bstep (se 4 (by rfl) ⟨322506, by rfl⟩ : syracuseStep 3440069 = 645013) B645013
theorem B1211921 : Blo 535802 1211921 := bstep (se 2 (by rfl) ⟨454470, by rfl⟩ : syracuseStep 1211921 = 908941) B908941
theorem B1211939 : Blo 535802 1211939 := bstep (se 1 (by rfl) ⟨908954, by rfl⟩ : syracuseStep 1211939 = 1817909) B1817909
theorem B1146467 : Blo 535802 1146467 := bstep (se 1 (by rfl) ⟨859850, by rfl⟩ : syracuseStep 1146467 = 1719701) B1719701
theorem B2719331 : Blo 535802 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B917219 : Blo 535802 917219 := bstep (se 1 (by rfl) ⟨687914, by rfl⟩ : syracuseStep 917219 = 1375829) B1375829
theorem B1212209 : Blo 535802 1212209 := bstep (se 2 (by rfl) ⟨454578, by rfl⟩ : syracuseStep 1212209 = 909157) B909157
theorem B1212227 : Blo 535802 1212227 := bstep (se 1 (by rfl) ⟨909170, by rfl⟩ : syracuseStep 1212227 = 1818341) B1818341
theorem B819155 : Blo 535802 819155 := bstep (se 1 (by rfl) ⟨614366, by rfl⟩ : syracuseStep 819155 = 1228733) B1228733
theorem B2326573 : Blo 535802 2326573 := bstep (se 3 (by rfl) ⟨436232, by rfl⟩ : syracuseStep 2326573 = 872465) B872465
theorem B26214475 : Blo 535802 26214475 := bstep (se 1 (by rfl) ⟨19660856, by rfl⟩ : syracuseStep 26214475 = 39321713) B39321713
theorem B2752643 : Blo 535802 2752643 := bstep (se 1 (by rfl) ⟨2064482, by rfl⟩ : syracuseStep 2752643 = 4128965) B4128965
theorem B1147031 : Blo 535802 1147031 := bstep (se 1 (by rfl) ⟨860273, by rfl⟩ : syracuseStep 1147031 = 1720547) B1720547
theorem B1212569 : Blo 535802 1212569 := bstep (se 2 (by rfl) ⟨454713, by rfl⟩ : syracuseStep 1212569 = 909427) B909427
theorem B1212659 : Blo 535802 1212659 := bstep (se 1 (by rfl) ⟨909494, by rfl⟩ : syracuseStep 1212659 = 1818989) B1818989
theorem B1212695 : Blo 535802 1212695 := bstep (se 1 (by rfl) ⟨909521, by rfl⟩ : syracuseStep 1212695 = 1819043) B1819043
theorem B786763 : Blo 535802 786763 := bstep (se 1 (by rfl) ⟨590072, by rfl⟩ : syracuseStep 786763 = 1180145) B1180145
theorem B6127973 : Blo 535802 6127973 := bstep (se 4 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 6127973 = 1148995) B1148995
theorem B1212875 : Blo 535802 1212875 := bstep (se 1 (by rfl) ⟨909656, by rfl⟩ : syracuseStep 1212875 = 1819313) B1819313
theorem B1212929 : Blo 535802 1212929 := bstep (se 2 (by rfl) ⟨454848, by rfl⟩ : syracuseStep 1212929 = 909697) B909697
theorem B1213145 : Blo 535802 1213145 := bstep (se 2 (by rfl) ⟨454929, by rfl⟩ : syracuseStep 1213145 = 909859) B909859
theorem B1213235 : Blo 535802 1213235 := bstep (se 1 (by rfl) ⟨909926, by rfl⟩ : syracuseStep 1213235 = 1819853) B1819853
theorem B1213271 : Blo 535802 1213271 := bstep (se 1 (by rfl) ⟨909953, by rfl⟩ : syracuseStep 1213271 = 1819907) B1819907
theorem B820055 : Blo 535802 820055 := bstep (se 1 (by rfl) ⟨615041, by rfl⟩ : syracuseStep 820055 = 1230083) B1230083
theorem B1213451 : Blo 535802 1213451 := bstep (se 1 (by rfl) ⟨910088, by rfl⟩ : syracuseStep 1213451 = 1820177) B1820177
theorem B1213505 : Blo 535802 1213505 := bstep (se 2 (by rfl) ⟨455064, by rfl⟩ : syracuseStep 1213505 = 910129) B910129
theorem B1148107 : Blo 535802 1148107 := bstep (se 1 (by rfl) ⟨861080, by rfl⟩ : syracuseStep 1148107 = 1722161) B1722161
theorem B1213721 : Blo 535802 1213721 := bstep (se 2 (by rfl) ⟨455145, by rfl⟩ : syracuseStep 1213721 = 910291) B910291
theorem B1213811 : Blo 535802 1213811 := bstep (se 1 (by rfl) ⟨910358, by rfl⟩ : syracuseStep 1213811 = 1820717) B1820717
theorem B1213847 : Blo 535802 1213847 := bstep (se 1 (by rfl) ⟨910385, by rfl⟩ : syracuseStep 1213847 = 1820771) B1820771
theorem B787979 : Blo 535802 787979 := bstep (se 1 (by rfl) ⟨590984, by rfl⟩ : syracuseStep 787979 = 1181969) B1181969
theorem B4916753 : Blo 535802 4916753 := bstep (se 2 (by rfl) ⟨1843782, by rfl⟩ : syracuseStep 4916753 = 3687565) B3687565
theorem B3868235 : Blo 535802 3868235 := bstep (se 1 (by rfl) ⟨2901176, by rfl⟩ : syracuseStep 3868235 = 5802353) B5802353
theorem B9176651 : Blo 535802 9176651 := bstep (se 1 (by rfl) ⟨6882488, by rfl⟩ : syracuseStep 9176651 = 13764977) B13764977
theorem B1214027 : Blo 535802 1214027 := bstep (se 1 (by rfl) ⟨910520, by rfl⟩ : syracuseStep 1214027 = 1821041) B1821041
theorem B1214081 : Blo 535802 1214081 := bstep (se 2 (by rfl) ⟨455280, by rfl⟩ : syracuseStep 1214081 = 910561) B910561
theorem B1017623 : Blo 535802 1017623 := bstep (se 1 (by rfl) ⟨763217, by rfl⟩ : syracuseStep 1017623 = 1526435) B1526435
theorem B1214297 : Blo 535802 1214297 := bstep (se 2 (by rfl) ⟨455361, by rfl⟩ : syracuseStep 1214297 = 910723) B910723
theorem B1148825 : Blo 535802 1148825 := bstep (se 2 (by rfl) ⟨430809, by rfl⟩ : syracuseStep 1148825 = 861619) B861619
theorem B1214387 : Blo 535802 1214387 := bstep (se 1 (by rfl) ⟨910790, by rfl⟩ : syracuseStep 1214387 = 1821581) B1821581
theorem B1214423 : Blo 535802 1214423 := bstep (se 1 (by rfl) ⟨910817, by rfl⟩ : syracuseStep 1214423 = 1821635) B1821635
theorem B3442733 : Blo 535802 3442733 := bstep (se 3 (by rfl) ⟨645512, by rfl⟩ : syracuseStep 3442733 = 1291025) B1291025
theorem B15763531 : Blo 535802 15763531 := bstep (se 1 (by rfl) ⟨11822648, by rfl⟩ : syracuseStep 15763531 = 23645297) B23645297
theorem B2721923 : Blo 535802 2721923 := bstep (se 1 (by rfl) ⟨2041442, by rfl⟩ : syracuseStep 2721923 = 4082885) B4082885
theorem B2459927 : Blo 535802 2459927 := bstep (se 1 (by rfl) ⟨1844945, by rfl⟩ : syracuseStep 2459927 = 3689891) B3689891
theorem B1018163 : Blo 535802 1018163 := bstep (se 1 (by rfl) ⟨763622, by rfl⟩ : syracuseStep 1018163 = 1527245) B1527245
theorem B1149337 : Blo 535802 1149337 := bstep (se 2 (by rfl) ⟨431001, by rfl⟩ : syracuseStep 1149337 = 862003) B862003
theorem B1935875 : Blo 535802 1935875 := bstep (se 1 (by rfl) ⟨1451906, by rfl⟩ : syracuseStep 1935875 = 2903813) B2903813
theorem B1149491 : Blo 535802 1149491 := bstep (se 1 (by rfl) ⟨862118, by rfl⟩ : syracuseStep 1149491 = 1724237) B1724237
theorem B2296471 : Blo 535802 2296471 := bstep (se 1 (by rfl) ⟨1722353, by rfl⟩ : syracuseStep 2296471 = 3444707) B3444707
theorem B1018649 : Blo 535802 1018649 := bstep (se 2 (by rfl) ⟨381993, by rfl⟩ : syracuseStep 1018649 = 763987) B763987
theorem B21269465 : Blo 535802 21269465 := bstep (se 2 (by rfl) ⟨7976049, by rfl⟩ : syracuseStep 21269465 = 15952099) B15952099
theorem B1117363 : Blo 535802 1117363 := bstep (se 1 (by rfl) ⟨838022, by rfl⟩ : syracuseStep 1117363 = 1676045) B1676045
theorem B2034989 : Blo 535802 2034989 := bstep (se 3 (by rfl) ⟨381560, by rfl⟩ : syracuseStep 2034989 = 763121) B763121
theorem B8293697 : Blo 535802 8293697 := bstep (se 2 (by rfl) ⟨3110136, by rfl⟩ : syracuseStep 8293697 = 6220273) B6220273
theorem B1150465 : Blo 535802 1150465 := bstep (se 2 (by rfl) ⟨431424, by rfl⟩ : syracuseStep 1150465 = 862849) B862849
theorem B8261189 : Blo 535802 8261189 := bstep (se 4 (by rfl) ⟨774486, by rfl⟩ : syracuseStep 8261189 = 1548973) B1548973
theorem B1150807 : Blo 535802 1150807 := bstep (se 1 (by rfl) ⟨863105, by rfl⟩ : syracuseStep 1150807 = 1726211) B1726211
theorem B2035763 : Blo 535802 2035763 := bstep (se 1 (by rfl) ⟨1526822, by rfl⟩ : syracuseStep 2035763 = 3053645) B3053645
theorem B8720459 : Blo 535802 8720459 := bstep (se 1 (by rfl) ⟨6540344, by rfl⟩ : syracuseStep 8720459 = 13080689) B13080689
theorem B1020107 : Blo 535802 1020107 := bstep (se 1 (by rfl) ⟨765080, by rfl⟩ : syracuseStep 1020107 = 1530161) B1530161
theorem B921817 : Blo 535802 921817 := bstep (se 2 (by rfl) ⟨345681, by rfl⟩ : syracuseStep 921817 = 691363) B691363
theorem B1151243 : Blo 535802 1151243 := bstep (se 1 (by rfl) ⟨863432, by rfl⟩ : syracuseStep 1151243 = 1726865) B1726865
theorem B2756909 : Blo 535802 2756909 := bstep (se 3 (by rfl) ⟨516920, by rfl⟩ : syracuseStep 2756909 = 1033841) B1033841
theorem B1577267 : Blo 535802 1577267 := bstep (se 1 (by rfl) ⟨1182950, by rfl⟩ : syracuseStep 1577267 = 2365901) B2365901
theorem B1020289 : Blo 535802 1020289 := bstep (se 2 (by rfl) ⟨382608, by rfl⟩ : syracuseStep 1020289 = 765217) B765217
theorem B7377425 : Blo 535802 7377425 := bstep (se 2 (by rfl) ⟨2766534, by rfl⟩ : syracuseStep 7377425 = 5533069) B5533069
theorem B9966341 : Blo 535802 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B1020737 : Blo 535802 1020737 := bstep (se 2 (by rfl) ⟨382776, by rfl⟩ : syracuseStep 1020737 = 765553) B765553
theorem B3052505 : Blo 535802 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B922699 : Blo 535802 922699 := bstep (se 1 (by rfl) ⟨692024, by rfl⟩ : syracuseStep 922699 = 1384049) B1384049
theorem B1152139 : Blo 535802 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B1021079 : Blo 535802 1021079 := bstep (se 1 (by rfl) ⟨765809, by rfl⟩ : syracuseStep 1021079 = 1531619) B1531619
theorem B1742231 : Blo 535802 1742231 := bstep (se 1 (by rfl) ⟨1306673, by rfl⟩ : syracuseStep 1742231 = 2613347) B2613347
theorem B2299357 : Blo 535802 2299357 := bstep (se 3 (by rfl) ⟨431129, by rfl⟩ : syracuseStep 2299357 = 862259) B862259
theorem B2037251 : Blo 535802 2037251 := bstep (se 1 (by rfl) ⟨1527938, by rfl⟩ : syracuseStep 2037251 = 3055877) B3055877
theorem B3446347 : Blo 535802 3446347 := bstep (se 1 (by rfl) ⟨2584760, by rfl⟩ : syracuseStep 3446347 = 5169521) B5169521
theorem B4888325 : Blo 535802 4888325 := bstep (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) B916561
theorem B2725649 : Blo 535802 2725649 := bstep (se 2 (by rfl) ⟨1022118, by rfl⟩ : syracuseStep 2725649 = 2044237) B2044237
theorem B1021747 : Blo 535802 1021747 := bstep (se 1 (by rfl) ⟨766310, by rfl⟩ : syracuseStep 1021747 = 1532621) B1532621
theorem B1841075 : Blo 535802 1841075 := bstep (se 1 (by rfl) ⟨1380806, by rfl⟩ : syracuseStep 1841075 = 2761613) B2761613
theorem B2725811 : Blo 535802 2725811 := bstep (se 1 (by rfl) ⟨2044358, by rfl⟩ : syracuseStep 2725811 = 4088717) B4088717
theorem B2037707 : Blo 535802 2037707 := bstep (se 1 (by rfl) ⟨1528280, by rfl⟩ : syracuseStep 2037707 = 3056561) B3056561
theorem B3872785 : Blo 535802 3872785 := bstep (se 2 (by rfl) ⟨1452294, by rfl⟩ : syracuseStep 3872785 = 2904589) B2904589
theorem B1808459 : Blo 535802 1808459 := bstep (se 1 (by rfl) ⟨1356344, by rfl⟩ : syracuseStep 1808459 = 2712689) B2712689
theorem B2037905 : Blo 535802 2037905 := bstep (se 2 (by rfl) ⟨764214, by rfl⟩ : syracuseStep 2037905 = 1528429) B1528429
theorem B1022195 : Blo 535802 1022195 := bstep (se 1 (by rfl) ⟨766646, by rfl⟩ : syracuseStep 1022195 = 1533293) B1533293
theorem B2300177 : Blo 535802 2300177 := bstep (se 2 (by rfl) ⟨862566, by rfl⟩ : syracuseStep 2300177 = 1725133) B1725133
theorem B1022233 : Blo 535802 1022233 := bstep (se 2 (by rfl) ⟨383337, by rfl⟩ : syracuseStep 1022233 = 766675) B766675
theorem B1808729 : Blo 535802 1808729 := bstep (se 2 (by rfl) ⟨678273, by rfl⟩ : syracuseStep 1808729 = 1356547) B1356547
theorem B4069763 : Blo 535802 4069763 := bstep (se 1 (by rfl) ⟨3052322, by rfl⟩ : syracuseStep 4069763 = 6104645) B6104645
theorem B3447191 : Blo 535802 3447191 := bstep (se 1 (by rfl) ⟨2585393, by rfl⟩ : syracuseStep 3447191 = 5170787) B5170787
theorem B1448513 : Blo 535802 1448513 := bstep (se 2 (by rfl) ⟨543192, by rfl⟩ : syracuseStep 1448513 = 1086385) B1086385
theorem B3054145 : Blo 535802 3054145 := bstep (se 2 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 3054145 = 2290609) B2290609
theorem B7740035 : Blo 535802 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B1022681 : Blo 535802 1022681 := bstep (se 2 (by rfl) ⟨383505, by rfl⟩ : syracuseStep 1022681 = 767011) B767011
theorem B2038679 : Blo 535802 2038679 := bstep (se 1 (by rfl) ⟨1529009, by rfl⟩ : syracuseStep 2038679 = 3058019) B3058019
theorem B2300845 : Blo 535802 2300845 := bstep (se 3 (by rfl) ⟨431408, by rfl⟩ : syracuseStep 2300845 = 862817) B862817
theorem B4201433 : Blo 535802 4201433 := bstep (se 2 (by rfl) ⟨1575537, by rfl⟩ : syracuseStep 4201433 = 3151075) B3151075
theorem B1809431 : Blo 535802 1809431 := bstep (se 1 (by rfl) ⟨1357073, by rfl⟩ : syracuseStep 1809431 = 2714147) B2714147
theorem B2038877 : Blo 535802 2038877 := bstep (se 3 (by rfl) ⟨382289, by rfl⟩ : syracuseStep 2038877 = 764579) B764579
theorem B3873997 : Blo 535802 3873997 := bstep (se 3 (by rfl) ⟨726374, by rfl⟩ : syracuseStep 3873997 = 1452749) B1452749
theorem B859351 : Blo 535802 859351 := bstep (se 1 (by rfl) ⟨644513, by rfl⟩ : syracuseStep 859351 = 1289027) B1289027
theorem B1023425 : Blo 535802 1023425 := bstep (se 2 (by rfl) ⟨383784, by rfl⟩ : syracuseStep 1023425 = 767569) B767569
theorem B2301443 : Blo 535802 2301443 := bstep (se 1 (by rfl) ⟨1726082, by rfl⟩ : syracuseStep 2301443 = 3452165) B3452165
theorem B1809971 : Blo 535802 1809971 := bstep (se 1 (by rfl) ⟨1357478, by rfl⟩ : syracuseStep 1809971 = 2714957) B2714957
theorem B859799 : Blo 535802 859799 := bstep (se 1 (by rfl) ⟨644849, by rfl⟩ : syracuseStep 859799 = 1289699) B1289699
theorem B1023691 : Blo 535802 1023691 := bstep (se 1 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 1023691 = 1535537) B1535537
theorem B1810241 : Blo 535802 1810241 := bstep (se 2 (by rfl) ⟨678840, by rfl⟩ : syracuseStep 1810241 = 1357681) B1357681
theorem B859979 : Blo 535802 859979 := bstep (se 1 (by rfl) ⟨644984, by rfl⟩ : syracuseStep 859979 = 1289969) B1289969
theorem B2727755 : Blo 535802 2727755 := bstep (se 1 (by rfl) ⟨2045816, by rfl⟩ : syracuseStep 2727755 = 4091633) B4091633
theorem B1089409 : Blo 535802 1089409 := bstep (se 2 (by rfl) ⟨408528, by rfl⟩ : syracuseStep 1089409 = 817057) B817057
theorem B9216017 : Blo 535802 9216017 := bstep (se 2 (by rfl) ⟨3456006, by rfl⟩ : syracuseStep 9216017 = 6912013) B6912013
theorem B4595777 : Blo 535802 4595777 := bstep (se 2 (by rfl) ⟨1723416, by rfl⟩ : syracuseStep 4595777 = 3446833) B3446833
theorem B1024139 : Blo 535802 1024139 := bstep (se 1 (by rfl) ⟨768104, by rfl⟩ : syracuseStep 1024139 = 1536209) B1536209
theorem B860363 : Blo 535802 860363 := bstep (se 1 (by rfl) ⟨645272, by rfl⟩ : syracuseStep 860363 = 1290545) B1290545
theorem B1024321 : Blo 535802 1024321 := bstep (se 2 (by rfl) ⟨384120, by rfl⟩ : syracuseStep 1024321 = 768241) B768241
theorem B860491 : Blo 535802 860491 := bstep (se 1 (by rfl) ⟨645368, by rfl⟩ : syracuseStep 860491 = 1290737) B1290737
theorem B1810781 : Blo 535802 1810781 := bstep (se 3 (by rfl) ⟨339521, by rfl⟩ : syracuseStep 1810781 = 679043) B679043
theorem B5808485 : Blo 535802 5808485 := bstep (se 4 (by rfl) ⟨544545, by rfl⟩ : syracuseStep 5808485 = 1089091) B1089091
theorem B1942147 : Blo 535802 1942147 := bstep (se 1 (by rfl) ⟨1456610, by rfl⟩ : syracuseStep 1942147 = 2913221) B2913221
theorem B1024663 : Blo 535802 1024663 := bstep (se 1 (by rfl) ⟨768497, by rfl⟩ : syracuseStep 1024663 = 1536995) B1536995
theorem B1745867 : Blo 535802 1745867 := bstep (se 1 (by rfl) ⟨1309400, by rfl⟩ : syracuseStep 1745867 = 2618801) B2618801
theorem B2040835 : Blo 535802 2040835 := bstep (se 1 (by rfl) ⟨1530626, by rfl⟩ : syracuseStep 2040835 = 3061253) B3061253
theorem B861209 : Blo 535802 861209 := bstep (se 2 (by rfl) ⟨322953, by rfl⟩ : syracuseStep 861209 = 645907) B645907
theorem B762967 : Blo 535802 762967 := bstep (se 1 (by rfl) ⟨572225, by rfl⟩ : syracuseStep 762967 = 1144451) B1144451
theorem B7349399 : Blo 535802 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B861401 : Blo 535802 861401 := bstep (se 2 (by rfl) ⟨323025, by rfl⟩ : syracuseStep 861401 = 646051) B646051
theorem B2041139 : Blo 535802 2041139 := bstep (se 1 (by rfl) ⟨1530854, by rfl⟩ : syracuseStep 2041139 = 3061709) B3061709
theorem B1811915 : Blo 535802 1811915 := bstep (se 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) B2717873
theorem B5219801 : Blo 535802 5219801 := bstep (se 2 (by rfl) ⟨1957425, by rfl⟩ : syracuseStep 5219801 = 3914851) B3914851
theorem B2729537 : Blo 535802 2729537 := bstep (se 2 (by rfl) ⟨1023576, by rfl⟩ : syracuseStep 2729537 = 2047153) B2047153
theorem B6891101 : Blo 535802 6891101 := bstep (se 3 (by rfl) ⟨1292081, by rfl⟩ : syracuseStep 6891101 = 2584163) B2584163
theorem B4073165 : Blo 535802 4073165 := bstep (se 3 (by rfl) ⟨763718, by rfl⟩ : syracuseStep 4073165 = 1527437) B1527437
theorem B8726221 : Blo 535802 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B1812185 : Blo 535802 1812185 := bstep (se 2 (by rfl) ⟨679569, by rfl⟩ : syracuseStep 1812185 = 1359139) B1359139
theorem B763673 : Blo 535802 763673 := bstep (se 2 (by rfl) ⟨286377, by rfl⟩ : syracuseStep 763673 = 572755) B572755
theorem B763787 : Blo 535802 763787 := bstep (se 1 (by rfl) ⟨572840, by rfl⟩ : syracuseStep 763787 = 1145681) B1145681
theorem B3057587 : Blo 535802 3057587 := bstep (se 1 (by rfl) ⟨2293190, by rfl⟩ : syracuseStep 3057587 = 4586381) B4586381
theorem B2041793 : Blo 535802 2041793 := bstep (se 2 (by rfl) ⟨765672, by rfl⟩ : syracuseStep 2041793 = 1531345) B1531345
theorem B1222667 : Blo 535802 1222667 := bstep (se 1 (by rfl) ⟨917000, by rfl⟩ : syracuseStep 1222667 = 1834001) B1834001
theorem B4073651 : Blo 535802 4073651 := bstep (se 1 (by rfl) ⟨3055238, by rfl⟩ : syracuseStep 4073651 = 6110477) B6110477
theorem B2074841 : Blo 535802 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B764311 : Blo 535802 764311 := bstep (se 1 (by rfl) ⟨573233, by rfl⟩ : syracuseStep 764311 = 1146467) B1146467
theorem B1812887 : Blo 535802 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B4598167 : Blo 535802 4598167 := bstep (se 1 (by rfl) ⟨3448625, by rfl⟩ : syracuseStep 4598167 = 6897251) B6897251
theorem B16198157 : Blo 535802 16198157 := bstep (se 3 (by rfl) ⟨3037154, by rfl⟩ : syracuseStep 16198157 = 6074309) B6074309
theorem B14920433 : Blo 535802 14920433 := bstep (se 2 (by rfl) ⟨5595162, by rfl⟩ : syracuseStep 14920433 = 11190325) B11190325
theorem B2075395 : Blo 535802 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B5253893 : Blo 535802 5253893 := bstep (se 4 (by rfl) ⟨492552, by rfl⟩ : syracuseStep 5253893 = 985105) B985105
theorem B1813427 : Blo 535802 1813427 := bstep (se 1 (by rfl) ⟨1360070, by rfl⟩ : syracuseStep 1813427 = 2720141) B2720141
theorem B1092595 : Blo 535802 1092595 := bstep (se 1 (by rfl) ⟨819446, by rfl⟩ : syracuseStep 1092595 = 1638893) B1638893
theorem B1289305 : Blo 535802 1289305 := bstep (se 2 (by rfl) ⟨483489, by rfl⟩ : syracuseStep 1289305 = 966979) B966979
theorem B2043053 : Blo 535802 2043053 := bstep (se 3 (by rfl) ⟨383072, by rfl⟩ : syracuseStep 2043053 = 766145) B766145
theorem B1813697 : Blo 535802 1813697 := bstep (se 2 (by rfl) ⟨680136, by rfl⟩ : syracuseStep 1813697 = 1360273) B1360273
theorem B765131 : Blo 535802 765131 := bstep (se 1 (by rfl) ⟨573848, by rfl⟩ : syracuseStep 765131 = 1147697) B1147697
theorem B2043083 : Blo 535802 2043083 := bstep (se 1 (by rfl) ⟨1532312, by rfl⟩ : syracuseStep 2043083 = 3064625) B3064625
theorem B535819 : Blo 535802 535819 := bstep (se 1 (by rfl) ⟨401864, by rfl⟩ : syracuseStep 535819 = 803729) B803729
theorem B535831 : Blo 535802 535831 := bstep (se 1 (by rfl) ⟨401873, by rfl⟩ : syracuseStep 535831 = 803747) B803747
theorem B535851 : Blo 535802 535851 := bstep (se 1 (by rfl) ⟨401888, by rfl⟩ : syracuseStep 535851 = 803777) B803777
theorem B535863 : Blo 535802 535863 := bstep (se 1 (by rfl) ⟨401897, by rfl⟩ : syracuseStep 535863 = 803795) B803795
theorem B4369729 : Blo 535802 4369729 := bstep (se 2 (by rfl) ⟨1638648, by rfl⟩ : syracuseStep 4369729 = 3277297) B3277297
theorem B535883 : Blo 535802 535883 := bstep (se 1 (by rfl) ⟨401912, by rfl⟩ : syracuseStep 535883 = 803825) B803825
theorem B535895 : Blo 535802 535895 := bstep (se 1 (by rfl) ⟨401921, by rfl⟩ : syracuseStep 535895 = 803843) B803843
theorem B3059045 : Blo 535802 3059045 := bstep (se 4 (by rfl) ⟨286785, by rfl⟩ : syracuseStep 3059045 = 573571) B573571
theorem B535915 : Blo 535802 535915 := bstep (se 1 (by rfl) ⟨401936, by rfl⟩ : syracuseStep 535915 = 803873) B803873
theorem B535927 : Blo 535802 535927 := bstep (se 1 (by rfl) ⟨401945, by rfl⟩ : syracuseStep 535927 = 803891) B803891
theorem B535947 : Blo 535802 535947 := bstep (se 1 (by rfl) ⟨401960, by rfl⟩ : syracuseStep 535947 = 803921) B803921
theorem B535959 : Blo 535802 535959 := bstep (se 1 (by rfl) ⟨401969, by rfl⟩ : syracuseStep 535959 = 803939) B803939
theorem B535979 : Blo 535802 535979 := bstep (se 1 (by rfl) ⟨401984, by rfl⟩ : syracuseStep 535979 = 803969) B803969
theorem B535991 : Blo 535802 535991 := bstep (se 1 (by rfl) ⟨401993, by rfl⟩ : syracuseStep 535991 = 803987) B803987
theorem B536011 : Blo 535802 536011 := bstep (se 1 (by rfl) ⟨402008, by rfl⟩ : syracuseStep 536011 = 804017) B804017
theorem B536023 : Blo 535802 536023 := bstep (se 1 (by rfl) ⟨402017, by rfl⟩ : syracuseStep 536023 = 804035) B804035
theorem B2731481 : Blo 535802 2731481 := bstep (se 2 (by rfl) ⟨1024305, by rfl⟩ : syracuseStep 2731481 = 2048611) B2048611
theorem B536043 : Blo 535802 536043 := bstep (se 1 (by rfl) ⟨402032, by rfl⟩ : syracuseStep 536043 = 804065) B804065
theorem B536055 : Blo 535802 536055 := bstep (se 1 (by rfl) ⟨402041, by rfl⟩ : syracuseStep 536055 = 804083) B804083
theorem B536075 : Blo 535802 536075 := bstep (se 1 (by rfl) ⟨402056, by rfl⟩ : syracuseStep 536075 = 804113) B804113
theorem B536087 : Blo 535802 536087 := bstep (se 1 (by rfl) ⟨402065, by rfl⟩ : syracuseStep 536087 = 804131) B804131
theorem B536107 : Blo 535802 536107 := bstep (se 1 (by rfl) ⟨402080, by rfl⟩ : syracuseStep 536107 = 804161) B804161
theorem B536119 : Blo 535802 536119 := bstep (se 1 (by rfl) ⟨402089, by rfl⟩ : syracuseStep 536119 = 804179) B804179
theorem B1060417 : Blo 535802 1060417 := bstep (se 2 (by rfl) ⟨397656, by rfl⟩ : syracuseStep 1060417 = 795313) B795313
theorem B536139 : Blo 535802 536139 := bstep (se 1 (by rfl) ⟨402104, by rfl⟩ : syracuseStep 536139 = 804209) B804209
theorem B536151 : Blo 535802 536151 := bstep (se 1 (by rfl) ⟨402113, by rfl⟩ : syracuseStep 536151 = 804227) B804227
theorem B4075109 : Blo 535802 4075109 := bstep (se 4 (by rfl) ⟨382041, by rfl⟩ : syracuseStep 4075109 = 764083) B764083
theorem B536171 : Blo 535802 536171 := bstep (se 1 (by rfl) ⟨402128, by rfl⟩ : syracuseStep 536171 = 804257) B804257
theorem B536183 : Blo 535802 536183 := bstep (se 1 (by rfl) ⟨402137, by rfl⟩ : syracuseStep 536183 = 804275) B804275
theorem B536203 : Blo 535802 536203 := bstep (se 1 (by rfl) ⟨402152, by rfl⟩ : syracuseStep 536203 = 804305) B804305
theorem B536215 : Blo 535802 536215 := bstep (se 1 (by rfl) ⟨402161, by rfl⟩ : syracuseStep 536215 = 804323) B804323
theorem B536235 : Blo 535802 536235 := bstep (se 1 (by rfl) ⟨402176, by rfl⟩ : syracuseStep 536235 = 804353) B804353
theorem B536247 : Blo 535802 536247 := bstep (se 1 (by rfl) ⟨402185, by rfl⟩ : syracuseStep 536247 = 804371) B804371
theorem B536267 : Blo 535802 536267 := bstep (se 1 (by rfl) ⟨402200, by rfl⟩ : syracuseStep 536267 = 804401) B804401
theorem B536279 : Blo 535802 536279 := bstep (se 1 (by rfl) ⟨402209, by rfl⟩ : syracuseStep 536279 = 804419) B804419
theorem B1814237 : Blo 535802 1814237 := bstep (se 3 (by rfl) ⟨340169, by rfl⟩ : syracuseStep 1814237 = 680339) B680339
theorem B536299 : Blo 535802 536299 := bstep (se 1 (by rfl) ⟨402224, by rfl⟩ : syracuseStep 536299 = 804449) B804449
theorem B536311 : Blo 535802 536311 := bstep (se 1 (by rfl) ⟨402233, by rfl⟩ : syracuseStep 536311 = 804467) B804467
theorem B536331 : Blo 535802 536331 := bstep (se 1 (by rfl) ⟨402248, by rfl⟩ : syracuseStep 536331 = 804497) B804497
theorem B536343 : Blo 535802 536343 := bstep (se 1 (by rfl) ⟨402257, by rfl⟩ : syracuseStep 536343 = 804515) B804515
theorem B536363 : Blo 535802 536363 := bstep (se 1 (by rfl) ⟨402272, by rfl⟩ : syracuseStep 536363 = 804545) B804545
theorem B536375 : Blo 535802 536375 := bstep (se 1 (by rfl) ⟨402281, by rfl⟩ : syracuseStep 536375 = 804563) B804563
theorem B536395 : Blo 535802 536395 := bstep (se 1 (by rfl) ⟨402296, by rfl⟩ : syracuseStep 536395 = 804593) B804593
theorem B536407 : Blo 535802 536407 := bstep (se 1 (by rfl) ⟨402305, by rfl⟩ : syracuseStep 536407 = 804611) B804611
theorem B2043737 : Blo 535802 2043737 := bstep (se 2 (by rfl) ⟨766401, by rfl⟩ : syracuseStep 2043737 = 1532803) B1532803
theorem B536427 : Blo 535802 536427 := bstep (se 1 (by rfl) ⟨402320, by rfl⟩ : syracuseStep 536427 = 804641) B804641
theorem B536439 : Blo 535802 536439 := bstep (se 1 (by rfl) ⟨402329, by rfl⟩ : syracuseStep 536439 = 804659) B804659
theorem B536459 : Blo 535802 536459 := bstep (se 1 (by rfl) ⟨402344, by rfl⟩ : syracuseStep 536459 = 804689) B804689
theorem B536471 : Blo 535802 536471 := bstep (se 1 (by rfl) ⟨402353, by rfl⟩ : syracuseStep 536471 = 804707) B804707
theorem B536491 : Blo 535802 536491 := bstep (se 1 (by rfl) ⟨402368, by rfl⟩ : syracuseStep 536491 = 804737) B804737
theorem B536503 : Blo 535802 536503 := bstep (se 1 (by rfl) ⟨402377, by rfl⟩ : syracuseStep 536503 = 804755) B804755
theorem B536523 : Blo 535802 536523 := bstep (se 1 (by rfl) ⟨402392, by rfl⟩ : syracuseStep 536523 = 804785) B804785
theorem B536535 : Blo 535802 536535 := bstep (se 1 (by rfl) ⟨402401, by rfl⟩ : syracuseStep 536535 = 804803) B804803
theorem B536555 : Blo 535802 536555 := bstep (se 1 (by rfl) ⟨402416, by rfl⟩ : syracuseStep 536555 = 804833) B804833
theorem B536567 : Blo 535802 536567 := bstep (se 1 (by rfl) ⟨402425, by rfl⟩ : syracuseStep 536567 = 804851) B804851
theorem B536587 : Blo 535802 536587 := bstep (se 1 (by rfl) ⟨402440, by rfl⟩ : syracuseStep 536587 = 804881) B804881
theorem B536599 : Blo 535802 536599 := bstep (se 1 (by rfl) ⟨402449, by rfl⟩ : syracuseStep 536599 = 804899) B804899
theorem B536619 : Blo 535802 536619 := bstep (se 1 (by rfl) ⟨402464, by rfl⟩ : syracuseStep 536619 = 804929) B804929
theorem B536631 : Blo 535802 536631 := bstep (se 1 (by rfl) ⟨402473, by rfl⟩ : syracuseStep 536631 = 804947) B804947
theorem B536651 : Blo 535802 536651 := bstep (se 1 (by rfl) ⟨402488, by rfl⟩ : syracuseStep 536651 = 804977) B804977
theorem B4075595 : Blo 535802 4075595 := bstep (se 1 (by rfl) ⟨3056696, by rfl⟩ : syracuseStep 4075595 = 6113393) B6113393
theorem B536663 : Blo 535802 536663 := bstep (se 1 (by rfl) ⟨402497, by rfl⟩ : syracuseStep 536663 = 804995) B804995
theorem B1224791 : Blo 535802 1224791 := bstep (se 1 (by rfl) ⟨918593, by rfl⟩ : syracuseStep 1224791 = 1837187) B1837187
theorem B536683 : Blo 535802 536683 := bstep (se 1 (by rfl) ⟨402512, by rfl⟩ : syracuseStep 536683 = 805025) B805025
theorem B536695 : Blo 535802 536695 := bstep (se 1 (by rfl) ⟨402521, by rfl⟩ : syracuseStep 536695 = 805043) B805043
theorem B536715 : Blo 535802 536715 := bstep (se 1 (by rfl) ⟨402536, by rfl⟩ : syracuseStep 536715 = 805073) B805073
theorem B536727 : Blo 535802 536727 := bstep (se 1 (by rfl) ⟨402545, by rfl⟩ : syracuseStep 536727 = 805091) B805091
theorem B2044055 : Blo 535802 2044055 := bstep (se 1 (by rfl) ⟨1533041, by rfl⟩ : syracuseStep 2044055 = 3066083) B3066083
theorem B864407 : Blo 535802 864407 := bstep (se 1 (by rfl) ⟨648305, by rfl⟩ : syracuseStep 864407 = 1296611) B1296611
theorem B536747 : Blo 535802 536747 := bstep (se 1 (by rfl) ⟨402560, by rfl⟩ : syracuseStep 536747 = 805121) B805121
theorem B536759 : Blo 535802 536759 := bstep (se 1 (by rfl) ⟨402569, by rfl⟩ : syracuseStep 536759 = 805139) B805139
theorem B1814731 : Blo 535802 1814731 := bstep (se 1 (by rfl) ⟨1361048, by rfl⟩ : syracuseStep 1814731 = 2722097) B2722097
theorem B536779 : Blo 535802 536779 := bstep (se 1 (by rfl) ⟨402584, by rfl⟩ : syracuseStep 536779 = 805169) B805169
theorem B536791 : Blo 535802 536791 := bstep (se 1 (by rfl) ⟨402593, by rfl⟩ : syracuseStep 536791 = 805187) B805187
theorem B536811 : Blo 535802 536811 := bstep (se 1 (by rfl) ⟨402608, by rfl⟩ : syracuseStep 536811 = 805217) B805217
theorem B536823 : Blo 535802 536823 := bstep (se 1 (by rfl) ⟨402617, by rfl⟩ : syracuseStep 536823 = 805235) B805235
theorem B536843 : Blo 535802 536843 := bstep (se 1 (by rfl) ⟨402632, by rfl⟩ : syracuseStep 536843 = 805265) B805265
theorem B4370705 : Blo 535802 4370705 := bstep (se 2 (by rfl) ⟨1639014, by rfl⟩ : syracuseStep 4370705 = 3278029) B3278029
theorem B536855 : Blo 535802 536855 := bstep (se 1 (by rfl) ⟨402641, by rfl⟩ : syracuseStep 536855 = 805283) B805283
theorem B536875 : Blo 535802 536875 := bstep (se 1 (by rfl) ⟨402656, by rfl⟩ : syracuseStep 536875 = 805313) B805313
theorem B536887 : Blo 535802 536887 := bstep (se 1 (by rfl) ⟨402665, by rfl⟩ : syracuseStep 536887 = 805331) B805331
theorem B536907 : Blo 535802 536907 := bstep (se 1 (by rfl) ⟨402680, by rfl⟩ : syracuseStep 536907 = 805361) B805361
theorem B536919 : Blo 535802 536919 := bstep (se 1 (by rfl) ⟨402689, by rfl⟩ : syracuseStep 536919 = 805379) B805379
theorem B536939 : Blo 535802 536939 := bstep (se 1 (by rfl) ⟨402704, by rfl⟩ : syracuseStep 536939 = 805409) B805409
theorem B9318773 : Blo 535802 9318773 := bstep (se 5 (by rfl) ⟨436817, by rfl⟩ : syracuseStep 9318773 = 873635) B873635
theorem B536951 : Blo 535802 536951 := bstep (se 1 (by rfl) ⟨402713, by rfl⟩ : syracuseStep 536951 = 805427) B805427
theorem B536971 : Blo 535802 536971 := bstep (se 1 (by rfl) ⟨402728, by rfl⟩ : syracuseStep 536971 = 805457) B805457
theorem B536983 : Blo 535802 536983 := bstep (se 1 (by rfl) ⟨402737, by rfl⟩ : syracuseStep 536983 = 805475) B805475
theorem B537003 : Blo 535802 537003 := bstep (se 1 (by rfl) ⟨402752, by rfl⟩ : syracuseStep 537003 = 805505) B805505
theorem B537015 : Blo 535802 537015 := bstep (se 1 (by rfl) ⟨402761, by rfl⟩ : syracuseStep 537015 = 805523) B805523
theorem B537035 : Blo 535802 537035 := bstep (se 1 (by rfl) ⟨402776, by rfl⟩ : syracuseStep 537035 = 805553) B805553
theorem B537047 : Blo 535802 537047 := bstep (se 1 (by rfl) ⟨402785, by rfl⟩ : syracuseStep 537047 = 805571) B805571
theorem B537067 : Blo 535802 537067 := bstep (se 1 (by rfl) ⟨402800, by rfl⟩ : syracuseStep 537067 = 805601) B805601
theorem B537079 : Blo 535802 537079 := bstep (se 1 (by rfl) ⟨402809, by rfl⟩ : syracuseStep 537079 = 805619) B805619
theorem B537099 : Blo 535802 537099 := bstep (se 1 (by rfl) ⟨402824, by rfl⟩ : syracuseStep 537099 = 805649) B805649
theorem B537111 : Blo 535802 537111 := bstep (se 1 (by rfl) ⟨402833, by rfl⟩ : syracuseStep 537111 = 805667) B805667
theorem B537131 : Blo 535802 537131 := bstep (se 1 (by rfl) ⟨402848, by rfl⟩ : syracuseStep 537131 = 805697) B805697
theorem B537143 : Blo 535802 537143 := bstep (se 1 (by rfl) ⟨402857, by rfl⟩ : syracuseStep 537143 = 805715) B805715
theorem B537163 : Blo 535802 537163 := bstep (se 1 (by rfl) ⟨402872, by rfl⟩ : syracuseStep 537163 = 805745) B805745
theorem B537175 : Blo 535802 537175 := bstep (se 1 (by rfl) ⟨402881, by rfl⟩ : syracuseStep 537175 = 805763) B805763
theorem B1094233 : Blo 535802 1094233 := bstep (se 2 (by rfl) ⟨410337, by rfl⟩ : syracuseStep 1094233 = 820675) B820675
theorem B537195 : Blo 535802 537195 := bstep (se 1 (by rfl) ⟨402896, by rfl⟩ : syracuseStep 537195 = 805793) B805793
theorem B537207 : Blo 535802 537207 := bstep (se 1 (by rfl) ⟨402905, by rfl⟩ : syracuseStep 537207 = 805811) B805811
theorem B537227 : Blo 535802 537227 := bstep (se 1 (by rfl) ⟨402920, by rfl⟩ : syracuseStep 537227 = 805841) B805841
theorem B537239 : Blo 535802 537239 := bstep (se 1 (by rfl) ⟨402929, by rfl⟩ : syracuseStep 537239 = 805859) B805859
theorem B537259 : Blo 535802 537259 := bstep (se 1 (by rfl) ⟨402944, by rfl⟩ : syracuseStep 537259 = 805889) B805889
theorem B537271 : Blo 535802 537271 := bstep (se 1 (by rfl) ⟨402953, by rfl⟩ : syracuseStep 537271 = 805907) B805907
theorem B537291 : Blo 535802 537291 := bstep (se 1 (by rfl) ⟨402968, by rfl⟩ : syracuseStep 537291 = 805937) B805937
theorem B537303 : Blo 535802 537303 := bstep (se 1 (by rfl) ⟨402977, by rfl⟩ : syracuseStep 537303 = 805955) B805955
theorem B537323 : Blo 535802 537323 := bstep (se 1 (by rfl) ⟨402992, by rfl⟩ : syracuseStep 537323 = 805985) B805985
theorem B537335 : Blo 535802 537335 := bstep (se 1 (by rfl) ⟨403001, by rfl⟩ : syracuseStep 537335 = 806003) B806003
theorem B537355 : Blo 535802 537355 := bstep (se 1 (by rfl) ⟨403016, by rfl⟩ : syracuseStep 537355 = 806033) B806033
theorem B537367 : Blo 535802 537367 := bstep (se 1 (by rfl) ⟨403025, by rfl⟩ : syracuseStep 537367 = 806051) B806051
theorem B602923 : Blo 535802 602923 := bstep (se 1 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 602923 = 904385) B904385
theorem B537387 : Blo 535802 537387 := bstep (se 1 (by rfl) ⟨403040, by rfl⟩ : syracuseStep 537387 = 806081) B806081
theorem B2044723 : Blo 535802 2044723 := bstep (se 1 (by rfl) ⟨1533542, by rfl⟩ : syracuseStep 2044723 = 3067085) B3067085
theorem B537399 : Blo 535802 537399 := bstep (se 1 (by rfl) ⟨403049, by rfl⟩ : syracuseStep 537399 = 806099) B806099
theorem B537419 : Blo 535802 537419 := bstep (se 1 (by rfl) ⟨403064, by rfl⟩ : syracuseStep 537419 = 806129) B806129
theorem B1815371 : Blo 535802 1815371 := bstep (se 1 (by rfl) ⟨1361528, by rfl⟩ : syracuseStep 1815371 = 2723057) B2723057
theorem B537431 : Blo 535802 537431 := bstep (se 1 (by rfl) ⟨403073, by rfl⟩ : syracuseStep 537431 = 806147) B806147
theorem B537451 : Blo 535802 537451 := bstep (se 1 (by rfl) ⟨403088, by rfl⟩ : syracuseStep 537451 = 806177) B806177
theorem B537463 : Blo 535802 537463 := bstep (se 1 (by rfl) ⟨403097, by rfl⟩ : syracuseStep 537463 = 806195) B806195
theorem B537483 : Blo 535802 537483 := bstep (se 1 (by rfl) ⟨403112, by rfl⟩ : syracuseStep 537483 = 806225) B806225
theorem B603031 : Blo 535802 603031 := bstep (se 1 (by rfl) ⟨452273, by rfl⟩ : syracuseStep 603031 = 904547) B904547
theorem B537495 : Blo 535802 537495 := bstep (se 1 (by rfl) ⟨403121, by rfl⟩ : syracuseStep 537495 = 806243) B806243
theorem B537515 : Blo 535802 537515 := bstep (se 1 (by rfl) ⟨403136, by rfl⟩ : syracuseStep 537515 = 806273) B806273
theorem B537527 : Blo 535802 537527 := bstep (se 1 (by rfl) ⟨403145, by rfl⟩ : syracuseStep 537527 = 806291) B806291
theorem B537547 : Blo 535802 537547 := bstep (se 1 (by rfl) ⟨403160, by rfl⟩ : syracuseStep 537547 = 806321) B806321
theorem B537559 : Blo 535802 537559 := bstep (se 1 (by rfl) ⟨403169, by rfl⟩ : syracuseStep 537559 = 806339) B806339
theorem B537579 : Blo 535802 537579 := bstep (se 1 (by rfl) ⟨403184, by rfl⟩ : syracuseStep 537579 = 806369) B806369
theorem B537591 : Blo 535802 537591 := bstep (se 1 (by rfl) ⟨403193, by rfl⟩ : syracuseStep 537591 = 806387) B806387
theorem B537611 : Blo 535802 537611 := bstep (se 1 (by rfl) ⟨403208, by rfl⟩ : syracuseStep 537611 = 806417) B806417
theorem B766999 : Blo 535802 766999 := bstep (se 1 (by rfl) ⟨575249, by rfl⟩ : syracuseStep 766999 = 1150499) B1150499
theorem B537623 : Blo 535802 537623 := bstep (se 1 (by rfl) ⟨403217, by rfl⟩ : syracuseStep 537623 = 806435) B806435
theorem B537643 : Blo 535802 537643 := bstep (se 1 (by rfl) ⟨403232, by rfl⟩ : syracuseStep 537643 = 806465) B806465
theorem B1356851 : Blo 535802 1356851 := bstep (se 1 (by rfl) ⟨1017638, by rfl⟩ : syracuseStep 1356851 = 2035277) B2035277
theorem B537655 : Blo 535802 537655 := bstep (se 1 (by rfl) ⟨403241, by rfl⟩ : syracuseStep 537655 = 806483) B806483
theorem B603211 : Blo 535802 603211 := bstep (se 1 (by rfl) ⟨452408, by rfl⟩ : syracuseStep 603211 = 904817) B904817
theorem B537675 : Blo 535802 537675 := bstep (se 1 (by rfl) ⟨403256, by rfl⟩ : syracuseStep 537675 = 806513) B806513
theorem B537687 : Blo 535802 537687 := bstep (se 1 (by rfl) ⟨403265, by rfl⟩ : syracuseStep 537687 = 806531) B806531
theorem B1815641 : Blo 535802 1815641 := bstep (se 2 (by rfl) ⟨680865, by rfl⟩ : syracuseStep 1815641 = 1361731) B1361731
theorem B537707 : Blo 535802 537707 := bstep (se 1 (by rfl) ⟨403280, by rfl⟩ : syracuseStep 537707 = 806561) B806561
theorem B537719 : Blo 535802 537719 := bstep (se 1 (by rfl) ⟨403289, by rfl⟩ : syracuseStep 537719 = 806579) B806579
theorem B537739 : Blo 535802 537739 := bstep (se 1 (by rfl) ⟨403304, by rfl⟩ : syracuseStep 537739 = 806609) B806609
theorem B537751 : Blo 535802 537751 := bstep (se 1 (by rfl) ⟨403313, by rfl⟩ : syracuseStep 537751 = 806627) B806627
theorem B537771 : Blo 535802 537771 := bstep (se 1 (by rfl) ⟨403328, by rfl⟩ : syracuseStep 537771 = 806657) B806657
theorem B603319 : Blo 535802 603319 := bstep (se 1 (by rfl) ⟨452489, by rfl⟩ : syracuseStep 603319 = 904979) B904979
theorem B537783 : Blo 535802 537783 := bstep (se 1 (by rfl) ⟨403337, by rfl⟩ : syracuseStep 537783 = 806675) B806675
theorem B537803 : Blo 535802 537803 := bstep (se 1 (by rfl) ⟨403352, by rfl⟩ : syracuseStep 537803 = 806705) B806705
theorem B537815 : Blo 535802 537815 := bstep (se 1 (by rfl) ⟨403361, by rfl⟩ : syracuseStep 537815 = 806723) B806723
theorem B537835 : Blo 535802 537835 := bstep (se 1 (by rfl) ⟨403376, by rfl⟩ : syracuseStep 537835 = 806753) B806753
theorem B537847 : Blo 535802 537847 := bstep (se 1 (by rfl) ⟨403385, by rfl⟩ : syracuseStep 537847 = 806771) B806771
theorem B537867 : Blo 535802 537867 := bstep (se 1 (by rfl) ⟨403400, by rfl⟩ : syracuseStep 537867 = 806801) B806801
theorem B537879 : Blo 535802 537879 := bstep (se 1 (by rfl) ⟨403409, by rfl⟩ : syracuseStep 537879 = 806819) B806819
theorem B537899 : Blo 535802 537899 := bstep (se 1 (by rfl) ⟨403424, by rfl⟩ : syracuseStep 537899 = 806849) B806849
theorem B12432685 : Blo 535802 12432685 := bstep (se 3 (by rfl) ⟨2331128, by rfl⟩ : syracuseStep 12432685 = 4662257) B4662257
theorem B537911 : Blo 535802 537911 := bstep (se 1 (by rfl) ⟨403433, by rfl⟩ : syracuseStep 537911 = 806867) B806867
theorem B1750337 : Blo 535802 1750337 := bstep (se 2 (by rfl) ⟨656376, by rfl⟩ : syracuseStep 1750337 = 1312753) B1312753
theorem B537931 : Blo 535802 537931 := bstep (se 1 (by rfl) ⟨403448, by rfl⟩ : syracuseStep 537931 = 806897) B806897
theorem B537943 : Blo 535802 537943 := bstep (se 1 (by rfl) ⟨403457, by rfl⟩ : syracuseStep 537943 = 806915) B806915
theorem B1357145 : Blo 535802 1357145 := bstep (se 2 (by rfl) ⟨508929, by rfl⟩ : syracuseStep 1357145 = 1017859) B1017859
theorem B603499 : Blo 535802 603499 := bstep (se 1 (by rfl) ⟨452624, by rfl⟩ : syracuseStep 603499 = 905249) B905249
theorem B537963 : Blo 535802 537963 := bstep (se 1 (by rfl) ⟨403472, by rfl⟩ : syracuseStep 537963 = 806945) B806945
theorem B537975 : Blo 535802 537975 := bstep (se 1 (by rfl) ⟨403481, by rfl⟩ : syracuseStep 537975 = 806963) B806963
theorem B537995 : Blo 535802 537995 := bstep (se 1 (by rfl) ⟨403496, by rfl⟩ : syracuseStep 537995 = 806993) B806993
theorem B538007 : Blo 535802 538007 := bstep (se 1 (by rfl) ⟨403505, by rfl⟩ : syracuseStep 538007 = 807011) B807011
theorem B538027 : Blo 535802 538027 := bstep (se 1 (by rfl) ⟨403520, by rfl⟩ : syracuseStep 538027 = 807041) B807041
theorem B4208051 : Blo 535802 4208051 := bstep (se 1 (by rfl) ⟨3156038, by rfl⟩ : syracuseStep 4208051 = 6312077) B6312077
theorem B538039 : Blo 535802 538039 := bstep (se 1 (by rfl) ⟨403529, by rfl⟩ : syracuseStep 538039 = 807059) B807059
theorem B538059 : Blo 535802 538059 := bstep (se 1 (by rfl) ⟨403544, by rfl⟩ : syracuseStep 538059 = 807089) B807089
theorem B603607 : Blo 535802 603607 := bstep (se 1 (by rfl) ⟨452705, by rfl⟩ : syracuseStep 603607 = 905411) B905411
theorem B538071 : Blo 535802 538071 := bstep (se 1 (by rfl) ⟨403553, by rfl⟩ : syracuseStep 538071 = 807107) B807107
theorem B538091 : Blo 535802 538091 := bstep (se 1 (by rfl) ⟨403568, by rfl⟩ : syracuseStep 538091 = 807137) B807137
theorem B538103 : Blo 535802 538103 := bstep (se 1 (by rfl) ⟨403577, by rfl⟩ : syracuseStep 538103 = 807155) B807155
theorem B538123 : Blo 535802 538123 := bstep (se 1 (by rfl) ⟨403592, by rfl⟩ : syracuseStep 538123 = 807185) B807185
theorem B538135 : Blo 535802 538135 := bstep (se 1 (by rfl) ⟨403601, by rfl⟩ : syracuseStep 538135 = 807203) B807203
theorem B538155 : Blo 535802 538155 := bstep (se 1 (by rfl) ⟨403616, by rfl⟩ : syracuseStep 538155 = 807233) B807233
theorem B538167 : Blo 535802 538167 := bstep (se 1 (by rfl) ⟨403625, by rfl⟩ : syracuseStep 538167 = 807251) B807251
theorem B538187 : Blo 535802 538187 := bstep (se 1 (by rfl) ⟨403640, by rfl⟩ : syracuseStep 538187 = 807281) B807281
theorem B538199 : Blo 535802 538199 := bstep (se 1 (by rfl) ⟨403649, by rfl⟩ : syracuseStep 538199 = 807299) B807299
theorem B538219 : Blo 535802 538219 := bstep (se 1 (by rfl) ⟨403664, by rfl⟩ : syracuseStep 538219 = 807329) B807329
theorem B538231 : Blo 535802 538231 := bstep (se 1 (by rfl) ⟨403673, by rfl⟩ : syracuseStep 538231 = 807347) B807347
theorem B9942659 : Blo 535802 9942659 := bstep (se 1 (by rfl) ⟨7456994, by rfl⟩ : syracuseStep 9942659 = 14913989) B14913989
theorem B603787 : Blo 535802 603787 := bstep (se 1 (by rfl) ⟨452840, by rfl⟩ : syracuseStep 603787 = 905681) B905681
theorem B538251 : Blo 535802 538251 := bstep (se 1 (by rfl) ⟨403688, by rfl⟩ : syracuseStep 538251 = 807377) B807377
theorem B538263 : Blo 535802 538263 := bstep (se 1 (by rfl) ⟨403697, by rfl⟩ : syracuseStep 538263 = 807395) B807395
theorem B538283 : Blo 535802 538283 := bstep (se 1 (by rfl) ⟨403712, by rfl⟩ : syracuseStep 538283 = 807425) B807425
theorem B538295 : Blo 535802 538295 := bstep (se 1 (by rfl) ⟨403721, by rfl⟩ : syracuseStep 538295 = 807443) B807443
theorem B538315 : Blo 535802 538315 := bstep (se 1 (by rfl) ⟨403736, by rfl⟩ : syracuseStep 538315 = 807473) B807473
theorem B538327 : Blo 535802 538327 := bstep (se 1 (by rfl) ⟨403745, by rfl⟩ : syracuseStep 538327 = 807491) B807491
theorem B538347 : Blo 535802 538347 := bstep (se 1 (by rfl) ⟨403760, by rfl⟩ : syracuseStep 538347 = 807521) B807521
theorem B603895 : Blo 535802 603895 := bstep (se 1 (by rfl) ⟨452921, by rfl⟩ : syracuseStep 603895 = 905843) B905843
theorem B538359 : Blo 535802 538359 := bstep (se 1 (by rfl) ⟨403769, by rfl⟩ : syracuseStep 538359 = 807539) B807539
theorem B538379 : Blo 535802 538379 := bstep (se 1 (by rfl) ⟨403784, by rfl⟩ : syracuseStep 538379 = 807569) B807569
theorem B1816343 : Blo 535802 1816343 := bstep (se 1 (by rfl) ⟨1362257, by rfl⟩ : syracuseStep 1816343 = 2724515) B2724515
theorem B538391 : Blo 535802 538391 := bstep (se 1 (by rfl) ⟨403793, by rfl⟩ : syracuseStep 538391 = 807587) B807587
theorem B538411 : Blo 535802 538411 := bstep (se 1 (by rfl) ⟨403808, by rfl⟩ : syracuseStep 538411 = 807617) B807617
theorem B3323693 : Blo 535802 3323693 := bstep (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) B1246385
theorem B538423 : Blo 535802 538423 := bstep (se 1 (by rfl) ⟨403817, by rfl⟩ : syracuseStep 538423 = 807635) B807635
theorem B538443 : Blo 535802 538443 := bstep (se 1 (by rfl) ⟨403832, by rfl⟩ : syracuseStep 538443 = 807665) B807665
theorem B538455 : Blo 535802 538455 := bstep (se 1 (by rfl) ⟨403841, by rfl⟩ : syracuseStep 538455 = 807683) B807683
theorem B538475 : Blo 535802 538475 := bstep (se 1 (by rfl) ⟨403856, by rfl⟩ : syracuseStep 538475 = 807713) B807713
theorem B538487 : Blo 535802 538487 := bstep (se 1 (by rfl) ⟨403865, by rfl⟩ : syracuseStep 538487 = 807731) B807731
theorem B538507 : Blo 535802 538507 := bstep (se 1 (by rfl) ⟨403880, by rfl⟩ : syracuseStep 538507 = 807761) B807761
theorem B538519 : Blo 535802 538519 := bstep (se 1 (by rfl) ⟨403889, by rfl⟩ : syracuseStep 538519 = 807779) B807779
theorem B604075 : Blo 535802 604075 := bstep (se 1 (by rfl) ⟨453056, by rfl⟩ : syracuseStep 604075 = 906113) B906113
theorem B538539 : Blo 535802 538539 := bstep (se 1 (by rfl) ⟨403904, by rfl⟩ : syracuseStep 538539 = 807809) B807809
theorem B538551 : Blo 535802 538551 := bstep (se 1 (by rfl) ⟨403913, by rfl⟩ : syracuseStep 538551 = 807827) B807827
theorem B538571 : Blo 535802 538571 := bstep (se 1 (by rfl) ⟨403928, by rfl⟩ : syracuseStep 538571 = 807857) B807857
theorem B538583 : Blo 535802 538583 := bstep (se 1 (by rfl) ⟨403937, by rfl⟩ : syracuseStep 538583 = 807875) B807875
theorem B538603 : Blo 535802 538603 := bstep (se 1 (by rfl) ⟨403952, by rfl⟩ : syracuseStep 538603 = 807905) B807905
theorem B538615 : Blo 535802 538615 := bstep (se 1 (by rfl) ⟨403961, by rfl⟩ : syracuseStep 538615 = 807923) B807923
theorem B538635 : Blo 535802 538635 := bstep (se 1 (by rfl) ⟨403976, by rfl⟩ : syracuseStep 538635 = 807953) B807953
theorem B2045969 : Blo 535802 2045969 := bstep (se 2 (by rfl) ⟨767238, by rfl⟩ : syracuseStep 2045969 = 1534477) B1534477
theorem B604183 : Blo 535802 604183 := bstep (se 1 (by rfl) ⟨453137, by rfl⟩ : syracuseStep 604183 = 906275) B906275
theorem B538647 : Blo 535802 538647 := bstep (se 1 (by rfl) ⟨403985, by rfl⟩ : syracuseStep 538647 = 807971) B807971
theorem B538667 : Blo 535802 538667 := bstep (se 1 (by rfl) ⟨404000, by rfl⟩ : syracuseStep 538667 = 808001) B808001
theorem B538679 : Blo 535802 538679 := bstep (se 1 (by rfl) ⟨404009, by rfl⟩ : syracuseStep 538679 = 808019) B808019
theorem B538699 : Blo 535802 538699 := bstep (se 1 (by rfl) ⟨404024, by rfl⟩ : syracuseStep 538699 = 808049) B808049
theorem B538711 : Blo 535802 538711 := bstep (se 1 (by rfl) ⟨404033, by rfl⟩ : syracuseStep 538711 = 808067) B808067
theorem B538731 : Blo 535802 538731 := bstep (se 1 (by rfl) ⟨404048, by rfl⟩ : syracuseStep 538731 = 808097) B808097
theorem B538743 : Blo 535802 538743 := bstep (se 1 (by rfl) ⟨404057, by rfl⟩ : syracuseStep 538743 = 808115) B808115
theorem B538763 : Blo 535802 538763 := bstep (se 1 (by rfl) ⟨404072, by rfl⟩ : syracuseStep 538763 = 808145) B808145
theorem B39172247 : Blo 535802 39172247 := bstep (se 1 (by rfl) ⟨29379185, by rfl⟩ : syracuseStep 39172247 = 58758371) B58758371
theorem B2209943 : Blo 535802 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B538775 : Blo 535802 538775 := bstep (se 1 (by rfl) ⟨404081, by rfl⟩ : syracuseStep 538775 = 808163) B808163
theorem B538795 : Blo 535802 538795 := bstep (se 1 (by rfl) ⟨404096, by rfl⟩ : syracuseStep 538795 = 808193) B808193
theorem B538807 : Blo 535802 538807 := bstep (se 1 (by rfl) ⟨404105, by rfl⟩ : syracuseStep 538807 = 808211) B808211
theorem B604363 : Blo 535802 604363 := bstep (se 1 (by rfl) ⟨453272, by rfl⟩ : syracuseStep 604363 = 906545) B906545
theorem B538827 : Blo 535802 538827 := bstep (se 1 (by rfl) ⟨404120, by rfl⟩ : syracuseStep 538827 = 808241) B808241
theorem B538839 : Blo 535802 538839 := bstep (se 1 (by rfl) ⟨404129, by rfl⟩ : syracuseStep 538839 = 808259) B808259
theorem B538859 : Blo 535802 538859 := bstep (se 1 (by rfl) ⟨404144, by rfl⟩ : syracuseStep 538859 = 808289) B808289
theorem B538871 : Blo 535802 538871 := bstep (se 1 (by rfl) ⟨404153, by rfl⟩ : syracuseStep 538871 = 808307) B808307
theorem B538891 : Blo 535802 538891 := bstep (se 1 (by rfl) ⟨404168, by rfl⟩ : syracuseStep 538891 = 808337) B808337
theorem B538903 : Blo 535802 538903 := bstep (se 1 (by rfl) ⟨404177, by rfl⟩ : syracuseStep 538903 = 808355) B808355
theorem B538923 : Blo 535802 538923 := bstep (se 1 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 538923 = 808385) B808385
theorem B1816883 : Blo 535802 1816883 := bstep (se 1 (by rfl) ⟨1362662, by rfl⟩ : syracuseStep 1816883 = 2725325) B2725325
theorem B604471 : Blo 535802 604471 := bstep (se 1 (by rfl) ⟨453353, by rfl⟩ : syracuseStep 604471 = 906707) B906707
theorem B538935 : Blo 535802 538935 := bstep (se 1 (by rfl) ⟨404201, by rfl⟩ : syracuseStep 538935 = 808403) B808403
theorem B538955 : Blo 535802 538955 := bstep (se 1 (by rfl) ⟨404216, by rfl⟩ : syracuseStep 538955 = 808433) B808433
theorem B538967 : Blo 535802 538967 := bstep (se 1 (by rfl) ⟨404225, by rfl⟩ : syracuseStep 538967 = 808451) B808451
theorem B538987 : Blo 535802 538987 := bstep (se 1 (by rfl) ⟨404240, by rfl⟩ : syracuseStep 538987 = 808481) B808481
theorem B538999 : Blo 535802 538999 := bstep (se 1 (by rfl) ⟨404249, by rfl⟩ : syracuseStep 538999 = 808499) B808499
theorem B539019 : Blo 535802 539019 := bstep (se 1 (by rfl) ⟨404264, by rfl⟩ : syracuseStep 539019 = 808529) B808529
theorem B539031 : Blo 535802 539031 := bstep (se 1 (by rfl) ⟨404273, by rfl⟩ : syracuseStep 539031 = 808547) B808547
theorem B1554839 : Blo 535802 1554839 := bstep (se 1 (by rfl) ⟨1166129, by rfl⟩ : syracuseStep 1554839 = 2332259) B2332259
theorem B1456535 : Blo 535802 1456535 := bstep (se 1 (by rfl) ⟨1092401, by rfl⟩ : syracuseStep 1456535 = 2184803) B2184803
theorem B539051 : Blo 535802 539051 := bstep (se 1 (by rfl) ⟨404288, by rfl⟩ : syracuseStep 539051 = 808577) B808577
theorem B539063 : Blo 535802 539063 := bstep (se 1 (by rfl) ⟨404297, by rfl⟩ : syracuseStep 539063 = 808595) B808595
theorem B539083 : Blo 535802 539083 := bstep (se 1 (by rfl) ⟨404312, by rfl⟩ : syracuseStep 539083 = 808625) B808625
theorem B539095 : Blo 535802 539095 := bstep (se 1 (by rfl) ⟨404321, by rfl⟩ : syracuseStep 539095 = 808643) B808643
theorem B604651 : Blo 535802 604651 := bstep (se 1 (by rfl) ⟨453488, by rfl⟩ : syracuseStep 604651 = 906977) B906977
theorem B539115 : Blo 535802 539115 := bstep (se 1 (by rfl) ⟨404336, by rfl⟩ : syracuseStep 539115 = 808673) B808673
theorem B539127 : Blo 535802 539127 := bstep (se 1 (by rfl) ⟨404345, by rfl⟩ : syracuseStep 539127 = 808691) B808691
theorem B539147 : Blo 535802 539147 := bstep (se 1 (by rfl) ⟨404360, by rfl⟩ : syracuseStep 539147 = 808721) B808721
theorem B539159 : Blo 535802 539159 := bstep (se 1 (by rfl) ⟨404369, by rfl⟩ : syracuseStep 539159 = 808739) B808739
theorem B539179 : Blo 535802 539179 := bstep (se 1 (by rfl) ⟨404384, by rfl⟩ : syracuseStep 539179 = 808769) B808769
theorem B1292851 : Blo 535802 1292851 := bstep (se 1 (by rfl) ⟨969638, by rfl⟩ : syracuseStep 1292851 = 1939277) B1939277
theorem B539191 : Blo 535802 539191 := bstep (se 1 (by rfl) ⟨404393, by rfl⟩ : syracuseStep 539191 = 808787) B808787
theorem B1817153 : Blo 535802 1817153 := bstep (se 2 (by rfl) ⟨681432, by rfl⟩ : syracuseStep 1817153 = 1362865) B1362865
theorem B539211 : Blo 535802 539211 := bstep (se 1 (by rfl) ⟨404408, by rfl⟩ : syracuseStep 539211 = 808817) B808817
theorem B604759 : Blo 535802 604759 := bstep (se 1 (by rfl) ⟨453569, by rfl⟩ : syracuseStep 604759 = 907139) B907139
theorem B539223 : Blo 535802 539223 := bstep (se 1 (by rfl) ⟨404417, by rfl⟩ : syracuseStep 539223 = 808835) B808835
theorem B539243 : Blo 535802 539243 := bstep (se 1 (by rfl) ⟨404432, by rfl⟩ : syracuseStep 539243 = 808865) B808865
theorem B539255 : Blo 535802 539255 := bstep (se 1 (by rfl) ⟨404441, by rfl⟩ : syracuseStep 539255 = 808883) B808883
theorem B539275 : Blo 535802 539275 := bstep (se 1 (by rfl) ⟨404456, by rfl⟩ : syracuseStep 539275 = 808913) B808913
theorem B539287 : Blo 535802 539287 := bstep (se 1 (by rfl) ⟨404465, by rfl⟩ : syracuseStep 539287 = 808931) B808931
theorem B539307 : Blo 535802 539307 := bstep (se 1 (by rfl) ⟨404480, by rfl⟩ : syracuseStep 539307 = 808961) B808961
theorem B539319 : Blo 535802 539319 := bstep (se 1 (by rfl) ⟨404489, by rfl⟩ : syracuseStep 539319 = 808979) B808979
theorem B2046667 : Blo 535802 2046667 := bstep (se 1 (by rfl) ⟨1535000, by rfl⟩ : syracuseStep 2046667 = 3070001) B3070001
theorem B539339 : Blo 535802 539339 := bstep (se 1 (by rfl) ⟨404504, by rfl⟩ : syracuseStep 539339 = 809009) B809009
theorem B539351 : Blo 535802 539351 := bstep (se 1 (by rfl) ⟨404513, by rfl⟩ : syracuseStep 539351 = 809027) B809027
theorem B539371 : Blo 535802 539371 := bstep (se 1 (by rfl) ⟨404528, by rfl⟩ : syracuseStep 539371 = 809057) B809057
theorem B539383 : Blo 535802 539383 := bstep (se 1 (by rfl) ⟨404537, by rfl⟩ : syracuseStep 539383 = 809075) B809075
theorem B604939 : Blo 535802 604939 := bstep (se 1 (by rfl) ⟨453704, by rfl⟩ : syracuseStep 604939 = 907409) B907409
theorem B539403 : Blo 535802 539403 := bstep (se 1 (by rfl) ⟨404552, by rfl⟩ : syracuseStep 539403 = 809105) B809105
theorem B539415 : Blo 535802 539415 := bstep (se 1 (by rfl) ⟨404561, by rfl⟩ : syracuseStep 539415 = 809123) B809123
theorem B539435 : Blo 535802 539435 := bstep (se 1 (by rfl) ⟨404576, by rfl⟩ : syracuseStep 539435 = 809153) B809153
theorem B539447 : Blo 535802 539447 := bstep (se 1 (by rfl) ⟨404585, by rfl⟩ : syracuseStep 539447 = 809171) B809171
theorem B539467 : Blo 535802 539467 := bstep (se 1 (by rfl) ⟨404600, by rfl⟩ : syracuseStep 539467 = 809201) B809201
theorem B539479 : Blo 535802 539479 := bstep (se 1 (by rfl) ⟨404609, by rfl⟩ : syracuseStep 539479 = 809219) B809219
theorem B539499 : Blo 535802 539499 := bstep (se 1 (by rfl) ⟨404624, by rfl⟩ : syracuseStep 539499 = 809249) B809249
theorem B605047 : Blo 535802 605047 := bstep (se 1 (by rfl) ⟨453785, by rfl⟩ : syracuseStep 605047 = 907571) B907571
theorem B539511 : Blo 535802 539511 := bstep (se 1 (by rfl) ⟨404633, by rfl⟩ : syracuseStep 539511 = 809267) B809267
theorem B539531 : Blo 535802 539531 := bstep (se 1 (by rfl) ⟨404648, by rfl⟩ : syracuseStep 539531 = 809297) B809297
theorem B539543 : Blo 535802 539543 := bstep (se 1 (by rfl) ⟨404657, by rfl⟩ : syracuseStep 539543 = 809315) B809315
theorem B539563 : Blo 535802 539563 := bstep (se 1 (by rfl) ⟨404672, by rfl⟩ : syracuseStep 539563 = 809345) B809345
theorem B539575 : Blo 535802 539575 := bstep (se 1 (by rfl) ⟨404681, by rfl⟩ : syracuseStep 539575 = 809363) B809363
theorem B1358795 : Blo 535802 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B539595 : Blo 535802 539595 := bstep (se 1 (by rfl) ⟨404696, by rfl⟩ : syracuseStep 539595 = 809393) B809393
theorem B539607 : Blo 535802 539607 := bstep (se 1 (by rfl) ⟨404705, by rfl⟩ : syracuseStep 539607 = 809411) B809411
theorem B2046941 : Blo 535802 2046941 := bstep (se 3 (by rfl) ⟨383801, by rfl⟩ : syracuseStep 2046941 = 767603) B767603
theorem B539627 : Blo 535802 539627 := bstep (se 1 (by rfl) ⟨404720, by rfl⟩ : syracuseStep 539627 = 809441) B809441
theorem B539639 : Blo 535802 539639 := bstep (se 1 (by rfl) ⟨404729, by rfl⟩ : syracuseStep 539639 = 809459) B809459
theorem B539659 : Blo 535802 539659 := bstep (se 1 (by rfl) ⟨404744, by rfl⟩ : syracuseStep 539659 = 809489) B809489
theorem B539671 : Blo 535802 539671 := bstep (se 1 (by rfl) ⟨404753, by rfl⟩ : syracuseStep 539671 = 809507) B809507
theorem B605227 : Blo 535802 605227 := bstep (se 1 (by rfl) ⟨453920, by rfl⟩ : syracuseStep 605227 = 907841) B907841
theorem B539691 : Blo 535802 539691 := bstep (se 1 (by rfl) ⟨404768, by rfl⟩ : syracuseStep 539691 = 809537) B809537
theorem B539703 : Blo 535802 539703 := bstep (se 1 (by rfl) ⟨404777, by rfl⟩ : syracuseStep 539703 = 809555) B809555
theorem B539723 : Blo 535802 539723 := bstep (se 1 (by rfl) ⟨404792, by rfl⟩ : syracuseStep 539723 = 809585) B809585
theorem B539735 : Blo 535802 539735 := bstep (se 1 (by rfl) ⟨404801, by rfl⟩ : syracuseStep 539735 = 809603) B809603
theorem B1817693 : Blo 535802 1817693 := bstep (se 3 (by rfl) ⟨340817, by rfl⟩ : syracuseStep 1817693 = 681635) B681635
theorem B539755 : Blo 535802 539755 := bstep (se 1 (by rfl) ⟨404816, by rfl⟩ : syracuseStep 539755 = 809633) B809633
theorem B539767 : Blo 535802 539767 := bstep (se 1 (by rfl) ⟨404825, by rfl⟩ : syracuseStep 539767 = 809651) B809651
theorem B539787 : Blo 535802 539787 := bstep (se 1 (by rfl) ⟨404840, by rfl⟩ : syracuseStep 539787 = 809681) B809681
theorem B572567 : Blo 535802 572567 := bstep (se 1 (by rfl) ⟨429425, by rfl⟩ : syracuseStep 572567 = 858851) B858851
theorem B605335 : Blo 535802 605335 := bstep (se 1 (by rfl) ⟨454001, by rfl⟩ : syracuseStep 605335 = 908003) B908003
theorem B539799 : Blo 535802 539799 := bstep (se 1 (by rfl) ⟨404849, by rfl⟩ : syracuseStep 539799 = 809699) B809699
theorem B605515 : Blo 535802 605515 := bstep (se 1 (by rfl) ⟨454136, by rfl⟩ : syracuseStep 605515 = 908273) B908273
theorem B605623 : Blo 535802 605623 := bstep (se 1 (by rfl) ⟨454217, by rfl⟩ : syracuseStep 605623 = 908435) B908435
theorem B605803 : Blo 535802 605803 := bstep (se 1 (by rfl) ⟨454352, by rfl⟩ : syracuseStep 605803 = 908705) B908705
theorem B2047639 : Blo 535802 2047639 := bstep (se 1 (by rfl) ⟨1535729, by rfl⟩ : syracuseStep 2047639 = 3071459) B3071459
theorem B605911 : Blo 535802 605911 := bstep (se 1 (by rfl) ⟨454433, by rfl⟩ : syracuseStep 605911 = 908867) B908867
theorem B1326871 : Blo 535802 1326871 := bstep (se 1 (by rfl) ⟨995153, by rfl⟩ : syracuseStep 1326871 = 1990307) B1990307
theorem B1261363 : Blo 535802 1261363 := bstep (se 1 (by rfl) ⟨946022, by rfl⟩ : syracuseStep 1261363 = 1892045) B1892045
theorem B1457995 : Blo 535802 1457995 := bstep (se 1 (by rfl) ⟨1093496, by rfl⟩ : syracuseStep 1457995 = 2186993) B2186993
theorem B606091 : Blo 535802 606091 := bstep (se 1 (by rfl) ⟨454568, by rfl⟩ : syracuseStep 606091 = 909137) B909137
theorem B1359767 : Blo 535802 1359767 := bstep (se 1 (by rfl) ⟨1019825, by rfl⟩ : syracuseStep 1359767 = 2039651) B2039651
theorem B606199 : Blo 535802 606199 := bstep (se 1 (by rfl) ⟨454649, by rfl⟩ : syracuseStep 606199 = 909299) B909299
theorem B606379 : Blo 535802 606379 := bstep (se 1 (by rfl) ⟨454784, by rfl⟩ : syracuseStep 606379 = 909569) B909569
theorem B1818827 : Blo 535802 1818827 := bstep (se 1 (by rfl) ⟨1364120, by rfl⟩ : syracuseStep 1818827 = 2728241) B2728241
theorem B606487 : Blo 535802 606487 := bstep (se 1 (by rfl) ⟨454865, by rfl⟩ : syracuseStep 606487 = 909731) B909731
theorem B2048429 : Blo 535802 2048429 := bstep (se 3 (by rfl) ⟨384080, by rfl⟩ : syracuseStep 2048429 = 768161) B768161
theorem B1458611 : Blo 535802 1458611 := bstep (se 1 (by rfl) ⟨1093958, by rfl⟩ : syracuseStep 1458611 = 2187917) B2187917
theorem B606667 : Blo 535802 606667 := bstep (se 1 (by rfl) ⟨455000, by rfl⟩ : syracuseStep 606667 = 910001) B910001
theorem B1819097 : Blo 535802 1819097 := bstep (se 2 (by rfl) ⟨682161, by rfl⟩ : syracuseStep 1819097 = 1364323) B1364323
theorem B1360435 : Blo 535802 1360435 := bstep (se 1 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 1360435 = 2040653) B2040653
theorem B606775 : Blo 535802 606775 := bstep (se 1 (by rfl) ⟨455081, by rfl⟩ : syracuseStep 606775 = 910163) B910163
theorem B1360577 : Blo 535802 1360577 := bstep (se 2 (by rfl) ⟨510216, by rfl⟩ : syracuseStep 1360577 = 1020433) B1020433
theorem B606955 : Blo 535802 606955 := bstep (se 1 (by rfl) ⟨455216, by rfl⟩ : syracuseStep 606955 = 910433) B910433
theorem B607063 : Blo 535802 607063 := bstep (se 1 (by rfl) ⟨455297, by rfl⟩ : syracuseStep 607063 = 910595) B910595
theorem B574327 : Blo 535802 574327 := bstep (se 1 (by rfl) ⟨430745, by rfl⟩ : syracuseStep 574327 = 861491) B861491
theorem B803723 : Blo 535802 803723 := bstep (se 1 (by rfl) ⟨602792, by rfl⟩ : syracuseStep 803723 = 1205585) B1205585
theorem B803735 : Blo 535802 803735 := bstep (se 1 (by rfl) ⟨602801, by rfl⟩ : syracuseStep 803735 = 1205603) B1205603
theorem B803801 : Blo 535802 803801 := bstep (se 2 (by rfl) ⟨301425, by rfl⟩ : syracuseStep 803801 = 602851) B602851
theorem B607243 : Blo 535802 607243 := bstep (se 1 (by rfl) ⟨455432, by rfl⟩ : syracuseStep 607243 = 910865) B910865
theorem B3064877 : Blo 535802 3064877 := bstep (se 3 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 3064877 = 1149329) B1149329
theorem B803915 : Blo 535802 803915 := bstep (se 1 (by rfl) ⟨602936, by rfl⟩ : syracuseStep 803915 = 1205873) B1205873
theorem B1229899 : Blo 535802 1229899 := bstep (se 1 (by rfl) ⟨922424, by rfl⟩ : syracuseStep 1229899 = 1844849) B1844849
theorem B803927 : Blo 535802 803927 := bstep (se 1 (by rfl) ⟨602945, by rfl⟩ : syracuseStep 803927 = 1205891) B1205891
theorem B1819799 : Blo 535802 1819799 := bstep (se 1 (by rfl) ⟨1364849, by rfl⟩ : syracuseStep 1819799 = 2729699) B2729699
theorem B803993 : Blo 535802 803993 := bstep (se 2 (by rfl) ⟨301497, by rfl⟩ : syracuseStep 803993 = 602995) B602995
theorem B804107 : Blo 535802 804107 := bstep (se 1 (by rfl) ⟨603080, by rfl⟩ : syracuseStep 804107 = 1206161) B1206161
theorem B804119 : Blo 535802 804119 := bstep (se 1 (by rfl) ⟨603089, by rfl⟩ : syracuseStep 804119 = 1206179) B1206179
theorem B1295639 : Blo 535802 1295639 := bstep (se 1 (by rfl) ⟨971729, by rfl⟩ : syracuseStep 1295639 = 1943459) B1943459
theorem B4080941 : Blo 535802 4080941 := bstep (se 3 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 4080941 = 1530353) B1530353
theorem B1721675 : Blo 535802 1721675 := bstep (se 1 (by rfl) ⟨1291256, by rfl⟩ : syracuseStep 1721675 = 2582513) B2582513
theorem B1230155 : Blo 535802 1230155 := bstep (se 1 (by rfl) ⟨922616, by rfl⟩ : syracuseStep 1230155 = 1845233) B1845233
theorem B804185 : Blo 535802 804185 := bstep (se 2 (by rfl) ⟨301569, by rfl⟩ : syracuseStep 804185 = 603139) B603139
theorem B9848243 : Blo 535802 9848243 := bstep (se 1 (by rfl) ⟨7386182, by rfl⟩ : syracuseStep 9848243 = 14772365) B14772365
theorem B804299 : Blo 535802 804299 := bstep (se 1 (by rfl) ⟨603224, by rfl⟩ : syracuseStep 804299 = 1206449) B1206449
theorem B804311 : Blo 535802 804311 := bstep (se 1 (by rfl) ⟨603233, by rfl⟩ : syracuseStep 804311 = 1206467) B1206467
theorem B804377 : Blo 535802 804377 := bstep (se 2 (by rfl) ⟨301641, by rfl⟩ : syracuseStep 804377 = 603283) B603283
theorem B804491 : Blo 535802 804491 := bstep (se 1 (by rfl) ⟨603368, by rfl⟩ : syracuseStep 804491 = 1206737) B1206737
theorem B804503 : Blo 535802 804503 := bstep (se 1 (by rfl) ⟨603377, by rfl⟩ : syracuseStep 804503 = 1206755) B1206755
theorem B575147 : Blo 535802 575147 := bstep (se 1 (by rfl) ⟨431360, by rfl⟩ : syracuseStep 575147 = 862721) B862721
theorem B1820339 : Blo 535802 1820339 := bstep (se 1 (by rfl) ⟨1365254, by rfl⟩ : syracuseStep 1820339 = 2730509) B2730509
theorem B804569 : Blo 535802 804569 := bstep (se 2 (by rfl) ⟨301713, by rfl⟩ : syracuseStep 804569 = 603427) B603427
theorem B804683 : Blo 535802 804683 := bstep (se 1 (by rfl) ⟨603512, by rfl⟩ : syracuseStep 804683 = 1207025) B1207025
theorem B804695 : Blo 535802 804695 := bstep (se 1 (by rfl) ⟨603521, by rfl⟩ : syracuseStep 804695 = 1207043) B1207043
theorem B804761 : Blo 535802 804761 := bstep (se 2 (by rfl) ⟨301785, by rfl⟩ : syracuseStep 804761 = 603571) B603571
theorem B1361843 : Blo 535802 1361843 := bstep (se 1 (by rfl) ⟨1021382, by rfl⟩ : syracuseStep 1361843 = 2042765) B2042765
theorem B1820609 : Blo 535802 1820609 := bstep (se 2 (by rfl) ⟨682728, by rfl⟩ : syracuseStep 1820609 = 1365457) B1365457
theorem B804875 : Blo 535802 804875 := bstep (se 1 (by rfl) ⟨603656, by rfl⟩ : syracuseStep 804875 = 1207313) B1207313
theorem B804887 : Blo 535802 804887 := bstep (se 1 (by rfl) ⟨603665, by rfl⟩ : syracuseStep 804887 = 1207331) B1207331
theorem B2902081 : Blo 535802 2902081 := bstep (se 2 (by rfl) ⟨1088280, by rfl⟩ : syracuseStep 2902081 = 2176561) B2176561
theorem B804953 : Blo 535802 804953 := bstep (se 2 (by rfl) ⟨301857, by rfl⟩ : syracuseStep 804953 = 603715) B603715
theorem B805067 : Blo 535802 805067 := bstep (se 1 (by rfl) ⟨603800, by rfl⟩ : syracuseStep 805067 = 1207601) B1207601
theorem B805079 : Blo 535802 805079 := bstep (se 1 (by rfl) ⟨603809, by rfl⟩ : syracuseStep 805079 = 1207619) B1207619
theorem B805145 : Blo 535802 805145 := bstep (se 2 (by rfl) ⟨301929, by rfl⟩ : syracuseStep 805145 = 603859) B603859
theorem B805259 : Blo 535802 805259 := bstep (se 1 (by rfl) ⟨603944, by rfl⟩ : syracuseStep 805259 = 1207889) B1207889
theorem B805271 : Blo 535802 805271 := bstep (se 1 (by rfl) ⟨603953, by rfl⟩ : syracuseStep 805271 = 1207907) B1207907
theorem B1362379 : Blo 535802 1362379 := bstep (se 1 (by rfl) ⟨1021784, by rfl⟩ : syracuseStep 1362379 = 2043569) B2043569
theorem B805337 : Blo 535802 805337 := bstep (se 2 (by rfl) ⟨302001, by rfl⟩ : syracuseStep 805337 = 604003) B604003
theorem B1821149 : Blo 535802 1821149 := bstep (se 3 (by rfl) ⟨341465, by rfl⟩ : syracuseStep 1821149 = 682931) B682931
theorem B805451 : Blo 535802 805451 := bstep (se 1 (by rfl) ⟨604088, by rfl⟩ : syracuseStep 805451 = 1208177) B1208177
theorem B805463 : Blo 535802 805463 := bstep (se 1 (by rfl) ⟨604097, by rfl⟩ : syracuseStep 805463 = 1208195) B1208195
theorem B1362521 : Blo 535802 1362521 := bstep (se 2 (by rfl) ⟨510945, by rfl⟩ : syracuseStep 1362521 = 1021891) B1021891
theorem B805529 : Blo 535802 805529 := bstep (se 2 (by rfl) ⟨302073, by rfl⟩ : syracuseStep 805529 = 604147) B604147
theorem B805643 : Blo 535802 805643 := bstep (se 1 (by rfl) ⟨604232, by rfl⟩ : syracuseStep 805643 = 1208465) B1208465
theorem B805655 : Blo 535802 805655 := bstep (se 1 (by rfl) ⟨604241, by rfl⟩ : syracuseStep 805655 = 1208483) B1208483
theorem B576343 : Blo 535802 576343 := bstep (se 1 (by rfl) ⟨432257, by rfl⟩ : syracuseStep 576343 = 864515) B864515
theorem B1526617 : Blo 535802 1526617 := bstep (se 2 (by rfl) ⟨572481, by rfl⟩ : syracuseStep 1526617 = 1144963) B1144963
theorem B805721 : Blo 535802 805721 := bstep (se 2 (by rfl) ⟨302145, by rfl⟩ : syracuseStep 805721 = 604291) B604291
theorem B1723315 : Blo 535802 1723315 := bstep (se 1 (by rfl) ⟨1292486, by rfl⟩ : syracuseStep 1723315 = 2584973) B2584973
theorem B805835 : Blo 535802 805835 := bstep (se 1 (by rfl) ⟨604376, by rfl⟩ : syracuseStep 805835 = 1208753) B1208753
theorem B805847 : Blo 535802 805847 := bstep (se 1 (by rfl) ⟨604385, by rfl⟩ : syracuseStep 805847 = 1208771) B1208771
theorem B805913 : Blo 535802 805913 := bstep (se 2 (by rfl) ⟨302217, by rfl⟩ : syracuseStep 805913 = 604435) B604435
theorem B4901933 : Blo 535802 4901933 := bstep (se 3 (by rfl) ⟨919112, by rfl⟩ : syracuseStep 4901933 = 1838225) B1838225
theorem B904331 : Blo 535802 904331 := bstep (se 1 (by rfl) ⟨678248, by rfl⟩ : syracuseStep 904331 = 1356497) B1356497
theorem B806027 : Blo 535802 806027 := bstep (se 1 (by rfl) ⟨604520, by rfl⟩ : syracuseStep 806027 = 1209041) B1209041
theorem B806039 : Blo 535802 806039 := bstep (se 1 (by rfl) ⟨604529, by rfl⟩ : syracuseStep 806039 = 1209059) B1209059
theorem B806105 : Blo 535802 806105 := bstep (se 2 (by rfl) ⟨302289, by rfl⟩ : syracuseStep 806105 = 604579) B604579
theorem B3493081 : Blo 535802 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B1527005 : Blo 535802 1527005 := bstep (se 3 (by rfl) ⟨286313, by rfl⟩ : syracuseStep 1527005 = 572627) B572627
theorem B543991 : Blo 535802 543991 := bstep (se 1 (by rfl) ⟨407993, by rfl⟩ : syracuseStep 543991 = 815987) B815987
theorem B904459 : Blo 535802 904459 := bstep (se 1 (by rfl) ⟨678344, by rfl⟩ : syracuseStep 904459 = 1356689) B1356689
theorem B806219 : Blo 535802 806219 := bstep (se 1 (by rfl) ⟨604664, by rfl⟩ : syracuseStep 806219 = 1209329) B1209329
theorem B806231 : Blo 535802 806231 := bstep (se 1 (by rfl) ⟨604673, by rfl⟩ : syracuseStep 806231 = 1209347) B1209347
theorem B3067267 : Blo 535802 3067267 := bstep (se 1 (by rfl) ⟨2300450, by rfl⟩ : syracuseStep 3067267 = 4600901) B4600901
theorem B1363351 : Blo 535802 1363351 := bstep (se 1 (by rfl) ⟨1022513, by rfl⟩ : syracuseStep 1363351 = 2045027) B2045027
theorem B904601 : Blo 535802 904601 := bstep (se 2 (by rfl) ⟨339225, by rfl⟩ : syracuseStep 904601 = 678451) B678451
theorem B806297 : Blo 535802 806297 := bstep (se 2 (by rfl) ⟨302361, by rfl⟩ : syracuseStep 806297 = 604723) B604723
theorem B2248157 : Blo 535802 2248157 := bstep (se 3 (by rfl) ⟨421529, by rfl⟩ : syracuseStep 2248157 = 843059) B843059
theorem B806411 : Blo 535802 806411 := bstep (se 1 (by rfl) ⟨604808, by rfl⟩ : syracuseStep 806411 = 1209617) B1209617
theorem B806423 : Blo 535802 806423 := bstep (se 1 (by rfl) ⟨604817, by rfl⟩ : syracuseStep 806423 = 1209635) B1209635
theorem B904729 : Blo 535802 904729 := bstep (se 2 (by rfl) ⟨339273, by rfl⟩ : syracuseStep 904729 = 678547) B678547
theorem B6114851 : Blo 535802 6114851 := bstep (se 1 (by rfl) ⟨4586138, by rfl⟩ : syracuseStep 6114851 = 9172277) B9172277
theorem B2575937 : Blo 535802 2575937 := bstep (se 2 (by rfl) ⟨965976, by rfl⟩ : syracuseStep 2575937 = 1931953) B1931953
theorem B806489 : Blo 535802 806489 := bstep (se 2 (by rfl) ⟨302433, by rfl⟩ : syracuseStep 806489 = 604867) B604867
theorem B806603 : Blo 535802 806603 := bstep (se 1 (by rfl) ⟨604952, by rfl⟩ : syracuseStep 806603 = 1209905) B1209905
theorem B806615 : Blo 535802 806615 := bstep (se 1 (by rfl) ⟨604961, by rfl⟩ : syracuseStep 806615 = 1209923) B1209923
theorem B806681 : Blo 535802 806681 := bstep (se 2 (by rfl) ⟨302505, by rfl⟩ : syracuseStep 806681 = 605011) B605011
theorem B1363787 : Blo 535802 1363787 := bstep (se 1 (by rfl) ⟨1022840, by rfl⟩ : syracuseStep 1363787 = 2045681) B2045681
theorem B16568165 : Blo 535802 16568165 := bstep (se 4 (by rfl) ⟨1553265, by rfl⟩ : syracuseStep 16568165 = 3106531) B3106531
theorem B806795 : Blo 535802 806795 := bstep (se 1 (by rfl) ⟨605096, by rfl⟩ : syracuseStep 806795 = 1210193) B1210193
theorem B3264407 : Blo 535802 3264407 := bstep (se 1 (by rfl) ⟨2448305, by rfl⟩ : syracuseStep 3264407 = 4896611) B4896611
theorem B806807 : Blo 535802 806807 := bstep (se 1 (by rfl) ⟨605105, by rfl⟩ : syracuseStep 806807 = 1210211) B1210211
theorem B806873 : Blo 535802 806873 := bstep (se 2 (by rfl) ⟨302577, by rfl⟩ : syracuseStep 806873 = 605155) B605155
theorem B806987 : Blo 535802 806987 := bstep (se 1 (by rfl) ⟨605240, by rfl⟩ : syracuseStep 806987 = 1210481) B1210481
theorem B905303 : Blo 535802 905303 := bstep (se 1 (by rfl) ⟨678977, by rfl⟩ : syracuseStep 905303 = 1357955) B1357955
theorem B806999 : Blo 535802 806999 := bstep (se 1 (by rfl) ⟨605249, by rfl⟩ : syracuseStep 806999 = 1210499) B1210499
theorem B807065 : Blo 535802 807065 := bstep (se 2 (by rfl) ⟨302649, by rfl⟩ : syracuseStep 807065 = 605299) B605299
theorem B1364161 : Blo 535802 1364161 := bstep (se 2 (by rfl) ⟨511560, by rfl⟩ : syracuseStep 1364161 = 1023121) B1023121
theorem B905431 : Blo 535802 905431 := bstep (se 1 (by rfl) ⟨679073, by rfl⟩ : syracuseStep 905431 = 1358147) B1358147
theorem B807179 : Blo 535802 807179 := bstep (se 1 (by rfl) ⟨605384, by rfl⟩ : syracuseStep 807179 = 1210769) B1210769
theorem B807191 : Blo 535802 807191 := bstep (se 1 (by rfl) ⟨605393, by rfl⟩ : syracuseStep 807191 = 1210787) B1210787
theorem B3068225 : Blo 535802 3068225 := bstep (se 2 (by rfl) ⟨1150584, by rfl⟩ : syracuseStep 3068225 = 2301169) B2301169
theorem B807257 : Blo 535802 807257 := bstep (se 2 (by rfl) ⟨302721, by rfl⟩ : syracuseStep 807257 = 605443) B605443
theorem B807371 : Blo 535802 807371 := bstep (se 1 (by rfl) ⟨605528, by rfl⟩ : syracuseStep 807371 = 1211057) B1211057
theorem B807383 : Blo 535802 807383 := bstep (se 1 (by rfl) ⟨605537, by rfl⟩ : syracuseStep 807383 = 1211075) B1211075
theorem B12440081 : Blo 535802 12440081 := bstep (se 2 (by rfl) ⟨4665030, by rfl⟩ : syracuseStep 12440081 = 9330061) B9330061
theorem B807449 : Blo 535802 807449 := bstep (se 2 (by rfl) ⟨302793, by rfl⟩ : syracuseStep 807449 = 605587) B605587
theorem B807563 : Blo 535802 807563 := bstep (se 1 (by rfl) ⟨605672, by rfl⟩ : syracuseStep 807563 = 1211345) B1211345
theorem B807575 : Blo 535802 807575 := bstep (se 1 (by rfl) ⟨605681, by rfl⟩ : syracuseStep 807575 = 1211363) B1211363
theorem B807641 : Blo 535802 807641 := bstep (se 2 (by rfl) ⟨302865, by rfl⟩ : syracuseStep 807641 = 605731) B605731
theorem B1364759 : Blo 535802 1364759 := bstep (se 1 (by rfl) ⟨1023569, by rfl⟩ : syracuseStep 1364759 = 2047139) B2047139
theorem B2511667 : Blo 535802 2511667 := bstep (se 1 (by rfl) ⟨1883750, by rfl⟩ : syracuseStep 2511667 = 3767501) B3767501
theorem B906059 : Blo 535802 906059 := bstep (se 1 (by rfl) ⟨679544, by rfl⟩ : syracuseStep 906059 = 1359089) B1359089
theorem B807755 : Blo 535802 807755 := bstep (se 1 (by rfl) ⟨605816, by rfl⟩ : syracuseStep 807755 = 1211633) B1211633
theorem B807767 : Blo 535802 807767 := bstep (se 1 (by rfl) ⟨605825, by rfl⟩ : syracuseStep 807767 = 1211651) B1211651
theorem B4608899 : Blo 535802 4608899 := bstep (se 1 (by rfl) ⟨3456674, by rfl⟩ : syracuseStep 4608899 = 6913349) B6913349
theorem B807833 : Blo 535802 807833 := bstep (se 2 (by rfl) ⟨302937, by rfl⟩ : syracuseStep 807833 = 605875) B605875
theorem B906187 : Blo 535802 906187 := bstep (se 1 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 906187 = 1359281) B1359281
theorem B807947 : Blo 535802 807947 := bstep (se 1 (by rfl) ⟨605960, by rfl⟩ : syracuseStep 807947 = 1211921) B1211921
theorem B807959 : Blo 535802 807959 := bstep (se 1 (by rfl) ⟨605969, by rfl⟩ : syracuseStep 807959 = 1211939) B1211939
theorem B906329 : Blo 535802 906329 := bstep (se 2 (by rfl) ⟨339873, by rfl⟩ : syracuseStep 906329 = 679747) B679747
theorem B808025 : Blo 535802 808025 := bstep (se 2 (by rfl) ⟨303009, by rfl⟩ : syracuseStep 808025 = 606019) B606019
theorem B5166173 : Blo 535802 5166173 := bstep (se 3 (by rfl) ⟨968657, by rfl⟩ : syracuseStep 5166173 = 1937315) B1937315
theorem B4084829 : Blo 535802 4084829 := bstep (se 3 (by rfl) ⟨765905, by rfl⟩ : syracuseStep 4084829 = 1531811) B1531811
theorem B1725533 : Blo 535802 1725533 := bstep (se 3 (by rfl) ⟨323537, by rfl⟩ : syracuseStep 1725533 = 647075) B647075
theorem B611479 : Blo 535802 611479 := bstep (se 1 (by rfl) ⟨458609, by rfl⟩ : syracuseStep 611479 = 917219) B917219
theorem B808139 : Blo 535802 808139 := bstep (se 1 (by rfl) ⟨606104, by rfl⟩ : syracuseStep 808139 = 1212209) B1212209
theorem B808151 : Blo 535802 808151 := bstep (se 1 (by rfl) ⟨606113, by rfl⟩ : syracuseStep 808151 = 1212227) B1212227
theorem B906457 : Blo 535802 906457 := bstep (se 2 (by rfl) ⟨339921, by rfl⟩ : syracuseStep 906457 = 679843) B679843
theorem B808217 : Blo 535802 808217 := bstep (se 2 (by rfl) ⟨303081, by rfl⟩ : syracuseStep 808217 = 606163) B606163
theorem B546103 : Blo 535802 546103 := bstep (se 1 (by rfl) ⟨409577, by rfl⟩ : syracuseStep 546103 = 819155) B819155
theorem B808331 : Blo 535802 808331 := bstep (se 1 (by rfl) ⟨606248, by rfl⟩ : syracuseStep 808331 = 1212497) B1212497
theorem B808343 : Blo 535802 808343 := bstep (se 1 (by rfl) ⟨606257, by rfl⟩ : syracuseStep 808343 = 1212515) B1212515
theorem B808409 : Blo 535802 808409 := bstep (se 2 (by rfl) ⟨303153, by rfl⟩ : syracuseStep 808409 = 606307) B606307
theorem B1365569 : Blo 535802 1365569 := bstep (se 2 (by rfl) ⟨512088, by rfl⟩ : syracuseStep 1365569 = 1024177) B1024177
theorem B808523 : Blo 535802 808523 := bstep (se 1 (by rfl) ⟨606392, by rfl⟩ : syracuseStep 808523 = 1212785) B1212785
theorem B808535 : Blo 535802 808535 := bstep (se 1 (by rfl) ⟨606401, by rfl⟩ : syracuseStep 808535 = 1212803) B1212803
theorem B2578013 : Blo 535802 2578013 := bstep (se 3 (by rfl) ⟨483377, by rfl⟩ : syracuseStep 2578013 = 966755) B966755
theorem B808601 : Blo 535802 808601 := bstep (se 2 (by rfl) ⟨303225, by rfl⟩ : syracuseStep 808601 = 606451) B606451
theorem B808715 : Blo 535802 808715 := bstep (se 1 (by rfl) ⟨606536, by rfl⟩ : syracuseStep 808715 = 1213073) B1213073
theorem B907031 : Blo 535802 907031 := bstep (se 1 (by rfl) ⟨680273, by rfl⟩ : syracuseStep 907031 = 1360547) B1360547
theorem B808727 : Blo 535802 808727 := bstep (se 1 (by rfl) ⟨606545, by rfl⟩ : syracuseStep 808727 = 1213091) B1213091
theorem B3888931 : Blo 535802 3888931 := bstep (se 1 (by rfl) ⟨2916698, by rfl⟩ : syracuseStep 3888931 = 5833397) B5833397
theorem B808793 : Blo 535802 808793 := bstep (se 2 (by rfl) ⟨303297, by rfl⟩ : syracuseStep 808793 = 606595) B606595
theorem B907159 : Blo 535802 907159 := bstep (se 1 (by rfl) ⟨680369, by rfl⟩ : syracuseStep 907159 = 1360739) B1360739
theorem B808907 : Blo 535802 808907 := bstep (se 1 (by rfl) ⟨606680, by rfl⟩ : syracuseStep 808907 = 1213361) B1213361
theorem B808919 : Blo 535802 808919 := bstep (se 1 (by rfl) ⟨606689, by rfl⟩ : syracuseStep 808919 = 1213379) B1213379
theorem B808985 : Blo 535802 808985 := bstep (se 2 (by rfl) ⟨303369, by rfl⟩ : syracuseStep 808985 = 606739) B606739
theorem B1529921 : Blo 535802 1529921 := bstep (se 2 (by rfl) ⟨573720, by rfl⟩ : syracuseStep 1529921 = 1147441) B1147441
theorem B1366105 : Blo 535802 1366105 := bstep (se 2 (by rfl) ⟨512289, by rfl⟩ : syracuseStep 1366105 = 1024579) B1024579
theorem B809099 : Blo 535802 809099 := bstep (se 1 (by rfl) ⟨606824, by rfl⟩ : syracuseStep 809099 = 1213649) B1213649
theorem B809111 : Blo 535802 809111 := bstep (se 1 (by rfl) ⟨606833, by rfl⟩ : syracuseStep 809111 = 1213667) B1213667
theorem B1530035 : Blo 535802 1530035 := bstep (se 1 (by rfl) ⟨1147526, by rfl⟩ : syracuseStep 1530035 = 2295053) B2295053
theorem B1038529 : Blo 535802 1038529 := bstep (se 2 (by rfl) ⟨389448, by rfl⟩ : syracuseStep 1038529 = 778897) B778897
theorem B809177 : Blo 535802 809177 := bstep (se 2 (by rfl) ⟨303441, by rfl⟩ : syracuseStep 809177 = 606883) B606883
theorem B5822765 : Blo 535802 5822765 := bstep (se 3 (by rfl) ⟨1091768, by rfl⟩ : syracuseStep 5822765 = 2183537) B2183537
theorem B809291 : Blo 535802 809291 := bstep (se 1 (by rfl) ⟨606968, by rfl⟩ : syracuseStep 809291 = 1213937) B1213937
theorem B809303 : Blo 535802 809303 := bstep (se 1 (by rfl) ⟨606977, by rfl⟩ : syracuseStep 809303 = 1213955) B1213955
theorem B809369 : Blo 535802 809369 := bstep (se 2 (by rfl) ⟨303513, by rfl⟩ : syracuseStep 809369 = 607027) B607027
theorem B907787 : Blo 535802 907787 := bstep (se 1 (by rfl) ⟨680840, by rfl⟩ : syracuseStep 907787 = 1361681) B1361681
theorem B809483 : Blo 535802 809483 := bstep (se 1 (by rfl) ⟨607112, by rfl⟩ : syracuseStep 809483 = 1214225) B1214225
theorem B809495 : Blo 535802 809495 := bstep (se 1 (by rfl) ⟨607121, by rfl⟩ : syracuseStep 809495 = 1214243) B1214243
theorem B809561 : Blo 535802 809561 := bstep (se 2 (by rfl) ⟨303585, by rfl⟩ : syracuseStep 809561 = 607171) B607171
theorem B907915 : Blo 535802 907915 := bstep (se 1 (by rfl) ⟨680936, by rfl⟩ : syracuseStep 907915 = 1361873) B1361873
theorem B809675 : Blo 535802 809675 := bstep (se 1 (by rfl) ⟨607256, by rfl⟩ : syracuseStep 809675 = 1214513) B1214513
theorem B809687 : Blo 535802 809687 := bstep (se 1 (by rfl) ⟨607265, by rfl⟩ : syracuseStep 809687 = 1214531) B1214531
theorem B908057 : Blo 535802 908057 := bstep (se 2 (by rfl) ⟨340521, by rfl⟩ : syracuseStep 908057 = 681043) B681043
theorem B2907011 : Blo 535802 2907011 := bstep (se 1 (by rfl) ⟨2180258, by rfl⟩ : syracuseStep 2907011 = 4360517) B4360517
theorem B908185 : Blo 535802 908185 := bstep (se 2 (by rfl) ⟨340569, by rfl⟩ : syracuseStep 908185 = 681139) B681139
theorem B678871 : Blo 535802 678871 := bstep (se 1 (by rfl) ⟨509153, by rfl⟩ : syracuseStep 678871 = 1018307) B1018307
theorem B4611289 : Blo 535802 4611289 := bstep (se 2 (by rfl) ⟨1729233, by rfl⟩ : syracuseStep 4611289 = 3458467) B3458467
theorem B908759 : Blo 535802 908759 := bstep (se 1 (by rfl) ⟨681569, by rfl⟩ : syracuseStep 908759 = 1363139) B1363139
theorem B908887 : Blo 535802 908887 := bstep (se 1 (by rfl) ⟨681665, by rfl⟩ : syracuseStep 908887 = 1363331) B1363331
theorem B679691 : Blo 535802 679691 := bstep (se 1 (by rfl) ⟨509768, by rfl⟩ : syracuseStep 679691 = 1019537) B1019537
theorem B6873011 : Blo 535802 6873011 := bstep (se 1 (by rfl) ⟨5154758, by rfl⟩ : syracuseStep 6873011 = 10309517) B10309517
theorem B909515 : Blo 535802 909515 := bstep (se 1 (by rfl) ⟨682136, by rfl⟩ : syracuseStep 909515 = 1364273) B1364273
theorem B2580781 : Blo 535802 2580781 := bstep (se 3 (by rfl) ⟨483896, by rfl⟩ : syracuseStep 2580781 = 967793) B967793
theorem B909643 : Blo 535802 909643 := bstep (se 1 (by rfl) ⟨682232, by rfl⟩ : syracuseStep 909643 = 1364465) B1364465
theorem B680395 : Blo 535802 680395 := bstep (se 1 (by rfl) ⟨510296, by rfl⟩ : syracuseStep 680395 = 1020593) B1020593
theorem B909785 : Blo 535802 909785 := bstep (se 2 (by rfl) ⟨341169, by rfl⟩ : syracuseStep 909785 = 682339) B682339
theorem B909913 : Blo 535802 909913 := bstep (se 2 (by rfl) ⟨341217, by rfl⟩ : syracuseStep 909913 = 682435) B682435
theorem B680663 : Blo 535802 680663 := bstep (se 1 (by rfl) ⟨510497, by rfl⟩ : syracuseStep 680663 = 1020995) B1020995
theorem B2581379 : Blo 535802 2581379 := bstep (se 1 (by rfl) ⟨1936034, by rfl⟩ : syracuseStep 2581379 = 3872069) B3872069
theorem B1532951 : Blo 535802 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B3073099 : Blo 535802 3073099 := bstep (se 1 (by rfl) ⟨2304824, by rfl⟩ : syracuseStep 3073099 = 4609649) B4609649
theorem B910487 : Blo 535802 910487 := bstep (se 1 (by rfl) ⟨682865, by rfl⟩ : syracuseStep 910487 = 1365731) B1365731
theorem B648343 : Blo 535802 648343 := bstep (se 1 (by rfl) ⟨486257, by rfl⟩ : syracuseStep 648343 = 972515) B972515
theorem B910615 : Blo 535802 910615 := bstep (se 1 (by rfl) ⟨682961, by rfl⟩ : syracuseStep 910615 = 1365923) B1365923
theorem B3073373 : Blo 535802 3073373 := bstep (se 3 (by rfl) ⟨576257, by rfl⟩ : syracuseStep 3073373 = 1152515) B1152515
theorem B681367 : Blo 535802 681367 := bstep (se 1 (by rfl) ⟨511025, by rfl⟩ : syracuseStep 681367 = 1022051) B1022051
theorem B1205657 : Blo 535802 1205657 := bstep (se 2 (by rfl) ⟨452121, by rfl⟩ : syracuseStep 1205657 = 904243) B904243
theorem B1205747 : Blo 535802 1205747 := bstep (se 1 (by rfl) ⟨904310, by rfl⟩ : syracuseStep 1205747 = 1808621) B1808621
theorem B1205783 : Blo 535802 1205783 := bstep (se 1 (by rfl) ⟨904337, by rfl⟩ : syracuseStep 1205783 = 1808675) B1808675
theorem B1205963 : Blo 535802 1205963 := bstep (se 1 (by rfl) ⟨904472, by rfl⟩ : syracuseStep 1205963 = 1808945) B1808945
theorem B1206017 : Blo 535802 1206017 := bstep (se 2 (by rfl) ⟨452256, by rfl⟩ : syracuseStep 1206017 = 904513) B904513
theorem B1206233 : Blo 535802 1206233 := bstep (se 2 (by rfl) ⟨452337, by rfl⟩ : syracuseStep 1206233 = 904675) B904675
theorem B1206323 : Blo 535802 1206323 := bstep (se 1 (by rfl) ⟨904742, by rfl⟩ : syracuseStep 1206323 = 1809485) B1809485
theorem B1206359 : Blo 535802 1206359 := bstep (se 1 (by rfl) ⟨904769, by rfl⟩ : syracuseStep 1206359 = 1809539) B1809539
theorem B1206539 : Blo 535802 1206539 := bstep (se 1 (by rfl) ⟨904904, by rfl⟩ : syracuseStep 1206539 = 1809809) B1809809
theorem B1206593 : Blo 535802 1206593 := bstep (se 2 (by rfl) ⟨452472, by rfl⟩ : syracuseStep 1206593 = 904945) B904945
theorem B1206809 : Blo 535802 1206809 := bstep (se 2 (by rfl) ⟨452553, by rfl⟩ : syracuseStep 1206809 = 905107) B905107
theorem B1206899 : Blo 535802 1206899 := bstep (se 1 (by rfl) ⟨905174, by rfl⟩ : syracuseStep 1206899 = 1810349) B1810349
theorem B1206935 : Blo 535802 1206935 := bstep (se 1 (by rfl) ⟨905201, by rfl⟩ : syracuseStep 1206935 = 1810403) B1810403
theorem B1207115 : Blo 535802 1207115 := bstep (se 1 (by rfl) ⟨905336, by rfl⟩ : syracuseStep 1207115 = 1810673) B1810673
theorem B1207169 : Blo 535802 1207169 := bstep (se 2 (by rfl) ⟨452688, by rfl⟩ : syracuseStep 1207169 = 905377) B905377
theorem B4713547 : Blo 535802 4713547 := bstep (se 1 (by rfl) ⟨3535160, by rfl⟩ : syracuseStep 4713547 = 7070321) B7070321
theorem B683083 : Blo 535802 683083 := bstep (se 1 (by rfl) ⟨512312, by rfl⟩ : syracuseStep 683083 = 1024625) B1024625
theorem B1207385 : Blo 535802 1207385 := bstep (se 2 (by rfl) ⟨452769, by rfl⟩ : syracuseStep 1207385 = 905539) B905539
theorem B1207475 : Blo 535802 1207475 := bstep (se 1 (by rfl) ⟨905606, by rfl⟩ : syracuseStep 1207475 = 1811213) B1811213
theorem B1207511 : Blo 535802 1207511 := bstep (se 1 (by rfl) ⟨905633, by rfl⟩ : syracuseStep 1207511 = 1811267) B1811267
theorem B2321729 : Blo 535802 2321729 := bstep (se 2 (by rfl) ⟨870648, by rfl⟩ : syracuseStep 2321729 = 1741297) B1741297
theorem B7761253 : Blo 535802 7761253 := bstep (se 4 (by rfl) ⟨727617, by rfl⟩ : syracuseStep 7761253 = 1455235) B1455235
theorem B1207691 : Blo 535802 1207691 := bstep (se 1 (by rfl) ⟨905768, by rfl⟩ : syracuseStep 1207691 = 1811537) B1811537
theorem B1535411 : Blo 535802 1535411 := bstep (se 1 (by rfl) ⟨1151558, by rfl⟩ : syracuseStep 1535411 = 2303117) B2303117
theorem B1207745 : Blo 535802 1207745 := bstep (se 2 (by rfl) ⟨452904, by rfl⟩ : syracuseStep 1207745 = 905809) B905809
theorem B1207961 : Blo 535802 1207961 := bstep (se 2 (by rfl) ⟨452985, by rfl⟩ : syracuseStep 1207961 = 905971) B905971
theorem B1208051 : Blo 535802 1208051 := bstep (se 1 (by rfl) ⟨906038, by rfl⟩ : syracuseStep 1208051 = 1812077) B1812077
theorem B1208087 : Blo 535802 1208087 := bstep (se 1 (by rfl) ⟨906065, by rfl⟩ : syracuseStep 1208087 = 1812131) B1812131
theorem B1208267 : Blo 535802 1208267 := bstep (se 1 (by rfl) ⟨906200, by rfl⟩ : syracuseStep 1208267 = 1812401) B1812401
theorem B1208321 : Blo 535802 1208321 := bstep (se 2 (by rfl) ⟨453120, by rfl⟩ : syracuseStep 1208321 = 906241) B906241
theorem B11006027 : Blo 535802 11006027 := bstep (se 1 (by rfl) ⟨8254520, by rfl⟩ : syracuseStep 11006027 = 16509041) B16509041
theorem B4911205 : Blo 535802 4911205 := bstep (se 4 (by rfl) ⟨460425, by rfl⟩ : syracuseStep 4911205 = 920851) B920851
theorem B4124803 : Blo 535802 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B1208537 : Blo 535802 1208537 := bstep (se 2 (by rfl) ⟨453201, by rfl⟩ : syracuseStep 1208537 = 906403) B906403
theorem B1208627 : Blo 535802 1208627 := bstep (se 1 (by rfl) ⟨906470, by rfl⟩ : syracuseStep 1208627 = 1812941) B1812941
theorem B2289995 : Blo 535802 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B1208663 : Blo 535802 1208663 := bstep (se 1 (by rfl) ⟨906497, by rfl⟩ : syracuseStep 1208663 = 1812995) B1812995
theorem B1208843 : Blo 535802 1208843 := bstep (se 1 (by rfl) ⟨906632, by rfl⟩ : syracuseStep 1208843 = 1813265) B1813265
theorem B1208897 : Blo 535802 1208897 := bstep (se 2 (by rfl) ⟨453336, by rfl⟩ : syracuseStep 1208897 = 906673) B906673
theorem B2716253 : Blo 535802 2716253 := bstep (se 3 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 2716253 = 1018595) B1018595
theorem B1209113 : Blo 535802 1209113 := bstep (se 2 (by rfl) ⟨453417, by rfl⟩ : syracuseStep 1209113 = 906835) B906835
theorem B1307443 : Blo 535802 1307443 := bstep (se 1 (by rfl) ⟨980582, by rfl⟩ : syracuseStep 1307443 = 1961165) B1961165
theorem B1209203 : Blo 535802 1209203 := bstep (se 1 (by rfl) ⟨906902, by rfl⟩ : syracuseStep 1209203 = 1813805) B1813805
theorem B1209239 : Blo 535802 1209239 := bstep (se 1 (by rfl) ⟨906929, by rfl⟩ : syracuseStep 1209239 = 1813859) B1813859
theorem B1209419 : Blo 535802 1209419 := bstep (se 1 (by rfl) ⟨907064, by rfl⟩ : syracuseStep 1209419 = 1814129) B1814129
theorem B2290781 : Blo 535802 2290781 := bstep (se 3 (by rfl) ⟨429521, by rfl⟩ : syracuseStep 2290781 = 859043) B859043
theorem B1209473 : Blo 535802 1209473 := bstep (se 2 (by rfl) ⟨453552, by rfl⟩ : syracuseStep 1209473 = 907105) B907105
theorem B1209689 : Blo 535802 1209689 := bstep (se 2 (by rfl) ⟨453633, by rfl⟩ : syracuseStep 1209689 = 907267) B907267
theorem B1209779 : Blo 535802 1209779 := bstep (se 1 (by rfl) ⟨907334, by rfl⟩ : syracuseStep 1209779 = 1814669) B1814669
theorem B1209815 : Blo 535802 1209815 := bstep (se 1 (by rfl) ⟨907361, by rfl⟩ : syracuseStep 1209815 = 1814723) B1814723
theorem B1209995 : Blo 535802 1209995 := bstep (se 1 (by rfl) ⟨907496, by rfl⟩ : syracuseStep 1209995 = 1814993) B1814993
theorem B1210049 : Blo 535802 1210049 := bstep (se 2 (by rfl) ⟨453768, by rfl⟩ : syracuseStep 1210049 = 907537) B907537
theorem B1210265 : Blo 535802 1210265 := bstep (se 2 (by rfl) ⟨453849, by rfl⟩ : syracuseStep 1210265 = 907699) B907699
theorem B1144793 : Blo 535802 1144793 := bstep (se 2 (by rfl) ⟨429297, by rfl⟩ : syracuseStep 1144793 = 858595) B858595
theorem B1210355 : Blo 535802 1210355 := bstep (se 1 (by rfl) ⟨907766, by rfl⟩ : syracuseStep 1210355 = 1815533) B1815533
theorem B1210391 : Blo 535802 1210391 := bstep (se 1 (by rfl) ⟨907793, by rfl⟩ : syracuseStep 1210391 = 1815587) B1815587
theorem B1833025 : Blo 535802 1833025 := bstep (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) B1374769
theorem B1210571 : Blo 535802 1210571 := bstep (se 1 (by rfl) ⟨907928, by rfl⟩ : syracuseStep 1210571 = 1815857) B1815857
theorem B1210625 : Blo 535802 1210625 := bstep (se 2 (by rfl) ⟨453984, by rfl⟩ : syracuseStep 1210625 = 907969) B907969
theorem B2750851 : Blo 535802 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B2292113 : Blo 535802 2292113 := bstep (se 2 (by rfl) ⟨859542, by rfl⟩ : syracuseStep 2292113 = 1719085) B1719085
theorem B817561 : Blo 535802 817561 := bstep (se 2 (by rfl) ⟨306585, by rfl⟩ : syracuseStep 817561 = 613171) B613171
theorem B1210841 : Blo 535802 1210841 := bstep (se 2 (by rfl) ⟨454065, by rfl⟩ : syracuseStep 1210841 = 908131) B908131
theorem B1931779 : Blo 535802 1931779 := bstep (se 1 (by rfl) ⟨1448834, by rfl⟩ : syracuseStep 1931779 = 2897669) B2897669
theorem B4356625 : Blo 535802 4356625 := bstep (se 2 (by rfl) ⟨1633734, by rfl⟩ : syracuseStep 4356625 = 3267469) B3267469
theorem B1210931 : Blo 535802 1210931 := bstep (se 1 (by rfl) ⟨908198, by rfl⟩ : syracuseStep 1210931 = 1816397) B1816397
theorem B1210967 : Blo 535802 1210967 := bstep (se 1 (by rfl) ⟨908225, by rfl⟩ : syracuseStep 1210967 = 1816451) B1816451
theorem B883289 : Blo 535802 883289 := bstep (se 2 (by rfl) ⟨331233, by rfl⟩ : syracuseStep 883289 = 662467) B662467
theorem B2718359 : Blo 535802 2718359 := bstep (se 1 (by rfl) ⟨2038769, by rfl⟩ : syracuseStep 2718359 = 4077539) B4077539
theorem B1211147 : Blo 535802 1211147 := bstep (se 1 (by rfl) ⟨908360, by rfl⟩ : syracuseStep 1211147 = 1816721) B1816721
theorem B1211201 : Blo 535802 1211201 := bstep (se 2 (by rfl) ⟨454200, by rfl⟩ : syracuseStep 1211201 = 908401) B908401
theorem B6126515 : Blo 535802 6126515 := bstep (se 1 (by rfl) ⟨4594886, by rfl⟩ : syracuseStep 6126515 = 9189773) B9189773
theorem B1211417 : Blo 535802 1211417 := bstep (se 2 (by rfl) ⟨454281, by rfl⟩ : syracuseStep 1211417 = 908563) B908563
theorem B1211507 : Blo 535802 1211507 := bstep (se 1 (by rfl) ⟨908630, by rfl⟩ : syracuseStep 1211507 = 1817261) B1817261
theorem B3865751 : Blo 535802 3865751 := bstep (se 1 (by rfl) ⟨2899313, by rfl⟩ : syracuseStep 3865751 = 5798627) B5798627
theorem B1211543 : Blo 535802 1211543 := bstep (se 1 (by rfl) ⟨908657, by rfl⟩ : syracuseStep 1211543 = 1817315) B1817315
theorem B1211723 : Blo 535802 1211723 := bstep (se 1 (by rfl) ⟨908792, by rfl⟩ : syracuseStep 1211723 = 1817585) B1817585
theorem B1211777 : Blo 535802 1211777 := bstep (se 2 (by rfl) ⟨454416, by rfl⟩ : syracuseStep 1211777 = 908833) B908833
theorem B1932761 : Blo 535802 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B1146433 : Blo 535802 1146433 := bstep (se 2 (by rfl) ⟨429912, by rfl⟩ : syracuseStep 1146433 = 859825) B859825
theorem B1211993 : Blo 535802 1211993 := bstep (se 2 (by rfl) ⟨454497, by rfl⟩ : syracuseStep 1211993 = 908995) B908995
theorem B2293379 : Blo 535802 2293379 := bstep (se 1 (by rfl) ⟨1720034, by rfl⟩ : syracuseStep 2293379 = 3440069) B3440069
theorem B1212083 : Blo 535802 1212083 := bstep (se 1 (by rfl) ⟨909062, by rfl⟩ : syracuseStep 1212083 = 1818125) B1818125
theorem B1212119 : Blo 535802 1212119 := bstep (se 1 (by rfl) ⟨909089, by rfl⟩ : syracuseStep 1212119 = 1818179) B1818179
theorem B1212299 : Blo 535802 1212299 := bstep (se 1 (by rfl) ⟨909224, by rfl⟩ : syracuseStep 1212299 = 1818449) B1818449
theorem B1212353 : Blo 535802 1212353 := bstep (se 2 (by rfl) ⟨454632, by rfl⟩ : syracuseStep 1212353 = 909265) B909265
theorem B1835095 : Blo 535802 1835095 := bstep (se 1 (by rfl) ⟨1376321, by rfl⟩ : syracuseStep 1835095 = 2752643) B2752643
theorem B1212551 : Blo 535802 1212551 := bstep (se 1 (by rfl) ⟨909413, by rfl⟩ : syracuseStep 1212551 = 1818827) B1818827
theorem B1212731 : Blo 535802 1212731 := bstep (se 1 (by rfl) ⟨909548, by rfl⟩ : syracuseStep 1212731 = 1819097) B1819097
theorem B3441041 : Blo 535802 3441041 := bstep (se 2 (by rfl) ⟨1290390, by rfl⟩ : syracuseStep 3441041 = 2580781) B2580781
theorem B1147321 : Blo 535802 1147321 := bstep (se 2 (by rfl) ⟨430245, by rfl⟩ : syracuseStep 1147321 = 860491) B860491
theorem B1212857 : Blo 535802 1212857 := bstep (se 2 (by rfl) ⟨454821, by rfl⟩ : syracuseStep 1212857 = 909643) B909643
theorem B1213199 : Blo 535802 1213199 := bstep (se 1 (by rfl) ⟨909899, by rfl⟩ : syracuseStep 1213199 = 1819799) B1819799
theorem B1213217 : Blo 535802 1213217 := bstep (se 2 (by rfl) ⟨454956, by rfl⟩ : syracuseStep 1213217 = 909913) B909913
theorem B2589529 : Blo 535802 2589529 := bstep (se 2 (by rfl) ⟨971073, by rfl⟩ : syracuseStep 2589529 = 1942147) B1942147
theorem B2720627 : Blo 535802 2720627 := bstep (se 1 (by rfl) ⟨2040470, by rfl⟩ : syracuseStep 2720627 = 4080941) B4080941
theorem B1147783 : Blo 535802 1147783 := bstep (se 1 (by rfl) ⟨860837, by rfl⟩ : syracuseStep 1147783 = 1721675) B1721675
theorem B820103 : Blo 535802 820103 := bstep (se 1 (by rfl) ⟨615077, by rfl⟩ : syracuseStep 820103 = 1230155) B1230155
theorem B3277835 : Blo 535802 3277835 := bstep (se 1 (by rfl) ⟨2458376, by rfl⟩ : syracuseStep 3277835 = 4916753) B4916753
theorem B1213559 : Blo 535802 1213559 := bstep (se 1 (by rfl) ⟨910169, by rfl⟩ : syracuseStep 1213559 = 1820339) B1820339
theorem B1213739 : Blo 535802 1213739 := bstep (se 1 (by rfl) ⟨910304, by rfl⟩ : syracuseStep 1213739 = 1820609) B1820609
theorem B2721113 : Blo 535802 2721113 := bstep (se 2 (by rfl) ⟨1020417, by rfl⟩ : syracuseStep 2721113 = 2040835) B2040835
theorem B2295155 : Blo 535802 2295155 := bstep (se 1 (by rfl) ⟨1721366, by rfl⟩ : syracuseStep 2295155 = 3442733) B3442733
theorem B1639865 : Blo 535802 1639865 := bstep (se 2 (by rfl) ⟨614949, by rfl⟩ : syracuseStep 1639865 = 1229899) B1229899
theorem B4097465 : Blo 535802 4097465 := bstep (se 2 (by rfl) ⟨1536549, by rfl⟩ : syracuseStep 4097465 = 3073099) B3073099
theorem B1017289 : Blo 535802 1017289 := bstep (se 2 (by rfl) ⟨381483, by rfl⟩ : syracuseStep 1017289 = 762967) B762967
theorem B1214099 : Blo 535802 1214099 := bstep (se 1 (by rfl) ⟨910574, by rfl⟩ : syracuseStep 1214099 = 1821149) B1821149
theorem B1214153 : Blo 535802 1214153 := bstep (se 2 (by rfl) ⟨455307, by rfl⟩ : syracuseStep 1214153 = 910615) B910615
theorem B4196069 : Blo 535802 4196069 := bstep (se 4 (by rfl) ⟨393381, by rfl⟩ : syracuseStep 4196069 = 786763) B786763
theorem B1018003 : Blo 535802 1018003 := bstep (se 1 (by rfl) ⟨763502, by rfl⟩ : syracuseStep 1018003 = 1527005) B1527005
theorem B11634961 : Blo 535802 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B5507459 : Blo 535802 5507459 := bstep (se 1 (by rfl) ⟨4130594, by rfl⟩ : syracuseStep 5507459 = 8261189) B8261189
theorem B11045443 : Blo 535802 11045443 := bstep (se 1 (by rfl) ⟨8284082, by rfl⟩ : syracuseStep 11045443 = 16568165) B16568165
theorem B3869441 : Blo 535802 3869441 := bstep (se 2 (by rfl) ⟨1451040, by rfl⟩ : syracuseStep 3869441 = 2902081) B2902081
theorem B1837939 : Blo 535802 1837939 := bstep (se 1 (by rfl) ⟨1378454, by rfl⟩ : syracuseStep 1837939 = 2756909) B2756909
theorem B8293387 : Blo 535802 8293387 := bstep (se 1 (by rfl) ⟨6220040, by rfl⟩ : syracuseStep 8293387 = 12440081) B12440081
theorem B4918283 : Blo 535802 4918283 := bstep (se 1 (by rfl) ⟨3688712, by rfl⟩ : syracuseStep 4918283 = 7377425) B7377425
theorem B1019081 : Blo 535802 1019081 := bstep (se 2 (by rfl) ⟨382155, by rfl⟩ : syracuseStep 1019081 = 764311) B764311
theorem B6130889 : Blo 535802 6130889 := bstep (se 2 (by rfl) ⟨2299083, by rfl⟩ : syracuseStep 6130889 = 4598167) B4598167
theorem B2297069 : Blo 535802 2297069 := bstep (se 3 (by rfl) ⟨430700, by rfl⟩ : syracuseStep 2297069 = 861401) B861401
theorem B2035003 : Blo 535802 2035003 := bstep (se 1 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 2035003 = 3052505) B3052505
theorem B3444115 : Blo 535802 3444115 := bstep (se 1 (by rfl) ⟨2583086, by rfl⟩ : syracuseStep 3444115 = 5166173) B5166173
theorem B2723219 : Blo 535802 2723219 := bstep (se 1 (by rfl) ⟨2042414, by rfl⟩ : syracuseStep 2723219 = 4084829) B4084829
theorem B1150355 : Blo 535802 1150355 := bstep (se 1 (by rfl) ⟨862766, by rfl⟩ : syracuseStep 1150355 = 1725533) B1725533
theorem B2035489 : Blo 535802 2035489 := bstep (se 2 (by rfl) ⟨763308, by rfl⟩ : syracuseStep 2035489 = 1526617) B1526617
theorem B2297753 : Blo 535802 2297753 := bstep (se 2 (by rfl) ⟨861657, by rfl⟩ : syracuseStep 2297753 = 1723315) B1723315
theorem B2101277 : Blo 535802 2101277 := bstep (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) B787979
theorem B1019947 : Blo 535802 1019947 := bstep (se 1 (by rfl) ⟨764960, by rfl⟩ : syracuseStep 1019947 = 1529921) B1529921
theorem B1020023 : Blo 535802 1020023 := bstep (se 1 (by rfl) ⟨765017, by rfl⟩ : syracuseStep 1020023 = 1530035) B1530035
theorem B2298127 : Blo 535802 2298127 := bstep (se 1 (by rfl) ⟨1723595, by rfl⟩ : syracuseStep 2298127 = 3447191) B3447191
theorem B4657441 : Blo 535802 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B725321 : Blo 535802 725321 := bstep (se 2 (by rfl) ⟨271995, by rfl⟩ : syracuseStep 725321 = 543991) B543991
theorem B1938007 : Blo 535802 1938007 := bstep (se 1 (by rfl) ⟨1453505, by rfl⟩ : syracuseStep 1938007 = 2907011) B2907011
theorem B2036461 : Blo 535802 2036461 := bstep (se 3 (by rfl) ⟨381836, by rfl⟩ : syracuseStep 2036461 = 763673) B763673
theorem B2036765 : Blo 535802 2036765 := bstep (se 3 (by rfl) ⟨381893, by rfl⟩ : syracuseStep 2036765 = 763787) B763787
theorem B3872323 : Blo 535802 3872323 := bstep (se 1 (by rfl) ⟨2904242, by rfl⟩ : syracuseStep 3872323 = 5808485) B5808485
theorem B1021967 : Blo 535802 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B6133805 : Blo 535802 6133805 := bstep (se 3 (by rfl) ⟨1150088, by rfl⟩ : syracuseStep 6133805 = 2300177) B2300177
theorem B6559805 : Blo 535802 6559805 := bstep (se 3 (by rfl) ⟨1229963, by rfl⟩ : syracuseStep 6559805 = 2459927) B2459927
theorem B3479867 : Blo 535802 3479867 := bstep (se 1 (by rfl) ⟨2609900, by rfl⟩ : syracuseStep 3479867 = 5219801) B5219801
theorem B4594067 : Blo 535802 4594067 := bstep (se 1 (by rfl) ⟨3445550, by rfl⟩ : syracuseStep 4594067 = 6891101) B6891101
theorem B1743257 : Blo 535802 1743257 := bstep (se 2 (by rfl) ⟨653721, by rfl⟩ : syracuseStep 1743257 = 1307443) B1307443
theorem B2726297 : Blo 535802 2726297 := bstep (se 2 (by rfl) ⟨1022361, by rfl⟩ : syracuseStep 2726297 = 2044723) B2044723
theorem B2038391 : Blo 535802 2038391 := bstep (se 1 (by rfl) ⟨1528793, by rfl⟩ : syracuseStep 2038391 = 3057587) B3057587
theorem B1383227 : Blo 535802 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B728137 : Blo 535802 728137 := bstep (se 2 (by rfl) ⟨273051, by rfl⟩ : syracuseStep 728137 = 546103) B546103
theorem B4595129 : Blo 535802 4595129 := bstep (se 2 (by rfl) ⟨1723173, by rfl⟩ : syracuseStep 4595129 = 3446347) B3446347
theorem B1547819 : Blo 535802 1547819 := bstep (se 1 (by rfl) ⟨1160864, by rfl⟩ : syracuseStep 1547819 = 2321729) B2321729
theorem B2039363 : Blo 535802 2039363 := bstep (se 1 (by rfl) ⟨1529522, by rfl⟩ : syracuseStep 2039363 = 3059045) B3059045
theorem B1023607 : Blo 535802 1023607 := bstep (se 1 (by rfl) ⟨767705, by rfl⟩ : syracuseStep 1023607 = 1535411) B1535411
theorem B5185241 : Blo 535802 5185241 := bstep (se 2 (by rfl) ⟨1944465, by rfl⟩ : syracuseStep 5185241 = 3888931) B3888931
theorem B1384705 : Blo 535802 1384705 := bstep (se 2 (by rfl) ⟨519264, by rfl⟩ : syracuseStep 1384705 = 1038529) B1038529
theorem B1810835 : Blo 535802 1810835 := bstep (se 1 (by rfl) ⟨1358126, by rfl⟩ : syracuseStep 1810835 = 2716253) B2716253
theorem B2040349 : Blo 535802 2040349 := bstep (se 3 (by rfl) ⟨382565, by rfl⟩ : syracuseStep 2040349 = 765131) B765131
theorem B1090081 : Blo 535802 1090081 := bstep (se 2 (by rfl) ⟨408780, by rfl⟩ : syracuseStep 1090081 = 817561) B817561
theorem B5808833 : Blo 535802 5808833 := bstep (se 2 (by rfl) ⟨2178312, by rfl⟩ : syracuseStep 5808833 = 4356625) B4356625
theorem B4072193 : Blo 535802 4072193 := bstep (se 2 (by rfl) ⟨1527072, by rfl⟩ : syracuseStep 4072193 = 3054145) B3054145
theorem B2728889 : Blo 535802 2728889 := bstep (se 2 (by rfl) ⟨1023333, by rfl⟩ : syracuseStep 2728889 = 2046667) B2046667
theorem B6628439 : Blo 535802 6628439 := bstep (se 1 (by rfl) ⟨4971329, by rfl⟩ : syracuseStep 6628439 = 9942659) B9942659
theorem B5154029 : Blo 535802 5154029 := bstep (se 3 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 5154029 = 1932761) B1932761
theorem B763195 : Blo 535802 763195 := bstep (se 1 (by rfl) ⟨572396, by rfl⟩ : syracuseStep 763195 = 1144793) B1144793
theorem B1812239 : Blo 535802 1812239 := bstep (se 1 (by rfl) ⟨1359179, by rfl⟩ : syracuseStep 1812239 = 2718359) B2718359
theorem B1812509 : Blo 535802 1812509 := bstep (se 3 (by rfl) ⟨339845, by rfl⟩ : syracuseStep 1812509 = 679691) B679691
theorem B2730185 : Blo 535802 2730185 := bstep (se 2 (by rfl) ⟨1023819, by rfl⟩ : syracuseStep 2730185 = 2047639) B2047639
theorem B1681817 : Blo 535802 1681817 := bstep (se 2 (by rfl) ⟨630681, by rfl⟩ : syracuseStep 1681817 = 1261363) B1261363
theorem B1943993 : Blo 535802 1943993 := bstep (se 2 (by rfl) ⟨728997, by rfl⟩ : syracuseStep 1943993 = 1457995) B1457995
theorem B1452545 : Blo 535802 1452545 := bstep (se 2 (by rfl) ⟨544704, by rfl⟩ : syracuseStep 1452545 = 1089409) B1089409
theorem B764687 : Blo 535802 764687 := bstep (se 1 (by rfl) ⟨573515, by rfl⟩ : syracuseStep 764687 = 1147031) B1147031
theorem B535815 : Blo 535802 535815 := bstep (se 1 (by rfl) ⟨401861, by rfl⟩ : syracuseStep 535815 = 803723) B803723
theorem B535823 : Blo 535802 535823 := bstep (se 1 (by rfl) ⟨401867, by rfl⟩ : syracuseStep 535823 = 803735) B803735
theorem B535867 : Blo 535802 535867 := bstep (se 1 (by rfl) ⟨401900, by rfl⟩ : syracuseStep 535867 = 803801) B803801
theorem B2043251 : Blo 535802 2043251 := bstep (se 1 (by rfl) ⟨1532438, by rfl⟩ : syracuseStep 2043251 = 3064877) B3064877
theorem B535943 : Blo 535802 535943 := bstep (se 1 (by rfl) ⟨401957, by rfl⟩ : syracuseStep 535943 = 803915) B803915
theorem B535951 : Blo 535802 535951 := bstep (se 1 (by rfl) ⟨401963, by rfl⟩ : syracuseStep 535951 = 803927) B803927
theorem B1813913 : Blo 535802 1813913 := bstep (se 2 (by rfl) ⟨680217, by rfl⟩ : syracuseStep 1813913 = 1360435) B1360435
theorem B535995 : Blo 535802 535995 := bstep (se 1 (by rfl) ⟨401996, by rfl⟩ : syracuseStep 535995 = 803993) B803993
theorem B536071 : Blo 535802 536071 := bstep (se 1 (by rfl) ⟨402053, by rfl⟩ : syracuseStep 536071 = 804107) B804107
theorem B536079 : Blo 535802 536079 := bstep (se 1 (by rfl) ⟨402059, by rfl⟩ : syracuseStep 536079 = 804119) B804119
theorem B863759 : Blo 535802 863759 := bstep (se 1 (by rfl) ⟨647819, by rfl⟩ : syracuseStep 863759 = 1295639) B1295639
theorem B536123 : Blo 535802 536123 := bstep (se 1 (by rfl) ⟨402092, by rfl⟩ : syracuseStep 536123 = 804185) B804185
theorem B6565495 : Blo 535802 6565495 := bstep (se 1 (by rfl) ⟨4924121, by rfl⟩ : syracuseStep 6565495 = 9848243) B9848243
theorem B536199 : Blo 535802 536199 := bstep (se 1 (by rfl) ⟨402149, by rfl⟩ : syracuseStep 536199 = 804299) B804299
theorem B24850061 : Blo 535802 24850061 := bstep (se 3 (by rfl) ⟨4659386, by rfl⟩ : syracuseStep 24850061 = 9318773) B9318773
theorem B536207 : Blo 535802 536207 := bstep (se 1 (by rfl) ⟨402155, by rfl⟩ : syracuseStep 536207 = 804311) B804311
theorem B536251 : Blo 535802 536251 := bstep (se 1 (by rfl) ⟨402188, by rfl⟩ : syracuseStep 536251 = 804377) B804377
theorem B9678565 : Blo 535802 9678565 := bstep (se 4 (by rfl) ⟨907365, by rfl⟩ : syracuseStep 9678565 = 1814731) B1814731
theorem B536327 : Blo 535802 536327 := bstep (se 1 (by rfl) ⟨402245, by rfl⟩ : syracuseStep 536327 = 804491) B804491
theorem B536335 : Blo 535802 536335 := bstep (se 1 (by rfl) ⟨402251, by rfl⟩ : syracuseStep 536335 = 804503) B804503
theorem B536379 : Blo 535802 536379 := bstep (se 1 (by rfl) ⟨402284, by rfl⟩ : syracuseStep 536379 = 804569) B804569
theorem B765769 : Blo 535802 765769 := bstep (se 2 (by rfl) ⟨287163, by rfl⟩ : syracuseStep 765769 = 574327) B574327
theorem B536455 : Blo 535802 536455 := bstep (se 1 (by rfl) ⟨402341, by rfl⟩ : syracuseStep 536455 = 804683) B804683
theorem B536463 : Blo 535802 536463 := bstep (se 1 (by rfl) ⟨402347, by rfl⟩ : syracuseStep 536463 = 804695) B804695
theorem B536507 : Blo 535802 536507 := bstep (se 1 (by rfl) ⟨402380, by rfl⟩ : syracuseStep 536507 = 804761) B804761
theorem B765883 : Blo 535802 765883 := bstep (se 1 (by rfl) ⟨574412, by rfl⟩ : syracuseStep 765883 = 1148825) B1148825
theorem B536583 : Blo 535802 536583 := bstep (se 1 (by rfl) ⟨402437, by rfl⟩ : syracuseStep 536583 = 804875) B804875
theorem B536591 : Blo 535802 536591 := bstep (se 1 (by rfl) ⟨402443, by rfl⟩ : syracuseStep 536591 = 804887) B804887
theorem B536635 : Blo 535802 536635 := bstep (se 1 (by rfl) ⟨402476, by rfl⟩ : syracuseStep 536635 = 804953) B804953
theorem B1814615 : Blo 535802 1814615 := bstep (se 1 (by rfl) ⟨1360961, by rfl⟩ : syracuseStep 1814615 = 2721923) B2721923
theorem B536711 : Blo 535802 536711 := bstep (se 1 (by rfl) ⟨402533, by rfl⟩ : syracuseStep 536711 = 805067) B805067
theorem B536719 : Blo 535802 536719 := bstep (se 1 (by rfl) ⟨402539, by rfl⟩ : syracuseStep 536719 = 805079) B805079
theorem B536763 : Blo 535802 536763 := bstep (se 1 (by rfl) ⟨402572, by rfl⟩ : syracuseStep 536763 = 805145) B805145
theorem B536839 : Blo 535802 536839 := bstep (se 1 (by rfl) ⟨402629, by rfl⟩ : syracuseStep 536839 = 805259) B805259
theorem B536847 : Blo 535802 536847 := bstep (se 1 (by rfl) ⟨402635, by rfl⟩ : syracuseStep 536847 = 805271) B805271
theorem B536891 : Blo 535802 536891 := bstep (se 1 (by rfl) ⟨402668, by rfl⟩ : syracuseStep 536891 = 805337) B805337
theorem B1290583 : Blo 535802 1290583 := bstep (se 1 (by rfl) ⟨967937, by rfl⟩ : syracuseStep 1290583 = 1935875) B1935875
theorem B536967 : Blo 535802 536967 := bstep (se 1 (by rfl) ⟨402725, by rfl⟩ : syracuseStep 536967 = 805451) B805451
theorem B536975 : Blo 535802 536975 := bstep (se 1 (by rfl) ⟨402731, by rfl⟩ : syracuseStep 536975 = 805463) B805463
theorem B537019 : Blo 535802 537019 := bstep (se 1 (by rfl) ⟨402764, by rfl⟩ : syracuseStep 537019 = 805529) B805529
theorem B537095 : Blo 535802 537095 := bstep (se 1 (by rfl) ⟨402821, by rfl⟩ : syracuseStep 537095 = 805643) B805643
theorem B537103 : Blo 535802 537103 := bstep (se 1 (by rfl) ⟨402827, by rfl⟩ : syracuseStep 537103 = 805655) B805655
theorem B537147 : Blo 535802 537147 := bstep (se 1 (by rfl) ⟨402860, by rfl⟩ : syracuseStep 537147 = 805721) B805721
theorem B1815101 : Blo 535802 1815101 := bstep (se 3 (by rfl) ⟨340331, by rfl⟩ : syracuseStep 1815101 = 680663) B680663
theorem B537223 : Blo 535802 537223 := bstep (se 1 (by rfl) ⟨402917, by rfl⟩ : syracuseStep 537223 = 805835) B805835
theorem B537231 : Blo 535802 537231 := bstep (se 1 (by rfl) ⟨402923, by rfl⟩ : syracuseStep 537231 = 805847) B805847
theorem B537275 : Blo 535802 537275 := bstep (se 1 (by rfl) ⟨402956, by rfl⟩ : syracuseStep 537275 = 805913) B805913
theorem B602887 : Blo 535802 602887 := bstep (se 1 (by rfl) ⟨452165, by rfl⟩ : syracuseStep 602887 = 904331) B904331
theorem B537351 : Blo 535802 537351 := bstep (se 1 (by rfl) ⟨403013, by rfl⟩ : syracuseStep 537351 = 806027) B806027
theorem B537359 : Blo 535802 537359 := bstep (se 1 (by rfl) ⟨403019, by rfl⟩ : syracuseStep 537359 = 806039) B806039
theorem B537403 : Blo 535802 537403 := bstep (se 1 (by rfl) ⟨403052, by rfl⟩ : syracuseStep 537403 = 806105) B806105
theorem B1356659 : Blo 535802 1356659 := bstep (se 1 (by rfl) ⟨1017494, by rfl⟩ : syracuseStep 1356659 = 2034989) B2034989
theorem B537479 : Blo 535802 537479 := bstep (se 1 (by rfl) ⟨403109, by rfl⟩ : syracuseStep 537479 = 806219) B806219
theorem B537487 : Blo 535802 537487 := bstep (se 1 (by rfl) ⟨403115, by rfl⟩ : syracuseStep 537487 = 806231) B806231
theorem B603067 : Blo 535802 603067 := bstep (se 1 (by rfl) ⟨452300, by rfl⟩ : syracuseStep 603067 = 904601) B904601
theorem B537531 : Blo 535802 537531 := bstep (se 1 (by rfl) ⟨403148, by rfl⟩ : syracuseStep 537531 = 806297) B806297
theorem B537607 : Blo 535802 537607 := bstep (se 1 (by rfl) ⟨403205, by rfl⟩ : syracuseStep 537607 = 806411) B806411
theorem B537615 : Blo 535802 537615 := bstep (se 1 (by rfl) ⟨403211, by rfl⟩ : syracuseStep 537615 = 806423) B806423
theorem B4076567 : Blo 535802 4076567 := bstep (se 1 (by rfl) ⟨3057425, by rfl⟩ : syracuseStep 4076567 = 6114851) B6114851
theorem B1717291 : Blo 535802 1717291 := bstep (se 1 (by rfl) ⟨1287968, by rfl⟩ : syracuseStep 1717291 = 2575937) B2575937
theorem B537659 : Blo 535802 537659 := bstep (se 1 (by rfl) ⟨403244, by rfl⟩ : syracuseStep 537659 = 806489) B806489
theorem B537735 : Blo 535802 537735 := bstep (se 1 (by rfl) ⟨403301, by rfl⟩ : syracuseStep 537735 = 806603) B806603
theorem B537743 : Blo 535802 537743 := bstep (se 1 (by rfl) ⟨403307, by rfl⟩ : syracuseStep 537743 = 806615) B806615
theorem B537787 : Blo 535802 537787 := bstep (se 1 (by rfl) ⟨403340, by rfl⟩ : syracuseStep 537787 = 806681) B806681
theorem B537863 : Blo 535802 537863 := bstep (se 1 (by rfl) ⟨403397, by rfl⟩ : syracuseStep 537863 = 806795) B806795
theorem B2176271 : Blo 535802 2176271 := bstep (se 1 (by rfl) ⟨1632203, by rfl⟩ : syracuseStep 2176271 = 3264407) B3264407
theorem B537871 : Blo 535802 537871 := bstep (se 1 (by rfl) ⟨403403, by rfl⟩ : syracuseStep 537871 = 806807) B806807
theorem B537915 : Blo 535802 537915 := bstep (se 1 (by rfl) ⟨403436, by rfl⟩ : syracuseStep 537915 = 806873) B806873
theorem B10302821 : Blo 535802 10302821 := bstep (se 4 (by rfl) ⟨965889, by rfl⟩ : syracuseStep 10302821 = 1931779) B1931779
theorem B1357175 : Blo 535802 1357175 := bstep (se 1 (by rfl) ⟨1017881, by rfl⟩ : syracuseStep 1357175 = 2035763) B2035763
theorem B5813639 : Blo 535802 5813639 := bstep (se 1 (by rfl) ⟨4360229, by rfl⟩ : syracuseStep 5813639 = 8720459) B8720459
theorem B537991 : Blo 535802 537991 := bstep (se 1 (by rfl) ⟨403493, by rfl⟩ : syracuseStep 537991 = 806987) B806987
theorem B603535 : Blo 535802 603535 := bstep (se 1 (by rfl) ⟨452651, by rfl⟩ : syracuseStep 603535 = 905303) B905303
theorem B537999 : Blo 535802 537999 := bstep (se 1 (by rfl) ⟨403499, by rfl⟩ : syracuseStep 537999 = 806999) B806999
theorem B21018041 : Blo 535802 21018041 := bstep (se 2 (by rfl) ⟨7881765, by rfl⟩ : syracuseStep 21018041 = 15763531) B15763531
theorem B538043 : Blo 535802 538043 := bstep (se 1 (by rfl) ⟨403532, by rfl⟩ : syracuseStep 538043 = 807065) B807065
theorem B767495 : Blo 535802 767495 := bstep (se 1 (by rfl) ⟨575621, by rfl⟩ : syracuseStep 767495 = 1151243) B1151243
theorem B538119 : Blo 535802 538119 := bstep (se 1 (by rfl) ⟨403589, by rfl⟩ : syracuseStep 538119 = 807179) B807179
theorem B538127 : Blo 535802 538127 := bstep (se 1 (by rfl) ⟨403595, by rfl⟩ : syracuseStep 538127 = 807191) B807191
theorem B2045483 : Blo 535802 2045483 := bstep (se 1 (by rfl) ⟨1534112, by rfl⟩ : syracuseStep 2045483 = 3068225) B3068225
theorem B538171 : Blo 535802 538171 := bstep (se 1 (by rfl) ⟨403628, by rfl⟩ : syracuseStep 538171 = 807257) B807257
theorem B538247 : Blo 535802 538247 := bstep (se 1 (by rfl) ⟨403685, by rfl⟩ : syracuseStep 538247 = 807371) B807371
theorem B538255 : Blo 535802 538255 := bstep (se 1 (by rfl) ⟨403691, by rfl⟩ : syracuseStep 538255 = 807383) B807383
theorem B538299 : Blo 535802 538299 := bstep (se 1 (by rfl) ⟨403724, by rfl⟩ : syracuseStep 538299 = 807449) B807449
theorem B538375 : Blo 535802 538375 := bstep (se 1 (by rfl) ⟨403781, by rfl⟩ : syracuseStep 538375 = 807563) B807563
theorem B538383 : Blo 535802 538383 := bstep (se 1 (by rfl) ⟨403787, by rfl⟩ : syracuseStep 538383 = 807575) B807575
theorem B538427 : Blo 535802 538427 := bstep (se 1 (by rfl) ⟨403820, by rfl⟩ : syracuseStep 538427 = 807641) B807641
theorem B16824181 : Blo 535802 16824181 := bstep (se 5 (by rfl) ⟨788633, by rfl⟩ : syracuseStep 16824181 = 1577267) B1577267
theorem B604039 : Blo 535802 604039 := bstep (se 1 (by rfl) ⟨453029, by rfl⟩ : syracuseStep 604039 = 906059) B906059
theorem B538503 : Blo 535802 538503 := bstep (se 1 (by rfl) ⟨403877, by rfl⟩ : syracuseStep 538503 = 807755) B807755
theorem B538511 : Blo 535802 538511 := bstep (se 1 (by rfl) ⟨403883, by rfl⟩ : syracuseStep 538511 = 807767) B807767
theorem B1816505 : Blo 535802 1816505 := bstep (se 2 (by rfl) ⟨681189, by rfl⟩ : syracuseStep 1816505 = 1362379) B1362379
theorem B538555 : Blo 535802 538555 := bstep (se 1 (by rfl) ⟨403916, by rfl⟩ : syracuseStep 538555 = 807833) B807833
theorem B538631 : Blo 535802 538631 := bstep (se 1 (by rfl) ⟨403973, by rfl⟩ : syracuseStep 538631 = 807947) B807947
theorem B538639 : Blo 535802 538639 := bstep (se 1 (by rfl) ⟨403979, by rfl⟩ : syracuseStep 538639 = 807959) B807959
theorem B604219 : Blo 535802 604219 := bstep (se 1 (by rfl) ⟨453164, by rfl⟩ : syracuseStep 604219 = 906329) B906329
theorem B538683 : Blo 535802 538683 := bstep (se 1 (by rfl) ⟨404012, by rfl⟩ : syracuseStep 538683 = 808025) B808025
theorem B538759 : Blo 535802 538759 := bstep (se 1 (by rfl) ⟨404069, by rfl⟩ : syracuseStep 538759 = 808139) B808139
theorem B538767 : Blo 535802 538767 := bstep (se 1 (by rfl) ⟨404075, by rfl⟩ : syracuseStep 538767 = 808151) B808151
theorem B538811 : Blo 535802 538811 := bstep (se 1 (by rfl) ⟨404108, by rfl⟩ : syracuseStep 538811 = 808217) B808217
theorem B3061961 : Blo 535802 3061961 := bstep (se 2 (by rfl) ⟨1148235, by rfl⟩ : syracuseStep 3061961 = 2296471) B2296471
theorem B538887 : Blo 535802 538887 := bstep (se 1 (by rfl) ⟨404165, by rfl⟩ : syracuseStep 538887 = 808331) B808331
theorem B1161487 : Blo 535802 1161487 := bstep (se 1 (by rfl) ⟨871115, by rfl⟩ : syracuseStep 1161487 = 1742231) B1742231
theorem B538895 : Blo 535802 538895 := bstep (se 1 (by rfl) ⟨404171, by rfl⟩ : syracuseStep 538895 = 808343) B808343
theorem B538939 : Blo 535802 538939 := bstep (se 1 (by rfl) ⟨404204, by rfl⟩ : syracuseStep 538939 = 808409) B808409
theorem B1358167 : Blo 535802 1358167 := bstep (se 1 (by rfl) ⟨1018625, by rfl⟩ : syracuseStep 1358167 = 2037251) B2037251
theorem B2767193 : Blo 535802 2767193 := bstep (se 2 (by rfl) ⟨1037697, by rfl⟩ : syracuseStep 2767193 = 2075395) B2075395
theorem B539015 : Blo 535802 539015 := bstep (se 1 (by rfl) ⟨404261, by rfl⟩ : syracuseStep 539015 = 808523) B808523
theorem B539023 : Blo 535802 539023 := bstep (se 1 (by rfl) ⟨404267, by rfl⟩ : syracuseStep 539023 = 808535) B808535
theorem B1718675 : Blo 535802 1718675 := bstep (se 1 (by rfl) ⟨1289006, by rfl⟩ : syracuseStep 1718675 = 2578013) B2578013
theorem B539067 : Blo 535802 539067 := bstep (se 1 (by rfl) ⟨404300, by rfl⟩ : syracuseStep 539067 = 808601) B808601
theorem B768457 : Blo 535802 768457 := bstep (se 2 (by rfl) ⟨288171, by rfl⟩ : syracuseStep 768457 = 576343) B576343
theorem B3258883 : Blo 535802 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B539143 : Blo 535802 539143 := bstep (se 1 (by rfl) ⟨404357, by rfl⟩ : syracuseStep 539143 = 808715) B808715
theorem B1817099 : Blo 535802 1817099 := bstep (se 1 (by rfl) ⟨1362824, by rfl⟩ : syracuseStep 1817099 = 2725649) B2725649
theorem B604687 : Blo 535802 604687 := bstep (se 1 (by rfl) ⟨453515, by rfl⟩ : syracuseStep 604687 = 907031) B907031
theorem B539151 : Blo 535802 539151 := bstep (se 1 (by rfl) ⟨404363, by rfl⟩ : syracuseStep 539151 = 808727) B808727
theorem B539195 : Blo 535802 539195 := bstep (se 1 (by rfl) ⟨404396, by rfl⟩ : syracuseStep 539195 = 808793) B808793
theorem B1227383 : Blo 535802 1227383 := bstep (se 1 (by rfl) ⟨920537, by rfl⟩ : syracuseStep 1227383 = 1841075) B1841075
theorem B1817207 : Blo 535802 1817207 := bstep (se 1 (by rfl) ⟨1362905, by rfl⟩ : syracuseStep 1817207 = 2725811) B2725811
theorem B1358471 : Blo 535802 1358471 := bstep (se 1 (by rfl) ⟨1018853, by rfl⟩ : syracuseStep 1358471 = 2037707) B2037707
theorem B539271 : Blo 535802 539271 := bstep (se 1 (by rfl) ⟨404453, by rfl⟩ : syracuseStep 539271 = 808907) B808907
theorem B539279 : Blo 535802 539279 := bstep (se 1 (by rfl) ⟨404459, by rfl⟩ : syracuseStep 539279 = 808919) B808919
theorem B1456793 : Blo 535802 1456793 := bstep (se 2 (by rfl) ⟨546297, by rfl⟩ : syracuseStep 1456793 = 1092595) B1092595
theorem B539323 : Blo 535802 539323 := bstep (se 1 (by rfl) ⟨404492, by rfl⟩ : syracuseStep 539323 = 808985) B808985
theorem B539399 : Blo 535802 539399 := bstep (se 1 (by rfl) ⟨404549, by rfl⟩ : syracuseStep 539399 = 809099) B809099
theorem B1358603 : Blo 535802 1358603 := bstep (se 1 (by rfl) ⟨1018952, by rfl⟩ : syracuseStep 1358603 = 2037905) B2037905
theorem B539407 : Blo 535802 539407 := bstep (se 1 (by rfl) ⟨404555, by rfl⟩ : syracuseStep 539407 = 809111) B809111
theorem B1719073 : Blo 535802 1719073 := bstep (se 2 (by rfl) ⟨644652, by rfl⟩ : syracuseStep 1719073 = 1289305) B1289305
theorem B539451 : Blo 535802 539451 := bstep (se 1 (by rfl) ⟨404588, by rfl⟩ : syracuseStep 539451 = 809177) B809177
theorem B3881843 : Blo 535802 3881843 := bstep (se 1 (by rfl) ⟨2911382, by rfl⟩ : syracuseStep 3881843 = 5822765) B5822765
theorem B539527 : Blo 535802 539527 := bstep (se 1 (by rfl) ⟨404645, by rfl⟩ : syracuseStep 539527 = 809291) B809291
theorem B539535 : Blo 535802 539535 := bstep (se 1 (by rfl) ⟨404651, by rfl⟩ : syracuseStep 539535 = 809303) B809303
theorem B1489817 : Blo 535802 1489817 := bstep (se 2 (by rfl) ⟨558681, by rfl⟩ : syracuseStep 1489817 = 1117363) B1117363
theorem B539579 : Blo 535802 539579 := bstep (se 1 (by rfl) ⟨404684, by rfl⟩ : syracuseStep 539579 = 809369) B809369
theorem B605191 : Blo 535802 605191 := bstep (se 1 (by rfl) ⟨453893, by rfl⟩ : syracuseStep 605191 = 907787) B907787
theorem B539655 : Blo 535802 539655 := bstep (se 1 (by rfl) ⟨404741, by rfl⟩ : syracuseStep 539655 = 809483) B809483
theorem B539663 : Blo 535802 539663 := bstep (se 1 (by rfl) ⟨404747, by rfl⟩ : syracuseStep 539663 = 809495) B809495
theorem B965675 : Blo 535802 965675 := bstep (se 1 (by rfl) ⟨724256, by rfl⟩ : syracuseStep 965675 = 1448513) B1448513
theorem B539707 : Blo 535802 539707 := bstep (se 1 (by rfl) ⟨404780, by rfl⟩ : syracuseStep 539707 = 809561) B809561
theorem B5160023 : Blo 535802 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B539783 : Blo 535802 539783 := bstep (se 1 (by rfl) ⟨404837, by rfl⟩ : syracuseStep 539783 = 809675) B809675
theorem B539791 : Blo 535802 539791 := bstep (se 1 (by rfl) ⟨404843, by rfl⟩ : syracuseStep 539791 = 809687) B809687
theorem B605371 : Blo 535802 605371 := bstep (se 1 (by rfl) ⟨454028, by rfl⟩ : syracuseStep 605371 = 908057) B908057
theorem B1817801 : Blo 535802 1817801 := bstep (se 2 (by rfl) ⟨681675, by rfl⟩ : syracuseStep 1817801 = 1363351) B1363351
theorem B1359119 : Blo 535802 1359119 := bstep (se 1 (by rfl) ⟨1019339, by rfl⟩ : syracuseStep 1359119 = 2038679) B2038679
theorem B2800955 : Blo 535802 2800955 := bstep (se 1 (by rfl) ⟨2100716, by rfl⟩ : syracuseStep 2800955 = 4201433) B4201433
theorem B1359251 : Blo 535802 1359251 := bstep (se 1 (by rfl) ⟨1019438, by rfl⟩ : syracuseStep 1359251 = 2038877) B2038877
theorem B605839 : Blo 535802 605839 := bstep (se 1 (by rfl) ⟨454379, by rfl⟩ : syracuseStep 605839 = 908759) B908759
theorem B573199 : Blo 535802 573199 := bstep (se 1 (by rfl) ⟨429899, by rfl⟩ : syracuseStep 573199 = 859799) B859799
theorem B573319 : Blo 535802 573319 := bstep (se 1 (by rfl) ⟨429989, by rfl⟩ : syracuseStep 573319 = 859979) B859979
theorem B1818503 : Blo 535802 1818503 := bstep (se 1 (by rfl) ⟨1363877, by rfl⟩ : syracuseStep 1818503 = 2727755) B2727755
theorem B6144011 : Blo 535802 6144011 := bstep (se 1 (by rfl) ⟨4608008, by rfl⟩ : syracuseStep 6144011 = 9216017) B9216017
theorem B3063851 : Blo 535802 3063851 := bstep (se 1 (by rfl) ⟨2297888, by rfl⟩ : syracuseStep 3063851 = 4595777) B4595777
theorem B573575 : Blo 535802 573575 := bstep (se 1 (by rfl) ⟨430181, by rfl⟩ : syracuseStep 573575 = 860363) B860363
theorem B606343 : Blo 535802 606343 := bstep (se 1 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 606343 = 909515) B909515
theorem B1818881 : Blo 535802 1818881 := bstep (se 2 (by rfl) ⟨682080, by rfl⟩ : syracuseStep 1818881 = 1364161) B1364161
theorem B1229089 : Blo 535802 1229089 := bstep (se 2 (by rfl) ⟨460908, by rfl⟩ : syracuseStep 1229089 = 921817) B921817
theorem B606523 : Blo 535802 606523 := bstep (se 1 (by rfl) ⟨454892, by rfl⟩ : syracuseStep 606523 = 909785) B909785
theorem B1360385 : Blo 535802 1360385 := bstep (se 2 (by rfl) ⟨510144, by rfl⟩ : syracuseStep 1360385 = 1020289) B1020289
theorem B1720919 : Blo 535802 1720919 := bstep (se 1 (by rfl) ⟨1290689, by rfl⟩ : syracuseStep 1720919 = 2581379) B2581379
theorem B1163911 : Blo 535802 1163911 := bstep (se 1 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 1163911 = 1745867) B1745867
theorem B574139 : Blo 535802 574139 := bstep (se 1 (by rfl) ⟨430604, by rfl⟩ : syracuseStep 574139 = 861209) B861209
theorem B4899599 : Blo 535802 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B606991 : Blo 535802 606991 := bstep (se 1 (by rfl) ⟨455243, by rfl⟩ : syracuseStep 606991 = 910487) B910487
theorem B1458977 : Blo 535802 1458977 := bstep (se 2 (by rfl) ⟨547116, by rfl⟩ : syracuseStep 1458977 = 1094233) B1094233
theorem B3261221 : Blo 535802 3261221 := bstep (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) B611479
theorem B3457829 : Blo 535802 3457829 := bstep (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) B648343
theorem B1360759 : Blo 535802 1360759 := bstep (se 1 (by rfl) ⟨1020569, by rfl⟩ : syracuseStep 1360759 = 2041139) B2041139
theorem B2048915 : Blo 535802 2048915 := bstep (se 1 (by rfl) ⟨1536686, by rfl⟩ : syracuseStep 2048915 = 3073373) B3073373
theorem B803771 : Blo 535802 803771 := bstep (se 1 (by rfl) ⟨602828, by rfl⟩ : syracuseStep 803771 = 1205657) B1205657
theorem B803831 : Blo 535802 803831 := bstep (se 1 (by rfl) ⟨602873, by rfl⟩ : syracuseStep 803831 = 1205747) B1205747
theorem B803855 : Blo 535802 803855 := bstep (se 1 (by rfl) ⟨602891, by rfl⟩ : syracuseStep 803855 = 1205783) B1205783
theorem B1819691 : Blo 535802 1819691 := bstep (se 1 (by rfl) ⟨1364768, by rfl⟩ : syracuseStep 1819691 = 2729537) B2729537
theorem B803897 : Blo 535802 803897 := bstep (se 2 (by rfl) ⟨301461, by rfl⟩ : syracuseStep 803897 = 602923) B602923
theorem B803975 : Blo 535802 803975 := bstep (se 1 (by rfl) ⟨602981, by rfl⟩ : syracuseStep 803975 = 1205963) B1205963
theorem B804011 : Blo 535802 804011 := bstep (se 1 (by rfl) ⟨603008, by rfl⟩ : syracuseStep 804011 = 1206017) B1206017
theorem B804041 : Blo 535802 804041 := bstep (se 2 (by rfl) ⟨301515, by rfl⟩ : syracuseStep 804041 = 603031) B603031
theorem B1361195 : Blo 535802 1361195 := bstep (se 1 (by rfl) ⟨1020896, by rfl⟩ : syracuseStep 1361195 = 2041793) B2041793
theorem B804155 : Blo 535802 804155 := bstep (se 1 (by rfl) ⟨603116, by rfl⟩ : syracuseStep 804155 = 1206233) B1206233
theorem B804215 : Blo 535802 804215 := bstep (se 1 (by rfl) ⟨603161, by rfl⟩ : syracuseStep 804215 = 1206323) B1206323
theorem B804239 : Blo 535802 804239 := bstep (se 1 (by rfl) ⟨603179, by rfl⟩ : syracuseStep 804239 = 1206359) B1206359
theorem B804281 : Blo 535802 804281 := bstep (se 2 (by rfl) ⟨301605, by rfl⟩ : syracuseStep 804281 = 603211) B603211
theorem B1230265 : Blo 535802 1230265 := bstep (se 2 (by rfl) ⟨461349, by rfl⟩ : syracuseStep 1230265 = 922699) B922699
theorem B3065309 : Blo 535802 3065309 := bstep (se 3 (by rfl) ⟨574745, by rfl⟩ : syracuseStep 3065309 = 1149491) B1149491
theorem B804359 : Blo 535802 804359 := bstep (se 1 (by rfl) ⟨603269, by rfl⟩ : syracuseStep 804359 = 1206539) B1206539
theorem B804395 : Blo 535802 804395 := bstep (se 1 (by rfl) ⟨603296, by rfl⟩ : syracuseStep 804395 = 1206593) B1206593
theorem B804425 : Blo 535802 804425 := bstep (se 2 (by rfl) ⟨301659, by rfl⟩ : syracuseStep 804425 = 603319) B603319
theorem B10798771 : Blo 535802 10798771 := bstep (se 1 (by rfl) ⟨8099078, by rfl⟩ : syracuseStep 10798771 = 16198157) B16198157
theorem B804539 : Blo 535802 804539 := bstep (se 1 (by rfl) ⟨603404, by rfl⟩ : syracuseStep 804539 = 1206809) B1206809
theorem B804599 : Blo 535802 804599 := bstep (se 1 (by rfl) ⟨603449, by rfl⟩ : syracuseStep 804599 = 1206899) B1206899
theorem B804623 : Blo 535802 804623 := bstep (se 1 (by rfl) ⟨603467, by rfl⟩ : syracuseStep 804623 = 1206935) B1206935
theorem B804665 : Blo 535802 804665 := bstep (se 2 (by rfl) ⟨301749, by rfl⟩ : syracuseStep 804665 = 603499) B603499
theorem B9946955 : Blo 535802 9946955 := bstep (se 1 (by rfl) ⟨7460216, by rfl⟩ : syracuseStep 9946955 = 14920433) B14920433
theorem B804743 : Blo 535802 804743 := bstep (se 1 (by rfl) ⟨603557, by rfl⟩ : syracuseStep 804743 = 1207115) B1207115
theorem B804779 : Blo 535802 804779 := bstep (se 1 (by rfl) ⟨603584, by rfl⟩ : syracuseStep 804779 = 1207169) B1207169
theorem B804809 : Blo 535802 804809 := bstep (se 2 (by rfl) ⟨301803, by rfl⟩ : syracuseStep 804809 = 603607) B603607
theorem B3065809 : Blo 535802 3065809 := bstep (se 2 (by rfl) ⟨1149678, by rfl⟩ : syracuseStep 3065809 = 2299357) B2299357
theorem B804923 : Blo 535802 804923 := bstep (se 1 (by rfl) ⟨603692, by rfl⟩ : syracuseStep 804923 = 1207385) B1207385
theorem B1362035 : Blo 535802 1362035 := bstep (se 1 (by rfl) ⟨1021526, by rfl⟩ : syracuseStep 1362035 = 2043053) B2043053
theorem B804983 : Blo 535802 804983 := bstep (se 1 (by rfl) ⟨603737, by rfl⟩ : syracuseStep 804983 = 1207475) B1207475
theorem B1362055 : Blo 535802 1362055 := bstep (se 1 (by rfl) ⟨1021541, by rfl⟩ : syracuseStep 1362055 = 2043083) B2043083
theorem B805007 : Blo 535802 805007 := bstep (se 1 (by rfl) ⟨603755, by rfl⟩ : syracuseStep 805007 = 1207511) B1207511
theorem B805049 : Blo 535802 805049 := bstep (se 2 (by rfl) ⟨301893, by rfl⟩ : syracuseStep 805049 = 603787) B603787
theorem B805127 : Blo 535802 805127 := bstep (se 1 (by rfl) ⟨603845, by rfl⟩ : syracuseStep 805127 = 1207691) B1207691
theorem B805163 : Blo 535802 805163 := bstep (se 1 (by rfl) ⟨603872, by rfl⟩ : syracuseStep 805163 = 1207745) B1207745
theorem B1820987 : Blo 535802 1820987 := bstep (se 1 (by rfl) ⟨1365740, by rfl⟩ : syracuseStep 1820987 = 2731481) B2731481
theorem B805193 : Blo 535802 805193 := bstep (se 2 (by rfl) ⟨301947, by rfl⟩ : syracuseStep 805193 = 603895) B603895
theorem B1362329 : Blo 535802 1362329 := bstep (se 2 (by rfl) ⟨510873, by rfl⟩ : syracuseStep 1362329 = 1021747) B1021747
theorem B805307 : Blo 535802 805307 := bstep (se 1 (by rfl) ⟨603980, by rfl⟩ : syracuseStep 805307 = 1207961) B1207961
theorem B805367 : Blo 535802 805367 := bstep (se 1 (by rfl) ⟨604025, by rfl⟩ : syracuseStep 805367 = 1208051) B1208051
theorem B805391 : Blo 535802 805391 := bstep (se 1 (by rfl) ⟨604043, by rfl⟩ : syracuseStep 805391 = 1208087) B1208087
theorem B805433 : Blo 535802 805433 := bstep (se 2 (by rfl) ⟨302037, by rfl⟩ : syracuseStep 805433 = 604075) B604075
theorem B1362491 : Blo 535802 1362491 := bstep (se 1 (by rfl) ⟨1021868, by rfl⟩ : syracuseStep 1362491 = 2043737) B2043737
theorem B805511 : Blo 535802 805511 := bstep (se 1 (by rfl) ⟨604133, by rfl⟩ : syracuseStep 805511 = 1208267) B1208267
theorem B805547 : Blo 535802 805547 := bstep (se 1 (by rfl) ⟨604160, by rfl⟩ : syracuseStep 805547 = 1208321) B1208321
theorem B5163713 : Blo 535802 5163713 := bstep (se 2 (by rfl) ⟨1936392, by rfl⟩ : syracuseStep 5163713 = 3872785) B3872785
theorem B805577 : Blo 535802 805577 := bstep (se 2 (by rfl) ⟨302091, by rfl⟩ : syracuseStep 805577 = 604183) B604183
theorem B2444033 : Blo 535802 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B1362703 : Blo 535802 1362703 := bstep (se 1 (by rfl) ⟨1022027, by rfl⟩ : syracuseStep 1362703 = 2044055) B2044055
theorem B576271 : Blo 535802 576271 := bstep (se 1 (by rfl) ⟨432203, by rfl⟩ : syracuseStep 576271 = 864407) B864407
theorem B1821473 : Blo 535802 1821473 := bstep (se 2 (by rfl) ⟨683052, by rfl⟩ : syracuseStep 1821473 = 1366105) B1366105
theorem B805691 : Blo 535802 805691 := bstep (se 1 (by rfl) ⟨604268, by rfl⟩ : syracuseStep 805691 = 1208537) B1208537
theorem B805751 : Blo 535802 805751 := bstep (se 1 (by rfl) ⟨604313, by rfl⟩ : syracuseStep 805751 = 1208627) B1208627
theorem B1526663 : Blo 535802 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B805775 : Blo 535802 805775 := bstep (se 1 (by rfl) ⟨604331, by rfl⟩ : syracuseStep 805775 = 1208663) B1208663
theorem B805817 : Blo 535802 805817 := bstep (se 2 (by rfl) ⟨302181, by rfl⟩ : syracuseStep 805817 = 604363) B604363
theorem B5655557 : Blo 535802 5655557 := bstep (se 4 (by rfl) ⟨530208, by rfl⟩ : syracuseStep 5655557 = 1060417) B1060417
theorem B805895 : Blo 535802 805895 := bstep (se 1 (by rfl) ⟨604421, by rfl⟩ : syracuseStep 805895 = 1208843) B1208843
theorem B1362977 : Blo 535802 1362977 := bstep (se 2 (by rfl) ⟨511116, by rfl⟩ : syracuseStep 1362977 = 1022233) B1022233
theorem B805931 : Blo 535802 805931 := bstep (se 1 (by rfl) ⟨604448, by rfl⟩ : syracuseStep 805931 = 1208897) B1208897
theorem B1526845 : Blo 535802 1526845 := bstep (se 3 (by rfl) ⟨286283, by rfl⟩ : syracuseStep 1526845 = 572567) B572567
theorem B805961 : Blo 535802 805961 := bstep (se 2 (by rfl) ⟨302235, by rfl⟩ : syracuseStep 805961 = 604471) B604471
theorem B806075 : Blo 535802 806075 := bstep (se 1 (by rfl) ⟨604556, by rfl⟩ : syracuseStep 806075 = 1209113) B1209113
theorem B806135 : Blo 535802 806135 := bstep (se 1 (by rfl) ⟨604601, by rfl⟩ : syracuseStep 806135 = 1209203) B1209203
theorem B806159 : Blo 535802 806159 := bstep (se 1 (by rfl) ⟨604619, by rfl⟩ : syracuseStep 806159 = 1209239) B1209239
theorem B806201 : Blo 535802 806201 := bstep (se 2 (by rfl) ⟨302325, by rfl⟩ : syracuseStep 806201 = 604651) B604651
theorem B904567 : Blo 535802 904567 := bstep (se 1 (by rfl) ⟨678425, by rfl⟩ : syracuseStep 904567 = 1356851) B1356851
theorem B806279 : Blo 535802 806279 := bstep (se 1 (by rfl) ⟨604709, by rfl⟩ : syracuseStep 806279 = 1209419) B1209419
theorem B1527187 : Blo 535802 1527187 := bstep (se 1 (by rfl) ⟨1145390, by rfl⟩ : syracuseStep 1527187 = 2290781) B2290781
theorem B1723801 : Blo 535802 1723801 := bstep (se 2 (by rfl) ⟨646425, by rfl⟩ : syracuseStep 1723801 = 1292851) B1292851
theorem B806315 : Blo 535802 806315 := bstep (se 1 (by rfl) ⟨604736, by rfl⟩ : syracuseStep 806315 = 1209473) B1209473
theorem B806345 : Blo 535802 806345 := bstep (se 2 (by rfl) ⟨302379, by rfl⟩ : syracuseStep 806345 = 604759) B604759
theorem B1166891 : Blo 535802 1166891 := bstep (se 1 (by rfl) ⟨875168, by rfl⟩ : syracuseStep 1166891 = 1750337) B1750337
theorem B904763 : Blo 535802 904763 := bstep (se 1 (by rfl) ⟨678572, by rfl⟩ : syracuseStep 904763 = 1357145) B1357145
theorem B806459 : Blo 535802 806459 := bstep (se 1 (by rfl) ⟨604844, by rfl⟩ : syracuseStep 806459 = 1209689) B1209689
theorem B806519 : Blo 535802 806519 := bstep (se 1 (by rfl) ⟨604889, by rfl⟩ : syracuseStep 806519 = 1209779) B1209779
theorem B2805367 : Blo 535802 2805367 := bstep (se 1 (by rfl) ⟨2104025, by rfl⟩ : syracuseStep 2805367 = 4208051) B4208051
theorem B806543 : Blo 535802 806543 := bstep (se 1 (by rfl) ⟨604907, by rfl⟩ : syracuseStep 806543 = 1209815) B1209815
theorem B806585 : Blo 535802 806585 := bstep (se 2 (by rfl) ⟨302469, by rfl⟩ : syracuseStep 806585 = 604939) B604939
theorem B806663 : Blo 535802 806663 := bstep (se 1 (by rfl) ⟨604997, by rfl⟩ : syracuseStep 806663 = 1209995) B1209995
theorem B806699 : Blo 535802 806699 := bstep (se 1 (by rfl) ⟨605024, by rfl⟩ : syracuseStep 806699 = 1210049) B1210049
theorem B806729 : Blo 535802 806729 := bstep (se 2 (by rfl) ⟨302523, by rfl⟩ : syracuseStep 806729 = 605047) B605047
theorem B2215795 : Blo 535802 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B3067793 : Blo 535802 3067793 := bstep (se 2 (by rfl) ⟨1150422, by rfl⟩ : syracuseStep 3067793 = 2300845) B2300845
theorem B806843 : Blo 535802 806843 := bstep (se 1 (by rfl) ⟨605132, by rfl⟩ : syracuseStep 806843 = 1210265) B1210265
theorem B905161 : Blo 535802 905161 := bstep (se 2 (by rfl) ⟨339435, by rfl⟩ : syracuseStep 905161 = 678871) B678871
theorem B806903 : Blo 535802 806903 := bstep (se 1 (by rfl) ⟨605177, by rfl⟩ : syracuseStep 806903 = 1210355) B1210355
theorem B1363979 : Blo 535802 1363979 := bstep (se 1 (by rfl) ⟨1022984, by rfl⟩ : syracuseStep 1363979 = 2045969) B2045969
theorem B806927 : Blo 535802 806927 := bstep (se 1 (by rfl) ⟨605195, by rfl⟩ : syracuseStep 806927 = 1210391) B1210391
theorem B806969 : Blo 535802 806969 := bstep (se 2 (by rfl) ⟨302613, by rfl⟩ : syracuseStep 806969 = 605227) B605227
theorem B807047 : Blo 535802 807047 := bstep (se 1 (by rfl) ⟨605285, by rfl⟩ : syracuseStep 807047 = 1210571) B1210571
theorem B807083 : Blo 535802 807083 := bstep (se 1 (by rfl) ⟨605312, by rfl⟩ : syracuseStep 807083 = 1210625) B1210625
theorem B807113 : Blo 535802 807113 := bstep (se 2 (by rfl) ⟨302667, by rfl⟩ : syracuseStep 807113 = 605335) B605335
theorem B1528075 : Blo 535802 1528075 := bstep (se 1 (by rfl) ⟨1146056, by rfl⟩ : syracuseStep 1528075 = 2292113) B2292113
theorem B1036559 : Blo 535802 1036559 := bstep (se 1 (by rfl) ⟨777419, by rfl⟩ : syracuseStep 1036559 = 1554839) B1554839
theorem B971023 : Blo 535802 971023 := bstep (se 1 (by rfl) ⟨728267, by rfl⟩ : syracuseStep 971023 = 1456535) B1456535
theorem B5165329 : Blo 535802 5165329 := bstep (se 2 (by rfl) ⟨1936998, by rfl⟩ : syracuseStep 5165329 = 3873997) B3873997
theorem B6148385 : Blo 535802 6148385 := bstep (se 2 (by rfl) ⟨2305644, by rfl⟩ : syracuseStep 6148385 = 4611289) B4611289
theorem B807227 : Blo 535802 807227 := bstep (se 1 (by rfl) ⟨605420, by rfl⟩ : syracuseStep 807227 = 1210841) B1210841
theorem B807287 : Blo 535802 807287 := bstep (se 1 (by rfl) ⟨605465, by rfl⟩ : syracuseStep 807287 = 1210931) B1210931
theorem B807311 : Blo 535802 807311 := bstep (se 1 (by rfl) ⟨605483, by rfl⟩ : syracuseStep 807311 = 1210967) B1210967
theorem B807353 : Blo 535802 807353 := bstep (se 2 (by rfl) ⟨302757, by rfl⟩ : syracuseStep 807353 = 605515) B605515
theorem B807431 : Blo 535802 807431 := bstep (se 1 (by rfl) ⟨605573, by rfl⟩ : syracuseStep 807431 = 1211147) B1211147
theorem B807467 : Blo 535802 807467 := bstep (se 1 (by rfl) ⟨605600, by rfl⟩ : syracuseStep 807467 = 1211201) B1211201
theorem B807497 : Blo 535802 807497 := bstep (se 2 (by rfl) ⟨302811, by rfl⟩ : syracuseStep 807497 = 605623) B605623
theorem B4084343 : Blo 535802 4084343 := bstep (se 1 (by rfl) ⟨3063257, by rfl⟩ : syracuseStep 4084343 = 6126515) B6126515
theorem B905863 : Blo 535802 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B1364627 : Blo 535802 1364627 := bstep (se 1 (by rfl) ⟨1023470, by rfl⟩ : syracuseStep 1364627 = 2046941) B2046941
theorem B807611 : Blo 535802 807611 := bstep (se 1 (by rfl) ⟨605708, by rfl⟩ : syracuseStep 807611 = 1211417) B1211417
theorem B807671 : Blo 535802 807671 := bstep (se 1 (by rfl) ⟨605753, by rfl⟩ : syracuseStep 807671 = 1211507) B1211507
theorem B1528577 : Blo 535802 1528577 := bstep (se 2 (by rfl) ⟨573216, by rfl⟩ : syracuseStep 1528577 = 1146433) B1146433
theorem B2577167 : Blo 535802 2577167 := bstep (se 1 (by rfl) ⟨1932875, by rfl⟩ : syracuseStep 2577167 = 3865751) B3865751
theorem B807695 : Blo 535802 807695 := bstep (se 1 (by rfl) ⟨605771, by rfl⟩ : syracuseStep 807695 = 1211543) B1211543
theorem B807737 : Blo 535802 807737 := bstep (se 2 (by rfl) ⟨302901, by rfl⟩ : syracuseStep 807737 = 605803) B605803
theorem B807815 : Blo 535802 807815 := bstep (se 1 (by rfl) ⟨605861, by rfl⟩ : syracuseStep 807815 = 1211723) B1211723
theorem B807851 : Blo 535802 807851 := bstep (se 1 (by rfl) ⟨605888, by rfl⟩ : syracuseStep 807851 = 1211777) B1211777
theorem B1364921 : Blo 535802 1364921 := bstep (se 2 (by rfl) ⟨511845, by rfl⟩ : syracuseStep 1364921 = 1023691) B1023691
theorem B807881 : Blo 535802 807881 := bstep (se 2 (by rfl) ⟨302955, by rfl⟩ : syracuseStep 807881 = 605911) B605911
theorem B807995 : Blo 535802 807995 := bstep (se 1 (by rfl) ⟨605996, by rfl⟩ : syracuseStep 807995 = 1211993) B1211993
theorem B1528919 : Blo 535802 1528919 := bstep (se 1 (by rfl) ⟨1146689, by rfl⟩ : syracuseStep 1528919 = 2293379) B2293379
theorem B808055 : Blo 535802 808055 := bstep (se 1 (by rfl) ⟨606041, by rfl⟩ : syracuseStep 808055 = 1212083) B1212083
theorem B808079 : Blo 535802 808079 := bstep (se 1 (by rfl) ⟨606059, by rfl⟩ : syracuseStep 808079 = 1212119) B1212119
theorem B808121 : Blo 535802 808121 := bstep (se 2 (by rfl) ⟨303045, by rfl⟩ : syracuseStep 808121 = 606091) B606091
theorem B808199 : Blo 535802 808199 := bstep (se 1 (by rfl) ⟨606149, by rfl⟩ : syracuseStep 808199 = 1212299) B1212299
theorem B906511 : Blo 535802 906511 := bstep (se 1 (by rfl) ⟨679883, by rfl⟩ : syracuseStep 906511 = 1359767) B1359767
theorem B808235 : Blo 535802 808235 := bstep (se 1 (by rfl) ⟨606176, by rfl⟩ : syracuseStep 808235 = 1212353) B1212353
theorem B808265 : Blo 535802 808265 := bstep (se 2 (by rfl) ⟨303099, by rfl⟩ : syracuseStep 808265 = 606199) B606199
theorem B3102097 : Blo 535802 3102097 := bstep (se 2 (by rfl) ⟨1163286, by rfl⟩ : syracuseStep 3102097 = 2326573) B2326573
theorem B34952633 : Blo 535802 34952633 := bstep (se 2 (by rfl) ⟨13107237, by rfl⟩ : syracuseStep 34952633 = 26214475) B26214475
theorem B808379 : Blo 535802 808379 := bstep (se 1 (by rfl) ⟨606284, by rfl⟩ : syracuseStep 808379 = 1212569) B1212569
theorem B808439 : Blo 535802 808439 := bstep (se 1 (by rfl) ⟨606329, by rfl⟩ : syracuseStep 808439 = 1212659) B1212659
theorem B808463 : Blo 535802 808463 := bstep (se 1 (by rfl) ⟨606347, by rfl⟩ : syracuseStep 808463 = 1212695) B1212695
theorem B808505 : Blo 535802 808505 := bstep (se 2 (by rfl) ⟨303189, by rfl⟩ : syracuseStep 808505 = 606379) B606379
theorem B4085315 : Blo 535802 4085315 := bstep (se 1 (by rfl) ⟨3063986, by rfl⟩ : syracuseStep 4085315 = 6127973) B6127973
theorem B1365619 : Blo 535802 1365619 := bstep (se 1 (by rfl) ⟨1024214, by rfl⟩ : syracuseStep 1365619 = 2048429) B2048429
theorem B972407 : Blo 535802 972407 := bstep (se 1 (by rfl) ⟨729305, by rfl⟩ : syracuseStep 972407 = 1458611) B1458611
theorem B808583 : Blo 535802 808583 := bstep (se 1 (by rfl) ⟨606437, by rfl⟩ : syracuseStep 808583 = 1212875) B1212875
theorem B808619 : Blo 535802 808619 := bstep (se 1 (by rfl) ⟨606464, by rfl⟩ : syracuseStep 808619 = 1212929) B1212929
theorem B808649 : Blo 535802 808649 := bstep (se 2 (by rfl) ⟨303243, by rfl⟩ : syracuseStep 808649 = 606487) B606487
theorem B1365761 : Blo 535802 1365761 := bstep (se 2 (by rfl) ⟨512160, by rfl⟩ : syracuseStep 1365761 = 1024321) B1024321
theorem B907051 : Blo 535802 907051 := bstep (se 1 (by rfl) ⟨680288, by rfl⟩ : syracuseStep 907051 = 1360577) B1360577
theorem B808763 : Blo 535802 808763 := bstep (se 1 (by rfl) ⟨606572, by rfl⟩ : syracuseStep 808763 = 1213145) B1213145
theorem B808823 : Blo 535802 808823 := bstep (se 1 (by rfl) ⟨606617, by rfl⟩ : syracuseStep 808823 = 1213235) B1213235
theorem B808847 : Blo 535802 808847 := bstep (se 1 (by rfl) ⟨606635, by rfl⟩ : syracuseStep 808847 = 1213271) B1213271
theorem B907193 : Blo 535802 907193 := bstep (se 2 (by rfl) ⟨340197, by rfl⟩ : syracuseStep 907193 = 680395) B680395
theorem B808889 : Blo 535802 808889 := bstep (se 2 (by rfl) ⟨303333, by rfl⟩ : syracuseStep 808889 = 606667) B606667
theorem B808967 : Blo 535802 808967 := bstep (se 1 (by rfl) ⟨606725, by rfl⟩ : syracuseStep 808967 = 1213451) B1213451
theorem B809003 : Blo 535802 809003 := bstep (se 1 (by rfl) ⟨606752, by rfl⟩ : syracuseStep 809003 = 1213505) B1213505
theorem B809033 : Blo 535802 809033 := bstep (se 2 (by rfl) ⟨303387, by rfl⟩ : syracuseStep 809033 = 606775) B606775
theorem B809147 : Blo 535802 809147 := bstep (se 1 (by rfl) ⟨606860, by rfl⟩ : syracuseStep 809147 = 1213721) B1213721
theorem B1366217 : Blo 535802 1366217 := bstep (se 2 (by rfl) ⟨512331, by rfl⟩ : syracuseStep 1366217 = 1024663) B1024663
theorem B809207 : Blo 535802 809207 := bstep (se 1 (by rfl) ⟨606905, by rfl⟩ : syracuseStep 809207 = 1213811) B1213811
theorem B809231 : Blo 535802 809231 := bstep (se 1 (by rfl) ⟨606923, by rfl⟩ : syracuseStep 809231 = 1213847) B1213847
theorem B809273 : Blo 535802 809273 := bstep (se 2 (by rfl) ⟨303477, by rfl⟩ : syracuseStep 809273 = 606955) B606955
theorem B2578823 : Blo 535802 2578823 := bstep (se 1 (by rfl) ⟨1934117, by rfl⟩ : syracuseStep 2578823 = 3868235) B3868235
theorem B6117767 : Blo 535802 6117767 := bstep (se 1 (by rfl) ⟨4588325, by rfl⟩ : syracuseStep 6117767 = 9176651) B9176651
theorem B809351 : Blo 535802 809351 := bstep (se 1 (by rfl) ⟨607013, by rfl⟩ : syracuseStep 809351 = 1214027) B1214027
theorem B809387 : Blo 535802 809387 := bstep (se 1 (by rfl) ⟨607040, by rfl⟩ : syracuseStep 809387 = 1214081) B1214081
theorem B809417 : Blo 535802 809417 := bstep (se 2 (by rfl) ⟨303531, by rfl⟩ : syracuseStep 809417 = 607063) B607063
theorem B809531 : Blo 535802 809531 := bstep (se 1 (by rfl) ⟨607148, by rfl⟩ : syracuseStep 809531 = 1214297) B1214297
theorem B907895 : Blo 535802 907895 := bstep (se 1 (by rfl) ⟨680921, by rfl⟩ : syracuseStep 907895 = 1361843) B1361843
theorem B809591 : Blo 535802 809591 := bstep (se 1 (by rfl) ⟨607193, by rfl⟩ : syracuseStep 809591 = 1214387) B1214387
theorem B809615 : Blo 535802 809615 := bstep (se 1 (by rfl) ⟨607211, by rfl⟩ : syracuseStep 809615 = 1214423) B1214423
theorem B809657 : Blo 535802 809657 := bstep (se 2 (by rfl) ⟨303621, by rfl⟩ : syracuseStep 809657 = 607243) B607243
theorem B678775 : Blo 535802 678775 := bstep (se 1 (by rfl) ⟨509081, by rfl⟩ : syracuseStep 678775 = 1018163) B1018163
theorem B1530809 : Blo 535802 1530809 := bstep (se 2 (by rfl) ⟨574053, by rfl⟩ : syracuseStep 1530809 = 1148107) B1148107
theorem B908347 : Blo 535802 908347 := bstep (se 1 (by rfl) ⟨681260, by rfl⟩ : syracuseStep 908347 = 1362521) B1362521
theorem B679099 : Blo 535802 679099 := bstep (se 1 (by rfl) ⟨509324, by rfl⟩ : syracuseStep 679099 = 1018649) B1018649
theorem B908489 : Blo 535802 908489 := bstep (se 2 (by rfl) ⟨340683, by rfl⟩ : syracuseStep 908489 = 681367) B681367
theorem B14179643 : Blo 535802 14179643 := bstep (se 1 (by rfl) ⟨10634732, by rfl⟩ : syracuseStep 14179643 = 21269465) B21269465
theorem B3267955 : Blo 535802 3267955 := bstep (se 1 (by rfl) ⟨2450966, by rfl⟩ : syracuseStep 3267955 = 4901933) B4901933
theorem B5529131 : Blo 535802 5529131 := bstep (se 1 (by rfl) ⟨4146848, by rfl⟩ : syracuseStep 5529131 = 8293697) B8293697
theorem B2186813 : Blo 535802 2186813 := bstep (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) B820055
theorem B1498771 : Blo 535802 1498771 := bstep (se 1 (by rfl) ⟨1124078, by rfl⟩ : syracuseStep 1498771 = 2248157) B2248157
theorem B909191 : Blo 535802 909191 := bstep (se 1 (by rfl) ⟨681893, by rfl⟩ : syracuseStep 909191 = 1363787) B1363787
theorem B680071 : Blo 535802 680071 := bstep (se 1 (by rfl) ⟨510053, by rfl⟩ : syracuseStep 680071 = 1020107) B1020107
theorem B6644227 : Blo 535802 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B909839 : Blo 535802 909839 := bstep (se 1 (by rfl) ⟨682379, by rfl⟩ : syracuseStep 909839 = 1364759) B1364759
theorem B1532449 : Blo 535802 1532449 := bstep (se 2 (by rfl) ⟨574668, by rfl⟩ : syracuseStep 1532449 = 1149337) B1149337
theorem B680491 : Blo 535802 680491 := bstep (se 1 (by rfl) ⟨510368, by rfl⟩ : syracuseStep 680491 = 1020737) B1020737
theorem B3072599 : Blo 535802 3072599 := bstep (se 1 (by rfl) ⟨2304449, by rfl⟩ : syracuseStep 3072599 = 4608899) B4608899
theorem B680719 : Blo 535802 680719 := bstep (se 1 (by rfl) ⟨510539, by rfl⟩ : syracuseStep 680719 = 1021079) B1021079
theorem B910379 : Blo 535802 910379 := bstep (se 1 (by rfl) ⟨682784, by rfl⟩ : syracuseStep 910379 = 1365569) B1365569
theorem B1205639 : Blo 535802 1205639 := bstep (se 1 (by rfl) ⟨904229, by rfl⟩ : syracuseStep 1205639 = 1808459) B1808459
theorem B6284729 : Blo 535802 6284729 := bstep (se 2 (by rfl) ⟨2356773, by rfl⟩ : syracuseStep 6284729 = 4713547) B4713547
theorem B910777 : Blo 535802 910777 := bstep (se 2 (by rfl) ⟨341541, by rfl⟩ : syracuseStep 910777 = 683083) B683083
theorem B681463 : Blo 535802 681463 := bstep (se 1 (by rfl) ⟨511097, by rfl⟩ : syracuseStep 681463 = 1022195) B1022195
theorem B1205819 : Blo 535802 1205819 := bstep (se 1 (by rfl) ⟨904364, by rfl⟩ : syracuseStep 1205819 = 1808729) B1808729
theorem B2713175 : Blo 535802 2713175 := bstep (se 1 (by rfl) ⟨2034881, by rfl⟩ : syracuseStep 2713175 = 4069763) B4069763
theorem B13395557 : Blo 535802 13395557 := bstep (se 4 (by rfl) ⟨1255833, by rfl⟩ : syracuseStep 13395557 = 2511667) B2511667
theorem B1205945 : Blo 535802 1205945 := bstep (se 2 (by rfl) ⟨452229, by rfl⟩ : syracuseStep 1205945 = 904459) B904459
theorem B5826305 : Blo 535802 5826305 := bstep (se 2 (by rfl) ⟨2184864, by rfl⟩ : syracuseStep 5826305 = 4369729) B4369729
theorem B1533725 : Blo 535802 1533725 := bstep (se 3 (by rfl) ⟨287573, by rfl⟩ : syracuseStep 1533725 = 575147) B575147
theorem B10348337 : Blo 535802 10348337 := bstep (se 2 (by rfl) ⟨3880626, by rfl⟩ : syracuseStep 10348337 = 7761253) B7761253
theorem B681787 : Blo 535802 681787 := bstep (se 1 (by rfl) ⟨511340, by rfl⟩ : syracuseStep 681787 = 1022681) B1022681
theorem B4089689 : Blo 535802 4089689 := bstep (se 2 (by rfl) ⟨1533633, by rfl⟩ : syracuseStep 4089689 = 3067267) B3067267
theorem B1533953 : Blo 535802 1533953 := bstep (se 2 (by rfl) ⟨575232, by rfl⟩ : syracuseStep 1533953 = 1150465) B1150465
theorem B1206287 : Blo 535802 1206287 := bstep (se 1 (by rfl) ⟨904715, by rfl⟩ : syracuseStep 1206287 = 1809431) B1809431
theorem B1206305 : Blo 535802 1206305 := bstep (se 2 (by rfl) ⟨452364, by rfl⟩ : syracuseStep 1206305 = 904729) B904729
theorem B2713661 : Blo 535802 2713661 := bstep (se 3 (by rfl) ⟨508811, by rfl⟩ : syracuseStep 2713661 = 1017623) B1017623
theorem B682283 : Blo 535802 682283 := bstep (se 1 (by rfl) ⟨511712, by rfl⟩ : syracuseStep 682283 = 1023425) B1023425
theorem B1534295 : Blo 535802 1534295 := bstep (se 1 (by rfl) ⟨1150721, by rfl⟩ : syracuseStep 1534295 = 2301443) B2301443
theorem B1206647 : Blo 535802 1206647 := bstep (se 1 (by rfl) ⟨904985, by rfl⟩ : syracuseStep 1206647 = 1809971) B1809971
theorem B1534409 : Blo 535802 1534409 := bstep (se 2 (by rfl) ⟨575403, by rfl⟩ : syracuseStep 1534409 = 1150807) B1150807
theorem B1206827 : Blo 535802 1206827 := bstep (se 1 (by rfl) ⟨905120, by rfl⟩ : syracuseStep 1206827 = 1810241) B1810241
theorem B4582007 : Blo 535802 4582007 := bstep (se 1 (by rfl) ⟨3436505, by rfl⟩ : syracuseStep 4582007 = 6873011) B6873011
theorem B682759 : Blo 535802 682759 := bstep (se 1 (by rfl) ⟨512069, by rfl⟩ : syracuseStep 682759 = 1024139) B1024139
theorem B4090661 : Blo 535802 4090661 := bstep (se 4 (by rfl) ⟨383499, by rfl⟩ : syracuseStep 4090661 = 766999) B766999
theorem B6548273 : Blo 535802 6548273 := bstep (se 2 (by rfl) ⟨2455602, by rfl⟩ : syracuseStep 6548273 = 4911205) B4911205
theorem B5499737 : Blo 535802 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B1207187 : Blo 535802 1207187 := bstep (se 1 (by rfl) ⟨905390, by rfl⟩ : syracuseStep 1207187 = 1810781) B1810781
theorem B1207241 : Blo 535802 1207241 := bstep (se 2 (by rfl) ⟨452715, by rfl⟩ : syracuseStep 1207241 = 905431) B905431
theorem B5893181 : Blo 535802 5893181 := bstep (se 3 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 5893181 = 2209943) B2209943
theorem B1207943 : Blo 535802 1207943 := bstep (se 1 (by rfl) ⟨905957, by rfl⟩ : syracuseStep 1207943 = 1811915) B1811915
theorem B2715443 : Blo 535802 2715443 := bstep (se 1 (by rfl) ⟨2036582, by rfl⟩ : syracuseStep 2715443 = 4073165) B4073165
theorem B1208123 : Blo 535802 1208123 := bstep (se 1 (by rfl) ⟨906092, by rfl⟩ : syracuseStep 1208123 = 1812185) B1812185
theorem B1208249 : Blo 535802 1208249 := bstep (se 2 (by rfl) ⟨453093, by rfl⟩ : syracuseStep 1208249 = 906187) B906187
theorem B815111 : Blo 535802 815111 := bstep (se 1 (by rfl) ⟨611333, by rfl⟩ : syracuseStep 815111 = 1222667) B1222667
theorem B2715767 : Blo 535802 2715767 := bstep (se 1 (by rfl) ⟨2036825, by rfl⟩ : syracuseStep 2715767 = 4073651) B4073651
theorem B1536185 : Blo 535802 1536185 := bstep (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) B1152139
theorem B2355437 : Blo 535802 2355437 := bstep (se 3 (by rfl) ⟨441644, by rfl⟩ : syracuseStep 2355437 = 883289) B883289
theorem B1208591 : Blo 535802 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B1208609 : Blo 535802 1208609 := bstep (se 2 (by rfl) ⟨453228, by rfl⟩ : syracuseStep 1208609 = 906457) B906457
theorem B16576913 : Blo 535802 16576913 := bstep (se 2 (by rfl) ⟨6216342, by rfl⟩ : syracuseStep 16576913 = 12432685) B12432685
theorem B3502595 : Blo 535802 3502595 := bstep (se 1 (by rfl) ⟨2626946, by rfl⟩ : syracuseStep 3502595 = 5253893) B5253893
theorem B1208951 : Blo 535802 1208951 := bstep (se 1 (by rfl) ⟨906713, by rfl⟩ : syracuseStep 1208951 = 1813427) B1813427
theorem B1209131 : Blo 535802 1209131 := bstep (se 1 (by rfl) ⟨906848, by rfl⟩ : syracuseStep 1209131 = 1813697) B1813697
theorem B2716739 : Blo 535802 2716739 := bstep (se 1 (by rfl) ⟨2037554, by rfl⟩ : syracuseStep 2716739 = 4075109) B4075109
theorem B1209491 : Blo 535802 1209491 := bstep (se 1 (by rfl) ⟨907118, by rfl⟩ : syracuseStep 1209491 = 1814237) B1814237
theorem B1209545 : Blo 535802 1209545 := bstep (se 2 (by rfl) ⟨453579, by rfl⟩ : syracuseStep 1209545 = 907159) B907159
theorem B7337351 : Blo 535802 7337351 := bstep (se 1 (by rfl) ⟨5503013, by rfl⟩ : syracuseStep 7337351 = 11006027) B11006027
theorem B2717063 : Blo 535802 2717063 := bstep (se 1 (by rfl) ⟨2037797, by rfl⟩ : syracuseStep 2717063 = 4075595) B4075595
theorem B816527 : Blo 535802 816527 := bstep (se 1 (by rfl) ⟨612395, by rfl⟩ : syracuseStep 816527 = 1224791) B1224791
theorem B2913803 : Blo 535802 2913803 := bstep (se 1 (by rfl) ⟨2185352, by rfl⟩ : syracuseStep 2913803 = 4370705) B4370705
theorem B3667801 : Blo 535802 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B1210247 : Blo 535802 1210247 := bstep (se 1 (by rfl) ⟨907685, by rfl⟩ : syracuseStep 1210247 = 1815371) B1815371
theorem B1210427 : Blo 535802 1210427 := bstep (se 1 (by rfl) ⟨907820, by rfl⟩ : syracuseStep 1210427 = 1815641) B1815641
theorem B1210553 : Blo 535802 1210553 := bstep (se 2 (by rfl) ⟨453957, by rfl⟩ : syracuseStep 1210553 = 907915) B907915
theorem B1210895 : Blo 535802 1210895 := bstep (se 1 (by rfl) ⟨908171, by rfl⟩ : syracuseStep 1210895 = 1816343) B1816343
theorem B1210913 : Blo 535802 1210913 := bstep (se 2 (by rfl) ⟨454092, by rfl⟩ : syracuseStep 1210913 = 908185) B908185
theorem B26114831 : Blo 535802 26114831 := bstep (se 1 (by rfl) ⟨19586123, by rfl⟩ : syracuseStep 26114831 = 39172247) B39172247
theorem B1211255 : Blo 535802 1211255 := bstep (se 1 (by rfl) ⟨908441, by rfl⟩ : syracuseStep 1211255 = 1816883) B1816883
theorem B1145801 : Blo 535802 1145801 := bstep (se 2 (by rfl) ⟨429675, by rfl⟩ : syracuseStep 1145801 = 859351) B859351
theorem B1211435 : Blo 535802 1211435 := bstep (se 1 (by rfl) ⟨908576, by rfl⟩ : syracuseStep 1211435 = 1817153) B1817153
theorem B1211795 : Blo 535802 1211795 := bstep (se 1 (by rfl) ⟨908846, by rfl⟩ : syracuseStep 1211795 = 1817693) B1817693
theorem B1211849 : Blo 535802 1211849 := bstep (se 2 (by rfl) ⟨454443, by rfl⟩ : syracuseStep 1211849 = 908887) B908887
theorem B1769161 : Blo 535802 1769161 := bstep (se 2 (by rfl) ⟨663435, by rfl⟩ : syracuseStep 1769161 = 1326871) B1326871
theorem B4096007 : Blo 535802 4096007 := bstep (se 1 (by rfl) ⟨3072005, by rfl⟩ : syracuseStep 4096007 = 6144011) B6144011
theorem B1212587 : Blo 535802 1212587 := bstep (se 1 (by rfl) ⟨909440, by rfl⟩ : syracuseStep 1212587 = 1818881) B1818881
theorem B2294027 : Blo 535802 2294027 := bstep (se 1 (by rfl) ⟨1720520, by rfl⟩ : syracuseStep 2294027 = 3441041) B3441041
theorem B1638785 : Blo 535802 1638785 := bstep (se 2 (by rfl) ⟨614544, by rfl⟩ : syracuseStep 1638785 = 1229089) B1229089
theorem B1147279 : Blo 535802 1147279 := bstep (se 1 (by rfl) ⟨860459, by rfl⟩ : syracuseStep 1147279 = 1720919) B1720919
theorem B4096493 : Blo 535802 4096493 := bstep (se 3 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 4096493 = 1536185) B1536185
theorem B1213127 : Blo 535802 1213127 := bstep (se 1 (by rfl) ⟨909845, by rfl⟩ : syracuseStep 1213127 = 1819691) B1819691
theorem B2720465 : Blo 535802 2720465 := bstep (se 2 (by rfl) ⟨1020174, by rfl⟩ : syracuseStep 2720465 = 2040349) B2040349
theorem B1934189 : Blo 535802 1934189 := bstep (se 3 (by rfl) ⟨362660, by rfl⟩ : syracuseStep 1934189 = 725321) B725321
theorem B44205101 : Blo 535802 44205101 := bstep (se 3 (by rfl) ⟨8288456, by rfl⟩ : syracuseStep 44205101 = 16576913) B16576913
theorem B1213991 : Blo 535802 1213991 := bstep (se 1 (by rfl) ⟨910493, by rfl⟩ : syracuseStep 1213991 = 1820987) B1820987
theorem B3671639 : Blo 535802 3671639 := bstep (se 1 (by rfl) ⟨2753729, by rfl⟩ : syracuseStep 3671639 = 5507459) B5507459
theorem B1017593 : Blo 535802 1017593 := bstep (se 2 (by rfl) ⟨381597, by rfl⟩ : syracuseStep 1017593 = 763195) B763195
theorem B3442475 : Blo 535802 3442475 := bstep (se 1 (by rfl) ⟨2581856, by rfl⟩ : syracuseStep 3442475 = 5163713) B5163713
theorem B1214315 : Blo 535802 1214315 := bstep (se 1 (by rfl) ⟨910736, by rfl⟩ : syracuseStep 1214315 = 1821473) B1821473
theorem B1640353 : Blo 535802 1640353 := bstep (se 2 (by rfl) ⟨615132, by rfl⟩ : syracuseStep 1640353 = 1230265) B1230265
theorem B1214369 : Blo 535802 1214369 := bstep (se 2 (by rfl) ⟨455388, by rfl⟩ : syracuseStep 1214369 = 910777) B910777
theorem B1017775 : Blo 535802 1017775 := bstep (se 1 (by rfl) ⟨763331, by rfl⟩ : syracuseStep 1017775 = 1526663) B1526663
theorem B3770371 : Blo 535802 3770371 := bstep (se 1 (by rfl) ⟨2827778, by rfl⟩ : syracuseStep 3770371 = 5655557) B5655557
theorem B3278855 : Blo 535802 3278855 := bstep (se 1 (by rfl) ⟨2459141, by rfl⟩ : syracuseStep 3278855 = 4918283) B4918283
theorem B4098437 : Blo 535802 4098437 := bstep (se 4 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 4098437 = 768457) B768457
theorem B691039 : Blo 535802 691039 := bstep (se 1 (by rfl) ⟨518279, by rfl⟩ : syracuseStep 691039 = 1036559) B1036559
theorem B4098923 : Blo 535802 4098923 := bstep (se 1 (by rfl) ⟨3074192, by rfl⟩ : syracuseStep 4098923 = 6148385) B6148385
theorem B2722895 : Blo 535802 2722895 := bstep (se 1 (by rfl) ⟨2042171, by rfl⟩ : syracuseStep 2722895 = 4084343) B4084343
theorem B1019051 : Blo 535802 1019051 := bstep (se 1 (by rfl) ⟨764288, by rfl⟩ : syracuseStep 1019051 = 1528577) B1528577
theorem B1019279 : Blo 535802 1019279 := bstep (se 1 (by rfl) ⟨764459, by rfl⟩ : syracuseStep 1019279 = 1528919) B1528919
theorem B23301755 : Blo 535802 23301755 := bstep (se 1 (by rfl) ⟨17476316, by rfl⟩ : syracuseStep 23301755 = 34952633) B34952633
theorem B19566269 : Blo 535802 19566269 := bstep (se 3 (by rfl) ⟨3668675, by rfl⟩ : syracuseStep 19566269 = 7337351) B7337351
theorem B2723543 : Blo 535802 2723543 := bstep (se 1 (by rfl) ⟨2042657, by rfl⟩ : syracuseStep 2723543 = 4085315) B4085315
theorem B2035793 : Blo 535802 2035793 := bstep (se 2 (by rfl) ⟨763422, by rfl⟩ : syracuseStep 2035793 = 1526845) B1526845
theorem B2036249 : Blo 535802 2036249 := bstep (se 2 (by rfl) ⟨763593, by rfl⟩ : syracuseStep 2036249 = 1527187) B1527187
theorem B4592153 : Blo 535802 4592153 := bstep (se 2 (by rfl) ⟨1722057, by rfl⟩ : syracuseStep 4592153 = 3444115) B3444115
theorem B2298401 : Blo 535802 2298401 := bstep (se 2 (by rfl) ⟨861900, by rfl⟩ : syracuseStep 2298401 = 1723801) B1723801
theorem B922151 : Blo 535802 922151 := bstep (se 1 (by rfl) ⟨691613, by rfl⟩ : syracuseStep 922151 = 1383227) B1383227
theorem B1020539 : Blo 535802 1020539 := bstep (se 1 (by rfl) ⟨765404, by rfl⟩ : syracuseStep 1020539 = 1530809) B1530809
theorem B3740489 : Blo 535802 3740489 := bstep (se 2 (by rfl) ⟨1402683, by rfl⟩ : syracuseStep 3740489 = 2805367) B2805367
theorem B8753993 : Blo 535802 8753993 := bstep (se 2 (by rfl) ⟨3282747, by rfl⟩ : syracuseStep 8753993 = 6565495) B6565495
theorem B1021025 : Blo 535802 1021025 := bstep (se 2 (by rfl) ⟨382884, by rfl⟩ : syracuseStep 1021025 = 765769) B765769
theorem B2954393 : Blo 535802 2954393 := bstep (se 2 (by rfl) ⟨1107897, by rfl⟩ : syracuseStep 2954393 = 2215795) B2215795
theorem B1021177 : Blo 535802 1021177 := bstep (se 2 (by rfl) ⟨382941, by rfl⟩ : syracuseStep 1021177 = 765883) B765883
theorem B2037433 : Blo 535802 2037433 := bstep (se 2 (by rfl) ⟨764037, by rfl⟩ : syracuseStep 2037433 = 1528075) B1528075
theorem B6887105 : Blo 535802 6887105 := bstep (se 2 (by rfl) ⟨2582664, by rfl⟩ : syracuseStep 6887105 = 5165329) B5165329
theorem B3872555 : Blo 535802 3872555 := bstep (se 1 (by rfl) ⟨2904416, by rfl⟩ : syracuseStep 3872555 = 5808833) B5808833
theorem B1808783 : Blo 535802 1808783 := bstep (se 1 (by rfl) ⟨1356587, by rfl⟩ : syracuseStep 1808783 = 2713175) B2713175
theorem B1022483 : Blo 535802 1022483 := bstep (se 1 (by rfl) ⟨766862, by rfl⟩ : syracuseStep 1022483 = 1533725) B1533725
theorem B2726459 : Blo 535802 2726459 := bstep (se 1 (by rfl) ⟨2044844, by rfl⟩ : syracuseStep 2726459 = 4089689) B4089689
theorem B1022635 : Blo 535802 1022635 := bstep (se 1 (by rfl) ⟨766976, by rfl⟩ : syracuseStep 1022635 = 1533953) B1533953
theorem B1809107 : Blo 535802 1809107 := bstep (se 1 (by rfl) ⟨1356830, by rfl⟩ : syracuseStep 1809107 = 2713661) B2713661
theorem B1022863 : Blo 535802 1022863 := bstep (se 1 (by rfl) ⟨767147, by rfl⟩ : syracuseStep 1022863 = 1534295) B1534295
theorem B1022939 : Blo 535802 1022939 := bstep (se 1 (by rfl) ⟨767204, by rfl⟩ : syracuseStep 1022939 = 1534409) B1534409
theorem B3054671 : Blo 535802 3054671 := bstep (se 1 (by rfl) ⟨2291003, by rfl⟩ : syracuseStep 3054671 = 4582007) B4582007
theorem B4136129 : Blo 535802 4136129 := bstep (se 2 (by rfl) ⟨1551048, by rfl⟩ : syracuseStep 4136129 = 3102097) B3102097
theorem B2727107 : Blo 535802 2727107 := bstep (se 1 (by rfl) ⟨2045330, by rfl⟩ : syracuseStep 2727107 = 4090661) B4090661
theorem B4365515 : Blo 535802 4365515 := bstep (se 1 (by rfl) ⟨3274136, by rfl⟩ : syracuseStep 4365515 = 6548273) B6548273
theorem B2039165 : Blo 535802 2039165 := bstep (se 3 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 2039165 = 764687) B764687
theorem B4890401 : Blo 535802 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B1810295 : Blo 535802 1810295 := bstep (se 1 (by rfl) ⟨1357721, by rfl⟩ : syracuseStep 1810295 = 2715443) B2715443
theorem B1810511 : Blo 535802 1810511 := bstep (se 1 (by rfl) ⟨1357883, by rfl⟩ : syracuseStep 1810511 = 2715767) B2715767
theorem B2335063 : Blo 535802 2335063 := bstep (se 1 (by rfl) ⟨1751297, by rfl⟩ : syracuseStep 2335063 = 3502595) B3502595
theorem B1548649 : Blo 535802 1548649 := bstep (se 2 (by rfl) ⟨580743, by rfl⟩ : syracuseStep 1548649 = 1161487) B1161487
theorem B1810889 : Blo 535802 1810889 := bstep (se 2 (by rfl) ⟨679083, by rfl⟩ : syracuseStep 1810889 = 1358167) B1358167
theorem B1811159 : Blo 535802 1811159 := bstep (se 1 (by rfl) ⟨1358369, by rfl⟩ : syracuseStep 1811159 = 2716739) B2716739
theorem B1450847 : Blo 535802 1450847 := bstep (se 1 (by rfl) ⟨1088135, by rfl⟩ : syracuseStep 1450847 = 2176271) B2176271
theorem B1811375 : Blo 535802 1811375 := bstep (se 1 (by rfl) ⟨1358531, by rfl⟩ : syracuseStep 1811375 = 2717063) B2717063
theorem B3875759 : Blo 535802 3875759 := bstep (se 1 (by rfl) ⟨2906819, by rfl⟩ : syracuseStep 3875759 = 5813639) B5813639
theorem B1942535 : Blo 535802 1942535 := bstep (se 1 (by rfl) ⟨1456901, by rfl⟩ : syracuseStep 1942535 = 2913803) B2913803
theorem B3057061 : Blo 535802 3057061 := bstep (se 4 (by rfl) ⟨286599, by rfl⟩ : syracuseStep 3057061 = 573199) B573199
theorem B2041307 : Blo 535802 2041307 := bstep (se 1 (by rfl) ⟨1530980, by rfl⟩ : syracuseStep 2041307 = 3061961) B3061961
theorem B1844795 : Blo 535802 1844795 := bstep (se 1 (by rfl) ⟨1383596, by rfl⟩ : syracuseStep 1844795 = 2767193) B2767193
theorem B17409887 : Blo 535802 17409887 := bstep (se 1 (by rfl) ⟨13057415, by rfl⟩ : syracuseStep 17409887 = 26114831) B26114831
theorem B993211 : Blo 535802 993211 := bstep (se 1 (by rfl) ⟨744908, by rfl⟩ : syracuseStep 993211 = 1489817) B1489817
theorem B763867 : Blo 535802 763867 := bstep (se 1 (by rfl) ⟨572900, by rfl⟩ : syracuseStep 763867 = 1145801) B1145801
theorem B764425 : Blo 535802 764425 := bstep (se 2 (by rfl) ⟨286659, by rfl⟩ : syracuseStep 764425 = 573319) B573319
theorem B2042567 : Blo 535802 2042567 := bstep (se 1 (by rfl) ⟨1531925, by rfl⟩ : syracuseStep 2042567 = 3063851) B3063851
theorem B1846273 : Blo 535802 1846273 := bstep (se 2 (by rfl) ⟨692352, by rfl⟩ : syracuseStep 1846273 = 1384705) B1384705
theorem B2174147 : Blo 535802 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B2305219 : Blo 535802 2305219 := bstep (se 1 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 2305219 = 3457829) B3457829
theorem B1813751 : Blo 535802 1813751 := bstep (se 1 (by rfl) ⟨1360313, by rfl⟩ : syracuseStep 1813751 = 2720627) B2720627
theorem B535847 : Blo 535802 535847 := bstep (se 1 (by rfl) ⟨401885, by rfl⟩ : syracuseStep 535847 = 803771) B803771
theorem B535887 : Blo 535802 535887 := bstep (se 1 (by rfl) ⟨401915, by rfl⟩ : syracuseStep 535887 = 803831) B803831
theorem B8858969 : Blo 535802 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B535903 : Blo 535802 535903 := bstep (se 1 (by rfl) ⟨401927, by rfl⟩ : syracuseStep 535903 = 803855) B803855
theorem B535931 : Blo 535802 535931 := bstep (se 1 (by rfl) ⟨401948, by rfl⟩ : syracuseStep 535931 = 803897) B803897
theorem B2043265 : Blo 535802 2043265 := bstep (se 2 (by rfl) ⟨766224, by rfl⟩ : syracuseStep 2043265 = 1532449) B1532449
theorem B535983 : Blo 535802 535983 := bstep (se 1 (by rfl) ⟨401987, by rfl⟩ : syracuseStep 535983 = 803975) B803975
theorem B536007 : Blo 535802 536007 := bstep (se 1 (by rfl) ⟨402005, by rfl⟩ : syracuseStep 536007 = 804011) B804011
theorem B536027 : Blo 535802 536027 := bstep (se 1 (by rfl) ⟨402020, by rfl⟩ : syracuseStep 536027 = 804041) B804041
theorem B1551881 : Blo 535802 1551881 := bstep (se 2 (by rfl) ⟨581955, by rfl⟩ : syracuseStep 1551881 = 1163911) B1163911
theorem B536103 : Blo 535802 536103 := bstep (se 1 (by rfl) ⟨402077, by rfl⟩ : syracuseStep 536103 = 804155) B804155
theorem B1814075 : Blo 535802 1814075 := bstep (se 1 (by rfl) ⟨1360556, by rfl⟩ : syracuseStep 1814075 = 2721113) B2721113
theorem B536143 : Blo 535802 536143 := bstep (se 1 (by rfl) ⟨402107, by rfl⟩ : syracuseStep 536143 = 804215) B804215
theorem B536159 : Blo 535802 536159 := bstep (se 1 (by rfl) ⟨402119, by rfl⟩ : syracuseStep 536159 = 804239) B804239
theorem B536187 : Blo 535802 536187 := bstep (se 1 (by rfl) ⟨402140, by rfl⟩ : syracuseStep 536187 = 804281) B804281
theorem B2731643 : Blo 535802 2731643 := bstep (se 1 (by rfl) ⟨2048732, by rfl⟩ : syracuseStep 2731643 = 4097465) B4097465
theorem B2043539 : Blo 535802 2043539 := bstep (se 1 (by rfl) ⟨1532654, by rfl⟩ : syracuseStep 2043539 = 3065309) B3065309
theorem B536239 : Blo 535802 536239 := bstep (se 1 (by rfl) ⟨402179, by rfl⟩ : syracuseStep 536239 = 804359) B804359
theorem B536263 : Blo 535802 536263 := bstep (se 1 (by rfl) ⟨402197, by rfl⟩ : syracuseStep 536263 = 804395) B804395
theorem B536283 : Blo 535802 536283 := bstep (se 1 (by rfl) ⟨402212, by rfl⟩ : syracuseStep 536283 = 804425) B804425
theorem B3452705 : Blo 535802 3452705 := bstep (se 2 (by rfl) ⟨1294764, by rfl⟩ : syracuseStep 3452705 = 2589529) B2589529
theorem B536359 : Blo 535802 536359 := bstep (se 1 (by rfl) ⟨402269, by rfl⟩ : syracuseStep 536359 = 804539) B804539
theorem B2797379 : Blo 535802 2797379 := bstep (se 1 (by rfl) ⟨2098034, by rfl⟩ : syracuseStep 2797379 = 4196069) B4196069
theorem B1814345 : Blo 535802 1814345 := bstep (se 2 (by rfl) ⟨680379, by rfl⟩ : syracuseStep 1814345 = 1360759) B1360759
theorem B536399 : Blo 535802 536399 := bstep (se 1 (by rfl) ⟨402299, by rfl⟩ : syracuseStep 536399 = 804599) B804599
theorem B536415 : Blo 535802 536415 := bstep (se 1 (by rfl) ⟨402311, by rfl⟩ : syracuseStep 536415 = 804623) B804623
theorem B536443 : Blo 535802 536443 := bstep (se 1 (by rfl) ⟨402332, by rfl⟩ : syracuseStep 536443 = 804665) B804665
theorem B6631303 : Blo 535802 6631303 := bstep (se 1 (by rfl) ⟨4973477, by rfl⟩ : syracuseStep 6631303 = 9946955) B9946955
theorem B536495 : Blo 535802 536495 := bstep (se 1 (by rfl) ⟨402371, by rfl⟩ : syracuseStep 536495 = 804743) B804743
theorem B536519 : Blo 535802 536519 := bstep (se 1 (by rfl) ⟨402389, by rfl⟩ : syracuseStep 536519 = 804779) B804779
theorem B536539 : Blo 535802 536539 := bstep (se 1 (by rfl) ⟨402404, by rfl⟩ : syracuseStep 536539 = 804809) B804809
theorem B536615 : Blo 535802 536615 := bstep (se 1 (by rfl) ⟨402461, by rfl⟩ : syracuseStep 536615 = 804923) B804923
theorem B536655 : Blo 535802 536655 := bstep (se 1 (by rfl) ⟨402491, by rfl⟩ : syracuseStep 536655 = 804983) B804983
theorem B536671 : Blo 535802 536671 := bstep (se 1 (by rfl) ⟨402503, by rfl⟩ : syracuseStep 536671 = 805007) B805007
theorem B536699 : Blo 535802 536699 := bstep (se 1 (by rfl) ⟨402524, by rfl⟩ : syracuseStep 536699 = 805049) B805049
theorem B536751 : Blo 535802 536751 := bstep (se 1 (by rfl) ⟨402563, by rfl⟩ : syracuseStep 536751 = 805127) B805127
theorem B536775 : Blo 535802 536775 := bstep (se 1 (by rfl) ⟨402581, by rfl⟩ : syracuseStep 536775 = 805163) B805163
theorem B536795 : Blo 535802 536795 := bstep (se 1 (by rfl) ⟨402596, by rfl⟩ : syracuseStep 536795 = 805193) B805193
theorem B536871 : Blo 535802 536871 := bstep (se 1 (by rfl) ⟨402653, by rfl⟩ : syracuseStep 536871 = 805307) B805307
theorem B536911 : Blo 535802 536911 := bstep (se 1 (by rfl) ⟨402683, by rfl⟩ : syracuseStep 536911 = 805367) B805367
theorem B536927 : Blo 535802 536927 := bstep (se 1 (by rfl) ⟨402695, by rfl⟩ : syracuseStep 536927 = 805391) B805391
theorem B536955 : Blo 535802 536955 := bstep (se 1 (by rfl) ⟨402716, by rfl⟩ : syracuseStep 536955 = 805433) B805433
theorem B537007 : Blo 535802 537007 := bstep (se 1 (by rfl) ⟨402755, by rfl⟩ : syracuseStep 537007 = 805511) B805511
theorem B537031 : Blo 535802 537031 := bstep (se 1 (by rfl) ⟨402773, by rfl⟩ : syracuseStep 537031 = 805547) B805547
theorem B537051 : Blo 535802 537051 := bstep (se 1 (by rfl) ⟨402788, by rfl⟩ : syracuseStep 537051 = 805577) B805577
theorem B537127 : Blo 535802 537127 := bstep (se 1 (by rfl) ⟨402845, by rfl⟩ : syracuseStep 537127 = 805691) B805691
theorem B537167 : Blo 535802 537167 := bstep (se 1 (by rfl) ⟨402875, by rfl⟩ : syracuseStep 537167 = 805751) B805751
theorem B537183 : Blo 535802 537183 := bstep (se 1 (by rfl) ⟨402887, by rfl⟩ : syracuseStep 537183 = 805775) B805775
theorem B1356385 : Blo 535802 1356385 := bstep (se 2 (by rfl) ⟨508644, by rfl⟩ : syracuseStep 1356385 = 1017289) B1017289
theorem B537211 : Blo 535802 537211 := bstep (se 1 (by rfl) ⟨402908, by rfl⟩ : syracuseStep 537211 = 805817) B805817
theorem B537263 : Blo 535802 537263 := bstep (se 1 (by rfl) ⟨402947, by rfl⟩ : syracuseStep 537263 = 805895) B805895
theorem B537287 : Blo 535802 537287 := bstep (se 1 (by rfl) ⟨402965, by rfl⟩ : syracuseStep 537287 = 805931) B805931
theorem B537307 : Blo 535802 537307 := bstep (se 1 (by rfl) ⟨402980, by rfl⟩ : syracuseStep 537307 = 805961) B805961
theorem B537383 : Blo 535802 537383 := bstep (se 1 (by rfl) ⟨403037, by rfl⟩ : syracuseStep 537383 = 806075) B806075
theorem B537423 : Blo 535802 537423 := bstep (se 1 (by rfl) ⟨403067, by rfl⟩ : syracuseStep 537423 = 806135) B806135
theorem B537439 : Blo 535802 537439 := bstep (se 1 (by rfl) ⟨403079, by rfl⟩ : syracuseStep 537439 = 806159) B806159
theorem B537467 : Blo 535802 537467 := bstep (se 1 (by rfl) ⟨403100, by rfl⟩ : syracuseStep 537467 = 806201) B806201
theorem B14398361 : Blo 535802 14398361 := bstep (se 2 (by rfl) ⟨5399385, by rfl⟩ : syracuseStep 14398361 = 10798771) B10798771
theorem B537519 : Blo 535802 537519 := bstep (se 1 (by rfl) ⟨403139, by rfl⟩ : syracuseStep 537519 = 806279) B806279
theorem B766903 : Blo 535802 766903 := bstep (se 1 (by rfl) ⟨575177, by rfl⟩ : syracuseStep 766903 = 1150355) B1150355
theorem B1815479 : Blo 535802 1815479 := bstep (se 1 (by rfl) ⟨1361609, by rfl⟩ : syracuseStep 1815479 = 2723219) B2723219
theorem B537543 : Blo 535802 537543 := bstep (se 1 (by rfl) ⟨403157, by rfl⟩ : syracuseStep 537543 = 806315) B806315
theorem B537563 : Blo 535802 537563 := bstep (se 1 (by rfl) ⟨403172, by rfl⟩ : syracuseStep 537563 = 806345) B806345
theorem B603175 : Blo 535802 603175 := bstep (se 1 (by rfl) ⟨452381, by rfl⟩ : syracuseStep 603175 = 904763) B904763
theorem B537639 : Blo 535802 537639 := bstep (se 1 (by rfl) ⟨403229, by rfl⟩ : syracuseStep 537639 = 806459) B806459
theorem B537679 : Blo 535802 537679 := bstep (se 1 (by rfl) ⟨403259, by rfl⟩ : syracuseStep 537679 = 806519) B806519
theorem B537695 : Blo 535802 537695 := bstep (se 1 (by rfl) ⟨403271, by rfl⟩ : syracuseStep 537695 = 806543) B806543
theorem B537723 : Blo 535802 537723 := bstep (se 1 (by rfl) ⟨403292, by rfl⟩ : syracuseStep 537723 = 806585) B806585
theorem B537775 : Blo 535802 537775 := bstep (se 1 (by rfl) ⟨403331, by rfl⟩ : syracuseStep 537775 = 806663) B806663
theorem B537799 : Blo 535802 537799 := bstep (se 1 (by rfl) ⟨403349, by rfl⟩ : syracuseStep 537799 = 806699) B806699
theorem B537819 : Blo 535802 537819 := bstep (se 1 (by rfl) ⟨403364, by rfl⟩ : syracuseStep 537819 = 806729) B806729
theorem B2045195 : Blo 535802 2045195 := bstep (se 1 (by rfl) ⟨1533896, by rfl⟩ : syracuseStep 2045195 = 3067793) B3067793
theorem B537895 : Blo 535802 537895 := bstep (se 1 (by rfl) ⟨403421, by rfl⟩ : syracuseStep 537895 = 806843) B806843
theorem B537935 : Blo 535802 537935 := bstep (se 1 (by rfl) ⟨403451, by rfl⟩ : syracuseStep 537935 = 806903) B806903
theorem B537951 : Blo 535802 537951 := bstep (se 1 (by rfl) ⟨403463, by rfl⟩ : syracuseStep 537951 = 806927) B806927
theorem B537979 : Blo 535802 537979 := bstep (se 1 (by rfl) ⟨403484, by rfl⟩ : syracuseStep 537979 = 806969) B806969
theorem B538031 : Blo 535802 538031 := bstep (se 1 (by rfl) ⟨403523, by rfl⟩ : syracuseStep 538031 = 807047) B807047
theorem B538055 : Blo 535802 538055 := bstep (se 1 (by rfl) ⟨403541, by rfl⟩ : syracuseStep 538055 = 807083) B807083
theorem B538075 : Blo 535802 538075 := bstep (se 1 (by rfl) ⟨403556, by rfl⟩ : syracuseStep 538075 = 807113) B807113
theorem B5813765 : Blo 535802 5813765 := bstep (se 4 (by rfl) ⟨545040, by rfl⟩ : syracuseStep 5813765 = 1090081) B1090081
theorem B1816073 : Blo 535802 1816073 := bstep (se 2 (by rfl) ⟨681027, by rfl⟩ : syracuseStep 1816073 = 1362055) B1362055
theorem B1357337 : Blo 535802 1357337 := bstep (se 2 (by rfl) ⟨509001, by rfl⟩ : syracuseStep 1357337 = 1018003) B1018003
theorem B538151 : Blo 535802 538151 := bstep (se 1 (by rfl) ⟨403613, by rfl⟩ : syracuseStep 538151 = 807227) B807227
theorem B538191 : Blo 535802 538191 := bstep (se 1 (by rfl) ⟨403643, by rfl⟩ : syracuseStep 538191 = 807287) B807287
theorem B538207 : Blo 535802 538207 := bstep (se 1 (by rfl) ⟨403655, by rfl⟩ : syracuseStep 538207 = 807311) B807311
theorem B538235 : Blo 535802 538235 := bstep (se 1 (by rfl) ⟨403676, by rfl⟩ : syracuseStep 538235 = 807353) B807353
theorem B538287 : Blo 535802 538287 := bstep (se 1 (by rfl) ⟨403715, by rfl⟩ : syracuseStep 538287 = 807431) B807431
theorem B15513281 : Blo 535802 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B538311 : Blo 535802 538311 := bstep (se 1 (by rfl) ⟨403733, by rfl⟩ : syracuseStep 538311 = 807467) B807467
theorem B538331 : Blo 535802 538331 := bstep (se 1 (by rfl) ⟨403748, by rfl⟩ : syracuseStep 538331 = 807497) B807497
theorem B538407 : Blo 535802 538407 := bstep (se 1 (by rfl) ⟨403805, by rfl⟩ : syracuseStep 538407 = 807611) B807611
theorem B538447 : Blo 535802 538447 := bstep (se 1 (by rfl) ⟨403835, by rfl⟩ : syracuseStep 538447 = 807671) B807671
theorem B1718111 : Blo 535802 1718111 := bstep (se 1 (by rfl) ⟨1288583, by rfl⟩ : syracuseStep 1718111 = 2577167) B2577167
theorem B538463 : Blo 535802 538463 := bstep (se 1 (by rfl) ⟨403847, by rfl⟩ : syracuseStep 538463 = 807695) B807695
theorem B538491 : Blo 535802 538491 := bstep (se 1 (by rfl) ⟨403868, by rfl⟩ : syracuseStep 538491 = 807737) B807737
theorem B538543 : Blo 535802 538543 := bstep (se 1 (by rfl) ⟨403907, by rfl⟩ : syracuseStep 538543 = 807815) B807815
theorem B538567 : Blo 535802 538567 := bstep (se 1 (by rfl) ⟨403925, by rfl⟩ : syracuseStep 538567 = 807851) B807851
theorem B538587 : Blo 535802 538587 := bstep (se 1 (by rfl) ⟨403940, by rfl⟩ : syracuseStep 538587 = 807881) B807881
theorem B1357843 : Blo 535802 1357843 := bstep (se 1 (by rfl) ⟨1018382, by rfl⟩ : syracuseStep 1357843 = 2036765) B2036765
theorem B538663 : Blo 535802 538663 := bstep (se 1 (by rfl) ⟨403997, by rfl⟩ : syracuseStep 538663 = 807995) B807995
theorem B538703 : Blo 535802 538703 := bstep (se 1 (by rfl) ⟨404027, by rfl⟩ : syracuseStep 538703 = 808055) B808055
theorem B14727257 : Blo 535802 14727257 := bstep (se 2 (by rfl) ⟨5522721, by rfl⟩ : syracuseStep 14727257 = 11045443) B11045443
theorem B538719 : Blo 535802 538719 := bstep (se 1 (by rfl) ⟨404039, by rfl⟩ : syracuseStep 538719 = 808079) B808079
theorem B538747 : Blo 535802 538747 := bstep (se 1 (by rfl) ⟨404060, by rfl⟩ : syracuseStep 538747 = 808121) B808121
theorem B538799 : Blo 535802 538799 := bstep (se 1 (by rfl) ⟨404099, by rfl⟩ : syracuseStep 538799 = 808199) B808199
theorem B538823 : Blo 535802 538823 := bstep (se 1 (by rfl) ⟨404117, by rfl⟩ : syracuseStep 538823 = 808235) B808235
theorem B538843 : Blo 535802 538843 := bstep (se 1 (by rfl) ⟨404132, by rfl⟩ : syracuseStep 538843 = 808265) B808265
theorem B538919 : Blo 535802 538919 := bstep (se 1 (by rfl) ⟨404189, by rfl⟩ : syracuseStep 538919 = 808379) B808379
theorem B538959 : Blo 535802 538959 := bstep (se 1 (by rfl) ⟨404219, by rfl⟩ : syracuseStep 538959 = 808439) B808439
theorem B538975 : Blo 535802 538975 := bstep (se 1 (by rfl) ⟨404231, by rfl⟩ : syracuseStep 538975 = 808463) B808463
theorem B1816937 : Blo 535802 1816937 := bstep (se 2 (by rfl) ⟨681351, by rfl⟩ : syracuseStep 1816937 = 1362703) B1362703
theorem B768361 : Blo 535802 768361 := bstep (se 2 (by rfl) ⟨288135, by rfl⟩ : syracuseStep 768361 = 576271) B576271
theorem B539003 : Blo 535802 539003 := bstep (se 1 (by rfl) ⟨404252, by rfl⟩ : syracuseStep 539003 = 808505) B808505
theorem B2177405 : Blo 535802 2177405 := bstep (se 3 (by rfl) ⟨408263, by rfl⟩ : syracuseStep 2177405 = 816527) B816527
theorem B539055 : Blo 535802 539055 := bstep (se 1 (by rfl) ⟨404291, by rfl⟩ : syracuseStep 539055 = 808583) B808583
theorem B539079 : Blo 535802 539079 := bstep (se 1 (by rfl) ⟨404309, by rfl⟩ : syracuseStep 539079 = 808619) B808619
theorem B539099 : Blo 535802 539099 := bstep (se 1 (by rfl) ⟨404324, by rfl⟩ : syracuseStep 539099 = 808649) B808649
theorem B4372973 : Blo 535802 4372973 := bstep (se 3 (by rfl) ⟨819932, by rfl⟩ : syracuseStep 4372973 = 1639865) B1639865
theorem B539175 : Blo 535802 539175 := bstep (se 1 (by rfl) ⟨404381, by rfl⟩ : syracuseStep 539175 = 808763) B808763
theorem B539215 : Blo 535802 539215 := bstep (se 1 (by rfl) ⟨404411, by rfl⟩ : syracuseStep 539215 = 808823) B808823
theorem B539231 : Blo 535802 539231 := bstep (se 1 (by rfl) ⟨404423, by rfl⟩ : syracuseStep 539231 = 808847) B808847
theorem B604795 : Blo 535802 604795 := bstep (se 1 (by rfl) ⟨453596, by rfl⟩ : syracuseStep 604795 = 907193) B907193
theorem B539259 : Blo 535802 539259 := bstep (se 1 (by rfl) ⟨404444, by rfl⟩ : syracuseStep 539259 = 808889) B808889
theorem B539311 : Blo 535802 539311 := bstep (se 1 (by rfl) ⟨404483, by rfl⟩ : syracuseStep 539311 = 808967) B808967
theorem B11057849 : Blo 535802 11057849 := bstep (se 2 (by rfl) ⟨4146693, by rfl⟩ : syracuseStep 11057849 = 8293387) B8293387
theorem B2046653 : Blo 535802 2046653 := bstep (se 3 (by rfl) ⟨383747, by rfl⟩ : syracuseStep 2046653 = 767495) B767495
theorem B539335 : Blo 535802 539335 := bstep (se 1 (by rfl) ⟨404501, by rfl⟩ : syracuseStep 539335 = 809003) B809003
theorem B4373203 : Blo 535802 4373203 := bstep (se 1 (by rfl) ⟨3279902, by rfl⟩ : syracuseStep 4373203 = 6559805) B6559805
theorem B539355 : Blo 535802 539355 := bstep (se 1 (by rfl) ⟨404516, by rfl⟩ : syracuseStep 539355 = 809033) B809033
theorem B539431 : Blo 535802 539431 := bstep (se 1 (by rfl) ⟨404573, by rfl⟩ : syracuseStep 539431 = 809147) B809147
theorem B539471 : Blo 535802 539471 := bstep (se 1 (by rfl) ⟨404603, by rfl⟩ : syracuseStep 539471 = 809207) B809207
theorem B539487 : Blo 535802 539487 := bstep (se 1 (by rfl) ⟨404615, by rfl⟩ : syracuseStep 539487 = 809231) B809231
theorem B539515 : Blo 535802 539515 := bstep (se 1 (by rfl) ⟨404636, by rfl⟩ : syracuseStep 539515 = 809273) B809273
theorem B1719215 : Blo 535802 1719215 := bstep (se 1 (by rfl) ⟨1289411, by rfl⟩ : syracuseStep 1719215 = 2578823) B2578823
theorem B4078511 : Blo 535802 4078511 := bstep (se 1 (by rfl) ⟨3058883, by rfl⟩ : syracuseStep 4078511 = 6117767) B6117767
theorem B539567 : Blo 535802 539567 := bstep (se 1 (by rfl) ⟨404675, by rfl⟩ : syracuseStep 539567 = 809351) B809351
theorem B3062711 : Blo 535802 3062711 := bstep (se 1 (by rfl) ⟨2297033, by rfl⟩ : syracuseStep 3062711 = 4594067) B4594067
theorem B1162171 : Blo 535802 1162171 := bstep (se 1 (by rfl) ⟨871628, by rfl⟩ : syracuseStep 1162171 = 1743257) B1743257
theorem B1817531 : Blo 535802 1817531 := bstep (se 1 (by rfl) ⟨1363148, by rfl⟩ : syracuseStep 1817531 = 2726297) B2726297
theorem B539591 : Blo 535802 539591 := bstep (se 1 (by rfl) ⟨404693, by rfl⟩ : syracuseStep 539591 = 809387) B809387
theorem B539611 : Blo 535802 539611 := bstep (se 1 (by rfl) ⟨404708, by rfl⟩ : syracuseStep 539611 = 809417) B809417
theorem B539687 : Blo 535802 539687 := bstep (se 1 (by rfl) ⟨404765, by rfl⟩ : syracuseStep 539687 = 809531) B809531
theorem B1358927 : Blo 535802 1358927 := bstep (se 1 (by rfl) ⟨1019195, by rfl⟩ : syracuseStep 1358927 = 2038391) B2038391
theorem B605263 : Blo 535802 605263 := bstep (se 1 (by rfl) ⟨453947, by rfl⟩ : syracuseStep 605263 = 907895) B907895
theorem B539727 : Blo 535802 539727 := bstep (se 1 (by rfl) ⟨404795, by rfl⟩ : syracuseStep 539727 = 809591) B809591
theorem B539743 : Blo 535802 539743 := bstep (se 1 (by rfl) ⟨404807, by rfl⟩ : syracuseStep 539743 = 809615) B809615
theorem B539771 : Blo 535802 539771 := bstep (se 1 (by rfl) ⟨404828, by rfl⟩ : syracuseStep 539771 = 809657) B809657
theorem B605659 : Blo 535802 605659 := bstep (se 1 (by rfl) ⟨454244, by rfl⟩ : syracuseStep 605659 = 908489) B908489
theorem B9453095 : Blo 535802 9453095 := bstep (se 1 (by rfl) ⟨7089821, by rfl⟩ : syracuseStep 9453095 = 14179643) B14179643
theorem B3063419 : Blo 535802 3063419 := bstep (se 1 (by rfl) ⟨2297564, by rfl⟩ : syracuseStep 3063419 = 4595129) B4595129
theorem B1031879 : Blo 535802 1031879 := bstep (se 1 (by rfl) ⟨773909, by rfl⟩ : syracuseStep 1031879 = 1547819) B1547819
theorem B3686087 : Blo 535802 3686087 := bstep (se 1 (by rfl) ⟨2764565, by rfl⟩ : syracuseStep 3686087 = 5529131) B5529131
theorem B1457875 : Blo 535802 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B1359575 : Blo 535802 1359575 := bstep (se 1 (by rfl) ⟨1019681, by rfl⟩ : syracuseStep 1359575 = 2039363) B2039363
theorem B3456827 : Blo 535802 3456827 := bstep (se 1 (by rfl) ⟨2592620, by rfl⟩ : syracuseStep 3456827 = 5185241) B5185241
theorem B606127 : Blo 535802 606127 := bstep (se 1 (by rfl) ⟨454595, by rfl⟩ : syracuseStep 606127 = 909191) B909191
theorem B1359929 : Blo 535802 1359929 := bstep (se 2 (by rfl) ⟨509973, by rfl⟩ : syracuseStep 1359929 = 1019947) B1019947
theorem B606559 : Blo 535802 606559 := bstep (se 1 (by rfl) ⟨454919, by rfl⟩ : syracuseStep 606559 = 909839) B909839
theorem B3064169 : Blo 535802 3064169 := bstep (se 2 (by rfl) ⟨1149063, by rfl⟩ : syracuseStep 3064169 = 2298127) B2298127
theorem B1294697 : Blo 535802 1294697 := bstep (se 2 (by rfl) ⟨485511, by rfl⟩ : syracuseStep 1294697 = 971023) B971023
theorem B6209921 : Blo 535802 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B2048399 : Blo 535802 2048399 := bstep (se 1 (by rfl) ⟨1536299, by rfl⟩ : syracuseStep 2048399 = 3072599) B3072599
theorem B1720777 : Blo 535802 1720777 := bstep (se 2 (by rfl) ⟨645291, by rfl⟩ : syracuseStep 1720777 = 1290583) B1290583
theorem B1819259 : Blo 535802 1819259 := bstep (se 1 (by rfl) ⟨1364444, by rfl⟩ : syracuseStep 1819259 = 2728889) B2728889
theorem B606919 : Blo 535802 606919 := bstep (se 1 (by rfl) ⟨455189, by rfl⟩ : syracuseStep 606919 = 910379) B910379
theorem B1819421 : Blo 535802 1819421 := bstep (se 3 (by rfl) ⟨341141, by rfl⟩ : syracuseStep 1819421 = 682283) B682283
theorem B803759 : Blo 535802 803759 := bstep (se 1 (by rfl) ⟨602819, by rfl⟩ : syracuseStep 803759 = 1205639) B1205639
theorem B803849 : Blo 535802 803849 := bstep (se 2 (by rfl) ⟨301443, by rfl⟩ : syracuseStep 803849 = 602887) B602887
theorem B803879 : Blo 535802 803879 := bstep (se 1 (by rfl) ⟨602909, by rfl⟩ : syracuseStep 803879 = 1205819) B1205819
theorem B8930371 : Blo 535802 8930371 := bstep (se 1 (by rfl) ⟨6697778, by rfl⟩ : syracuseStep 8930371 = 13395557) B13395557
theorem B803963 : Blo 535802 803963 := bstep (se 1 (by rfl) ⟨602972, by rfl⟩ : syracuseStep 803963 = 1205945) B1205945
theorem B3884203 : Blo 535802 3884203 := bstep (se 1 (by rfl) ⟨2913152, by rfl⟩ : syracuseStep 3884203 = 5826305) B5826305
theorem B6898891 : Blo 535802 6898891 := bstep (se 1 (by rfl) ⟨5174168, by rfl⟩ : syracuseStep 6898891 = 10348337) B10348337
theorem B804089 : Blo 535802 804089 := bstep (se 2 (by rfl) ⟨301533, by rfl⟩ : syracuseStep 804089 = 603067) B603067
theorem B804191 : Blo 535802 804191 := bstep (se 1 (by rfl) ⟨603143, by rfl⟩ : syracuseStep 804191 = 1206287) B1206287
theorem B804203 : Blo 535802 804203 := bstep (se 1 (by rfl) ⟨603152, by rfl⟩ : syracuseStep 804203 = 1206305) B1206305
theorem B1820123 : Blo 535802 1820123 := bstep (se 1 (by rfl) ⟨1365092, by rfl⟩ : syracuseStep 1820123 = 2730185) B2730185
theorem B804431 : Blo 535802 804431 := bstep (se 1 (by rfl) ⟨603323, by rfl⟩ : syracuseStep 804431 = 1206647) B1206647
theorem B1295995 : Blo 535802 1295995 := bstep (se 1 (by rfl) ⟨971996, by rfl⟩ : syracuseStep 1295995 = 1943993) B1943993
theorem B968363 : Blo 535802 968363 := bstep (se 1 (by rfl) ⟨726272, by rfl⟩ : syracuseStep 968363 = 1452545) B1452545
theorem B804551 : Blo 535802 804551 := bstep (se 1 (by rfl) ⟨603413, by rfl⟩ : syracuseStep 804551 = 1206827) B1206827
theorem B804713 : Blo 535802 804713 := bstep (se 2 (by rfl) ⟨301767, by rfl⟩ : syracuseStep 804713 = 603535) B603535
theorem B804791 : Blo 535802 804791 := bstep (se 1 (by rfl) ⟨603593, by rfl⟩ : syracuseStep 804791 = 1207187) B1207187
theorem B804827 : Blo 535802 804827 := bstep (se 1 (by rfl) ⟨603620, by rfl⟩ : syracuseStep 804827 = 1207241) B1207241
theorem B5163097 : Blo 535802 5163097 := bstep (se 2 (by rfl) ⟨1936161, by rfl⟩ : syracuseStep 5163097 = 3872323) B3872323
theorem B1820825 : Blo 535802 1820825 := bstep (se 2 (by rfl) ⟨682809, by rfl⟩ : syracuseStep 1820825 = 1365619) B1365619
theorem B1362167 : Blo 535802 1362167 := bstep (se 1 (by rfl) ⟨1021625, by rfl⟩ : syracuseStep 1362167 = 2043251) B2043251
theorem B575839 : Blo 535802 575839 := bstep (se 1 (by rfl) ⟨431879, by rfl⟩ : syracuseStep 575839 = 863759) B863759
theorem B805295 : Blo 535802 805295 := bstep (se 1 (by rfl) ⟨603971, by rfl⟩ : syracuseStep 805295 = 1207943) B1207943
theorem B16566707 : Blo 535802 16566707 := bstep (se 1 (by rfl) ⟨12425030, by rfl⟩ : syracuseStep 16566707 = 24850061) B24850061
theorem B22432241 : Blo 535802 22432241 := bstep (se 2 (by rfl) ⟨8412090, by rfl⟩ : syracuseStep 22432241 = 16824181) B16824181
theorem B805385 : Blo 535802 805385 := bstep (se 2 (by rfl) ⟨302019, by rfl⟩ : syracuseStep 805385 = 604039) B604039
theorem B805415 : Blo 535802 805415 := bstep (se 1 (by rfl) ⟨604061, by rfl⟩ : syracuseStep 805415 = 1208123) B1208123
theorem B805499 : Blo 535802 805499 := bstep (se 1 (by rfl) ⟨604124, by rfl⟩ : syracuseStep 805499 = 1208249) B1208249
theorem B543407 : Blo 535802 543407 := bstep (se 1 (by rfl) ⟨407555, by rfl⟩ : syracuseStep 543407 = 815111) B815111
theorem B805625 : Blo 535802 805625 := bstep (se 2 (by rfl) ⟨302109, by rfl⟩ : syracuseStep 805625 = 604219) B604219
theorem B805727 : Blo 535802 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B805739 : Blo 535802 805739 := bstep (se 1 (by rfl) ⟨604304, by rfl⟩ : syracuseStep 805739 = 1208609) B1208609
theorem B805967 : Blo 535802 805967 := bstep (se 1 (by rfl) ⟨604475, by rfl⟩ : syracuseStep 805967 = 1208951) B1208951
theorem B806087 : Blo 535802 806087 := bstep (se 1 (by rfl) ⟨604565, by rfl⟩ : syracuseStep 806087 = 1209131) B1209131
theorem B904439 : Blo 535802 904439 := bstep (se 1 (by rfl) ⟨678329, by rfl⟩ : syracuseStep 904439 = 1356659) B1356659
theorem B4345177 : Blo 535802 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B806249 : Blo 535802 806249 := bstep (se 2 (by rfl) ⟨302343, by rfl⟩ : syracuseStep 806249 = 604687) B604687
theorem B806327 : Blo 535802 806327 := bstep (se 1 (by rfl) ⟨604745, by rfl⟩ : syracuseStep 806327 = 1209491) B1209491
theorem B806363 : Blo 535802 806363 := bstep (se 1 (by rfl) ⟨604772, by rfl⟩ : syracuseStep 806363 = 1209545) B1209545
theorem B6868547 : Blo 535802 6868547 := bstep (se 1 (by rfl) ⟨5151410, by rfl⟩ : syracuseStep 6868547 = 10302821) B10302821
theorem B904783 : Blo 535802 904783 := bstep (se 1 (by rfl) ⟨678587, by rfl⟩ : syracuseStep 904783 = 1357175) B1357175
theorem B14012027 : Blo 535802 14012027 := bstep (se 1 (by rfl) ⟨10509020, by rfl⟩ : syracuseStep 14012027 = 21018041) B21018041
theorem B1363655 : Blo 535802 1363655 := bstep (se 1 (by rfl) ⟨1022741, by rfl⟩ : syracuseStep 1363655 = 2045483) B2045483
theorem B905033 : Blo 535802 905033 := bstep (se 2 (by rfl) ⟨339387, by rfl⟩ : syracuseStep 905033 = 678775) B678775
theorem B806831 : Blo 535802 806831 := bstep (se 1 (by rfl) ⟨605123, by rfl⟩ : syracuseStep 806831 = 1210247) B1210247
theorem B806921 : Blo 535802 806921 := bstep (se 2 (by rfl) ⟨302595, by rfl⟩ : syracuseStep 806921 = 605191) B605191
theorem B806951 : Blo 535802 806951 := bstep (se 1 (by rfl) ⟨605213, by rfl⟩ : syracuseStep 806951 = 1210427) B1210427
theorem B970849 : Blo 535802 970849 := bstep (se 2 (by rfl) ⟨364068, by rfl⟩ : syracuseStep 970849 = 728137) B728137
theorem B807035 : Blo 535802 807035 := bstep (se 1 (by rfl) ⟨605276, by rfl⟩ : syracuseStep 807035 = 1210553) B1210553
theorem B905465 : Blo 535802 905465 := bstep (se 2 (by rfl) ⟨339549, by rfl⟩ : syracuseStep 905465 = 679099) B679099
theorem B807161 : Blo 535802 807161 := bstep (se 2 (by rfl) ⟨302685, by rfl⟩ : syracuseStep 807161 = 605371) B605371
theorem B807263 : Blo 535802 807263 := bstep (se 1 (by rfl) ⟨605447, by rfl⟩ : syracuseStep 807263 = 1210895) B1210895
theorem B807275 : Blo 535802 807275 := bstep (se 1 (by rfl) ⟨605456, by rfl⟩ : syracuseStep 807275 = 1210913) B1210913
theorem B905647 : Blo 535802 905647 := bstep (se 1 (by rfl) ⟨679235, by rfl⟩ : syracuseStep 905647 = 1358471) B1358471
theorem B971195 : Blo 535802 971195 := bstep (se 1 (by rfl) ⟨728396, by rfl⟩ : syracuseStep 971195 = 1456793) B1456793
theorem B905735 : Blo 535802 905735 := bstep (se 1 (by rfl) ⟨679301, by rfl⟩ : syracuseStep 905735 = 1358603) B1358603
theorem B807503 : Blo 535802 807503 := bstep (se 1 (by rfl) ⟨605627, by rfl⟩ : syracuseStep 807503 = 1211255) B1211255
theorem B643783 : Blo 535802 643783 := bstep (se 1 (by rfl) ⟨482837, by rfl⟩ : syracuseStep 643783 = 965675) B965675
theorem B807623 : Blo 535802 807623 := bstep (se 1 (by rfl) ⟨605717, by rfl⟩ : syracuseStep 807623 = 1211435) B1211435
theorem B1364809 : Blo 535802 1364809 := bstep (se 2 (by rfl) ⟨511803, by rfl⟩ : syracuseStep 1364809 = 1023607) B1023607
theorem B906079 : Blo 535802 906079 := bstep (se 1 (by rfl) ⟨679559, by rfl⟩ : syracuseStep 906079 = 1359119) B1359119
theorem B807785 : Blo 535802 807785 := bstep (se 2 (by rfl) ⟨302919, by rfl⟩ : syracuseStep 807785 = 605839) B605839
theorem B906167 : Blo 535802 906167 := bstep (se 1 (by rfl) ⟨679625, by rfl⟩ : syracuseStep 906167 = 1359251) B1359251
theorem B807863 : Blo 535802 807863 := bstep (se 1 (by rfl) ⟨605897, by rfl⟩ : syracuseStep 807863 = 1211795) B1211795
theorem B807899 : Blo 535802 807899 := bstep (se 1 (by rfl) ⟨605924, by rfl⟩ : syracuseStep 807899 = 1211849) B1211849
theorem B808367 : Blo 535802 808367 := bstep (se 1 (by rfl) ⟨606275, by rfl⟩ : syracuseStep 808367 = 1212551) B1212551
theorem B2446793 : Blo 535802 2446793 := bstep (se 2 (by rfl) ⟨917547, by rfl⟩ : syracuseStep 2446793 = 1835095) B1835095
theorem B906761 : Blo 535802 906761 := bstep (se 2 (by rfl) ⟨340035, by rfl⟩ : syracuseStep 906761 = 680071) B680071
theorem B808457 : Blo 535802 808457 := bstep (se 2 (by rfl) ⟨303171, by rfl⟩ : syracuseStep 808457 = 606343) B606343
theorem B808487 : Blo 535802 808487 := bstep (se 1 (by rfl) ⟨606365, by rfl⟩ : syracuseStep 808487 = 1212731) B1212731
theorem B808571 : Blo 535802 808571 := bstep (se 1 (by rfl) ⟨606428, by rfl⟩ : syracuseStep 808571 = 1212857) B1212857
theorem B906923 : Blo 535802 906923 := bstep (se 1 (by rfl) ⟨680192, by rfl⟩ : syracuseStep 906923 = 1360385) B1360385
theorem B1529533 : Blo 535802 1529533 := bstep (se 3 (by rfl) ⟨286787, by rfl⟩ : syracuseStep 1529533 = 573575) B573575
theorem B808697 : Blo 535802 808697 := bstep (se 2 (by rfl) ⟨303261, by rfl⟩ : syracuseStep 808697 = 606523) B606523
theorem B3266399 : Blo 535802 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B808799 : Blo 535802 808799 := bstep (se 1 (by rfl) ⟨606599, by rfl⟩ : syracuseStep 808799 = 1213199) B1213199
theorem B808811 : Blo 535802 808811 := bstep (se 1 (by rfl) ⟨606608, by rfl⟩ : syracuseStep 808811 = 1213217) B1213217
theorem B1529761 : Blo 535802 1529761 := bstep (se 2 (by rfl) ⟨573660, by rfl⟩ : syracuseStep 1529761 = 1147321) B1147321
theorem B1365943 : Blo 535802 1365943 := bstep (se 1 (by rfl) ⟨1024457, by rfl⟩ : syracuseStep 1365943 = 2048915) B2048915
theorem B2185223 : Blo 535802 2185223 := bstep (se 1 (by rfl) ⟨1638917, by rfl⟩ : syracuseStep 2185223 = 3277835) B3277835
theorem B907321 : Blo 535802 907321 := bstep (se 2 (by rfl) ⟨340245, by rfl⟩ : syracuseStep 907321 = 680491) B680491
theorem B809039 : Blo 535802 809039 := bstep (se 1 (by rfl) ⟨606779, by rfl⟩ : syracuseStep 809039 = 1213559) B1213559
theorem B907463 : Blo 535802 907463 := bstep (se 1 (by rfl) ⟨680597, by rfl⟩ : syracuseStep 907463 = 1361195) B1361195
theorem B809159 : Blo 535802 809159 := bstep (se 1 (by rfl) ⟨606869, by rfl⟩ : syracuseStep 809159 = 1213739) B1213739
theorem B1530103 : Blo 535802 1530103 := bstep (se 1 (by rfl) ⟨1147577, by rfl⟩ : syracuseStep 1530103 = 2295155) B2295155
theorem B907625 : Blo 535802 907625 := bstep (se 2 (by rfl) ⟨340359, by rfl⟩ : syracuseStep 907625 = 680719) B680719
theorem B809321 : Blo 535802 809321 := bstep (se 2 (by rfl) ⟨303495, by rfl⟩ : syracuseStep 809321 = 606991) B606991
theorem B809399 : Blo 535802 809399 := bstep (se 1 (by rfl) ⟨607049, by rfl⟩ : syracuseStep 809399 = 1214099) B1214099
theorem B809435 : Blo 535802 809435 := bstep (se 1 (by rfl) ⟨607076, by rfl⟩ : syracuseStep 809435 = 1214153) B1214153
theorem B1530377 : Blo 535802 1530377 := bstep (se 2 (by rfl) ⟨573891, by rfl⟩ : syracuseStep 1530377 = 1147783) B1147783
theorem B908023 : Blo 535802 908023 := bstep (se 1 (by rfl) ⟨681017, by rfl⟩ : syracuseStep 908023 = 1362035) B1362035
theorem B908219 : Blo 535802 908219 := bstep (se 1 (by rfl) ⟨681164, by rfl⟩ : syracuseStep 908219 = 1362329) B1362329
theorem B908327 : Blo 535802 908327 := bstep (se 1 (by rfl) ⟨681245, by rfl⟩ : syracuseStep 908327 = 1362491) B1362491
theorem B1531037 : Blo 535802 1531037 := bstep (se 3 (by rfl) ⟨287069, by rfl⟩ : syracuseStep 1531037 = 574139) B574139
theorem B2579627 : Blo 535802 2579627 := bstep (se 1 (by rfl) ⟨1934720, by rfl⟩ : syracuseStep 2579627 = 3869441) B3869441
theorem B908617 : Blo 535802 908617 := bstep (se 2 (by rfl) ⟨340731, by rfl⟩ : syracuseStep 908617 = 681463) B681463
theorem B908651 : Blo 535802 908651 := bstep (se 1 (by rfl) ⟨681488, by rfl⟩ : syracuseStep 908651 = 1362977) B1362977
theorem B3890605 : Blo 535802 3890605 := bstep (se 3 (by rfl) ⟨729488, by rfl⟩ : syracuseStep 3890605 = 1458977) B1458977
theorem B4087259 : Blo 535802 4087259 := bstep (se 1 (by rfl) ⟨3065444, by rfl⟩ : syracuseStep 4087259 = 6130889) B6130889
theorem B1531379 : Blo 535802 1531379 := bstep (se 1 (by rfl) ⟨1148534, by rfl⟩ : syracuseStep 1531379 = 2297069) B2297069
theorem B2186941 : Blo 535802 2186941 := bstep (se 3 (by rfl) ⟨410051, by rfl⟩ : syracuseStep 2186941 = 820103) B820103
theorem B909049 : Blo 535802 909049 := bstep (se 2 (by rfl) ⟨340893, by rfl⟩ : syracuseStep 909049 = 681787) B681787
theorem B1531835 : Blo 535802 1531835 := bstep (se 1 (by rfl) ⟨1148876, by rfl⟩ : syracuseStep 1531835 = 2297753) B2297753
theorem B4087745 : Blo 535802 4087745 := bstep (se 2 (by rfl) ⟨1532904, by rfl⟩ : syracuseStep 4087745 = 3065809) B3065809
theorem B909319 : Blo 535802 909319 := bstep (se 1 (by rfl) ⟨681989, by rfl⟩ : syracuseStep 909319 = 1363979) B1363979
theorem B1400851 : Blo 535802 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B680015 : Blo 535802 680015 := bstep (se 1 (by rfl) ⟨510011, by rfl⟩ : syracuseStep 680015 = 1020023) B1020023
theorem B909751 : Blo 535802 909751 := bstep (se 1 (by rfl) ⟨682313, by rfl⟩ : syracuseStep 909751 = 1364627) B1364627
theorem B909947 : Blo 535802 909947 := bstep (se 1 (by rfl) ⟨682460, by rfl⟩ : syracuseStep 909947 = 1364921) B1364921
theorem B910345 : Blo 535802 910345 := bstep (se 2 (by rfl) ⟨341379, by rfl⟩ : syracuseStep 910345 = 682759) B682759
theorem B648271 : Blo 535802 648271 := bstep (se 1 (by rfl) ⟨486203, by rfl⟩ : syracuseStep 648271 = 972407) B972407
theorem B2450585 : Blo 535802 2450585 := bstep (se 2 (by rfl) ⟨918969, by rfl⟩ : syracuseStep 2450585 = 1837939) B1837939
theorem B910507 : Blo 535802 910507 := bstep (se 1 (by rfl) ⟨682880, by rfl⟩ : syracuseStep 910507 = 1365761) B1365761
theorem B681311 : Blo 535802 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B4089203 : Blo 535802 4089203 := bstep (se 1 (by rfl) ⟨3066902, by rfl⟩ : syracuseStep 4089203 = 6133805) B6133805
theorem B910811 : Blo 535802 910811 := bstep (se 1 (by rfl) ⟨683108, by rfl⟩ : syracuseStep 910811 = 1366217) B1366217
theorem B2319911 : Blo 535802 2319911 := bstep (se 1 (by rfl) ⟨1739933, by rfl⟩ : syracuseStep 2319911 = 3479867) B3479867
theorem B2713337 : Blo 535802 2713337 := bstep (se 2 (by rfl) ⟨1017501, by rfl⟩ : syracuseStep 2713337 = 2035003) B2035003
theorem B1206089 : Blo 535802 1206089 := bstep (se 2 (by rfl) ⟨452283, by rfl⟩ : syracuseStep 1206089 = 904567) B904567
theorem B12904753 : Blo 535802 12904753 := bstep (se 2 (by rfl) ⟨4839282, by rfl⟩ : syracuseStep 12904753 = 9678565) B9678565
theorem B2713985 : Blo 535802 2713985 := bstep (se 2 (by rfl) ⟨1017744, by rfl⟩ : syracuseStep 2713985 = 2035489) B2035489
theorem B1206881 : Blo 535802 1206881 := bstep (se 2 (by rfl) ⟨452580, by rfl⟩ : syracuseStep 1206881 = 905161) B905161
theorem B1207223 : Blo 535802 1207223 := bstep (se 1 (by rfl) ⟨905417, by rfl⟩ : syracuseStep 1207223 = 1810835) B1810835
theorem B2714795 : Blo 535802 2714795 := bstep (se 1 (by rfl) ⟨2036096, by rfl⟩ : syracuseStep 2714795 = 4072193) B4072193
theorem B4418959 : Blo 535802 4418959 := bstep (se 1 (by rfl) ⟨3314219, by rfl⟩ : syracuseStep 4418959 = 6628439) B6628439
theorem B2584009 : Blo 535802 2584009 := bstep (se 2 (by rfl) ⟨969003, by rfl⟩ : syracuseStep 2584009 = 1938007) B1938007
theorem B3436019 : Blo 535802 3436019 := bstep (se 1 (by rfl) ⟨2577014, by rfl⟩ : syracuseStep 3436019 = 5154029) B5154029
theorem B1207817 : Blo 535802 1207817 := bstep (se 2 (by rfl) ⟨452931, by rfl⟩ : syracuseStep 1207817 = 905863) B905863
theorem B4189819 : Blo 535802 4189819 := bstep (se 1 (by rfl) ⟨3142364, by rfl⟩ : syracuseStep 4189819 = 6284729) B6284729
theorem B2715281 : Blo 535802 2715281 := bstep (se 2 (by rfl) ⟨1018230, by rfl⟩ : syracuseStep 2715281 = 2036461) B2036461
theorem B4484845 : Blo 535802 4484845 := bstep (se 3 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 4484845 = 1681817) B1681817
theorem B1208159 : Blo 535802 1208159 := bstep (se 1 (by rfl) ⟨906119, by rfl⟩ : syracuseStep 1208159 = 1812239) B1812239
theorem B1208339 : Blo 535802 1208339 := bstep (se 1 (by rfl) ⟨906254, by rfl⟩ : syracuseStep 1208339 = 1812509) B1812509
theorem B2289721 : Blo 535802 2289721 := bstep (se 2 (by rfl) ⟨858645, by rfl⟩ : syracuseStep 2289721 = 1717291) B1717291
theorem B1208681 : Blo 535802 1208681 := bstep (se 2 (by rfl) ⟨453255, by rfl⟩ : syracuseStep 1208681 = 906511) B906511
theorem B3666491 : Blo 535802 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B17429093 : Blo 535802 17429093 := bstep (se 4 (by rfl) ⟨1633977, by rfl⟩ : syracuseStep 17429093 = 3267955) B3267955
theorem B6517421 : Blo 535802 6517421 := bstep (se 3 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 6517421 = 2444033) B2444033
theorem B3928787 : Blo 535802 3928787 := bstep (se 1 (by rfl) ⟨2946590, by rfl⟩ : syracuseStep 3928787 = 5893181) B5893181
theorem B1209275 : Blo 535802 1209275 := bstep (se 1 (by rfl) ⟨906956, by rfl⟩ : syracuseStep 1209275 = 1813913) B1813913
theorem B1209401 : Blo 535802 1209401 := bstep (se 2 (by rfl) ⟨453525, by rfl⟩ : syracuseStep 1209401 = 907051) B907051
theorem B1209743 : Blo 535802 1209743 := bstep (se 1 (by rfl) ⟨907307, by rfl⟩ : syracuseStep 1209743 = 1814615) B1814615
theorem B1570291 : Blo 535802 1570291 := bstep (se 1 (by rfl) ⟨1177718, by rfl⟩ : syracuseStep 1570291 = 2355437) B2355437
theorem B1210067 : Blo 535802 1210067 := bstep (se 1 (by rfl) ⟨907550, by rfl⟩ : syracuseStep 1210067 = 1815101) B1815101
theorem B2717549 : Blo 535802 2717549 := bstep (se 3 (by rfl) ⟨509540, by rfl⟩ : syracuseStep 2717549 = 1019081) B1019081
theorem B2717711 : Blo 535802 2717711 := bstep (se 1 (by rfl) ⟨2038283, by rfl⟩ : syracuseStep 2717711 = 4076567) B4076567
theorem B2292097 : Blo 535802 2292097 := bstep (se 2 (by rfl) ⟨859536, by rfl⟩ : syracuseStep 2292097 = 1719073) B1719073
theorem B1211003 : Blo 535802 1211003 := bstep (se 1 (by rfl) ⟨908252, by rfl⟩ : syracuseStep 1211003 = 1816505) B1816505
theorem B1211129 : Blo 535802 1211129 := bstep (se 2 (by rfl) ⟨454173, by rfl⟩ : syracuseStep 1211129 = 908347) B908347
theorem B3111709 : Blo 535802 3111709 := bstep (se 3 (by rfl) ⟨583445, by rfl⟩ : syracuseStep 3111709 = 1166891) B1166891
theorem B1145783 : Blo 535802 1145783 := bstep (se 1 (by rfl) ⟨859337, by rfl⟩ : syracuseStep 1145783 = 1718675) B1718675
theorem B1211399 : Blo 535802 1211399 := bstep (se 1 (by rfl) ⟨908549, by rfl⟩ : syracuseStep 1211399 = 1817099) B1817099
theorem B818255 : Blo 535802 818255 := bstep (se 1 (by rfl) ⟨613691, by rfl⟩ : syracuseStep 818255 = 1227383) B1227383
theorem B1211471 : Blo 535802 1211471 := bstep (se 1 (by rfl) ⟨908603, by rfl⟩ : syracuseStep 1211471 = 1817207) B1817207
theorem B2587895 : Blo 535802 2587895 := bstep (se 1 (by rfl) ⟨1940921, by rfl⟩ : syracuseStep 2587895 = 3881843) B3881843
theorem B3440015 : Blo 535802 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B1211867 : Blo 535802 1211867 := bstep (se 1 (by rfl) ⟨908900, by rfl⟩ : syracuseStep 1211867 = 1817801) B1817801
theorem B1998361 : Blo 535802 1998361 := bstep (se 2 (by rfl) ⟨749385, by rfl⟩ : syracuseStep 1998361 = 1498771) B1498771
theorem B1867303 : Blo 535802 1867303 := bstep (se 1 (by rfl) ⟨1400477, by rfl⟩ : syracuseStep 1867303 = 2800955) B2800955
theorem B2358881 : Blo 535802 2358881 := bstep (se 2 (by rfl) ⟨884580, by rfl⟩ : syracuseStep 2358881 = 1769161) B1769161
theorem B1212335 : Blo 535802 1212335 := bstep (se 1 (by rfl) ⟨909251, by rfl⟩ : syracuseStep 1212335 = 1818503) B1818503
theorem B1212425 : Blo 535802 1212425 := bstep (se 2 (by rfl) ⟨454659, by rfl⟩ : syracuseStep 1212425 = 909319) B909319
theorem B1867801 : Blo 535802 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B1212839 : Blo 535802 1212839 := bstep (se 1 (by rfl) ⟨909629, by rfl⟩ : syracuseStep 1212839 = 1819259) B1819259
theorem B3113417 : Blo 535802 3113417 := bstep (se 2 (by rfl) ⟨1167531, by rfl⟩ : syracuseStep 3113417 = 2335063) B2335063
theorem B2064865 : Blo 535802 2064865 := bstep (se 2 (by rfl) ⟨774324, by rfl⟩ : syracuseStep 2064865 = 1548649) B1548649
theorem B1212947 : Blo 535802 1212947 := bstep (se 1 (by rfl) ⟨909710, by rfl⟩ : syracuseStep 1212947 = 1819421) B1819421
theorem B1213001 : Blo 535802 1213001 := bstep (se 2 (by rfl) ⟨454875, by rfl⟩ : syracuseStep 1213001 = 909751) B909751
theorem B2294369 : Blo 535802 2294369 := bstep (se 2 (by rfl) ⟨860388, by rfl⟩ : syracuseStep 2294369 = 1720777) B1720777
theorem B1213415 : Blo 535802 1213415 := bstep (se 1 (by rfl) ⟨910061, by rfl⟩ : syracuseStep 1213415 = 1820123) B1820123
theorem B2589853 : Blo 535802 2589853 := bstep (se 3 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 2589853 = 971195) B971195
theorem B2294983 : Blo 535802 2294983 := bstep (se 1 (by rfl) ⟨1721237, by rfl⟩ : syracuseStep 2294983 = 3442475) B3442475
theorem B1213793 : Blo 535802 1213793 := bstep (se 2 (by rfl) ⟨455172, by rfl⟩ : syracuseStep 1213793 = 910345) B910345
theorem B1213883 : Blo 535802 1213883 := bstep (se 1 (by rfl) ⟨910412, by rfl⟩ : syracuseStep 1213883 = 1820825) B1820825
theorem B2459069 : Blo 535802 2459069 := bstep (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) B922151
theorem B5178937 : Blo 535802 5178937 := bstep (se 2 (by rfl) ⟨1942101, by rfl⟩ : syracuseStep 5178937 = 3884203) B3884203
theorem B1214009 : Blo 535802 1214009 := bstep (se 2 (by rfl) ⟨455253, by rfl⟩ : syracuseStep 1214009 = 910507) B910507
theorem B11044471 : Blo 535802 11044471 := bstep (se 1 (by rfl) ⟨8283353, by rfl⟩ : syracuseStep 11044471 = 16566707) B16566707
theorem B2721437 : Blo 535802 2721437 := bstep (se 3 (by rfl) ⟨510269, by rfl⟩ : syracuseStep 2721437 = 1020539) B1020539
theorem B15534503 : Blo 535802 15534503 := bstep (se 1 (by rfl) ⟨11650877, by rfl⟩ : syracuseStep 15534503 = 23301755) B23301755
theorem B9341351 : Blo 535802 9341351 := bstep (se 1 (by rfl) ⟨7006013, by rfl⟩ : syracuseStep 9341351 = 14012027) B14012027
theorem B13044179 : Blo 535802 13044179 := bstep (se 1 (by rfl) ⟨9783134, by rfl⟩ : syracuseStep 13044179 = 19566269) B19566269
theorem B1018489 : Blo 535802 1018489 := bstep (se 2 (by rfl) ⟨381933, by rfl⟩ : syracuseStep 1018489 = 763867) B763867
theorem B6884129 : Blo 535802 6884129 := bstep (se 2 (by rfl) ⟨2581548, by rfl⟩ : syracuseStep 6884129 = 5163097) B5163097
theorem B2722733 : Blo 535802 2722733 := bstep (se 3 (by rfl) ⟨510512, by rfl⟩ : syracuseStep 2722733 = 1021025) B1021025
theorem B17206337 : Blo 535802 17206337 := bstep (se 2 (by rfl) ⟨6452376, by rfl⟩ : syracuseStep 17206337 = 12904753) B12904753
theorem B2493659 : Blo 535802 2493659 := bstep (se 1 (by rfl) ⟨1870244, by rfl⟩ : syracuseStep 2493659 = 3740489) B3740489
theorem B5835995 : Blo 535802 5835995 := bstep (se 1 (by rfl) ⟨4376996, by rfl⟩ : syracuseStep 5835995 = 8753993) B8753993
theorem B1019233 : Blo 535802 1019233 := bstep (se 2 (by rfl) ⟨382212, by rfl⟩ : syracuseStep 1019233 = 764425) B764425
theorem B1969595 : Blo 535802 1969595 := bstep (se 1 (by rfl) ⟨1477196, by rfl⟩ : syracuseStep 1969595 = 2954393) B2954393
theorem B921385 : Blo 535802 921385 := bstep (se 2 (by rfl) ⟨345519, by rfl⟩ : syracuseStep 921385 = 691039) B691039
theorem B4591403 : Blo 535802 4591403 := bstep (se 1 (by rfl) ⟨3443552, by rfl⟩ : syracuseStep 4591403 = 6887105) B6887105
theorem B2461697 : Blo 535802 2461697 := bstep (se 2 (by rfl) ⟨923136, by rfl⟩ : syracuseStep 2461697 = 1846273) B1846273
theorem B4919453 : Blo 535802 4919453 := bstep (se 3 (by rfl) ⟨922397, by rfl⟩ : syracuseStep 4919453 = 1844795) B1844795
theorem B1020251 : Blo 535802 1020251 := bstep (se 1 (by rfl) ⟨765188, by rfl⟩ : syracuseStep 1020251 = 1530377) B1530377
theorem B2724353 : Blo 535802 2724353 := bstep (se 2 (by rfl) ⟨1021632, by rfl⟩ : syracuseStep 2724353 = 2043265) B2043265
theorem B3445345 : Blo 535802 3445345 := bstep (se 2 (by rfl) ⟨1292004, by rfl⟩ : syracuseStep 3445345 = 2584009) B2584009
theorem B2036447 : Blo 535802 2036447 := bstep (se 1 (by rfl) ⟨1527335, by rfl⟩ : syracuseStep 2036447 = 3054671) B3054671
theorem B1020691 : Blo 535802 1020691 := bstep (se 1 (by rfl) ⟨765518, by rfl⟩ : syracuseStep 1020691 = 1531037) B1531037
theorem B2757419 : Blo 535802 2757419 := bstep (se 1 (by rfl) ⟨2068064, by rfl⟩ : syracuseStep 2757419 = 4136129) B4136129
theorem B2724839 : Blo 535802 2724839 := bstep (se 1 (by rfl) ⟨2043629, by rfl⟩ : syracuseStep 2724839 = 4087259) B4087259
theorem B1020919 : Blo 535802 1020919 := bstep (se 1 (by rfl) ⟨765689, by rfl⟩ : syracuseStep 1020919 = 1531379) B1531379
theorem B1021223 : Blo 535802 1021223 := bstep (se 1 (by rfl) ⟨765917, by rfl⟩ : syracuseStep 1021223 = 1531835) B1531835
theorem B2725163 : Blo 535802 2725163 := bstep (se 1 (by rfl) ⟨2043872, by rfl⟩ : syracuseStep 2725163 = 4087745) B4087745
theorem B3052961 : Blo 535802 3052961 := bstep (se 2 (by rfl) ⟨1144860, by rfl⟩ : syracuseStep 3052961 = 2289721) B2289721
theorem B1808513 : Blo 535802 1808513 := bstep (se 2 (by rfl) ⟨678192, by rfl⟩ : syracuseStep 1808513 = 1356385) B1356385
theorem B2726135 : Blo 535802 2726135 := bstep (se 1 (by rfl) ⟨2044601, by rfl⟩ : syracuseStep 2726135 = 4089203) B4089203
theorem B858377 : Blo 535802 858377 := bstep (se 2 (by rfl) ⟨321891, by rfl⟩ : syracuseStep 858377 = 643783) B643783
theorem B1546607 : Blo 535802 1546607 := bstep (se 1 (by rfl) ⟨1159955, by rfl⟩ : syracuseStep 1546607 = 2319911) B2319911
theorem B1808891 : Blo 535802 1808891 := bstep (se 1 (by rfl) ⟨1356668, by rfl⟩ : syracuseStep 1808891 = 2713337) B2713337
theorem B11606591 : Blo 535802 11606591 := bstep (se 1 (by rfl) ⟨8704943, by rfl⟩ : syracuseStep 11606591 = 17409887) B17409887
theorem B1022537 : Blo 535802 1022537 := bstep (se 2 (by rfl) ⟨383451, by rfl⟩ : syracuseStep 1022537 = 766903) B766903
theorem B2726621 : Blo 535802 2726621 := bstep (se 3 (by rfl) ⟨511241, by rfl⟩ : syracuseStep 2726621 = 1022483) B1022483
theorem B1809323 : Blo 535802 1809323 := bstep (se 1 (by rfl) ⟨1356992, by rfl⟩ : syracuseStep 1809323 = 2713985) B2713985
theorem B1449085 : Blo 535802 1449085 := bstep (se 3 (by rfl) ⟨271703, by rfl⟩ : syracuseStep 1449085 = 543407) B543407
theorem B1809863 : Blo 535802 1809863 := bstep (se 1 (by rfl) ⟨1357397, by rfl⟩ : syracuseStep 1809863 = 2714795) B2714795
theorem B1449431 : Blo 535802 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B5905979 : Blo 535802 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B2039377 : Blo 535802 2039377 := bstep (se 2 (by rfl) ⟨764766, by rfl⟩ : syracuseStep 2039377 = 1529533) B1529533
theorem B1810187 : Blo 535802 1810187 := bstep (se 1 (by rfl) ⟨1357640, by rfl⟩ : syracuseStep 1810187 = 2715281) B2715281
theorem B3055421 : Blo 535802 3055421 := bstep (se 3 (by rfl) ⟨572891, by rfl⟩ : syracuseStep 3055421 = 1145783) B1145783
theorem B2301803 : Blo 535802 2301803 := bstep (se 1 (by rfl) ⟨1726352, by rfl⟩ : syracuseStep 2301803 = 3452705) B3452705
theorem B2039681 : Blo 535802 2039681 := bstep (se 2 (by rfl) ⟨764880, by rfl⟩ : syracuseStep 2039681 = 1529761) B1529761
theorem B1810457 : Blo 535802 1810457 := bstep (se 2 (by rfl) ⟨678921, by rfl⟩ : syracuseStep 1810457 = 1357843) B1357843
theorem B10657925 : Blo 535802 10657925 := bstep (se 4 (by rfl) ⟨999180, by rfl⟩ : syracuseStep 10657925 = 1998361) B1998361
theorem B2040137 : Blo 535802 2040137 := bstep (se 2 (by rfl) ⟨765051, by rfl⟩ : syracuseStep 2040137 = 1530103) B1530103
theorem B1024481 : Blo 535802 1024481 := bstep (se 2 (by rfl) ⟨384180, by rfl⟩ : syracuseStep 1024481 = 768361) B768361
theorem B3056129 : Blo 535802 3056129 := bstep (se 2 (by rfl) ⟨1146048, by rfl⟩ : syracuseStep 3056129 = 2292097) B2292097
theorem B3875843 : Blo 535802 3875843 := bstep (se 1 (by rfl) ⟨2906882, by rfl⟩ : syracuseStep 3875843 = 5813765) B5813765
theorem B1811699 : Blo 535802 1811699 := bstep (se 1 (by rfl) ⟨1358774, by rfl⟩ : syracuseStep 1811699 = 2717549) B2717549
theorem B1549561 : Blo 535802 1549561 := bstep (se 2 (by rfl) ⟨581085, by rfl⟩ : syracuseStep 1549561 = 1162171) B1162171
theorem B1811807 : Blo 535802 1811807 := bstep (se 1 (by rfl) ⟨1358855, by rfl⟩ : syracuseStep 1811807 = 2717711) B2717711
theorem B1451603 : Blo 535802 1451603 := bstep (se 1 (by rfl) ⟨1088702, by rfl⟩ : syracuseStep 1451603 = 2177405) B2177405
theorem B5187473 : Blo 535802 5187473 := bstep (se 2 (by rfl) ⟨1945302, by rfl⟩ : syracuseStep 5187473 = 3890605) B3890605
theorem B2041807 : Blo 535802 2041807 := bstep (se 1 (by rfl) ⟨1531355, by rfl⟩ : syracuseStep 2041807 = 3062711) B3062711
theorem B1943833 : Blo 535802 1943833 := bstep (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) B1457875
theorem B6302063 : Blo 535802 6302063 := bstep (se 1 (by rfl) ⟨4726547, by rfl⟩ : syracuseStep 6302063 = 9453095) B9453095
theorem B33499541 : Blo 535802 33499541 := bstep (se 6 (by rfl) ⟨785145, by rfl⟩ : syracuseStep 33499541 = 1570291) B1570291
theorem B2042279 : Blo 535802 2042279 := bstep (se 1 (by rfl) ⟨1531709, by rfl⟩ : syracuseStep 2042279 = 3063419) B3063419
theorem B2304551 : Blo 535802 2304551 := bstep (se 1 (by rfl) ⟨1728413, by rfl⟩ : syracuseStep 2304551 = 3456827) B3456827
theorem B2730671 : Blo 535802 2730671 := bstep (se 1 (by rfl) ⟨2048003, by rfl⟩ : syracuseStep 2730671 = 4096007) B4096007
theorem B1813373 : Blo 535802 1813373 := bstep (se 3 (by rfl) ⟨340007, by rfl⟩ : syracuseStep 1813373 = 680015) B680015
theorem B2042779 : Blo 535802 2042779 := bstep (se 1 (by rfl) ⟨1532084, by rfl⟩ : syracuseStep 2042779 = 3064169) B3064169
theorem B863131 : Blo 535802 863131 := bstep (se 1 (by rfl) ⟨647348, by rfl⟩ : syracuseStep 863131 = 1294697) B1294697
theorem B4139947 : Blo 535802 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B1092523 : Blo 535802 1092523 := bstep (se 1 (by rfl) ⟨819392, by rfl⟩ : syracuseStep 1092523 = 1638785) B1638785
theorem B2730995 : Blo 535802 2730995 := bstep (se 1 (by rfl) ⟨2048246, by rfl⟩ : syracuseStep 2730995 = 4096493) B4096493
theorem B1813643 : Blo 535802 1813643 := bstep (se 1 (by rfl) ⟨1360232, by rfl⟩ : syracuseStep 1813643 = 2720465) B2720465
theorem B1289459 : Blo 535802 1289459 := bstep (se 1 (by rfl) ⟨967094, by rfl⟩ : syracuseStep 1289459 = 1934189) B1934189
theorem B535839 : Blo 535802 535839 := bstep (se 1 (by rfl) ⟨401879, by rfl⟩ : syracuseStep 535839 = 803759) B803759
theorem B535899 : Blo 535802 535899 := bstep (se 1 (by rfl) ⟨401924, by rfl⟩ : syracuseStep 535899 = 803849) B803849
theorem B535919 : Blo 535802 535919 := bstep (se 1 (by rfl) ⟨401939, by rfl⟩ : syracuseStep 535919 = 803879) B803879
theorem B29470067 : Blo 535802 29470067 := bstep (se 1 (by rfl) ⟨22102550, by rfl⟩ : syracuseStep 29470067 = 44205101) B44205101
theorem B535975 : Blo 535802 535975 := bstep (se 1 (by rfl) ⟨401981, by rfl⟩ : syracuseStep 535975 = 803963) B803963
theorem B536059 : Blo 535802 536059 := bstep (se 1 (by rfl) ⟨402044, by rfl⟩ : syracuseStep 536059 = 804089) B804089
theorem B536127 : Blo 535802 536127 := bstep (se 1 (by rfl) ⟨402095, by rfl⟩ : syracuseStep 536127 = 804191) B804191
theorem B536135 : Blo 535802 536135 := bstep (se 1 (by rfl) ⟨402101, by rfl⟩ : syracuseStep 536135 = 804203) B804203
theorem B536287 : Blo 535802 536287 := bstep (se 1 (by rfl) ⟨402215, by rfl⟩ : syracuseStep 536287 = 804431) B804431
theorem B536367 : Blo 535802 536367 := bstep (se 1 (by rfl) ⟨402275, by rfl⟩ : syracuseStep 536367 = 804551) B804551
theorem B536475 : Blo 535802 536475 := bstep (se 1 (by rfl) ⟨402356, by rfl⟩ : syracuseStep 536475 = 804713) B804713
theorem B536527 : Blo 535802 536527 := bstep (se 1 (by rfl) ⟨402395, by rfl⟩ : syracuseStep 536527 = 804791) B804791
theorem B536551 : Blo 535802 536551 := bstep (se 1 (by rfl) ⟨402413, by rfl⟩ : syracuseStep 536551 = 804827) B804827
theorem B11907161 : Blo 535802 11907161 := bstep (se 2 (by rfl) ⟨4465185, by rfl⟩ : syracuseStep 11907161 = 8930371) B8930371
theorem B864361 : Blo 535802 864361 := bstep (se 2 (by rfl) ⟨324135, by rfl⟩ : syracuseStep 864361 = 648271) B648271
theorem B2732291 : Blo 535802 2732291 := bstep (se 1 (by rfl) ⟨2049218, by rfl⟩ : syracuseStep 2732291 = 4098437) B4098437
theorem B536863 : Blo 535802 536863 := bstep (se 1 (by rfl) ⟨402647, by rfl⟩ : syracuseStep 536863 = 805295) B805295
theorem B14954827 : Blo 535802 14954827 := bstep (se 1 (by rfl) ⟨11216120, by rfl⟩ : syracuseStep 14954827 = 22432241) B22432241
theorem B536923 : Blo 535802 536923 := bstep (se 1 (by rfl) ⟨402692, by rfl⟩ : syracuseStep 536923 = 805385) B805385
theorem B536943 : Blo 535802 536943 := bstep (se 1 (by rfl) ⟨402707, by rfl⟩ : syracuseStep 536943 = 805415) B805415
theorem B536999 : Blo 535802 536999 := bstep (se 1 (by rfl) ⟨402749, by rfl⟩ : syracuseStep 536999 = 805499) B805499
theorem B537083 : Blo 535802 537083 := bstep (se 1 (by rfl) ⟨402812, by rfl⟩ : syracuseStep 537083 = 805625) B805625
theorem B4076081 : Blo 535802 4076081 := bstep (se 2 (by rfl) ⟨1528530, by rfl⟩ : syracuseStep 4076081 = 3057061) B3057061
theorem B537151 : Blo 535802 537151 := bstep (se 1 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 537151 = 805727) B805727
theorem B537159 : Blo 535802 537159 := bstep (se 1 (by rfl) ⟨402869, by rfl⟩ : syracuseStep 537159 = 805739) B805739
theorem B2732615 : Blo 535802 2732615 := bstep (se 1 (by rfl) ⟨2049461, by rfl⟩ : syracuseStep 2732615 = 4098923) B4098923
theorem B537311 : Blo 535802 537311 := bstep (se 1 (by rfl) ⟨402983, by rfl⟩ : syracuseStep 537311 = 805967) B805967
theorem B1815263 : Blo 535802 1815263 := bstep (se 1 (by rfl) ⟨1361447, by rfl⟩ : syracuseStep 1815263 = 2722895) B2722895
theorem B537391 : Blo 535802 537391 := bstep (se 1 (by rfl) ⟨403043, by rfl⟩ : syracuseStep 537391 = 806087) B806087
theorem B602959 : Blo 535802 602959 := bstep (se 1 (by rfl) ⟨452219, by rfl⟩ : syracuseStep 602959 = 904439) B904439
theorem B537499 : Blo 535802 537499 := bstep (se 1 (by rfl) ⟨403124, by rfl⟩ : syracuseStep 537499 = 806249) B806249
theorem B537551 : Blo 535802 537551 := bstep (se 1 (by rfl) ⟨403163, by rfl⟩ : syracuseStep 537551 = 806327) B806327
theorem B537575 : Blo 535802 537575 := bstep (se 1 (by rfl) ⟨403181, by rfl⟩ : syracuseStep 537575 = 806363) B806363
theorem B1815695 : Blo 535802 1815695 := bstep (se 1 (by rfl) ⟨1361771, by rfl⟩ : syracuseStep 1815695 = 2723543) B2723543
theorem B603355 : Blo 535802 603355 := bstep (se 1 (by rfl) ⟨452516, by rfl⟩ : syracuseStep 603355 = 905033) B905033
theorem B1357033 : Blo 535802 1357033 := bstep (se 2 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 1357033 = 1017775) B1017775
theorem B537887 : Blo 535802 537887 := bstep (se 1 (by rfl) ⟨403415, by rfl⟩ : syracuseStep 537887 = 806831) B806831
theorem B537947 : Blo 535802 537947 := bstep (se 1 (by rfl) ⟨403460, by rfl⟩ : syracuseStep 537947 = 806921) B806921
theorem B537967 : Blo 535802 537967 := bstep (se 1 (by rfl) ⟨403475, by rfl⟩ : syracuseStep 537967 = 806951) B806951
theorem B1357195 : Blo 535802 1357195 := bstep (se 1 (by rfl) ⟨1017896, by rfl⟩ : syracuseStep 1357195 = 2035793) B2035793
theorem B538023 : Blo 535802 538023 := bstep (se 1 (by rfl) ⟨403517, by rfl⟩ : syracuseStep 538023 = 807035) B807035
theorem B603643 : Blo 535802 603643 := bstep (se 1 (by rfl) ⟨452732, by rfl⟩ : syracuseStep 603643 = 905465) B905465
theorem B538107 : Blo 535802 538107 := bstep (se 1 (by rfl) ⟨403580, by rfl⟩ : syracuseStep 538107 = 807161) B807161
theorem B538175 : Blo 535802 538175 := bstep (se 1 (by rfl) ⟨403631, by rfl⟩ : syracuseStep 538175 = 807263) B807263
theorem B538183 : Blo 535802 538183 := bstep (se 1 (by rfl) ⟨403637, by rfl⟩ : syracuseStep 538183 = 807275) B807275
theorem B603823 : Blo 535802 603823 := bstep (se 1 (by rfl) ⟨452867, by rfl⟩ : syracuseStep 603823 = 905735) B905735
theorem B1357499 : Blo 535802 1357499 := bstep (se 1 (by rfl) ⟨1018124, by rfl⟩ : syracuseStep 1357499 = 2036249) B2036249
theorem B3061435 : Blo 535802 3061435 := bstep (se 1 (by rfl) ⟨2296076, by rfl⟩ : syracuseStep 3061435 = 4592153) B4592153
theorem B538335 : Blo 535802 538335 := bstep (se 1 (by rfl) ⟨403751, by rfl⟩ : syracuseStep 538335 = 807503) B807503
theorem B6534893 : Blo 535802 6534893 := bstep (se 3 (by rfl) ⟨1225292, by rfl⟩ : syracuseStep 6534893 = 2450585) B2450585
theorem B538415 : Blo 535802 538415 := bstep (se 1 (by rfl) ⟨403811, by rfl⟩ : syracuseStep 538415 = 807623) B807623
theorem B538523 : Blo 535802 538523 := bstep (se 1 (by rfl) ⟨403892, by rfl⟩ : syracuseStep 538523 = 807785) B807785
theorem B604111 : Blo 535802 604111 := bstep (se 1 (by rfl) ⟨453083, by rfl⟩ : syracuseStep 604111 = 906167) B906167
theorem B538575 : Blo 535802 538575 := bstep (se 1 (by rfl) ⟨403931, by rfl⟩ : syracuseStep 538575 = 807863) B807863
theorem B538599 : Blo 535802 538599 := bstep (se 1 (by rfl) ⟨403949, by rfl⟩ : syracuseStep 538599 = 807899) B807899
theorem B1816829 : Blo 535802 1816829 := bstep (se 3 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 1816829 = 681311) B681311
theorem B538911 : Blo 535802 538911 := bstep (se 1 (by rfl) ⟨404183, by rfl⟩ : syracuseStep 538911 = 808367) B808367
theorem B604507 : Blo 535802 604507 := bstep (se 1 (by rfl) ⟨453380, by rfl⟩ : syracuseStep 604507 = 906761) B906761
theorem B538971 : Blo 535802 538971 := bstep (se 1 (by rfl) ⟨404228, by rfl⟩ : syracuseStep 538971 = 808457) B808457
theorem B538991 : Blo 535802 538991 := bstep (se 1 (by rfl) ⟨404243, by rfl⟩ : syracuseStep 538991 = 808487) B808487
theorem B539047 : Blo 535802 539047 := bstep (se 1 (by rfl) ⟨404285, by rfl⟩ : syracuseStep 539047 = 808571) B808571
theorem B604615 : Blo 535802 604615 := bstep (se 1 (by rfl) ⟨453461, by rfl⟩ : syracuseStep 604615 = 906923) B906923
theorem B539131 : Blo 535802 539131 := bstep (se 1 (by rfl) ⟨404348, by rfl⟩ : syracuseStep 539131 = 808697) B808697
theorem B2177599 : Blo 535802 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B539199 : Blo 535802 539199 := bstep (se 1 (by rfl) ⟨404399, by rfl⟩ : syracuseStep 539199 = 808799) B808799
theorem B539207 : Blo 535802 539207 := bstep (se 1 (by rfl) ⟨404405, by rfl⟩ : syracuseStep 539207 = 808811) B808811
theorem B539359 : Blo 535802 539359 := bstep (se 1 (by rfl) ⟨404519, by rfl⟩ : syracuseStep 539359 = 809039) B809039
theorem B604975 : Blo 535802 604975 := bstep (se 1 (by rfl) ⟨453731, by rfl⟩ : syracuseStep 604975 = 907463) B907463
theorem B539439 : Blo 535802 539439 := bstep (se 1 (by rfl) ⟨404579, by rfl⟩ : syracuseStep 539439 = 809159) B809159
theorem B605083 : Blo 535802 605083 := bstep (se 1 (by rfl) ⟨453812, by rfl⟩ : syracuseStep 605083 = 907625) B907625
theorem B539547 : Blo 535802 539547 := bstep (se 1 (by rfl) ⟨404660, by rfl⟩ : syracuseStep 539547 = 809321) B809321
theorem B539599 : Blo 535802 539599 := bstep (se 1 (by rfl) ⟨404699, by rfl⟩ : syracuseStep 539599 = 809399) B809399
theorem B539623 : Blo 535802 539623 := bstep (se 1 (by rfl) ⟨404717, by rfl⟩ : syracuseStep 539623 = 809435) B809435
theorem B1817639 : Blo 535802 1817639 := bstep (se 1 (by rfl) ⟨1363229, by rfl⟩ : syracuseStep 1817639 = 2726459) B2726459
theorem B605479 : Blo 535802 605479 := bstep (se 1 (by rfl) ⟨454109, by rfl⟩ : syracuseStep 605479 = 908219) B908219
theorem B605551 : Blo 535802 605551 := bstep (se 1 (by rfl) ⟨454163, by rfl⟩ : syracuseStep 605551 = 908327) B908327
theorem B1818071 : Blo 535802 1818071 := bstep (se 1 (by rfl) ⟨1363553, by rfl⟩ : syracuseStep 1818071 = 2727107) B2727107
theorem B5586425 : Blo 535802 5586425 := bstep (se 2 (by rfl) ⟨2094909, by rfl⟩ : syracuseStep 5586425 = 4189819) B4189819
theorem B605767 : Blo 535802 605767 := bstep (se 1 (by rfl) ⟨454325, by rfl⟩ : syracuseStep 605767 = 908651) B908651
theorem B1359443 : Blo 535802 1359443 := bstep (se 1 (by rfl) ⟨1019582, by rfl⟩ : syracuseStep 1359443 = 2039165) B2039165
theorem B5979793 : Blo 535802 5979793 := bstep (se 2 (by rfl) ⟨2242422, by rfl⟩ : syracuseStep 5979793 = 4484845) B4484845
theorem B3260267 : Blo 535802 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B1294465 : Blo 535802 1294465 := bstep (se 2 (by rfl) ⟨485424, by rfl⟩ : syracuseStep 1294465 = 970849) B970849
theorem B606631 : Blo 535802 606631 := bstep (se 1 (by rfl) ⟨454973, by rfl⟩ : syracuseStep 606631 = 909947) B909947
theorem B967231 : Blo 535802 967231 := bstep (se 1 (by rfl) ⟨725423, by rfl⟩ : syracuseStep 967231 = 1450847) B1450847
theorem B1295023 : Blo 535802 1295023 := bstep (se 1 (by rfl) ⟨971267, by rfl⟩ : syracuseStep 1295023 = 1942535) B1942535
theorem B1360871 : Blo 535802 1360871 := bstep (se 1 (by rfl) ⟨1020653, by rfl⟩ : syracuseStep 1360871 = 2041307) B2041307
theorem B607207 : Blo 535802 607207 := bstep (se 1 (by rfl) ⟨455405, by rfl⟩ : syracuseStep 607207 = 910811) B910811
theorem B1819745 : Blo 535802 1819745 := bstep (se 2 (by rfl) ⟨682404, by rfl⟩ : syracuseStep 1819745 = 1364809) B1364809
theorem B804059 : Blo 535802 804059 := bstep (se 1 (by rfl) ⟨603044, by rfl⟩ : syracuseStep 804059 = 1206089) B1206089
theorem B804233 : Blo 535802 804233 := bstep (se 2 (by rfl) ⟨301587, by rfl⟩ : syracuseStep 804233 = 603175) B603175
theorem B1361569 : Blo 535802 1361569 := bstep (se 2 (by rfl) ⟨510588, by rfl⟩ : syracuseStep 1361569 = 1021177) B1021177
theorem B804587 : Blo 535802 804587 := bstep (se 1 (by rfl) ⟨603440, by rfl⟩ : syracuseStep 804587 = 1206881) B1206881
theorem B1361711 : Blo 535802 1361711 := bstep (se 1 (by rfl) ⟨1021283, by rfl⟩ : syracuseStep 1361711 = 2042567) B2042567
theorem B804815 : Blo 535802 804815 := bstep (se 1 (by rfl) ⟨603611, by rfl⟩ : syracuseStep 804815 = 1207223) B1207223
theorem B805211 : Blo 535802 805211 := bstep (se 1 (by rfl) ⟨603908, by rfl⟩ : syracuseStep 805211 = 1207817) B1207817
theorem B1034587 : Blo 535802 1034587 := bstep (se 1 (by rfl) ⟨775940, by rfl⟩ : syracuseStep 1034587 = 1551881) B1551881
theorem B1821095 : Blo 535802 1821095 := bstep (se 1 (by rfl) ⟨1365821, by rfl⟩ : syracuseStep 1821095 = 2731643) B2731643
theorem B1362359 : Blo 535802 1362359 := bstep (se 1 (by rfl) ⟨1021769, by rfl⟩ : syracuseStep 1362359 = 2043539) B2043539
theorem B805439 : Blo 535802 805439 := bstep (se 1 (by rfl) ⟨604079, by rfl⟩ : syracuseStep 805439 = 1208159) B1208159
theorem B1821257 : Blo 535802 1821257 := bstep (se 2 (by rfl) ⟨682971, by rfl⟩ : syracuseStep 1821257 = 1365943) B1365943
theorem B805559 : Blo 535802 805559 := bstep (se 1 (by rfl) ⟨604169, by rfl⟩ : syracuseStep 805559 = 1208339) B1208339
theorem B805787 : Blo 535802 805787 := bstep (se 1 (by rfl) ⟨604340, by rfl⟩ : syracuseStep 805787 = 1208681) B1208681
theorem B2444327 : Blo 535802 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B11619395 : Blo 535802 11619395 := bstep (se 1 (by rfl) ⟨8714546, by rfl⟩ : syracuseStep 11619395 = 17429093) B17429093
theorem B4344947 : Blo 535802 4344947 := bstep (se 1 (by rfl) ⟨3258710, by rfl⟩ : syracuseStep 4344947 = 6517421) B6517421
theorem B806183 : Blo 535802 806183 := bstep (se 1 (by rfl) ⟨604637, by rfl⟩ : syracuseStep 806183 = 1209275) B1209275
theorem B806267 : Blo 535802 806267 := bstep (se 1 (by rfl) ⟨604700, by rfl⟩ : syracuseStep 806267 = 1209401) B1209401
theorem B806393 : Blo 535802 806393 := bstep (se 2 (by rfl) ⟨302397, by rfl⟩ : syracuseStep 806393 = 604795) B604795
theorem B1363463 : Blo 535802 1363463 := bstep (se 1 (by rfl) ⟨1022597, by rfl⟩ : syracuseStep 1363463 = 2045195) B2045195
theorem B1363513 : Blo 535802 1363513 := bstep (se 2 (by rfl) ⟨511317, by rfl⟩ : syracuseStep 1363513 = 1022635) B1022635
theorem B806495 : Blo 535802 806495 := bstep (se 1 (by rfl) ⟨604871, by rfl⟩ : syracuseStep 806495 = 1209743) B1209743
theorem B904891 : Blo 535802 904891 := bstep (se 1 (by rfl) ⟨678668, by rfl⟩ : syracuseStep 904891 = 1357337) B1357337
theorem B4148945 : Blo 535802 4148945 := bstep (se 2 (by rfl) ⟨1555854, by rfl⟩ : syracuseStep 4148945 = 3111709) B3111709
theorem B10342187 : Blo 535802 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B806711 : Blo 535802 806711 := bstep (se 1 (by rfl) ⟨605033, by rfl⟩ : syracuseStep 806711 = 1210067) B1210067
theorem B1363817 : Blo 535802 1363817 := bstep (se 2 (by rfl) ⟨511431, by rfl⟩ : syracuseStep 1363817 = 1022863) B1022863
theorem B9818171 : Blo 535802 9818171 := bstep (se 1 (by rfl) ⟨7363628, by rfl⟩ : syracuseStep 9818171 = 14727257) B14727257
theorem B807017 : Blo 535802 807017 := bstep (se 2 (by rfl) ⟨302631, by rfl⟩ : syracuseStep 807017 = 605263) B605263
theorem B807335 : Blo 535802 807335 := bstep (se 1 (by rfl) ⟨605501, by rfl⟩ : syracuseStep 807335 = 1211003) B1211003
theorem B1364435 : Blo 535802 1364435 := bstep (se 1 (by rfl) ⟨1023326, by rfl⟩ : syracuseStep 1364435 = 2046653) B2046653
theorem B807419 : Blo 535802 807419 := bstep (se 1 (by rfl) ⟨605564, by rfl⟩ : syracuseStep 807419 = 1211129) B1211129
theorem B807545 : Blo 535802 807545 := bstep (se 2 (by rfl) ⟨302829, by rfl⟩ : syracuseStep 807545 = 605659) B605659
theorem B807599 : Blo 535802 807599 := bstep (se 1 (by rfl) ⟨605699, by rfl⟩ : syracuseStep 807599 = 1211399) B1211399
theorem B807647 : Blo 535802 807647 := bstep (se 1 (by rfl) ⟨605735, by rfl⟩ : syracuseStep 807647 = 1211471) B1211471
theorem B905951 : Blo 535802 905951 := bstep (se 1 (by rfl) ⟨679463, by rfl⟩ : syracuseStep 905951 = 1358927) B1358927
theorem B545503 : Blo 535802 545503 := bstep (se 1 (by rfl) ⟨409127, by rfl⟩ : syracuseStep 545503 = 818255) B818255
theorem B1725263 : Blo 535802 1725263 := bstep (se 1 (by rfl) ⟨1293947, by rfl⟩ : syracuseStep 1725263 = 2587895) B2587895
theorem B5297125 : Blo 535802 5297125 := bstep (se 4 (by rfl) ⟨496605, by rfl⟩ : syracuseStep 5297125 = 993211) B993211
theorem B807911 : Blo 535802 807911 := bstep (se 1 (by rfl) ⟨605933, by rfl⟩ : syracuseStep 807911 = 1211867) B1211867
theorem B906383 : Blo 535802 906383 := bstep (se 1 (by rfl) ⟨679787, by rfl⟩ : syracuseStep 906383 = 1359575) B1359575
theorem B808169 : Blo 535802 808169 := bstep (se 2 (by rfl) ⟨303063, by rfl⟩ : syracuseStep 808169 = 606127) B606127
theorem B808223 : Blo 535802 808223 := bstep (se 1 (by rfl) ⟨606167, by rfl⟩ : syracuseStep 808223 = 1212335) B1212335
theorem B20108645 : Blo 535802 20108645 := bstep (se 4 (by rfl) ⟨1885185, by rfl⟩ : syracuseStep 20108645 = 3770371) B3770371
theorem B906619 : Blo 535802 906619 := bstep (se 1 (by rfl) ⟨679964, by rfl⟩ : syracuseStep 906619 = 1359929) B1359929
theorem B808391 : Blo 535802 808391 := bstep (se 1 (by rfl) ⟨606293, by rfl⟩ : syracuseStep 808391 = 1212587) B1212587
theorem B1529351 : Blo 535802 1529351 := bstep (se 1 (by rfl) ⟨1147013, by rfl⟩ : syracuseStep 1529351 = 2294027) B2294027
theorem B1365599 : Blo 535802 1365599 := bstep (se 1 (by rfl) ⟨1024199, by rfl⟩ : syracuseStep 1365599 = 2048399) B2048399
theorem B808745 : Blo 535802 808745 := bstep (se 2 (by rfl) ⟨303279, by rfl⟩ : syracuseStep 808745 = 606559) B606559
theorem B808751 : Blo 535802 808751 := bstep (se 1 (by rfl) ⟨606563, by rfl⟩ : syracuseStep 808751 = 1213127) B1213127
theorem B1529705 : Blo 535802 1529705 := bstep (se 2 (by rfl) ⟨573639, by rfl⟩ : syracuseStep 1529705 = 1147279) B1147279
theorem B809225 : Blo 535802 809225 := bstep (se 2 (by rfl) ⟨303459, by rfl⟩ : syracuseStep 809225 = 606919) B606919
theorem B809327 : Blo 535802 809327 := bstep (se 1 (by rfl) ⟨606995, by rfl⟩ : syracuseStep 809327 = 1213991) B1213991
theorem B2447759 : Blo 535802 2447759 := bstep (se 1 (by rfl) ⟨1835819, by rfl⟩ : syracuseStep 2447759 = 3671639) B3671639
theorem B645575 : Blo 535802 645575 := bstep (se 1 (by rfl) ⟨484181, by rfl⟩ : syracuseStep 645575 = 968363) B968363
theorem B678395 : Blo 535802 678395 := bstep (se 1 (by rfl) ⟨508796, by rfl⟩ : syracuseStep 678395 = 1017593) B1017593
theorem B809543 : Blo 535802 809543 := bstep (se 1 (by rfl) ⟨607157, by rfl⟩ : syracuseStep 809543 = 1214315) B1214315
theorem B809579 : Blo 535802 809579 := bstep (se 1 (by rfl) ⟨607184, by rfl⟩ : syracuseStep 809579 = 1214369) B1214369
theorem B2185903 : Blo 535802 2185903 := bstep (se 1 (by rfl) ⟨1639427, by rfl⟩ : syracuseStep 2185903 = 3278855) B3278855
theorem B908111 : Blo 535802 908111 := bstep (se 1 (by rfl) ⟨681083, by rfl⟩ : syracuseStep 908111 = 1362167) B1362167
theorem B9198521 : Blo 535802 9198521 := bstep (se 2 (by rfl) ⟨3449445, by rfl⟩ : syracuseStep 9198521 = 6898891) B6898891
theorem B3071141 : Blo 535802 3071141 := bstep (se 4 (by rfl) ⟨287919, by rfl⟩ : syracuseStep 3071141 = 575839) B575839
theorem B679367 : Blo 535802 679367 := bstep (se 1 (by rfl) ⟨509525, by rfl⟩ : syracuseStep 679367 = 1019051) B1019051
theorem B1727993 : Blo 535802 1727993 := bstep (se 2 (by rfl) ⟨647997, by rfl⟩ : syracuseStep 1727993 = 1295995) B1295995
theorem B679519 : Blo 535802 679519 := bstep (se 1 (by rfl) ⟨509639, by rfl⟩ : syracuseStep 679519 = 1019279) B1019279
theorem B4579031 : Blo 535802 4579031 := bstep (se 1 (by rfl) ⟨3434273, by rfl⟩ : syracuseStep 4579031 = 6868547) B6868547
theorem B909103 : Blo 535802 909103 := bstep (se 1 (by rfl) ⟨681827, by rfl⟩ : syracuseStep 909103 = 1363655) B1363655
theorem B2187137 : Blo 535802 2187137 := bstep (se 2 (by rfl) ⟨820176, by rfl⟩ : syracuseStep 2187137 = 1640353) B1640353
theorem B1532267 : Blo 535802 1532267 := bstep (se 1 (by rfl) ⟨1149200, by rfl⟩ : syracuseStep 1532267 = 2298401) B2298401
theorem B1631195 : Blo 535802 1631195 := bstep (se 1 (by rfl) ⟨1223396, by rfl⟩ : syracuseStep 1631195 = 2446793) B2446793
theorem B2581703 : Blo 535802 2581703 := bstep (se 1 (by rfl) ⟨1936277, by rfl⟩ : syracuseStep 2581703 = 3872555) B3872555
theorem B3073625 : Blo 535802 3073625 := bstep (se 2 (by rfl) ⟨1152609, by rfl⟩ : syracuseStep 3073625 = 2305219) B2305219
theorem B1205855 : Blo 535802 1205855 := bstep (se 1 (by rfl) ⟨904391, by rfl⟩ : syracuseStep 1205855 = 1808783) B1808783
theorem B5793569 : Blo 535802 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B1206071 : Blo 535802 1206071 := bstep (se 1 (by rfl) ⟨904553, by rfl⟩ : syracuseStep 1206071 = 1809107) B1809107
theorem B5891945 : Blo 535802 5891945 := bstep (se 2 (by rfl) ⟨2209479, by rfl⟩ : syracuseStep 5891945 = 4418959) B4418959
theorem B681959 : Blo 535802 681959 := bstep (se 1 (by rfl) ⟨511469, by rfl⟩ : syracuseStep 681959 = 1022939) B1022939
theorem B1206377 : Blo 535802 1206377 := bstep (se 2 (by rfl) ⟨452391, by rfl⟩ : syracuseStep 1206377 = 904783) B904783
theorem B2910343 : Blo 535802 2910343 := bstep (se 1 (by rfl) ⟨2182757, by rfl⟩ : syracuseStep 2910343 = 4365515) B4365515
theorem B4581629 : Blo 535802 4581629 := bstep (se 3 (by rfl) ⟨859055, by rfl⟩ : syracuseStep 4581629 = 1718111) B1718111
theorem B8841737 : Blo 535802 8841737 := bstep (se 2 (by rfl) ⟨3315651, by rfl⟩ : syracuseStep 8841737 = 6631303) B6631303
theorem B1206863 : Blo 535802 1206863 := bstep (se 1 (by rfl) ⟨905147, by rfl⟩ : syracuseStep 1206863 = 1810295) B1810295
theorem B5827261 : Blo 535802 5827261 := bstep (se 3 (by rfl) ⟨1092611, by rfl⟩ : syracuseStep 5827261 = 2185223) B2185223
theorem B1207007 : Blo 535802 1207007 := bstep (se 1 (by rfl) ⟨905255, by rfl⟩ : syracuseStep 1207007 = 1810511) B1810511
theorem B1207259 : Blo 535802 1207259 := bstep (se 1 (by rfl) ⟨905444, by rfl⟩ : syracuseStep 1207259 = 1810889) B1810889
theorem B1207439 : Blo 535802 1207439 := bstep (se 1 (by rfl) ⟨905579, by rfl⟩ : syracuseStep 1207439 = 1811159) B1811159
theorem B1207529 : Blo 535802 1207529 := bstep (se 2 (by rfl) ⟨452823, by rfl⟩ : syracuseStep 1207529 = 905647) B905647
theorem B1207583 : Blo 535802 1207583 := bstep (se 1 (by rfl) ⟨905687, by rfl⟩ : syracuseStep 1207583 = 1811375) B1811375
theorem B2583839 : Blo 535802 2583839 := bstep (se 1 (by rfl) ⟨1937879, by rfl⟩ : syracuseStep 2583839 = 3875759) B3875759
theorem B1208105 : Blo 535802 1208105 := bstep (se 2 (by rfl) ⟨453039, by rfl⟩ : syracuseStep 1208105 = 906079) B906079
theorem B1209167 : Blo 535802 1209167 := bstep (se 1 (by rfl) ⟨906875, by rfl⟩ : syracuseStep 1209167 = 1813751) B1813751
theorem B2716577 : Blo 535802 2716577 := bstep (se 2 (by rfl) ⟨1018716, by rfl⟩ : syracuseStep 2716577 = 2037433) B2037433
theorem B2290679 : Blo 535802 2290679 := bstep (se 1 (by rfl) ⟨1718009, by rfl⟩ : syracuseStep 2290679 = 3436019) B3436019
theorem B1209383 : Blo 535802 1209383 := bstep (se 1 (by rfl) ⟨907037, by rfl⟩ : syracuseStep 1209383 = 1814075) B1814075
theorem B1864919 : Blo 535802 1864919 := bstep (se 1 (by rfl) ⟨1398689, by rfl⟩ : syracuseStep 1864919 = 2797379) B2797379
theorem B1209563 : Blo 535802 1209563 := bstep (se 1 (by rfl) ⟨907172, by rfl⟩ : syracuseStep 1209563 = 1814345) B1814345
theorem B1209761 : Blo 535802 1209761 := bstep (se 2 (by rfl) ⟨453660, by rfl⟩ : syracuseStep 1209761 = 907321) B907321
theorem B6879005 : Blo 535802 6879005 := bstep (se 3 (by rfl) ⟨1289813, by rfl⟩ : syracuseStep 6879005 = 2579627) B2579627
theorem B2619191 : Blo 535802 2619191 := bstep (se 1 (by rfl) ⟨1964393, by rfl⟩ : syracuseStep 2619191 = 3928787) B3928787
theorem B9598907 : Blo 535802 9598907 := bstep (se 1 (by rfl) ⟨7199180, by rfl⟩ : syracuseStep 9598907 = 14398361) B14398361
theorem B1210319 : Blo 535802 1210319 := bstep (se 1 (by rfl) ⟨907739, by rfl⟩ : syracuseStep 1210319 = 1815479) B1815479
theorem B5830937 : Blo 535802 5830937 := bstep (se 2 (by rfl) ⟨2186601, by rfl⟩ : syracuseStep 5830937 = 4373203) B4373203
theorem B1210697 : Blo 535802 1210697 := bstep (se 2 (by rfl) ⟨454011, by rfl⟩ : syracuseStep 1210697 = 908023) B908023
theorem B1210715 : Blo 535802 1210715 := bstep (se 1 (by rfl) ⟨908036, by rfl⟩ : syracuseStep 1210715 = 1816073) B1816073
theorem B1211291 : Blo 535802 1211291 := bstep (se 1 (by rfl) ⟨908468, by rfl⟩ : syracuseStep 1211291 = 1816937) B1816937
theorem B2915315 : Blo 535802 2915315 := bstep (se 1 (by rfl) ⟨2186486, by rfl⟩ : syracuseStep 2915315 = 4372973) B4372973
theorem B1211489 : Blo 535802 1211489 := bstep (se 2 (by rfl) ⟨454308, by rfl⟩ : syracuseStep 1211489 = 908617) B908617
theorem B7371899 : Blo 535802 7371899 := bstep (se 1 (by rfl) ⟨5528924, by rfl⟩ : syracuseStep 7371899 = 11057849) B11057849
theorem B1146143 : Blo 535802 1146143 := bstep (se 1 (by rfl) ⟨859607, by rfl⟩ : syracuseStep 1146143 = 1719215) B1719215
theorem B2719007 : Blo 535802 2719007 := bstep (se 1 (by rfl) ⟨2039255, by rfl⟩ : syracuseStep 2719007 = 4078511) B4078511
theorem B1211687 : Blo 535802 1211687 := bstep (se 1 (by rfl) ⟨908765, by rfl⟩ : syracuseStep 1211687 = 1817531) B1817531
theorem B2489737 : Blo 535802 2489737 := bstep (se 2 (by rfl) ⟨933651, by rfl⟩ : syracuseStep 2489737 = 1867303) B1867303
theorem B2915921 : Blo 535802 2915921 := bstep (se 2 (by rfl) ⟨1093470, by rfl⟩ : syracuseStep 2915921 = 2186941) B2186941
theorem B2293343 : Blo 535802 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B1212065 : Blo 535802 1212065 := bstep (se 2 (by rfl) ⟨454524, by rfl⟩ : syracuseStep 1212065 = 909049) B909049
theorem B1572587 : Blo 535802 1572587 := bstep (se 1 (by rfl) ⟨1179440, by rfl⟩ : syracuseStep 1572587 = 2358881) B2358881
theorem B687919 : Blo 535802 687919 := bstep (se 1 (by rfl) ⟨515939, by rfl⟩ : syracuseStep 687919 = 1031879) B1031879
theorem B2457391 : Blo 535802 2457391 := bstep (se 1 (by rfl) ⟨1843043, by rfl⟩ : syracuseStep 2457391 = 3686087) B3686087
theorem B2490401 : Blo 535802 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B2753153 : Blo 535802 2753153 := bstep (se 2 (by rfl) ⟨1032432, by rfl⟩ : syracuseStep 2753153 = 2064865) B2064865
theorem B1213163 : Blo 535802 1213163 := bstep (se 1 (by rfl) ⟨909872, by rfl⟩ : syracuseStep 1213163 = 1819745) B1819745
theorem B1639379 : Blo 535802 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B10356335 : Blo 535802 10356335 := bstep (se 1 (by rfl) ⟨7767251, by rfl⟩ : syracuseStep 10356335 = 15534503) B15534503
theorem B6227567 : Blo 535802 6227567 := bstep (se 1 (by rfl) ⟨4670675, by rfl⟩ : syracuseStep 6227567 = 9341351) B9341351
theorem B1214063 : Blo 535802 1214063 := bstep (se 1 (by rfl) ⟨910547, by rfl⟩ : syracuseStep 1214063 = 1821095) B1821095
theorem B2066081 : Blo 535802 2066081 := bstep (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) B1549561
theorem B1214171 : Blo 535802 1214171 := bstep (se 1 (by rfl) ⟨910628, by rfl⟩ : syracuseStep 1214171 = 1821257) B1821257
theorem B4589419 : Blo 535802 4589419 := bstep (se 1 (by rfl) ⟨3442064, by rfl⟩ : syracuseStep 4589419 = 6884129) B6884129
theorem B11470891 : Blo 535802 11470891 := bstep (se 1 (by rfl) ⟨8603168, by rfl⟩ : syracuseStep 11470891 = 17206337) B17206337
theorem B1313063 : Blo 535802 1313063 := bstep (se 1 (by rfl) ⟨984797, by rfl⟩ : syracuseStep 1313063 = 1969595) B1969595
theorem B2722409 : Blo 535802 2722409 := bstep (se 2 (by rfl) ⟨1020903, by rfl⟩ : syracuseStep 2722409 = 2041807) B2041807
theorem B1641131 : Blo 535802 1641131 := bstep (se 1 (by rfl) ⟨1230848, by rfl⟩ : syracuseStep 1641131 = 2461697) B2461697
theorem B3279635 : Blo 535802 3279635 := bstep (se 1 (by rfl) ⟨2459726, by rfl⟩ : syracuseStep 3279635 = 4919453) B4919453
theorem B2591777 : Blo 535802 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B1379449 : Blo 535802 1379449 := bstep (se 2 (by rfl) ⟨517293, by rfl⟩ : syracuseStep 1379449 = 1034587) B1034587
theorem B1838279 : Blo 535802 1838279 := bstep (se 1 (by rfl) ⟨1378709, by rfl⟩ : syracuseStep 1838279 = 2757419) B2757419
theorem B1150175 : Blo 535802 1150175 := bstep (se 1 (by rfl) ⟨862631, by rfl⟩ : syracuseStep 1150175 = 1725263) B1725263
theorem B13405763 : Blo 535802 13405763 := bstep (se 1 (by rfl) ⟨10054322, by rfl⟩ : syracuseStep 13405763 = 20108645) B20108645
theorem B7769681 : Blo 535802 7769681 := bstep (se 2 (by rfl) ⟨2913630, by rfl⟩ : syracuseStep 7769681 = 5827261) B5827261
theorem B2035307 : Blo 535802 2035307 := bstep (se 1 (by rfl) ⟨1526480, by rfl⟩ : syracuseStep 2035307 = 3052961) B3052961
theorem B1019567 : Blo 535802 1019567 := bstep (se 1 (by rfl) ⟨764675, by rfl⟩ : syracuseStep 1019567 = 1529351) B1529351
theorem B2723705 : Blo 535802 2723705 := bstep (se 2 (by rfl) ⟨1021389, by rfl⟩ : syracuseStep 2723705 = 2042779) B2042779
theorem B1150841 : Blo 535802 1150841 := bstep (se 2 (by rfl) ⟨431565, by rfl⟩ : syracuseStep 1150841 = 863131) B863131
theorem B1019803 : Blo 535802 1019803 := bstep (se 1 (by rfl) ⟨764852, by rfl⟩ : syracuseStep 1019803 = 1529705) B1529705
theorem B7737727 : Blo 535802 7737727 := bstep (se 1 (by rfl) ⟨5803295, by rfl⟩ : syracuseStep 7737727 = 11606591) B11606591
theorem B6132347 : Blo 535802 6132347 := bstep (se 1 (by rfl) ⟨4599260, by rfl⟩ : syracuseStep 6132347 = 9198521) B9198521
theorem B6886133 : Blo 535802 6886133 := bstep (se 5 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 6886133 = 645575) B645575
theorem B1151995 : Blo 535802 1151995 := bstep (se 1 (by rfl) ⟨863996, by rfl⟩ : syracuseStep 1151995 = 1727993) B1727993
theorem B3937319 : Blo 535802 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B3052687 : Blo 535802 3052687 := bstep (se 1 (by rfl) ⟨2289515, by rfl⟩ : syracuseStep 3052687 = 4579031) B4579031
theorem B2036947 : Blo 535802 2036947 := bstep (se 1 (by rfl) ⟨1527710, by rfl⟩ : syracuseStep 2036947 = 3055421) B3055421
theorem B1152481 : Blo 535802 1152481 := bstep (se 2 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 1152481 = 864361) B864361
theorem B1021511 : Blo 535802 1021511 := bstep (se 1 (by rfl) ⟨766133, by rfl⟩ : syracuseStep 1021511 = 1532267) B1532267
theorem B2037419 : Blo 535802 2037419 := bstep (se 1 (by rfl) ⟨1528064, by rfl⟩ : syracuseStep 2037419 = 3056129) B3056129
theorem B1087463 : Blo 535802 1087463 := bstep (se 1 (by rfl) ⟨815597, by rfl⟩ : syracuseStep 1087463 = 1631195) B1631195
theorem B4593793 : Blo 535802 4593793 := bstep (se 2 (by rfl) ⟨1722672, by rfl⟩ : syracuseStep 4593793 = 3445345) B3445345
theorem B727337 : Blo 535802 727337 := bstep (se 2 (by rfl) ⟨272751, by rfl⟩ : syracuseStep 727337 = 545503) B545503
theorem B89332109 : Blo 535802 89332109 := bstep (se 3 (by rfl) ⟨16749770, by rfl⟩ : syracuseStep 89332109 = 33499541) B33499541
theorem B1809053 : Blo 535802 1809053 := bstep (se 3 (by rfl) ⟨339197, by rfl⟩ : syracuseStep 1809053 = 678395) B678395
theorem B3054419 : Blo 535802 3054419 := bstep (se 1 (by rfl) ⟨2290814, by rfl⟩ : syracuseStep 3054419 = 4581629) B4581629
theorem B1809377 : Blo 535802 1809377 := bstep (se 2 (by rfl) ⟨678516, by rfl⟩ : syracuseStep 1809377 = 1357033) B1357033
theorem B1809593 : Blo 535802 1809593 := bstep (se 2 (by rfl) ⟨678597, by rfl⟩ : syracuseStep 1809593 = 1357195) B1357195
theorem B7938107 : Blo 535802 7938107 := bstep (se 1 (by rfl) ⟨5953580, by rfl⟩ : syracuseStep 7938107 = 11907161) B11907161
theorem B1811051 : Blo 535802 1811051 := bstep (se 1 (by rfl) ⟨1358288, by rfl⟩ : syracuseStep 1811051 = 2716577) B2716577
theorem B1811645 : Blo 535802 1811645 := bstep (se 3 (by rfl) ⟨339683, by rfl⟩ : syracuseStep 1811645 = 679367) B679367
theorem B1746127 : Blo 535802 1746127 := bstep (se 1 (by rfl) ⟨1309595, by rfl⟩ : syracuseStep 1746127 = 2619191) B2619191
theorem B6399271 : Blo 535802 6399271 := bstep (se 1 (by rfl) ⟨4799453, by rfl⟩ : syracuseStep 6399271 = 9598907) B9598907
theorem B3319649 : Blo 535802 3319649 := bstep (se 2 (by rfl) ⟨1244868, by rfl⟩ : syracuseStep 3319649 = 2489737) B2489737
theorem B1943543 : Blo 535802 1943543 := bstep (se 1 (by rfl) ⟨1457657, by rfl⟩ : syracuseStep 1943543 = 2915315) B2915315
theorem B764095 : Blo 535802 764095 := bstep (se 1 (by rfl) ⟨573071, by rfl⟩ : syracuseStep 764095 = 1146143) B1146143
theorem B1812671 : Blo 535802 1812671 := bstep (se 1 (by rfl) ⟨1359503, by rfl⟩ : syracuseStep 1812671 = 2719007) B2719007
theorem B7973057 : Blo 535802 7973057 := bstep (se 2 (by rfl) ⟨2989896, by rfl⟩ : syracuseStep 7973057 = 5979793) B5979793
theorem B1943947 : Blo 535802 1943947 := bstep (se 1 (by rfl) ⟨1457960, by rfl⟩ : syracuseStep 1943947 = 2915921) B2915921
theorem B2173511 : Blo 535802 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B536039 : Blo 535802 536039 := bstep (se 1 (by rfl) ⟨402029, by rfl⟩ : syracuseStep 536039 = 804059) B804059
theorem B536155 : Blo 535802 536155 := bstep (se 1 (by rfl) ⟨402116, by rfl⟩ : syracuseStep 536155 = 804233) B804233
theorem B1814291 : Blo 535802 1814291 := bstep (se 1 (by rfl) ⟨1360718, by rfl⟩ : syracuseStep 1814291 = 2721437) B2721437
theorem B536391 : Blo 535802 536391 := bstep (se 1 (by rfl) ⟨402293, by rfl⟩ : syracuseStep 536391 = 804587) B804587
theorem B8302445 : Blo 535802 8302445 := bstep (se 3 (by rfl) ⟨1556708, by rfl⟩ : syracuseStep 8302445 = 3113417) B3113417
theorem B536543 : Blo 535802 536543 := bstep (se 1 (by rfl) ⟨402407, by rfl⟩ : syracuseStep 536543 = 804815) B804815
theorem B3453137 : Blo 535802 3453137 := bstep (se 2 (by rfl) ⟨1294926, by rfl⟩ : syracuseStep 3453137 = 2589853) B2589853
theorem B536807 : Blo 535802 536807 := bstep (se 1 (by rfl) ⟨402605, by rfl⟩ : syracuseStep 536807 = 805211) B805211
theorem B3059977 : Blo 535802 3059977 := bstep (se 2 (by rfl) ⟨1147491, by rfl⟩ : syracuseStep 3059977 = 2294983) B2294983
theorem B536959 : Blo 535802 536959 := bstep (se 1 (by rfl) ⟨402719, by rfl⟩ : syracuseStep 536959 = 805439) B805439
theorem B537039 : Blo 535802 537039 := bstep (se 1 (by rfl) ⟨402779, by rfl⟩ : syracuseStep 537039 = 805559) B805559
theorem B537191 : Blo 535802 537191 := bstep (se 1 (by rfl) ⟨402893, by rfl⟩ : syracuseStep 537191 = 805787) B805787
theorem B1815155 : Blo 535802 1815155 := bstep (se 1 (by rfl) ⟨1361366, by rfl⟩ : syracuseStep 1815155 = 2722733) B2722733
theorem B7746263 : Blo 535802 7746263 := bstep (se 1 (by rfl) ⟨5809697, by rfl⟩ : syracuseStep 7746263 = 11619395) B11619395
theorem B2896631 : Blo 535802 2896631 := bstep (se 1 (by rfl) ⟨2172473, by rfl⟩ : syracuseStep 2896631 = 4344947) B4344947
theorem B14725961 : Blo 535802 14725961 := bstep (se 2 (by rfl) ⟨5522235, by rfl⟩ : syracuseStep 14725961 = 11044471) B11044471
theorem B537455 : Blo 535802 537455 := bstep (se 1 (by rfl) ⟨403091, by rfl⟩ : syracuseStep 537455 = 806183) B806183
theorem B1815425 : Blo 535802 1815425 := bstep (se 2 (by rfl) ⟨680784, by rfl⟩ : syracuseStep 1815425 = 1361569) B1361569
theorem B537511 : Blo 535802 537511 := bstep (se 1 (by rfl) ⟨403133, by rfl⟩ : syracuseStep 537511 = 806267) B806267
theorem B537595 : Blo 535802 537595 := bstep (se 1 (by rfl) ⟨403196, by rfl⟩ : syracuseStep 537595 = 806393) B806393
theorem B537663 : Blo 535802 537663 := bstep (se 1 (by rfl) ⟨403247, by rfl⟩ : syracuseStep 537663 = 806495) B806495
theorem B2765963 : Blo 535802 2765963 := bstep (se 1 (by rfl) ⟨2074472, by rfl⟩ : syracuseStep 2765963 = 4148945) B4148945
theorem B3060935 : Blo 535802 3060935 := bstep (se 1 (by rfl) ⟨2295701, by rfl⟩ : syracuseStep 3060935 = 4591403) B4591403
theorem B6894791 : Blo 535802 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B537807 : Blo 535802 537807 := bstep (se 1 (by rfl) ⟨403355, by rfl⟩ : syracuseStep 537807 = 806711) B806711
theorem B538011 : Blo 535802 538011 := bstep (se 1 (by rfl) ⟨403508, by rfl⟩ : syracuseStep 538011 = 807017) B807017
theorem B3880457 : Blo 535802 3880457 := bstep (se 2 (by rfl) ⟨1455171, by rfl⟩ : syracuseStep 3880457 = 2910343) B2910343
theorem B538223 : Blo 535802 538223 := bstep (se 1 (by rfl) ⟨403667, by rfl⟩ : syracuseStep 538223 = 807335) B807335
theorem B5158565 : Blo 535802 5158565 := bstep (se 4 (by rfl) ⟨483615, by rfl⟩ : syracuseStep 5158565 = 967231) B967231
theorem B538279 : Blo 535802 538279 := bstep (se 1 (by rfl) ⟨403709, by rfl⟩ : syracuseStep 538279 = 807419) B807419
theorem B1816235 : Blo 535802 1816235 := bstep (se 1 (by rfl) ⟨1362176, by rfl⟩ : syracuseStep 1816235 = 2724353) B2724353
theorem B538363 : Blo 535802 538363 := bstep (se 1 (by rfl) ⟨403772, by rfl⟩ : syracuseStep 538363 = 807545) B807545
theorem B538399 : Blo 535802 538399 := bstep (se 1 (by rfl) ⟨403799, by rfl⟩ : syracuseStep 538399 = 807599) B807599
theorem B1357631 : Blo 535802 1357631 := bstep (se 1 (by rfl) ⟨1018223, by rfl⟩ : syracuseStep 1357631 = 2036447) B2036447
theorem B603967 : Blo 535802 603967 := bstep (se 1 (by rfl) ⟨452975, by rfl⟩ : syracuseStep 603967 = 905951) B905951
theorem B538431 : Blo 535802 538431 := bstep (se 1 (by rfl) ⟨403823, by rfl⟩ : syracuseStep 538431 = 807647) B807647
theorem B1816559 : Blo 535802 1816559 := bstep (se 1 (by rfl) ⟨1362419, by rfl⟩ : syracuseStep 1816559 = 2724839) B2724839
theorem B538607 : Blo 535802 538607 := bstep (se 1 (by rfl) ⟨403955, by rfl⟩ : syracuseStep 538607 = 807911) B807911
theorem B604255 : Blo 535802 604255 := bstep (se 1 (by rfl) ⟨453191, by rfl⟩ : syracuseStep 604255 = 906383) B906383
theorem B538779 : Blo 535802 538779 := bstep (se 1 (by rfl) ⟨404084, by rfl⟩ : syracuseStep 538779 = 808169) B808169
theorem B1357985 : Blo 535802 1357985 := bstep (se 2 (by rfl) ⟨509244, by rfl⟩ : syracuseStep 1357985 = 1018489) B1018489
theorem B538815 : Blo 535802 538815 := bstep (se 1 (by rfl) ⟨404111, by rfl⟩ : syracuseStep 538815 = 808223) B808223
theorem B1816775 : Blo 535802 1816775 := bstep (se 1 (by rfl) ⟨1362581, by rfl⟩ : syracuseStep 1816775 = 2725163) B2725163
theorem B538927 : Blo 535802 538927 := bstep (se 1 (by rfl) ⟨404195, by rfl⟩ : syracuseStep 538927 = 808391) B808391
theorem B539163 : Blo 535802 539163 := bstep (se 1 (by rfl) ⟨404372, by rfl⟩ : syracuseStep 539163 = 808745) B808745
theorem B539167 : Blo 535802 539167 := bstep (se 1 (by rfl) ⟨404375, by rfl⟩ : syracuseStep 539167 = 808751) B808751
theorem B5519929 : Blo 535802 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B1456697 : Blo 535802 1456697 := bstep (se 2 (by rfl) ⟨546261, by rfl⟩ : syracuseStep 1456697 = 1092523) B1092523
theorem B1817423 : Blo 535802 1817423 := bstep (se 1 (by rfl) ⟨1363067, by rfl⟩ : syracuseStep 1817423 = 2726135) B2726135
theorem B539483 : Blo 535802 539483 := bstep (se 1 (by rfl) ⟨404612, by rfl⟩ : syracuseStep 539483 = 809225) B809225
theorem B1031071 : Blo 535802 1031071 := bstep (se 1 (by rfl) ⟨773303, by rfl⟩ : syracuseStep 1031071 = 1546607) B1546607
theorem B539551 : Blo 535802 539551 := bstep (se 1 (by rfl) ⟨404663, by rfl⟩ : syracuseStep 539551 = 809327) B809327
theorem B539695 : Blo 535802 539695 := bstep (se 1 (by rfl) ⟨404771, by rfl⟩ : syracuseStep 539695 = 809543) B809543
theorem B539719 : Blo 535802 539719 := bstep (se 1 (by rfl) ⟨404789, by rfl⟩ : syracuseStep 539719 = 809579) B809579
theorem B1358977 : Blo 535802 1358977 := bstep (se 2 (by rfl) ⟨509616, by rfl⟩ : syracuseStep 1358977 = 1019233) B1019233
theorem B1817747 : Blo 535802 1817747 := bstep (se 1 (by rfl) ⟨1363310, by rfl⟩ : syracuseStep 1817747 = 2726621) B2726621
theorem B605407 : Blo 535802 605407 := bstep (se 1 (by rfl) ⟨454055, by rfl⟩ : syracuseStep 605407 = 908111) B908111
theorem B1818017 : Blo 535802 1818017 := bstep (se 2 (by rfl) ⟨681756, by rfl⟩ : syracuseStep 1818017 = 1363513) B1363513
theorem B2047427 : Blo 535802 2047427 := bstep (se 1 (by rfl) ⟨1535570, by rfl⟩ : syracuseStep 2047427 = 3071141) B3071141
theorem B15711853 : Blo 535802 15711853 := bstep (se 3 (by rfl) ⟨2945972, by rfl⟩ : syracuseStep 15711853 = 5891945) B5891945
theorem B966287 : Blo 535802 966287 := bstep (se 1 (by rfl) ⟨724715, by rfl⟩ : syracuseStep 966287 = 1449431) B1449431
theorem B1359787 : Blo 535802 1359787 := bstep (se 1 (by rfl) ⟨1019840, by rfl⟩ : syracuseStep 1359787 = 2039681) B2039681
theorem B1458091 : Blo 535802 1458091 := bstep (se 1 (by rfl) ⟨1093568, by rfl⟩ : syracuseStep 1458091 = 2187137) B2187137
theorem B1818557 : Blo 535802 1818557 := bstep (se 3 (by rfl) ⟨340979, by rfl⟩ : syracuseStep 1818557 = 681959) B681959
theorem B1360091 : Blo 535802 1360091 := bstep (se 1 (by rfl) ⟨1020068, by rfl⟩ : syracuseStep 1360091 = 2040137) B2040137
theorem B19939769 : Blo 535802 19939769 := bstep (se 2 (by rfl) ⟨7477413, by rfl⟩ : syracuseStep 19939769 = 14954827) B14954827
theorem B1721135 : Blo 535802 1721135 := bstep (se 1 (by rfl) ⟨1290851, by rfl⟩ : syracuseStep 1721135 = 2581703) B2581703
theorem B1360921 : Blo 535802 1360921 := bstep (se 2 (by rfl) ⟨510345, by rfl⟩ : syracuseStep 1360921 = 1020691) B1020691
theorem B967735 : Blo 535802 967735 := bstep (se 1 (by rfl) ⟨725801, by rfl⟩ : syracuseStep 967735 = 1451603) B1451603
theorem B2049083 : Blo 535802 2049083 := bstep (se 1 (by rfl) ⟨1536812, by rfl⟩ : syracuseStep 2049083 = 3073625) B3073625
theorem B803903 : Blo 535802 803903 := bstep (se 1 (by rfl) ⟨602927, by rfl⟩ : syracuseStep 803903 = 1205855) B1205855
theorem B803945 : Blo 535802 803945 := bstep (se 2 (by rfl) ⟨301479, by rfl⟩ : syracuseStep 803945 = 602959) B602959
theorem B804047 : Blo 535802 804047 := bstep (se 1 (by rfl) ⟨603035, by rfl⟩ : syracuseStep 804047 = 1206071) B1206071
theorem B34784477 : Blo 535802 34784477 := bstep (se 3 (by rfl) ⟨6522089, by rfl⟩ : syracuseStep 34784477 = 13044179) B13044179
theorem B3458315 : Blo 535802 3458315 := bstep (se 1 (by rfl) ⟨2593736, by rfl⟩ : syracuseStep 3458315 = 5187473) B5187473
theorem B7062833 : Blo 535802 7062833 := bstep (se 2 (by rfl) ⟨2648562, by rfl⟩ : syracuseStep 7062833 = 5297125) B5297125
theorem B1361225 : Blo 535802 1361225 := bstep (se 2 (by rfl) ⟨510459, by rfl⟩ : syracuseStep 1361225 = 1020919) B1020919
theorem B23577965 : Blo 535802 23577965 := bstep (se 3 (by rfl) ⟨4420868, by rfl⟩ : syracuseStep 23577965 = 8841737) B8841737
theorem B804251 : Blo 535802 804251 := bstep (se 1 (by rfl) ⟨603188, by rfl⟩ : syracuseStep 804251 = 1206377) B1206377
theorem B6145469 : Blo 535802 6145469 := bstep (se 3 (by rfl) ⟨1152275, by rfl⟩ : syracuseStep 6145469 = 2304551) B2304551
theorem B1361519 : Blo 535802 1361519 := bstep (se 1 (by rfl) ⟨1021139, by rfl⟩ : syracuseStep 1361519 = 2042279) B2042279
theorem B804473 : Blo 535802 804473 := bstep (se 2 (by rfl) ⟨301677, by rfl⟩ : syracuseStep 804473 = 603355) B603355
theorem B804575 : Blo 535802 804575 := bstep (se 1 (by rfl) ⟨603431, by rfl⟩ : syracuseStep 804575 = 1206863) B1206863
theorem B1820447 : Blo 535802 1820447 := bstep (se 1 (by rfl) ⟨1365335, by rfl⟩ : syracuseStep 1820447 = 2730671) B2730671
theorem B804671 : Blo 535802 804671 := bstep (se 1 (by rfl) ⟨603503, by rfl⟩ : syracuseStep 804671 = 1207007) B1207007
theorem B804839 : Blo 535802 804839 := bstep (se 1 (by rfl) ⟨603629, by rfl⟩ : syracuseStep 804839 = 1207259) B1207259
theorem B1820663 : Blo 535802 1820663 := bstep (se 1 (by rfl) ⟨1365497, by rfl⟩ : syracuseStep 1820663 = 2730995) B2730995
theorem B804857 : Blo 535802 804857 := bstep (se 2 (by rfl) ⟨301821, by rfl⟩ : syracuseStep 804857 = 603643) B603643
theorem B804959 : Blo 535802 804959 := bstep (se 1 (by rfl) ⟨603719, by rfl⟩ : syracuseStep 804959 = 1207439) B1207439
theorem B805019 : Blo 535802 805019 := bstep (se 1 (by rfl) ⟨603764, by rfl⟩ : syracuseStep 805019 = 1207529) B1207529
theorem B805055 : Blo 535802 805055 := bstep (se 1 (by rfl) ⟨603791, by rfl⟩ : syracuseStep 805055 = 1207583) B1207583
theorem B1722559 : Blo 535802 1722559 := bstep (se 1 (by rfl) ⟨1291919, by rfl⟩ : syracuseStep 1722559 = 2583839) B2583839
theorem B805097 : Blo 535802 805097 := bstep (se 2 (by rfl) ⟨301911, by rfl⟩ : syracuseStep 805097 = 603823) B603823
theorem B19646711 : Blo 535802 19646711 := bstep (se 1 (by rfl) ⟨14735033, by rfl⟩ : syracuseStep 19646711 = 29470067) B29470067
theorem B4081913 : Blo 535802 4081913 := bstep (se 2 (by rfl) ⟨1530717, by rfl⟩ : syracuseStep 4081913 = 3061435) B3061435
theorem B805403 : Blo 535802 805403 := bstep (se 1 (by rfl) ⟨604052, by rfl⟩ : syracuseStep 805403 = 1208105) B1208105
theorem B805481 : Blo 535802 805481 := bstep (se 2 (by rfl) ⟨302055, by rfl⟩ : syracuseStep 805481 = 604111) B604111
theorem B1821527 : Blo 535802 1821527 := bstep (se 1 (by rfl) ⟨1366145, by rfl⟩ : syracuseStep 1821527 = 2732291) B2732291
theorem B1821743 : Blo 535802 1821743 := bstep (se 1 (by rfl) ⟨1366307, by rfl⟩ : syracuseStep 1821743 = 2732615) B2732615
theorem B806009 : Blo 535802 806009 := bstep (se 2 (by rfl) ⟨302253, by rfl⟩ : syracuseStep 806009 = 604507) B604507
theorem B806111 : Blo 535802 806111 := bstep (se 1 (by rfl) ⟨604583, by rfl⟩ : syracuseStep 806111 = 1209167) B1209167
theorem B806153 : Blo 535802 806153 := bstep (se 2 (by rfl) ⟨302307, by rfl⟩ : syracuseStep 806153 = 604615) B604615
theorem B1527119 : Blo 535802 1527119 := bstep (se 1 (by rfl) ⟨1145339, by rfl⟩ : syracuseStep 1527119 = 2290679) B2290679
theorem B806255 : Blo 535802 806255 := bstep (se 1 (by rfl) ⟨604691, by rfl⟩ : syracuseStep 806255 = 1209383) B1209383
theorem B2903465 : Blo 535802 2903465 := bstep (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) B2177599
theorem B806375 : Blo 535802 806375 := bstep (se 1 (by rfl) ⟨604781, by rfl⟩ : syracuseStep 806375 = 1209563) B1209563
theorem B806507 : Blo 535802 806507 := bstep (se 1 (by rfl) ⟨604880, by rfl⟩ : syracuseStep 806507 = 1209761) B1209761
theorem B806633 : Blo 535802 806633 := bstep (se 2 (by rfl) ⟨302487, by rfl⟩ : syracuseStep 806633 = 604975) B604975
theorem B904999 : Blo 535802 904999 := bstep (se 1 (by rfl) ⟨678749, by rfl⟩ : syracuseStep 904999 = 1357499) B1357499
theorem B806777 : Blo 535802 806777 := bstep (se 2 (by rfl) ⟨302541, by rfl⟩ : syracuseStep 806777 = 605083) B605083
theorem B806879 : Blo 535802 806879 := bstep (se 1 (by rfl) ⟨605159, by rfl⟩ : syracuseStep 806879 = 1210319) B1210319
theorem B3887291 : Blo 535802 3887291 := bstep (se 1 (by rfl) ⟨2915468, by rfl⟩ : syracuseStep 3887291 = 5830937) B5830937
theorem B807131 : Blo 535802 807131 := bstep (se 1 (by rfl) ⟨605348, by rfl⟩ : syracuseStep 807131 = 1210697) B1210697
theorem B807143 : Blo 535802 807143 := bstep (se 1 (by rfl) ⟨605357, by rfl⟩ : syracuseStep 807143 = 1210715) B1210715
theorem B807305 : Blo 535802 807305 := bstep (se 2 (by rfl) ⟨302739, by rfl⟩ : syracuseStep 807305 = 605479) B605479
theorem B807401 : Blo 535802 807401 := bstep (se 2 (by rfl) ⟨302775, by rfl⟩ : syracuseStep 807401 = 605551) B605551
theorem B807527 : Blo 535802 807527 := bstep (se 1 (by rfl) ⟨605645, by rfl⟩ : syracuseStep 807527 = 1211291) B1211291
theorem B807659 : Blo 535802 807659 := bstep (se 1 (by rfl) ⟨605744, by rfl⟩ : syracuseStep 807659 = 1211489) B1211489
theorem B807689 : Blo 535802 807689 := bstep (se 2 (by rfl) ⟨302883, by rfl⟩ : syracuseStep 807689 = 605767) B605767
theorem B906025 : Blo 535802 906025 := bstep (se 2 (by rfl) ⟨339759, by rfl⟩ : syracuseStep 906025 = 679519) B679519
theorem B807791 : Blo 535802 807791 := bstep (se 1 (by rfl) ⟨605843, by rfl⟩ : syracuseStep 807791 = 1211687) B1211687
theorem B3724283 : Blo 535802 3724283 := bstep (se 1 (by rfl) ⟨2793212, by rfl⟩ : syracuseStep 3724283 = 5586425) B5586425
theorem B906295 : Blo 535802 906295 := bstep (se 1 (by rfl) ⟨679721, by rfl⟩ : syracuseStep 906295 = 1359443) B1359443
theorem B1528895 : Blo 535802 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B808043 : Blo 535802 808043 := bstep (se 1 (by rfl) ⟨606032, by rfl⟩ : syracuseStep 808043 = 1212065) B1212065
theorem B808283 : Blo 535802 808283 := bstep (se 1 (by rfl) ⟨606212, by rfl⟩ : syracuseStep 808283 = 1212425) B1212425
theorem B1725953 : Blo 535802 1725953 := bstep (se 2 (by rfl) ⟨647232, by rfl⟩ : syracuseStep 1725953 = 1294465) B1294465
theorem B808559 : Blo 535802 808559 := bstep (se 1 (by rfl) ⟨606419, by rfl⟩ : syracuseStep 808559 = 1212839) B1212839
theorem B808631 : Blo 535802 808631 := bstep (se 1 (by rfl) ⟨606473, by rfl⟩ : syracuseStep 808631 = 1212947) B1212947
theorem B808667 : Blo 535802 808667 := bstep (se 1 (by rfl) ⟨606500, by rfl⟩ : syracuseStep 808667 = 1213001) B1213001
theorem B1529579 : Blo 535802 1529579 := bstep (se 1 (by rfl) ⟨1147184, by rfl⟩ : syracuseStep 1529579 = 2294369) B2294369
theorem B808841 : Blo 535802 808841 := bstep (se 2 (by rfl) ⟨303315, by rfl⟩ : syracuseStep 808841 = 606631) B606631
theorem B907247 : Blo 535802 907247 := bstep (se 1 (by rfl) ⟨680435, by rfl⟩ : syracuseStep 907247 = 1360871) B1360871
theorem B808943 : Blo 535802 808943 := bstep (se 1 (by rfl) ⟨606707, by rfl⟩ : syracuseStep 808943 = 1213415) B1213415
theorem B1726697 : Blo 535802 1726697 := bstep (se 2 (by rfl) ⟨647511, by rfl⟩ : syracuseStep 1726697 = 1295023) B1295023
theorem B809195 : Blo 535802 809195 := bstep (se 1 (by rfl) ⟨606896, by rfl⟩ : syracuseStep 809195 = 1213793) B1213793
theorem B809255 : Blo 535802 809255 := bstep (se 1 (by rfl) ⟨606941, by rfl⟩ : syracuseStep 809255 = 1213883) B1213883
theorem B809339 : Blo 535802 809339 := bstep (se 1 (by rfl) ⟨607004, by rfl⟩ : syracuseStep 809339 = 1214009) B1214009
theorem B907807 : Blo 535802 907807 := bstep (se 1 (by rfl) ⟨680855, by rfl⟩ : syracuseStep 907807 = 1361711) B1361711
theorem B809609 : Blo 535802 809609 := bstep (se 2 (by rfl) ⟨303603, by rfl⟩ : syracuseStep 809609 = 607207) B607207
theorem B908239 : Blo 535802 908239 := bstep (se 1 (by rfl) ⟨681179, by rfl⟩ : syracuseStep 908239 = 1362359) B1362359
theorem B1629551 : Blo 535802 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B6905249 : Blo 535802 6905249 := bstep (se 2 (by rfl) ⟨2589468, by rfl⟩ : syracuseStep 6905249 = 5178937) B5178937
theorem B1662439 : Blo 535802 1662439 := bstep (se 1 (by rfl) ⟨1246829, by rfl⟩ : syracuseStep 1662439 = 2493659) B2493659
theorem B3890663 : Blo 535802 3890663 := bstep (se 1 (by rfl) ⟨2917997, by rfl⟩ : syracuseStep 3890663 = 5835995) B5835995
theorem B908975 : Blo 535802 908975 := bstep (se 1 (by rfl) ⟨681731, by rfl⟩ : syracuseStep 908975 = 1363463) B1363463
theorem B909211 : Blo 535802 909211 := bstep (se 1 (by rfl) ⟨681908, by rfl⟩ : syracuseStep 909211 = 1363817) B1363817
theorem B6545447 : Blo 535802 6545447 := bstep (se 1 (by rfl) ⟨4909085, by rfl⟩ : syracuseStep 6545447 = 9818171) B9818171
theorem B680167 : Blo 535802 680167 := bstep (se 1 (by rfl) ⟨510125, by rfl⟩ : syracuseStep 680167 = 1020251) B1020251
theorem B909623 : Blo 535802 909623 := bstep (se 1 (by rfl) ⟨682217, by rfl⟩ : syracuseStep 909623 = 1364435) B1364435
theorem B680815 : Blo 535802 680815 := bstep (se 1 (by rfl) ⟨510611, by rfl⟩ : syracuseStep 680815 = 1021223) B1021223
theorem B910399 : Blo 535802 910399 := bstep (se 1 (by rfl) ⟨682799, by rfl⟩ : syracuseStep 910399 = 1365599) B1365599
theorem B1205675 : Blo 535802 1205675 := bstep (se 1 (by rfl) ⟨904256, by rfl⟩ : syracuseStep 1205675 = 1808513) B1808513
theorem B1631839 : Blo 535802 1631839 := bstep (se 1 (by rfl) ⟨1223879, by rfl⟩ : syracuseStep 1631839 = 2447759) B2447759
theorem B1205927 : Blo 535802 1205927 := bstep (se 1 (by rfl) ⟨904445, by rfl⟩ : syracuseStep 1205927 = 1808891) B1808891
theorem B681691 : Blo 535802 681691 := bstep (se 1 (by rfl) ⟨511268, by rfl⟩ : syracuseStep 681691 = 1022537) B1022537
theorem B1206215 : Blo 535802 1206215 := bstep (se 1 (by rfl) ⟨904661, by rfl⟩ : syracuseStep 1206215 = 1809323) B1809323
theorem B1206521 : Blo 535802 1206521 := bstep (se 2 (by rfl) ⟨452445, by rfl⟩ : syracuseStep 1206521 = 904891) B904891
theorem B1206575 : Blo 535802 1206575 := bstep (se 1 (by rfl) ⟨904931, by rfl⟩ : syracuseStep 1206575 = 1809863) B1809863
theorem B1206791 : Blo 535802 1206791 := bstep (se 1 (by rfl) ⟨905093, by rfl⟩ : syracuseStep 1206791 = 1810187) B1810187
theorem B1534535 : Blo 535802 1534535 := bstep (se 1 (by rfl) ⟨1150901, by rfl⟩ : syracuseStep 1534535 = 2301803) B2301803
theorem B1206971 : Blo 535802 1206971 := bstep (se 1 (by rfl) ⟨905228, by rfl⟩ : syracuseStep 1206971 = 1810457) B1810457
theorem B7105283 : Blo 535802 7105283 := bstep (se 1 (by rfl) ⟨5328962, by rfl⟩ : syracuseStep 7105283 = 10657925) B10657925
theorem B682987 : Blo 535802 682987 := bstep (se 1 (by rfl) ⟨512240, by rfl⟩ : syracuseStep 682987 = 1024481) B1024481
theorem B2583895 : Blo 535802 2583895 := bstep (se 1 (by rfl) ⟨1937921, by rfl⟩ : syracuseStep 2583895 = 3875843) B3875843
theorem B2289005 : Blo 535802 2289005 := bstep (se 3 (by rfl) ⟨429188, by rfl⟩ : syracuseStep 2289005 = 858377) B858377
theorem B1207799 : Blo 535802 1207799 := bstep (se 1 (by rfl) ⟨905849, by rfl⟩ : syracuseStep 1207799 = 1811699) B1811699
theorem B1207871 : Blo 535802 1207871 := bstep (se 1 (by rfl) ⟨905903, by rfl⟩ : syracuseStep 1207871 = 1811807) B1811807
theorem B16805501 : Blo 535802 16805501 := bstep (se 3 (by rfl) ⟨3151031, by rfl⟩ : syracuseStep 16805501 = 6302063) B6302063
theorem B3862379 : Blo 535802 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B1208825 : Blo 535802 1208825 := bstep (se 2 (by rfl) ⟨453309, by rfl⟩ : syracuseStep 1208825 = 906619) B906619
theorem B1208915 : Blo 535802 1208915 := bstep (se 1 (by rfl) ⟨906686, by rfl⟩ : syracuseStep 1208915 = 1813373) B1813373
theorem B1209095 : Blo 535802 1209095 := bstep (se 1 (by rfl) ⟨906821, by rfl⟩ : syracuseStep 1209095 = 1813643) B1813643
theorem B2717387 : Blo 535802 2717387 := bstep (se 1 (by rfl) ⟨2038040, by rfl⟩ : syracuseStep 2717387 = 4076081) B4076081
theorem B1210175 : Blo 535802 1210175 := bstep (se 1 (by rfl) ⟨907631, by rfl⟩ : syracuseStep 1210175 = 1815263) B1815263
theorem B3438557 : Blo 535802 3438557 := bstep (se 3 (by rfl) ⟨644729, by rfl⟩ : syracuseStep 3438557 = 1289459) B1289459
theorem B1210463 : Blo 535802 1210463 := bstep (se 1 (by rfl) ⟨907847, by rfl⟩ : syracuseStep 1210463 = 1815695) B1815695
theorem B1243279 : Blo 535802 1243279 := bstep (se 1 (by rfl) ⟨932459, by rfl⟩ : syracuseStep 1243279 = 1864919) B1864919
theorem B2914537 : Blo 535802 2914537 := bstep (se 2 (by rfl) ⟨1092951, by rfl⟩ : syracuseStep 2914537 = 2185903) B2185903
theorem B4356595 : Blo 535802 4356595 := bstep (se 1 (by rfl) ⟨3267446, by rfl⟩ : syracuseStep 4356595 = 6534893) B6534893
theorem B4586003 : Blo 535802 4586003 := bstep (se 1 (by rfl) ⟨3439502, by rfl⟩ : syracuseStep 4586003 = 6879005) B6879005
theorem B1932113 : Blo 535802 1932113 := bstep (se 2 (by rfl) ⟨724542, by rfl⟩ : syracuseStep 1932113 = 1449085) B1449085
theorem B1211219 : Blo 535802 1211219 := bstep (se 1 (by rfl) ⟨908414, by rfl⟩ : syracuseStep 1211219 = 1816829) B1816829
theorem B4914053 : Blo 535802 4914053 := bstep (se 4 (by rfl) ⟨460692, by rfl⟩ : syracuseStep 4914053 = 921385) B921385
theorem B1211759 : Blo 535802 1211759 := bstep (se 1 (by rfl) ⟨908819, by rfl⟩ : syracuseStep 1211759 = 1817639) B1817639
theorem B4914599 : Blo 535802 4914599 := bstep (se 1 (by rfl) ⟨3685949, by rfl⟩ : syracuseStep 4914599 = 7371899) B7371899
theorem B2719169 : Blo 535802 2719169 := bstep (se 2 (by rfl) ⟨1019688, by rfl⟩ : syracuseStep 2719169 = 2039377) B2039377
theorem B1212047 : Blo 535802 1212047 := bstep (se 1 (by rfl) ⟨909035, by rfl⟩ : syracuseStep 1212047 = 1818071) B1818071
theorem B917225 : Blo 535802 917225 := bstep (se 2 (by rfl) ⟨343959, by rfl⟩ : syracuseStep 917225 = 687919) B687919
theorem B1212137 : Blo 535802 1212137 := bstep (se 2 (by rfl) ⟨454551, by rfl⟩ : syracuseStep 1212137 = 909103) B909103
theorem B3276521 : Blo 535802 3276521 := bstep (se 2 (by rfl) ⟨1228695, by rfl⟩ : syracuseStep 3276521 = 2457391) B2457391
theorem B1048391 : Blo 535802 1048391 := bstep (se 1 (by rfl) ⟨786293, by rfl⟩ : syracuseStep 1048391 = 1572587) B1572587
theorem B1835435 : Blo 535802 1835435 := bstep (se 1 (by rfl) ⟨1376576, by rfl⟩ : syracuseStep 1835435 = 2753153) B2753153
theorem B4096979 : Blo 535802 4096979 := bstep (se 1 (by rfl) ⟨3072734, by rfl⟩ : syracuseStep 4096979 = 6145469) B6145469
theorem B1213631 : Blo 535802 1213631 := bstep (se 1 (by rfl) ⟨910223, by rfl⟩ : syracuseStep 1213631 = 1820447) B1820447
theorem B1213775 : Blo 535802 1213775 := bstep (se 1 (by rfl) ⟨910331, by rfl⟩ : syracuseStep 1213775 = 1820663) B1820663
theorem B1213865 : Blo 535802 1213865 := bstep (se 2 (by rfl) ⟨455199, by rfl⟩ : syracuseStep 1213865 = 910399) B910399
theorem B2721275 : Blo 535802 2721275 := bstep (se 1 (by rfl) ⟨2040956, by rfl⟩ : syracuseStep 2721275 = 4081913) B4081913
theorem B2328169 : Blo 535802 2328169 := bstep (se 2 (by rfl) ⟨873063, by rfl⟩ : syracuseStep 2328169 = 1746127) B1746127
theorem B1214351 : Blo 535802 1214351 := bstep (se 1 (by rfl) ⟨910763, by rfl⟩ : syracuseStep 1214351 = 1821527) B1821527
theorem B1214495 : Blo 535802 1214495 := bstep (se 1 (by rfl) ⟨910871, by rfl⟩ : syracuseStep 1214495 = 1821743) B1821743
theorem B4589693 : Blo 535802 4589693 := bstep (se 3 (by rfl) ⟨860567, by rfl⟩ : syracuseStep 4589693 = 1721135) B1721135
theorem B1018079 : Blo 535802 1018079 := bstep (se 1 (by rfl) ⟨763559, by rfl⟩ : syracuseStep 1018079 = 1527119) B1527119
theorem B5179787 : Blo 535802 5179787 := bstep (se 1 (by rfl) ⟨3884840, by rfl⟩ : syracuseStep 5179787 = 7769681) B7769681
theorem B2591527 : Blo 535802 2591527 := bstep (se 1 (by rfl) ⟨1943645, by rfl⟩ : syracuseStep 2591527 = 3887291) B3887291
theorem B1018793 : Blo 535802 1018793 := bstep (se 2 (by rfl) ⟨382047, by rfl⟩ : syracuseStep 1018793 = 764095) B764095
theorem B2296745 : Blo 535802 2296745 := bstep (se 2 (by rfl) ⟨861279, by rfl⟩ : syracuseStep 2296745 = 1722559) B1722559
theorem B4590755 : Blo 535802 4590755 := bstep (se 1 (by rfl) ⟨3443066, by rfl⟩ : syracuseStep 4590755 = 6886133) B6886133
theorem B2591929 : Blo 535802 2591929 := bstep (se 2 (by rfl) ⟨971973, by rfl⟩ : syracuseStep 2591929 = 1943947) B1943947
theorem B2624879 : Blo 535802 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B1019719 : Blo 535802 1019719 := bstep (se 1 (by rfl) ⟨764789, by rfl⟩ : syracuseStep 1019719 = 1529579) B1529579
theorem B2724029 : Blo 535802 2724029 := bstep (se 3 (by rfl) ⟨510755, by rfl⟩ : syracuseStep 2724029 = 1021511) B1021511
theorem B5509549 : Blo 535802 5509549 := bstep (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) B2066081
theorem B3445193 : Blo 535802 3445193 := bstep (se 2 (by rfl) ⟨1291947, by rfl⟩ : syracuseStep 3445193 = 2583895) B2583895
theorem B2036279 : Blo 535802 2036279 := bstep (se 1 (by rfl) ⟨1527209, by rfl⟩ : syracuseStep 2036279 = 3054419) B3054419
theorem B1086367 : Blo 535802 1086367 := bstep (se 1 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 1086367 = 1629551) B1629551
theorem B2593775 : Blo 535802 2593775 := bstep (se 1 (by rfl) ⟨1945331, by rfl⟩ : syracuseStep 2593775 = 3890663) B3890663
theorem B4363631 : Blo 535802 4363631 := bstep (se 1 (by rfl) ⟨3272723, by rfl⟩ : syracuseStep 4363631 = 6545447) B6545447
theorem B1939565 : Blo 535802 1939565 := bstep (se 3 (by rfl) ⟨363668, by rfl⟩ : syracuseStep 1939565 = 727337) B727337
theorem B5315371 : Blo 535802 5315371 := bstep (se 1 (by rfl) ⟨3986528, by rfl⟩ : syracuseStep 5315371 = 7973057) B7973057
theorem B4070249 : Blo 535802 4070249 := bstep (se 2 (by rfl) ⟨1526343, by rfl⟩ : syracuseStep 4070249 = 3052687) B3052687
theorem B1023023 : Blo 535802 1023023 := bstep (se 1 (by rfl) ⟨767267, by rfl⟩ : syracuseStep 1023023 = 1534535) B1534535
theorem B2302091 : Blo 535802 2302091 := bstep (se 1 (by rfl) ⟨1726568, by rfl⟩ : syracuseStep 2302091 = 3453137) B3453137
theorem B5808793 : Blo 535802 5808793 := bstep (se 2 (by rfl) ⟨2178297, by rfl⟩ : syracuseStep 5808793 = 4356595) B4356595
theorem B1843975 : Blo 535802 1843975 := bstep (se 1 (by rfl) ⟨1382981, by rfl⟩ : syracuseStep 1843975 = 2765963) B2765963
theorem B2040623 : Blo 535802 2040623 := bstep (se 1 (by rfl) ⟨1530467, by rfl⟩ : syracuseStep 2040623 = 3060935) B3060935
theorem B4596527 : Blo 535802 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B7742573 : Blo 535802 7742573 := bstep (se 3 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 7742573 = 2903465) B2903465
theorem B1811591 : Blo 535802 1811591 := bstep (se 1 (by rfl) ⟨1358693, by rfl⟩ : syracuseStep 1811591 = 2717387) B2717387
theorem B1811969 : Blo 535802 1811969 := bstep (se 2 (by rfl) ⟨679488, by rfl⟩ : syracuseStep 1811969 = 1358977) B1358977
theorem B3057335 : Blo 535802 3057335 := bstep (se 1 (by rfl) ⟨2293001, by rfl⟩ : syracuseStep 3057335 = 4586003) B4586003
theorem B1288075 : Blo 535802 1288075 := bstep (se 1 (by rfl) ⟨966056, by rfl⟩ : syracuseStep 1288075 = 1932113) B1932113
theorem B20949137 : Blo 535802 20949137 := bstep (se 2 (by rfl) ⟨7855926, by rfl⟩ : syracuseStep 20949137 = 15711853) B15711853
theorem B1812779 : Blo 535802 1812779 := bstep (se 1 (by rfl) ⟨1359584, by rfl⟩ : syracuseStep 1812779 = 2719169) B2719169
theorem B698927 : Blo 535802 698927 := bstep (se 1 (by rfl) ⟨524195, by rfl⟩ : syracuseStep 698927 = 1048391) B1048391
theorem B1813049 : Blo 535802 1813049 := bstep (se 2 (by rfl) ⟨679893, by rfl⟩ : syracuseStep 1813049 = 1359787) B1359787
theorem B1944121 : Blo 535802 1944121 := bstep (se 2 (by rfl) ⟨729045, by rfl⟩ : syracuseStep 1944121 = 1458091) B1458091
theorem B535935 : Blo 535802 535935 := bstep (se 1 (by rfl) ⟨401951, by rfl⟩ : syracuseStep 535935 = 803903) B803903
theorem B535963 : Blo 535802 535963 := bstep (se 1 (by rfl) ⟨401972, by rfl⟩ : syracuseStep 535963 = 803945) B803945
theorem B536031 : Blo 535802 536031 := bstep (se 1 (by rfl) ⟨402023, by rfl⟩ : syracuseStep 536031 = 804047) B804047
theorem B2305543 : Blo 535802 2305543 := bstep (se 1 (by rfl) ⟨1729157, by rfl⟩ : syracuseStep 2305543 = 3458315) B3458315
theorem B536167 : Blo 535802 536167 := bstep (se 1 (by rfl) ⟨402125, by rfl⟩ : syracuseStep 536167 = 804251) B804251
theorem B536315 : Blo 535802 536315 := bstep (se 1 (by rfl) ⟨402236, by rfl⟩ : syracuseStep 536315 = 804473) B804473
theorem B536383 : Blo 535802 536383 := bstep (se 1 (by rfl) ⟨402287, by rfl⟩ : syracuseStep 536383 = 804575) B804575
theorem B536447 : Blo 535802 536447 := bstep (se 1 (by rfl) ⟨402335, by rfl⟩ : syracuseStep 536447 = 804671) B804671
theorem B536559 : Blo 535802 536559 := bstep (se 1 (by rfl) ⟨402419, by rfl⟩ : syracuseStep 536559 = 804839) B804839
theorem B536571 : Blo 535802 536571 := bstep (se 1 (by rfl) ⟨402428, by rfl⟩ : syracuseStep 536571 = 804857) B804857
theorem B1814561 : Blo 535802 1814561 := bstep (se 2 (by rfl) ⟨680460, by rfl⟩ : syracuseStep 1814561 = 1360921) B1360921
theorem B536639 : Blo 535802 536639 := bstep (se 1 (by rfl) ⟨402479, by rfl⟩ : syracuseStep 536639 = 804959) B804959
theorem B1290313 : Blo 535802 1290313 := bstep (se 2 (by rfl) ⟨483867, by rfl⟩ : syracuseStep 1290313 = 967735) B967735
theorem B536679 : Blo 535802 536679 := bstep (se 1 (by rfl) ⟨402509, by rfl⟩ : syracuseStep 536679 = 805019) B805019
theorem B536703 : Blo 535802 536703 := bstep (se 1 (by rfl) ⟨402527, by rfl⟩ : syracuseStep 536703 = 805055) B805055
theorem B536731 : Blo 535802 536731 := bstep (se 1 (by rfl) ⟨402548, by rfl⟩ : syracuseStep 536731 = 805097) B805097
theorem B536935 : Blo 535802 536935 := bstep (se 1 (by rfl) ⟨402701, by rfl⟩ : syracuseStep 536935 = 805403) B805403
theorem B8532361 : Blo 535802 8532361 := bstep (se 2 (by rfl) ⟨3199635, by rfl⟩ : syracuseStep 8532361 = 6399271) B6399271
theorem B536987 : Blo 535802 536987 := bstep (se 1 (by rfl) ⟨402740, by rfl⟩ : syracuseStep 536987 = 805481) B805481
theorem B1814939 : Blo 535802 1814939 := bstep (se 1 (by rfl) ⟨1361204, by rfl⟩ : syracuseStep 1814939 = 2722409) B2722409
theorem B1094087 : Blo 535802 1094087 := bstep (se 1 (by rfl) ⟨820565, by rfl⟩ : syracuseStep 1094087 = 1641131) B1641131
theorem B537339 : Blo 535802 537339 := bstep (se 1 (by rfl) ⟨403004, by rfl⟩ : syracuseStep 537339 = 806009) B806009
theorem B2175785 : Blo 535802 2175785 := bstep (se 2 (by rfl) ⟨815919, by rfl⟩ : syracuseStep 2175785 = 1631839) B1631839
theorem B537407 : Blo 535802 537407 := bstep (se 1 (by rfl) ⟨403055, by rfl⟩ : syracuseStep 537407 = 806111) B806111
theorem B766783 : Blo 535802 766783 := bstep (se 1 (by rfl) ⟨575087, by rfl⟩ : syracuseStep 766783 = 1150175) B1150175
theorem B537435 : Blo 535802 537435 := bstep (se 1 (by rfl) ⟨403076, by rfl⟩ : syracuseStep 537435 = 806153) B806153
theorem B537503 : Blo 535802 537503 := bstep (se 1 (by rfl) ⟨403127, by rfl⟩ : syracuseStep 537503 = 806255) B806255
theorem B537583 : Blo 535802 537583 := bstep (se 1 (by rfl) ⟨403187, by rfl⟩ : syracuseStep 537583 = 806375) B806375
theorem B1356871 : Blo 535802 1356871 := bstep (se 1 (by rfl) ⟨1017653, by rfl⟩ : syracuseStep 1356871 = 2035307) B2035307
theorem B537671 : Blo 535802 537671 := bstep (se 1 (by rfl) ⟨403253, by rfl⟩ : syracuseStep 537671 = 806507) B806507
theorem B537755 : Blo 535802 537755 := bstep (se 1 (by rfl) ⟨403316, by rfl⟩ : syracuseStep 537755 = 806633) B806633
theorem B4371677 : Blo 535802 4371677 := bstep (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) B1639379
theorem B537851 : Blo 535802 537851 := bstep (se 1 (by rfl) ⟨403388, by rfl⟩ : syracuseStep 537851 = 806777) B806777
theorem B1815803 : Blo 535802 1815803 := bstep (se 1 (by rfl) ⟨1361852, by rfl⟩ : syracuseStep 1815803 = 2723705) B2723705
theorem B767227 : Blo 535802 767227 := bstep (se 1 (by rfl) ⟨575420, by rfl⟩ : syracuseStep 767227 = 1150841) B1150841
theorem B537919 : Blo 535802 537919 := bstep (se 1 (by rfl) ⟨403439, by rfl⟩ : syracuseStep 537919 = 806879) B806879
theorem B538087 : Blo 535802 538087 := bstep (se 1 (by rfl) ⟨403565, by rfl⟩ : syracuseStep 538087 = 807131) B807131
theorem B538095 : Blo 535802 538095 := bstep (se 1 (by rfl) ⟨403571, by rfl⟩ : syracuseStep 538095 = 807143) B807143
theorem B4077053 : Blo 535802 4077053 := bstep (se 3 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 4077053 = 1528895) B1528895
theorem B538203 : Blo 535802 538203 := bstep (se 1 (by rfl) ⟨403652, by rfl⟩ : syracuseStep 538203 = 807305) B807305
theorem B538267 : Blo 535802 538267 := bstep (se 1 (by rfl) ⟨403700, by rfl⟩ : syracuseStep 538267 = 807401) B807401
theorem B538351 : Blo 535802 538351 := bstep (se 1 (by rfl) ⟨403763, by rfl⟩ : syracuseStep 538351 = 807527) B807527
theorem B538439 : Blo 535802 538439 := bstep (se 1 (by rfl) ⟨403829, by rfl⟩ : syracuseStep 538439 = 807659) B807659
theorem B538459 : Blo 535802 538459 := bstep (se 1 (by rfl) ⟨403844, by rfl⟩ : syracuseStep 538459 = 807689) B807689
theorem B538527 : Blo 535802 538527 := bstep (se 1 (by rfl) ⟨403895, by rfl⟩ : syracuseStep 538527 = 807791) B807791
theorem B538695 : Blo 535802 538695 := bstep (se 1 (by rfl) ⟨404021, by rfl⟩ : syracuseStep 538695 = 808043) B808043
theorem B538855 : Blo 535802 538855 := bstep (se 1 (by rfl) ⟨404141, by rfl⟩ : syracuseStep 538855 = 808283) B808283
theorem B539039 : Blo 535802 539039 := bstep (se 1 (by rfl) ⟨404279, by rfl⟩ : syracuseStep 539039 = 808559) B808559
theorem B1358279 : Blo 535802 1358279 := bstep (se 1 (by rfl) ⟨1018709, by rfl⟩ : syracuseStep 1358279 = 2037419) B2037419
theorem B539087 : Blo 535802 539087 := bstep (se 1 (by rfl) ⟨404315, by rfl⟩ : syracuseStep 539087 = 808631) B808631
theorem B539111 : Blo 535802 539111 := bstep (se 1 (by rfl) ⟨404333, by rfl⟩ : syracuseStep 539111 = 808667) B808667
theorem B539227 : Blo 535802 539227 := bstep (se 1 (by rfl) ⟨404420, by rfl⟩ : syracuseStep 539227 = 808841) B808841
theorem B604831 : Blo 535802 604831 := bstep (se 1 (by rfl) ⟨453623, by rfl⟩ : syracuseStep 604831 = 907247) B907247
theorem B539295 : Blo 535802 539295 := bstep (se 1 (by rfl) ⟨404471, by rfl⟩ : syracuseStep 539295 = 808943) B808943
theorem B4602541 : Blo 535802 4602541 := bstep (se 3 (by rfl) ⟨862976, by rfl⟩ : syracuseStep 4602541 = 1725953) B1725953
theorem B539463 : Blo 535802 539463 := bstep (se 1 (by rfl) ⟨404597, by rfl⟩ : syracuseStep 539463 = 809195) B809195
theorem B539503 : Blo 535802 539503 := bstep (se 1 (by rfl) ⟨404627, by rfl⟩ : syracuseStep 539503 = 809255) B809255
theorem B539559 : Blo 535802 539559 := bstep (se 1 (by rfl) ⟨404669, by rfl⟩ : syracuseStep 539559 = 809339) B809339
theorem B59554739 : Blo 535802 59554739 := bstep (se 1 (by rfl) ⟨44666054, by rfl⟩ : syracuseStep 59554739 = 89332109) B89332109
theorem B539739 : Blo 535802 539739 := bstep (se 1 (by rfl) ⟨404804, by rfl⟩ : syracuseStep 539739 = 809609) B809609
theorem B4603499 : Blo 535802 4603499 := bstep (se 1 (by rfl) ⟨3452624, by rfl⟩ : syracuseStep 4603499 = 6905249) B6905249
theorem B605983 : Blo 535802 605983 := bstep (se 1 (by rfl) ⟨454487, by rfl⟩ : syracuseStep 605983 = 908975) B908975
theorem B1359737 : Blo 535802 1359737 := bstep (se 2 (by rfl) ⟨509901, by rfl⟩ : syracuseStep 1359737 = 1019803) B1019803
theorem B2899901 : Blo 535802 2899901 := bstep (se 3 (by rfl) ⟨543731, by rfl⟩ : syracuseStep 2899901 = 1087463) B1087463
theorem B5292071 : Blo 535802 5292071 := bstep (se 1 (by rfl) ⟨3969053, by rfl⟩ : syracuseStep 5292071 = 7938107) B7938107
theorem B606415 : Blo 535802 606415 := bstep (se 1 (by rfl) ⟨454811, by rfl⟩ : syracuseStep 606415 = 909623) B909623
theorem B4079969 : Blo 535802 4079969 := bstep (se 2 (by rfl) ⟨1529988, by rfl⟩ : syracuseStep 4079969 = 3059977) B3059977
theorem B4604525 : Blo 535802 4604525 := bstep (se 3 (by rfl) ⟨863348, by rfl⟩ : syracuseStep 4604525 = 1726697) B1726697
theorem B7357061 : Blo 535802 7357061 := bstep (se 4 (by rfl) ⟨689724, by rfl⟩ : syracuseStep 7357061 = 1379449) B1379449
theorem B803783 : Blo 535802 803783 := bstep (se 1 (by rfl) ⟨602837, by rfl⟩ : syracuseStep 803783 = 1205675) B1205675
theorem B803951 : Blo 535802 803951 := bstep (se 1 (by rfl) ⟨602963, by rfl⟩ : syracuseStep 803951 = 1205927) B1205927
theorem B2213099 : Blo 535802 2213099 := bstep (se 1 (by rfl) ⟨1659824, by rfl⟩ : syracuseStep 2213099 = 3319649) B3319649
theorem B804143 : Blo 535802 804143 := bstep (se 1 (by rfl) ⟨603107, by rfl⟩ : syracuseStep 804143 = 1206215) B1206215
theorem B1295695 : Blo 535802 1295695 := bstep (se 1 (by rfl) ⟨971771, by rfl⟩ : syracuseStep 1295695 = 1943543) B1943543
theorem B804347 : Blo 535802 804347 := bstep (se 1 (by rfl) ⟨603260, by rfl⟩ : syracuseStep 804347 = 1206521) B1206521
theorem B804383 : Blo 535802 804383 := bstep (se 1 (by rfl) ⟨603287, by rfl⟩ : syracuseStep 804383 = 1206575) B1206575
theorem B804527 : Blo 535802 804527 := bstep (se 1 (by rfl) ⟨603395, by rfl⟩ : syracuseStep 804527 = 1206791) B1206791
theorem B804647 : Blo 535802 804647 := bstep (se 1 (by rfl) ⟨603485, by rfl⟩ : syracuseStep 804647 = 1206971) B1206971
theorem B4736855 : Blo 535802 4736855 := bstep (se 1 (by rfl) ⟨3552641, by rfl⟩ : syracuseStep 4736855 = 7105283) B7105283
theorem B1526003 : Blo 535802 1526003 := bstep (se 1 (by rfl) ⟨1144502, by rfl⟩ : syracuseStep 1526003 = 2289005) B2289005
theorem B805199 : Blo 535802 805199 := bstep (se 1 (by rfl) ⟨603899, by rfl⟩ : syracuseStep 805199 = 1207799) B1207799
theorem B805247 : Blo 535802 805247 := bstep (se 1 (by rfl) ⟨603935, by rfl⟩ : syracuseStep 805247 = 1207871) B1207871
theorem B805289 : Blo 535802 805289 := bstep (se 2 (by rfl) ⟨301983, by rfl⟩ : syracuseStep 805289 = 603967) B603967
theorem B2574919 : Blo 535802 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B805673 : Blo 535802 805673 := bstep (se 2 (by rfl) ⟨302127, by rfl⟩ : syracuseStep 805673 = 604255) B604255
theorem B1657705 : Blo 535802 1657705 := bstep (se 2 (by rfl) ⟨621639, by rfl⟩ : syracuseStep 1657705 = 1243279) B1243279
theorem B3886049 : Blo 535802 3886049 := bstep (se 2 (by rfl) ⟨1457268, by rfl⟩ : syracuseStep 3886049 = 2914537) B2914537
theorem B805883 : Blo 535802 805883 := bstep (se 1 (by rfl) ⟨604412, by rfl⟩ : syracuseStep 805883 = 1208825) B1208825
theorem B805943 : Blo 535802 805943 := bstep (se 1 (by rfl) ⟨604457, by rfl⟩ : syracuseStep 805943 = 1208915) B1208915
theorem B5164175 : Blo 535802 5164175 := bstep (se 1 (by rfl) ⟨3873131, by rfl⟩ : syracuseStep 5164175 = 7746263) B7746263
theorem B806063 : Blo 535802 806063 := bstep (se 1 (by rfl) ⟨604547, by rfl⟩ : syracuseStep 806063 = 1209095) B1209095
theorem B4902077 : Blo 535802 4902077 := bstep (se 3 (by rfl) ⟨919139, by rfl⟩ : syracuseStep 4902077 = 1838279) B1838279
theorem B9817307 : Blo 535802 9817307 := bstep (se 1 (by rfl) ⟨7362980, by rfl⟩ : syracuseStep 9817307 = 14725961) B14725961
theorem B7359905 : Blo 535802 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B905087 : Blo 535802 905087 := bstep (se 1 (by rfl) ⟨678815, by rfl⟩ : syracuseStep 905087 = 1357631) B1357631
theorem B806783 : Blo 535802 806783 := bstep (se 1 (by rfl) ⟨605087, by rfl⟩ : syracuseStep 806783 = 1210175) B1210175
theorem B806975 : Blo 535802 806975 := bstep (se 1 (by rfl) ⟨605231, by rfl⟩ : syracuseStep 806975 = 1210463) B1210463
theorem B905323 : Blo 535802 905323 := bstep (se 1 (by rfl) ⟨678992, by rfl⟩ : syracuseStep 905323 = 1357985) B1357985
theorem B807209 : Blo 535802 807209 := bstep (se 2 (by rfl) ⟨302703, by rfl⟩ : syracuseStep 807209 = 605407) B605407
theorem B971131 : Blo 535802 971131 := bstep (se 1 (by rfl) ⟨728348, by rfl⟩ : syracuseStep 971131 = 1456697) B1456697
theorem B2576765 : Blo 535802 2576765 := bstep (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) B966287
theorem B807479 : Blo 535802 807479 := bstep (se 1 (by rfl) ⟨605609, by rfl⟩ : syracuseStep 807479 = 1211219) B1211219
theorem B2216585 : Blo 535802 2216585 := bstep (se 2 (by rfl) ⟨831219, by rfl⟩ : syracuseStep 2216585 = 1662439) B1662439
theorem B807839 : Blo 535802 807839 := bstep (se 1 (by rfl) ⟨605879, by rfl⟩ : syracuseStep 807839 = 1211759) B1211759
theorem B1364951 : Blo 535802 1364951 := bstep (se 1 (by rfl) ⟨1023713, by rfl⟩ : syracuseStep 1364951 = 2047427) B2047427
theorem B808031 : Blo 535802 808031 := bstep (se 1 (by rfl) ⟨606023, by rfl⟩ : syracuseStep 808031 = 1212047) B1212047
theorem B611483 : Blo 535802 611483 := bstep (se 1 (by rfl) ⟨458612, by rfl⟩ : syracuseStep 611483 = 917225) B917225
theorem B808091 : Blo 535802 808091 := bstep (se 1 (by rfl) ⟨606068, by rfl⟩ : syracuseStep 808091 = 1212137) B1212137
theorem B2184347 : Blo 535802 2184347 := bstep (se 1 (by rfl) ⟨1638260, by rfl⟩ : syracuseStep 2184347 = 3276521) B3276521
theorem B1660267 : Blo 535802 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B906727 : Blo 535802 906727 := bstep (se 1 (by rfl) ⟨680045, by rfl⟩ : syracuseStep 906727 = 1360091) B1360091
theorem B13293179 : Blo 535802 13293179 := bstep (se 1 (by rfl) ⟨9969884, by rfl⟩ : syracuseStep 13293179 = 19939769) B19939769
theorem B906889 : Blo 535802 906889 := bstep (se 2 (by rfl) ⟨340083, by rfl⟩ : syracuseStep 906889 = 680167) B680167
theorem B808775 : Blo 535802 808775 := bstep (se 1 (by rfl) ⟨606581, by rfl⟩ : syracuseStep 808775 = 1213163) B1213163
theorem B1366055 : Blo 535802 1366055 := bstep (se 1 (by rfl) ⟨1024541, by rfl⟩ : syracuseStep 1366055 = 2049083) B2049083
theorem B23189651 : Blo 535802 23189651 := bstep (se 1 (by rfl) ⟨17392238, by rfl⟩ : syracuseStep 23189651 = 34784477) B34784477
theorem B907483 : Blo 535802 907483 := bstep (se 1 (by rfl) ⟨680612, by rfl⟩ : syracuseStep 907483 = 1361225) B1361225
theorem B15718643 : Blo 535802 15718643 := bstep (se 1 (by rfl) ⟨11788982, by rfl⟩ : syracuseStep 15718643 = 23577965) B23577965
theorem B907679 : Blo 535802 907679 := bstep (se 1 (by rfl) ⟨680759, by rfl⟩ : syracuseStep 907679 = 1361519) B1361519
theorem B6904223 : Blo 535802 6904223 := bstep (se 1 (by rfl) ⟨5178167, by rfl⟩ : syracuseStep 6904223 = 10356335) B10356335
theorem B4151711 : Blo 535802 4151711 := bstep (se 1 (by rfl) ⟨3113783, by rfl⟩ : syracuseStep 4151711 = 6227567) B6227567
theorem B809375 : Blo 535802 809375 := bstep (se 1 (by rfl) ⟨607031, by rfl⟩ : syracuseStep 809375 = 1214063) B1214063
theorem B809447 : Blo 535802 809447 := bstep (se 1 (by rfl) ⟨607085, by rfl⟩ : syracuseStep 809447 = 1214171) B1214171
theorem B907753 : Blo 535802 907753 := bstep (se 2 (by rfl) ⟨340407, by rfl⟩ : syracuseStep 907753 = 680815) B680815
theorem B13097807 : Blo 535802 13097807 := bstep (se 1 (by rfl) ⟨9823355, by rfl⟩ : syracuseStep 13097807 = 19646711) B19646711
theorem B875375 : Blo 535802 875375 := bstep (se 1 (by rfl) ⟨656531, by rfl⟩ : syracuseStep 875375 = 1313063) B1313063
theorem B2186423 : Blo 535802 2186423 := bstep (se 1 (by rfl) ⟨1639817, by rfl⟩ : syracuseStep 2186423 = 3279635) B3279635
theorem B1727851 : Blo 535802 1727851 := bstep (se 1 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 1727851 = 2591777) B2591777
theorem B908921 : Blo 535802 908921 := bstep (se 2 (by rfl) ⟨340845, by rfl⟩ : syracuseStep 908921 = 681691) B681691
theorem B8937175 : Blo 535802 8937175 := bstep (se 1 (by rfl) ⟨6702881, by rfl⟩ : syracuseStep 8937175 = 13405763) B13405763
theorem B6119225 : Blo 535802 6119225 := bstep (se 2 (by rfl) ⟨2294709, by rfl⟩ : syracuseStep 6119225 = 4589419) B4589419
theorem B15294521 : Blo 535802 15294521 := bstep (se 2 (by rfl) ⟨5735445, by rfl⟩ : syracuseStep 15294521 = 11470891) B11470891
theorem B4088231 : Blo 535802 4088231 := bstep (se 1 (by rfl) ⟨3066173, by rfl⟩ : syracuseStep 4088231 = 6132347) B6132347
theorem B2482855 : Blo 535802 2482855 := bstep (se 1 (by rfl) ⟨1862141, by rfl⟩ : syracuseStep 2482855 = 3724283) B3724283
theorem B18834221 : Blo 535802 18834221 := bstep (se 3 (by rfl) ⟨3531416, by rfl⟩ : syracuseStep 18834221 = 7062833) B7062833
theorem B910649 : Blo 535802 910649 := bstep (se 2 (by rfl) ⟨341493, by rfl⟩ : syracuseStep 910649 = 682987) B682987
theorem B1206035 : Blo 535802 1206035 := bstep (se 1 (by rfl) ⟨904526, by rfl⟩ : syracuseStep 1206035 = 1809053) B1809053
theorem B1206251 : Blo 535802 1206251 := bstep (se 1 (by rfl) ⟨904688, by rfl⟩ : syracuseStep 1206251 = 1809377) B1809377
theorem B1206395 : Blo 535802 1206395 := bstep (se 1 (by rfl) ⟨904796, by rfl⟩ : syracuseStep 1206395 = 1809593) B1809593
theorem B1206665 : Blo 535802 1206665 := bstep (se 2 (by rfl) ⟨452499, by rfl⟩ : syracuseStep 1206665 = 904999) B904999
theorem B1207367 : Blo 535802 1207367 := bstep (se 1 (by rfl) ⟨905525, by rfl⟩ : syracuseStep 1207367 = 1811051) B1811051
theorem B10316969 : Blo 535802 10316969 := bstep (se 2 (by rfl) ⟨3868863, by rfl⟩ : syracuseStep 10316969 = 7737727) B7737727
theorem B1207763 : Blo 535802 1207763 := bstep (se 1 (by rfl) ⟨905822, by rfl⟩ : syracuseStep 1207763 = 1811645) B1811645
theorem B1208033 : Blo 535802 1208033 := bstep (se 2 (by rfl) ⟨453012, by rfl⟩ : syracuseStep 1208033 = 906025) B906025
theorem B1535993 : Blo 535802 1535993 := bstep (se 2 (by rfl) ⟨575997, by rfl⟩ : syracuseStep 1535993 = 1151995) B1151995
theorem B1208393 : Blo 535802 1208393 := bstep (se 2 (by rfl) ⟨453147, by rfl⟩ : syracuseStep 1208393 = 906295) B906295
theorem B1208447 : Blo 535802 1208447 := bstep (se 1 (by rfl) ⟨906335, by rfl⟩ : syracuseStep 1208447 = 1812671) B1812671
theorem B5796029 : Blo 535802 5796029 := bstep (se 3 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 5796029 = 2173511) B2173511
theorem B2715929 : Blo 535802 2715929 := bstep (se 2 (by rfl) ⟨1018473, by rfl⟩ : syracuseStep 2715929 = 2036947) B2036947
theorem B1536641 : Blo 535802 1536641 := bstep (se 2 (by rfl) ⟨576240, by rfl⟩ : syracuseStep 1536641 = 1152481) B1152481
theorem B11203667 : Blo 535802 11203667 := bstep (se 1 (by rfl) ⟨8402750, by rfl⟩ : syracuseStep 11203667 = 16805501) B16805501
theorem B1209527 : Blo 535802 1209527 := bstep (se 1 (by rfl) ⟨907145, by rfl⟩ : syracuseStep 1209527 = 1814291) B1814291
theorem B5534963 : Blo 535802 5534963 := bstep (se 1 (by rfl) ⟨4151222, by rfl⟩ : syracuseStep 5534963 = 8302445) B8302445
theorem B6125057 : Blo 535802 6125057 := bstep (se 2 (by rfl) ⟨2296896, by rfl⟩ : syracuseStep 6125057 = 4593793) B4593793
theorem B1210103 : Blo 535802 1210103 := bstep (se 1 (by rfl) ⟨907577, by rfl⟩ : syracuseStep 1210103 = 1815155) B1815155
theorem B1931087 : Blo 535802 1931087 := bstep (se 1 (by rfl) ⟨1448315, by rfl⟩ : syracuseStep 1931087 = 2896631) B2896631
theorem B1210283 : Blo 535802 1210283 := bstep (se 1 (by rfl) ⟨907712, by rfl⟩ : syracuseStep 1210283 = 1815425) B1815425
theorem B1210409 : Blo 535802 1210409 := bstep (se 2 (by rfl) ⟨453903, by rfl⟩ : syracuseStep 1210409 = 907807) B907807
theorem B2586971 : Blo 535802 2586971 := bstep (se 1 (by rfl) ⟨1940228, by rfl⟩ : syracuseStep 2586971 = 3880457) B3880457
theorem B13105597 : Blo 535802 13105597 := bstep (se 3 (by rfl) ⟨2457299, by rfl⟩ : syracuseStep 13105597 = 4914599) B4914599
theorem B3439043 : Blo 535802 3439043 := bstep (se 1 (by rfl) ⟨2579282, by rfl⟩ : syracuseStep 3439043 = 5158565) B5158565
theorem B1210823 : Blo 535802 1210823 := bstep (se 1 (by rfl) ⟨908117, by rfl⟩ : syracuseStep 1210823 = 1816235) B1816235
theorem B1374761 : Blo 535802 1374761 := bstep (se 2 (by rfl) ⟨515535, by rfl⟩ : syracuseStep 1374761 = 1031071) B1031071
theorem B1210985 : Blo 535802 1210985 := bstep (se 2 (by rfl) ⟨454119, by rfl⟩ : syracuseStep 1210985 = 908239) B908239
theorem B2292371 : Blo 535802 2292371 := bstep (se 1 (by rfl) ⟨1719278, by rfl⟩ : syracuseStep 2292371 = 3438557) B3438557
theorem B1211039 : Blo 535802 1211039 := bstep (se 1 (by rfl) ⟨908279, by rfl⟩ : syracuseStep 1211039 = 1816559) B1816559
theorem B1211183 : Blo 535802 1211183 := bstep (se 1 (by rfl) ⟨908387, by rfl⟩ : syracuseStep 1211183 = 1816775) B1816775
theorem B2718845 : Blo 535802 2718845 := bstep (se 3 (by rfl) ⟨509783, by rfl⟩ : syracuseStep 2718845 = 1019567) B1019567
theorem B1211615 : Blo 535802 1211615 := bstep (se 1 (by rfl) ⟨908711, by rfl⟩ : syracuseStep 1211615 = 1817423) B1817423
theorem B3276035 : Blo 535802 3276035 := bstep (se 1 (by rfl) ⟨2457026, by rfl⟩ : syracuseStep 3276035 = 4914053) B4914053
theorem B1211831 : Blo 535802 1211831 := bstep (se 1 (by rfl) ⟨908873, by rfl⟩ : syracuseStep 1211831 = 1817747) B1817747
theorem B1212011 : Blo 535802 1212011 := bstep (se 1 (by rfl) ⟨909008, by rfl⟩ : syracuseStep 1212011 = 1818017) B1818017
theorem B1212281 : Blo 535802 1212281 := bstep (se 2 (by rfl) ⟨454605, by rfl⟩ : syracuseStep 1212281 = 909211) B909211
theorem B1212371 : Blo 535802 1212371 := bstep (se 1 (by rfl) ⟨909278, by rfl⟩ : syracuseStep 1212371 = 1818557) B1818557
theorem B2719979 : Blo 535802 2719979 := bstep (se 1 (by rfl) ⟨2039984, by rfl⟩ : syracuseStep 2719979 = 4079969) B4079969
theorem B6881669 : Blo 535802 6881669 := bstep (se 4 (by rfl) ⟨645156, by rfl⟩ : syracuseStep 6881669 = 1290313) B1290313
theorem B1475399 : Blo 535802 1475399 := bstep (se 1 (by rfl) ⟨1106549, by rfl⟩ : syracuseStep 1475399 = 2213099) B2213099
theorem B2458633 : Blo 535802 2458633 := bstep (se 2 (by rfl) ⟨921987, by rfl⟩ : syracuseStep 2458633 = 1843975) B1843975
theorem B2917565 : Blo 535802 2917565 := bstep (se 3 (by rfl) ⟨547043, by rfl⟩ : syracuseStep 2917565 = 1094087) B1094087
theorem B1017335 : Blo 535802 1017335 := bstep (se 1 (by rfl) ⟨763001, by rfl⟩ : syracuseStep 1017335 = 1526003) B1526003
theorem B2590699 : Blo 535802 2590699 := bstep (se 1 (by rfl) ⟨1943024, by rfl⟩ : syracuseStep 2590699 = 3886049) B3886049
theorem B3442783 : Blo 535802 3442783 := bstep (se 1 (by rfl) ⟨2582087, by rfl⟩ : syracuseStep 3442783 = 5164175) B5164175
theorem B2296795 : Blo 535802 2296795 := bstep (se 1 (by rfl) ⟨1722596, by rfl⟩ : syracuseStep 2296795 = 3445193) B3445193
theorem B2592161 : Blo 535802 2592161 := bstep (se 2 (by rfl) ⟨972060, by rfl⟩ : syracuseStep 2592161 = 1944121) B1944121
theorem B13241893 : Blo 535802 13241893 := bstep (se 4 (by rfl) ⟨1241427, by rfl⟩ : syracuseStep 13241893 = 2482855) B2482855
theorem B28348645 : Blo 535802 28348645 := bstep (se 4 (by rfl) ⟨2657685, by rfl⟩ : syracuseStep 28348645 = 5315371) B5315371
theorem B5149565 : Blo 535802 5149565 := bstep (se 3 (by rfl) ⟨965543, by rfl⟩ : syracuseStep 5149565 = 1931087) B1931087
theorem B10196347 : Blo 535802 10196347 := bstep (se 1 (by rfl) ⟨7647260, by rfl⟩ : syracuseStep 10196347 = 15294521) B15294521
theorem B2725487 : Blo 535802 2725487 := bstep (se 1 (by rfl) ⟨2044115, by rfl⟩ : syracuseStep 2725487 = 4088231) B4088231
theorem B12556147 : Blo 535802 12556147 := bstep (se 1 (by rfl) ⟨9417110, by rfl⟩ : syracuseStep 12556147 = 18834221) B18834221
theorem B7346065 : Blo 535802 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B1022377 : Blo 535802 1022377 := bstep (se 2 (by rfl) ⟨383391, by rfl⟩ : syracuseStep 1022377 = 766783) B766783
theorem B2038223 : Blo 535802 2038223 := bstep (se 1 (by rfl) ⟨1528667, by rfl⟩ : syracuseStep 2038223 = 3057335) B3057335
theorem B1448489 : Blo 535802 1448489 := bstep (se 2 (by rfl) ⟨543183, by rfl⟩ : syracuseStep 1448489 = 1086367) B1086367
theorem B1809161 : Blo 535802 1809161 := bstep (se 2 (by rfl) ⟨678435, by rfl⟩ : syracuseStep 1809161 = 1356871) B1356871
theorem B13966091 : Blo 535802 13966091 := bstep (se 1 (by rfl) ⟨10474568, by rfl⟩ : syracuseStep 13966091 = 20949137) B20949137
theorem B1022969 : Blo 535802 1022969 := bstep (se 2 (by rfl) ⟨383613, by rfl⟩ : syracuseStep 1022969 = 767227) B767227
theorem B1023995 : Blo 535802 1023995 := bstep (se 1 (by rfl) ⟨767996, by rfl⟩ : syracuseStep 1023995 = 1535993) B1535993
theorem B1810619 : Blo 535802 1810619 := bstep (se 1 (by rfl) ⟨1357964, by rfl⟩ : syracuseStep 1810619 = 2715929) B2715929
theorem B1024427 : Blo 535802 1024427 := bstep (se 1 (by rfl) ⟨768320, by rfl⟩ : syracuseStep 1024427 = 1536641) B1536641
theorem B1450523 : Blo 535802 1450523 := bstep (se 1 (by rfl) ⟨1087892, by rfl⟩ : syracuseStep 1450523 = 2175785) B2175785
theorem B17474129 : Blo 535802 17474129 := bstep (se 2 (by rfl) ⟨6552798, by rfl⟩ : syracuseStep 17474129 = 13105597) B13105597
theorem B6136721 : Blo 535802 6136721 := bstep (se 2 (by rfl) ⟨2301270, by rfl⟩ : syracuseStep 6136721 = 4602541) B4602541
theorem B2303801 : Blo 535802 2303801 := bstep (se 2 (by rfl) ⟨863925, by rfl⟩ : syracuseStep 2303801 = 1727851) B1727851
theorem B1812563 : Blo 535802 1812563 := bstep (se 1 (by rfl) ⟨1359422, by rfl⟩ : syracuseStep 1812563 = 2718845) B2718845
theorem B1223623 : Blo 535802 1223623 := bstep (se 1 (by rfl) ⟨917717, by rfl⟩ : syracuseStep 1223623 = 1835435) B1835435
theorem B535855 : Blo 535802 535855 := bstep (se 1 (by rfl) ⟨401891, by rfl⟩ : syracuseStep 535855 = 803783) B803783
theorem B2731319 : Blo 535802 2731319 := bstep (se 1 (by rfl) ⟨2048489, by rfl⟩ : syracuseStep 2731319 = 4096979) B4096979
theorem B535967 : Blo 535802 535967 := bstep (se 1 (by rfl) ⟨401975, by rfl⟩ : syracuseStep 535967 = 803951) B803951
theorem B536095 : Blo 535802 536095 := bstep (se 1 (by rfl) ⟨402071, by rfl⟩ : syracuseStep 536095 = 804143) B804143
theorem B7745057 : Blo 535802 7745057 := bstep (se 2 (by rfl) ⟨2904396, by rfl⟩ : syracuseStep 7745057 = 5808793) B5808793
theorem B536231 : Blo 535802 536231 := bstep (se 1 (by rfl) ⟨402173, by rfl⟩ : syracuseStep 536231 = 804347) B804347
theorem B1814183 : Blo 535802 1814183 := bstep (se 1 (by rfl) ⟨1360637, by rfl⟩ : syracuseStep 1814183 = 2721275) B2721275
theorem B536255 : Blo 535802 536255 := bstep (se 1 (by rfl) ⟨402191, by rfl⟩ : syracuseStep 536255 = 804383) B804383
theorem B536351 : Blo 535802 536351 := bstep (se 1 (by rfl) ⟨402263, by rfl⟩ : syracuseStep 536351 = 804527) B804527
theorem B536431 : Blo 535802 536431 := bstep (se 1 (by rfl) ⟨402323, by rfl⟩ : syracuseStep 536431 = 804647) B804647
theorem B3157903 : Blo 535802 3157903 := bstep (se 1 (by rfl) ⟨2368427, by rfl⟩ : syracuseStep 3157903 = 4736855) B4736855
theorem B3059795 : Blo 535802 3059795 := bstep (se 1 (by rfl) ⟨2294846, by rfl⟩ : syracuseStep 3059795 = 4589693) B4589693
theorem B536799 : Blo 535802 536799 := bstep (se 1 (by rfl) ⟨402599, by rfl⟩ : syracuseStep 536799 = 805199) B805199
theorem B536831 : Blo 535802 536831 := bstep (se 1 (by rfl) ⟨402623, by rfl⟩ : syracuseStep 536831 = 805247) B805247
theorem B3453191 : Blo 535802 3453191 := bstep (se 1 (by rfl) ⟨2589893, by rfl⟩ : syracuseStep 3453191 = 5179787) B5179787
theorem B536859 : Blo 535802 536859 := bstep (se 1 (by rfl) ⟨402644, by rfl⟩ : syracuseStep 536859 = 805289) B805289
theorem B5910893 : Blo 535802 5910893 := bstep (se 3 (by rfl) ⟨1108292, by rfl⟩ : syracuseStep 5910893 = 2216585) B2216585
theorem B537115 : Blo 535802 537115 := bstep (se 1 (by rfl) ⟨402836, by rfl⟩ : syracuseStep 537115 = 805673) B805673
theorem B537255 : Blo 535802 537255 := bstep (se 1 (by rfl) ⟨402941, by rfl⟩ : syracuseStep 537255 = 805883) B805883
theorem B537295 : Blo 535802 537295 := bstep (se 1 (by rfl) ⟨402971, by rfl⟩ : syracuseStep 537295 = 805943) B805943
theorem B3060503 : Blo 535802 3060503 := bstep (se 1 (by rfl) ⟨2295377, by rfl⟩ : syracuseStep 3060503 = 4590755) B4590755
theorem B537375 : Blo 535802 537375 := bstep (se 1 (by rfl) ⟨403031, by rfl⟩ : syracuseStep 537375 = 806063) B806063
theorem B1749919 : Blo 535802 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B1717433 : Blo 535802 1717433 := bstep (se 2 (by rfl) ⟨644037, by rfl⟩ : syracuseStep 1717433 = 1288075) B1288075
theorem B603391 : Blo 535802 603391 := bstep (se 1 (by rfl) ⟨452543, by rfl⟩ : syracuseStep 603391 = 905087) B905087
theorem B537855 : Blo 535802 537855 := bstep (se 1 (by rfl) ⟨403391, by rfl⟩ : syracuseStep 537855 = 806783) B806783
theorem B537983 : Blo 535802 537983 := bstep (se 1 (by rfl) ⟨403487, by rfl⟩ : syracuseStep 537983 = 806975) B806975
theorem B1816019 : Blo 535802 1816019 := bstep (se 1 (by rfl) ⟨1362014, by rfl⟩ : syracuseStep 1816019 = 2724029) B2724029
theorem B538139 : Blo 535802 538139 := bstep (se 1 (by rfl) ⟨403604, by rfl⟩ : syracuseStep 538139 = 807209) B807209
theorem B1717843 : Blo 535802 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B1357519 : Blo 535802 1357519 := bstep (se 1 (by rfl) ⟨1018139, by rfl⟩ : syracuseStep 1357519 = 2036279) B2036279
theorem B538319 : Blo 535802 538319 := bstep (se 1 (by rfl) ⟨403739, by rfl⟩ : syracuseStep 538319 = 807479) B807479
theorem B538559 : Blo 535802 538559 := bstep (se 1 (by rfl) ⟨403919, by rfl⟩ : syracuseStep 538559 = 807839) B807839
theorem B538687 : Blo 535802 538687 := bstep (se 1 (by rfl) ⟨404015, by rfl⟩ : syracuseStep 538687 = 808031) B808031
theorem B538727 : Blo 535802 538727 := bstep (se 1 (by rfl) ⟨404045, by rfl⟩ : syracuseStep 538727 = 808091) B808091
theorem B1456231 : Blo 535802 1456231 := bstep (se 1 (by rfl) ⟨1092173, by rfl⟩ : syracuseStep 1456231 = 2184347) B2184347
theorem B3455369 : Blo 535802 3455369 := bstep (se 2 (by rfl) ⟨1295763, by rfl⟩ : syracuseStep 3455369 = 2591527) B2591527
theorem B8862119 : Blo 535802 8862119 := bstep (se 1 (by rfl) ⟨6646589, by rfl⟩ : syracuseStep 8862119 = 13293179) B13293179
theorem B2210273 : Blo 535802 2210273 := bstep (se 2 (by rfl) ⟨828852, by rfl⟩ : syracuseStep 2210273 = 1657705) B1657705
theorem B539183 : Blo 535802 539183 := bstep (se 1 (by rfl) ⟨404387, by rfl⟩ : syracuseStep 539183 = 808775) B808775
theorem B3455905 : Blo 535802 3455905 := bstep (se 2 (by rfl) ⟨1295964, by rfl⟩ : syracuseStep 3455905 = 2591929) B2591929
theorem B605119 : Blo 535802 605119 := bstep (se 1 (by rfl) ⟨453839, by rfl⟩ : syracuseStep 605119 = 907679) B907679
theorem B4602815 : Blo 535802 4602815 := bstep (se 1 (by rfl) ⟨3452111, by rfl⟩ : syracuseStep 4602815 = 6904223) B6904223
theorem B2767807 : Blo 535802 2767807 := bstep (se 1 (by rfl) ⟨2075855, by rfl⟩ : syracuseStep 2767807 = 4151711) B4151711
theorem B539583 : Blo 535802 539583 := bstep (se 1 (by rfl) ⟨404687, by rfl⟩ : syracuseStep 539583 = 809375) B809375
theorem B539631 : Blo 535802 539631 := bstep (se 1 (by rfl) ⟨404723, by rfl⟩ : syracuseStep 539631 = 809447) B809447
theorem B8731871 : Blo 535802 8731871 := bstep (se 1 (by rfl) ⟨6548903, by rfl⟩ : syracuseStep 8731871 = 13097807) B13097807
theorem B1457615 : Blo 535802 1457615 := bstep (se 1 (by rfl) ⟨1093211, by rfl⟩ : syracuseStep 1457615 = 2186423) B2186423
theorem B605947 : Blo 535802 605947 := bstep (se 1 (by rfl) ⟨454460, by rfl⟩ : syracuseStep 605947 = 908921) B908921
theorem B1359625 : Blo 535802 1359625 := bstep (se 2 (by rfl) ⟨509859, by rfl⟩ : syracuseStep 1359625 = 1019719) B1019719
theorem B4079483 : Blo 535802 4079483 := bstep (se 1 (by rfl) ⟨3059612, by rfl⟩ : syracuseStep 4079483 = 6119225) B6119225
theorem B1294841 : Blo 535802 1294841 := bstep (se 2 (by rfl) ⟨485565, by rfl⟩ : syracuseStep 1294841 = 971131) B971131
theorem B1360415 : Blo 535802 1360415 := bstep (se 1 (by rfl) ⟨1020311, by rfl⟩ : syracuseStep 1360415 = 2040623) B2040623
theorem B3064351 : Blo 535802 3064351 := bstep (se 1 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 3064351 = 4596527) B4596527
theorem B5161715 : Blo 535802 5161715 := bstep (se 1 (by rfl) ⟨3871286, by rfl⟩ : syracuseStep 5161715 = 7742573) B7742573
theorem B607099 : Blo 535802 607099 := bstep (se 1 (by rfl) ⟨455324, by rfl⟩ : syracuseStep 607099 = 910649) B910649
theorem B804023 : Blo 535802 804023 := bstep (se 1 (by rfl) ⟨603017, by rfl⟩ : syracuseStep 804023 = 1206035) B1206035
theorem B804167 : Blo 535802 804167 := bstep (se 1 (by rfl) ⟨603125, by rfl⟩ : syracuseStep 804167 = 1206251) B1206251
theorem B804263 : Blo 535802 804263 := bstep (se 1 (by rfl) ⟨603197, by rfl⟩ : syracuseStep 804263 = 1206395) B1206395
theorem B804443 : Blo 535802 804443 := bstep (se 1 (by rfl) ⟨603332, by rfl⟩ : syracuseStep 804443 = 1206665) B1206665
theorem B2213689 : Blo 535802 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B804911 : Blo 535802 804911 := bstep (se 1 (by rfl) ⟨603683, by rfl⟩ : syracuseStep 804911 = 1207367) B1207367
theorem B805175 : Blo 535802 805175 := bstep (se 1 (by rfl) ⟨603881, by rfl⟩ : syracuseStep 805175 = 1207763) B1207763
theorem B805355 : Blo 535802 805355 := bstep (se 1 (by rfl) ⟨604016, by rfl⟩ : syracuseStep 805355 = 1208033) B1208033
theorem B805595 : Blo 535802 805595 := bstep (se 1 (by rfl) ⟨604196, by rfl⟩ : syracuseStep 805595 = 1208393) B1208393
theorem B805631 : Blo 535802 805631 := bstep (se 1 (by rfl) ⟨604223, by rfl⟩ : syracuseStep 805631 = 1208447) B1208447
theorem B806351 : Blo 535802 806351 := bstep (se 1 (by rfl) ⟨604763, by rfl⟩ : syracuseStep 806351 = 1209527) B1209527
theorem B3689975 : Blo 535802 3689975 := bstep (se 1 (by rfl) ⟨2767481, by rfl⟩ : syracuseStep 3689975 = 5534963) B5534963
theorem B806441 : Blo 535802 806441 := bstep (se 2 (by rfl) ⟨302415, by rfl⟩ : syracuseStep 806441 = 604831) B604831
theorem B4083371 : Blo 535802 4083371 := bstep (se 1 (by rfl) ⟨3062528, by rfl⟩ : syracuseStep 4083371 = 6125057) B6125057
theorem B806735 : Blo 535802 806735 := bstep (se 1 (by rfl) ⟨605051, by rfl⟩ : syracuseStep 806735 = 1210103) B1210103
theorem B806855 : Blo 535802 806855 := bstep (se 1 (by rfl) ⟨605141, by rfl⟩ : syracuseStep 806855 = 1210283) B1210283
theorem B806939 : Blo 535802 806939 := bstep (se 1 (by rfl) ⟨605204, by rfl⟩ : syracuseStep 806939 = 1210409) B1210409
theorem B1724647 : Blo 535802 1724647 := bstep (se 1 (by rfl) ⟨1293485, by rfl⟩ : syracuseStep 1724647 = 2586971) B2586971
theorem B905519 : Blo 535802 905519 := bstep (se 1 (by rfl) ⟨679139, by rfl⟩ : syracuseStep 905519 = 1358279) B1358279
theorem B807215 : Blo 535802 807215 := bstep (se 1 (by rfl) ⟨605411, by rfl⟩ : syracuseStep 807215 = 1210823) B1210823
theorem B807323 : Blo 535802 807323 := bstep (se 1 (by rfl) ⟨605492, by rfl⟩ : syracuseStep 807323 = 1210985) B1210985
theorem B1528247 : Blo 535802 1528247 := bstep (se 1 (by rfl) ⟨1146185, by rfl⟩ : syracuseStep 1528247 = 2292371) B2292371
theorem B807359 : Blo 535802 807359 := bstep (se 1 (by rfl) ⟨605519, by rfl⟩ : syracuseStep 807359 = 1211039) B1211039
theorem B807455 : Blo 535802 807455 := bstep (se 1 (by rfl) ⟨605591, by rfl⟩ : syracuseStep 807455 = 1211183) B1211183
theorem B39703159 : Blo 535802 39703159 := bstep (se 1 (by rfl) ⟨29777369, by rfl⟩ : syracuseStep 39703159 = 59554739) B59554739
theorem B807743 : Blo 535802 807743 := bstep (se 1 (by rfl) ⟨605807, by rfl⟩ : syracuseStep 807743 = 1211615) B1211615
theorem B2184023 : Blo 535802 2184023 := bstep (se 1 (by rfl) ⟨1638017, by rfl⟩ : syracuseStep 2184023 = 3276035) B3276035
theorem B11916233 : Blo 535802 11916233 := bstep (se 2 (by rfl) ⟨4468587, by rfl⟩ : syracuseStep 11916233 = 8937175) B8937175
theorem B807887 : Blo 535802 807887 := bstep (se 1 (by rfl) ⟨605915, by rfl⟩ : syracuseStep 807887 = 1211831) B1211831
theorem B807977 : Blo 535802 807977 := bstep (se 2 (by rfl) ⟨302991, by rfl⟩ : syracuseStep 807977 = 605983) B605983
theorem B808007 : Blo 535802 808007 := bstep (se 1 (by rfl) ⟨606005, by rfl⟩ : syracuseStep 808007 = 1212011) B1212011
theorem B3068999 : Blo 535802 3068999 := bstep (se 1 (by rfl) ⟨2301749, by rfl⟩ : syracuseStep 3068999 = 4603499) B4603499
theorem B906491 : Blo 535802 906491 := bstep (se 1 (by rfl) ⟨679868, by rfl⟩ : syracuseStep 906491 = 1359737) B1359737
theorem B808187 : Blo 535802 808187 := bstep (se 1 (by rfl) ⟨606140, by rfl⟩ : syracuseStep 808187 = 1212281) B1212281
theorem B808247 : Blo 535802 808247 := bstep (se 1 (by rfl) ⟨606185, by rfl⟩ : syracuseStep 808247 = 1212371) B1212371
theorem B3528047 : Blo 535802 3528047 := bstep (se 1 (by rfl) ⟨2646035, by rfl⟩ : syracuseStep 3528047 = 5292071) B5292071
theorem B808553 : Blo 535802 808553 := bstep (se 2 (by rfl) ⟨303207, by rfl⟩ : syracuseStep 808553 = 606415) B606415
theorem B3069683 : Blo 535802 3069683 := bstep (se 1 (by rfl) ⟨2302262, by rfl⟩ : syracuseStep 3069683 = 4604525) B4604525
theorem B4904707 : Blo 535802 4904707 := bstep (se 1 (by rfl) ⟨3678530, by rfl⟩ : syracuseStep 4904707 = 7357061) B7357061
theorem B809087 : Blo 535802 809087 := bstep (se 1 (by rfl) ⟨606815, by rfl⟩ : syracuseStep 809087 = 1213631) B1213631
theorem B809183 : Blo 535802 809183 := bstep (se 1 (by rfl) ⟨606887, by rfl⟩ : syracuseStep 809183 = 1213775) B1213775
theorem B809243 : Blo 535802 809243 := bstep (se 1 (by rfl) ⟨606932, by rfl⟩ : syracuseStep 809243 = 1213865) B1213865
theorem B809567 : Blo 535802 809567 := bstep (se 1 (by rfl) ⟨607175, by rfl⟩ : syracuseStep 809567 = 1214351) B1214351
theorem B809663 : Blo 535802 809663 := bstep (se 1 (by rfl) ⟨607247, by rfl⟩ : syracuseStep 809663 = 1214495) B1214495
theorem B678719 : Blo 535802 678719 := bstep (se 1 (by rfl) ⟨509039, by rfl⟩ : syracuseStep 678719 = 1018079) B1018079
theorem B679195 : Blo 535802 679195 := bstep (se 1 (by rfl) ⟨509396, by rfl⟩ : syracuseStep 679195 = 1018793) B1018793
theorem B1531163 : Blo 535802 1531163 := bstep (se 1 (by rfl) ⟨1148372, by rfl⟩ : syracuseStep 1531163 = 2296745) B2296745
theorem B45505925 : Blo 535802 45505925 := bstep (se 4 (by rfl) ⟨4266180, by rfl⟩ : syracuseStep 45505925 = 8532361) B8532361
theorem B3104225 : Blo 535802 3104225 := bstep (se 2 (by rfl) ⟨1164084, by rfl⟩ : syracuseStep 3104225 = 2328169) B2328169
theorem B6544871 : Blo 535802 6544871 := bstep (se 1 (by rfl) ⟨4908653, by rfl⟩ : syracuseStep 6544871 = 9817307) B9817307
theorem B4906603 : Blo 535802 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B1630621 : Blo 535802 1630621 := bstep (se 3 (by rfl) ⟨305741, by rfl⟩ : syracuseStep 1630621 = 611483) B611483
theorem B909967 : Blo 535802 909967 := bstep (se 1 (by rfl) ⟨682475, by rfl⟩ : syracuseStep 909967 = 1364951) B1364951
theorem B1729183 : Blo 535802 1729183 := bstep (se 1 (by rfl) ⟨1296887, by rfl⟩ : syracuseStep 1729183 = 2593775) B2593775
theorem B3433225 : Blo 535802 3433225 := bstep (se 2 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 3433225 = 2574919) B2574919
theorem B2909087 : Blo 535802 2909087 := bstep (se 1 (by rfl) ⟨2181815, by rfl⟩ : syracuseStep 2909087 = 4363631) B4363631
theorem B910703 : Blo 535802 910703 := bstep (se 1 (by rfl) ⟨683027, by rfl⟩ : syracuseStep 910703 = 1366055) B1366055
theorem B15459767 : Blo 535802 15459767 := bstep (se 1 (by rfl) ⟨11594825, by rfl⟩ : syracuseStep 15459767 = 23189651) B23189651
theorem B10479095 : Blo 535802 10479095 := bstep (se 1 (by rfl) ⟨7859321, by rfl⟩ : syracuseStep 10479095 = 15718643) B15718643
theorem B2713499 : Blo 535802 2713499 := bstep (se 1 (by rfl) ⟨2035124, by rfl⟩ : syracuseStep 2713499 = 4070249) B4070249
theorem B583583 : Blo 535802 583583 := bstep (se 1 (by rfl) ⟨437687, by rfl⟩ : syracuseStep 583583 = 875375) B875375
theorem B3074057 : Blo 535802 3074057 := bstep (se 2 (by rfl) ⟨1152771, by rfl⟩ : syracuseStep 3074057 = 2305543) B2305543
theorem B682015 : Blo 535802 682015 := bstep (se 1 (by rfl) ⟨511511, by rfl⟩ : syracuseStep 682015 = 1023023) B1023023
theorem B1534727 : Blo 535802 1534727 := bstep (se 1 (by rfl) ⟨1151045, by rfl⟩ : syracuseStep 1534727 = 2302091) B2302091
theorem B1207097 : Blo 535802 1207097 := bstep (se 2 (by rfl) ⟨452661, by rfl⟩ : syracuseStep 1207097 = 905323) B905323
theorem B5172173 : Blo 535802 5172173 := bstep (se 3 (by rfl) ⟨969782, by rfl⟩ : syracuseStep 5172173 = 1939565) B1939565
theorem B1207727 : Blo 535802 1207727 := bstep (se 1 (by rfl) ⟨905795, by rfl⟩ : syracuseStep 1207727 = 1811591) B1811591
theorem B1207979 : Blo 535802 1207979 := bstep (se 1 (by rfl) ⟨905984, by rfl⟩ : syracuseStep 1207979 = 1811969) B1811969
theorem B1863805 : Blo 535802 1863805 := bstep (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) B698927
theorem B1208519 : Blo 535802 1208519 := bstep (se 1 (by rfl) ⟨906389, by rfl⟩ : syracuseStep 1208519 = 1812779) B1812779
theorem B1208699 : Blo 535802 1208699 := bstep (se 1 (by rfl) ⟨906524, by rfl⟩ : syracuseStep 1208699 = 1813049) B1813049
theorem B6910373 : Blo 535802 6910373 := bstep (se 4 (by rfl) ⟨647847, by rfl⟩ : syracuseStep 6910373 = 1295695) B1295695
theorem B1208969 : Blo 535802 1208969 := bstep (se 2 (by rfl) ⟨453363, by rfl⟩ : syracuseStep 1208969 = 906727) B906727
theorem B6877979 : Blo 535802 6877979 := bstep (se 1 (by rfl) ⟨5158484, by rfl⟩ : syracuseStep 6877979 = 10316969) B10316969
theorem B1209185 : Blo 535802 1209185 := bstep (se 2 (by rfl) ⟨453444, by rfl⟩ : syracuseStep 1209185 = 906889) B906889
theorem B1209707 : Blo 535802 1209707 := bstep (se 1 (by rfl) ⟨907280, by rfl⟩ : syracuseStep 1209707 = 1814561) B1814561
theorem B3864019 : Blo 535802 3864019 := bstep (se 1 (by rfl) ⟨2898014, by rfl⟩ : syracuseStep 3864019 = 5796029) B5796029
theorem B1209959 : Blo 535802 1209959 := bstep (se 1 (by rfl) ⟨907469, by rfl⟩ : syracuseStep 1209959 = 1814939) B1814939
theorem B1209977 : Blo 535802 1209977 := bstep (se 2 (by rfl) ⟨453741, by rfl⟩ : syracuseStep 1209977 = 907483) B907483
theorem B13072205 : Blo 535802 13072205 := bstep (se 3 (by rfl) ⟨2451038, by rfl⟩ : syracuseStep 13072205 = 4902077) B4902077
theorem B1210337 : Blo 535802 1210337 := bstep (se 2 (by rfl) ⟨453876, by rfl⟩ : syracuseStep 1210337 = 907753) B907753
theorem B7469111 : Blo 535802 7469111 := bstep (se 1 (by rfl) ⟨5601833, by rfl⟩ : syracuseStep 7469111 = 11203667) B11203667
theorem B2914451 : Blo 535802 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B1210535 : Blo 535802 1210535 := bstep (se 1 (by rfl) ⟨907901, by rfl⟩ : syracuseStep 1210535 = 1815803) B1815803
theorem B2718035 : Blo 535802 2718035 := bstep (se 1 (by rfl) ⟨2038526, by rfl⟩ : syracuseStep 2718035 = 4077053) B4077053
theorem B2292695 : Blo 535802 2292695 := bstep (se 1 (by rfl) ⟨1719521, by rfl⟩ : syracuseStep 2292695 = 3439043) B3439043
theorem B916507 : Blo 535802 916507 := bstep (se 1 (by rfl) ⟨687380, by rfl⟩ : syracuseStep 916507 = 1374761) B1374761
theorem B1933267 : Blo 535802 1933267 := bstep (se 1 (by rfl) ⟨1449950, by rfl⟩ : syracuseStep 1933267 = 2899901) B2899901
theorem B4587779 : Blo 535802 4587779 := bstep (se 1 (by rfl) ⟨3440834, by rfl⟩ : syracuseStep 4587779 = 6881669) B6881669
theorem B3441143 : Blo 535802 3441143 := bstep (se 1 (by rfl) ⟨2580857, by rfl⟩ : syracuseStep 3441143 = 5161715) B5161715
theorem B983599 : Blo 535802 983599 := bstep (se 1 (by rfl) ⟨737699, by rfl⟩ : syracuseStep 983599 = 1475399) B1475399
theorem B1213289 : Blo 535802 1213289 := bstep (se 2 (by rfl) ⟨454983, by rfl⟩ : syracuseStep 1213289 = 909967) B909967
theorem B3278177 : Blo 535802 3278177 := bstep (se 2 (by rfl) ⟨1229316, by rfl⟩ : syracuseStep 3278177 = 2458633) B2458633
theorem B2459983 : Blo 535802 2459983 := bstep (se 1 (by rfl) ⟨1844987, by rfl⟩ : syracuseStep 2459983 = 3689975) B3689975
theorem B2951585 : Blo 535802 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B2722247 : Blo 535802 2722247 := bstep (se 1 (by rfl) ⟨2041685, by rfl⟩ : syracuseStep 2722247 = 4083371) B4083371
theorem B4590377 : Blo 535802 4590377 := bstep (se 2 (by rfl) ⟨1721391, by rfl⟩ : syracuseStep 4590377 = 3442783) B3442783
theorem B1018831 : Blo 535802 1018831 := bstep (se 1 (by rfl) ⟨764123, by rfl⟩ : syracuseStep 1018831 = 1528247) B1528247
theorem B9408125 : Blo 535802 9408125 := bstep (se 3 (by rfl) ⟨1764023, by rfl⟩ : syracuseStep 9408125 = 3528047) B3528047
theorem B9310727 : Blo 535802 9310727 := bstep (se 1 (by rfl) ⟨6983045, by rfl⟩ : syracuseStep 9310727 = 13966091) B13966091
theorem B604771093 : Blo 535802 604771093 := bstep (se 6 (by rfl) ⟨14174322, by rfl⟩ : syracuseStep 604771093 = 28348645) B28348645
theorem B1020775 : Blo 535802 1020775 := bstep (se 1 (by rfl) ⟨765581, by rfl⟩ : syracuseStep 1020775 = 1531163) B1531163
theorem B2069483 : Blo 535802 2069483 := bstep (se 1 (by rfl) ⟨1552112, by rfl⟩ : syracuseStep 2069483 = 3104225) B3104225
theorem B4363247 : Blo 535802 4363247 := bstep (se 1 (by rfl) ⟨3272435, by rfl⟩ : syracuseStep 4363247 = 6544871) B6544871
theorem B2299529 : Blo 535802 2299529 := bstep (se 2 (by rfl) ⟨862323, by rfl⟩ : syracuseStep 2299529 = 1724647) B1724647
theorem B1939391 : Blo 535802 1939391 := bstep (se 1 (by rfl) ⟨1454543, by rfl⟩ : syracuseStep 1939391 = 2909087) B2909087
theorem B6986063 : Blo 535802 6986063 := bstep (se 1 (by rfl) ⟨5239547, by rfl⟩ : syracuseStep 6986063 = 10479095) B10479095
theorem B2333225 : Blo 535802 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B1808999 : Blo 535802 1808999 := bstep (se 1 (by rfl) ⟨1356749, by rfl⟩ : syracuseStep 1808999 = 2713499) B2713499
theorem B5152025 : Blo 535802 5152025 := bstep (se 2 (by rfl) ⟨1932009, by rfl⟩ : syracuseStep 5152025 = 3864019) B3864019
theorem B3448115 : Blo 535802 3448115 := bstep (se 1 (by rfl) ⟨2586086, by rfl⟩ : syracuseStep 3448115 = 5172173) B5172173
theorem B1809917 : Blo 535802 1809917 := bstep (se 3 (by rfl) ⟨339359, by rfl⟩ : syracuseStep 1809917 = 678719) B678719
theorem B1810025 : Blo 535802 1810025 := bstep (se 2 (by rfl) ⟨678759, by rfl⟩ : syracuseStep 1810025 = 1357519) B1357519
theorem B2727917 : Blo 535802 2727917 := bstep (se 3 (by rfl) ⟨511484, by rfl⟩ : syracuseStep 2727917 = 1022969) B1022969
theorem B2039863 : Blo 535802 2039863 := bstep (se 1 (by rfl) ⟨1529897, by rfl⟩ : syracuseStep 2039863 = 3059795) B3059795
theorem B1941641 : Blo 535802 1941641 := bstep (se 2 (by rfl) ⟨728115, by rfl⟩ : syracuseStep 1941641 = 1456231) B1456231
theorem B2302127 : Blo 535802 2302127 := bstep (se 1 (by rfl) ⟨1726595, by rfl⟩ : syracuseStep 2302127 = 3453191) B3453191
theorem B3940595 : Blo 535802 3940595 := bstep (se 1 (by rfl) ⟨2955446, by rfl⟩ : syracuseStep 3940595 = 5910893) B5910893
theorem B2040335 : Blo 535802 2040335 := bstep (se 1 (by rfl) ⟨1530251, by rfl⟩ : syracuseStep 2040335 = 3060503) B3060503
theorem B1222009 : Blo 535802 1222009 := bstep (se 2 (by rfl) ⟨458253, by rfl⟩ : syracuseStep 1222009 = 916507) B916507
theorem B1942967 : Blo 535802 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B1812023 : Blo 535802 1812023 := bstep (se 1 (by rfl) ⟨1359017, by rfl⟩ : syracuseStep 1812023 = 2718035) B2718035
theorem B2303579 : Blo 535802 2303579 := bstep (se 1 (by rfl) ⟨1727684, by rfl⟩ : syracuseStep 2303579 = 3455369) B3455369
theorem B5908079 : Blo 535802 5908079 := bstep (se 1 (by rfl) ⟨4431059, by rfl⟩ : syracuseStep 5908079 = 8862119) B8862119
theorem B1812833 : Blo 535802 1812833 := bstep (se 2 (by rfl) ⟨679812, by rfl⟩ : syracuseStep 1812833 = 1359625) B1359625
theorem B1813319 : Blo 535802 1813319 := bstep (se 1 (by rfl) ⟨1359989, by rfl⟩ : syracuseStep 1813319 = 2719979) B2719979
theorem B863227 : Blo 535802 863227 := bstep (se 1 (by rfl) ⟨647420, by rfl⟩ : syracuseStep 863227 = 1294841) B1294841
theorem B2174161 : Blo 535802 2174161 := bstep (se 2 (by rfl) ⟨815310, by rfl⟩ : syracuseStep 2174161 = 1630621) B1630621
theorem B536015 : Blo 535802 536015 := bstep (se 1 (by rfl) ⟨402011, by rfl⟩ : syracuseStep 536015 = 804023) B804023
theorem B1945043 : Blo 535802 1945043 := bstep (se 1 (by rfl) ⟨1458782, by rfl⟩ : syracuseStep 1945043 = 2917565) B2917565
theorem B2305577 : Blo 535802 2305577 := bstep (se 2 (by rfl) ⟨864591, by rfl⟩ : syracuseStep 2305577 = 1729183) B1729183
theorem B536111 : Blo 535802 536111 := bstep (se 1 (by rfl) ⟨402083, by rfl⟩ : syracuseStep 536111 = 804167) B804167
theorem B536175 : Blo 535802 536175 := bstep (se 1 (by rfl) ⟨402131, by rfl⟩ : syracuseStep 536175 = 804263) B804263
theorem B536295 : Blo 535802 536295 := bstep (se 1 (by rfl) ⟨402221, by rfl⟩ : syracuseStep 536295 = 804443) B804443
theorem B2731805 : Blo 535802 2731805 := bstep (se 3 (by rfl) ⟨512213, by rfl⟩ : syracuseStep 2731805 = 1024427) B1024427
theorem B536607 : Blo 535802 536607 := bstep (se 1 (by rfl) ⟨402455, by rfl⟩ : syracuseStep 536607 = 804911) B804911
theorem B536783 : Blo 535802 536783 := bstep (se 1 (by rfl) ⟨402587, by rfl⟩ : syracuseStep 536783 = 805175) B805175
theorem B536903 : Blo 535802 536903 := bstep (se 1 (by rfl) ⟨402677, by rfl⟩ : syracuseStep 536903 = 805355) B805355
theorem B537063 : Blo 535802 537063 := bstep (se 1 (by rfl) ⟨402797, by rfl⟩ : syracuseStep 537063 = 805595) B805595
theorem B537087 : Blo 535802 537087 := bstep (se 1 (by rfl) ⟨402815, by rfl⟩ : syracuseStep 537087 = 805631) B805631
theorem B537567 : Blo 535802 537567 := bstep (se 1 (by rfl) ⟨403175, by rfl⟩ : syracuseStep 537567 = 806351) B806351
theorem B537627 : Blo 535802 537627 := bstep (se 1 (by rfl) ⟨403220, by rfl⟩ : syracuseStep 537627 = 806441) B806441
theorem B537823 : Blo 535802 537823 := bstep (se 1 (by rfl) ⟨403367, by rfl⟩ : syracuseStep 537823 = 806735) B806735
theorem B537903 : Blo 535802 537903 := bstep (se 1 (by rfl) ⟨403427, by rfl⟩ : syracuseStep 537903 = 806855) B806855
theorem B3454265 : Blo 535802 3454265 := bstep (se 2 (by rfl) ⟨1295349, by rfl⟩ : syracuseStep 3454265 = 2590699) B2590699
theorem B537959 : Blo 535802 537959 := bstep (se 1 (by rfl) ⟨403469, by rfl⟩ : syracuseStep 537959 = 806939) B806939
theorem B603679 : Blo 535802 603679 := bstep (se 1 (by rfl) ⟨452759, by rfl⟩ : syracuseStep 603679 = 905519) B905519
theorem B538143 : Blo 535802 538143 := bstep (se 1 (by rfl) ⟨403607, by rfl⟩ : syracuseStep 538143 = 807215) B807215
theorem B538215 : Blo 535802 538215 := bstep (se 1 (by rfl) ⟨403661, by rfl⟩ : syracuseStep 538215 = 807323) B807323
theorem B538239 : Blo 535802 538239 := bstep (se 1 (by rfl) ⟨403679, by rfl⟩ : syracuseStep 538239 = 807359) B807359
theorem B538303 : Blo 535802 538303 := bstep (se 1 (by rfl) ⟨403727, by rfl⟩ : syracuseStep 538303 = 807455) B807455
theorem B538495 : Blo 535802 538495 := bstep (se 1 (by rfl) ⟨403871, by rfl⟩ : syracuseStep 538495 = 807743) B807743
theorem B1456015 : Blo 535802 1456015 := bstep (se 1 (by rfl) ⟨1092011, by rfl⟩ : syracuseStep 1456015 = 2184023) B2184023
theorem B7944155 : Blo 535802 7944155 := bstep (se 1 (by rfl) ⟨5958116, by rfl⟩ : syracuseStep 7944155 = 11916233) B11916233
theorem B538591 : Blo 535802 538591 := bstep (se 1 (by rfl) ⟨403943, by rfl⟩ : syracuseStep 538591 = 807887) B807887
theorem B538651 : Blo 535802 538651 := bstep (se 1 (by rfl) ⟨403988, by rfl⟩ : syracuseStep 538651 = 807977) B807977
theorem B538671 : Blo 535802 538671 := bstep (se 1 (by rfl) ⟨404003, by rfl⟩ : syracuseStep 538671 = 808007) B808007
theorem B2045999 : Blo 535802 2045999 := bstep (se 1 (by rfl) ⟨1534499, by rfl⟩ : syracuseStep 2045999 = 3068999) B3068999
theorem B604327 : Blo 535802 604327 := bstep (se 1 (by rfl) ⟨453245, by rfl⟩ : syracuseStep 604327 = 906491) B906491
theorem B538791 : Blo 535802 538791 := bstep (se 1 (by rfl) ⟨404093, by rfl⟩ : syracuseStep 538791 = 808187) B808187
theorem B538831 : Blo 535802 538831 := bstep (se 1 (by rfl) ⟨404123, by rfl⟩ : syracuseStep 538831 = 808247) B808247
theorem B539035 : Blo 535802 539035 := bstep (se 1 (by rfl) ⟨404276, by rfl⟩ : syracuseStep 539035 = 808553) B808553
theorem B1816991 : Blo 535802 1816991 := bstep (se 1 (by rfl) ⟨1362743, by rfl⟩ : syracuseStep 1816991 = 2725487) B2725487
theorem B2046455 : Blo 535802 2046455 := bstep (se 1 (by rfl) ⟨1534841, by rfl⟩ : syracuseStep 2046455 = 3069683) B3069683
theorem B3062393 : Blo 535802 3062393 := bstep (se 2 (by rfl) ⟨1148397, by rfl⟩ : syracuseStep 3062393 = 2296795) B2296795
theorem B539391 : Blo 535802 539391 := bstep (se 1 (by rfl) ⟨404543, by rfl⟩ : syracuseStep 539391 = 809087) B809087
theorem B539455 : Blo 535802 539455 := bstep (se 1 (by rfl) ⟨404591, by rfl⟩ : syracuseStep 539455 = 809183) B809183
theorem B539495 : Blo 535802 539495 := bstep (se 1 (by rfl) ⟨404621, by rfl⟩ : syracuseStep 539495 = 809243) B809243
theorem B1358815 : Blo 535802 1358815 := bstep (se 1 (by rfl) ⟨1019111, by rfl⟩ : syracuseStep 1358815 = 2038223) B2038223
theorem B539711 : Blo 535802 539711 := bstep (se 1 (by rfl) ⟨404783, by rfl⟩ : syracuseStep 539711 = 809567) B809567
theorem B539775 : Blo 535802 539775 := bstep (se 1 (by rfl) ⟨404831, by rfl⟩ : syracuseStep 539775 = 809663) B809663
theorem B1556221 : Blo 535802 1556221 := bstep (se 3 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 1556221 = 583583) B583583
theorem B4210537 : Blo 535802 4210537 := bstep (se 2 (by rfl) ⟨1578951, by rfl⟩ : syracuseStep 4210537 = 3157903) B3157903
theorem B967015 : Blo 535802 967015 := bstep (se 1 (by rfl) ⟨725261, by rfl⟩ : syracuseStep 967015 = 1450523) B1450523
theorem B11649419 : Blo 535802 11649419 := bstep (se 1 (by rfl) ⟨8737064, by rfl⟩ : syracuseStep 11649419 = 17474129) B17474129
theorem B52937545 : Blo 535802 52937545 := bstep (se 2 (by rfl) ⟨19851579, by rfl⟩ : syracuseStep 52937545 = 39703159) B39703159
theorem B607135 : Blo 535802 607135 := bstep (se 1 (by rfl) ⟨455351, by rfl⟩ : syracuseStep 607135 = 910703) B910703
theorem B10306511 : Blo 535802 10306511 := bstep (se 1 (by rfl) ⟨7729883, by rfl⟩ : syracuseStep 10306511 = 15459767) B15459767
theorem B2049371 : Blo 535802 2049371 := bstep (se 1 (by rfl) ⟨1537028, by rfl⟩ : syracuseStep 2049371 = 3074057) B3074057
theorem B804521 : Blo 535802 804521 := bstep (se 2 (by rfl) ⟨301695, by rfl⟩ : syracuseStep 804521 = 603391) B603391
theorem B804731 : Blo 535802 804731 := bstep (se 1 (by rfl) ⟨603548, by rfl⟩ : syracuseStep 804731 = 1207097) B1207097
theorem B1820879 : Blo 535802 1820879 := bstep (se 1 (by rfl) ⟨1365659, by rfl⟩ : syracuseStep 1820879 = 2731319) B2731319
theorem B805151 : Blo 535802 805151 := bstep (se 1 (by rfl) ⟨603863, by rfl⟩ : syracuseStep 805151 = 1207727) B1207727
theorem B6539609 : Blo 535802 6539609 := bstep (se 2 (by rfl) ⟨2452353, by rfl⟩ : syracuseStep 6539609 = 4904707) B4904707
theorem B5163371 : Blo 535802 5163371 := bstep (se 1 (by rfl) ⟨3872528, by rfl⟩ : syracuseStep 5163371 = 7745057) B7745057
theorem B805319 : Blo 535802 805319 := bstep (se 1 (by rfl) ⟨603989, by rfl⟩ : syracuseStep 805319 = 1207979) B1207979
theorem B805679 : Blo 535802 805679 := bstep (se 1 (by rfl) ⟨604259, by rfl⟩ : syracuseStep 805679 = 1208519) B1208519
theorem B805799 : Blo 535802 805799 := bstep (se 1 (by rfl) ⟨604349, by rfl⟩ : syracuseStep 805799 = 1208699) B1208699
theorem B4606915 : Blo 535802 4606915 := bstep (se 1 (by rfl) ⟨3455186, by rfl⟩ : syracuseStep 4606915 = 6910373) B6910373
theorem B805979 : Blo 535802 805979 := bstep (se 1 (by rfl) ⟨604484, by rfl⟩ : syracuseStep 805979 = 1208969) B1208969
theorem B1363169 : Blo 535802 1363169 := bstep (se 2 (by rfl) ⟨511188, by rfl⟩ : syracuseStep 1363169 = 1022377) B1022377
theorem B806123 : Blo 535802 806123 := bstep (se 1 (by rfl) ⟨604592, by rfl⟩ : syracuseStep 806123 = 1209185) B1209185
theorem B806471 : Blo 535802 806471 := bstep (se 1 (by rfl) ⟨604853, by rfl⟩ : syracuseStep 806471 = 1209707) B1209707
theorem B806639 : Blo 535802 806639 := bstep (se 1 (by rfl) ⟨604979, by rfl⟩ : syracuseStep 806639 = 1209959) B1209959
theorem B806651 : Blo 535802 806651 := bstep (se 1 (by rfl) ⟨604988, by rfl⟩ : syracuseStep 806651 = 1209977) B1209977
theorem B3886973 : Blo 535802 3886973 := bstep (se 3 (by rfl) ⟨728807, by rfl⟩ : syracuseStep 3886973 = 1457615) B1457615
theorem B4607873 : Blo 535802 4607873 := bstep (se 2 (by rfl) ⟨1727952, by rfl⟩ : syracuseStep 4607873 = 3455905) B3455905
theorem B806825 : Blo 535802 806825 := bstep (se 2 (by rfl) ⟨302559, by rfl⟩ : syracuseStep 806825 = 605119) B605119
theorem B3690409 : Blo 535802 3690409 := bstep (se 2 (by rfl) ⟨1383903, by rfl⟩ : syracuseStep 3690409 = 2767807) B2767807
theorem B806891 : Blo 535802 806891 := bstep (se 1 (by rfl) ⟨605168, by rfl⟩ : syracuseStep 806891 = 1210337) B1210337
theorem B807023 : Blo 535802 807023 := bstep (se 1 (by rfl) ⟨605267, by rfl⟩ : syracuseStep 807023 = 1210535) B1210535
theorem B905593 : Blo 535802 905593 := bstep (se 2 (by rfl) ⟨339597, by rfl⟩ : syracuseStep 905593 = 679195) B679195
theorem B3068543 : Blo 535802 3068543 := bstep (se 1 (by rfl) ⟨2301407, by rfl⟩ : syracuseStep 3068543 = 4602815) B4602815
theorem B1528463 : Blo 535802 1528463 := bstep (se 1 (by rfl) ⟨1146347, by rfl⟩ : syracuseStep 1528463 = 2292695) B2292695
theorem B6542137 : Blo 535802 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B5821247 : Blo 535802 5821247 := bstep (se 1 (by rfl) ⟨4365935, by rfl⟩ : syracuseStep 5821247 = 8731871) B8731871
theorem B807929 : Blo 535802 807929 := bstep (se 2 (by rfl) ⟨302973, by rfl⟩ : syracuseStep 807929 = 605947) B605947
theorem B2577689 : Blo 535802 2577689 := bstep (se 2 (by rfl) ⟨966633, by rfl⟩ : syracuseStep 2577689 = 1933267) B1933267
theorem B906943 : Blo 535802 906943 := bstep (se 1 (by rfl) ⟨680207, by rfl⟩ : syracuseStep 906943 = 1360415) B1360415
theorem B4085801 : Blo 535802 4085801 := bstep (se 2 (by rfl) ⟨1532175, by rfl⟩ : syracuseStep 4085801 = 3064351) B3064351
theorem B678223 : Blo 535802 678223 := bstep (se 1 (by rfl) ⟨508667, by rfl⟩ : syracuseStep 678223 = 1017335) B1017335
theorem B4577633 : Blo 535802 4577633 := bstep (se 2 (by rfl) ⟨1716612, by rfl⟩ : syracuseStep 4577633 = 3433225) B3433225
theorem B809465 : Blo 535802 809465 := bstep (se 2 (by rfl) ⟨303549, by rfl⟩ : syracuseStep 809465 = 607099) B607099
theorem B1728107 : Blo 535802 1728107 := bstep (se 1 (by rfl) ⟨1296080, by rfl⟩ : syracuseStep 1728107 = 2592161) B2592161
theorem B909353 : Blo 535802 909353 := bstep (se 2 (by rfl) ⟨341007, by rfl⟩ : syracuseStep 909353 = 682015) B682015
theorem B3433043 : Blo 535802 3433043 := bstep (se 1 (by rfl) ⟨2574782, by rfl⟩ : syracuseStep 3433043 = 5149565) B5149565
theorem B1631497 : Blo 535802 1631497 := bstep (se 2 (by rfl) ⟨611811, by rfl⟩ : syracuseStep 1631497 = 1223623) B1223623
theorem B1206107 : Blo 535802 1206107 := bstep (se 1 (by rfl) ⟨904580, by rfl⟩ : syracuseStep 1206107 = 1809161) B1809161
theorem B17655857 : Blo 535802 17655857 := bstep (se 2 (by rfl) ⟨6620946, by rfl⟩ : syracuseStep 17655857 = 13241893) B13241893
theorem B30337283 : Blo 535802 30337283 := bstep (se 1 (by rfl) ⟨22752962, by rfl⟩ : syracuseStep 30337283 = 45505925) B45505925
theorem B682663 : Blo 535802 682663 := bstep (se 1 (by rfl) ⟨511997, by rfl⟩ : syracuseStep 682663 = 1023995) B1023995
theorem B1207079 : Blo 535802 1207079 := bstep (se 1 (by rfl) ⟨905309, by rfl⟩ : syracuseStep 1207079 = 1810619) B1810619
theorem B2485073 : Blo 535802 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B4091147 : Blo 535802 4091147 := bstep (se 1 (by rfl) ⟨3068360, by rfl⟩ : syracuseStep 4091147 = 6136721) B6136721
theorem B1535867 : Blo 535802 1535867 := bstep (se 1 (by rfl) ⟨1151900, by rfl⟩ : syracuseStep 1535867 = 2303801) B2303801
theorem B1208375 : Blo 535802 1208375 := bstep (se 1 (by rfl) ⟨906281, by rfl⟩ : syracuseStep 1208375 = 1812563) B1812563
theorem B3862637 : Blo 535802 3862637 := bstep (se 3 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 3862637 = 1448489) B1448489
theorem B13595129 : Blo 535802 13595129 := bstep (se 2 (by rfl) ⟨5098173, by rfl⟩ : syracuseStep 13595129 = 10196347) B10196347
theorem B4092605 : Blo 535802 4092605 := bstep (se 3 (by rfl) ⟨767363, by rfl⟩ : syracuseStep 4092605 = 1534727) B1534727
theorem B2290457 : Blo 535802 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B1209455 : Blo 535802 1209455 := bstep (se 1 (by rfl) ⟨907091, by rfl⟩ : syracuseStep 1209455 = 1814183) B1814183
theorem B16741529 : Blo 535802 16741529 := bstep (se 2 (by rfl) ⟨6278073, by rfl⟩ : syracuseStep 16741529 = 12556147) B12556147
theorem B9794753 : Blo 535802 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B4585319 : Blo 535802 4585319 := bstep (se 1 (by rfl) ⟨3438989, by rfl⟩ : syracuseStep 4585319 = 6877979) B6877979
theorem B1144955 : Blo 535802 1144955 := bstep (se 1 (by rfl) ⟨858716, by rfl⟩ : syracuseStep 1144955 = 1717433) B1717433
theorem B1210679 : Blo 535802 1210679 := bstep (se 1 (by rfl) ⟨908009, by rfl⟩ : syracuseStep 1210679 = 1816019) B1816019
theorem B8714803 : Blo 535802 8714803 := bstep (se 1 (by rfl) ⟨6536102, by rfl⟩ : syracuseStep 8714803 = 13072205) B13072205
theorem B4979407 : Blo 535802 4979407 := bstep (se 1 (by rfl) ⟨3734555, by rfl⟩ : syracuseStep 4979407 = 7469111) B7469111
theorem B1473515 : Blo 535802 1473515 := bstep (se 1 (by rfl) ⟨1105136, by rfl⟩ : syracuseStep 1473515 = 2210273) B2210273
theorem B2719655 : Blo 535802 2719655 := bstep (se 1 (by rfl) ⟨2039741, by rfl⟩ : syracuseStep 2719655 = 4079483) B4079483
theorem B2719817 : Blo 535802 2719817 := bstep (se 2 (by rfl) ⟨1019931, by rfl⟩ : syracuseStep 2719817 = 2039863) B2039863
theorem B7766279 : Blo 535802 7766279 := bstep (se 1 (by rfl) ⟨5824709, by rfl⟩ : syracuseStep 7766279 = 11649419) B11649419
theorem B2294095 : Blo 535802 2294095 := bstep (se 1 (by rfl) ⟨1720571, by rfl⟩ : syracuseStep 2294095 = 3441143) B3441143
theorem B70583393 : Blo 535802 70583393 := bstep (se 2 (by rfl) ⟨26468772, by rfl⟩ : syracuseStep 70583393 = 52937545) B52937545
theorem B1213919 : Blo 535802 1213919 := bstep (se 1 (by rfl) ⟨910439, by rfl⟩ : syracuseStep 1213919 = 1820879) B1820879
theorem B4359739 : Blo 535802 4359739 := bstep (se 1 (by rfl) ⟨3269804, by rfl⟩ : syracuseStep 4359739 = 6539609) B6539609
theorem B3442247 : Blo 535802 3442247 := bstep (se 1 (by rfl) ⟨2581685, by rfl⟩ : syracuseStep 3442247 = 5163371) B5163371
theorem B1967723 : Blo 535802 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B2591315 : Blo 535802 2591315 := bstep (se 1 (by rfl) ⟨1943486, by rfl⟩ : syracuseStep 2591315 = 3886973) B3886973
theorem B1018975 : Blo 535802 1018975 := bstep (se 1 (by rfl) ⟨764231, by rfl⟩ : syracuseStep 1018975 = 1528463) B1528463
theorem B3279977 : Blo 535802 3279977 := bstep (se 2 (by rfl) ⟨1229991, by rfl⟩ : syracuseStep 3279977 = 2459983) B2459983
theorem B5181245 : Blo 535802 5181245 := bstep (se 3 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 5181245 = 1942967) B1942967
theorem B2723867 : Blo 535802 2723867 := bstep (se 1 (by rfl) ⟨2042900, by rfl⟩ : syracuseStep 2723867 = 4085801) B4085801
theorem B4657375 : Blo 535802 4657375 := bstep (se 1 (by rfl) ⟨3493031, by rfl⟩ : syracuseStep 4657375 = 6986063) B6986063
theorem B3051755 : Blo 535802 3051755 := bstep (se 1 (by rfl) ⟨2288816, by rfl⟩ : syracuseStep 3051755 = 4577633) B4577633
theorem B2298743 : Blo 535802 2298743 := bstep (se 1 (by rfl) ⟨1724057, by rfl⟩ : syracuseStep 2298743 = 3448115) B3448115
theorem B1152071 : Blo 535802 1152071 := bstep (se 1 (by rfl) ⟨864053, by rfl⟩ : syracuseStep 1152071 = 1728107) B1728107
theorem B4920545 : Blo 535802 4920545 := bstep (se 2 (by rfl) ⟨1845204, by rfl⟩ : syracuseStep 4920545 = 3690409) B3690409
theorem B2627063 : Blo 535802 2627063 := bstep (se 1 (by rfl) ⟨1970297, by rfl⟩ : syracuseStep 2627063 = 3940595) B3940595
theorem B3053213 : Blo 535802 3053213 := bstep (se 3 (by rfl) ⟨572477, by rfl⟩ : syracuseStep 3053213 = 1144955) B1144955
theorem B3938719 : Blo 535802 3938719 := bstep (se 1 (by rfl) ⟨2954039, by rfl⟩ : syracuseStep 3938719 = 5908079) B5908079
theorem B11770571 : Blo 535802 11770571 := bstep (se 1 (by rfl) ⟨8827928, by rfl⟩ : syracuseStep 11770571 = 17655857) B17655857
theorem B20224855 : Blo 535802 20224855 := bstep (se 1 (by rfl) ⟨15168641, by rfl⟩ : syracuseStep 20224855 = 30337283) B30337283
theorem B2727431 : Blo 535802 2727431 := bstep (se 1 (by rfl) ⟨2045573, by rfl⟩ : syracuseStep 2727431 = 4091147) B4091147
theorem B6626861 : Blo 535802 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B1941353 : Blo 535802 1941353 := bstep (se 2 (by rfl) ⟨728007, by rfl⟩ : syracuseStep 1941353 = 1456015) B1456015
theorem B1023911 : Blo 535802 1023911 := bstep (se 1 (by rfl) ⟨767933, by rfl⟩ : syracuseStep 1023911 = 1535867) B1535867
theorem B2728403 : Blo 535802 2728403 := bstep (se 1 (by rfl) ⟨2046302, by rfl⟩ : syracuseStep 2728403 = 4092605) B4092605
theorem B13738733 : Blo 535802 13738733 := bstep (se 3 (by rfl) ⟨2576012, by rfl⟩ : syracuseStep 13738733 = 5152025) B5152025
theorem B6529835 : Blo 535802 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B2302843 : Blo 535802 2302843 := bstep (se 1 (by rfl) ⟨1727132, by rfl⟩ : syracuseStep 2302843 = 3454265) B3454265
theorem B3056879 : Blo 535802 3056879 := bstep (se 1 (by rfl) ⟨2292659, by rfl⟩ : syracuseStep 3056879 = 4585319) B4585319
theorem B1811753 : Blo 535802 1811753 := bstep (se 2 (by rfl) ⟨679407, by rfl⟩ : syracuseStep 1811753 = 1358815) B1358815
theorem B2041595 : Blo 535802 2041595 := bstep (se 1 (by rfl) ⟨1531196, by rfl⟩ : syracuseStep 2041595 = 3062393) B3062393
theorem B2074961 : Blo 535802 2074961 := bstep (se 2 (by rfl) ⟨778110, by rfl⟩ : syracuseStep 2074961 = 1556221) B1556221
theorem B5614049 : Blo 535802 5614049 := bstep (se 2 (by rfl) ⟨2105268, by rfl⟩ : syracuseStep 5614049 = 4210537) B4210537
theorem B1813103 : Blo 535802 1813103 := bstep (se 1 (by rfl) ⟨1359827, by rfl⟩ : syracuseStep 1813103 = 2719655) B2719655
theorem B3058519 : Blo 535802 3058519 := bstep (se 1 (by rfl) ⟨2293889, by rfl⟩ : syracuseStep 3058519 = 4587779) B4587779
theorem B1289353 : Blo 535802 1289353 := bstep (se 2 (by rfl) ⟨483507, by rfl⟩ : syracuseStep 1289353 = 967015) B967015
theorem B20983445 : Blo 535802 20983445 := bstep (se 6 (by rfl) ⟨491799, by rfl⟩ : syracuseStep 20983445 = 983599) B983599
theorem B536347 : Blo 535802 536347 := bstep (se 1 (by rfl) ⟨402260, by rfl⟩ : syracuseStep 536347 = 804521) B804521
theorem B536487 : Blo 535802 536487 := bstep (se 1 (by rfl) ⟨402365, by rfl⟩ : syracuseStep 536487 = 804731) B804731
theorem B536767 : Blo 535802 536767 := bstep (se 1 (by rfl) ⟨402575, by rfl⟩ : syracuseStep 536767 = 805151) B805151
theorem B9154781 : Blo 535802 9154781 := bstep (se 3 (by rfl) ⟨1716521, by rfl⟩ : syracuseStep 9154781 = 3433043) B3433043
theorem B536879 : Blo 535802 536879 := bstep (se 1 (by rfl) ⟨402659, by rfl⟩ : syracuseStep 536879 = 805319) B805319
theorem B1814831 : Blo 535802 1814831 := bstep (se 1 (by rfl) ⟨1361123, by rfl⟩ : syracuseStep 1814831 = 2722247) B2722247
theorem B2175329 : Blo 535802 2175329 := bstep (se 2 (by rfl) ⟨815748, by rfl⟩ : syracuseStep 2175329 = 1631497) B1631497
theorem B3060251 : Blo 535802 3060251 := bstep (se 1 (by rfl) ⟨2295188, by rfl⟩ : syracuseStep 3060251 = 4590377) B4590377
theorem B537119 : Blo 535802 537119 := bstep (se 1 (by rfl) ⟨402839, by rfl⟩ : syracuseStep 537119 = 805679) B805679
theorem B537199 : Blo 535802 537199 := bstep (se 1 (by rfl) ⟨402899, by rfl⟩ : syracuseStep 537199 = 805799) B805799
theorem B537319 : Blo 535802 537319 := bstep (se 1 (by rfl) ⟨402989, by rfl⟩ : syracuseStep 537319 = 805979) B805979
theorem B537415 : Blo 535802 537415 := bstep (se 1 (by rfl) ⟨403061, by rfl⟩ : syracuseStep 537415 = 806123) B806123
theorem B537647 : Blo 535802 537647 := bstep (se 1 (by rfl) ⟨403235, by rfl⟩ : syracuseStep 537647 = 806471) B806471
theorem B6272083 : Blo 535802 6272083 := bstep (se 1 (by rfl) ⟨4704062, by rfl⟩ : syracuseStep 6272083 = 9408125) B9408125
theorem B537759 : Blo 535802 537759 := bstep (se 1 (by rfl) ⟨403319, by rfl⟩ : syracuseStep 537759 = 806639) B806639
theorem B537767 : Blo 535802 537767 := bstep (se 1 (by rfl) ⟨403325, by rfl⟩ : syracuseStep 537767 = 806651) B806651
theorem B537883 : Blo 535802 537883 := bstep (se 1 (by rfl) ⟨403412, by rfl⟩ : syracuseStep 537883 = 806825) B806825
theorem B5518621 : Blo 535802 5518621 := bstep (se 3 (by rfl) ⟨1034741, by rfl⟩ : syracuseStep 5518621 = 2069483) B2069483
theorem B537927 : Blo 535802 537927 := bstep (se 1 (by rfl) ⟨403445, by rfl⟩ : syracuseStep 537927 = 806891) B806891
theorem B538015 : Blo 535802 538015 := bstep (se 1 (by rfl) ⟨403511, by rfl⟩ : syracuseStep 538015 = 807023) B807023
theorem B6207151 : Blo 535802 6207151 := bstep (se 1 (by rfl) ⟨4655363, by rfl⟩ : syracuseStep 6207151 = 9310727) B9310727
theorem B2045695 : Blo 535802 2045695 := bstep (se 1 (by rfl) ⟨1534271, by rfl⟩ : syracuseStep 2045695 = 3068543) B3068543
theorem B538619 : Blo 535802 538619 := bstep (se 1 (by rfl) ⟨403964, by rfl⟩ : syracuseStep 538619 = 807929) B807929
theorem B1718459 : Blo 535802 1718459 := bstep (se 1 (by rfl) ⟨1288844, by rfl⟩ : syracuseStep 1718459 = 2577689) B2577689
theorem B6142553 : Blo 535802 6142553 := bstep (se 2 (by rfl) ⟨2303457, by rfl⟩ : syracuseStep 6142553 = 4606915) B4606915
theorem B1358441 : Blo 535802 1358441 := bstep (se 2 (by rfl) ⟨509415, by rfl⟩ : syracuseStep 1358441 = 1018831) B1018831
theorem B1292927 : Blo 535802 1292927 := bstep (se 1 (by rfl) ⟨969695, by rfl⟩ : syracuseStep 1292927 = 1939391) B1939391
theorem B2898881 : Blo 535802 2898881 := bstep (se 2 (by rfl) ⟨1087080, by rfl⟩ : syracuseStep 2898881 = 2174161) B2174161
theorem B539643 : Blo 535802 539643 := bstep (se 1 (by rfl) ⟨404732, by rfl⟩ : syracuseStep 539643 = 809465) B809465
theorem B4603877 : Blo 535802 4603877 := bstep (se 4 (by rfl) ⟨431613, by rfl⟩ : syracuseStep 4603877 = 863227) B863227
theorem B1818611 : Blo 535802 1818611 := bstep (se 1 (by rfl) ⟨1363958, by rfl⟩ : syracuseStep 1818611 = 2727917) B2727917
theorem B606235 : Blo 535802 606235 := bstep (se 1 (by rfl) ⟨454676, by rfl⟩ : syracuseStep 606235 = 909353) B909353
theorem B1294427 : Blo 535802 1294427 := bstep (se 1 (by rfl) ⟨970820, by rfl⟩ : syracuseStep 1294427 = 1941641) B1941641
theorem B1360223 : Blo 535802 1360223 := bstep (se 1 (by rfl) ⟨1020167, by rfl⟩ : syracuseStep 1360223 = 2040335) B2040335
theorem B1361033 : Blo 535802 1361033 := bstep (se 2 (by rfl) ⟨510387, by rfl⟩ : syracuseStep 1361033 = 1020775) B1020775
theorem B804071 : Blo 535802 804071 := bstep (se 1 (by rfl) ⟨603053, by rfl⟩ : syracuseStep 804071 = 1206107) B1206107
theorem B804719 : Blo 535802 804719 := bstep (se 1 (by rfl) ⟨603539, by rfl⟩ : syracuseStep 804719 = 1207079) B1207079
theorem B804905 : Blo 535802 804905 := bstep (se 2 (by rfl) ⟨301839, by rfl⟩ : syracuseStep 804905 = 603679) B603679
theorem B1296695 : Blo 535802 1296695 := bstep (se 1 (by rfl) ⟨972521, by rfl⟩ : syracuseStep 1296695 = 1945043) B1945043
theorem B1821203 : Blo 535802 1821203 := bstep (se 1 (by rfl) ⟨1365902, by rfl⟩ : syracuseStep 1821203 = 2731805) B2731805
theorem B805583 : Blo 535802 805583 := bstep (se 1 (by rfl) ⟨604187, by rfl⟩ : syracuseStep 805583 = 1208375) B1208375
theorem B2575091 : Blo 535802 2575091 := bstep (se 1 (by rfl) ⟨1931318, by rfl⟩ : syracuseStep 2575091 = 3862637) B3862637
theorem B805769 : Blo 535802 805769 := bstep (se 2 (by rfl) ⟨302163, by rfl⟩ : syracuseStep 805769 = 604327) B604327
theorem B9063419 : Blo 535802 9063419 := bstep (se 1 (by rfl) ⟨6797564, by rfl⟩ : syracuseStep 9063419 = 13595129) B13595129
theorem B904297 : Blo 535802 904297 := bstep (se 2 (by rfl) ⟨339111, by rfl⟩ : syracuseStep 904297 = 678223) B678223
theorem B1526971 : Blo 535802 1526971 := bstep (se 1 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 1526971 = 2290457) B2290457
theorem B11619737 : Blo 535802 11619737 := bstep (se 2 (by rfl) ⟨4357401, by rfl⟩ : syracuseStep 11619737 = 8714803) B8714803
theorem B806303 : Blo 535802 806303 := bstep (se 1 (by rfl) ⟨604727, by rfl⟩ : syracuseStep 806303 = 1209455) B1209455
theorem B11161019 : Blo 535802 11161019 := bstep (se 1 (by rfl) ⟨8370764, by rfl⟩ : syracuseStep 11161019 = 16741529) B16741529
theorem B6639209 : Blo 535802 6639209 := bstep (se 2 (by rfl) ⟨2489703, by rfl⟩ : syracuseStep 6639209 = 4979407) B4979407
theorem B5296103 : Blo 535802 5296103 := bstep (se 1 (by rfl) ⟨3972077, by rfl⟩ : syracuseStep 5296103 = 7944155) B7944155
theorem B1363999 : Blo 535802 1363999 := bstep (se 1 (by rfl) ⟨1022999, by rfl⟩ : syracuseStep 1363999 = 2045999) B2045999
theorem B807119 : Blo 535802 807119 := bstep (se 1 (by rfl) ⟨605339, by rfl⟩ : syracuseStep 807119 = 1210679) B1210679
theorem B1364303 : Blo 535802 1364303 := bstep (se 1 (by rfl) ⟨1023227, by rfl⟩ : syracuseStep 1364303 = 2046455) B2046455
theorem B808859 : Blo 535802 808859 := bstep (se 1 (by rfl) ⟨606644, by rfl⟩ : syracuseStep 808859 = 1213289) B1213289
theorem B6871007 : Blo 535802 6871007 := bstep (se 1 (by rfl) ⟨5153255, by rfl⟩ : syracuseStep 6871007 = 10306511) B10306511
theorem B1366247 : Blo 535802 1366247 := bstep (se 1 (by rfl) ⟨1024685, by rfl⟩ : syracuseStep 1366247 = 2049371) B2049371
theorem B2185451 : Blo 535802 2185451 := bstep (se 1 (by rfl) ⟨1639088, by rfl⟩ : syracuseStep 2185451 = 3278177) B3278177
theorem B809513 : Blo 535802 809513 := bstep (se 2 (by rfl) ⟨303567, by rfl⟩ : syracuseStep 809513 = 607135) B607135
theorem B908779 : Blo 535802 908779 := bstep (se 1 (by rfl) ⟨681584, by rfl⟩ : syracuseStep 908779 = 1363169) B1363169
theorem B15523325 : Blo 535802 15523325 := bstep (se 3 (by rfl) ⟨2910623, by rfl⟩ : syracuseStep 15523325 = 5821247) B5821247
theorem B3071915 : Blo 535802 3071915 := bstep (se 1 (by rfl) ⟨2303936, by rfl⟩ : syracuseStep 3071915 = 4607873) B4607873
theorem B2908831 : Blo 535802 2908831 := bstep (se 1 (by rfl) ⟨2181623, by rfl⟩ : syracuseStep 2908831 = 4363247) B4363247
theorem B910217 : Blo 535802 910217 := bstep (se 2 (by rfl) ⟨341331, by rfl⟩ : syracuseStep 910217 = 682663) B682663
theorem B1533019 : Blo 535802 1533019 := bstep (se 1 (by rfl) ⟨1149764, by rfl⟩ : syracuseStep 1533019 = 2299529) B2299529
theorem B3225445829 : Blo 535802 3225445829 := bstep (se 4 (by rfl) ⟨302385546, by rfl⟩ : syracuseStep 3225445829 = 604771093) B604771093
theorem B34891397 : Blo 535802 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B1205999 : Blo 535802 1205999 := bstep (se 1 (by rfl) ⟨904499, by rfl⟩ : syracuseStep 1205999 = 1808999) B1808999
theorem B1206611 : Blo 535802 1206611 := bstep (se 1 (by rfl) ⟨904958, by rfl⟩ : syracuseStep 1206611 = 1809917) B1809917
theorem B1206683 : Blo 535802 1206683 := bstep (se 1 (by rfl) ⟨905012, by rfl⟩ : syracuseStep 1206683 = 1810025) B1810025
theorem B1534751 : Blo 535802 1534751 := bstep (se 1 (by rfl) ⟨1151063, by rfl⟩ : syracuseStep 1534751 = 2302127) B2302127
theorem B1207457 : Blo 535802 1207457 := bstep (se 2 (by rfl) ⟨452796, by rfl⟩ : syracuseStep 1207457 = 905593) B905593
theorem B1208015 : Blo 535802 1208015 := bstep (se 1 (by rfl) ⟨906011, by rfl⟩ : syracuseStep 1208015 = 1812023) B1812023
theorem B1535719 : Blo 535802 1535719 := bstep (se 1 (by rfl) ⟨1151789, by rfl⟩ : syracuseStep 1535719 = 2303579) B2303579
theorem B6221933 : Blo 535802 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B1208555 : Blo 535802 1208555 := bstep (se 1 (by rfl) ⟨906416, by rfl⟩ : syracuseStep 1208555 = 1812833) B1812833
theorem B1208879 : Blo 535802 1208879 := bstep (se 1 (by rfl) ⟨906659, by rfl⟩ : syracuseStep 1208879 = 1813319) B1813319
theorem B6517381 : Blo 535802 6517381 := bstep (se 4 (by rfl) ⟨611004, by rfl⟩ : syracuseStep 6517381 = 1222009) B1222009
theorem B1209257 : Blo 535802 1209257 := bstep (se 2 (by rfl) ⟨453471, by rfl⟩ : syracuseStep 1209257 = 906943) B906943
theorem B1537051 : Blo 535802 1537051 := bstep (se 1 (by rfl) ⟨1152788, by rfl⟩ : syracuseStep 1537051 = 2305577) B2305577
theorem B1211327 : Blo 535802 1211327 := bstep (se 1 (by rfl) ⟨908495, by rfl⟩ : syracuseStep 1211327 = 1816991) B1816991
theorem B982343 : Blo 535802 982343 := bstep (se 1 (by rfl) ⟨736757, by rfl⟩ : syracuseStep 982343 = 1473515) B1473515
theorem B5177519 : Blo 535802 5177519 := bstep (se 1 (by rfl) ⟨3883139, by rfl⟩ : syracuseStep 5177519 = 7766279) B7766279
theorem B47055595 : Blo 535802 47055595 := bstep (se 1 (by rfl) ⟨35291696, by rfl⟩ : syracuseStep 47055595 = 70583393) B70583393
theorem B2294831 : Blo 535802 2294831 := bstep (se 1 (by rfl) ⟨1721123, by rfl⟩ : syracuseStep 2294831 = 3442247) B3442247
theorem B1311815 : Blo 535802 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B1214135 : Blo 535802 1214135 := bstep (se 1 (by rfl) ⟨910601, by rfl⟩ : syracuseStep 1214135 = 1821203) B1821203
theorem B7440679 : Blo 535802 7440679 := bstep (se 1 (by rfl) ⟨5580509, by rfl⟩ : syracuseStep 7440679 = 11161019) B11161019
theorem B4426139 : Blo 535802 4426139 := bstep (se 1 (by rfl) ⟨3319604, by rfl⟩ : syracuseStep 4426139 = 6639209) B6639209
theorem B2034503 : Blo 535802 2034503 := bstep (se 1 (by rfl) ⟨1525877, by rfl⟩ : syracuseStep 2034503 = 3051755) B3051755
theorem B2035475 : Blo 535802 2035475 := bstep (se 1 (by rfl) ⟨1526606, by rfl⟩ : syracuseStep 2035475 = 3053213) B3053213
theorem B2035961 : Blo 535802 2035961 := bstep (se 2 (by rfl) ⟨763485, by rfl⟩ : syracuseStep 2035961 = 1526971) B1526971
theorem B2037919 : Blo 535802 2037919 := bstep (se 1 (by rfl) ⟨1528439, by rfl⟩ : syracuseStep 2037919 = 3056879) B3056879
theorem B8689841 : Blo 535802 8689841 := bstep (se 2 (by rfl) ⟨3258690, by rfl⟩ : syracuseStep 8689841 = 6517381) B6517381
theorem B8362777 : Blo 535802 8362777 := bstep (se 2 (by rfl) ⟨3136041, by rfl⟩ : syracuseStep 8362777 = 6272083) B6272083
theorem B1383307 : Blo 535802 1383307 := bstep (se 1 (by rfl) ⟨1037480, by rfl⟩ : syracuseStep 1383307 = 2074961) B2074961
theorem B3742699 : Blo 535802 3742699 := bstep (se 1 (by rfl) ⟨2807024, by rfl⟩ : syracuseStep 3742699 = 5614049) B5614049
theorem B1023167 : Blo 535802 1023167 := bstep (se 1 (by rfl) ⟨767375, by rfl⟩ : syracuseStep 1023167 = 1534751) B1534751
theorem B2727593 : Blo 535802 2727593 := bstep (se 2 (by rfl) ⟨1022847, by rfl⟩ : syracuseStep 2727593 = 2045695) B2045695
theorem B6103187 : Blo 535802 6103187 := bstep (se 1 (by rfl) ⟨4577390, by rfl⟩ : syracuseStep 6103187 = 9154781) B9154781
theorem B1450219 : Blo 535802 1450219 := bstep (se 1 (by rfl) ⟨1087664, by rfl⟩ : syracuseStep 1450219 = 2175329) B2175329
theorem B2040167 : Blo 535802 2040167 := bstep (se 1 (by rfl) ⟨1530125, by rfl⟩ : syracuseStep 2040167 = 3060251) B3060251
theorem B5251625 : Blo 535802 5251625 := bstep (se 2 (by rfl) ⟨1969359, by rfl⟩ : syracuseStep 5251625 = 3938719) B3938719
theorem B1813211 : Blo 535802 1813211 := bstep (se 1 (by rfl) ⟨1359908, by rfl⟩ : syracuseStep 1813211 = 2719817) B2719817
theorem B3451805 : Blo 535802 3451805 := bstep (se 3 (by rfl) ⟨647213, by rfl⟩ : syracuseStep 3451805 = 1294427) B1294427
theorem B3058793 : Blo 535802 3058793 := bstep (se 2 (by rfl) ⟨1147047, by rfl⟩ : syracuseStep 3058793 = 2294095) B2294095
theorem B536047 : Blo 535802 536047 := bstep (se 1 (by rfl) ⟨402035, by rfl⟩ : syracuseStep 536047 = 804071) B804071
theorem B3878441 : Blo 535802 3878441 := bstep (se 2 (by rfl) ⟨1454415, by rfl⟩ : syracuseStep 3878441 = 2908831) B2908831
theorem B536479 : Blo 535802 536479 := bstep (se 1 (by rfl) ⟨402359, by rfl⟩ : syracuseStep 536479 = 804719) B804719
theorem B536603 : Blo 535802 536603 := bstep (se 1 (by rfl) ⟨402452, by rfl⟩ : syracuseStep 536603 = 804905) B804905
theorem B2044025 : Blo 535802 2044025 := bstep (se 2 (by rfl) ⟨766509, by rfl⟩ : syracuseStep 2044025 = 1533019) B1533019
theorem B537055 : Blo 535802 537055 := bstep (se 1 (by rfl) ⟨402791, by rfl⟩ : syracuseStep 537055 = 805583) B805583
theorem B1716727 : Blo 535802 1716727 := bstep (se 1 (by rfl) ⟨1287545, by rfl⟩ : syracuseStep 1716727 = 2575091) B2575091
theorem B537179 : Blo 535802 537179 := bstep (se 1 (by rfl) ⟨402884, by rfl⟩ : syracuseStep 537179 = 805769) B805769
theorem B5812985 : Blo 535802 5812985 := bstep (se 2 (by rfl) ⟨2179869, by rfl⟩ : syracuseStep 5812985 = 4359739) B4359739
theorem B17412893 : Blo 535802 17412893 := bstep (se 3 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 17412893 = 6529835) B6529835
theorem B7746491 : Blo 535802 7746491 := bstep (se 1 (by rfl) ⟨5809868, by rfl⟩ : syracuseStep 7746491 = 11619737) B11619737
theorem B537535 : Blo 535802 537535 := bstep (se 1 (by rfl) ⟨403151, by rfl⟩ : syracuseStep 537535 = 806303) B806303
theorem B3454163 : Blo 535802 3454163 := bstep (se 1 (by rfl) ⟨2590622, by rfl⟩ : syracuseStep 3454163 = 5181245) B5181245
theorem B1815911 : Blo 535802 1815911 := bstep (se 1 (by rfl) ⟨1361933, by rfl⟩ : syracuseStep 1815911 = 2723867) B2723867
theorem B538079 : Blo 535802 538079 := bstep (se 1 (by rfl) ⟨403559, by rfl⟩ : syracuseStep 538079 = 807119) B807119
theorem B13121453 : Blo 535802 13121453 := bstep (se 3 (by rfl) ⟨2460272, by rfl⟩ : syracuseStep 13121453 = 4920545) B4920545
theorem B768047 : Blo 535802 768047 := bstep (se 1 (by rfl) ⟨576035, by rfl⟩ : syracuseStep 768047 = 1152071) B1152071
theorem B1751375 : Blo 535802 1751375 := bstep (se 1 (by rfl) ⟨1313531, by rfl⟩ : syracuseStep 1751375 = 2627063) B2627063
theorem B4078025 : Blo 535802 4078025 := bstep (se 2 (by rfl) ⟨1529259, by rfl⟩ : syracuseStep 4078025 = 3058519) B3058519
theorem B539239 : Blo 535802 539239 := bstep (se 1 (by rfl) ⟨404429, by rfl⟩ : syracuseStep 539239 = 808859) B808859
theorem B1358633 : Blo 535802 1358633 := bstep (se 2 (by rfl) ⟨509487, by rfl⟩ : syracuseStep 1358633 = 1018975) B1018975
theorem B1456967 : Blo 535802 1456967 := bstep (se 1 (by rfl) ⟨1092725, by rfl⟩ : syracuseStep 1456967 = 2185451) B2185451
theorem B1719137 : Blo 535802 1719137 := bstep (se 2 (by rfl) ⟨644676, by rfl⟩ : syracuseStep 1719137 = 1289353) B1289353
theorem B539675 : Blo 535802 539675 := bstep (se 1 (by rfl) ⟨404756, by rfl⟩ : syracuseStep 539675 = 809513) B809513
theorem B7847047 : Blo 535802 7847047 := bstep (se 1 (by rfl) ⟨5885285, by rfl⟩ : syracuseStep 7847047 = 11770571) B11770571
theorem B2047625 : Blo 535802 2047625 := bstep (se 2 (by rfl) ⟨767859, by rfl⟩ : syracuseStep 2047625 = 1535719) B1535719
theorem B1818287 : Blo 535802 1818287 := bstep (se 1 (by rfl) ⟨1363715, by rfl⟩ : syracuseStep 1818287 = 2727431) B2727431
theorem B1294235 : Blo 535802 1294235 := bstep (se 1 (by rfl) ⟨970676, by rfl⟩ : syracuseStep 1294235 = 1941353) B1941353
theorem B2047943 : Blo 535802 2047943 := bstep (se 1 (by rfl) ⟨1535957, by rfl⟩ : syracuseStep 2047943 = 3071915) B3071915
theorem B1818665 : Blo 535802 1818665 := bstep (se 2 (by rfl) ⟨681999, by rfl⟩ : syracuseStep 1818665 = 1363999) B1363999
theorem B6209833 : Blo 535802 6209833 := bstep (se 2 (by rfl) ⟨2328687, by rfl⟩ : syracuseStep 6209833 = 4657375) B4657375
theorem B1818935 : Blo 535802 1818935 := bstep (se 1 (by rfl) ⟨1364201, by rfl⟩ : syracuseStep 1818935 = 2728403) B2728403
theorem B9159155 : Blo 535802 9159155 := bstep (se 1 (by rfl) ⟨6869366, by rfl⟩ : syracuseStep 9159155 = 13738733) B13738733
theorem B606811 : Blo 535802 606811 := bstep (se 1 (by rfl) ⟨455108, by rfl⟩ : syracuseStep 606811 = 910217) B910217
theorem B3457853 : Blo 535802 3457853 := bstep (se 3 (by rfl) ⟨648347, by rfl⟩ : syracuseStep 3457853 = 1296695) B1296695
theorem B803999 : Blo 535802 803999 := bstep (se 1 (by rfl) ⟨602999, by rfl⟩ : syracuseStep 803999 = 1205999) B1205999
theorem B1361063 : Blo 535802 1361063 := bstep (se 1 (by rfl) ⟨1020797, by rfl⟩ : syracuseStep 1361063 = 2041595) B2041595
theorem B2049401 : Blo 535802 2049401 := bstep (se 2 (by rfl) ⟨768525, by rfl⟩ : syracuseStep 2049401 = 1537051) B1537051
theorem B804407 : Blo 535802 804407 := bstep (se 1 (by rfl) ⟨603305, by rfl⟩ : syracuseStep 804407 = 1206611) B1206611
theorem B804455 : Blo 535802 804455 := bstep (se 1 (by rfl) ⟨603341, by rfl⟩ : syracuseStep 804455 = 1206683) B1206683
theorem B7358161 : Blo 535802 7358161 := bstep (se 2 (by rfl) ⟨2759310, by rfl⟩ : syracuseStep 7358161 = 5518621) B5518621
theorem B804971 : Blo 535802 804971 := bstep (se 1 (by rfl) ⟨603728, by rfl⟩ : syracuseStep 804971 = 1207457) B1207457
theorem B8276201 : Blo 535802 8276201 := bstep (se 2 (by rfl) ⟨3103575, by rfl⟩ : syracuseStep 8276201 = 6207151) B6207151
theorem B805343 : Blo 535802 805343 := bstep (se 1 (by rfl) ⟨604007, by rfl⟩ : syracuseStep 805343 = 1208015) B1208015
theorem B24169117 : Blo 535802 24169117 := bstep (se 3 (by rfl) ⟨4531709, by rfl⟩ : syracuseStep 24169117 = 9063419) B9063419
theorem B4147955 : Blo 535802 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B805703 : Blo 535802 805703 := bstep (se 1 (by rfl) ⟨604277, by rfl⟩ : syracuseStep 805703 = 1208555) B1208555
theorem B805919 : Blo 535802 805919 := bstep (se 1 (by rfl) ⟨604439, by rfl⟩ : syracuseStep 805919 = 1208879) B1208879
theorem B806171 : Blo 535802 806171 := bstep (se 1 (by rfl) ⟨604628, by rfl⟩ : syracuseStep 806171 = 1209257) B1209257
theorem B905627 : Blo 535802 905627 := bstep (se 1 (by rfl) ⟨679220, by rfl⟩ : syracuseStep 905627 = 1358441) B1358441
theorem B807551 : Blo 535802 807551 := bstep (se 1 (by rfl) ⟨605663, by rfl⟩ : syracuseStep 807551 = 1211327) B1211327
theorem B3069251 : Blo 535802 3069251 := bstep (se 1 (by rfl) ⟨2301938, by rfl⟩ : syracuseStep 3069251 = 4603877) B4603877
theorem B808313 : Blo 535802 808313 := bstep (se 2 (by rfl) ⟨303117, by rfl⟩ : syracuseStep 808313 = 606235) B606235
theorem B906815 : Blo 535802 906815 := bstep (se 1 (by rfl) ⟨680111, by rfl⟩ : syracuseStep 906815 = 1360223) B1360223
theorem B907355 : Blo 535802 907355 := bstep (se 1 (by rfl) ⟨680516, by rfl⟩ : syracuseStep 907355 = 1361033) B1361033
theorem B809279 : Blo 535802 809279 := bstep (se 1 (by rfl) ⟨606959, by rfl⟩ : syracuseStep 809279 = 1213919) B1213919
theorem B3070457 : Blo 535802 3070457 := bstep (se 2 (by rfl) ⟨1151421, by rfl⟩ : syracuseStep 3070457 = 2302843) B2302843
theorem B1727543 : Blo 535802 1727543 := bstep (se 1 (by rfl) ⟨1295657, by rfl⟩ : syracuseStep 1727543 = 2591315) B2591315
theorem B2186651 : Blo 535802 2186651 := bstep (se 1 (by rfl) ⟨1639988, by rfl⟩ : syracuseStep 2186651 = 3279977) B3279977
theorem B3530735 : Blo 535802 3530735 := bstep (se 1 (by rfl) ⟨2648051, by rfl⟩ : syracuseStep 3530735 = 5296103) B5296103
theorem B909535 : Blo 535802 909535 := bstep (se 1 (by rfl) ⟨682151, by rfl⟩ : syracuseStep 909535 = 1364303) B1364303
theorem B1532495 : Blo 535802 1532495 := bstep (se 1 (by rfl) ⟨1149371, by rfl⟩ : syracuseStep 1532495 = 2298743) B2298743
theorem B4580671 : Blo 535802 4580671 := bstep (se 1 (by rfl) ⟨3435503, by rfl⟩ : syracuseStep 4580671 = 6871007) B6871007
theorem B1205729 : Blo 535802 1205729 := bstep (se 2 (by rfl) ⟨452148, by rfl⟩ : syracuseStep 1205729 = 904297) B904297
theorem B910831 : Blo 535802 910831 := bstep (se 1 (by rfl) ⟨683123, by rfl⟩ : syracuseStep 910831 = 1366247) B1366247
theorem B107865893 : Blo 535802 107865893 := bstep (se 4 (by rfl) ⟨10112427, by rfl⟩ : syracuseStep 107865893 = 20224855) B20224855
theorem B10348883 : Blo 535802 10348883 := bstep (se 1 (by rfl) ⟨7761662, by rfl⟩ : syracuseStep 10348883 = 15523325) B15523325
theorem B4417907 : Blo 535802 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B682607 : Blo 535802 682607 := bstep (se 1 (by rfl) ⟨511955, by rfl⟩ : syracuseStep 682607 = 1023911) B1023911
theorem B1207835 : Blo 535802 1207835 := bstep (se 1 (by rfl) ⟨905876, by rfl⟩ : syracuseStep 1207835 = 1811753) B1811753
theorem B2150297219 : Blo 535802 2150297219 := bstep (se 1 (by rfl) ⟨1612722914, by rfl⟩ : syracuseStep 2150297219 = 3225445829) B3225445829
theorem B23260931 : Blo 535802 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B13791221 : Blo 535802 13791221 := bstep (se 5 (by rfl) ⟨646463, by rfl⟩ : syracuseStep 13791221 = 1292927) B1292927
theorem B1208735 : Blo 535802 1208735 := bstep (se 1 (by rfl) ⟨906551, by rfl⟩ : syracuseStep 1208735 = 1813103) B1813103
theorem B13988963 : Blo 535802 13988963 := bstep (se 1 (by rfl) ⟨10491722, by rfl⟩ : syracuseStep 13988963 = 20983445) B20983445
theorem B1209887 : Blo 535802 1209887 := bstep (se 1 (by rfl) ⟨907415, by rfl⟩ : syracuseStep 1209887 = 1814831) B1814831
theorem B1145639 : Blo 535802 1145639 := bstep (se 1 (by rfl) ⟨859229, by rfl⟩ : syracuseStep 1145639 = 1718459) B1718459
theorem B4095035 : Blo 535802 4095035 := bstep (se 1 (by rfl) ⟨3071276, by rfl⟩ : syracuseStep 4095035 = 6142553) B6142553
theorem B1932587 : Blo 535802 1932587 := bstep (se 1 (by rfl) ⟨1449440, by rfl⟩ : syracuseStep 1932587 = 2898881) B2898881
theorem B1211705 : Blo 535802 1211705 := bstep (se 2 (by rfl) ⟨454389, by rfl⟩ : syracuseStep 1211705 = 908779) B908779
theorem B654895 : Blo 535802 654895 := bstep (se 1 (by rfl) ⟨491171, by rfl⟩ : syracuseStep 654895 = 982343) B982343
theorem B1212407 : Blo 535802 1212407 := bstep (se 1 (by rfl) ⟨909305, by rfl⟩ : syracuseStep 1212407 = 1818611) B1818611
theorem B1212443 : Blo 535802 1212443 := bstep (se 1 (by rfl) ⟨909332, by rfl⟩ : syracuseStep 1212443 = 1818665) B1818665
theorem B1212623 : Blo 535802 1212623 := bstep (se 1 (by rfl) ⟨909467, by rfl⟩ : syracuseStep 1212623 = 1818935) B1818935
theorem B1212713 : Blo 535802 1212713 := bstep (se 2 (by rfl) ⟨454767, by rfl⟩ : syracuseStep 1212713 = 909535) B909535
theorem B1933625 : Blo 535802 1933625 := bstep (se 2 (by rfl) ⟨725109, by rfl⟩ : syracuseStep 1933625 = 1450219) B1450219
theorem B39683621 : Blo 535802 39683621 := bstep (se 4 (by rfl) ⟨3720339, by rfl⟩ : syracuseStep 39683621 = 7440679) B7440679
theorem B2950759 : Blo 535802 2950759 := bstep (se 1 (by rfl) ⟨2213069, by rfl⟩ : syracuseStep 2950759 = 4426139) B4426139
theorem B1214441 : Blo 535802 1214441 := bstep (se 2 (by rfl) ⟨455415, by rfl⟩ : syracuseStep 1214441 = 910831) B910831
theorem B1151695 : Blo 535802 1151695 := bstep (se 1 (by rfl) ⟨863771, by rfl⟩ : syracuseStep 1151695 = 1727543) B1727543
theorem B7377637 : Blo 535802 7377637 := bstep (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) B1383307
theorem B4068791 : Blo 535802 4068791 := bstep (se 1 (by rfl) ⟨3051593, by rfl⟩ : syracuseStep 4068791 = 6103187) B6103187
theorem B1021663 : Blo 535802 1021663 := bstep (se 1 (by rfl) ⟨766247, by rfl⟩ : syracuseStep 1021663 = 1532495) B1532495
theorem B2301203 : Blo 535802 2301203 := bstep (se 1 (by rfl) ⟨1725902, by rfl⟩ : syracuseStep 2301203 = 3451805) B3451805
theorem B2039195 : Blo 535802 2039195 := bstep (se 1 (by rfl) ⟨1529396, by rfl⟩ : syracuseStep 2039195 = 3058793) B3058793
theorem B15507287 : Blo 535802 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B3875323 : Blo 535802 3875323 := bstep (se 1 (by rfl) ⟨2906492, by rfl⟩ : syracuseStep 3875323 = 5812985) B5812985
theorem B11608595 : Blo 535802 11608595 := bstep (se 1 (by rfl) ⟨8706446, by rfl⟩ : syracuseStep 11608595 = 17412893) B17412893
theorem B2302775 : Blo 535802 2302775 := bstep (se 1 (by rfl) ⟨1727081, by rfl⟩ : syracuseStep 2302775 = 3454163) B3454163
theorem B11150369 : Blo 535802 11150369 := bstep (se 2 (by rfl) ⟨4181388, by rfl⟩ : syracuseStep 11150369 = 8362777) B8362777
theorem B4990265 : Blo 535802 4990265 := bstep (se 2 (by rfl) ⟨1871349, by rfl⟩ : syracuseStep 4990265 = 3742699) B3742699
theorem B10462729 : Blo 535802 10462729 := bstep (se 2 (by rfl) ⟨3923523, by rfl⟩ : syracuseStep 10462729 = 7847047) B7847047
theorem B763759 : Blo 535802 763759 := bstep (se 1 (by rfl) ⟨572819, by rfl⟩ : syracuseStep 763759 = 1145639) B1145639
theorem B2730023 : Blo 535802 2730023 := bstep (se 1 (by rfl) ⟨2047517, by rfl⟩ : syracuseStep 2730023 = 4095035) B4095035
theorem B1288391 : Blo 535802 1288391 := bstep (se 1 (by rfl) ⟨966293, by rfl⟩ : syracuseStep 1288391 = 1932587) B1932587
theorem B862823 : Blo 535802 862823 := bstep (se 1 (by rfl) ⟨647117, by rfl⟩ : syracuseStep 862823 = 1294235) B1294235
theorem B3451679 : Blo 535802 3451679 := bstep (se 1 (by rfl) ⟨2588759, by rfl⟩ : syracuseStep 3451679 = 5177519) B5177519
theorem B6106103 : Blo 535802 6106103 := bstep (se 1 (by rfl) ⟨4579577, by rfl⟩ : syracuseStep 6106103 = 9159155) B9159155
theorem B2305235 : Blo 535802 2305235 := bstep (se 1 (by rfl) ⟨1728926, by rfl⟩ : syracuseStep 2305235 = 3457853) B3457853
theorem B535999 : Blo 535802 535999 := bstep (se 1 (by rfl) ⟨401999, by rfl⟩ : syracuseStep 535999 = 803999) B803999
theorem B536271 : Blo 535802 536271 := bstep (se 1 (by rfl) ⟨402203, by rfl⟩ : syracuseStep 536271 = 804407) B804407
theorem B536303 : Blo 535802 536303 := bstep (se 1 (by rfl) ⟨402227, by rfl⟩ : syracuseStep 536303 = 804455) B804455
theorem B536647 : Blo 535802 536647 := bstep (se 1 (by rfl) ⟨402485, by rfl⟩ : syracuseStep 536647 = 804971) B804971
theorem B5517467 : Blo 535802 5517467 := bstep (se 1 (by rfl) ⟨4138100, by rfl⟩ : syracuseStep 5517467 = 8276201) B8276201
theorem B536895 : Blo 535802 536895 := bstep (se 1 (by rfl) ⟨402671, by rfl⟩ : syracuseStep 536895 = 805343) B805343
theorem B6107561 : Blo 535802 6107561 := bstep (se 2 (by rfl) ⟨2290335, by rfl⟩ : syracuseStep 6107561 = 4580671) B4580671
theorem B2765303 : Blo 535802 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B1356335 : Blo 535802 1356335 := bstep (se 1 (by rfl) ⟨1017251, by rfl⟩ : syracuseStep 1356335 = 2034503) B2034503
theorem B537135 : Blo 535802 537135 := bstep (se 1 (by rfl) ⟨402851, by rfl⟩ : syracuseStep 537135 = 805703) B805703
theorem B537279 : Blo 535802 537279 := bstep (se 1 (by rfl) ⟨402959, by rfl⟩ : syracuseStep 537279 = 805919) B805919
theorem B537447 : Blo 535802 537447 := bstep (se 1 (by rfl) ⟨403085, by rfl⟩ : syracuseStep 537447 = 806171) B806171
theorem B9810881 : Blo 535802 9810881 := bstep (se 2 (by rfl) ⟨3679080, by rfl⟩ : syracuseStep 9810881 = 7358161) B7358161
theorem B1356983 : Blo 535802 1356983 := bstep (se 1 (by rfl) ⟨1017737, by rfl⟩ : syracuseStep 1356983 = 2035475) B2035475
theorem B1357307 : Blo 535802 1357307 := bstep (se 1 (by rfl) ⟨1017980, by rfl⟩ : syracuseStep 1357307 = 2035961) B2035961
theorem B37303901 : Blo 535802 37303901 := bstep (se 3 (by rfl) ⟨6994481, by rfl⟩ : syracuseStep 37303901 = 13988963) B13988963
theorem B603751 : Blo 535802 603751 := bstep (se 1 (by rfl) ⟨452813, by rfl⟩ : syracuseStep 603751 = 905627) B905627
theorem B538367 : Blo 535802 538367 := bstep (se 1 (by rfl) ⟨403775, by rfl⟩ : syracuseStep 538367 = 807551) B807551
theorem B32225489 : Blo 535802 32225489 := bstep (se 2 (by rfl) ⟨12084558, by rfl⟩ : syracuseStep 32225489 = 24169117) B24169117
theorem B2046167 : Blo 535802 2046167 := bstep (se 1 (by rfl) ⟨1534625, by rfl⟩ : syracuseStep 2046167 = 3069251) B3069251
theorem B538875 : Blo 535802 538875 := bstep (se 1 (by rfl) ⟨404156, by rfl⟩ : syracuseStep 538875 = 808313) B808313
theorem B604543 : Blo 535802 604543 := bstep (se 1 (by rfl) ⟨453407, by rfl⟩ : syracuseStep 604543 = 906815) B906815
theorem B604903 : Blo 535802 604903 := bstep (se 1 (by rfl) ⟨453677, by rfl⟩ : syracuseStep 604903 = 907355) B907355
theorem B539519 : Blo 535802 539519 := bstep (se 1 (by rfl) ⟨404639, by rfl⟩ : syracuseStep 539519 = 809279) B809279
theorem B2046971 : Blo 535802 2046971 := bstep (se 1 (by rfl) ⟨1535228, by rfl⟩ : syracuseStep 2046971 = 3070457) B3070457
theorem B1457767 : Blo 535802 1457767 := bstep (se 1 (by rfl) ⟨1093325, by rfl⟩ : syracuseStep 1457767 = 2186651) B2186651
theorem B1818395 : Blo 535802 1818395 := bstep (se 1 (by rfl) ⟨1363796, by rfl⟩ : syracuseStep 1818395 = 2727593) B2727593
theorem B2048125 : Blo 535802 2048125 := bstep (se 3 (by rfl) ⟨384023, by rfl⟩ : syracuseStep 2048125 = 768047) B768047
theorem B1360111 : Blo 535802 1360111 := bstep (se 1 (by rfl) ⟨1020083, by rfl⟩ : syracuseStep 1360111 = 2040167) B2040167
theorem B11781085 : Blo 535802 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B803819 : Blo 535802 803819 := bstep (se 1 (by rfl) ⟨602864, by rfl⟩ : syracuseStep 803819 = 1205729) B1205729
theorem B71910595 : Blo 535802 71910595 := bstep (se 1 (by rfl) ⟨53932946, by rfl⟩ : syracuseStep 71910595 = 107865893) B107865893
theorem B6899255 : Blo 535802 6899255 := bstep (se 1 (by rfl) ⟨5174441, by rfl⟩ : syracuseStep 6899255 = 10348883) B10348883
theorem B1820285 : Blo 535802 1820285 := bstep (se 3 (by rfl) ⟨341303, by rfl⟩ : syracuseStep 1820285 = 682607) B682607
theorem B805223 : Blo 535802 805223 := bstep (se 1 (by rfl) ⟨603917, by rfl⟩ : syracuseStep 805223 = 1207835) B1207835
theorem B9194147 : Blo 535802 9194147 := bstep (se 1 (by rfl) ⟨6895610, by rfl⟩ : syracuseStep 9194147 = 13791221) B13791221
theorem B1362683 : Blo 535802 1362683 := bstep (se 1 (by rfl) ⟨1022012, by rfl⟩ : syracuseStep 1362683 = 2044025) B2044025
theorem B3492773 : Blo 535802 3492773 := bstep (se 4 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 3492773 = 654895) B654895
theorem B805823 : Blo 535802 805823 := bstep (se 1 (by rfl) ⟨604367, by rfl⟩ : syracuseStep 805823 = 1208735) B1208735
theorem B5164327 : Blo 535802 5164327 := bstep (se 1 (by rfl) ⟨3873245, by rfl⟩ : syracuseStep 5164327 = 7746491) B7746491
theorem B806591 : Blo 535802 806591 := bstep (se 1 (by rfl) ⟨604943, by rfl⟩ : syracuseStep 806591 = 1209887) B1209887
theorem B1167583 : Blo 535802 1167583 := bstep (se 1 (by rfl) ⟨875687, by rfl⟩ : syracuseStep 1167583 = 1751375) B1751375
theorem B5734125917 : Blo 535802 5734125917 := bstep (se 3 (by rfl) ⟨1075148609, by rfl⟩ : syracuseStep 5734125917 = 2150297219) B2150297219
theorem B905755 : Blo 535802 905755 := bstep (se 1 (by rfl) ⟨679316, by rfl⟩ : syracuseStep 905755 = 1358633) B1358633
theorem B971311 : Blo 535802 971311 := bstep (se 1 (by rfl) ⟨728483, by rfl⟩ : syracuseStep 971311 = 1456967) B1456967
theorem B807803 : Blo 535802 807803 := bstep (se 1 (by rfl) ⟨605852, by rfl⟩ : syracuseStep 807803 = 1211705) B1211705
theorem B1365083 : Blo 535802 1365083 := bstep (se 1 (by rfl) ⟨1023812, by rfl⟩ : syracuseStep 1365083 = 2047625) B2047625
theorem B1365295 : Blo 535802 1365295 := bstep (se 1 (by rfl) ⟨1023971, by rfl⟩ : syracuseStep 1365295 = 2047943) B2047943
theorem B808271 : Blo 535802 808271 := bstep (se 1 (by rfl) ⟨606203, by rfl⟩ : syracuseStep 808271 = 1212407) B1212407
theorem B8279777 : Blo 535802 8279777 := bstep (se 2 (by rfl) ⟨3104916, by rfl⟩ : syracuseStep 8279777 = 6209833) B6209833
theorem B1529887 : Blo 535802 1529887 := bstep (se 1 (by rfl) ⟨1147415, by rfl⟩ : syracuseStep 1529887 = 2294831) B2294831
theorem B907375 : Blo 535802 907375 := bstep (se 1 (by rfl) ⟨680531, by rfl⟩ : syracuseStep 907375 = 1361063) B1361063
theorem B809081 : Blo 535802 809081 := bstep (se 2 (by rfl) ⟨303405, by rfl⟩ : syracuseStep 809081 = 606811) B606811
theorem B1366267 : Blo 535802 1366267 := bstep (se 1 (by rfl) ⟨1024700, by rfl⟩ : syracuseStep 1366267 = 2049401) B2049401
theorem B62740793 : Blo 535802 62740793 := bstep (se 2 (by rfl) ⟨23527797, by rfl⟩ : syracuseStep 62740793 = 47055595) B47055595
theorem B809423 : Blo 535802 809423 := bstep (se 1 (by rfl) ⟨607067, by rfl⟩ : syracuseStep 809423 = 1214135) B1214135
theorem B3498173 : Blo 535802 3498173 := bstep (se 3 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 3498173 = 1311815) B1311815
theorem B5793227 : Blo 535802 5793227 := bstep (se 1 (by rfl) ⟨4344920, by rfl⟩ : syracuseStep 5793227 = 8689841) B8689841
theorem B682111 : Blo 535802 682111 := bstep (se 1 (by rfl) ⟨511583, by rfl⟩ : syracuseStep 682111 = 1023167) B1023167
theorem B2353823 : Blo 535802 2353823 := bstep (se 1 (by rfl) ⟨1765367, by rfl⟩ : syracuseStep 2353823 = 3530735) B3530735
theorem B3501083 : Blo 535802 3501083 := bstep (se 1 (by rfl) ⟨2625812, by rfl⟩ : syracuseStep 3501083 = 5251625) B5251625
theorem B2288969 : Blo 535802 2288969 := bstep (se 2 (by rfl) ⟨858363, by rfl⟩ : syracuseStep 2288969 = 1716727) B1716727
theorem B1208807 : Blo 535802 1208807 := bstep (se 1 (by rfl) ⟨906605, by rfl⟩ : syracuseStep 1208807 = 1813211) B1813211
theorem B2585627 : Blo 535802 2585627 := bstep (se 1 (by rfl) ⟨1939220, by rfl⟩ : syracuseStep 2585627 = 3878441) B3878441
theorem B2717225 : Blo 535802 2717225 := bstep (se 2 (by rfl) ⟨1018959, by rfl⟩ : syracuseStep 2717225 = 2037919) B2037919
theorem B1210607 : Blo 535802 1210607 := bstep (se 1 (by rfl) ⟨907955, by rfl⟩ : syracuseStep 1210607 = 1815911) B1815911
theorem B8747635 : Blo 535802 8747635 := bstep (se 1 (by rfl) ⟨6560726, by rfl⟩ : syracuseStep 8747635 = 13121453) B13121453
theorem B2718683 : Blo 535802 2718683 := bstep (se 1 (by rfl) ⟨2039012, by rfl⟩ : syracuseStep 2718683 = 4078025) B4078025
theorem B1146091 : Blo 535802 1146091 := bstep (se 1 (by rfl) ⟨859568, by rfl⟩ : syracuseStep 1146091 = 1719137) B1719137
theorem B1212191 : Blo 535802 1212191 := bstep (se 1 (by rfl) ⟨909143, by rfl⟩ : syracuseStep 1212191 = 1818287) B1818287
theorem B1213523 : Blo 535802 1213523 := bstep (se 1 (by rfl) ⟨910142, by rfl⟩ : syracuseStep 1213523 = 1820285) B1820285
theorem B6129431 : Blo 535802 6129431 := bstep (se 1 (by rfl) ⟨4597073, by rfl⟩ : syracuseStep 6129431 = 9194147) B9194147
theorem B2328515 : Blo 535802 2328515 := bstep (se 1 (by rfl) ⟨1746386, by rfl⟩ : syracuseStep 2328515 = 3492773) B3492773
theorem B3934345 : Blo 535802 3934345 := bstep (se 2 (by rfl) ⟨1475379, by rfl⟩ : syracuseStep 3934345 = 2950759) B2950759
theorem B1018345 : Blo 535802 1018345 := bstep (se 2 (by rfl) ⟨381879, by rfl⟩ : syracuseStep 1018345 = 763759) B763759
theorem B3822750611 : Blo 535802 3822750611 := bstep (se 1 (by rfl) ⟨2867062958, by rfl⟩ : syracuseStep 3822750611 = 5734125917) B5734125917
theorem B6885769 : Blo 535802 6885769 := bstep (se 2 (by rfl) ⟨2582163, by rfl⟩ : syracuseStep 6885769 = 5164327) B5164327
theorem B2332115 : Blo 535802 2332115 := bstep (se 1 (by rfl) ⟨1749086, by rfl⟩ : syracuseStep 2332115 = 3498173) B3498173
theorem B7739063 : Blo 535802 7739063 := bstep (se 1 (by rfl) ⟨5804297, by rfl⟩ : syracuseStep 7739063 = 11608595) B11608595
theorem B9836849 : Blo 535802 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B383523173 : Blo 535802 383523173 := bstep (se 4 (by rfl) ⟨35955297, by rfl⟩ : syracuseStep 383523173 = 71910595) B71910595
theorem B2300861 : Blo 535802 2300861 := bstep (se 3 (by rfl) ⟨431411, by rfl⟩ : syracuseStep 2300861 = 862823) B862823
theorem B2301119 : Blo 535802 2301119 := bstep (se 1 (by rfl) ⟨1725839, by rfl⟩ : syracuseStep 2301119 = 3451679) B3451679
theorem B4070735 : Blo 535802 4070735 := bstep (se 1 (by rfl) ⟨3053051, by rfl⟩ : syracuseStep 4070735 = 6106103) B6106103
theorem B2039849 : Blo 535802 2039849 := bstep (se 2 (by rfl) ⟨764943, by rfl⟩ : syracuseStep 2039849 = 1529887) B1529887
theorem B3678311 : Blo 535802 3678311 := bstep (se 1 (by rfl) ⟨2758733, by rfl⟩ : syracuseStep 3678311 = 5517467) B5517467
theorem B4071707 : Blo 535802 4071707 := bstep (se 1 (by rfl) ⟨3053780, by rfl⟩ : syracuseStep 4071707 = 6107561) B6107561
theorem B1843535 : Blo 535802 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B1811483 : Blo 535802 1811483 := bstep (se 1 (by rfl) ⟨1358612, by rfl⟩ : syracuseStep 1811483 = 2717225) B2717225
theorem B1812455 : Blo 535802 1812455 := bstep (se 1 (by rfl) ⟨1359341, by rfl⟩ : syracuseStep 1812455 = 2718683) B2718683
theorem B1943689 : Blo 535802 1943689 := bstep (se 2 (by rfl) ⟨728883, by rfl⟩ : syracuseStep 1943689 = 1457767) B1457767
theorem B2730833 : Blo 535802 2730833 := bstep (se 2 (by rfl) ⟨1024062, by rfl⟩ : syracuseStep 2730833 = 2048125) B2048125
theorem B1289083 : Blo 535802 1289083 := bstep (se 1 (by rfl) ⟨966812, by rfl⟩ : syracuseStep 1289083 = 1933625) B1933625
theorem B1813481 : Blo 535802 1813481 := bstep (se 2 (by rfl) ⟨680055, by rfl⟩ : syracuseStep 1813481 = 1360111) B1360111
theorem B535879 : Blo 535802 535879 := bstep (se 1 (by rfl) ⟨401909, by rfl⟩ : syracuseStep 535879 = 803819) B803819
theorem B26455747 : Blo 535802 26455747 := bstep (se 1 (by rfl) ⟨19841810, by rfl⟩ : syracuseStep 26455747 = 39683621) B39683621
theorem B4599503 : Blo 535802 4599503 := bstep (se 1 (by rfl) ⟨3449627, by rfl⟩ : syracuseStep 4599503 = 6899255) B6899255
theorem B15708113 : Blo 535802 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B536815 : Blo 535802 536815 := bstep (se 1 (by rfl) ⟨402611, by rfl⟩ : syracuseStep 536815 = 805223) B805223
theorem B537215 : Blo 535802 537215 := bstep (se 1 (by rfl) ⟨402911, by rfl⟩ : syracuseStep 537215 = 805823) B805823
theorem B537727 : Blo 535802 537727 := bstep (se 1 (by rfl) ⟨403295, by rfl⟩ : syracuseStep 537727 = 806591) B806591
theorem B538535 : Blo 535802 538535 := bstep (se 1 (by rfl) ⟨403901, by rfl⟩ : syracuseStep 538535 = 807803) B807803
theorem B538847 : Blo 535802 538847 := bstep (se 1 (by rfl) ⟨404135, by rfl⟩ : syracuseStep 538847 = 808271) B808271
theorem B539387 : Blo 535802 539387 := bstep (se 1 (by rfl) ⟨404540, by rfl⟩ : syracuseStep 539387 = 809081) B809081
theorem B41827195 : Blo 535802 41827195 := bstep (se 1 (by rfl) ⟨31370396, by rfl⟩ : syracuseStep 41827195 = 62740793) B62740793
theorem B539615 : Blo 535802 539615 := bstep (se 1 (by rfl) ⟨404711, by rfl⟩ : syracuseStep 539615 = 809423) B809423
theorem B1359463 : Blo 535802 1359463 := bstep (se 1 (by rfl) ⟨1019597, by rfl⟩ : syracuseStep 1359463 = 2039195) B2039195
theorem B10338191 : Blo 535802 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B1556777 : Blo 535802 1556777 := bstep (se 2 (by rfl) ⟨583791, by rfl⟩ : syracuseStep 1556777 = 1167583) B1167583
theorem B1295081 : Blo 535802 1295081 := bstep (se 2 (by rfl) ⟨485655, by rfl⟩ : syracuseStep 1295081 = 971311) B971311
theorem B3326843 : Blo 535802 3326843 := bstep (se 1 (by rfl) ⟨2495132, by rfl⟩ : syracuseStep 3326843 = 4990265) B4990265
theorem B1820015 : Blo 535802 1820015 := bstep (se 1 (by rfl) ⟨1365011, by rfl⟩ : syracuseStep 1820015 = 2730023) B2730023
theorem B1820393 : Blo 535802 1820393 := bstep (se 2 (by rfl) ⟨682647, by rfl⟩ : syracuseStep 1820393 = 1365295) B1365295
theorem B805001 : Blo 535802 805001 := bstep (se 2 (by rfl) ⟨301875, by rfl⟩ : syracuseStep 805001 = 603751) B603751
theorem B1525979 : Blo 535802 1525979 := bstep (se 1 (by rfl) ⟨1144484, by rfl⟩ : syracuseStep 1525979 = 2288969) B2288969
theorem B1362217 : Blo 535802 1362217 := bstep (se 2 (by rfl) ⟨510831, by rfl⟩ : syracuseStep 1362217 = 1021663) B1021663
theorem B805871 : Blo 535802 805871 := bstep (se 1 (by rfl) ⟨604403, by rfl⟩ : syracuseStep 805871 = 1208807) B1208807
theorem B1821689 : Blo 535802 1821689 := bstep (se 2 (by rfl) ⟨683133, by rfl⟩ : syracuseStep 1821689 = 1366267) B1366267
theorem B904223 : Blo 535802 904223 := bstep (se 1 (by rfl) ⟨678167, by rfl⟩ : syracuseStep 904223 = 1356335) B1356335
theorem B806057 : Blo 535802 806057 := bstep (se 2 (by rfl) ⟨302271, by rfl⟩ : syracuseStep 806057 = 604543) B604543
theorem B6540587 : Blo 535802 6540587 := bstep (se 1 (by rfl) ⟨4905440, by rfl⟩ : syracuseStep 6540587 = 9810881) B9810881
theorem B1723751 : Blo 535802 1723751 := bstep (se 1 (by rfl) ⟨1292813, by rfl⟩ : syracuseStep 1723751 = 2585627) B2585627
theorem B904655 : Blo 535802 904655 := bstep (se 1 (by rfl) ⟨678491, by rfl⟩ : syracuseStep 904655 = 1356983) B1356983
theorem B806537 : Blo 535802 806537 := bstep (se 2 (by rfl) ⟨302451, by rfl⟩ : syracuseStep 806537 = 604903) B604903
theorem B904871 : Blo 535802 904871 := bstep (se 1 (by rfl) ⟨678653, by rfl⟩ : syracuseStep 904871 = 1357307) B1357307
theorem B21483659 : Blo 535802 21483659 := bstep (se 1 (by rfl) ⟨16112744, by rfl⟩ : syracuseStep 21483659 = 32225489) B32225489
theorem B1364111 : Blo 535802 1364111 := bstep (se 1 (by rfl) ⟨1023083, by rfl⟩ : syracuseStep 1364111 = 2046167) B2046167
theorem B807071 : Blo 535802 807071 := bstep (se 1 (by rfl) ⟨605303, by rfl⟩ : syracuseStep 807071 = 1210607) B1210607
theorem B1528121 : Blo 535802 1528121 := bstep (se 2 (by rfl) ⟨573045, by rfl⟩ : syracuseStep 1528121 = 1146091) B1146091
theorem B1364647 : Blo 535802 1364647 := bstep (se 1 (by rfl) ⟨1023485, by rfl⟩ : syracuseStep 1364647 = 2046971) B2046971
theorem B808127 : Blo 535802 808127 := bstep (se 1 (by rfl) ⟨606095, by rfl⟩ : syracuseStep 808127 = 1212191) B1212191
theorem B808295 : Blo 535802 808295 := bstep (se 1 (by rfl) ⟨606221, by rfl⟩ : syracuseStep 808295 = 1212443) B1212443
theorem B808415 : Blo 535802 808415 := bstep (se 1 (by rfl) ⟨606311, by rfl⟩ : syracuseStep 808415 = 1212623) B1212623
theorem B808475 : Blo 535802 808475 := bstep (se 1 (by rfl) ⟨606356, by rfl⟩ : syracuseStep 808475 = 1212713) B1212713
theorem B5167097 : Blo 535802 5167097 := bstep (se 2 (by rfl) ⟨1937661, by rfl⟩ : syracuseStep 5167097 = 3875323) B3875323
theorem B809627 : Blo 535802 809627 := bstep (se 1 (by rfl) ⟨607220, by rfl⟩ : syracuseStep 809627 = 1214441) B1214441
theorem B908455 : Blo 535802 908455 := bstep (se 1 (by rfl) ⟨681341, by rfl⟩ : syracuseStep 908455 = 1362683) B1362683
theorem B13950305 : Blo 535802 13950305 := bstep (se 2 (by rfl) ⟨5231364, by rfl⟩ : syracuseStep 13950305 = 10462729) B10462729
theorem B909481 : Blo 535802 909481 := bstep (se 2 (by rfl) ⟨341055, by rfl⟩ : syracuseStep 909481 = 682111) B682111
theorem B910055 : Blo 535802 910055 := bstep (se 1 (by rfl) ⟨682541, by rfl⟩ : syracuseStep 910055 = 1365083) B1365083
theorem B2712527 : Blo 535802 2712527 := bstep (se 1 (by rfl) ⟨2034395, by rfl⟩ : syracuseStep 2712527 = 4068791) B4068791
theorem B22079405 : Blo 535802 22079405 := bstep (se 3 (by rfl) ⟨4139888, by rfl⟩ : syracuseStep 22079405 = 8279777) B8279777
theorem B1534135 : Blo 535802 1534135 := bstep (se 1 (by rfl) ⟨1150601, by rfl⟩ : syracuseStep 1534135 = 2301203) B2301203
theorem B3435709 : Blo 535802 3435709 := bstep (se 3 (by rfl) ⟨644195, by rfl⟩ : syracuseStep 3435709 = 1288391) B1288391
theorem B1535183 : Blo 535802 1535183 := bstep (se 1 (by rfl) ⟨1151387, by rfl⟩ : syracuseStep 1535183 = 2302775) B2302775
theorem B7433579 : Blo 535802 7433579 := bstep (se 1 (by rfl) ⟨5575184, by rfl⟩ : syracuseStep 7433579 = 11150369) B11150369
theorem B1207673 : Blo 535802 1207673 := bstep (se 2 (by rfl) ⟨452877, by rfl⟩ : syracuseStep 1207673 = 905755) B905755
theorem B1535593 : Blo 535802 1535593 := bstep (se 2 (by rfl) ⟨575847, by rfl⟩ : syracuseStep 1535593 = 1151695) B1151695
theorem B3862151 : Blo 535802 3862151 := bstep (se 1 (by rfl) ⟨2896613, by rfl⟩ : syracuseStep 3862151 = 5793227) B5793227
theorem B1569215 : Blo 535802 1569215 := bstep (se 1 (by rfl) ⟨1176911, by rfl⟩ : syracuseStep 1569215 = 2353823) B2353823
theorem B1536823 : Blo 535802 1536823 := bstep (se 1 (by rfl) ⟨1152617, by rfl⟩ : syracuseStep 1536823 = 2305235) B2305235
theorem B9336221 : Blo 535802 9336221 := bstep (se 3 (by rfl) ⟨1750541, by rfl⟩ : syracuseStep 9336221 = 3501083) B3501083
theorem B1209833 : Blo 535802 1209833 := bstep (se 2 (by rfl) ⟨453687, by rfl⟩ : syracuseStep 1209833 = 907375) B907375
theorem B11663513 : Blo 535802 11663513 := bstep (se 2 (by rfl) ⟨4373817, by rfl⟩ : syracuseStep 11663513 = 8747635) B8747635
theorem B24869267 : Blo 535802 24869267 := bstep (se 1 (by rfl) ⟨18651950, by rfl⟩ : syracuseStep 24869267 = 37303901) B37303901
theorem B1212263 : Blo 535802 1212263 := bstep (se 1 (by rfl) ⟨909197, by rfl⟩ : syracuseStep 1212263 = 1818395) B1818395
theorem B1212641 : Blo 535802 1212641 := bstep (se 2 (by rfl) ⟨454740, by rfl⟩ : syracuseStep 1212641 = 909481) B909481
theorem B1213343 : Blo 535802 1213343 := bstep (se 1 (by rfl) ⟨910007, by rfl⟩ : syracuseStep 1213343 = 1820015) B1820015
theorem B1213595 : Blo 535802 1213595 := bstep (se 1 (by rfl) ⟨910196, by rfl⟩ : syracuseStep 1213595 = 1820393) B1820393
theorem B2548500407 : Blo 535802 2548500407 := bstep (se 1 (by rfl) ⟨1911375305, by rfl⟩ : syracuseStep 2548500407 = 3822750611) B3822750611
theorem B1214459 : Blo 535802 1214459 := bstep (se 1 (by rfl) ⟨910844, by rfl⟩ : syracuseStep 1214459 = 1821689) B1821689
theorem B4360391 : Blo 535802 4360391 := bstep (se 1 (by rfl) ⟨3270293, by rfl⟩ : syracuseStep 4360391 = 6540587) B6540587
theorem B1149167 : Blo 535802 1149167 := bstep (se 1 (by rfl) ⟨861875, by rfl⟩ : syracuseStep 1149167 = 1723751) B1723751
theorem B14322439 : Blo 535802 14322439 := bstep (se 1 (by rfl) ⟨10741829, by rfl⟩ : syracuseStep 14322439 = 21483659) B21483659
theorem B5245793 : Blo 535802 5245793 := bstep (se 2 (by rfl) ⟨1967172, by rfl⟩ : syracuseStep 5245793 = 3934345) B3934345
theorem B2591585 : Blo 535802 2591585 := bstep (se 2 (by rfl) ⟨971844, by rfl⟩ : syracuseStep 2591585 = 1943689) B1943689
theorem B1018747 : Blo 535802 1018747 := bstep (se 1 (by rfl) ⟨764060, by rfl⟩ : syracuseStep 1018747 = 1528121) B1528121
theorem B3444731 : Blo 535802 3444731 := bstep (se 1 (by rfl) ⟨2583548, by rfl⟩ : syracuseStep 3444731 = 5167097) B5167097
theorem B9181025 : Blo 535802 9181025 := bstep (se 2 (by rfl) ⟨3442884, by rfl⟩ : syracuseStep 9181025 = 6885769) B6885769
theorem B4069277 : Blo 535802 4069277 := bstep (se 3 (by rfl) ⟨762989, by rfl⟩ : syracuseStep 4069277 = 1525979) B1525979
theorem B1808351 : Blo 535802 1808351 := bstep (se 1 (by rfl) ⟨1356263, by rfl⟩ : syracuseStep 1808351 = 2712527) B2712527
theorem B14719603 : Blo 535802 14719603 := bstep (se 1 (by rfl) ⟨11039702, by rfl⟩ : syracuseStep 14719603 = 22079405) B22079405
theorem B1023455 : Blo 535802 1023455 := bstep (se 1 (by rfl) ⟨767591, by rfl⟩ : syracuseStep 1023455 = 1535183) B1535183
theorem B7775675 : Blo 535802 7775675 := bstep (se 1 (by rfl) ⟨5831756, by rfl⟩ : syracuseStep 7775675 = 11663513) B11663513
theorem B1812617 : Blo 535802 1812617 := bstep (se 2 (by rfl) ⟨679731, by rfl⟩ : syracuseStep 1812617 = 1359463) B1359463
theorem B6892127 : Blo 535802 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B863387 : Blo 535802 863387 := bstep (se 1 (by rfl) ⟨647540, by rfl⟩ : syracuseStep 863387 = 1295081) B1295081
theorem B1552343 : Blo 535802 1552343 := bstep (se 1 (by rfl) ⟨1164257, by rfl⟩ : syracuseStep 1552343 = 2328515) B2328515
theorem B536667 : Blo 535802 536667 := bstep (se 1 (by rfl) ⟨402500, by rfl⟩ : syracuseStep 536667 = 805001) B805001
theorem B537247 : Blo 535802 537247 := bstep (se 1 (by rfl) ⟨402935, by rfl⟩ : syracuseStep 537247 = 805871) B805871
theorem B602815 : Blo 535802 602815 := bstep (se 1 (by rfl) ⟨452111, by rfl⟩ : syracuseStep 602815 = 904223) B904223
theorem B537371 : Blo 535802 537371 := bstep (se 1 (by rfl) ⟨403028, by rfl⟩ : syracuseStep 537371 = 806057) B806057
theorem B603103 : Blo 535802 603103 := bstep (se 1 (by rfl) ⟨452327, by rfl⟩ : syracuseStep 603103 = 904655) B904655
theorem B537691 : Blo 535802 537691 := bstep (se 1 (by rfl) ⟨403268, by rfl⟩ : syracuseStep 537691 = 806537) B806537
theorem B603247 : Blo 535802 603247 := bstep (se 1 (by rfl) ⟨452435, by rfl⟩ : syracuseStep 603247 = 904871) B904871
theorem B538047 : Blo 535802 538047 := bstep (se 1 (by rfl) ⟨403535, by rfl⟩ : syracuseStep 538047 = 807071) B807071
theorem B2045513 : Blo 535802 2045513 := bstep (se 2 (by rfl) ⟨767067, by rfl⟩ : syracuseStep 2045513 = 1534135) B1534135
theorem B1816289 : Blo 535802 1816289 := bstep (se 2 (by rfl) ⟨681108, by rfl⟩ : syracuseStep 1816289 = 1362217) B1362217
theorem B1357793 : Blo 535802 1357793 := bstep (se 2 (by rfl) ⟨509172, by rfl⟩ : syracuseStep 1357793 = 1018345) B1018345
theorem B538751 : Blo 535802 538751 := bstep (se 1 (by rfl) ⟨404063, by rfl⟩ : syracuseStep 538751 = 808127) B808127
theorem B538863 : Blo 535802 538863 := bstep (se 1 (by rfl) ⟨404147, by rfl⟩ : syracuseStep 538863 = 808295) B808295
theorem B1554743 : Blo 535802 1554743 := bstep (se 1 (by rfl) ⟨1166057, by rfl⟩ : syracuseStep 1554743 = 2332115) B2332115
theorem B538943 : Blo 535802 538943 := bstep (se 1 (by rfl) ⟨404207, by rfl⟩ : syracuseStep 538943 = 808415) B808415
theorem B538983 : Blo 535802 538983 := bstep (se 1 (by rfl) ⟨404237, by rfl⟩ : syracuseStep 538983 = 808475) B808475
theorem B5159375 : Blo 535802 5159375 := bstep (se 1 (by rfl) ⟨3869531, by rfl⟩ : syracuseStep 5159375 = 7739063) B7739063
theorem B1718777 : Blo 535802 1718777 := bstep (se 2 (by rfl) ⟨644541, by rfl⟩ : syracuseStep 1718777 = 1289083) B1289083
theorem B539751 : Blo 535802 539751 := bstep (se 1 (by rfl) ⟨404813, by rfl⟩ : syracuseStep 539751 = 809627) B809627
theorem B2047457 : Blo 535802 2047457 := bstep (se 2 (by rfl) ⟨767796, by rfl⟩ : syracuseStep 2047457 = 1535593) B1535593
theorem B35274329 : Blo 535802 35274329 := bstep (se 2 (by rfl) ⟨13227873, by rfl⟩ : syracuseStep 35274329 = 26455747) B26455747
theorem B1359899 : Blo 535802 1359899 := bstep (se 1 (by rfl) ⟨1019924, by rfl⟩ : syracuseStep 1359899 = 2039849) B2039849
theorem B1229023 : Blo 535802 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B606703 : Blo 535802 606703 := bstep (se 1 (by rfl) ⟨455027, by rfl⟩ : syracuseStep 606703 = 910055) B910055
theorem B26231597 : Blo 535802 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B1819529 : Blo 535802 1819529 := bstep (se 2 (by rfl) ⟨682323, by rfl⟩ : syracuseStep 1819529 = 1364647) B1364647
theorem B2049097 : Blo 535802 2049097 := bstep (se 2 (by rfl) ⟨768411, by rfl⟩ : syracuseStep 2049097 = 1536823) B1536823
theorem B1820555 : Blo 535802 1820555 := bstep (se 1 (by rfl) ⟨1365416, by rfl⟩ : syracuseStep 1820555 = 2730833) B2730833
theorem B805115 : Blo 535802 805115 := bstep (se 1 (by rfl) ⟨603836, by rfl⟩ : syracuseStep 805115 = 1207673) B1207673
theorem B2574767 : Blo 535802 2574767 := bstep (se 1 (by rfl) ⟨1931075, by rfl⟩ : syracuseStep 2574767 = 3862151) B3862151
theorem B3066335 : Blo 535802 3066335 := bstep (se 1 (by rfl) ⟨2299751, by rfl⟩ : syracuseStep 3066335 = 4599503) B4599503
theorem B10472075 : Blo 535802 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B806555 : Blo 535802 806555 := bstep (se 1 (by rfl) ⟨604916, by rfl⟩ : syracuseStep 806555 = 1209833) B1209833
theorem B808175 : Blo 535802 808175 := bstep (se 1 (by rfl) ⟨606131, by rfl⟩ : syracuseStep 808175 = 1212263) B1212263
theorem B809015 : Blo 535802 809015 := bstep (se 1 (by rfl) ⟨606761, by rfl⟩ : syracuseStep 809015 = 1213523) B1213523
theorem B4151405 : Blo 535802 4151405 := bstep (se 3 (by rfl) ⟨778388, by rfl⟩ : syracuseStep 4151405 = 1556777) B1556777
theorem B4086287 : Blo 535802 4086287 := bstep (se 1 (by rfl) ⟨3064715, by rfl⟩ : syracuseStep 4086287 = 6129431) B6129431
theorem B8871581 : Blo 535802 8871581 := bstep (se 3 (by rfl) ⟨1663421, by rfl⟩ : syracuseStep 8871581 = 3326843) B3326843
theorem B909407 : Blo 535802 909407 := bstep (se 1 (by rfl) ⟨682055, by rfl⟩ : syracuseStep 909407 = 1364111) B1364111
theorem B255682115 : Blo 535802 255682115 := bstep (se 1 (by rfl) ⟨191761586, by rfl⟩ : syracuseStep 255682115 = 383523173) B383523173
theorem B4580945 : Blo 535802 4580945 := bstep (se 2 (by rfl) ⟨1717854, by rfl⟩ : syracuseStep 4580945 = 3435709) B3435709
theorem B1533907 : Blo 535802 1533907 := bstep (se 1 (by rfl) ⟨1150430, by rfl⟩ : syracuseStep 1533907 = 2300861) B2300861
theorem B1534079 : Blo 535802 1534079 := bstep (se 1 (by rfl) ⟨1150559, by rfl⟩ : syracuseStep 1534079 = 2301119) B2301119
theorem B2713823 : Blo 535802 2713823 := bstep (se 1 (by rfl) ⟨2035367, by rfl⟩ : syracuseStep 2713823 = 4070735) B4070735
theorem B9300203 : Blo 535802 9300203 := bstep (se 1 (by rfl) ⟨6975152, by rfl⟩ : syracuseStep 9300203 = 13950305) B13950305
theorem B2452207 : Blo 535802 2452207 := bstep (se 1 (by rfl) ⟨1839155, by rfl⟩ : syracuseStep 2452207 = 3678311) B3678311
theorem B2714471 : Blo 535802 2714471 := bstep (se 1 (by rfl) ⟨2035853, by rfl⟩ : syracuseStep 2714471 = 4071707) B4071707
theorem B1207655 : Blo 535802 1207655 := bstep (se 1 (by rfl) ⟨905741, by rfl⟩ : syracuseStep 1207655 = 1811483) B1811483
theorem B1208303 : Blo 535802 1208303 := bstep (se 1 (by rfl) ⟨906227, by rfl⟩ : syracuseStep 1208303 = 1812455) B1812455
theorem B1208987 : Blo 535802 1208987 := bstep (se 1 (by rfl) ⟨906740, by rfl⟩ : syracuseStep 1208987 = 1813481) B1813481
theorem B1046143 : Blo 535802 1046143 := bstep (se 1 (by rfl) ⟨784607, by rfl⟩ : syracuseStep 1046143 = 1569215) B1569215
theorem B6224147 : Blo 535802 6224147 := bstep (se 1 (by rfl) ⟨4668110, by rfl⟩ : syracuseStep 6224147 = 9336221) B9336221
theorem B19822877 : Blo 535802 19822877 := bstep (se 3 (by rfl) ⟨3716789, by rfl⟩ : syracuseStep 19822877 = 7433579) B7433579
theorem B55769593 : Blo 535802 55769593 := bstep (se 2 (by rfl) ⟨20913597, by rfl⟩ : syracuseStep 55769593 = 41827195) B41827195
theorem B1211273 : Blo 535802 1211273 := bstep (se 2 (by rfl) ⟨454227, by rfl⟩ : syracuseStep 1211273 = 908455) B908455
theorem B16579511 : Blo 535802 16579511 := bstep (se 1 (by rfl) ⟨12434633, by rfl⟩ : syracuseStep 16579511 = 24869267) B24869267
theorem B1213019 : Blo 535802 1213019 := bstep (se 1 (by rfl) ⟨909764, by rfl⟩ : syracuseStep 1213019 = 1819529) B1819529
theorem B6554789 : Blo 535802 6554789 := bstep (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) B1229023
theorem B1213703 : Blo 535802 1213703 := bstep (se 1 (by rfl) ⟨910277, by rfl⟩ : syracuseStep 1213703 = 1820555) B1820555
theorem B6981383 : Blo 535802 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B2296487 : Blo 535802 2296487 := bstep (se 1 (by rfl) ⟨1722365, by rfl⟩ : syracuseStep 2296487 = 3444731) B3444731
theorem B76386341 : Blo 535802 76386341 := bstep (se 4 (by rfl) ⟨7161219, by rfl⟩ : syracuseStep 76386341 = 14322439) B14322439
theorem B2724191 : Blo 535802 2724191 := bstep (se 1 (by rfl) ⟨2043143, by rfl⟩ : syracuseStep 2724191 = 4086287) B4086287
theorem B5183783 : Blo 535802 5183783 := bstep (se 1 (by rfl) ⟨3887837, by rfl⟩ : syracuseStep 5183783 = 7775675) B7775675
theorem B3053963 : Blo 535802 3053963 := bstep (se 1 (by rfl) ⟨2290472, by rfl⟩ : syracuseStep 3053963 = 4580945) B4580945
theorem B1022719 : Blo 535802 1022719 := bstep (se 1 (by rfl) ⟨767039, by rfl⟩ : syracuseStep 1022719 = 1534079) B1534079
theorem B1809215 : Blo 535802 1809215 := bstep (se 1 (by rfl) ⟨1356911, by rfl⟩ : syracuseStep 1809215 = 2713823) B2713823
theorem B6200135 : Blo 535802 6200135 := bstep (se 1 (by rfl) ⟨4650101, by rfl⟩ : syracuseStep 6200135 = 9300203) B9300203
theorem B4594751 : Blo 535802 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B1809647 : Blo 535802 1809647 := bstep (se 1 (by rfl) ⟨1357235, by rfl⟩ : syracuseStep 1809647 = 2714471) B2714471
theorem B74359457 : Blo 535802 74359457 := bstep (se 2 (by rfl) ⟨27884796, by rfl⟩ : syracuseStep 74359457 = 55769593) B55769593
theorem B2729213 : Blo 535802 2729213 := bstep (se 3 (by rfl) ⟨511727, by rfl⟩ : syracuseStep 2729213 = 1023455) B1023455
theorem B13215251 : Blo 535802 13215251 := bstep (se 1 (by rfl) ⟨9911438, by rfl⟩ : syracuseStep 13215251 = 19822877) B19822877
theorem B11053007 : Blo 535802 11053007 := bstep (se 1 (by rfl) ⟨8289755, by rfl⟩ : syracuseStep 11053007 = 16579511) B16579511
theorem B4139581 : Blo 535802 4139581 := bstep (se 3 (by rfl) ⟨776171, by rfl⟩ : syracuseStep 4139581 = 1552343) B1552343
theorem B1699000271 : Blo 535802 1699000271 := bstep (se 1 (by rfl) ⟨1274250203, by rfl⟩ : syracuseStep 1699000271 = 2548500407) B2548500407
theorem B2732129 : Blo 535802 2732129 := bstep (se 2 (by rfl) ⟨1024548, by rfl⟩ : syracuseStep 2732129 = 2049097) B2049097
theorem B766111 : Blo 535802 766111 := bstep (se 1 (by rfl) ⟨574583, by rfl⟩ : syracuseStep 766111 = 1149167) B1149167
theorem B536743 : Blo 535802 536743 := bstep (se 1 (by rfl) ⟨402557, by rfl⟩ : syracuseStep 536743 = 805115) B805115
theorem B1716511 : Blo 535802 1716511 := bstep (se 1 (by rfl) ⟨1287383, by rfl⟩ : syracuseStep 1716511 = 2574767) B2574767
theorem B2044223 : Blo 535802 2044223 := bstep (se 1 (by rfl) ⟨1533167, by rfl⟩ : syracuseStep 2044223 = 3066335) B3066335
theorem B537703 : Blo 535802 537703 := bstep (se 1 (by rfl) ⟨403277, by rfl⟩ : syracuseStep 537703 = 806555) B806555
theorem B2045209 : Blo 535802 2045209 := bstep (se 2 (by rfl) ⟨766953, by rfl⟩ : syracuseStep 2045209 = 1533907) B1533907
theorem B538783 : Blo 535802 538783 := bstep (se 1 (by rfl) ⟨404087, by rfl⟩ : syracuseStep 538783 = 808175) B808175
theorem B1358329 : Blo 535802 1358329 := bstep (se 2 (by rfl) ⟨509373, by rfl⟩ : syracuseStep 1358329 = 1018747) B1018747
theorem B539343 : Blo 535802 539343 := bstep (se 1 (by rfl) ⟨404507, by rfl⟩ : syracuseStep 539343 = 809015) B809015
theorem B2767603 : Blo 535802 2767603 := bstep (se 1 (by rfl) ⟨2075702, by rfl⟩ : syracuseStep 2767603 = 4151405) B4151405
theorem B5914387 : Blo 535802 5914387 := bstep (se 1 (by rfl) ⟨4435790, by rfl⟩ : syracuseStep 5914387 = 8871581) B8871581
theorem B606271 : Blo 535802 606271 := bstep (se 1 (by rfl) ⟨454703, by rfl⟩ : syracuseStep 606271 = 909407) B909407
theorem B803753 : Blo 535802 803753 := bstep (se 2 (by rfl) ⟨301407, by rfl⟩ : syracuseStep 803753 = 602815) B602815
theorem B804137 : Blo 535802 804137 := bstep (se 2 (by rfl) ⟨301551, by rfl⟩ : syracuseStep 804137 = 603103) B603103
theorem B804329 : Blo 535802 804329 := bstep (se 2 (by rfl) ⟨301623, by rfl⟩ : syracuseStep 804329 = 603247) B603247
theorem B575591 : Blo 535802 575591 := bstep (se 1 (by rfl) ⟨431693, by rfl⟩ : syracuseStep 575591 = 863387) B863387
theorem B1394857 : Blo 535802 1394857 := bstep (se 2 (by rfl) ⟨523071, by rfl⟩ : syracuseStep 1394857 = 1046143) B1046143
theorem B805103 : Blo 535802 805103 := bstep (se 1 (by rfl) ⟨603827, by rfl⟩ : syracuseStep 805103 = 1207655) B1207655
theorem B805535 : Blo 535802 805535 := bstep (se 1 (by rfl) ⟨604151, by rfl⟩ : syracuseStep 805535 = 1208303) B1208303
theorem B805991 : Blo 535802 805991 := bstep (se 1 (by rfl) ⟨604493, by rfl⟩ : syracuseStep 805991 = 1208987) B1208987
theorem B1363675 : Blo 535802 1363675 := bstep (se 1 (by rfl) ⟨1022756, by rfl⟩ : syracuseStep 1363675 = 2045513) B2045513
theorem B905195 : Blo 535802 905195 := bstep (se 1 (by rfl) ⟨678896, by rfl⟩ : syracuseStep 905195 = 1357793) B1357793
theorem B4149431 : Blo 535802 4149431 := bstep (se 1 (by rfl) ⟨3112073, by rfl⟩ : syracuseStep 4149431 = 6224147) B6224147
theorem B1036495 : Blo 535802 1036495 := bstep (se 1 (by rfl) ⟨777371, by rfl⟩ : syracuseStep 1036495 = 1554743) B1554743
theorem B807515 : Blo 535802 807515 := bstep (se 1 (by rfl) ⟨605636, by rfl⟩ : syracuseStep 807515 = 1211273) B1211273
theorem B1364971 : Blo 535802 1364971 := bstep (se 1 (by rfl) ⟨1023728, by rfl⟩ : syracuseStep 1364971 = 2047457) B2047457
theorem B23516219 : Blo 535802 23516219 := bstep (se 1 (by rfl) ⟨17637164, by rfl⟩ : syracuseStep 23516219 = 35274329) B35274329
theorem B906599 : Blo 535802 906599 := bstep (se 1 (by rfl) ⟨679949, by rfl⟩ : syracuseStep 906599 = 1359899) B1359899
theorem B808427 : Blo 535802 808427 := bstep (se 1 (by rfl) ⟨606320, by rfl⟩ : syracuseStep 808427 = 1212641) B1212641
theorem B17487731 : Blo 535802 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B808895 : Blo 535802 808895 := bstep (se 1 (by rfl) ⟨606671, by rfl⟩ : syracuseStep 808895 = 1213343) B1213343
theorem B808937 : Blo 535802 808937 := bstep (se 2 (by rfl) ⟨303351, by rfl⟩ : syracuseStep 808937 = 606703) B606703
theorem B809063 : Blo 535802 809063 := bstep (se 1 (by rfl) ⟨606797, by rfl⟩ : syracuseStep 809063 = 1213595) B1213595
theorem B809639 : Blo 535802 809639 := bstep (se 1 (by rfl) ⟨607229, by rfl⟩ : syracuseStep 809639 = 1214459) B1214459
theorem B2906927 : Blo 535802 2906927 := bstep (se 1 (by rfl) ⟨2180195, by rfl⟩ : syracuseStep 2906927 = 4360391) B4360391
theorem B3497195 : Blo 535802 3497195 := bstep (se 1 (by rfl) ⟨2622896, by rfl⟩ : syracuseStep 3497195 = 5245793) B5245793
theorem B1727723 : Blo 535802 1727723 := bstep (se 1 (by rfl) ⟨1295792, by rfl⟩ : syracuseStep 1727723 = 2591585) B2591585
theorem B3269609 : Blo 535802 3269609 := bstep (se 2 (by rfl) ⟨1226103, by rfl⟩ : syracuseStep 3269609 = 2452207) B2452207
theorem B6120683 : Blo 535802 6120683 := bstep (se 1 (by rfl) ⟨4590512, by rfl⟩ : syracuseStep 6120683 = 9181025) B9181025
theorem B2712851 : Blo 535802 2712851 := bstep (se 1 (by rfl) ⟨2034638, by rfl⟩ : syracuseStep 2712851 = 4069277) B4069277
theorem B1205567 : Blo 535802 1205567 := bstep (se 1 (by rfl) ⟨904175, by rfl⟩ : syracuseStep 1205567 = 1808351) B1808351
theorem B170454743 : Blo 535802 170454743 := bstep (se 1 (by rfl) ⟨127841057, by rfl⟩ : syracuseStep 170454743 = 255682115) B255682115
theorem B4583405 : Blo 535802 4583405 := bstep (se 3 (by rfl) ⟨859388, by rfl⟩ : syracuseStep 4583405 = 1718777) B1718777
theorem B1208411 : Blo 535802 1208411 := bstep (se 1 (by rfl) ⟨906308, by rfl⟩ : syracuseStep 1208411 = 1812617) B1812617
theorem B19626137 : Blo 535802 19626137 := bstep (se 2 (by rfl) ⟨7359801, by rfl⟩ : syracuseStep 19626137 = 14719603) B14719603
theorem B1210859 : Blo 535802 1210859 := bstep (se 1 (by rfl) ⟨908144, by rfl⟩ : syracuseStep 1210859 = 1816289) B1816289
theorem B3439583 : Blo 535802 3439583 := bstep (se 1 (by rfl) ⟨2579687, by rfl⟩ : syracuseStep 3439583 = 5159375) B5159375
theorem B4654255 : Blo 535802 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B50924227 : Blo 535802 50924227 := bstep (se 1 (by rfl) ⟨38193170, by rfl⟩ : syracuseStep 50924227 = 76386341) B76386341
theorem B2035975 : Blo 535802 2035975 := bstep (se 1 (by rfl) ⟨1526981, by rfl⟩ : syracuseStep 2035975 = 3053963) B3053963
theorem B1937951 : Blo 535802 1937951 := bstep (se 1 (by rfl) ⟨1453463, by rfl⟩ : syracuseStep 1937951 = 2906927) B2906927
theorem B4133423 : Blo 535802 4133423 := bstep (se 1 (by rfl) ⟨3100067, by rfl⟩ : syracuseStep 4133423 = 6200135) B6200135
theorem B2331463 : Blo 535802 2331463 := bstep (se 1 (by rfl) ⟨1748597, by rfl⟩ : syracuseStep 2331463 = 3497195) B3497195
theorem B1151815 : Blo 535802 1151815 := bstep (se 1 (by rfl) ⟨863861, by rfl⟩ : syracuseStep 1151815 = 1727723) B1727723
theorem B1021481 : Blo 535802 1021481 := bstep (se 2 (by rfl) ⟨383055, by rfl⟩ : syracuseStep 1021481 = 766111) B766111
theorem B1808567 : Blo 535802 1808567 := bstep (se 1 (by rfl) ⟨1356425, by rfl⟩ : syracuseStep 1808567 = 2712851) B2712851
theorem B2726945 : Blo 535802 2726945 := bstep (se 2 (by rfl) ⟨1022604, by rfl⟩ : syracuseStep 2726945 = 2045209) B2045209
theorem B1132666847 : Blo 535802 1132666847 := bstep (se 1 (by rfl) ⟨849500135, by rfl⟩ : syracuseStep 1132666847 = 1699000271) B1699000271
theorem B3055603 : Blo 535802 3055603 := bstep (se 1 (by rfl) ⟨2291702, by rfl⟩ : syracuseStep 3055603 = 4583405) B4583405
theorem B1811105 : Blo 535802 1811105 := bstep (se 2 (by rfl) ⟨679164, by rfl⟩ : syracuseStep 1811105 = 1358329) B1358329
theorem B13084091 : Blo 535802 13084091 := bstep (se 1 (by rfl) ⟨9813068, by rfl⟩ : syracuseStep 13084091 = 19626137) B19626137
theorem B535835 : Blo 535802 535835 := bstep (se 1 (by rfl) ⟨401876, by rfl⟩ : syracuseStep 535835 = 803753) B803753
theorem B4369859 : Blo 535802 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B536091 : Blo 535802 536091 := bstep (se 1 (by rfl) ⟨402068, by rfl⟩ : syracuseStep 536091 = 804137) B804137
theorem B536219 : Blo 535802 536219 := bstep (se 1 (by rfl) ⟨402164, by rfl⟩ : syracuseStep 536219 = 804329) B804329
theorem B6139637 : Blo 535802 6139637 := bstep (se 5 (by rfl) ⟨287795, by rfl⟩ : syracuseStep 6139637 = 575591) B575591
theorem B536735 : Blo 535802 536735 := bstep (se 1 (by rfl) ⟨402551, by rfl⟩ : syracuseStep 536735 = 805103) B805103
theorem B537023 : Blo 535802 537023 := bstep (se 1 (by rfl) ⟨402767, by rfl⟩ : syracuseStep 537023 = 805535) B805535
theorem B537327 : Blo 535802 537327 := bstep (se 1 (by rfl) ⟨402995, by rfl⟩ : syracuseStep 537327 = 805991) B805991
theorem B603463 : Blo 535802 603463 := bstep (se 1 (by rfl) ⟨452597, by rfl⟩ : syracuseStep 603463 = 905195) B905195
theorem B2766287 : Blo 535802 2766287 := bstep (se 1 (by rfl) ⟨2074715, by rfl⟩ : syracuseStep 2766287 = 4149431) B4149431
theorem B1816127 : Blo 535802 1816127 := bstep (se 1 (by rfl) ⟨1362095, by rfl⟩ : syracuseStep 1816127 = 2724191) B2724191
theorem B538343 : Blo 535802 538343 := bstep (se 1 (by rfl) ⟨403757, by rfl⟩ : syracuseStep 538343 = 807515) B807515
theorem B15677479 : Blo 535802 15677479 := bstep (se 1 (by rfl) ⟨11758109, by rfl⟩ : syracuseStep 15677479 = 23516219) B23516219
theorem B5519441 : Blo 535802 5519441 := bstep (se 2 (by rfl) ⟨2069790, by rfl⟩ : syracuseStep 5519441 = 4139581) B4139581
theorem B604399 : Blo 535802 604399 := bstep (se 1 (by rfl) ⟨453299, by rfl⟩ : syracuseStep 604399 = 906599) B906599
theorem B538951 : Blo 535802 538951 := bstep (se 1 (by rfl) ⟨404213, by rfl⟩ : syracuseStep 538951 = 808427) B808427
theorem B539263 : Blo 535802 539263 := bstep (se 1 (by rfl) ⟨404447, by rfl⟩ : syracuseStep 539263 = 808895) B808895
theorem B539291 : Blo 535802 539291 := bstep (se 1 (by rfl) ⟨404468, by rfl⟩ : syracuseStep 539291 = 808937) B808937
theorem B539375 : Blo 535802 539375 := bstep (se 1 (by rfl) ⟨404531, by rfl⟩ : syracuseStep 539375 = 809063) B809063
theorem B3455855 : Blo 535802 3455855 := bstep (se 1 (by rfl) ⟨2591891, by rfl⟩ : syracuseStep 3455855 = 5183783) B5183783
theorem B539759 : Blo 535802 539759 := bstep (se 1 (by rfl) ⟨404819, by rfl⟩ : syracuseStep 539759 = 809639) B809639
theorem B3063167 : Blo 535802 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B1818233 : Blo 535802 1818233 := bstep (se 2 (by rfl) ⟨681837, by rfl⟩ : syracuseStep 1818233 = 1363675) B1363675
theorem B2179739 : Blo 535802 2179739 := bstep (se 1 (by rfl) ⟨1634804, by rfl⟩ : syracuseStep 2179739 = 3269609) B3269609
theorem B4080455 : Blo 535802 4080455 := bstep (se 1 (by rfl) ⟨3060341, by rfl⟩ : syracuseStep 4080455 = 6120683) B6120683
theorem B1819475 : Blo 535802 1819475 := bstep (se 1 (by rfl) ⟨1364606, by rfl⟩ : syracuseStep 1819475 = 2729213) B2729213
theorem B803711 : Blo 535802 803711 := bstep (se 1 (by rfl) ⟨602783, by rfl⟩ : syracuseStep 803711 = 1205567) B1205567
theorem B1819961 : Blo 535802 1819961 := bstep (se 2 (by rfl) ⟨682485, by rfl⟩ : syracuseStep 1819961 = 1364971) B1364971
theorem B805607 : Blo 535802 805607 := bstep (se 1 (by rfl) ⟨604205, by rfl⟩ : syracuseStep 805607 = 1208411) B1208411
theorem B1821419 : Blo 535802 1821419 := bstep (se 1 (by rfl) ⟨1366064, by rfl⟩ : syracuseStep 1821419 = 2732129) B2732129
theorem B1362815 : Blo 535802 1362815 := bstep (se 1 (by rfl) ⟨1022111, by rfl⟩ : syracuseStep 1362815 = 2044223) B2044223
theorem B3690137 : Blo 535802 3690137 := bstep (se 2 (by rfl) ⟨1383801, by rfl⟩ : syracuseStep 3690137 = 2767603) B2767603
theorem B1363625 : Blo 535802 1363625 := bstep (se 2 (by rfl) ⟨511359, by rfl⟩ : syracuseStep 1363625 = 1022719) B1022719
theorem B807239 : Blo 535802 807239 := bstep (se 1 (by rfl) ⟨605429, by rfl⟩ : syracuseStep 807239 = 1210859) B1210859
theorem B7885849 : Blo 535802 7885849 := bstep (se 2 (by rfl) ⟨2957193, by rfl⟩ : syracuseStep 7885849 = 5914387) B5914387
theorem B808361 : Blo 535802 808361 := bstep (se 2 (by rfl) ⟨303135, by rfl⟩ : syracuseStep 808361 = 606271) B606271
theorem B808679 : Blo 535802 808679 := bstep (se 1 (by rfl) ⟨606509, by rfl⟩ : syracuseStep 808679 = 1213019) B1213019
theorem B809135 : Blo 535802 809135 := bstep (se 1 (by rfl) ⟨606851, by rfl⟩ : syracuseStep 809135 = 1213703) B1213703
theorem B5527973 : Blo 535802 5527973 := bstep (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) B1036495
theorem B1530991 : Blo 535802 1530991 := bstep (se 1 (by rfl) ⟨1148243, by rfl⟩ : syracuseStep 1530991 = 2296487) B2296487
theorem B1859809 : Blo 535802 1859809 := bstep (se 2 (by rfl) ⟨697428, by rfl⟩ : syracuseStep 1859809 = 1394857) B1394857
theorem B11658487 : Blo 535802 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B1206143 : Blo 535802 1206143 := bstep (se 1 (by rfl) ⟨904607, by rfl⟩ : syracuseStep 1206143 = 1809215) B1809215
theorem B1206431 : Blo 535802 1206431 := bstep (se 1 (by rfl) ⟨904823, by rfl⟩ : syracuseStep 1206431 = 1809647) B1809647
theorem B2288681 : Blo 535802 2288681 := bstep (se 2 (by rfl) ⟨858255, by rfl⟩ : syracuseStep 2288681 = 1716511) B1716511
theorem B49572971 : Blo 535802 49572971 := bstep (se 1 (by rfl) ⟨37179728, by rfl⟩ : syracuseStep 49572971 = 74359457) B74359457
theorem B8810167 : Blo 535802 8810167 := bstep (se 1 (by rfl) ⟨6607625, by rfl⟩ : syracuseStep 8810167 = 13215251) B13215251
theorem B7368671 : Blo 535802 7368671 := bstep (se 1 (by rfl) ⟨5526503, by rfl⟩ : syracuseStep 7368671 = 11053007) B11053007
theorem B113636495 : Blo 535802 113636495 := bstep (se 1 (by rfl) ⟨85227371, by rfl⟩ : syracuseStep 113636495 = 170454743) B170454743
theorem B2293055 : Blo 535802 2293055 := bstep (se 1 (by rfl) ⟨1719791, by rfl⟩ : syracuseStep 2293055 = 3439583) B3439583
theorem B2720303 : Blo 535802 2720303 := bstep (se 1 (by rfl) ⟨2040227, by rfl⟩ : syracuseStep 2720303 = 4080455) B4080455
theorem B1212983 : Blo 535802 1212983 := bstep (se 1 (by rfl) ⟨909737, by rfl⟩ : syracuseStep 1212983 = 1819475) B1819475
theorem B1213307 : Blo 535802 1213307 := bstep (se 1 (by rfl) ⟨909980, by rfl⟩ : syracuseStep 1213307 = 1819961) B1819961
theorem B1214279 : Blo 535802 1214279 := bstep (se 1 (by rfl) ⟨910709, by rfl⟩ : syracuseStep 1214279 = 1821419) B1821419
theorem B2460091 : Blo 535802 2460091 := bstep (se 1 (by rfl) ⟨1845068, by rfl⟩ : syracuseStep 2460091 = 3690137) B3690137
theorem B2755615 : Blo 535802 2755615 := bstep (se 1 (by rfl) ⟨2066711, by rfl⟩ : syracuseStep 2755615 = 4133423) B4133423
theorem B67898969 : Blo 535802 67898969 := bstep (se 2 (by rfl) ⟨25462113, by rfl⟩ : syracuseStep 67898969 = 50924227) B50924227
theorem B755111231 : Blo 535802 755111231 := bstep (se 1 (by rfl) ⟨566333423, by rfl⟩ : syracuseStep 755111231 = 1132666847) B1132666847
theorem B14718509 : Blo 535802 14718509 := bstep (se 3 (by rfl) ⟨2759720, by rfl⟩ : syracuseStep 14718509 = 5519441) B5519441
theorem B8722727 : Blo 535802 8722727 := bstep (se 1 (by rfl) ⟨6542045, by rfl⟩ : syracuseStep 8722727 = 13084091) B13084091
theorem B1844191 : Blo 535802 1844191 := bstep (se 1 (by rfl) ⟨1383143, by rfl⟩ : syracuseStep 1844191 = 2766287) B2766287
theorem B2041321 : Blo 535802 2041321 := bstep (se 2 (by rfl) ⟨765495, by rfl⟩ : syracuseStep 2041321 = 1530991) B1530991
theorem B2303903 : Blo 535802 2303903 := bstep (se 1 (by rfl) ⟨1727927, by rfl⟩ : syracuseStep 2303903 = 3455855) B3455855
theorem B2042111 : Blo 535802 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B4074137 : Blo 535802 4074137 := bstep (se 2 (by rfl) ⟨1527801, by rfl⟩ : syracuseStep 4074137 = 3055603) B3055603
theorem B1453159 : Blo 535802 1453159 := bstep (se 1 (by rfl) ⟨1089869, by rfl⟩ : syracuseStep 1453159 = 2179739) B2179739
theorem B535807 : Blo 535802 535807 := bstep (se 1 (by rfl) ⟨401855, by rfl⟩ : syracuseStep 535807 = 803711) B803711
theorem B6205673 : Blo 535802 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B15544649 : Blo 535802 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B537071 : Blo 535802 537071 := bstep (se 1 (by rfl) ⟨402803, by rfl⟩ : syracuseStep 537071 = 805607) B805607
theorem B538159 : Blo 535802 538159 := bstep (se 1 (by rfl) ⟨403619, by rfl⟩ : syracuseStep 538159 = 807239) B807239
theorem B1291967 : Blo 535802 1291967 := bstep (se 1 (by rfl) ⟨968975, by rfl⟩ : syracuseStep 1291967 = 1937951) B1937951
theorem B538907 : Blo 535802 538907 := bstep (se 1 (by rfl) ⟨404180, by rfl⟩ : syracuseStep 538907 = 808361) B808361
theorem B539119 : Blo 535802 539119 := bstep (se 1 (by rfl) ⟨404339, by rfl⟩ : syracuseStep 539119 = 808679) B808679
theorem B539423 : Blo 535802 539423 := bstep (se 1 (by rfl) ⟨404567, by rfl⟩ : syracuseStep 539423 = 809135) B809135
theorem B1817963 : Blo 535802 1817963 := bstep (se 1 (by rfl) ⟨1363472, by rfl⟩ : syracuseStep 1817963 = 2726945) B2726945
theorem B11746889 : Blo 535802 11746889 := bstep (se 2 (by rfl) ⟨4405083, by rfl⟩ : syracuseStep 11746889 = 8810167) B8810167
theorem B804095 : Blo 535802 804095 := bstep (se 1 (by rfl) ⟨603071, by rfl⟩ : syracuseStep 804095 = 1206143) B1206143
theorem B804287 : Blo 535802 804287 := bstep (se 1 (by rfl) ⟨603215, by rfl⟩ : syracuseStep 804287 = 1206431) B1206431
theorem B804617 : Blo 535802 804617 := bstep (se 2 (by rfl) ⟨301731, by rfl⟩ : syracuseStep 804617 = 603463) B603463
theorem B1525787 : Blo 535802 1525787 := bstep (se 1 (by rfl) ⟨1144340, by rfl⟩ : syracuseStep 1525787 = 2288681) B2288681
theorem B33048647 : Blo 535802 33048647 := bstep (se 1 (by rfl) ⟨24786485, by rfl⟩ : syracuseStep 33048647 = 49572971) B49572971
theorem B805865 : Blo 535802 805865 := bstep (se 2 (by rfl) ⟨302199, by rfl⟩ : syracuseStep 805865 = 604399) B604399
theorem B1528703 : Blo 535802 1528703 := bstep (se 1 (by rfl) ⟨1146527, by rfl⟩ : syracuseStep 1528703 = 2293055) B2293055
theorem B2479745 : Blo 535802 2479745 := bstep (se 2 (by rfl) ⟨929904, by rfl⟩ : syracuseStep 2479745 = 1859809) B1859809
theorem B908543 : Blo 535802 908543 := bstep (se 1 (by rfl) ⟨681407, by rfl⟩ : syracuseStep 908543 = 1362815) B1362815
theorem B909083 : Blo 535802 909083 := bstep (se 1 (by rfl) ⟨681812, by rfl⟩ : syracuseStep 909083 = 1363625) B1363625
theorem B680987 : Blo 535802 680987 := bstep (se 1 (by rfl) ⟨510740, by rfl⟩ : syracuseStep 680987 = 1021481) B1021481
theorem B1205711 : Blo 535802 1205711 := bstep (se 1 (by rfl) ⟨904283, by rfl⟩ : syracuseStep 1205711 = 1808567) B1808567
theorem B2714633 : Blo 535802 2714633 := bstep (se 2 (by rfl) ⟨1017987, by rfl⟩ : syracuseStep 2714633 = 2035975) B2035975
theorem B1207403 : Blo 535802 1207403 := bstep (se 1 (by rfl) ⟨905552, by rfl⟩ : syracuseStep 1207403 = 1811105) B1811105
theorem B3108617 : Blo 535802 3108617 := bstep (se 2 (by rfl) ⟨1165731, by rfl⟩ : syracuseStep 3108617 = 2331463) B2331463
theorem B1535753 : Blo 535802 1535753 := bstep (se 2 (by rfl) ⟨575907, by rfl⟩ : syracuseStep 1535753 = 1151815) B1151815
theorem B14741261 : Blo 535802 14741261 := bstep (se 3 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 14741261 = 5527973) B5527973
theorem B10514465 : Blo 535802 10514465 := bstep (se 2 (by rfl) ⟨3942924, by rfl⟩ : syracuseStep 10514465 = 7885849) B7885849
theorem B2913239 : Blo 535802 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B4093091 : Blo 535802 4093091 := bstep (se 1 (by rfl) ⟨3069818, by rfl⟩ : syracuseStep 4093091 = 6139637) B6139637
theorem B4912447 : Blo 535802 4912447 := bstep (se 1 (by rfl) ⟨3684335, by rfl⟩ : syracuseStep 4912447 = 7368671) B7368671
theorem B20903305 : Blo 535802 20903305 := bstep (se 2 (by rfl) ⟨7838739, by rfl⟩ : syracuseStep 20903305 = 15677479) B15677479
theorem B75757663 : Blo 535802 75757663 := bstep (se 1 (by rfl) ⟨56818247, by rfl⟩ : syracuseStep 75757663 = 113636495) B113636495
theorem B1210751 : Blo 535802 1210751 := bstep (se 1 (by rfl) ⟨908063, by rfl⟩ : syracuseStep 1210751 = 1816127) B1816127
theorem B1212155 : Blo 535802 1212155 := bstep (se 1 (by rfl) ⟨909116, by rfl⟩ : syracuseStep 1212155 = 1818233) B1818233
theorem B16548461 : Blo 535802 16548461 := bstep (se 3 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 16548461 = 6205673) B6205673
theorem B2458921 : Blo 535802 2458921 := bstep (se 2 (by rfl) ⟨922095, by rfl⟩ : syracuseStep 2458921 = 1844191) B1844191
theorem B1017191 : Blo 535802 1017191 := bstep (se 1 (by rfl) ⟨762893, by rfl⟩ : syracuseStep 1017191 = 1525787) B1525787
theorem B2721761 : Blo 535802 2721761 := bstep (se 2 (by rfl) ⟨1020660, by rfl⟩ : syracuseStep 2721761 = 2041321) B2041321
theorem B3280121 : Blo 535802 3280121 := bstep (se 2 (by rfl) ⟨1230045, by rfl⟩ : syracuseStep 3280121 = 2460091) B2460091
theorem B1019135 : Blo 535802 1019135 := bstep (se 1 (by rfl) ⟨764351, by rfl⟩ : syracuseStep 1019135 = 1528703) B1528703
theorem B3674153 : Blo 535802 3674153 := bstep (se 2 (by rfl) ⟨1377807, by rfl⟩ : syracuseStep 3674153 = 2755615) B2755615
theorem B1809755 : Blo 535802 1809755 := bstep (se 1 (by rfl) ⟨1357316, by rfl⟩ : syracuseStep 1809755 = 2714633) B2714633
theorem B2072411 : Blo 535802 2072411 := bstep (se 1 (by rfl) ⟨1554308, by rfl⟩ : syracuseStep 2072411 = 3108617) B3108617
theorem B1023835 : Blo 535802 1023835 := bstep (se 1 (by rfl) ⟨767876, by rfl⟩ : syracuseStep 1023835 = 1535753) B1535753
theorem B10363099 : Blo 535802 10363099 := bstep (se 1 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 10363099 = 15544649) B15544649
theorem B1942159 : Blo 535802 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B2728727 : Blo 535802 2728727 := bstep (se 1 (by rfl) ⟨2046545, by rfl⟩ : syracuseStep 2728727 = 4093091) B4093091
theorem B861311 : Blo 535802 861311 := bstep (se 1 (by rfl) ⟨645983, by rfl⟩ : syracuseStep 861311 = 1291967) B1291967
theorem B1813535 : Blo 535802 1813535 := bstep (se 1 (by rfl) ⟨1360151, by rfl⟩ : syracuseStep 1813535 = 2720303) B2720303
theorem B404040869 : Blo 535802 404040869 := bstep (se 4 (by rfl) ⟨37878831, by rfl⟩ : syracuseStep 404040869 = 75757663) B75757663
theorem B536063 : Blo 535802 536063 := bstep (se 1 (by rfl) ⟨402047, by rfl⟩ : syracuseStep 536063 = 804095) B804095
theorem B536191 : Blo 535802 536191 := bstep (se 1 (by rfl) ⟨402143, by rfl⟩ : syracuseStep 536191 = 804287) B804287
theorem B536411 : Blo 535802 536411 := bstep (se 1 (by rfl) ⟨402308, by rfl⟩ : syracuseStep 536411 = 804617) B804617
theorem B22032431 : Blo 535802 22032431 := bstep (se 1 (by rfl) ⟨16524323, by rfl⟩ : syracuseStep 22032431 = 33048647) B33048647
theorem B537243 : Blo 535802 537243 := bstep (se 1 (by rfl) ⟨402932, by rfl⟩ : syracuseStep 537243 = 805865) B805865
theorem B45265979 : Blo 535802 45265979 := bstep (se 1 (by rfl) ⟨33949484, by rfl⟩ : syracuseStep 45265979 = 67898969) B67898969
theorem B1815965 : Blo 535802 1815965 := bstep (se 3 (by rfl) ⟨340493, by rfl⟩ : syracuseStep 1815965 = 680987) B680987
theorem B9812339 : Blo 535802 9812339 := bstep (se 1 (by rfl) ⟨7359254, by rfl⟩ : syracuseStep 9812339 = 14718509) B14718509
theorem B5815151 : Blo 535802 5815151 := bstep (se 1 (by rfl) ⟨4361363, by rfl⟩ : syracuseStep 5815151 = 8722727) B8722727
theorem B605695 : Blo 535802 605695 := bstep (se 1 (by rfl) ⟨454271, by rfl⟩ : syracuseStep 605695 = 908543) B908543
theorem B606055 : Blo 535802 606055 := bstep (se 1 (by rfl) ⟨454541, by rfl⟩ : syracuseStep 606055 = 909083) B909083
theorem B7750181 : Blo 535802 7750181 := bstep (se 4 (by rfl) ⟨726579, by rfl⟩ : syracuseStep 7750181 = 1453159) B1453159
theorem B803807 : Blo 535802 803807 := bstep (se 1 (by rfl) ⟨602855, by rfl⟩ : syracuseStep 803807 = 1205711) B1205711
theorem B1361407 : Blo 535802 1361407 := bstep (se 1 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 1361407 = 2042111) B2042111
theorem B27871073 : Blo 535802 27871073 := bstep (se 2 (by rfl) ⟨10451652, by rfl⟩ : syracuseStep 27871073 = 20903305) B20903305
theorem B804935 : Blo 535802 804935 := bstep (se 1 (by rfl) ⟨603701, by rfl⟩ : syracuseStep 804935 = 1207403) B1207403
theorem B807167 : Blo 535802 807167 := bstep (se 1 (by rfl) ⟨605375, by rfl⟩ : syracuseStep 807167 = 1210751) B1210751
theorem B808103 : Blo 535802 808103 := bstep (se 1 (by rfl) ⟨606077, by rfl⟩ : syracuseStep 808103 = 1212155) B1212155
theorem B808655 : Blo 535802 808655 := bstep (se 1 (by rfl) ⟨606491, by rfl⟩ : syracuseStep 808655 = 1212983) B1212983
theorem B808871 : Blo 535802 808871 := bstep (se 1 (by rfl) ⟨606653, by rfl⟩ : syracuseStep 808871 = 1213307) B1213307
theorem B809519 : Blo 535802 809519 := bstep (se 1 (by rfl) ⟨607139, by rfl⟩ : syracuseStep 809519 = 1214279) B1214279
theorem B503407487 : Blo 535802 503407487 := bstep (se 1 (by rfl) ⟨377555615, by rfl⟩ : syracuseStep 503407487 = 755111231) B755111231
theorem B6612653 : Blo 535802 6612653 := bstep (se 3 (by rfl) ⟨1239872, by rfl⟩ : syracuseStep 6612653 = 2479745) B2479745
theorem B1535935 : Blo 535802 1535935 := bstep (se 1 (by rfl) ⟨1151951, by rfl⟩ : syracuseStep 1535935 = 2303903) B2303903
theorem B6549929 : Blo 535802 6549929 := bstep (se 2 (by rfl) ⟨2456223, by rfl⟩ : syracuseStep 6549929 = 4912447) B4912447
theorem B2716091 : Blo 535802 2716091 := bstep (se 1 (by rfl) ⟨2037068, by rfl⟩ : syracuseStep 2716091 = 4074137) B4074137
theorem B9827507 : Blo 535802 9827507 := bstep (se 1 (by rfl) ⟨7370630, by rfl⟩ : syracuseStep 9827507 = 14741261) B14741261
theorem B7009643 : Blo 535802 7009643 := bstep (se 1 (by rfl) ⟨5257232, by rfl⟩ : syracuseStep 7009643 = 10514465) B10514465
theorem B1211975 : Blo 535802 1211975 := bstep (se 1 (by rfl) ⟨908981, by rfl⟩ : syracuseStep 1211975 = 1817963) B1817963
theorem B7831259 : Blo 535802 7831259 := bstep (se 1 (by rfl) ⟨5873444, by rfl⟩ : syracuseStep 7831259 = 11746889) B11746889
theorem B2589545 : Blo 535802 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B18580715 : Blo 535802 18580715 := bstep (se 1 (by rfl) ⟨13935536, by rfl⟩ : syracuseStep 18580715 = 27871073) B27871073
theorem B3278561 : Blo 535802 3278561 := bstep (se 2 (by rfl) ⟨1229460, by rfl⟩ : syracuseStep 3278561 = 2458921) B2458921
theorem B2296829 : Blo 535802 2296829 := bstep (se 3 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 2296829 = 861311) B861311
theorem B1381607 : Blo 535802 1381607 := bstep (se 1 (by rfl) ⟨1036205, by rfl⟩ : syracuseStep 1381607 = 2072411) B2072411
theorem B269360579 : Blo 535802 269360579 := bstep (se 1 (by rfl) ⟨202020434, by rfl⟩ : syracuseStep 269360579 = 404040869) B404040869
theorem B14688287 : Blo 535802 14688287 := bstep (se 1 (by rfl) ⟨11016215, by rfl⟩ : syracuseStep 14688287 = 22032431) B22032431
theorem B4366619 : Blo 535802 4366619 := bstep (se 1 (by rfl) ⟨3274964, by rfl⟩ : syracuseStep 4366619 = 6549929) B6549929
theorem B1810727 : Blo 535802 1810727 := bstep (se 1 (by rfl) ⟨1358045, by rfl⟩ : syracuseStep 1810727 = 2716091) B2716091
theorem B3876767 : Blo 535802 3876767 := bstep (se 1 (by rfl) ⟨2907575, by rfl⟩ : syracuseStep 3876767 = 5815151) B5815151
theorem B5220839 : Blo 535802 5220839 := bstep (se 1 (by rfl) ⟨3915629, by rfl⟩ : syracuseStep 5220839 = 7831259) B7831259
theorem B535871 : Blo 535802 535871 := bstep (se 1 (by rfl) ⟨401903, by rfl⟩ : syracuseStep 535871 = 803807) B803807
theorem B1814507 : Blo 535802 1814507 := bstep (se 1 (by rfl) ⟨1360880, by rfl⟩ : syracuseStep 1814507 = 2721761) B2721761
theorem B536623 : Blo 535802 536623 := bstep (se 1 (by rfl) ⟨402467, by rfl⟩ : syracuseStep 536623 = 804935) B804935
theorem B1815209 : Blo 535802 1815209 := bstep (se 2 (by rfl) ⟨680703, by rfl⟩ : syracuseStep 1815209 = 1361407) B1361407
theorem B538111 : Blo 535802 538111 := bstep (se 1 (by rfl) ⟨403583, by rfl⟩ : syracuseStep 538111 = 807167) B807167
theorem B538735 : Blo 535802 538735 := bstep (se 1 (by rfl) ⟨404051, by rfl⟩ : syracuseStep 538735 = 808103) B808103
theorem B539103 : Blo 535802 539103 := bstep (se 1 (by rfl) ⟨404327, by rfl⟩ : syracuseStep 539103 = 808655) B808655
theorem B539247 : Blo 535802 539247 := bstep (se 1 (by rfl) ⟨404435, by rfl⟩ : syracuseStep 539247 = 808871) B808871
theorem B539679 : Blo 535802 539679 := bstep (se 1 (by rfl) ⟨404759, by rfl⟩ : syracuseStep 539679 = 809519) B809519
theorem B2047913 : Blo 535802 2047913 := bstep (se 2 (by rfl) ⟨767967, by rfl⟩ : syracuseStep 2047913 = 1535935) B1535935
theorem B1819151 : Blo 535802 1819151 := bstep (se 1 (by rfl) ⟨1364363, by rfl⟩ : syracuseStep 1819151 = 2728727) B2728727
theorem B4408435 : Blo 535802 4408435 := bstep (se 1 (by rfl) ⟨3306326, by rfl⟩ : syracuseStep 4408435 = 6612653) B6612653
theorem B4673095 : Blo 535802 4673095 := bstep (se 1 (by rfl) ⟨3504821, by rfl⟩ : syracuseStep 4673095 = 7009643) B7009643
theorem B6541559 : Blo 535802 6541559 := bstep (se 1 (by rfl) ⟨4906169, by rfl⟩ : syracuseStep 6541559 = 9812339) B9812339
theorem B807593 : Blo 535802 807593 := bstep (se 2 (by rfl) ⟨302847, by rfl⟩ : syracuseStep 807593 = 605695) B605695
theorem B807983 : Blo 535802 807983 := bstep (se 1 (by rfl) ⟨605987, by rfl⟩ : syracuseStep 807983 = 1211975) B1211975
theorem B1365113 : Blo 535802 1365113 := bstep (se 2 (by rfl) ⟨511917, by rfl⟩ : syracuseStep 1365113 = 1023835) B1023835
theorem B808073 : Blo 535802 808073 := bstep (se 2 (by rfl) ⟨303027, by rfl⟩ : syracuseStep 808073 = 606055) B606055
theorem B13817465 : Blo 535802 13817465 := bstep (se 2 (by rfl) ⟨5181549, by rfl⟩ : syracuseStep 13817465 = 10363099) B10363099
theorem B11032307 : Blo 535802 11032307 := bstep (se 1 (by rfl) ⟨8274230, by rfl⟩ : syracuseStep 11032307 = 16548461) B16548461
theorem B678127 : Blo 535802 678127 := bstep (se 1 (by rfl) ⟨508595, by rfl⟩ : syracuseStep 678127 = 1017191) B1017191
theorem B20667149 : Blo 535802 20667149 := bstep (se 3 (by rfl) ⟨3875090, by rfl⟩ : syracuseStep 20667149 = 7750181) B7750181
theorem B2186747 : Blo 535802 2186747 := bstep (se 1 (by rfl) ⟨1640060, by rfl⟩ : syracuseStep 2186747 = 3280121) B3280121
theorem B679423 : Blo 535802 679423 := bstep (se 1 (by rfl) ⟨509567, by rfl⟩ : syracuseStep 679423 = 1019135) B1019135
theorem B2449435 : Blo 535802 2449435 := bstep (se 1 (by rfl) ⟨1837076, by rfl⟩ : syracuseStep 2449435 = 3674153) B3674153
theorem B26206685 : Blo 535802 26206685 := bstep (se 3 (by rfl) ⟨4913753, by rfl⟩ : syracuseStep 26206685 = 9827507) B9827507
theorem B1206503 : Blo 535802 1206503 := bstep (se 1 (by rfl) ⟨904877, by rfl⟩ : syracuseStep 1206503 = 1809755) B1809755
theorem B335604991 : Blo 535802 335604991 := bstep (se 1 (by rfl) ⟨251703743, by rfl⟩ : syracuseStep 335604991 = 503407487) B503407487
theorem B1209023 : Blo 535802 1209023 := bstep (se 1 (by rfl) ⟨906767, by rfl⟩ : syracuseStep 1209023 = 1813535) B1813535
theorem B30177319 : Blo 535802 30177319 := bstep (se 1 (by rfl) ⟨22632989, by rfl⟩ : syracuseStep 30177319 = 45265979) B45265979
theorem B1210643 : Blo 535802 1210643 := bstep (se 1 (by rfl) ⟨907982, by rfl⟩ : syracuseStep 1210643 = 1815965) B1815965
theorem B1212767 : Blo 535802 1212767 := bstep (se 1 (by rfl) ⟨909575, by rfl⟩ : syracuseStep 1212767 = 1819151) B1819151
theorem B12387143 : Blo 535802 12387143 := bstep (se 1 (by rfl) ⟨9290357, by rfl⟩ : syracuseStep 12387143 = 18580715) B18580715
theorem B4361039 : Blo 535802 4361039 := bstep (se 1 (by rfl) ⟨3270779, by rfl⟩ : syracuseStep 4361039 = 6541559) B6541559
theorem B921071 : Blo 535802 921071 := bstep (se 1 (by rfl) ⟨690803, by rfl⟩ : syracuseStep 921071 = 1381607) B1381607
theorem B9211643 : Blo 535802 9211643 := bstep (se 1 (by rfl) ⟨6908732, by rfl⟩ : syracuseStep 9211643 = 13817465) B13817465
theorem B17471123 : Blo 535802 17471123 := bstep (se 1 (by rfl) ⟨13103342, by rfl⟩ : syracuseStep 17471123 = 26206685) B26206685
theorem B538395 : Blo 535802 538395 := bstep (se 1 (by rfl) ⟨403796, by rfl⟩ : syracuseStep 538395 = 807593) B807593
theorem B538655 : Blo 535802 538655 := bstep (se 1 (by rfl) ⟨403991, by rfl⟩ : syracuseStep 538655 = 807983) B807983
theorem B538715 : Blo 535802 538715 := bstep (se 1 (by rfl) ⟨404036, by rfl⟩ : syracuseStep 538715 = 808073) B808073
theorem B7354871 : Blo 535802 7354871 := bstep (se 1 (by rfl) ⟨5516153, by rfl⟩ : syracuseStep 7354871 = 11032307) B11032307
theorem B13778099 : Blo 535802 13778099 := bstep (se 1 (by rfl) ⟨10333574, by rfl⟩ : syracuseStep 13778099 = 20667149) B20667149
theorem B1457831 : Blo 535802 1457831 := bstep (se 1 (by rfl) ⟨1093373, by rfl⟩ : syracuseStep 1457831 = 2186747) B2186747
theorem B23511653 : Blo 535802 23511653 := bstep (se 4 (by rfl) ⟨2204217, by rfl⟩ : syracuseStep 23511653 = 4408435) B4408435
theorem B804335 : Blo 535802 804335 := bstep (se 1 (by rfl) ⟨603251, by rfl⟩ : syracuseStep 804335 = 1206503) B1206503
theorem B904169 : Blo 535802 904169 := bstep (se 2 (by rfl) ⟨339063, by rfl⟩ : syracuseStep 904169 = 678127) B678127
theorem B24923173 : Blo 535802 24923173 := bstep (se 4 (by rfl) ⟨2336547, by rfl⟩ : syracuseStep 24923173 = 4673095) B4673095
theorem B806015 : Blo 535802 806015 := bstep (se 1 (by rfl) ⟨604511, by rfl⟩ : syracuseStep 806015 = 1209023) B1209023
theorem B718294877 : Blo 535802 718294877 := bstep (se 3 (by rfl) ⟨134680289, by rfl⟩ : syracuseStep 718294877 = 269360579) B269360579
theorem B807095 : Blo 535802 807095 := bstep (se 1 (by rfl) ⟨605321, by rfl⟩ : syracuseStep 807095 = 1210643) B1210643
theorem B905897 : Blo 535802 905897 := bstep (se 2 (by rfl) ⟨339711, by rfl⟩ : syracuseStep 905897 = 679423) B679423
theorem B1365275 : Blo 535802 1365275 := bstep (se 1 (by rfl) ⟨1023956, by rfl⟩ : syracuseStep 1365275 = 2047913) B2047913
theorem B3265913 : Blo 535802 3265913 := bstep (se 2 (by rfl) ⟨1224717, by rfl⟩ : syracuseStep 3265913 = 2449435) B2449435
theorem B1726363 : Blo 535802 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B1531219 : Blo 535802 1531219 := bstep (se 1 (by rfl) ⟨1148414, by rfl⟩ : syracuseStep 1531219 = 2296829) B2296829
theorem B910075 : Blo 535802 910075 := bstep (se 1 (by rfl) ⟨682556, by rfl⟩ : syracuseStep 910075 = 1365113) B1365113
theorem B447473321 : Blo 535802 447473321 := bstep (se 2 (by rfl) ⟨167802495, by rfl⟩ : syracuseStep 447473321 = 335604991) B335604991
theorem B8742829 : Blo 535802 8742829 := bstep (se 3 (by rfl) ⟨1639280, by rfl⟩ : syracuseStep 8742829 = 3278561) B3278561
theorem B9792191 : Blo 535802 9792191 := bstep (se 1 (by rfl) ⟨7344143, by rfl⟩ : syracuseStep 9792191 = 14688287) B14688287
theorem B2911079 : Blo 535802 2911079 := bstep (se 1 (by rfl) ⟨2183309, by rfl⟩ : syracuseStep 2911079 = 4366619) B4366619
theorem B1207151 : Blo 535802 1207151 := bstep (se 1 (by rfl) ⟨905363, by rfl⟩ : syracuseStep 1207151 = 1810727) B1810727
theorem B13922237 : Blo 535802 13922237 := bstep (se 3 (by rfl) ⟨2610419, by rfl⟩ : syracuseStep 13922237 = 5220839) B5220839
theorem B2584511 : Blo 535802 2584511 := bstep (se 1 (by rfl) ⟨1938383, by rfl⟩ : syracuseStep 2584511 = 3876767) B3876767
theorem B1209671 : Blo 535802 1209671 := bstep (se 1 (by rfl) ⟨907253, by rfl⟩ : syracuseStep 1209671 = 1814507) B1814507
theorem B40236425 : Blo 535802 40236425 := bstep (se 2 (by rfl) ⟨15088659, by rfl⟩ : syracuseStep 40236425 = 30177319) B30177319
theorem B1210139 : Blo 535802 1210139 := bstep (se 1 (by rfl) ⟨907604, by rfl⟩ : syracuseStep 1210139 = 1815209) B1815209
theorem B8258095 : Blo 535802 8258095 := bstep (se 1 (by rfl) ⟨6193571, by rfl⟩ : syracuseStep 8258095 = 12387143) B12387143
theorem B1213433 : Blo 535802 1213433 := bstep (se 2 (by rfl) ⟨455037, by rfl⟩ : syracuseStep 1213433 = 910075) B910075
theorem B33230897 : Blo 535802 33230897 := bstep (se 2 (by rfl) ⟨12461586, by rfl⟩ : syracuseStep 33230897 = 24923173) B24923173
theorem B6528127 : Blo 535802 6528127 := bstep (se 1 (by rfl) ⟨4896095, by rfl⟩ : syracuseStep 6528127 = 9792191) B9792191
theorem B1940719 : Blo 535802 1940719 := bstep (se 1 (by rfl) ⟨1455539, by rfl⟩ : syracuseStep 1940719 = 2911079) B2911079
theorem B2041625 : Blo 535802 2041625 := bstep (se 2 (by rfl) ⟨765609, by rfl⟩ : syracuseStep 2041625 = 1531219) B1531219
theorem B9185399 : Blo 535802 9185399 := bstep (se 1 (by rfl) ⟨6889049, by rfl⟩ : syracuseStep 9185399 = 13778099) B13778099
theorem B15674435 : Blo 535802 15674435 := bstep (se 1 (by rfl) ⟨11755826, by rfl⟩ : syracuseStep 15674435 = 23511653) B23511653
theorem B536223 : Blo 535802 536223 := bstep (se 1 (by rfl) ⟨402167, by rfl⟩ : syracuseStep 536223 = 804335) B804335
theorem B602779 : Blo 535802 602779 := bstep (se 1 (by rfl) ⟨452084, by rfl⟩ : syracuseStep 602779 = 904169) B904169
theorem B537343 : Blo 535802 537343 := bstep (se 1 (by rfl) ⟨403007, by rfl⟩ : syracuseStep 537343 = 806015) B806015
theorem B6141095 : Blo 535802 6141095 := bstep (se 1 (by rfl) ⟨4605821, by rfl⟩ : syracuseStep 6141095 = 9211643) B9211643
theorem B538063 : Blo 535802 538063 := bstep (se 1 (by rfl) ⟨403547, by rfl⟩ : syracuseStep 538063 = 807095) B807095
theorem B603931 : Blo 535802 603931 := bstep (se 1 (by rfl) ⟨452948, by rfl⟩ : syracuseStep 603931 = 905897) B905897
theorem B2177275 : Blo 535802 2177275 := bstep (se 1 (by rfl) ⟨1632956, by rfl⟩ : syracuseStep 2177275 = 3265913) B3265913
theorem B11647415 : Blo 535802 11647415 := bstep (se 1 (by rfl) ⟨8735561, by rfl⟩ : syracuseStep 11647415 = 17471123) B17471123
theorem B804767 : Blo 535802 804767 := bstep (se 1 (by rfl) ⟨603575, by rfl⟩ : syracuseStep 804767 = 1207151) B1207151
theorem B1723007 : Blo 535802 1723007 := bstep (se 1 (by rfl) ⟨1292255, by rfl⟩ : syracuseStep 1723007 = 2584511) B2584511
theorem B806447 : Blo 535802 806447 := bstep (se 1 (by rfl) ⟨604835, by rfl⟩ : syracuseStep 806447 = 1209671) B1209671
theorem B26824283 : Blo 535802 26824283 := bstep (se 1 (by rfl) ⟨20118212, by rfl⟩ : syracuseStep 26824283 = 40236425) B40236425
theorem B806759 : Blo 535802 806759 := bstep (se 1 (by rfl) ⟨605069, by rfl⟩ : syracuseStep 806759 = 1210139) B1210139
theorem B4903247 : Blo 535802 4903247 := bstep (se 1 (by rfl) ⟨3677435, by rfl⟩ : syracuseStep 4903247 = 7354871) B7354871
theorem B971887 : Blo 535802 971887 := bstep (se 1 (by rfl) ⟨728915, by rfl⟩ : syracuseStep 971887 = 1457831) B1457831
theorem B808511 : Blo 535802 808511 := bstep (se 1 (by rfl) ⟨606383, by rfl⟩ : syracuseStep 808511 = 1212767) B1212767
theorem B2907359 : Blo 535802 2907359 := bstep (se 1 (by rfl) ⟨2180519, by rfl⟩ : syracuseStep 2907359 = 4361039) B4361039
theorem B614047 : Blo 535802 614047 := bstep (se 1 (by rfl) ⟨460535, by rfl⟩ : syracuseStep 614047 = 921071) B921071
theorem B11657105 : Blo 535802 11657105 := bstep (se 2 (by rfl) ⟨4371414, by rfl⟩ : syracuseStep 11657105 = 8742829) B8742829
theorem B478863251 : Blo 535802 478863251 := bstep (se 1 (by rfl) ⟨359147438, by rfl⟩ : syracuseStep 478863251 = 718294877) B718294877
theorem B910183 : Blo 535802 910183 := bstep (se 1 (by rfl) ⟨682637, by rfl⟩ : syracuseStep 910183 = 1365275) B1365275
theorem B298315547 : Blo 535802 298315547 := bstep (se 1 (by rfl) ⟨223736660, by rfl⟩ : syracuseStep 298315547 = 447473321) B447473321
theorem B9207269 : Blo 535802 9207269 := bstep (se 4 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 9207269 = 1726363) B1726363
theorem B37125965 : Blo 535802 37125965 := bstep (se 3 (by rfl) ⟨6961118, by rfl⟩ : syracuseStep 37125965 = 13922237) B13922237
theorem B1213577 : Blo 535802 1213577 := bstep (se 2 (by rfl) ⟨455091, by rfl⟩ : syracuseStep 1213577 = 910183) B910183
theorem B1148671 : Blo 535802 1148671 := bstep (se 1 (by rfl) ⟨861503, by rfl⟩ : syracuseStep 1148671 = 1723007) B1723007
theorem B22153931 : Blo 535802 22153931 := bstep (se 1 (by rfl) ⟨16615448, by rfl⟩ : syracuseStep 22153931 = 33230897) B33230897
theorem B44043173 : Blo 535802 44043173 := bstep (se 4 (by rfl) ⟨4129047, by rfl⟩ : syracuseStep 44043173 = 8258095) B8258095
theorem B1938239 : Blo 535802 1938239 := bstep (se 1 (by rfl) ⟨1453679, by rfl⟩ : syracuseStep 1938239 = 2907359) B2907359
theorem B7771403 : Blo 535802 7771403 := bstep (se 1 (by rfl) ⟨5828552, by rfl⟩ : syracuseStep 7771403 = 11657105) B11657105
theorem B198877031 : Blo 535802 198877031 := bstep (se 1 (by rfl) ⟨149157773, by rfl⟩ : syracuseStep 198877031 = 298315547) B298315547
theorem B99002573 : Blo 535802 99002573 := bstep (se 3 (by rfl) ⟨18562982, by rfl⟩ : syracuseStep 99002573 = 37125965) B37125965
theorem B6138179 : Blo 535802 6138179 := bstep (se 1 (by rfl) ⟨4603634, by rfl⟩ : syracuseStep 6138179 = 9207269) B9207269
theorem B536511 : Blo 535802 536511 := bstep (se 1 (by rfl) ⟨402383, by rfl⟩ : syracuseStep 536511 = 804767) B804767
theorem B537631 : Blo 535802 537631 := bstep (se 1 (by rfl) ⟨403223, by rfl⟩ : syracuseStep 537631 = 806447) B806447
theorem B537839 : Blo 535802 537839 := bstep (se 1 (by rfl) ⟨403379, by rfl⟩ : syracuseStep 537839 = 806759) B806759
theorem B539007 : Blo 535802 539007 := bstep (se 1 (by rfl) ⟨404255, by rfl⟩ : syracuseStep 539007 = 808511) B808511
theorem B319242167 : Blo 535802 319242167 := bstep (se 1 (by rfl) ⟨239431625, by rfl⟩ : syracuseStep 319242167 = 478863251) B478863251
theorem B803705 : Blo 535802 803705 := bstep (se 2 (by rfl) ⟨301389, by rfl⟩ : syracuseStep 803705 = 602779) B602779
theorem B1361083 : Blo 535802 1361083 := bstep (se 1 (by rfl) ⟨1020812, by rfl⟩ : syracuseStep 1361083 = 2041625) B2041625
theorem B1295849 : Blo 535802 1295849 := bstep (se 2 (by rfl) ⟨485943, by rfl⟩ : syracuseStep 1295849 = 971887) B971887
theorem B805241 : Blo 535802 805241 := bstep (se 2 (by rfl) ⟨301965, by rfl⟩ : syracuseStep 805241 = 603931) B603931
theorem B2903033 : Blo 535802 2903033 := bstep (se 2 (by rfl) ⟨1088637, by rfl⟩ : syracuseStep 2903033 = 2177275) B2177275
theorem B8704169 : Blo 535802 8704169 := bstep (se 2 (by rfl) ⟨3264063, by rfl⟩ : syracuseStep 8704169 = 6528127) B6528127
theorem B808955 : Blo 535802 808955 := bstep (se 1 (by rfl) ⟨606716, by rfl⟩ : syracuseStep 808955 = 1213433) B1213433
theorem B17882855 : Blo 535802 17882855 := bstep (se 1 (by rfl) ⟨13412141, by rfl⟩ : syracuseStep 17882855 = 26824283) B26824283
theorem B3268831 : Blo 535802 3268831 := bstep (se 1 (by rfl) ⟨2451623, by rfl⟩ : syracuseStep 3268831 = 4903247) B4903247
theorem B31059773 : Blo 535802 31059773 := bstep (se 3 (by rfl) ⟨5823707, by rfl⟩ : syracuseStep 31059773 = 11647415) B11647415
theorem B6123599 : Blo 535802 6123599 := bstep (se 1 (by rfl) ⟨4592699, by rfl⟩ : syracuseStep 6123599 = 9185399) B9185399
theorem B10449623 : Blo 535802 10449623 := bstep (se 1 (by rfl) ⟨7837217, by rfl⟩ : syracuseStep 10449623 = 15674435) B15674435
theorem B4094063 : Blo 535802 4094063 := bstep (se 1 (by rfl) ⟨3070547, by rfl⟩ : syracuseStep 4094063 = 6141095) B6141095
theorem B2587625 : Blo 535802 2587625 := bstep (se 2 (by rfl) ⟨970359, by rfl⟩ : syracuseStep 2587625 = 1940719) B1940719
theorem B818729 : Blo 535802 818729 := bstep (se 2 (by rfl) ⟨307023, by rfl⟩ : syracuseStep 818729 = 614047) B614047
theorem B4358441 : Blo 535802 4358441 := bstep (se 2 (by rfl) ⟨1634415, by rfl⟩ : syracuseStep 4358441 = 3268831) B3268831
theorem B29362115 : Blo 535802 29362115 := bstep (se 1 (by rfl) ⟨22021586, by rfl⟩ : syracuseStep 29362115 = 44043173) B44043173
theorem B1935355 : Blo 535802 1935355 := bstep (se 1 (by rfl) ⟨1451516, by rfl⟩ : syracuseStep 1935355 = 2903033) B2903033
theorem B5802779 : Blo 535802 5802779 := bstep (se 1 (by rfl) ⟨4352084, by rfl⟩ : syracuseStep 5802779 = 8704169) B8704169
theorem B5180935 : Blo 535802 5180935 := bstep (se 1 (by rfl) ⟨3885701, by rfl⟩ : syracuseStep 5180935 = 7771403) B7771403
theorem B132584687 : Blo 535802 132584687 := bstep (se 1 (by rfl) ⟨99438515, by rfl⟩ : syracuseStep 132584687 = 198877031) B198877031
theorem B66001715 : Blo 535802 66001715 := bstep (se 1 (by rfl) ⟨49501286, by rfl⟩ : syracuseStep 66001715 = 99002573) B99002573
theorem B2729375 : Blo 535802 2729375 := bstep (se 1 (by rfl) ⟨2047031, by rfl⟩ : syracuseStep 2729375 = 4094063) B4094063
theorem B535803 : Blo 535802 535803 := bstep (se 1 (by rfl) ⟨401852, by rfl⟩ : syracuseStep 535803 = 803705) B803705
theorem B1814777 : Blo 535802 1814777 := bstep (se 2 (by rfl) ⟨680541, by rfl⟩ : syracuseStep 1814777 = 1361083) B1361083
theorem B536827 : Blo 535802 536827 := bstep (se 1 (by rfl) ⟨402620, by rfl⟩ : syracuseStep 536827 = 805241) B805241
theorem B1292159 : Blo 535802 1292159 := bstep (se 1 (by rfl) ⟨969119, by rfl⟩ : syracuseStep 1292159 = 1938239) B1938239
theorem B3455597 : Blo 535802 3455597 := bstep (se 3 (by rfl) ⟨647924, by rfl⟩ : syracuseStep 3455597 = 1295849) B1295849
theorem B539303 : Blo 535802 539303 := bstep (se 1 (by rfl) ⟨404477, by rfl⟩ : syracuseStep 539303 = 808955) B808955
theorem B4082399 : Blo 535802 4082399 := bstep (se 1 (by rfl) ⟨3061799, by rfl⟩ : syracuseStep 4082399 = 6123599) B6123599
theorem B6966415 : Blo 535802 6966415 := bstep (se 1 (by rfl) ⟨5224811, by rfl⟩ : syracuseStep 6966415 = 10449623) B10449623
theorem B1725083 : Blo 535802 1725083 := bstep (se 1 (by rfl) ⟨1293812, by rfl⟩ : syracuseStep 1725083 = 2587625) B2587625
theorem B545819 : Blo 535802 545819 := bstep (se 1 (by rfl) ⟨409364, by rfl⟩ : syracuseStep 545819 = 818729) B818729
theorem B809051 : Blo 535802 809051 := bstep (se 1 (by rfl) ⟨606788, by rfl⟩ : syracuseStep 809051 = 1213577) B1213577
theorem B14769287 : Blo 535802 14769287 := bstep (se 1 (by rfl) ⟨11076965, by rfl⟩ : syracuseStep 14769287 = 22153931) B22153931
theorem B1531561 : Blo 535802 1531561 := bstep (se 2 (by rfl) ⟨574335, by rfl⟩ : syracuseStep 1531561 = 1148671) B1148671
theorem B11921903 : Blo 535802 11921903 := bstep (se 1 (by rfl) ⟨8941427, by rfl⟩ : syracuseStep 11921903 = 17882855) B17882855
theorem B4092119 : Blo 535802 4092119 := bstep (se 1 (by rfl) ⟨3069089, by rfl⟩ : syracuseStep 4092119 = 6138179) B6138179
theorem B20706515 : Blo 535802 20706515 := bstep (se 1 (by rfl) ⟨15529886, by rfl⟩ : syracuseStep 20706515 = 31059773) B31059773
theorem B212828111 : Blo 535802 212828111 := bstep (se 1 (by rfl) ⟨159621083, by rfl⟩ : syracuseStep 212828111 = 319242167) B319242167
theorem B2721599 : Blo 535802 2721599 := bstep (se 1 (by rfl) ⟨2041199, by rfl⟩ : syracuseStep 2721599 = 4082399) B4082399
theorem B3868519 : Blo 535802 3868519 := bstep (se 1 (by rfl) ⟨2901389, by rfl⟩ : syracuseStep 3868519 = 5802779) B5802779
theorem B1150055 : Blo 535802 1150055 := bstep (se 1 (by rfl) ⟨862541, by rfl⟩ : syracuseStep 1150055 = 1725083) B1725083
theorem B2728079 : Blo 535802 2728079 := bstep (se 1 (by rfl) ⟨2046059, by rfl⟩ : syracuseStep 2728079 = 4092119) B4092119
theorem B13804343 : Blo 535802 13804343 := bstep (se 1 (by rfl) ⟨10353257, by rfl⟩ : syracuseStep 13804343 = 20706515) B20706515
theorem B861439 : Blo 535802 861439 := bstep (se 1 (by rfl) ⟨646079, by rfl⟩ : syracuseStep 861439 = 1292159) B1292159
theorem B2303731 : Blo 535802 2303731 := bstep (se 1 (by rfl) ⟨1727798, by rfl⟩ : syracuseStep 2303731 = 3455597) B3455597
theorem B2042081 : Blo 535802 2042081 := bstep (se 2 (by rfl) ⟨765780, by rfl⟩ : syracuseStep 2042081 = 1531561) B1531561
theorem B1455517 : Blo 535802 1455517 := bstep (se 3 (by rfl) ⟨272909, by rfl⟩ : syracuseStep 1455517 = 545819) B545819
theorem B88389791 : Blo 535802 88389791 := bstep (se 1 (by rfl) ⟨66292343, by rfl⟩ : syracuseStep 88389791 = 132584687) B132584687
theorem B539367 : Blo 535802 539367 := bstep (se 1 (by rfl) ⟨404525, by rfl⟩ : syracuseStep 539367 = 809051) B809051
theorem B9846191 : Blo 535802 9846191 := bstep (se 1 (by rfl) ⟨7384643, by rfl⟩ : syracuseStep 9846191 = 14769287) B14769287
theorem B78298973 : Blo 535802 78298973 := bstep (se 3 (by rfl) ⟨14681057, by rfl⟩ : syracuseStep 78298973 = 29362115) B29362115
theorem B1819583 : Blo 535802 1819583 := bstep (se 1 (by rfl) ⟨1364687, by rfl⟩ : syracuseStep 1819583 = 2729375) B2729375
theorem B7947935 : Blo 535802 7947935 := bstep (se 1 (by rfl) ⟨5960951, by rfl⟩ : syracuseStep 7947935 = 11921903) B11921903
theorem B2905627 : Blo 535802 2905627 := bstep (se 1 (by rfl) ⟨2179220, by rfl⟩ : syracuseStep 2905627 = 4358441) B4358441
theorem B2580473 : Blo 535802 2580473 := bstep (se 2 (by rfl) ⟨967677, by rfl⟩ : syracuseStep 2580473 = 1935355) B1935355
theorem B44001143 : Blo 535802 44001143 := bstep (se 1 (by rfl) ⟨33000857, by rfl⟩ : syracuseStep 44001143 = 66001715) B66001715
theorem B6907913 : Blo 535802 6907913 := bstep (se 2 (by rfl) ⟨2590467, by rfl⟩ : syracuseStep 6907913 = 5180935) B5180935
theorem B37154213 : Blo 535802 37154213 := bstep (se 4 (by rfl) ⟨3483207, by rfl⟩ : syracuseStep 37154213 = 6966415) B6966415
theorem B1209851 : Blo 535802 1209851 := bstep (se 1 (by rfl) ⟨907388, by rfl⟩ : syracuseStep 1209851 = 1814777) B1814777
theorem B141885407 : Blo 535802 141885407 := bstep (se 1 (by rfl) ⟨106414055, by rfl⟩ : syracuseStep 141885407 = 212828111) B212828111
theorem B1213055 : Blo 535802 1213055 := bstep (se 1 (by rfl) ⟨909791, by rfl⟩ : syracuseStep 1213055 = 1819583) B1819583
theorem B1148585 : Blo 535802 1148585 := bstep (se 2 (by rfl) ⟨430719, by rfl⟩ : syracuseStep 1148585 = 861439) B861439
theorem B29334095 : Blo 535802 29334095 := bstep (se 1 (by rfl) ⟨22000571, by rfl⟩ : syracuseStep 29334095 = 44001143) B44001143
theorem B1940689 : Blo 535802 1940689 := bstep (se 2 (by rfl) ⟨727758, by rfl⟩ : syracuseStep 1940689 = 1455517) B1455517
theorem B3874169 : Blo 535802 3874169 := bstep (se 2 (by rfl) ⟨1452813, by rfl⟩ : syracuseStep 3874169 = 2905627) B2905627
theorem B58926527 : Blo 535802 58926527 := bstep (se 1 (by rfl) ⟨44194895, by rfl⟩ : syracuseStep 58926527 = 88389791) B88389791
theorem B6564127 : Blo 535802 6564127 := bstep (se 1 (by rfl) ⟨4923095, by rfl⟩ : syracuseStep 6564127 = 9846191) B9846191
theorem B1814399 : Blo 535802 1814399 := bstep (se 1 (by rfl) ⟨1360799, by rfl⟩ : syracuseStep 1814399 = 2721599) B2721599
theorem B766703 : Blo 535802 766703 := bstep (se 1 (by rfl) ⟨575027, by rfl⟩ : syracuseStep 766703 = 1150055) B1150055
theorem B5158025 : Blo 535802 5158025 := bstep (se 2 (by rfl) ⟨1934259, by rfl⟩ : syracuseStep 5158025 = 3868519) B3868519
theorem B1720315 : Blo 535802 1720315 := bstep (se 1 (by rfl) ⟨1290236, by rfl⟩ : syracuseStep 1720315 = 2580473) B2580473
theorem B1818719 : Blo 535802 1818719 := bstep (se 1 (by rfl) ⟨1364039, by rfl⟩ : syracuseStep 1818719 = 2728079) B2728079
theorem B4605275 : Blo 535802 4605275 := bstep (se 1 (by rfl) ⟨3453956, by rfl⟩ : syracuseStep 4605275 = 6907913) B6907913
theorem B1361387 : Blo 535802 1361387 := bstep (se 1 (by rfl) ⟨1021040, by rfl⟩ : syracuseStep 1361387 = 2042081) B2042081
theorem B806567 : Blo 535802 806567 := bstep (se 1 (by rfl) ⟨604925, by rfl⟩ : syracuseStep 806567 = 1209851) B1209851
theorem B94590271 : Blo 535802 94590271 := bstep (se 1 (by rfl) ⟨70942703, by rfl⟩ : syracuseStep 94590271 = 141885407) B141885407
theorem B5298623 : Blo 535802 5298623 := bstep (se 1 (by rfl) ⟨3973967, by rfl⟩ : syracuseStep 5298623 = 7947935) B7947935
theorem B3071641 : Blo 535802 3071641 := bstep (se 2 (by rfl) ⟨1151865, by rfl⟩ : syracuseStep 3071641 = 2303731) B2303731
theorem B9202895 : Blo 535802 9202895 := bstep (se 1 (by rfl) ⟨6902171, by rfl⟩ : syracuseStep 9202895 = 13804343) B13804343
theorem B24769475 : Blo 535802 24769475 := bstep (se 1 (by rfl) ⟨18577106, by rfl⟩ : syracuseStep 24769475 = 37154213) B37154213
theorem B52199315 : Blo 535802 52199315 := bstep (se 1 (by rfl) ⟨39149486, by rfl⟩ : syracuseStep 52199315 = 78298973) B78298973
theorem B1212479 : Blo 535802 1212479 := bstep (se 1 (by rfl) ⟨909359, by rfl⟩ : syracuseStep 1212479 = 1818719) B1818719
theorem B8752169 : Blo 535802 8752169 := bstep (se 2 (by rfl) ⟨3282063, by rfl⟩ : syracuseStep 8752169 = 6564127) B6564127
theorem B6135263 : Blo 535802 6135263 := bstep (se 1 (by rfl) ⟨4601447, by rfl⟩ : syracuseStep 6135263 = 9202895) B9202895
theorem B2044541 : Blo 535802 2044541 := bstep (se 3 (by rfl) ⟨383351, by rfl⟩ : syracuseStep 2044541 = 766703) B766703
theorem B537711 : Blo 535802 537711 := bstep (se 1 (by rfl) ⟨403283, by rfl⟩ : syracuseStep 537711 = 806567) B806567
theorem B3062893 : Blo 535802 3062893 := bstep (se 3 (by rfl) ⟨574292, by rfl⟩ : syracuseStep 3062893 = 1148585) B1148585
theorem B808703 : Blo 535802 808703 := bstep (se 1 (by rfl) ⟨606527, by rfl⟩ : syracuseStep 808703 = 1213055) B1213055
theorem B3070183 : Blo 535802 3070183 := bstep (se 1 (by rfl) ⟨2302637, by rfl⟩ : syracuseStep 3070183 = 4605275) B4605275
theorem B907591 : Blo 535802 907591 := bstep (se 1 (by rfl) ⟨680693, by rfl⟩ : syracuseStep 907591 = 1361387) B1361387
theorem B3532415 : Blo 535802 3532415 := bstep (se 1 (by rfl) ⟨2649311, by rfl⟩ : syracuseStep 3532415 = 5298623) B5298623
theorem B19556063 : Blo 535802 19556063 := bstep (se 1 (by rfl) ⟨14667047, by rfl⟩ : syracuseStep 19556063 = 29334095) B29334095
theorem B2582779 : Blo 535802 2582779 := bstep (se 1 (by rfl) ⟨1937084, by rfl⟩ : syracuseStep 2582779 = 3874169) B3874169
theorem B39284351 : Blo 535802 39284351 := bstep (se 1 (by rfl) ⟨29463263, by rfl⟩ : syracuseStep 39284351 = 58926527) B58926527
theorem B10350341 : Blo 535802 10350341 := bstep (se 4 (by rfl) ⟨970344, by rfl⟩ : syracuseStep 10350341 = 1940689) B1940689
theorem B126120361 : Blo 535802 126120361 := bstep (se 2 (by rfl) ⟨47295135, by rfl⟩ : syracuseStep 126120361 = 94590271) B94590271
theorem B1209599 : Blo 535802 1209599 := bstep (se 1 (by rfl) ⟨907199, by rfl⟩ : syracuseStep 1209599 = 1814399) B1814399
theorem B16512983 : Blo 535802 16512983 := bstep (se 1 (by rfl) ⟨12384737, by rfl⟩ : syracuseStep 16512983 = 24769475) B24769475
theorem B3438683 : Blo 535802 3438683 := bstep (se 1 (by rfl) ⟨2579012, by rfl⟩ : syracuseStep 3438683 = 5158025) B5158025
theorem B4095521 : Blo 535802 4095521 := bstep (se 2 (by rfl) ⟨1535820, by rfl⟩ : syracuseStep 4095521 = 3071641) B3071641
theorem B34799543 : Blo 535802 34799543 := bstep (se 1 (by rfl) ⟨26099657, by rfl⟩ : syracuseStep 34799543 = 52199315) B52199315
theorem B2293753 : Blo 535802 2293753 := bstep (se 2 (by rfl) ⟨860157, by rfl⟩ : syracuseStep 2293753 = 1720315) B1720315
theorem B3443705 : Blo 535802 3443705 := bstep (se 2 (by rfl) ⟨1291389, by rfl⟩ : syracuseStep 3443705 = 2582779) B2582779
theorem B26189567 : Blo 535802 26189567 := bstep (se 1 (by rfl) ⟨19642175, by rfl⟩ : syracuseStep 26189567 = 39284351) B39284351
theorem B23339117 : Blo 535802 23339117 := bstep (se 3 (by rfl) ⟨4376084, by rfl⟩ : syracuseStep 23339117 = 8752169) B8752169
theorem B2730347 : Blo 535802 2730347 := bstep (se 1 (by rfl) ⟨2047760, by rfl⟩ : syracuseStep 2730347 = 4095521) B4095521
theorem B3058337 : Blo 535802 3058337 := bstep (se 2 (by rfl) ⟨1146876, by rfl⟩ : syracuseStep 3058337 = 2293753) B2293753
theorem B539135 : Blo 535802 539135 := bstep (se 1 (by rfl) ⟨404351, by rfl⟩ : syracuseStep 539135 = 808703) B808703
theorem B6900227 : Blo 535802 6900227 := bstep (se 1 (by rfl) ⟨5175170, by rfl⟩ : syracuseStep 6900227 = 10350341) B10350341
theorem B1363027 : Blo 535802 1363027 := bstep (se 1 (by rfl) ⟨1022270, by rfl⟩ : syracuseStep 1363027 = 2044541) B2044541
theorem B806399 : Blo 535802 806399 := bstep (se 1 (by rfl) ⟨604799, by rfl⟩ : syracuseStep 806399 = 1209599) B1209599
theorem B4083857 : Blo 535802 4083857 := bstep (se 2 (by rfl) ⟨1531446, by rfl⟩ : syracuseStep 4083857 = 3062893) B3062893
theorem B808319 : Blo 535802 808319 := bstep (se 1 (by rfl) ⟨606239, by rfl⟩ : syracuseStep 808319 = 1212479) B1212479
theorem B4090175 : Blo 535802 4090175 := bstep (se 1 (by rfl) ⟨3067631, by rfl⟩ : syracuseStep 4090175 = 6135263) B6135263
theorem B168160481 : Blo 535802 168160481 := bstep (se 2 (by rfl) ⟨63060180, by rfl⟩ : syracuseStep 168160481 = 126120361) B126120361
theorem B13037375 : Blo 535802 13037375 := bstep (se 1 (by rfl) ⟨9778031, by rfl⟩ : syracuseStep 13037375 = 19556063) B19556063
theorem B37679093 : Blo 535802 37679093 := bstep (se 5 (by rfl) ⟨1766207, by rfl⟩ : syracuseStep 37679093 = 3532415) B3532415
theorem B4093577 : Blo 535802 4093577 := bstep (se 2 (by rfl) ⟨1535091, by rfl⟩ : syracuseStep 4093577 = 3070183) B3070183
theorem B1210121 : Blo 535802 1210121 := bstep (se 2 (by rfl) ⟨453795, by rfl⟩ : syracuseStep 1210121 = 907591) B907591
theorem B11008655 : Blo 535802 11008655 := bstep (se 1 (by rfl) ⟨8256491, by rfl⟩ : syracuseStep 11008655 = 16512983) B16512983
theorem B2292455 : Blo 535802 2292455 := bstep (se 1 (by rfl) ⟨1719341, by rfl⟩ : syracuseStep 2292455 = 3438683) B3438683
theorem B23199695 : Blo 535802 23199695 := bstep (se 1 (by rfl) ⟨17399771, by rfl⟩ : syracuseStep 23199695 = 34799543) B34799543
theorem B2295803 : Blo 535802 2295803 := bstep (se 1 (by rfl) ⟨1721852, by rfl⟩ : syracuseStep 2295803 = 3443705) B3443705
theorem B2722571 : Blo 535802 2722571 := bstep (se 1 (by rfl) ⟨2041928, by rfl⟩ : syracuseStep 2722571 = 4083857) B4083857
theorem B2726783 : Blo 535802 2726783 := bstep (se 1 (by rfl) ⟨2045087, by rfl⟩ : syracuseStep 2726783 = 4090175) B4090175
theorem B2038891 : Blo 535802 2038891 := bstep (se 1 (by rfl) ⟨1529168, by rfl⟩ : syracuseStep 2038891 = 3058337) B3058337
theorem B112106987 : Blo 535802 112106987 := bstep (se 1 (by rfl) ⟨84080240, by rfl⟩ : syracuseStep 112106987 = 168160481) B168160481
theorem B8691583 : Blo 535802 8691583 := bstep (se 1 (by rfl) ⟨6518687, by rfl⟩ : syracuseStep 8691583 = 13037375) B13037375
theorem B2729051 : Blo 535802 2729051 := bstep (se 1 (by rfl) ⟨2046788, by rfl⟩ : syracuseStep 2729051 = 4093577) B4093577
theorem B4600151 : Blo 535802 4600151 := bstep (se 1 (by rfl) ⟨3450113, by rfl⟩ : syracuseStep 4600151 = 6900227) B6900227
theorem B537599 : Blo 535802 537599 := bstep (se 1 (by rfl) ⟨403199, by rfl⟩ : syracuseStep 537599 = 806399) B806399
theorem B538879 : Blo 535802 538879 := bstep (se 1 (by rfl) ⟨404159, by rfl⟩ : syracuseStep 538879 = 808319) B808319
theorem B1817369 : Blo 535802 1817369 := bstep (se 2 (by rfl) ⟨681513, by rfl⟩ : syracuseStep 1817369 = 1363027) B1363027
theorem B1820231 : Blo 535802 1820231 := bstep (se 1 (by rfl) ⟨1365173, by rfl⟩ : syracuseStep 1820231 = 2730347) B2730347
theorem B25119395 : Blo 535802 25119395 := bstep (se 1 (by rfl) ⟨18839546, by rfl⟩ : syracuseStep 25119395 = 37679093) B37679093
theorem B806747 : Blo 535802 806747 := bstep (se 1 (by rfl) ⟨605060, by rfl⟩ : syracuseStep 806747 = 1210121) B1210121
theorem B1528303 : Blo 535802 1528303 := bstep (se 1 (by rfl) ⟨1146227, by rfl⟩ : syracuseStep 1528303 = 2292455) B2292455
theorem B17459711 : Blo 535802 17459711 := bstep (se 1 (by rfl) ⟨13094783, by rfl⟩ : syracuseStep 17459711 = 26189567) B26189567
theorem B15559411 : Blo 535802 15559411 := bstep (se 1 (by rfl) ⟨11669558, by rfl⟩ : syracuseStep 15559411 = 23339117) B23339117
theorem B7339103 : Blo 535802 7339103 := bstep (se 1 (by rfl) ⟨5504327, by rfl⟩ : syracuseStep 7339103 = 11008655) B11008655
theorem B15466463 : Blo 535802 15466463 := bstep (se 1 (by rfl) ⟨11599847, by rfl⟩ : syracuseStep 15466463 = 23199695) B23199695
theorem B1213487 : Blo 535802 1213487 := bstep (se 1 (by rfl) ⟨910115, by rfl⟩ : syracuseStep 1213487 = 1820231) B1820231
theorem B16746263 : Blo 535802 16746263 := bstep (se 1 (by rfl) ⟨12559697, by rfl⟩ : syracuseStep 16746263 = 25119395) B25119395
theorem B20745881 : Blo 535802 20745881 := bstep (se 2 (by rfl) ⟨7779705, by rfl⟩ : syracuseStep 20745881 = 15559411) B15559411
theorem B2037737 : Blo 535802 2037737 := bstep (se 2 (by rfl) ⟨764151, by rfl⟩ : syracuseStep 2037737 = 1528303) B1528303
theorem B11639807 : Blo 535802 11639807 := bstep (se 1 (by rfl) ⟨8729855, by rfl⟩ : syracuseStep 11639807 = 17459711) B17459711
theorem B4892735 : Blo 535802 4892735 := bstep (se 1 (by rfl) ⟨3669551, by rfl⟩ : syracuseStep 4892735 = 7339103) B7339103
theorem B1815047 : Blo 535802 1815047 := bstep (se 1 (by rfl) ⟨1361285, by rfl⟩ : syracuseStep 1815047 = 2722571) B2722571
theorem B537831 : Blo 535802 537831 := bstep (se 1 (by rfl) ⟨403373, by rfl⟩ : syracuseStep 537831 = 806747) B806747
theorem B1817855 : Blo 535802 1817855 := bstep (se 1 (by rfl) ⟨1363391, by rfl⟩ : syracuseStep 1817855 = 2726783) B2726783
theorem B1819367 : Blo 535802 1819367 := bstep (se 1 (by rfl) ⟨1364525, by rfl⟩ : syracuseStep 1819367 = 2729051) B2729051
theorem B3066767 : Blo 535802 3066767 := bstep (se 1 (by rfl) ⟨2300075, by rfl⟩ : syracuseStep 3066767 = 4600151) B4600151
theorem B11588777 : Blo 535802 11588777 := bstep (se 2 (by rfl) ⟨4345791, by rfl⟩ : syracuseStep 11588777 = 8691583) B8691583
theorem B10310975 : Blo 535802 10310975 := bstep (se 1 (by rfl) ⟨7733231, by rfl⟩ : syracuseStep 10310975 = 15466463) B15466463
theorem B74737991 : Blo 535802 74737991 := bstep (se 1 (by rfl) ⟨56053493, by rfl⟩ : syracuseStep 74737991 = 112106987) B112106987
theorem B6122141 : Blo 535802 6122141 := bstep (se 3 (by rfl) ⟨1147901, by rfl⟩ : syracuseStep 6122141 = 2295803) B2295803
theorem B2718521 : Blo 535802 2718521 := bstep (se 2 (by rfl) ⟨1019445, by rfl⟩ : syracuseStep 2718521 = 2038891) B2038891
theorem B1211579 : Blo 535802 1211579 := bstep (se 1 (by rfl) ⟨908684, by rfl⟩ : syracuseStep 1211579 = 1817369) B1817369
theorem B1212911 : Blo 535802 1212911 := bstep (se 1 (by rfl) ⟨909683, by rfl⟩ : syracuseStep 1212911 = 1819367) B1819367
theorem B13830587 : Blo 535802 13830587 := bstep (se 1 (by rfl) ⟨10372940, by rfl⟩ : syracuseStep 13830587 = 20745881) B20745881
theorem B13047293 : Blo 535802 13047293 := bstep (se 3 (by rfl) ⟨2446367, by rfl⟩ : syracuseStep 13047293 = 4892735) B4892735
theorem B1812347 : Blo 535802 1812347 := bstep (se 1 (by rfl) ⟨1359260, by rfl⟩ : syracuseStep 1812347 = 2718521) B2718521
theorem B2044511 : Blo 535802 2044511 := bstep (se 1 (by rfl) ⟨1533383, by rfl⟩ : syracuseStep 2044511 = 3066767) B3066767
theorem B1358491 : Blo 535802 1358491 := bstep (se 1 (by rfl) ⟨1018868, by rfl⟩ : syracuseStep 1358491 = 2037737) B2037737
theorem B49825327 : Blo 535802 49825327 := bstep (se 1 (by rfl) ⟨37368995, by rfl⟩ : syracuseStep 49825327 = 74737991) B74737991
theorem B4081427 : Blo 535802 4081427 := bstep (se 1 (by rfl) ⟨3061070, by rfl⟩ : syracuseStep 4081427 = 6122141) B6122141
theorem B807719 : Blo 535802 807719 := bstep (se 1 (by rfl) ⟨605789, by rfl⟩ : syracuseStep 807719 = 1211579) B1211579
theorem B808991 : Blo 535802 808991 := bstep (se 1 (by rfl) ⟨606743, by rfl⟩ : syracuseStep 808991 = 1213487) B1213487
theorem B11164175 : Blo 535802 11164175 := bstep (se 1 (by rfl) ⟨8373131, by rfl⟩ : syracuseStep 11164175 = 16746263) B16746263
theorem B7725851 : Blo 535802 7725851 := bstep (se 1 (by rfl) ⟨5794388, by rfl⟩ : syracuseStep 7725851 = 11588777) B11588777
theorem B6873983 : Blo 535802 6873983 := bstep (se 1 (by rfl) ⟨5155487, by rfl⟩ : syracuseStep 6873983 = 10310975) B10310975
theorem B7759871 : Blo 535802 7759871 := bstep (se 1 (by rfl) ⟨5819903, by rfl⟩ : syracuseStep 7759871 = 11639807) B11639807
theorem B1210031 : Blo 535802 1210031 := bstep (se 1 (by rfl) ⟨907523, by rfl⟩ : syracuseStep 1210031 = 1815047) B1815047
theorem B1211903 : Blo 535802 1211903 := bstep (se 1 (by rfl) ⟨908927, by rfl⟩ : syracuseStep 1211903 = 1817855) B1817855
theorem B2720951 : Blo 535802 2720951 := bstep (se 1 (by rfl) ⟨2040713, by rfl⟩ : syracuseStep 2720951 = 4081427) B4081427
theorem B7442783 : Blo 535802 7442783 := bstep (se 1 (by rfl) ⟨5582087, by rfl⟩ : syracuseStep 7442783 = 11164175) B11164175
theorem B5150567 : Blo 535802 5150567 := bstep (se 1 (by rfl) ⟨3862925, by rfl⟩ : syracuseStep 5150567 = 7725851) B7725851
theorem B1811321 : Blo 535802 1811321 := bstep (se 2 (by rfl) ⟨679245, by rfl⟩ : syracuseStep 1811321 = 1358491) B1358491
theorem B9220391 : Blo 535802 9220391 := bstep (se 1 (by rfl) ⟨6915293, by rfl⟩ : syracuseStep 9220391 = 13830587) B13830587
theorem B66433769 : Blo 535802 66433769 := bstep (se 2 (by rfl) ⟨24912663, by rfl⟩ : syracuseStep 66433769 = 49825327) B49825327
theorem B538479 : Blo 535802 538479 := bstep (se 1 (by rfl) ⟨403859, by rfl⟩ : syracuseStep 538479 = 807719) B807719
theorem B8698195 : Blo 535802 8698195 := bstep (se 1 (by rfl) ⟨6523646, by rfl⟩ : syracuseStep 8698195 = 13047293) B13047293
theorem B539327 : Blo 535802 539327 := bstep (se 1 (by rfl) ⟨404495, by rfl⟩ : syracuseStep 539327 = 808991) B808991
theorem B1363007 : Blo 535802 1363007 := bstep (se 1 (by rfl) ⟨1022255, by rfl⟩ : syracuseStep 1363007 = 2044511) B2044511
theorem B806687 : Blo 535802 806687 := bstep (se 1 (by rfl) ⟨605015, by rfl⟩ : syracuseStep 806687 = 1210031) B1210031
theorem B807935 : Blo 535802 807935 := bstep (se 1 (by rfl) ⟨605951, by rfl⟩ : syracuseStep 807935 = 1211903) B1211903
theorem B808607 : Blo 535802 808607 := bstep (se 1 (by rfl) ⟨606455, by rfl⟩ : syracuseStep 808607 = 1212911) B1212911
theorem B4582655 : Blo 535802 4582655 := bstep (se 1 (by rfl) ⟨3436991, by rfl⟩ : syracuseStep 4582655 = 6873983) B6873983
theorem B1208231 : Blo 535802 1208231 := bstep (se 1 (by rfl) ⟨906173, by rfl⟩ : syracuseStep 1208231 = 1812347) B1812347
theorem B5173247 : Blo 535802 5173247 := bstep (se 1 (by rfl) ⟨3879935, by rfl⟩ : syracuseStep 5173247 = 7759871) B7759871
theorem B3055103 : Blo 535802 3055103 := bstep (se 1 (by rfl) ⟨2291327, by rfl⟩ : syracuseStep 3055103 = 4582655) B4582655
theorem B3448831 : Blo 535802 3448831 := bstep (se 1 (by rfl) ⟨2586623, by rfl⟩ : syracuseStep 3448831 = 5173247) B5173247
theorem B1813967 : Blo 535802 1813967 := bstep (se 1 (by rfl) ⟨1360475, by rfl⟩ : syracuseStep 1813967 = 2720951) B2720951
theorem B537791 : Blo 535802 537791 := bstep (se 1 (by rfl) ⟨403343, by rfl⟩ : syracuseStep 537791 = 806687) B806687
theorem B4961855 : Blo 535802 4961855 := bstep (se 1 (by rfl) ⟨3721391, by rfl⟩ : syracuseStep 4961855 = 7442783) B7442783
theorem B538623 : Blo 535802 538623 := bstep (se 1 (by rfl) ⟨403967, by rfl⟩ : syracuseStep 538623 = 807935) B807935
theorem B539071 : Blo 535802 539071 := bstep (se 1 (by rfl) ⟨404303, by rfl⟩ : syracuseStep 539071 = 808607) B808607
theorem B805487 : Blo 535802 805487 := bstep (se 1 (by rfl) ⟨604115, by rfl⟩ : syracuseStep 805487 = 1208231) B1208231
theorem B6146927 : Blo 535802 6146927 := bstep (se 1 (by rfl) ⟨4610195, by rfl⟩ : syracuseStep 6146927 = 9220391) B9220391
theorem B44289179 : Blo 535802 44289179 := bstep (se 1 (by rfl) ⟨33216884, by rfl⟩ : syracuseStep 44289179 = 66433769) B66433769
theorem B908671 : Blo 535802 908671 := bstep (se 1 (by rfl) ⟨681503, by rfl⟩ : syracuseStep 908671 = 1363007) B1363007
theorem B3433711 : Blo 535802 3433711 := bstep (se 1 (by rfl) ⟨2575283, by rfl⟩ : syracuseStep 3433711 = 5150567) B5150567
theorem B1207547 : Blo 535802 1207547 := bstep (se 1 (by rfl) ⟨905660, by rfl⟩ : syracuseStep 1207547 = 1811321) B1811321
theorem B11597593 : Blo 535802 11597593 := bstep (se 2 (by rfl) ⟨4349097, by rfl⟩ : syracuseStep 11597593 = 8698195) B8698195
theorem B4097951 : Blo 535802 4097951 := bstep (se 1 (by rfl) ⟨3073463, by rfl⟩ : syracuseStep 4097951 = 6146927) B6146927
theorem B29526119 : Blo 535802 29526119 := bstep (se 1 (by rfl) ⟨22144589, by rfl⟩ : syracuseStep 29526119 = 44289179) B44289179
theorem B2036735 : Blo 535802 2036735 := bstep (se 1 (by rfl) ⟨1527551, by rfl⟩ : syracuseStep 2036735 = 3055103) B3055103
theorem B4598441 : Blo 535802 4598441 := bstep (se 2 (by rfl) ⟨1724415, by rfl⟩ : syracuseStep 4598441 = 3448831) B3448831
theorem B536991 : Blo 535802 536991 := bstep (se 1 (by rfl) ⟨402743, by rfl⟩ : syracuseStep 536991 = 805487) B805487
theorem B805031 : Blo 535802 805031 := bstep (se 1 (by rfl) ⟨603773, by rfl⟩ : syracuseStep 805031 = 1207547) B1207547
theorem B4578281 : Blo 535802 4578281 := bstep (se 2 (by rfl) ⟨1716855, by rfl⟩ : syracuseStep 4578281 = 3433711) B3433711
theorem B13231613 : Blo 535802 13231613 := bstep (se 3 (by rfl) ⟨2480927, by rfl⟩ : syracuseStep 13231613 = 4961855) B4961855
theorem B1209311 : Blo 535802 1209311 := bstep (se 1 (by rfl) ⟨906983, by rfl⟩ : syracuseStep 1209311 = 1813967) B1813967
theorem B15463457 : Blo 535802 15463457 := bstep (se 2 (by rfl) ⟨5798796, by rfl⟩ : syracuseStep 15463457 = 11597593) B11597593
theorem B1211561 : Blo 535802 1211561 := bstep (se 2 (by rfl) ⟨454335, by rfl⟩ : syracuseStep 1211561 = 908671) B908671
theorem B3052187 : Blo 535802 3052187 := bstep (se 1 (by rfl) ⟨2289140, by rfl⟩ : syracuseStep 3052187 = 4578281) B4578281
theorem B2731967 : Blo 535802 2731967 := bstep (se 1 (by rfl) ⟨2048975, by rfl⟩ : syracuseStep 2731967 = 4097951) B4097951
theorem B536687 : Blo 535802 536687 := bstep (se 1 (by rfl) ⟨402515, by rfl⟩ : syracuseStep 536687 = 805031) B805031
theorem B1357823 : Blo 535802 1357823 := bstep (se 1 (by rfl) ⟨1018367, by rfl⟩ : syracuseStep 1357823 = 2036735) B2036735
theorem B3065627 : Blo 535802 3065627 := bstep (se 1 (by rfl) ⟨2299220, by rfl⟩ : syracuseStep 3065627 = 4598441) B4598441
theorem B806207 : Blo 535802 806207 := bstep (se 1 (by rfl) ⟨604655, by rfl⟩ : syracuseStep 806207 = 1209311) B1209311
theorem B10308971 : Blo 535802 10308971 := bstep (se 1 (by rfl) ⟨7731728, by rfl⟩ : syracuseStep 10308971 = 15463457) B15463457
theorem B807707 : Blo 535802 807707 := bstep (se 1 (by rfl) ⟨605780, by rfl⟩ : syracuseStep 807707 = 1211561) B1211561
theorem B19684079 : Blo 535802 19684079 := bstep (se 1 (by rfl) ⟨14763059, by rfl⟩ : syracuseStep 19684079 = 29526119) B29526119
theorem B35284301 : Blo 535802 35284301 := bstep (se 3 (by rfl) ⟨6615806, by rfl⟩ : syracuseStep 35284301 = 13231613) B13231613
theorem B2034791 : Blo 535802 2034791 := bstep (se 1 (by rfl) ⟨1526093, by rfl⟩ : syracuseStep 2034791 = 3052187) B3052187
theorem B2043751 : Blo 535802 2043751 := bstep (se 1 (by rfl) ⟨1532813, by rfl⟩ : syracuseStep 2043751 = 3065627) B3065627
theorem B537471 : Blo 535802 537471 := bstep (se 1 (by rfl) ⟨403103, by rfl⟩ : syracuseStep 537471 = 806207) B806207
theorem B538471 : Blo 535802 538471 := bstep (se 1 (by rfl) ⟨403853, by rfl⟩ : syracuseStep 538471 = 807707) B807707
theorem B13122719 : Blo 535802 13122719 := bstep (se 1 (by rfl) ⟨9842039, by rfl⟩ : syracuseStep 13122719 = 19684079) B19684079
theorem B1821311 : Blo 535802 1821311 := bstep (se 1 (by rfl) ⟨1365983, by rfl⟩ : syracuseStep 1821311 = 2731967) B2731967
theorem B905215 : Blo 535802 905215 := bstep (se 1 (by rfl) ⟨678911, by rfl⟩ : syracuseStep 905215 = 1357823) B1357823
theorem B6872647 : Blo 535802 6872647 := bstep (se 1 (by rfl) ⟨5154485, by rfl⟩ : syracuseStep 6872647 = 10308971) B10308971
theorem B23522867 : Blo 535802 23522867 := bstep (se 1 (by rfl) ⟨17642150, by rfl⟩ : syracuseStep 23522867 = 35284301) B35284301
theorem B1214207 : Blo 535802 1214207 := bstep (se 1 (by rfl) ⟨910655, by rfl⟩ : syracuseStep 1214207 = 1821311) B1821311
theorem B2725001 : Blo 535802 2725001 := bstep (se 2 (by rfl) ⟨1021875, by rfl⟩ : syracuseStep 2725001 = 2043751) B2043751
theorem B250910581 : Blo 535802 250910581 := bstep (se 5 (by rfl) ⟨11761433, by rfl⟩ : syracuseStep 250910581 = 23522867) B23522867
theorem B1356527 : Blo 535802 1356527 := bstep (se 1 (by rfl) ⟨1017395, by rfl⟩ : syracuseStep 1356527 = 2034791) B2034791
theorem B9163529 : Blo 535802 9163529 := bstep (se 2 (by rfl) ⟨3436323, by rfl⟩ : syracuseStep 9163529 = 6872647) B6872647
theorem B1206953 : Blo 535802 1206953 := bstep (se 2 (by rfl) ⟨452607, by rfl⟩ : syracuseStep 1206953 = 905215) B905215
theorem B8748479 : Blo 535802 8748479 := bstep (se 1 (by rfl) ⟨6561359, by rfl⟩ : syracuseStep 8748479 = 13122719) B13122719
theorem B6109019 : Blo 535802 6109019 := bstep (se 1 (by rfl) ⟨4581764, by rfl⟩ : syracuseStep 6109019 = 9163529) B9163529
theorem B1816667 : Blo 535802 1816667 := bstep (se 1 (by rfl) ⟨1362500, by rfl⟩ : syracuseStep 1816667 = 2725001) B2725001
theorem B804635 : Blo 535802 804635 := bstep (se 1 (by rfl) ⟨603476, by rfl⟩ : syracuseStep 804635 = 1206953) B1206953
theorem B334547441 : Blo 535802 334547441 := bstep (se 2 (by rfl) ⟨125455290, by rfl⟩ : syracuseStep 334547441 = 250910581) B250910581
theorem B904351 : Blo 535802 904351 := bstep (se 1 (by rfl) ⟨678263, by rfl⟩ : syracuseStep 904351 = 1356527) B1356527
theorem B809471 : Blo 535802 809471 := bstep (se 1 (by rfl) ⟨607103, by rfl⟩ : syracuseStep 809471 = 1214207) B1214207
theorem B5832319 : Blo 535802 5832319 := bstep (se 1 (by rfl) ⟨4374239, by rfl⟩ : syracuseStep 5832319 = 8748479) B8748479
theorem B4072679 : Blo 535802 4072679 := bstep (se 1 (by rfl) ⟨3054509, by rfl⟩ : syracuseStep 4072679 = 6109019) B6109019
theorem B7776425 : Blo 535802 7776425 := bstep (se 2 (by rfl) ⟨2916159, by rfl⟩ : syracuseStep 7776425 = 5832319) B5832319
theorem B536423 : Blo 535802 536423 := bstep (se 1 (by rfl) ⟨402317, by rfl⟩ : syracuseStep 536423 = 804635) B804635
theorem B223031627 : Blo 535802 223031627 := bstep (se 1 (by rfl) ⟨167273720, by rfl⟩ : syracuseStep 223031627 = 334547441) B334547441
theorem B539647 : Blo 535802 539647 := bstep (se 1 (by rfl) ⟨404735, by rfl⟩ : syracuseStep 539647 = 809471) B809471
theorem B1205801 : Blo 535802 1205801 := bstep (se 2 (by rfl) ⟨452175, by rfl⟩ : syracuseStep 1205801 = 904351) B904351
theorem B1211111 : Blo 535802 1211111 := bstep (se 1 (by rfl) ⟨908333, by rfl⟩ : syracuseStep 1211111 = 1816667) B1816667
theorem B5184283 : Blo 535802 5184283 := bstep (se 1 (by rfl) ⟨3888212, by rfl⟩ : syracuseStep 5184283 = 7776425) B7776425
theorem B803867 : Blo 535802 803867 := bstep (se 1 (by rfl) ⟨602900, by rfl⟩ : syracuseStep 803867 = 1205801) B1205801
theorem B148687751 : Blo 535802 148687751 := bstep (se 1 (by rfl) ⟨111515813, by rfl⟩ : syracuseStep 148687751 = 223031627) B223031627
theorem B807407 : Blo 535802 807407 := bstep (se 1 (by rfl) ⟨605555, by rfl⟩ : syracuseStep 807407 = 1211111) B1211111
theorem B2715119 : Blo 535802 2715119 := bstep (se 1 (by rfl) ⟨2036339, by rfl⟩ : syracuseStep 2715119 = 4072679) B4072679
theorem B99125167 : Blo 535802 99125167 := bstep (se 1 (by rfl) ⟨74343875, by rfl⟩ : syracuseStep 99125167 = 148687751) B148687751
theorem B1810079 : Blo 535802 1810079 := bstep (se 1 (by rfl) ⟨1357559, by rfl⟩ : syracuseStep 1810079 = 2715119) B2715119
theorem B535911 : Blo 535802 535911 := bstep (se 1 (by rfl) ⟨401933, by rfl⟩ : syracuseStep 535911 = 803867) B803867
theorem B538271 : Blo 535802 538271 := bstep (se 1 (by rfl) ⟨403703, by rfl⟩ : syracuseStep 538271 = 807407) B807407
theorem B6912377 : Blo 535802 6912377 := bstep (se 2 (by rfl) ⟨2592141, by rfl⟩ : syracuseStep 6912377 = 5184283) B5184283
theorem B132166889 : Blo 535802 132166889 := bstep (se 2 (by rfl) ⟨49562583, by rfl⟩ : syracuseStep 132166889 = 99125167) B99125167
theorem B4608251 : Blo 535802 4608251 := bstep (se 1 (by rfl) ⟨3456188, by rfl⟩ : syracuseStep 4608251 = 6912377) B6912377
theorem B1206719 : Blo 535802 1206719 := bstep (se 1 (by rfl) ⟨905039, by rfl⟩ : syracuseStep 1206719 = 1810079) B1810079
theorem B804479 : Blo 535802 804479 := bstep (se 1 (by rfl) ⟨603359, by rfl⟩ : syracuseStep 804479 = 1206719) B1206719
theorem B3072167 : Blo 535802 3072167 := bstep (se 1 (by rfl) ⟨2304125, by rfl⟩ : syracuseStep 3072167 = 4608251) B4608251
theorem B88111259 : Blo 535802 88111259 := bstep (se 1 (by rfl) ⟨66083444, by rfl⟩ : syracuseStep 88111259 = 132166889) B132166889
theorem B536319 : Blo 535802 536319 := bstep (se 1 (by rfl) ⟨402239, by rfl⟩ : syracuseStep 536319 = 804479) B804479
theorem B2048111 : Blo 535802 2048111 := bstep (se 1 (by rfl) ⟨1536083, by rfl⟩ : syracuseStep 2048111 = 3072167) B3072167
theorem B58740839 : Blo 535802 58740839 := bstep (se 1 (by rfl) ⟨44055629, by rfl⟩ : syracuseStep 58740839 = 88111259) B88111259
theorem B39160559 : Blo 535802 39160559 := bstep (se 1 (by rfl) ⟨29370419, by rfl⟩ : syracuseStep 39160559 = 58740839) B58740839
theorem B1365407 : Blo 535802 1365407 := bstep (se 1 (by rfl) ⟨1024055, by rfl⟩ : syracuseStep 1365407 = 2048111) B2048111
theorem B26107039 : Blo 535802 26107039 := bstep (se 1 (by rfl) ⟨19580279, by rfl⟩ : syracuseStep 26107039 = 39160559) B39160559
theorem B910271 : Blo 535802 910271 := bstep (se 1 (by rfl) ⟨682703, by rfl⟩ : syracuseStep 910271 = 1365407) B1365407
theorem B34809385 : Blo 535802 34809385 := bstep (se 2 (by rfl) ⟨13053519, by rfl⟩ : syracuseStep 34809385 = 26107039) B26107039
theorem B606847 : Blo 535802 606847 := bstep (se 1 (by rfl) ⟨455135, by rfl⟩ : syracuseStep 606847 = 910271) B910271
theorem B46412513 : Blo 535802 46412513 := bstep (se 2 (by rfl) ⟨17404692, by rfl⟩ : syracuseStep 46412513 = 34809385) B34809385
theorem B809129 : Blo 535802 809129 := bstep (se 2 (by rfl) ⟨303423, by rfl⟩ : syracuseStep 809129 = 606847) B606847
theorem B30941675 : Blo 535802 30941675 := bstep (se 1 (by rfl) ⟨23206256, by rfl⟩ : syracuseStep 30941675 = 46412513) B46412513
theorem B539419 : Blo 535802 539419 := bstep (se 1 (by rfl) ⟨404564, by rfl⟩ : syracuseStep 539419 = 809129) B809129
theorem B20627783 : Blo 535802 20627783 := bstep (se 1 (by rfl) ⟨15470837, by rfl⟩ : syracuseStep 20627783 = 30941675) B30941675
theorem B13751855 : Blo 535802 13751855 := bstep (se 1 (by rfl) ⟨10313891, by rfl⟩ : syracuseStep 13751855 = 20627783) B20627783
theorem B9167903 : Blo 535802 9167903 := bstep (se 1 (by rfl) ⟨6875927, by rfl⟩ : syracuseStep 9167903 = 13751855) B13751855
theorem B6111935 : Blo 535802 6111935 := bstep (se 1 (by rfl) ⟨4583951, by rfl⟩ : syracuseStep 6111935 = 9167903) B9167903
theorem B4074623 : Blo 535802 4074623 := bstep (se 1 (by rfl) ⟨3055967, by rfl⟩ : syracuseStep 4074623 = 6111935) B6111935
theorem B2716415 : Blo 535802 2716415 := bstep (se 1 (by rfl) ⟨2037311, by rfl⟩ : syracuseStep 2716415 = 4074623) B4074623
theorem B1810943 : Blo 535802 1810943 := bstep (se 1 (by rfl) ⟨1358207, by rfl⟩ : syracuseStep 1810943 = 2716415) B2716415
theorem B1207295 : Blo 535802 1207295 := bstep (se 1 (by rfl) ⟨905471, by rfl⟩ : syracuseStep 1207295 = 1810943) B1810943
theorem B804863 : Blo 535802 804863 := bstep (se 1 (by rfl) ⟨603647, by rfl⟩ : syracuseStep 804863 = 1207295) B1207295
theorem B536575 : Blo 535802 536575 := bstep (se 1 (by rfl) ⟨402431, by rfl⟩ : syracuseStep 536575 = 804863) B804863

theorem C0 (j : ℕ) (h1 : 133950 ≤ j) (h2 : j ≤ 134649) : Blo 535802 (4 * j + 3) := by
  interval_cases j
  · exact B535803
  · exact B535807
  · exact B535811
  · exact B535815
  · exact B535819
  · exact B535823
  · exact B535827
  · exact B535831
  · exact B535835
  · exact B535839
  · exact B535843
  · exact B535847
  · exact B535851
  · exact B535855
  · exact B535859
  · exact B535863
  · exact B535867
  · exact B535871
  · exact B535875
  · exact B535879
  · exact B535883
  · exact B535887
  · exact B535891
  · exact B535895
  · exact B535899
  · exact B535903
  · exact B535907
  · exact B535911
  · exact B535915
  · exact B535919
  · exact B535923
  · exact B535927
  · exact B535931
  · exact B535935
  · exact B535939
  · exact B535943
  · exact B535947
  · exact B535951
  · exact B535955
  · exact B535959
  · exact B535963
  · exact B535967
  · exact B535971
  · exact B535975
  · exact B535979
  · exact B535983
  · exact B535987
  · exact B535991
  · exact B535995
  · exact B535999
  · exact B536003
  · exact B536007
  · exact B536011
  · exact B536015
  · exact B536019
  · exact B536023
  · exact B536027
  · exact B536031
  · exact B536035
  · exact B536039
  · exact B536043
  · exact B536047
  · exact B536051
  · exact B536055
  · exact B536059
  · exact B536063
  · exact B536067
  · exact B536071
  · exact B536075
  · exact B536079
  · exact B536083
  · exact B536087
  · exact B536091
  · exact B536095
  · exact B536099
  · exact B536103
  · exact B536107
  · exact B536111
  · exact B536115
  · exact B536119
  · exact B536123
  · exact B536127
  · exact B536131
  · exact B536135
  · exact B536139
  · exact B536143
  · exact B536147
  · exact B536151
  · exact B536155
  · exact B536159
  · exact B536163
  · exact B536167
  · exact B536171
  · exact B536175
  · exact B536179
  · exact B536183
  · exact B536187
  · exact B536191
  · exact B536195
  · exact B536199
  · exact B536203
  · exact B536207
  · exact B536211
  · exact B536215
  · exact B536219
  · exact B536223
  · exact B536227
  · exact B536231
  · exact B536235
  · exact B536239
  · exact B536243
  · exact B536247
  · exact B536251
  · exact B536255
  · exact B536259
  · exact B536263
  · exact B536267
  · exact B536271
  · exact B536275
  · exact B536279
  · exact B536283
  · exact B536287
  · exact B536291
  · exact B536295
  · exact B536299
  · exact B536303
  · exact B536307
  · exact B536311
  · exact B536315
  · exact B536319
  · exact B536323
  · exact B536327
  · exact B536331
  · exact B536335
  · exact B536339
  · exact B536343
  · exact B536347
  · exact B536351
  · exact B536355
  · exact B536359
  · exact B536363
  · exact B536367
  · exact B536371
  · exact B536375
  · exact B536379
  · exact B536383
  · exact B536387
  · exact B536391
  · exact B536395
  · exact B536399
  · exact B536403
  · exact B536407
  · exact B536411
  · exact B536415
  · exact B536419
  · exact B536423
  · exact B536427
  · exact B536431
  · exact B536435
  · exact B536439
  · exact B536443
  · exact B536447
  · exact B536451
  · exact B536455
  · exact B536459
  · exact B536463
  · exact B536467
  · exact B536471
  · exact B536475
  · exact B536479
  · exact B536483
  · exact B536487
  · exact B536491
  · exact B536495
  · exact B536499
  · exact B536503
  · exact B536507
  · exact B536511
  · exact B536515
  · exact B536519
  · exact B536523
  · exact B536527
  · exact B536531
  · exact B536535
  · exact B536539
  · exact B536543
  · exact B536547
  · exact B536551
  · exact B536555
  · exact B536559
  · exact B536563
  · exact B536567
  · exact B536571
  · exact B536575
  · exact B536579
  · exact B536583
  · exact B536587
  · exact B536591
  · exact B536595
  · exact B536599
  · exact B536603
  · exact B536607
  · exact B536611
  · exact B536615
  · exact B536619
  · exact B536623
  · exact B536627
  · exact B536631
  · exact B536635
  · exact B536639
  · exact B536643
  · exact B536647
  · exact B536651
  · exact B536655
  · exact B536659
  · exact B536663
  · exact B536667
  · exact B536671
  · exact B536675
  · exact B536679
  · exact B536683
  · exact B536687
  · exact B536691
  · exact B536695
  · exact B536699
  · exact B536703
  · exact B536707
  · exact B536711
  · exact B536715
  · exact B536719
  · exact B536723
  · exact B536727
  · exact B536731
  · exact B536735
  · exact B536739
  · exact B536743
  · exact B536747
  · exact B536751
  · exact B536755
  · exact B536759
  · exact B536763
  · exact B536767
  · exact B536771
  · exact B536775
  · exact B536779
  · exact B536783
  · exact B536787
  · exact B536791
  · exact B536795
  · exact B536799
  · exact B536803
  · exact B536807
  · exact B536811
  · exact B536815
  · exact B536819
  · exact B536823
  · exact B536827
  · exact B536831
  · exact B536835
  · exact B536839
  · exact B536843
  · exact B536847
  · exact B536851
  · exact B536855
  · exact B536859
  · exact B536863
  · exact B536867
  · exact B536871
  · exact B536875
  · exact B536879
  · exact B536883
  · exact B536887
  · exact B536891
  · exact B536895
  · exact B536899
  · exact B536903
  · exact B536907
  · exact B536911
  · exact B536915
  · exact B536919
  · exact B536923
  · exact B536927
  · exact B536931
  · exact B536935
  · exact B536939
  · exact B536943
  · exact B536947
  · exact B536951
  · exact B536955
  · exact B536959
  · exact B536963
  · exact B536967
  · exact B536971
  · exact B536975
  · exact B536979
  · exact B536983
  · exact B536987
  · exact B536991
  · exact B536995
  · exact B536999
  · exact B537003
  · exact B537007
  · exact B537011
  · exact B537015
  · exact B537019
  · exact B537023
  · exact B537027
  · exact B537031
  · exact B537035
  · exact B537039
  · exact B537043
  · exact B537047
  · exact B537051
  · exact B537055
  · exact B537059
  · exact B537063
  · exact B537067
  · exact B537071
  · exact B537075
  · exact B537079
  · exact B537083
  · exact B537087
  · exact B537091
  · exact B537095
  · exact B537099
  · exact B537103
  · exact B537107
  · exact B537111
  · exact B537115
  · exact B537119
  · exact B537123
  · exact B537127
  · exact B537131
  · exact B537135
  · exact B537139
  · exact B537143
  · exact B537147
  · exact B537151
  · exact B537155
  · exact B537159
  · exact B537163
  · exact B537167
  · exact B537171
  · exact B537175
  · exact B537179
  · exact B537183
  · exact B537187
  · exact B537191
  · exact B537195
  · exact B537199
  · exact B537203
  · exact B537207
  · exact B537211
  · exact B537215
  · exact B537219
  · exact B537223
  · exact B537227
  · exact B537231
  · exact B537235
  · exact B537239
  · exact B537243
  · exact B537247
  · exact B537251
  · exact B537255
  · exact B537259
  · exact B537263
  · exact B537267
  · exact B537271
  · exact B537275
  · exact B537279
  · exact B537283
  · exact B537287
  · exact B537291
  · exact B537295
  · exact B537299
  · exact B537303
  · exact B537307
  · exact B537311
  · exact B537315
  · exact B537319
  · exact B537323
  · exact B537327
  · exact B537331
  · exact B537335
  · exact B537339
  · exact B537343
  · exact B537347
  · exact B537351
  · exact B537355
  · exact B537359
  · exact B537363
  · exact B537367
  · exact B537371
  · exact B537375
  · exact B537379
  · exact B537383
  · exact B537387
  · exact B537391
  · exact B537395
  · exact B537399
  · exact B537403
  · exact B537407
  · exact B537411
  · exact B537415
  · exact B537419
  · exact B537423
  · exact B537427
  · exact B537431
  · exact B537435
  · exact B537439
  · exact B537443
  · exact B537447
  · exact B537451
  · exact B537455
  · exact B537459
  · exact B537463
  · exact B537467
  · exact B537471
  · exact B537475
  · exact B537479
  · exact B537483
  · exact B537487
  · exact B537491
  · exact B537495
  · exact B537499
  · exact B537503
  · exact B537507
  · exact B537511
  · exact B537515
  · exact B537519
  · exact B537523
  · exact B537527
  · exact B537531
  · exact B537535
  · exact B537539
  · exact B537543
  · exact B537547
  · exact B537551
  · exact B537555
  · exact B537559
  · exact B537563
  · exact B537567
  · exact B537571
  · exact B537575
  · exact B537579
  · exact B537583
  · exact B537587
  · exact B537591
  · exact B537595
  · exact B537599
  · exact B537603
  · exact B537607
  · exact B537611
  · exact B537615
  · exact B537619
  · exact B537623
  · exact B537627
  · exact B537631
  · exact B537635
  · exact B537639
  · exact B537643
  · exact B537647
  · exact B537651
  · exact B537655
  · exact B537659
  · exact B537663
  · exact B537667
  · exact B537671
  · exact B537675
  · exact B537679
  · exact B537683
  · exact B537687
  · exact B537691
  · exact B537695
  · exact B537699
  · exact B537703
  · exact B537707
  · exact B537711
  · exact B537715
  · exact B537719
  · exact B537723
  · exact B537727
  · exact B537731
  · exact B537735
  · exact B537739
  · exact B537743
  · exact B537747
  · exact B537751
  · exact B537755
  · exact B537759
  · exact B537763
  · exact B537767
  · exact B537771
  · exact B537775
  · exact B537779
  · exact B537783
  · exact B537787
  · exact B537791
  · exact B537795
  · exact B537799
  · exact B537803
  · exact B537807
  · exact B537811
  · exact B537815
  · exact B537819
  · exact B537823
  · exact B537827
  · exact B537831
  · exact B537835
  · exact B537839
  · exact B537843
  · exact B537847
  · exact B537851
  · exact B537855
  · exact B537859
  · exact B537863
  · exact B537867
  · exact B537871
  · exact B537875
  · exact B537879
  · exact B537883
  · exact B537887
  · exact B537891
  · exact B537895
  · exact B537899
  · exact B537903
  · exact B537907
  · exact B537911
  · exact B537915
  · exact B537919
  · exact B537923
  · exact B537927
  · exact B537931
  · exact B537935
  · exact B537939
  · exact B537943
  · exact B537947
  · exact B537951
  · exact B537955
  · exact B537959
  · exact B537963
  · exact B537967
  · exact B537971
  · exact B537975
  · exact B537979
  · exact B537983
  · exact B537987
  · exact B537991
  · exact B537995
  · exact B537999
  · exact B538003
  · exact B538007
  · exact B538011
  · exact B538015
  · exact B538019
  · exact B538023
  · exact B538027
  · exact B538031
  · exact B538035
  · exact B538039
  · exact B538043
  · exact B538047
  · exact B538051
  · exact B538055
  · exact B538059
  · exact B538063
  · exact B538067
  · exact B538071
  · exact B538075
  · exact B538079
  · exact B538083
  · exact B538087
  · exact B538091
  · exact B538095
  · exact B538099
  · exact B538103
  · exact B538107
  · exact B538111
  · exact B538115
  · exact B538119
  · exact B538123
  · exact B538127
  · exact B538131
  · exact B538135
  · exact B538139
  · exact B538143
  · exact B538147
  · exact B538151
  · exact B538155
  · exact B538159
  · exact B538163
  · exact B538167
  · exact B538171
  · exact B538175
  · exact B538179
  · exact B538183
  · exact B538187
  · exact B538191
  · exact B538195
  · exact B538199
  · exact B538203
  · exact B538207
  · exact B538211
  · exact B538215
  · exact B538219
  · exact B538223
  · exact B538227
  · exact B538231
  · exact B538235
  · exact B538239
  · exact B538243
  · exact B538247
  · exact B538251
  · exact B538255
  · exact B538259
  · exact B538263
  · exact B538267
  · exact B538271
  · exact B538275
  · exact B538279
  · exact B538283
  · exact B538287
  · exact B538291
  · exact B538295
  · exact B538299
  · exact B538303
  · exact B538307
  · exact B538311
  · exact B538315
  · exact B538319
  · exact B538323
  · exact B538327
  · exact B538331
  · exact B538335
  · exact B538339
  · exact B538343
  · exact B538347
  · exact B538351
  · exact B538355
  · exact B538359
  · exact B538363
  · exact B538367
  · exact B538371
  · exact B538375
  · exact B538379
  · exact B538383
  · exact B538387
  · exact B538391
  · exact B538395
  · exact B538399
  · exact B538403
  · exact B538407
  · exact B538411
  · exact B538415
  · exact B538419
  · exact B538423
  · exact B538427
  · exact B538431
  · exact B538435
  · exact B538439
  · exact B538443
  · exact B538447
  · exact B538451
  · exact B538455
  · exact B538459
  · exact B538463
  · exact B538467
  · exact B538471
  · exact B538475
  · exact B538479
  · exact B538483
  · exact B538487
  · exact B538491
  · exact B538495
  · exact B538499
  · exact B538503
  · exact B538507
  · exact B538511
  · exact B538515
  · exact B538519
  · exact B538523
  · exact B538527
  · exact B538531
  · exact B538535
  · exact B538539
  · exact B538543
  · exact B538547
  · exact B538551
  · exact B538555
  · exact B538559
  · exact B538563
  · exact B538567
  · exact B538571
  · exact B538575
  · exact B538579
  · exact B538583
  · exact B538587
  · exact B538591
  · exact B538595
  · exact B538599

theorem C1 (j : ℕ) (h1 : 134650 ≤ j) (h2 : j ≤ 134949) : Blo 535802 (4 * j + 3) := by
  interval_cases j
  · exact B538603
  · exact B538607
  · exact B538611
  · exact B538615
  · exact B538619
  · exact B538623
  · exact B538627
  · exact B538631
  · exact B538635
  · exact B538639
  · exact B538643
  · exact B538647
  · exact B538651
  · exact B538655
  · exact B538659
  · exact B538663
  · exact B538667
  · exact B538671
  · exact B538675
  · exact B538679
  · exact B538683
  · exact B538687
  · exact B538691
  · exact B538695
  · exact B538699
  · exact B538703
  · exact B538707
  · exact B538711
  · exact B538715
  · exact B538719
  · exact B538723
  · exact B538727
  · exact B538731
  · exact B538735
  · exact B538739
  · exact B538743
  · exact B538747
  · exact B538751
  · exact B538755
  · exact B538759
  · exact B538763
  · exact B538767
  · exact B538771
  · exact B538775
  · exact B538779
  · exact B538783
  · exact B538787
  · exact B538791
  · exact B538795
  · exact B538799
  · exact B538803
  · exact B538807
  · exact B538811
  · exact B538815
  · exact B538819
  · exact B538823
  · exact B538827
  · exact B538831
  · exact B538835
  · exact B538839
  · exact B538843
  · exact B538847
  · exact B538851
  · exact B538855
  · exact B538859
  · exact B538863
  · exact B538867
  · exact B538871
  · exact B538875
  · exact B538879
  · exact B538883
  · exact B538887
  · exact B538891
  · exact B538895
  · exact B538899
  · exact B538903
  · exact B538907
  · exact B538911
  · exact B538915
  · exact B538919
  · exact B538923
  · exact B538927
  · exact B538931
  · exact B538935
  · exact B538939
  · exact B538943
  · exact B538947
  · exact B538951
  · exact B538955
  · exact B538959
  · exact B538963
  · exact B538967
  · exact B538971
  · exact B538975
  · exact B538979
  · exact B538983
  · exact B538987
  · exact B538991
  · exact B538995
  · exact B538999
  · exact B539003
  · exact B539007
  · exact B539011
  · exact B539015
  · exact B539019
  · exact B539023
  · exact B539027
  · exact B539031
  · exact B539035
  · exact B539039
  · exact B539043
  · exact B539047
  · exact B539051
  · exact B539055
  · exact B539059
  · exact B539063
  · exact B539067
  · exact B539071
  · exact B539075
  · exact B539079
  · exact B539083
  · exact B539087
  · exact B539091
  · exact B539095
  · exact B539099
  · exact B539103
  · exact B539107
  · exact B539111
  · exact B539115
  · exact B539119
  · exact B539123
  · exact B539127
  · exact B539131
  · exact B539135
  · exact B539139
  · exact B539143
  · exact B539147
  · exact B539151
  · exact B539155
  · exact B539159
  · exact B539163
  · exact B539167
  · exact B539171
  · exact B539175
  · exact B539179
  · exact B539183
  · exact B539187
  · exact B539191
  · exact B539195
  · exact B539199
  · exact B539203
  · exact B539207
  · exact B539211
  · exact B539215
  · exact B539219
  · exact B539223
  · exact B539227
  · exact B539231
  · exact B539235
  · exact B539239
  · exact B539243
  · exact B539247
  · exact B539251
  · exact B539255
  · exact B539259
  · exact B539263
  · exact B539267
  · exact B539271
  · exact B539275
  · exact B539279
  · exact B539283
  · exact B539287
  · exact B539291
  · exact B539295
  · exact B539299
  · exact B539303
  · exact B539307
  · exact B539311
  · exact B539315
  · exact B539319
  · exact B539323
  · exact B539327
  · exact B539331
  · exact B539335
  · exact B539339
  · exact B539343
  · exact B539347
  · exact B539351
  · exact B539355
  · exact B539359
  · exact B539363
  · exact B539367
  · exact B539371
  · exact B539375
  · exact B539379
  · exact B539383
  · exact B539387
  · exact B539391
  · exact B539395
  · exact B539399
  · exact B539403
  · exact B539407
  · exact B539411
  · exact B539415
  · exact B539419
  · exact B539423
  · exact B539427
  · exact B539431
  · exact B539435
  · exact B539439
  · exact B539443
  · exact B539447
  · exact B539451
  · exact B539455
  · exact B539459
  · exact B539463
  · exact B539467
  · exact B539471
  · exact B539475
  · exact B539479
  · exact B539483
  · exact B539487
  · exact B539491
  · exact B539495
  · exact B539499
  · exact B539503
  · exact B539507
  · exact B539511
  · exact B539515
  · exact B539519
  · exact B539523
  · exact B539527
  · exact B539531
  · exact B539535
  · exact B539539
  · exact B539543
  · exact B539547
  · exact B539551
  · exact B539555
  · exact B539559
  · exact B539563
  · exact B539567
  · exact B539571
  · exact B539575
  · exact B539579
  · exact B539583
  · exact B539587
  · exact B539591
  · exact B539595
  · exact B539599
  · exact B539603
  · exact B539607
  · exact B539611
  · exact B539615
  · exact B539619
  · exact B539623
  · exact B539627
  · exact B539631
  · exact B539635
  · exact B539639
  · exact B539643
  · exact B539647
  · exact B539651
  · exact B539655
  · exact B539659
  · exact B539663
  · exact B539667
  · exact B539671
  · exact B539675
  · exact B539679
  · exact B539683
  · exact B539687
  · exact B539691
  · exact B539695
  · exact B539699
  · exact B539703
  · exact B539707
  · exact B539711
  · exact B539715
  · exact B539719
  · exact B539723
  · exact B539727
  · exact B539731
  · exact B539735
  · exact B539739
  · exact B539743
  · exact B539747
  · exact B539751
  · exact B539755
  · exact B539759
  · exact B539763
  · exact B539767
  · exact B539771
  · exact B539775
  · exact B539779
  · exact B539783
  · exact B539787
  · exact B539791
  · exact B539795
  · exact B539799

theorem solution (m : ℕ) (hlo : 535802 ≤ m) (hhi : m ≤ 539802) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 133950 ≤ j := by omega
    have hj2 : j ≤ 134949 := by omega
    have hb : Blo 535802 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 134650 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
